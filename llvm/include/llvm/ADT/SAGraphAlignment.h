#include <map>
#include <numeric>
#include <set>
#include <stack>
#include <vector>
#include <utility>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DirectedGraph.h"
#include "llvm/ADT/PriorityQueue.h"
#include "llvm/ADT/SmallBitVector.h"

#include "llvm/Analysis/ValueTracking.h"

//#define ENABLE_GA_DEBUG

template<typename Ty>
class TriangularMatrix {
  std::vector<Ty> Arr;

public:
  TriangularMatrix(size_t Size) : Arr((Size * (Size - 1)) / 2) {};

  inline Ty &get_direct(size_t x, size_t y) {
      return Arr[(x * (x - 1)) / 2 + y];
  }

  inline Ty &get(size_t x, size_t y) {
    if (x > y)
      return get_direct(x, y);
    return get_direct(y, x);
  }
};

enum Relation {
  NONE,
  ANCESTOR,
  DESCENTANT,
};

template<typename ContainerType, typename Ty>
class DependencyInfo {
  llvm::SmallVector<llvm::SmallBitVector> Dep;
  size_t Size;

public:

  DependencyInfo(const ContainerType &Seq) : Size{Seq.size()} {
    llvm::SmallDenseMap<llvm::Instruction *, size_t> IMap;
#ifdef ENABLE_GA_DEBUG
    llvm::errs() << "Sequence Size: " << Size << "\n";
#endif

    for (size_t Idx = 0; Idx < Size; ++Idx) {
      Dep.emplace_back(Idx);
      llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(Seq[Idx]);
      if (I == nullptr)
        continue;
      IMap[I] = Idx;
    }

    for (size_t Idx = 0; Idx < Size - 1; ++Idx) {
      llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(Seq[Idx]);
      if (I == nullptr)
        continue;

      // Add dependencies between this Instruction and its users
      for (const llvm::User *U: I->users()) {
        const llvm::Instruction *UI = llvm::dyn_cast<llvm::Instruction>(U);
        if (!UI || UI->getParent() != I->getParent())
          continue;

        auto It = IMap.find(UI);
        if (It == IMap.end())
          continue;

        size_t Jdx = It->second;
        if (Idx == Jdx)
          continue;

        assert(Idx < Jdx);
        Dep[Jdx].set(Idx);
      }

      // Add dependencies between this and all other instructions,
      // if control might leave this basic block
      if (I->mayThrow() || !I->willReturn() || llvm::isa<llvm::CallBase>(I)) {
        Dep[Idx].set();
        for (size_t Jdx = Idx + 1; Jdx < Size; ++Jdx)
          Dep[Jdx].set(Idx);
        continue;
      }

      // Add dependencies between this and all other memory instructions,
      // if this instruction modifies memory
      if (I->mayWriteToMemory()) {
        for (size_t Jdx = 1; Jdx < Idx; ++Jdx) {
          llvm::Instruction *ID = llvm::dyn_cast<llvm::Instruction>(Seq[Jdx]);
          if (!ID)
            continue;
          if (ID->mayReadFromMemory() || ID->mayWriteToMemory())
            Dep[Idx].set(Jdx);
        }
        for (size_t Jdx = Idx + 1; Jdx < Size; ++Jdx) {
          llvm::Instruction *ID = llvm::dyn_cast<llvm::Instruction>(Seq[Jdx]);
          if (ID->mayReadFromMemory() || ID->mayWriteToMemory())
            Dep[Jdx].set(Idx);
        }
      }
    }

    // First column represents the BB entry
    // It's treated separately
    for (size_t Idx = 1; Idx < Size; ++Idx)
      Dep[Idx].reset(0);

    // Connect all ancestors and descentants
    for (size_t Idx = 2; Idx < Size - 1; ++Idx)
      for (size_t Jdx: Dep[Idx].set_bits())
        for (size_t Kdx = Idx + 1; Kdx < Size; ++Kdx) 
          if (Dep[Kdx][Idx])
            Dep[Kdx].set(Jdx);

    // Connect all instructions with the terminator
    Dep[Size - 1].set();
    Dep[Size - 1].reset(0);
  }

  bool isReady(size_t Idx) {
    return Dep[Idx].none();
  }

  bool removeDependency(const size_t Idx, const size_t Jdx) {
#ifdef ENABLE_GA_DEBUG
    llvm::errs() << "BEFOR: " << (Dep[Jdx][Idx] ? "Y" : "N") << "\n";
#endif
    if (!Dep[Jdx][Idx])
      return false;

    Dep[Jdx].reset(Idx);
    return Dep[Jdx].none();
  }

  Relation getRelation(size_t Idx, size_t Jdx) {
    if (Idx < Jdx && Dep[Jdx][Idx])
      return ANCESTOR;
    if (Idx > Jdx && Dep[Idx][Jdx])
      return DESCENTANT;
    return NONE;
  }

  void print_state() {
    for (size_t Idx = 0; Idx < Size; ++Idx) {
      for (size_t Jdx = 0; Jdx < Idx; ++Jdx) {
        llvm::errs() << (Dep[Idx][Jdx] ? "Y " : "N ");
      }
      llvm::errs() << "\n";
    }
  }

  size_t size() {
    return Size;
  }

  llvm::SmallBitVector getConnections(size_t Idx) {
    llvm::SmallBitVector conns(Size);
    for (size_t i = 0; i < Size; ++i) {
      if (i < Idx)
        conns[i] = Dep[Idx][i];
      else if (i > Idx)
        conns[i] = Dep[i][Idx];
    }
    return conns;
  }
};


template<typename ContainerType, typename Ty>
class ConflictsInfo {

  bool Cached{false};
  TriangularMatrix<int> Cache;
  std::vector<std::pair<size_t, size_t>> &Matches;
  DependencyInfo<ContainerType, Ty> &Dep1;
  DependencyInfo<ContainerType, Ty> &Dep2;


  public:

  ConflictsInfo(
      std::vector<std::pair<size_t, size_t>> &Matches,
      DependencyInfo<ContainerType, Ty> &Dep1, 
      DependencyInfo<ContainerType, Ty> &Dep2, 
      size_t Size) : Cache(Size), Matches{Matches}, Dep1{Dep1}, Dep2{Dep2} {

    if (Size != Matches.size())
      return;

    Cached = true;
    for (size_t i = 0; i < Size; ++i)
      for (size_t j = 0; j < i; ++j)
        Cache.get_direct(i, j) = _isConflict(i, j);

#ifdef ENABLE_GA_DEBUG
    for (size_t i = 0; i < Size; ++i) {
      for (size_t j = 0; j < i; ++j) {
        llvm::errs() << Cache.get_direct(i, j) << " ";
      }
      llvm::errs() << "\n";
    }
#endif

  }

  bool isConflict(size_t MatchIdx1, size_t MatchIdx2) {
    if (Cached)
      return Cache.get(MatchIdx1, MatchIdx2);
    return _isConflict(MatchIdx1, MatchIdx2);
  }

  private:
  bool _isConflict(size_t MatchIdx1, size_t MatchIdx2) {
    size_t element1a = Matches[MatchIdx1].first;
    size_t element1b = Matches[MatchIdx1].second;

    size_t element2a = Matches[MatchIdx2].first;
    size_t element2b = Matches[MatchIdx2].second;

    if ((element1a == element2a) || (element1b == element2b))
      return true;

    auto rel1 = Dep1.getRelation(element1a, element2a);
    auto rel2 = Dep2.getRelation(element1b, element2b);
    if (rel1 == ANCESTOR && rel2 == DESCENTANT)
      return true;
    if (rel1 == DESCENTANT && rel2 == ANCESTOR)
      return true;

    return false;
  }

};

template <typename ContainerType,
          typename Ty = typename ContainerType::value_type, Ty Blank = Ty(0),
          typename MatchFnTy = std::function<bool(Ty, Ty)>>
class GraphSA : public SequenceAligner<ContainerType, Ty, Blank, MatchFnTy> {
private:
  using BaseType = SequenceAligner<ContainerType, Ty, Blank, MatchFnTy>;


  std::unordered_map<size_t, size_t> EagerMatchSolver(
      std::vector<std::pair<size_t, size_t>> &Matches,
      DependencyInfo<ContainerType, Ty> &D1,
      DependencyInfo<ContainerType, Ty> &D2) {

    std::unordered_map<size_t, size_t> Selected;
    size_t mcount = Matches.size();
    size_t Size1 = D1.size();
    size_t Size2 = D2.size();

    if (mcount == 0)
      return Selected;

    // Register conflicts
    ConflictsInfo<ContainerType, Ty> CI(Matches, D1, D2, (mcount * mcount < Size1 * Size2) ? mcount : 0);

    // Count conflicts
    std::vector<size_t> num_conflicts(mcount);
    for (size_t i = 0; i < mcount; ++i) {
      for (size_t j = 0; j < i; ++j) {
        if (CI.isConflict(i, j)) {
          num_conflicts[i]++;
          num_conflicts[j]++;
        }
      }
    }

    // Rank matches by ascending numbers of conflicts
    std::vector<int> idxs(mcount);
    std::iota(idxs.begin(), idxs.end(), 0);
    std::sort(idxs.begin(), idxs.end(), [&](int idx1, int idx2) {return num_conflicts[idx1] < num_conflicts[idx2];});

    // Greedy selection of matches
    for (size_t i = 0; i < mcount; ++i) {
      int MatchIdx1 = idxs[i];
      if (MatchIdx1 < 0)
        continue;

      auto Match = Matches[MatchIdx1];
      Selected[Match.first] = Match.second;

      for (size_t j = i + 1; j < mcount; ++j) {
        int &MatchIdx2 = idxs[j];
        if (MatchIdx2 < 0)
          continue;
        if (CI.isConflict(MatchIdx1, MatchIdx2))
          MatchIdx2 = -1;
      }
    }
    return Selected;
  }

  static constexpr bool count_matches = false;

  std::unordered_map<size_t, size_t> ExhaustiveSolver(
      std::vector<std::pair<size_t, size_t>> &Matches,
      DependencyInfo<ContainerType, Ty> &D1,
      DependencyInfo<ContainerType, Ty> &D2) {

    std::unordered_map<size_t, size_t> Selected;
    size_t mcount = Matches.size();
    size_t Size1 = D1.size();
    size_t Size2 = D2.size();

    if (mcount == 0)
      return Selected;

    // Register conflicts
    ConflictsInfo<ContainerType, Ty> CI(Matches, D1, D2, (mcount * mcount < Size1 * Size2) ? mcount : 0);

    std::stack<size_t> stk;
    std::stack<size_t> score;
    std::stack<llvm::SmallBitVector> valid;

    size_t best_score = 0;
    llvm::SmallBitVector best(mcount);
    llvm::SmallBitVector curr(mcount);

    stk.push(0);
    score.push(0);
    valid.emplace(mcount);
    valid.top().set();

    while (!stk.empty()) {
      size_t Idx = stk.top();
      size_t this_score = score.top();
      curr.flip(Idx);

      auto& curr_valid = valid.top();
      curr_valid.reset(Idx);
      auto next_valid = curr_valid;

      if (curr[Idx]) {
        for (size_t Jdx: curr_valid.set_bits())
          if (CI.isConflict(Idx, Jdx))
            next_valid.reset(Jdx);
        if (count_matches)
          this_score += 1;
        else {
          this_score += 10; // Matching node
          llvm::SmallBitVector pred1 = D1.getConnections(Matches[Idx].first);
          llvm::SmallBitVector pred2 = D2.getConnections(Matches[Idx].second);
          for (size_t Jdx: curr.set_bits())
            if (pred1[Matches[Jdx].first] && pred2[Matches[Jdx].second])
              this_score += 1;
        }
      }


      bool cannot_be_best;
      if (count_matches)
        cannot_be_best = (this_score + next_valid.count()) < best_score;
      else
        cannot_be_best = (this_score + next_valid.count() * 25) < best_score;

      if (next_valid.none() || cannot_be_best) {
        if (this_score > best_score) {
          best = curr;
          best_score = this_score;
        }

        while (!stk.empty() && !curr[stk.top()]) {
          stk.pop();
          score.pop();
          valid.pop();
        }
      } else {
        stk.push(next_valid.find_first());
        score.push(this_score);
        valid.push(next_valid);
      } 
    }
    
    for (size_t Idx: best.set_bits()) {
      auto Match = Matches[Idx];
      Selected[Match.first] = Match.second;
    }

    return Selected;
  }

public:
  static ScoringSystem getDefaultScoring() { return ScoringSystem(0, 1, 0); }

  GraphSA() : BaseType(getDefaultScoring(), nullptr) {}

  GraphSA(ScoringSystem Scoring, MatchFnTy Match = nullptr) : BaseType(Scoring, Match) {}

  ~GraphSA() = default;

  virtual size_t getMemoryRequirement(ContainerType &Seq1,
                                      ContainerType &Seq2) override {
    // Finding matching pairs
    size_t num_matches = 0;
    for (size_t i = 0; i < Seq1.size(); ++i) {
      for (size_t j = 0; j < Seq2.size(); ++j) {
        if (BaseType::match(Seq1[i], Seq2[j])) {
          num_matches++;
        }
      }
    }

    size_t MemorySize = 2 * sizeof(size_t) * num_matches;
    MemorySize += sizeof(size_t) * (num_matches * (num_matches - 1)) / 2;
    MemorySize += 3 * sizeof(size_t) * num_matches * num_matches;

    return MemorySize;
  }

  virtual AlignedSequence<Ty, Blank> getAlignment(ContainerType &Seq1,
                                                  ContainerType &Seq2) override {
    assert(BaseType::getMatchOperation() != nullptr);

    // Triangular matrices indicating direct or indirect dependencies
    DependencyInfo<ContainerType, Ty> Dependent1(Seq1);
    DependencyInfo<ContainerType, Ty> Dependent2(Seq2);

    const size_t Size1{Seq1.size()};
    const size_t Size2{Seq2.size()};

    // Finding matching pairs. Skip the basicblock and the last instruction.
    std::vector<std::pair<size_t, size_t>> Matches;
    for (size_t i = 1; i < Size1 - 1; ++i)
      for (size_t j = 1; j < Size2 - 1; ++j)
        if (BaseType::match(Seq1[i], Seq2[j]))
          Matches.emplace_back(i, j);

#ifdef ENABLE_GA_DEBUG
    for (auto Match: Matches) 
      llvm::errs() <<  Match.first << "\t" << Match.second << "\n";
    llvm::errs() << "Number of Matches: " << Matches.size() << "\n";
#endif

    // Get a solution in the form of map from Seq1 indexes to Seq2 indexes
    std::unordered_map<size_t, size_t> M1;
    if (Matches.size() > 80)
      M1 = EagerMatchSolver(Matches, Dependent1, Dependent2);
    else
      M1 = ExhaustiveSolver(Matches, Dependent1, Dependent2);

    // Terminators can only match with each other. Add them to the solution if matching.
    if (BaseType::match(Seq1.back(), Seq2.back()))
      M1[Size1 - 1] = Size2 - 1;

    // Reverse lookup
    decltype(M1) M2;
    for (const auto& kv: M1)
      M2[kv.second] = kv.first;

#ifdef ENABLE_GA_DEBUG
    llvm::errs() << "Selected Matches: \n";
    for (auto &p : M1)
      llvm::errs() << "--->\t" << p.first << "\t" << p.second << "\n";
#endif

    // Construct the aligned Sequence
    AlignedSequence<Ty, Blank> Result;

    // Process BB entries
    if (BaseType::match(Seq1[0], Seq2[0])) {
      Result.Data.push_front(typename BaseType::EntryType(Seq1[0], Seq2[0], true));
    } else {
      Result.Data.push_front(typename BaseType::EntryType(Seq1[0], Blank, false));
      Result.Data.push_front(typename BaseType::EntryType(Blank, Seq2[0], false));
    }

    llvm::PriorityQueue<size_t, std::vector<size_t>, std::greater<size_t>> Ready1, Ready2, ReadyMatches;
    std::set<size_t> UnReady1, UnReady2;

    for (size_t i = 1; i < Size1; ++i) {
      if (Dependent1.isReady(i)) {
        auto it = M1.find(i);
        if (it == M1.end()) 
          Ready1.emplace(i);
        else if (Dependent2.isReady(it->second))
          ReadyMatches.emplace(i);
        else 
          UnReady1.emplace(i);
      }
    }

    for (size_t i = 1; i < Size2; ++i) {
      if (Dependent2.isReady(i)) {
        auto it = M2.find(i);
        if (it == M2.end()) 
          Ready2.emplace(i);
        else if (!Dependent1.isReady(it->second))
          UnReady2.emplace(i);
      }
    }

    int state = 0;
    bool Progress = false;
    while (!Ready1.empty() || !Ready2.empty() || !ReadyMatches.empty()) {
      if (state == 0) {
        state = 1;
        Progress = false;
        while (!ReadyMatches.empty()) {
          Progress = true;
          size_t Idx1 = ReadyMatches.top();
          size_t Idx2 = M1[Idx1];

          Result.Data.push_front(typename BaseType::EntryType(Seq1[Idx1], Seq2[Idx2], true));
          ReadyMatches.pop();

          for (size_t Jdx = Idx1 + 1; Jdx < Size1; ++Jdx) {
#ifdef ENABLE_GA_DEBUG
            llvm::errs() << "REMOVE 1: " << Idx1 << " -> " << Jdx << "\n";
#endif
            if (Dependent1.removeDependency(Idx1, Jdx)) {
              auto it = M1.find(Jdx);
              if (it == M1.end()) {
                Ready1.emplace(Jdx);
              } else {
                auto it_other = UnReady2.find(it->second);
                if (it_other != UnReady2.end()) {
                  ReadyMatches.emplace(Jdx);
                  UnReady2.erase(it_other);
                } else {
                  UnReady1.emplace(Jdx);
                }
              }
            }
          }

          for (size_t Jdx = Idx2 + 1; Jdx < Size2; ++Jdx) {
#ifdef ENABLE_GA_DEBUG
            llvm::errs() << "REMOVE 2: " << Idx2 << " -> " << Jdx << "\n";
#endif
            if (Dependent2.removeDependency(Idx2, Jdx)) {
              auto it = M2.find(Jdx);
              if (it == M2.end()) {
                Ready2.emplace(Jdx);
              } else {
                auto it_other = UnReady1.find(it->second);
                if (it_other != UnReady1.end()) {
                  ReadyMatches.emplace(it->second);
                  UnReady1.erase(it_other);
                } else {
                  UnReady2.emplace(Jdx);
                }
              }
            }
          }

#ifdef ENABLE_GA_DEBUG
          llvm::errs() << "XXXX 1 XXXX\n";
          Dependent1.print_state();
          llvm::errs() << "XXXX 2 XXXX\n";
          Dependent2.print_state();
#endif
        }
      } else if (state == 1) {
        state = 2;
        while (!Ready1.empty()) {
          Progress = true;
          size_t Idx1 = Ready1.top();

          Result.Data.push_front(typename BaseType::EntryType(Seq1[Idx1], Blank, false));
          Ready1.pop();

          for (size_t Jdx = Idx1 + 1; Jdx < Size1; ++Jdx) {
#ifdef ENABLE_GA_DEBUG
            llvm::errs() << "REMOVE 1: " << Idx1 << " -> " << Jdx << "\n";
#endif
            if (Dependent1.removeDependency(Idx1, Jdx)) {
              auto it = M1.find(Jdx);
              if (it == M1.end()) {
                Ready1.emplace(Jdx);
              } else {
                auto it_other = UnReady2.find(it->second);
                if (it_other != UnReady2.end()) {
                  ReadyMatches.emplace(Jdx);
                  UnReady2.erase(it_other);
                } else {
                  UnReady1.emplace(Jdx);
                }
              }
            }
          }
#ifdef ENABLE_GA_DEBUG
          llvm::errs() << "XXXX 1 XXXX\n";
          Dependent1.print_state();
#endif
        }
      } else if (state == 2) {
        state = 3;
        while (!Ready2.empty()) {
          Progress = true;
          size_t Idx2 = Ready2.top();

          Result.Data.push_front(typename BaseType::EntryType(Blank, Seq2[Idx2], false));
          Ready2.pop();

          for (size_t Jdx = Idx2 + 1; Jdx < Size2; ++Jdx) {
            if (Dependent2.removeDependency(Idx2, Jdx)) {
              auto it = M2.find(Jdx);
              if (it == M2.end()) {
                Ready2.emplace(Jdx);
              } else {
                auto it_other = UnReady1.find(it->second);
                if (it_other != UnReady1.end()) {
                  ReadyMatches.emplace(it->second);
                  UnReady1.erase(it_other);
                } else {
                  UnReady2.emplace(Jdx);
                }
              }
            }
          }
#ifdef ENABLE_GA_DEBUG
          llvm::errs() << "XXXX 2 XXXX\n";
          Dependent2.print_state();
#endif
        }
      } else if (state == 3) {
        state = 0;
        if (Progress)
          continue;

        // If we get here, we went through a whole cycle of states without
        // adding any instructions to the Result. This will only happen, if
        // all ready instructions are matched with unready instructions.
        // This should not happen but it does because we might have selected
        // some matches that conflict with the other ones. 1-to-1 conflicts
        // are forbidden by design, but 1-to-many are still possible. A better
        // match selection algorithm could avoid this, but it's more convenient
        // to just remove matches when it happens.

        // Remove the match for the numerically smallest ready instruction
        
        size_t min1 = std::numeric_limits<size_t>::max();
        if (UnReady1.size() > 0)
          min1 = *(UnReady1.begin());

        size_t min2 = std::numeric_limits<size_t>::max();
        if (UnReady2.size() > 0)
          min2 = *(UnReady2.begin());

        assert(min1 != std::numeric_limits<size_t>::max() || min2 != std::numeric_limits<size_t>::max());

        if (min1 <= min2) {
          assert(M1.count(min1) > 0);
          M2.erase(M1[min1]);
          M1.erase(min1);
          UnReady1.erase(min1);
          Ready1.emplace(min1);
        } else {
          assert(M2.count(min2) > 0);
          M1.erase(M2[min2]);
          M2.erase(min2);
          UnReady2.erase(min2);
          Ready2.emplace(min2);
        }
      }
    }

    Result.Data.reverse();

#ifdef ENABLE_GA_DEBUG
    for (auto &Entry : Result.Data) {
      if (Entry.match()) {
        llvm::errs() << "1: ";
        if (llvm::isa<llvm::BasicBlock>(Entry.get(0)))
          llvm::errs() << "BB " << "\n";
        else
          Entry.get(0)->dump();
        llvm::errs() << "2: ";
        if (llvm::isa<llvm::BasicBlock>(Entry.get(1)))
          llvm::errs() << "BB " << "\n";
        else
          Entry.get(1)->dump();
        llvm::errs() << "----\n";
      } else {
        if (Entry.get(0)) {
          llvm::errs() << "1: ";
          if (llvm::isa<llvm::BasicBlock>(Entry.get(0)))
            llvm::errs() << "BB " << "\n";
          else
            Entry.get(0)->dump();
          llvm::errs() << "2: -\n";
        } else if (Entry.get(1)) {
          llvm::errs() << "1: -\n";
          llvm::errs() << "2: ";
          if (llvm::isa<llvm::BasicBlock>(Entry.get(1)))
            llvm::errs() << "BB " << "\n";
          else
            Entry.get(1)->dump();
        }
        llvm::errs() << "----\n";
      }
    }
#endif

    return Result;
  }
};
