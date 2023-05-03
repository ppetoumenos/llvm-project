#include <map>
#include <numeric>
#include <set>
#include <vector>
#include <utility>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DirectedGraph.h"
#include "llvm/ADT/PriorityQueue.h"
#include "llvm/ADT/SmallBitVector.h"

#include "llvm/Analysis/ValueTracking.h"

//#define ENABLE_GA_DEBUG

class FMDEdge;
class FMDNode;

class FMDEdge : public llvm::DGEdge<FMDNode, FMDEdge> {
public:
  FMDEdge(FMDNode &N) : DGEdge<FMDNode, FMDEdge>(N) {}
  FMDEdge(const FMDEdge &E) : DGEdge<FMDNode, FMDEdge>(E) {}
  FMDEdge(FMDEdge &&E) : DGEdge<FMDNode, FMDEdge>(std::move(E)) {}
  FMDEdge &operator=(const FMDEdge &E) = default;

  FMDEdge &operator=(FMDEdge &&E) {
    DGEdge<FMDNode, FMDEdge>::operator=(std::move(E));
    return *this;
  }
};

class FMDNode : public llvm::DGNode<FMDNode, FMDEdge> {
  llvm::Instruction* I;
  int Idx;
public:
  FMDNode() = delete;
  FMDNode(llvm::Instruction *I, int Idx) :  I(I), Idx(Idx) {};
  FMDNode(const FMDNode &N) : DGNode<FMDNode, FMDEdge>(N), I(N.I), Idx(N.Idx) {};
  FMDNode(FMDNode &&N) : DGNode<FMDNode, FMDEdge>(N), I(N.I), Idx(N.Idx) {};
  FMDNode &operator=(const FMDNode &N) = default;

  FMDNode &operator=(FMDNode &&N) {
    DGNode<FMDNode, FMDEdge>::operator=(std::move(N));
    I = N.I;
    Idx = N.Idx;
    return *this;
  }

  /// Get the instruction in this node.
  const llvm::Instruction *getInstruction() const {
    return I;
  }

  int getIdx() const {
    return Idx;
  }
};

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

template <typename ContainerType>
class FMDGraph : public llvm::DirectedGraph<FMDNode, FMDEdge>{
  llvm::DenseMap<llvm::Instruction *, FMDNode *> IMap;
public:
  using NodeType = FMDNode;
  using EdgeType = FMDEdge;

  FMDGraph() = delete;
  FMDGraph(const FMDGraph &G) = delete;
  FMDGraph(FMDGraph &&G) = delete;
  FMDGraph(ContainerType &Seq) {
    for (size_t count = 0; count < Seq.size(); ++count) {
      llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(Seq[count]);
      if (!I)
        continue;
      FMDNode *NewNode = new FMDNode(I, count);
      addNode(*NewNode);
      IMap.insert(std::make_pair(I, NewNode));
    }

    for (auto *N : Nodes) {
      std::set<FMDNode *> Visited;
      const llvm::Instruction *I = N->getInstruction();
      const int Idx = N->getIdx();

      for (const llvm::User *U: I->users()) {
        const llvm::Instruction *UI = llvm::dyn_cast<llvm::Instruction>(U);
        if (!UI)
          continue;
        if (UI->getParent() != I->getParent())
          continue;
        auto It = IMap.find(UI);
        if (It != IMap.end()) {
          auto *ND = It->second;
          if (ND == N)
            continue;
          if (Visited.insert(ND).second) {
            auto *NewEdge = new FMDEdge(*ND);
            connect(*N, *ND, *NewEdge);
          }
        }
      }

      // Serialize if control might leave this basic block
      if (I->mayThrow() || !I->willReturn() || llvm::isa<llvm::CallBase>(I)) {
        for (auto *ND : Nodes) {
          if (ND->getIdx() < Idx) {
            auto *NewEdge = new FMDEdge(*N);
            connect(*ND, *N, *NewEdge);
          } else if (ND->getIdx() > Idx) {
            auto *NewEdge = new FMDEdge(*ND);
            connect(*N, *ND, *NewEdge);
          }
        }
        continue;
      }

      if (I->mayWriteToMemory()) {
        for (auto *ND : Nodes) {
          const llvm::Instruction *ID = ND->getInstruction();
          if (ID->mayReadFromMemory() || ID->mayWriteToMemory()) {
            if (ND->getIdx() < Idx) {
              auto *NewEdge = new FMDEdge(*N);
              connect(*ND, *N, *NewEdge);
            } else if (ND->getIdx() > Idx) {
              auto *NewEdge = new FMDEdge(*ND);
              connect(*N, *ND, *NewEdge);
            }
          }
        }
      }

    }
  }

  FMDNode *getNode(const llvm::Value *V) {
    const llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(V);
    assert(I != nullptr);
    return IMap.find(I)->second;
  }

  ~FMDGraph() {
    for (auto *N : Nodes) {
      for (auto *E : *N) {
        delete E;
      }
      delete N;
    }
  }

protected:
  bool addNode(NodeType &N) {
    return DirectedGraph<FMDNode, FMDEdge>::addNode(N);
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

template<typename Ty>
bool isReady(TriangularMatrix<Ty> &Mtx, size_t Idx) {
  for (size_t Jdx = 0; Jdx < Idx; ++Jdx)
    if (Mtx.get_direct(Idx, Jdx))
      return false;
  return true;
}

template<typename Ty>
bool removeDependency(TriangularMatrix<Ty> &Mtx, size_t Idx, size_t Jdx) {
  auto &entry = Mtx.get_direct(Jdx, Idx);
  if (!entry)
    return false;

  entry = false;
  return isReady(Mtx, Jdx);
}


template <typename ContainerType,
          typename Ty = typename ContainerType::value_type, Ty Blank = Ty(0),
          typename MatchFnTy = std::function<bool(Ty, Ty)>>
class GraphSA : public SequenceAligner<ContainerType, Ty, Blank, MatchFnTy> {
private:
  using BaseType = SequenceAligner<ContainerType, Ty, Blank, MatchFnTy>;

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

  TriangularMatrix<int> getDependencies(ContainerType &Seq) {
    FMDGraph<ContainerType> G(Seq);

    size_t SeqSize = Seq.size();

    TriangularMatrix<int> Dependent(SeqSize);

    for (size_t i = 0; i < SeqSize; ++i) {
      for (size_t j = 0; j < i; ++j) {
        if (Dependent.get_direct(i, j)) {
          for (FMDEdge *E: G.getNode(Seq[i])->getEdges()) {
            size_t k = E->getTargetNode().getIdx();
            assert(k > i);
            Dependent.get_direct(k, j) = true;
          }
        }
      }
    }
    return Dependent;
  }

  virtual AlignedSequence<Ty, Blank> getAlignment(ContainerType &Seq1,
                                                  ContainerType &Seq2) override {
    AlignedSequence<Ty, Blank> Result;

    assert(BaseType::getMatchOperation() != nullptr);


    // Triangular matrices indicating direct or indirect dependencies
    DependencyInfo<ContainerType, Ty> Dependent1(Seq1);
    DependencyInfo<ContainerType, Ty> Dependent2(Seq2);

    std::vector<std::pair<size_t, size_t>> Matches;
    std::unordered_map<size_t, size_t> M1;
    std::unordered_map<size_t, size_t> M2;

    const size_t Size1{Seq1.size()};
    const size_t Size2{Seq2.size()};

    // Last entries (Terminators) can only match with each other
    // Directly add them to the solution
    if (BaseType::match(Seq1.back(), Seq2.back())) {
      M1[Size1 - 1] = Size2 - 1;
      M2[Size2 - 1] = Size1 - 1;
    }

    // Finding matching pairs. Skip the basicblock and the last instruction.
    for (size_t i = 1; i < Size1 - 1; ++i)
      for (size_t j = 1; j < Size2 - 1; ++j)
        if (BaseType::match(Seq1[i], Seq2[j]))
          Matches.emplace_back(i, j);

#ifdef ENABLE_GA_DEBUG
    for (auto Match: Matches) 
      llvm::errs() <<  Match.first << "\t" << Match.second << "\n";
    llvm::errs() << "Number of Matches: " << Matches.size() << "\n";
#endif

    size_t mcount = Matches.size();

    // Register conflicts
    ConflictsInfo<ContainerType, Ty> CI(Matches, Dependent1, Dependent2, (mcount * mcount < Size1 * Size2) ? mcount : 0);


#if 0
    // One set for each match, containing the match index and its conflicts indexes
    std::vector<std::pair<size_t, std::set<int>>> MatchSets;
    for (size_t i = 0; i < mcount; ++i) {
      std::set<int> S;
      S.emplace(i);
      for (size_t j = 0; j < mcount; ++j) {
        if (i == j)
          continue;
        if (CI.isConflict(i, j))
          S.emplace(j);
      }
      MatchSets.push_back({i, std::move(S)});
    }

    std::sort(MatchSets.begin(), MatchSets.end(), [] (auto S1, auto S2) {return S1.second.size() < S2.second.size();});
    for (size_t i = 0; i < MatchSets.size(); ++i) {
      int Idx = MatchSets[i].first;
      if (Idx < 0)
        continue;
      M1[Matches[Idx].first] = Matches[Idx].second;
      M2[Matches[Idx].second] = Matches[Idx].first;
      for (size_t j = i + 1; j < MatchSets.size(); ++j) {
        if (MatchSets[j].first < 0)
          continue;
        if (MatchSets[j].second.count(Idx) > 0) {
          MatchSets[j].first = -1;
        }
      }
    }
#else
    std::vector<size_t> num_conflicts(mcount);
    for (size_t i = 0; i < mcount; ++i) {
      for (size_t j = 0; j < i; ++j) {
        if (CI.isConflict(i, j)) {
          num_conflicts[i]++;
          num_conflicts[j]++;
        }
      }
    }

    std::vector<int> idxs(mcount);
    std::iota(idxs.begin(), idxs.end(), 0);
    std::sort(idxs.begin(), idxs.end(), [&](int idx1, int idx2) {return num_conflicts[idx1] < num_conflicts[idx2];});

    for (size_t i = 0; i < mcount; ++i) {
      int MatchIdx1 = idxs[i];
      if (MatchIdx1 < 0)
        continue;

      M1[Matches[MatchIdx1].first] = Matches[MatchIdx1].second;
      M2[Matches[MatchIdx1].second] = Matches[MatchIdx1].first;

      for (size_t j = i + 1; j < mcount; ++j) {
        int &MatchIdx2 = idxs[j];
        if (MatchIdx2 < 0)
          continue;
        if (CI.isConflict(MatchIdx1, MatchIdx2))
          MatchIdx2 = -1;
      }
    }
#endif

#ifdef ENABLE_GA_DEBUG
  llvm::errs() << "Selected Matches: \n";
  for (auto &p : M1)
    llvm::errs() << "--->\t" << p.first << "\t" << p.second << "\n";
#endif

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
