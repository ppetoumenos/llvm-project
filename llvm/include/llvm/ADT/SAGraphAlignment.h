#include <map>
#include <set>
#include <vector>
#include <utility>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DirectedGraph.h"
#include "llvm/ADT/SmallBitVector.h"

#include "llvm/Analysis/ValueTracking.h"

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

template<typename ContainerType, typename Ty>
class DependencyInfo {
  llvm::SmallVector<llvm::SmallBitVector> Mtx;
  size_t Size;

public:
  enum Relation {
    NONE,
    ANCESTOR,
    DESCENTANT,
  };

  DependencyInfo(ContainerType Seq) : Size{Seq.Size()} {
    llvm::SmallDenseMap<llvm::Instruction *, size_t> IMap;

    for (size_t Idx = 0; Idx < Size; ++Idx) {
      Mtx.emplace_back(Idx);
      llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(Seq[Idx]);
      assert(I != nullptr);
      IMap[I] = Idx;
    }

    for (size_t Idx = 0; Idx < Size; ++Idx) {
      llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(Seq[Idx]);

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
        Mtx[Jdx].set(Idx);
      }

      // Add dependencies between this and all other instructions,
      // if control might leave this basic block
      if (I->mayThrow() || !I->willReturn() || llvm::isa<llvm::CallBase>(I)) {
        Mtx[Idx].set();
        for (size_t Jdx = Idx + 1; Jdx < Size; ++Jdx)
          Mtx[Jdx].set(Idx);
        continue;
      }

      // Add dependencies between this and all other memory instructions,
      // if this instruction modifies memory
      if (I->mayWriteToMemory()) {
        for (size_t Jdx = 0; Jdx < Idx; ++Jdx) {
          llvm::Instruction *ID = llvm::dyn_cast<llvm::Instruction>(Seq[Jdx]);
          if (ID->mayReadFromMemory() || ID->mayWriteToMemory())
            Mtx[Idx].set(Jdx);
        }
        for (size_t Jdx = Idx + 1; Jdx < Size; ++Jdx) {
          llvm::Instruction *ID = llvm::dyn_cast<llvm::Instruction>(Seq[Jdx]);
          if (ID->mayReadFromMemory() || ID->mayWriteToMemory())
            Mtx[Jdx].set(Idx);
        }
      }
    }

    // Connect all ancestors and descentants
    for (size_t Idx = 0; Idx < Size; ++Idx)
      for (size_t Jdx = 0; Jdx < Idx; ++Jdx)
        if(Mtx[Idx][Jdx])
          for (size_t Kdx = Idx + 1; Kdx < Size; ++Kdx) 
            if (Mtx[Kdx][Idx])
              Mtx[Kdx].set(Jdx);
  }

  bool isReady(size_t Idx) {
    return Mtx[Idx].none();
  }

  bool removeDependency(const size_t Idx, const size_t Jdx) {
    if (Mtx[Jdx][Idx])
      return false;

    Mtx[Jdx].reset(Idx);
    return Mtx[Jdx].none();
  }

  Relation getRelation(size_t Idx, size_t Jdx) {
    if (Idx < Jdx && Mtx[Jdx][Idx])
      return ANCESTOR;
    if (Idx > Jdx && Mtx[Idx][Jdx])
      return DESCENTANT;
    return NONE;
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
    for (size_t i = 0; i < Seq1.size(); ++i)
      for (size_t j = 0; j < Seq2.size(); ++j)
        if (BaseType::match(Seq1[i], Seq2[i]))
          num_matches++;

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
    DependencyInfo Dependent1(Seq1);
    DependencyInfo Dependent2(Seq2);

    std::vector<std::pair<size_t, size_t>> Matches;
    // Finding matching pairs. Skip the last instruction.
    for (size_t i = 0; i < Seq1.size() - 1; ++i)
      for (size_t j = 0; j < Seq2.size() - 1; ++j)
        if (BaseType::match(Seq1[i], Seq2[i]))
          Matches.emplace_back(i, j);

    // Last instructions can only match with each other.
    if (BaseType::match(Seq1.back(), Seq2.back()))
      Matches.emplace_back(Seq1.size() - 1, Seq2.size() - 1);

    // Register conflicts 
    size_t mcount = Matches.size();
    TriangularMatrix<int> Conflicts(mcount);
    for (size_t i = 0; i < mcount; ++i) {
      for (size_t j = 0; j < i; ++j) {
        size_t element1a = Matches[i].first;
        size_t element1b = Matches[i].second;
        size_t element2a = Matches[j].first;
        size_t element2b = Matches[j].second;

        if ((element1a == element2a) || (element1b == element2b)) {
          Conflicts.get_direct(i, j) = true;
          continue;
        }

        Relation rel1 = Dependent1.getRelation(element1a, element2a);
        Relation rel2 = Dependent2.getRelation(element1b, element2b);
        if (rel1 == ANCESTOR && rel2 == DESCENTANT)
          Conflicts.get_direct(i, j) = true;
        if (rel1 == DESCENTANT && rel2 == ANCESTOR)
          Conflicts.get_direct(i, j) = true;
      }
    }

    std::vector<std::pair<size_t, std::set<int>>> MatchSets;
    // One set for each match, containing the match index and its conflicts indexes
    for (size_t i = 0; i < mcount; ++i) {
      std::set<int> S;
      S.emplace(i);
      for (size_t j = 0; j < mcount; ++j) {
        if (i == j)
          continue;
        if (Conflicts.get(i, j))
          S.emplace(j);
      }
      MatchSets.push_back({i, std::move(S)});
    }

    std::unordered_map<size_t, size_t> M1(Matches.size());
    std::unordered_map<size_t, size_t> M2(Matches.size());

    std::sort(MatchSets.begin(), MatchSets.end(), [] (auto S1, auto S2) {return S1.second.size() > S2.second.size();});
    for (size_t i = 0; i < MatchSets.size(); ++i) {
      int Idx = MatchSets[i].first;
      if (Idx < 0)
        continue;
      M1[Matches[Idx].first] = Matches[Idx].second;
      M2[Matches[Idx].second] = Matches[Idx].first;
      for (size_t j = i + 1; j < MatchSets.size(); ++j) {
        if (MatchSets[j].second.count(Idx) > 0) {
          MatchSets[j].first = -1;
          break;
        }
      }
    }

    std::set<size_t> Ready1;
    for (size_t i = 0; i < Seq1.size(); ++i)
      if (Dependent1.isReady(i))
        Ready1.emplace(i);

    std::set<size_t> Ready2;
    for (size_t i = 0; i < Seq2.size(); ++i)
      if (Dependent2.isReady(i))
        Ready2.emplace(i);

    int state = 0;
    while ((Ready1.size() > 0) && (Ready2.size() > 0)) {
      if (state == 0) {
        state = 1;
        for (size_t Idx1 : Ready1) {
          auto it = M1.find(Idx1);
          if (it == M1.end())
            continue;
          size_t Idx2 = it->second;
          if (Ready2.count(Idx2) == 0)
            continue;

          Result.Data.push_front(typename BaseType::EntryType(Seq1[Idx1], Seq2[Idx2], true));
          Ready1.erase(Idx1);
          Ready2.erase(Idx2);

          for (size_t Jdx = Idx1 + 1; Jdx < Seq1.size(); ++Jdx)
            if (Dependent1.removeDependency(Idx1, Jdx))
              Ready1.emplace(Jdx);

          for (size_t Jdx = Idx2 + 1; Jdx < Seq2.size(); ++Jdx)
            if (Dependent2.removeDependency(Idx2, Jdx))
              Ready2.emplace(Jdx);

          state = 0;
          break;
        }
      } else if (state == 1) {
        state = 2;
        for (size_t Idx1 : Ready1) {
          auto it = M1.find(Idx1);
          if (it != M1.end())
            continue;

          Result.Data.push_front(typename BaseType::EntryType(Seq1[Idx1], Blank, false));

          for (size_t Jdx = Idx1 + 1; Jdx < Seq1.size(); ++Jdx) {
            if (Dependent1.removeDependency(Idx1, Jdx))
              Ready1.emplace(Jdx);
          }

          state = 1;
          break;
        }
      } else if (state == 2) {
        state = 0;
        for (size_t Idx2 : Ready2) {
          auto it = M2.find(Idx2);
          if (it != M2.end())
            continue;

          Result.Data.push_front(typename BaseType::EntryType(Blank, Seq2[Idx2], false));

          for (size_t Jdx = Idx2 + 1; Jdx < Seq2.size(); ++Jdx) {
            if (Dependent2.removeDependency(Idx2, Jdx))
              Ready2.emplace(Jdx);
          }

          state = 2;
          break;
        }
      }
    }

    return Result;
  }
};
