#ifndef SANEEDLEMANWUNSCH_H
#define SANEEDLEMANWUNSCH_H

#include <functional>

#include "llvm/ADT/SequenceAlignment.h"

template <typename Ty>
class Vec2D {
  public:
    bool empty() {
      return Data.empty();
    }

    void clear() {
      Rows = 0;
      Cols = 0;
      Data.clear();
    }

    void resize(size_t NewRows, size_t NewCols) {
      Rows = NewRows;
      Cols = NewCols;
      Data.resize(Rows * Cols);
    }

    const Ty& operator()(size_t Row, size_t Col) const {
      return Data[Row * Cols + Col];
    }

    Ty& operator()(size_t Row, size_t Col) {
      return Data[Row * Cols + Col];
    }
  private:
    std::vector<Ty> Data;
    size_t Rows;
    size_t Cols;

};

template <typename ContainerType,
          typename Ty = typename ContainerType::value_type, Ty Blank = Ty(0),
          typename MatchFnTy = std::function<MatchScore(Ty, Ty)>>
class NeedlemanWunschSA
    : public SequenceAligner<ContainerType, Ty, Blank, MatchFnTy> {
private:
  Vec2D<MatchScore> Matches;
  Vec2D<ScoreSystemType> Matrix;

  const static unsigned END = 0;
  const static unsigned DIAGONAL = 1;
  const static unsigned UP = 2;
  const static unsigned LEFT = 3;

  using BaseType = SequenceAligner<ContainerType, Ty, Blank, MatchFnTy>;

  void cacheAllMatches(ContainerType &Seq1, ContainerType &Seq2) {
    const size_t SizeSeq1 = Seq1.size();
    const size_t SizeSeq2 = Seq2.size();
    Matches.resize(SizeSeq1, SizeSeq2);

    if (BaseType::getMatchOperation() == nullptr) {
      for (unsigned i = 0; i < SizeSeq1; i++)
        for (unsigned j = 0; j < SizeSeq2; j++)
          Matches(i, j) = (Seq1[i] == Seq2[j]) ? MatchScore::MATCH : MatchScore::MISMATCH;
    } else {
      for (unsigned i = 0; i < SizeSeq1; i++)
        for (unsigned j = 0; j < SizeSeq2; j++)
          Matches(i, j) = BaseType::match(Seq1[i], Seq2[j]);
    }
  }

  void computeScoreMatrix(ContainerType &Seq1, ContainerType &Seq2) {
    const size_t SizeSeq1 = Seq1.size();
    const size_t SizeSeq2 = Seq2.size();

    const size_t NumRows = SizeSeq1 + 1;
    const size_t NumCols = SizeSeq2 + 1;
    Matrix.resize(NumRows, NumCols);

    ScoringSystem &Scoring = BaseType::getScoring();
    const ScoreSystemType Gap = Scoring.getGapPenalty();
    const ScoreSystemType Match = Scoring.getMatchProfit();
    const ScoreSystemType FullMatch = Scoring.getFullMatchProfit();
    const ScoreSystemType Mismatch = std::numeric_limits<ScoreSystemType>::min();

    for (unsigned i = 0; i < NumRows; i++)
      Matrix(i, 0) = i * Gap;
    for (unsigned j = 0; j < NumCols; j++)
      Matrix(0, j) = j * Gap;

    for (unsigned i = 1; i < NumRows; i++) {
      for (unsigned j = 1; j < NumCols; j++) {
        ScoreSystemType Diagonal = Mismatch;
        if (Matches(i - 1, j - 1) == MatchScore::FULL_MATCH)
          Diagonal = Matrix(i - 1, j - 1) + FullMatch;
        else if (Matches(i - 1, j - 1) == MatchScore::MATCH)
          Diagonal = Matrix(i - 1, j - 1) + Match;

        ScoreSystemType Upper = Matrix(i - 1, j) + Gap;
        ScoreSystemType Left = Matrix(i, j - 1) + Gap;
        ScoreSystemType Score = std::max(std::max(Diagonal, Upper), Left);
        Matrix(i, j) = Score;
      }
    }
  }

  AlignedSequence<Ty, Blank> buildResult(ContainerType &Seq1, ContainerType &Seq2) {
    AlignedSequence<Ty, Blank> Result;
    auto &Data = Result.Data;

    ScoringSystem &Scoring = BaseType::getScoring();
    const ScoreSystemType Gap = Scoring.getGapPenalty();
    const ScoreSystemType Match = Scoring.getMatchProfit();
    const ScoreSystemType FullMatch = Scoring.getFullMatchProfit();

    int i = Seq1.size(), j = Seq2.size();

    while (i > 0 || j > 0) {
      if (i > 0 && j > 0 && 
          (Matches(i - 1, j - 1) == MatchScore::FULL_MATCH) && 
          (Matrix(i, j) == (Matrix(i - 1, j - 1) + FullMatch))) {
        // Diagonal
        Data.push_front(typename BaseType::EntryType(Seq1[i - 1], Seq2[j - 1], true));
        --i;
        --j;
      } else if (i > 0 && j > 0 && 
          (Matches(i - 1, j - 1) == MatchScore::MATCH) && 
          (Matrix(i, j) == (Matrix(i - 1, j - 1) + Match))) {
        // Diagonal
        Data.push_front(typename BaseType::EntryType(Seq1[i - 1], Seq2[j - 1], true));
        --i;
        --j;
      } else if ((i > 0) && (Matrix(i, j) == (Matrix(i - 1, j) + Gap))) {
        // Up
        Data.push_front(
            typename BaseType::EntryType(Seq1[i - 1], Blank, false));
        --i;
      } else if ((j > 0) && (Matrix(i, j) == (Matrix(i, j - 1) + Gap))) {
        // Left
        Data.push_front(
            typename BaseType::EntryType(Blank, Seq2[j - 1], false));
        --j;
      } else {
        assert(false && "We should never get here");
      }
    }

    return Result;
  }

public:
  static ScoringSystem getDefaultScoring() { return ScoringSystem(-1, 2); }

  NeedlemanWunschSA() : BaseType(getDefaultScoring(), nullptr) {}

  NeedlemanWunschSA(ScoringSystem Scoring, MatchFnTy Match = nullptr)
      : BaseType(Scoring, Match) {}

  ~NeedlemanWunschSA() = default;

  virtual size_t getMemoryRequirement(ContainerType &Seq1,
                                      ContainerType &Seq2) override {
    const size_t SizeSeq1 = Seq1.size();
    const size_t SizeSeq2 = Seq2.size();
    size_t MemorySize = 0;

    MemorySize += sizeof(ScoreSystemType)*(SizeSeq1+1)*(SizeSeq2+1);

    if (BaseType::getMatchOperation() != nullptr)
      MemorySize += SizeSeq1*SizeSeq2*sizeof(MatchScore);

    return MemorySize;
  }

  virtual AlignedSequence<Ty, Blank> getAlignment(ContainerType &Seq1,
                                                  ContainerType &Seq2) override {
    cacheAllMatches(Seq1, Seq2);
    computeScoreMatrix(Seq1, Seq2);
    return buildResult(Seq1, Seq2);
  }
};

#endif
