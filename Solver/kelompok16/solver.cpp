#include "nqueens.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>

namespace {

constexpr long long SNAPSHOT_INTERVAL = 1000;

// Normal N-Queens with bitmask backtracking
void dfsNormal(int r, int n, int cols, int d1, int d2,
               std::vector<int>& cur,
               std::vector<std::vector<int>>& solutions,
               long long& debugCount) {
  if (r == n) {
    solutions.push_back(cur);
    NQ_SNAPSHOT(nq::queensOf(cur), "solution " + std::to_string(solutions.size()));
    return;
  }

  int avail = (~(cols | d1 | d2)) & ((1 << n) - 1);
  if (!avail && snapshotsEnabled() && (++debugCount == 1 || debugCount % SNAPSHOT_INTERVAL == 0)) {
    snapshot(nq::queensOf(cur), "dead end at row " + std::to_string(r));
  }

  while (avail) {
    int bit = avail & -avail;
    int c = __builtin_ctz(bit);
    avail &= ~bit;

    cur[r] = c;
    dfsNormal(r + 1, n, cols | bit, (d1 | bit) << 1, (d2 | bit) >> 1, cur, solutions, debugCount);
  }
}

// Pre-placed queens
void dfsPreplaced(int r, int n, int cols, int d1, int d2,
                  const std::vector<int>& fixedCol,
                  const std::vector<int>& fixedRow,
                  std::vector<int>& cur,
                  std::vector<std::vector<int>>& solutions,
                  long long& debugCount) {
  if (r == n) {
    solutions.push_back(cur);
    NQ_SNAPSHOT(nq::queensOf(cur), "solution " + std::to_string(solutions.size()));
    return;
  }

  if (fixedCol[r] >= 0) {
    int c = fixedCol[r];
    int bit = 1 << c;
    int d1_bit = 1 << (r - c + n - 1);
    int d2_bit = 1 << (r + c);

    if ((cols & bit) || (d1 & d1_bit) || (d2 & d2_bit)) {
      if (snapshotsEnabled() && (++debugCount == 1 || debugCount % SNAPSHOT_INTERVAL == 0)) {
        snapshot(nq::queensOf(cur), "conflict at fixed row " + std::to_string(r));
      }
      return;
    }

    cur[r] = c;
    dfsPreplaced(r + 1, n, cols | bit, d1 | d1_bit, d2 | d2_bit,
                 fixedCol, fixedRow, cur, solutions, debugCount);
  } else {
    for (int c = 0; c < n; ++c) {
      if (fixedRow[c] >= 0) continue;

      int bit = 1 << c;
      int d1_bit = 1 << (r - c + n - 1);
      int d2_bit = 1 << (r + c);

      if ((cols & bit) || (d1 & d1_bit) || (d2 & d2_bit)) continue;

      cur[r] = c;
      dfsPreplaced(r + 1, n, cols | bit, d1 | d1_bit, d2 | d2_bit,
                   fixedCol, fixedRow, cur, solutions, debugCount);
    }
  }
}

// N-Queens with holes
void dfsHoles(int r, int n, int cols, int d1, int d2,
              const std::vector<int>& holeMask,
              std::vector<int>& cur,
              std::vector<std::vector<int>>& solutions,
              long long& debugCount) {
  if (r == n) {
    solutions.push_back(cur);
    NQ_SNAPSHOT(nq::queensOf(cur), "solution " + std::to_string(solutions.size()));
    return;
  }

  int avail = (~(cols | d1 | d2 | holeMask[r])) & ((1 << n) - 1);
  if (!avail && snapshotsEnabled() && (++debugCount == 1 || debugCount % SNAPSHOT_INTERVAL == 0)) {
    snapshot(nq::queensOf(cur), "dead end at row " + std::to_string(r));
  }

  while (avail) {
    int bit = avail & -avail;
    int c = __builtin_ctz(bit);
    avail &= ~bit;

    cur[r] = c;
    dfsHoles(r + 1, n, cols | bit, (d1 | bit) << 1, (d2 | bit) >> 1, holeMask, cur, solutions, debugCount);
  }
}

using Board = std::vector<std::pair<int, int>>;

// Bitmask for up to 12x12 cells
struct Mask144 {
  uint64_t w0 = 0;
  uint64_t w1 = 0;
  uint64_t w2 = 0;

  void set(int bit) {
    if (bit < 64) {
      w0 |= (1ULL << bit);
    } else if (bit < 128) {
      w1 |= (1ULL << (bit - 64));
    } else {
      w2 |= (1ULL << (bit - 128));
    }
  }

  bool get(int bit) const {
    if (bit < 64) return (w0 & (1ULL << bit)) != 0;
    if (bit < 128) return (w1 & (1ULL << (bit - 64))) != 0;
    return (w2 & (1ULL << (bit - 128))) != 0;
  }

  bool intersects(const Mask144& o) const {
    return (w0 & o.w0) || (w1 & o.w1) || (w2 & o.w2);
  }

  Mask144 operator&(const Mask144& o) const {
    return {w0 & o.w0, w1 & o.w1, w2 & o.w2};
  }

  Mask144 operator~() const {
    return {~w0, ~w1, ~w2};
  }
};

// Walled case: branch-and-bound over horizontal segments
class WalledSearch {
 public:
  WalledSearch(int n, const std::vector<std::string>& grid) : n_(n), grid_(grid) {
    for (int r = 0; r < n_; ++r) {
      for (int c = 0; c < n_; ++c) {
        if (grid_[r][c] != 'W') {
          cellCoords_.emplace_back(r, c);
        }
      }
    }
    numCells_ = static_cast<int>(cellCoords_.size());

    conflicts_.assign(numCells_, Mask144());
    for (int i = 0; i < numCells_; ++i) {
      for (int j = 0; j < numCells_; ++j) {
        if (i != j && attacks(cellCoords_[i].first, cellCoords_[i].second,
                              cellCoords_[j].first, cellCoords_[j].second)) {
          conflicts_[i].set(j);
        }
      }
    }

    int cellIdx = 0;
    for (int r = 0; r < n_; ++r) {
      std::vector<int> currentSeg;
      for (int c = 0; c < n_; ++c) {
        if (grid_[r][c] != 'W') {
          currentSeg.push_back(cellIdx++);
        } else {
          if (!currentSeg.empty()) {
            segments_.push_back(currentSeg);
            currentSeg.clear();
          }
        }
      }
      if (!currentSeg.empty()) {
        segments_.push_back(currentSeg);
      }
    }
    numSegments_ = static_cast<int>(segments_.size());

    segmentMasks_.assign(numSegments_, Mask144());
    for (int s = 0; s < numSegments_; ++s) {
      for (int cell : segments_[s]) {
        segmentMasks_[s].set(cell);
      }
    }
  }

  std::vector<Board> run() {
    if (numCells_ == 0) return {};

    runGreedy();

    Mask144 initialAvail;
    for (int i = 0; i < numCells_; ++i) initialAvail.set(i);

    dfs(0, initialAvail);
    return std::move(best_);
  }

 private:
  const int n_;
  const std::vector<std::string>& grid_;
  std::vector<std::pair<int, int>> cellCoords_;
  int numCells_ = 0;
  std::vector<Mask144> conflicts_;
  std::vector<std::vector<int>> segments_;
  std::vector<Mask144> segmentMasks_;
  int numSegments_ = 0;

  Board queens_;
  std::vector<Board> best_;
  size_t bestSize_ = 0;
  long long debugCount_ = 0;

  static int sign(int x) { return (x > 0) - (x < 0); }

  bool attacks(int r1, int c1, int r2, int c2) const {
    const bool sameLine = r1 == r2 || c1 == c2 || std::abs(r1 - r2) == std::abs(c1 - c2);
    if (!sameLine) return false;
    const int dr = sign(r2 - r1), dc = sign(c2 - c1);
    for (int r = r1 + dr, c = c1 + dc; r != r2 || c != c2; r += dr, c += dc) {
      if (grid_[r][c] == 'W') return false;
    }
    return true;
  }

  void runGreedy() {
    Mask144 avail;
    for (int i = 0; i < numCells_; ++i) avail.set(i);
    size_t count = 0;
    for (int s = 0; s < numSegments_; ++s) {
      for (int cell : segments_[s]) {
        if (avail.get(cell)) {
          count++;
          avail = avail & ~conflicts_[cell];
          break;
        }
      }
    }
    bestSize_ = count;
  }

  void dfs(int segIdx, const Mask144& avail) {
    if (queens_.size() + (numSegments_ - segIdx) < bestSize_) {
      return;
    }

    if (segIdx == numSegments_) {
      if (queens_.size() > bestSize_) {
        best_.clear();
        bestSize_ = queens_.size();
        best_.push_back(queens_);
        NQ_SNAPSHOT(queens_, "new record: " + std::to_string(bestSize_) + " queens");
      } else if (queens_.size() == bestSize_ && bestSize_ > 0) {
        best_.push_back(queens_);
        NQ_SNAPSHOT(queens_, "another board with " + std::to_string(bestSize_) + " queens");
      }
      return;
    }

    int remainingPossible = 0;
    for (int s = segIdx; s < numSegments_; ++s) {
      if (segmentMasks_[s].intersects(avail)) {
        remainingPossible++;
      }
    }
    if (queens_.size() + remainingPossible < bestSize_) {
      return;
    }

    for (int cell : segments_[segIdx]) {
      if (avail.get(cell)) {
        queens_.push_back(cellCoords_[cell]);
        Mask144 nextAvail = avail & ~conflicts_[cell];
        dfs(segIdx + 1, nextAvail);
        queens_.pop_back();
      }
    }

    dfs(segIdx + 1, avail);
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  std::vector<std::vector<int>> solutions;
  std::vector<int> cur(n);
  long long debugCount = 0;
  dfsNormal(0, n, 0, 0, 0, cur, solutions, debugCount);
  return solutions;
}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<std::vector<int>> solutions;
  std::vector<int> fixedCol(n, -1);
  std::vector<int> fixedRow(n, -1);

  for (const auto& q : preplaced) {
    if (q.first < 0 || q.first >= n || q.second < 0 || q.second >= n) return {};
    if (fixedCol[q.first] >= 0 || fixedRow[q.second] >= 0) return {};
    fixedCol[q.first] = q.second;
    fixedRow[q.second] = q.first;
  }

  for (size_t i = 0; i < preplaced.size(); ++i) {
    for (size_t j = i + 1; j < preplaced.size(); ++j) {
      if (std::abs(preplaced[i].first - preplaced[j].first) ==
          std::abs(preplaced[i].second - preplaced[j].second)) {
        return {};
      }
    }
  }

  std::vector<int> cur(n);
  long long debugCount = 0;
  dfsPreplaced(0, n, 0, 0, 0, fixedCol, fixedRow, cur, solutions, debugCount);
  return solutions;
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  std::vector<std::vector<int>> solutions;
  std::vector<int> holeMask(n, 0);

  for (int r = 0; r < n; ++r) {
    for (int c = 0; c < n; ++c) {
      if (grid[r][c] == 'H') {
        holeMask[r] |= (1 << c);
      }
    }
  }

  std::vector<int> cur(n);
  long long debugCount = 0;
  dfsHoles(0, n, 0, 0, 0, holeMask, cur, solutions, debugCount);
  return solutions;
}

std::vector<std::vector<std::pair<int, int>>> solveWalled(int n, const std::vector<std::string>& grid) {
  return WalledSearch(n, grid).run();
}
