#include "nqueens.h"
#include <cstdint>
#include <string>
#include <vector>

namespace {
void searchRows(int row, int n, uint32_t cols, uint32_t down, uint32_t up,
                const std::vector<uint32_t>* forbidden, std::vector<int>& cur,
                std::vector<std::vector<int>>& out) {
  if (row == n) { out.push_back(cur); NQ_SNAPSHOT(nq::queensOf(cur), "solution " + std::to_string(out.size())); return; }
  const uint32_t full=(uint32_t(1)<<n)-1;
  uint32_t avail=full & ~(cols|down|up);
  if(forbidden) avail &= ~(*forbidden)[row];
  while(avail) { uint32_t bit=avail&-avail; avail^=bit; cur[row]=__builtin_ctz(bit);
    searchRows(row+1,n,cols|bit,((down|bit)<<1)&full,(up|bit)>>1,forbidden,cur,out); }
}
}

// CASE NORMAL: satu ratu per baris pada papan kosong. Bitmask membuat
// pemeriksaan kolom dan diagonal menjadi operasi bit yang konstan.
std::vector<std::vector<int>> solveNQueens(int n) {
  std::vector<std::vector<int>> out;
  if(n<1 || n>31) return out;
  std::vector<int> cur(n);
  searchRows(0,n,0,0,0,nullptr,cur,out);
  return out;
}
