#include "nqueens.h"
#include <cstdint>
#include <string>
#include <vector>

namespace {
void searchRows(int row, int n, uint32_t cols, uint32_t down, uint32_t up,
                const std::vector<uint32_t>& holes, std::vector<int>& cur,
                std::vector<std::vector<int>>& out) {
  if(row==n) { out.push_back(cur); NQ_SNAPSHOT(nq::queensOf(cur), "solution " + std::to_string(out.size())); return; }
  const uint32_t full=(uint32_t(1)<<n)-1;
  uint32_t avail=full&~(cols|down|up|holes[row]);
  while(avail) { uint32_t bit=avail&-avail; avail^=bit; cur[row]=__builtin_ctz(bit);
    searchRows(row+1,n,cols|bit,((down|bit)<<1)&full,(up|bit)>>1,holes,cur,out); }
}
}

// CASE HOLES: 'H' tidak boleh ditempati, tetapi serangan tetap melewati hole.
// Karena itu hole hanya menghapus pilihan kolom pada baris terkait.
std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  std::vector<std::vector<int>> out;
  if(n<1 || n>31 || (int)grid.size()!=n) return out;
  std::vector<uint32_t> holes(n,0);
  for(int r=0;r<n;++r) {
    if((int)grid[r].size()!=n) return {};
    for(int c=0;c<n;++c) if(grid[r][c]=='H') holes[r]|=uint32_t(1)<<c;
  }
  std::vector<int> cur(n);
  searchRows(0,n,0,0,0,holes,cur,out);
  return out;
}
