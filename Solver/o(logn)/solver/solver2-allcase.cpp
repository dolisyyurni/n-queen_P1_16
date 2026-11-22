#include "nqueens.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>

namespace {
void searchRows(int row, int n, uint32_t cols, uint32_t down, uint32_t up,
                const std::vector<uint32_t>* forbidden, std::vector<int>& cur,
                std::vector<std::vector<int>>& out) {
  if (row == n) {
    out.push_back(cur);
    NQ_SNAPSHOT(nq::queensOf(cur), "solution " + std::to_string(out.size()));
    return;
  }
  const uint32_t full = (uint32_t(1) << n) - 1;
  uint32_t avail = full & ~(cols | down | up);
  if (forbidden) avail &= ~(*forbidden)[row];
  while (avail) {
    const uint32_t bit = avail & -avail;
    avail ^= bit;
    cur[row] = __builtin_ctz(bit);
    searchRows(row + 1, n, cols | bit, ((down | bit) << 1) & full,
               (up | bit) >> 1, forbidden, cur, out);
  }
}

struct Bits {
  uint64_t w[3] = {0, 0, 0};
  void set(int i) { w[i >> 6] |= uint64_t(1) << (i & 63); }
  bool has(int i) const { return (w[i >> 6] >> (i & 63)) & 1; }
  bool any() const { return w[0] || w[1] || w[2]; }
  Bits without(const Bits& b) const { return {{w[0] & ~b.w[0], w[1] & ~b.w[1], w[2] & ~b.w[2]}}; }
  bool intersects(const Bits& b) const { return (w[0]&b.w[0]) || (w[1]&b.w[1]) || (w[2]&b.w[2]); }
};

class WalledSolver {
  using Board = std::vector<std::pair<int,int>>;
  int n;
  const std::vector<std::string>& grid;
  std::vector<std::pair<int,int>> cells;
  std::vector<Bits> conflict, groups, groupMasks;
  Board cur;
  std::vector<Board> answers;
  int best = 0;

  bool attacks(int a, int b) const {
    int r1=cells[a].first, c1=cells[a].second, r2=cells[b].first, c2=cells[b].second;
    int dr=(r2>r1)-(r2<r1), dc=(c2>c1)-(c2<c1);
    if (!(r1==r2 || c1==c2 || std::abs(r1-r2)==std::abs(c1-c2))) return false;
    for (int r=r1+dr,c=c1+dc; r!=r2 || c!=c2; r+=dr,c+=dc)
      if (grid[r][c]=='W') return false;
    return true;
  }
  void dfs(int g, const Bits& available) {
    if (static_cast<int>(cur.size()) + static_cast<int>(groups.size()-g) < best) return;
    if (g == static_cast<int>(groups.size())) {
      int count=static_cast<int>(cur.size());
      if (count > best) { best=count; answers.clear(); }
      if (count == best && count > 0) {
        answers.push_back(cur);
        NQ_SNAPSHOT(cur, "best board: " + std::to_string(best) + " queens");
      }
      return;
    }
    int possible=0;
    for (int i=g;i<(int)groups.size();++i) if (groups[i].intersects(available)) ++possible;
    if ((int)cur.size()+possible < best) return;

    for (int cell : segmentCells[g]) {
      if (!available.has(cell)) continue;
      cur.push_back(cells[cell]);
      dfs(g+1, available.without(conflict[cell]));
      cur.pop_back();
    }
    dfs(g+1, available);
  }
  std::vector<std::vector<int>> segmentCells;

 public:
  WalledSolver(int size, const std::vector<std::string>& board): n(size), grid(board) {
    for(int r=0;r<n;++r) for(int c=0;c<n;++c) if(grid[r][c]!='W') cells.emplace_back(r,c);
    int m=(int)cells.size();
    if(m>192) return;
    conflict.resize(m);
    for(int i=0;i<m;++i) for(int j=0;j<m;++j) if(i!=j && attacks(i,j)) conflict[i].set(j);
    for(int r=0;r<n;++r) {
      std::vector<int> seg;
      for(int c=0;c<n;++c) {
        if(grid[r][c]=='W') { if(!seg.empty()) { segmentCells.push_back(seg); seg.clear(); } }
        else {
          int idx=0; 
          int lo=0,hi=m;
          while(lo<hi) { int mid=(lo+hi)/2; if(cells[mid]<std::make_pair(r,c)) lo=mid+1; else hi=mid; }
          idx=lo; seg.push_back(idx);
        }
      }
      if(!seg.empty()) segmentCells.push_back(seg);
    }
    groups.resize(segmentCells.size());
    for(int g=0;g<(int)segmentCells.size();++g) for(int i:segmentCells[g]) groups[g].set(i);
  }
  std::vector<Board> run() {
    if(cells.empty() || cells.size()>192) return {};
    Bits all; for(int i=0;i<(int)cells.size();++i) all.set(i);
    dfs(0,all);
    return std::move(answers);
  }
};

}

// CASE 1 — NORMAL
// Tempatkan satu ratu per baris pada papan kosong. searchRows memakai bitmask
// untuk kolom dan dua diagonal; setiap solusi dikembalikan sebagai daftar
// kolom, dengan indeks baris sebagai posisi di dalam daftar.
std::vector<std::vector<int>> solveNQueens(int n) {
  std::vector<std::vector<int>> out;
  if(n<1 || n>31) return out;
  std::vector<int> cur(n);
  searchRows(0,n,0,0,0,nullptr,cur,out);
  return out;
}

// CASE 2 — PRE-PLACED
// Ratu yang sudah ditentukan dipertahankan pada koordinatnya. Input divalidasi
// lebih dulu agar tidak ada dua ratu tetap pada baris, kolom, atau diagonal yang
// sama. Saat pencarian, baris tetap hanya boleh memilih kolom yang ditentukan;
// baris lain tidak boleh memakai kolom ratu tetap.
std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int,int>>& fixed) {
  std::vector<std::vector<int>> out;
  if(n<1 || n>31) return out;
  std::vector<int> col(n,-1), rowOfCol(n,-1);
  for(auto q:fixed) {
    if(q.first<0 || q.first>=n || q.second<0 || q.second>=n || col[q.first]>=0 || rowOfCol[q.second]>=0) return out;
    col[q.first]=q.second; rowOfCol[q.second]=q.first;
  }
  for(int i=0;i<(int)fixed.size();++i) for(int j=i+1;j<(int)fixed.size();++j)
    if(std::abs(fixed[i].first-fixed[j].first)==std::abs(fixed[i].second-fixed[j].second)) return out;

  std::vector<int> cur(n,-1);
  auto visit = [&](auto&& self,int r,uint32_t c,uint32_t d,uint32_t u)->void {
    if(r==n) { out.push_back(cur); NQ_SNAPSHOT(nq::queensOf(cur), "solution " + std::to_string(out.size())); return; }
    uint32_t full=(uint32_t(1)<<n)-1, avail=full & ~(c|d|u);
    if(col[r]>=0) avail &= uint32_t(1)<<col[r];
    else for(int x=0;x<n;++x) if(rowOfCol[x]>=0) avail &= ~(uint32_t(1)<<x);
    while(avail) { uint32_t b=avail&-avail; avail^=b; cur[r]=__builtin_ctz(b); self(self,r+1,c|b,((d|b)<<1)&full,(u|b)>>1); }
  };
  visit(visit,0,0,0,0);
  return out;
}

// CASE 3 — HOLES
// Sel bertanda 'H' tidak boleh ditempati ratu, tetapi tidak menghalangi
// serangan. Karena itu, posisi lubang dibuat menjadi bit terlarang per baris,
// lalu pencarian bitmask yang sama dengan kasus Normal digunakan.
std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  std::vector<std::vector<int>> out;
  if(n<1 || n>31 || (int)grid.size()!=n) return out;
  std::vector<uint32_t> forbidden(n,0);
  for(int r=0;r<n;++r) {
    if((int)grid[r].size()!=n) return {};
    for(int c=0;c<n;++c) if(grid[r][c]=='H') forbidden[r] |= uint32_t(1)<<c;
  }
  std::vector<int> cur(n);
  searchRows(0,n,0,0,0,&forbidden,cur,out);
  return out;
}

// CASE 4 — WALLED
// Dinding 'W' tidak dapat ditempati dan menghentikan serangan yang melewatinya.
// WalledSolver membagi tiap baris menjadi segmen bebas dinding, lalu mencari
// susunan dengan jumlah ratu maksimum. Branch-and-bound memangkas cabang yang
// tidak mungkin menyamai jumlah terbaik yang sudah ditemukan; semua susunan
// optimal dikembalikan sebagai daftar koordinat (baris, kolom).
std::vector<std::vector<std::pair<int,int>>> solveWalled(int n, const std::vector<std::string>& grid) {
  if(n<1 || n>12 || (int)grid.size()!=n) return {};
  for(const auto& row:grid) if((int)row.size()!=n) return {};
  return WalledSolver(n,grid).run();
}
