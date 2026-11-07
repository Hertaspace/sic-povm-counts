#include <algorithm>
#include <array>
#include <cstdint>
#include <functional>
#include <iostream>
#include <map>
#include <unordered_set>
#include <vector>

// Independent audit: recursive ternary enumeration and the full SL(2,Z/d),
// rather than e01's integer-code enumeration and two-generator orbit walk.
using Mask = uint64_t;
using Relations = std::vector<std::vector<Mask>>;
int mod(int x, int d) { return (x % d + d) % d; }
Relations read_relations() {
  int n; std::cin >> n;
  Relations rels(n);
  for (auto &r : rels) {
    int k; std::cin >> k; r.resize(k);
    for (auto &m : r) std::cin >> m;
  }
  std::sort(rels.begin(), rels.end(), [](const auto &a, const auto &b) {
    return a.size() < b.size();
  });
  return rels;
}
bool passes(Mask support, const Relations &rels) {
  for (const auto &rel : rels) {
    int count = 0;
    for (auto monomial : rel)
      if ((support & monomial) == monomial && ++count > 1) break;
    if (count == 1) return false;
  }
  return true;
}
int main() {
  int d; std::cin >> d;
  auto square = read_relations(), minors = read_relations();
  std::vector<std::array<int,2>> pairs;
  for (int u=0; u<d; ++u) for (int v=0; v<d; ++v) {
    int q=d*u+v, r=d*mod(-u,d)+mod(-v,d);
    if (q<r) pairs.push_back({q,r});
  }
  std::vector<std::vector<int>> group;
  for (int a=0;a<d;++a) for(int b=0;b<d;++b)
    for(int c=0;c<d;++c) for(int e=0;e<d;++e) {
      if (mod(a*e-b*c,d)!=1) continue;
      std::vector<int> perm(d*d);
      for(int u=0;u<d;++u) for(int v=0;v<d;++v)
        perm[d*u+v]=d*mod(a*u+b*v,d)+mod(c*u+e*v,d);
      group.push_back(perm);
    }
  auto transform=[](Mask mask, const std::vector<int> &perm) {
    Mask value=0;
    while(mask) { int q=__builtin_ctzll(mask); mask&=mask-1;
      value |= Mask(1)<<perm[q]; }
    return value;
  };
  struct Orbit { uint64_t size=0; bool good=true; };
  std::map<Mask,Orbit> orbits;
  std::unordered_set<Mask> candidates;
  uint64_t size_ok=0, square_ok=0, minor_ok=0;
  std::function<void(size_t,Mask,int)> visit=[&](size_t i,Mask mask,int size) {
    if (size+int(pairs.size()-i)<d) return;
    if (i!=pairs.size()) {
      visit(i+1,mask,size);
      visit(i+1,mask|(Mask(1)<<pairs[i][0]),size+1);
      visit(i+1,mask|(Mask(1)<<pairs[i][1]),size+1);
      return;
    }
    ++size_ok;
    if (!passes(mask,square)) return;
    ++square_ok; candidates.insert(mask);
    bool good=passes(mask,minors); minor_ok+=good;
    Mask key=mask;
    for(const auto &perm:group) key=std::min(key,transform(mask,perm));
    auto &orbit=orbits[key]; ++orbit.size; orbit.good &= good;
  };
  visit(0,0,0);
  uint64_t closed=0,closed_orbits=0;
  for(const auto &[rep,orbit]:orbits) {
    std::unordered_set<Mask> transformed;
    for(const auto &perm:group) transformed.insert(transform(rep,perm));
    if(transformed.size()!=orbit.size) return 4;
    for(auto mask:transformed) if(!candidates.count(mask)) return 5;
    if(orbit.good) { closed+=orbit.size; ++closed_orbits; }
  }
  std::cout << "SUMMARY " << pairs.size() << ' ' << group.size() << ' '
            << size_ok << ' ' << square_ok << ' ' << minor_ok << ' '
            << orbits.size() << ' ' << closed << ' ' << closed_orbits << '\n';
  for(const auto &[rep,orbit]:orbits) if(orbit.good)
    std::cout << "ORBIT " << rep << ' ' << orbit.size << ' '
              << __builtin_popcountll(rep) << '\n';
}
