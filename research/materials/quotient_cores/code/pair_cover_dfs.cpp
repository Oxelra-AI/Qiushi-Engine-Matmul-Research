// analysis: DFS combining repaired signed-pair propagation with residual-cover pruning.
//
// This file starts from pair_prop_dfs.cpp and adds the sound cover test
// from cover_bitset_dfs.cpp.  Constraint rows drive ordinary Wang
// saturation and over-cap rejection.  Pair rows generate signed pair
// inequalities.  Cover rows are genuine upper-bound rows checked by
// u + |future outside R| < need.  No lower fill obligation is introduced.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

static constexpr int MAXP=255;
static constexpr int WORDS=4;
static bool bit4(const uint64_t w[WORDS], int p){ return (w[p>>6]>>(p&63))&1ULL; }
static void setbit4(uint64_t w[WORDS], int p){ w[p>>6] |= 1ULL<<(p&63); }
static void clrbit4(uint64_t w[WORDS], int p){ w[p>>6] &= ~(1ULL<<(p&63)); }
static int pop4(const uint64_t w[WORDS]){ return __builtin_popcountll(w[0])+__builtin_popcountll(w[1])+__builtin_popcountll(w[2])+__builtin_popcountll(w[3]); }

struct Row{ uint8_t cap=0, dim=0; uint16_t reserved=0; uint64_t word[WORDS]={0,0,0,0}; };
struct CoverCert{ int row=-1, cap=0, count=0, residual=0, future_in=0, future_out=0, need=0, avail=0, depth=0; };
struct PairIneq{ uint64_t I[WORDS]; uint64_t O[WORDS]; int threshold=0, I_size=0, O_size=0; };
struct Result{
  int branch=-1, rep=0, target=0, max_depth=0; double elapsed_sec=0.0;
  bool timeout=false, complete=false, forced_infeasible=false;
  uint64_t calls=0,candidate_tests=0,overcap_rejects=0,cover_overcap_rejects=0,global_shortage=0;
  uint64_t saturated_rows=0,saturation_removed_points=0,initial_cap0_removed=0,solutions=0;
  uint64_t pair_checks=0,pair_prunes=0,pair_propagations=0,pair_exclusions=0,pair_forces=0,pair_cascade_rounds=0;
  uint64_t cover_checks=0,cover_row_tests=0,cover_prunes=0,cover_skips=0;
  std::array<uint64_t,32> nodes{}, pair_depth{}, cover_depth{};
  std::vector<std::vector<int>> sol_head; std::vector<CoverCert> cover_certs;
};
static std::string arr_json(const std::array<uint64_t,32>& a,int upto){ std::ostringstream o; o<<"["; for(int i=0;i<=upto && i<(int)a.size();i++){ if(i)o<<","; o<<a[i]; } o<<"]"; return o.str(); }
static std::string vec_json(const std::vector<int>& v){ std::ostringstream o; o<<"["; for(size_t i=0;i<v.size();i++){ if(i)o<<","; o<<v[i]; } o<<"]"; return o.str(); }
static std::string sols_json(const std::vector<std::vector<int>>& vv){ std::ostringstream o; o<<"["; for(size_t i=0;i<vv.size();i++){ if(i)o<<","; o<<vec_json(vv[i]); } o<<"]"; return o.str(); }
static std::string certs_json(const std::vector<CoverCert>& cc){ std::ostringstream o; o<<"["; for(size_t i=0;i<cc.size();i++){ if(i)o<<","; const auto& c=cc[i]; o<<"{\"row\":"<<c.row<<",\"cap\":"<<c.cap<<",\"count\":"<<c.count<<",\"residual\":"<<c.residual<<",\"future_in\":"<<c.future_in<<",\"future_out\":"<<c.future_out<<",\"need\":"<<c.need<<",\"avail\":"<<c.avail<<",\"depth\":"<<c.depth<<"}"; } o<<"]"; return o.str(); }

static bool load_rows(const std::string& path, std::vector<Row>& rows){
  if(path.empty()) return true; std::ifstream in(path,std::ios::binary); if(!in){ std::cerr<<"cannot open "<<path<<"\n"; return false; }
  char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"E11WANG1",8)!=0){ std::cerr<<"bad row magic "<<path<<"\n"; return false; }
  uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); rows.resize(n);
  for(uint32_t i=0;i<n;i++){ in.read(reinterpret_cast<char*>(&rows[i].cap),1); in.read(reinterpret_cast<char*>(&rows[i].dim),1); in.read(reinterpret_cast<char*>(&rows[i].reserved),2); for(int w=0;w<WORDS;w++) in.read(reinterpret_cast<char*>(&rows[i].word[w]),8); }
  if(!in){ std::cerr<<"short read "<<path<<"\n"; return false; } return true;
}
static std::vector<std::vector<uint32_t>> point_rows(const std::vector<Row>& rows){ std::vector<std::vector<uint32_t>> pr(256); for(uint32_t i=0;i<rows.size();i++) for(int p=1;p<=MAXP;p++) if(bit4(rows[i].word,p)) pr[p].push_back(i); return pr; }
static std::vector<int> parse_list(const std::string& s){ std::vector<int> v; if(s.empty()) return v; size_t pos=0; while(pos<s.size()){ size_t nx=s.find(',',pos); if(nx==std::string::npos) nx=s.size(); if(nx>pos){ int p=std::stoi(s.substr(pos,nx-pos)); if(1<=p && p<=MAXP) v.push_back(p); } pos=nx+1; } std::sort(v.begin(),v.end()); v.erase(std::unique(v.begin(),v.end()),v.end()); return v; }

struct Searcher{
  const std::vector<Row>& rows; const std::vector<std::vector<uint32_t>>& pr;
  const std::vector<Row>& cov; const std::vector<std::vector<uint32_t>>& cpr;
  std::vector<PairIneq> pairs; std::vector<std::vector<uint32_t>> pt_in_I, pt_in_O;
  int target; double limit; int cover_min_depth; int cover_max_slack;
  std::chrono::steady_clock::time_point start;
  std::vector<uint8_t> cnt, ccnt; std::vector<int16_t> pair_margin;
  uint64_t dom[WORDS], mandatory[WORDS]; std::vector<int> chosen; Result res;
  Searcher(const std::vector<Row>& r,const std::vector<std::vector<uint32_t>>& p,const std::vector<Row>& cr,const std::vector<std::vector<uint32_t>>& cp,const std::vector<Row>& pair_rows,int t,double lim,int cmd,int cms)
    : rows(r), pr(p), cov(cr), cpr(cp), target(t), limit(lim), cover_min_depth(cmd), cover_max_slack(cms), cnt(r.size(),0), ccnt(cr.size(),0) {
    int nr=(int)pair_rows.size();
    for(int i=0;i<nr;i++) for(int j=i+1;j<nr;j++){ PairIneq pi; uint64_t U[WORDS]; for(int w=0;w<WORDS;w++){ pi.I[w]=pair_rows[i].word[w]&pair_rows[j].word[w]; U[w]=pair_rows[i].word[w]|pair_rows[j].word[w]; pi.O[w]=~U[w]; } pi.O[0]&=~1ULL; pi.threshold=target-(int)pair_rows[i].cap-(int)pair_rows[j].cap; pi.I_size=pop4(pi.I); pi.O_size=pop4(pi.O); if(pi.threshold>0) pairs.push_back(pi); }
    pair_margin.resize(pairs.size(),0); pt_in_I.resize(256); pt_in_O.resize(256); for(uint32_t i=0;i<pairs.size();i++) for(int pnt=1;pnt<=MAXP;pnt++){ if(bit4(pairs[i].I,pnt)) pt_in_I[pnt].push_back(i); if(bit4(pairs[i].O,pnt)) pt_in_O[pnt].push_back(i); }
    std::cerr<<"Built "<<pairs.size()<<" pair inequalities from "<<nr<<" rows\n";
  }
  bool timed() const { return limit>0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=limit; }
  void full_domain(){ dom[0]=dom[1]=dom[2]=dom[3]=~0ULL; dom[0]&=~1ULL; }
  bool in_dom(int p) const { return bit4(dom,p); }
  void remove_dom(int p){ clrbit4(dom,p); }
  int avail_from(int minp) const { int c=0; for(int p=minp;p<=MAXP;p++) if(in_dom(p)) c++; return c; }
  void future_words(int minp,uint64_t out[WORDS]) const { for(int w=0;w<WORDS;w++) out[w]=dom[w]; if(minp>1) for(int p=1;p<minp && p<=MAXP;p++) clrbit4(out,p); }
  void init_pair_margins(){ for(size_t pi=0;pi<pairs.size();pi++){ int ao=0; for(int p=1;p<=MAXP;p++) if(in_dom(p)&&bit4(pairs[pi].O,p)) ao++; pair_margin[pi]=(int16_t)(ao-pairs[pi].threshold); } }
  void update_margins_select(int q){ for(uint32_t pi:pt_in_I[q]) pair_margin[pi]--; }
  void update_margins_domain_remove(int q){ for(uint32_t pi:pt_in_O[q]) pair_margin[pi]--; }
  bool cover_possible(int minp,int need){
    if(cov.empty()) return true; uint64_t fut[WORDS]; future_words(minp,fut); int avail=pop4(fut); int depth=(int)chosen.size(); int slack=avail-need;
    bool threshold=(need==0)||(depth>=cover_min_depth)||(cover_max_slack>=0 && slack<=cover_max_slack); if(!threshold){ res.cover_skips++; return true; }
    res.cover_checks++;
    for(size_t i=0;i<cov.size();i++){ int u=(int)cov[i].cap-(int)ccnt[i]; if(u>=need) continue; res.cover_row_tests++; if(u<0){ res.cover_prunes++; if(depth<(int)res.cover_depth.size()) res.cover_depth[depth]++; if(res.cover_certs.size()<5) res.cover_certs.push_back({(int)i,(int)cov[i].cap,(int)ccnt[i],u,0,avail,need,avail,depth}); return false; } uint64_t a[WORDS]; for(int w=0;w<WORDS;w++) a[w]=fut[w]&cov[i].word[w]; int in=pop4(a); int outside=avail-in; if(u+outside<need){ res.cover_prunes++; if(depth<(int)res.cover_depth.size()) res.cover_depth[depth]++; if(res.cover_certs.size()<5) res.cover_certs.push_back({(int)i,(int)cov[i].cap,(int)ccnt[i],u,in,outside,need,avail,depth}); return false; } }
    return true;
  }
  bool propagate_pairs(int minp,std::vector<int>& removed,std::vector<int>& forced){
    bool changed=true; while(changed){ changed=false; res.pair_cascade_rounds++; for(size_t pi=0;pi<pairs.size();pi++){ if(pair_margin[pi]<0){ res.pair_prunes++; int d=(int)chosen.size(); if(d<(int)res.pair_depth.size()) res.pair_depth[d]++; return false; } if(pair_margin[pi]==0){ res.pair_propagations++; for(int p=1;p<=MAXP;p++) if(in_dom(p)&&bit4(pairs[pi].I,p)){ remove_dom(p); removed.push_back(p); res.pair_exclusions++; update_margins_domain_remove(p); changed=true; } for(int p=minp;p<=MAXP;p++) if(in_dom(p)&&bit4(pairs[pi].O,p)&&!bit4(mandatory,p)){ setbit4(mandatory,p); forced.push_back(p); res.pair_forces++; } } } }
    return true;
  }
  bool terminal_pairs_ok(){ for(size_t pi=0;pi<pairs.size();pi++){ int lhs=0; for(int q:chosen){ if(bit4(pairs[pi].O,q)) lhs++; if(bit4(pairs[pi].I,q)) lhs--; } if(lhs<pairs[pi].threshold){ res.pair_prunes++; int d=(int)chosen.size(); if(d<(int)res.pair_depth.size()) res.pair_depth[d]++; return false; } } return true; }
  bool try_select(int q,std::vector<uint32_t>& touched,std::vector<uint32_t>& ctouched,uint64_t olddom[WORDS]){
    res.candidate_tests++; for(int w=0;w<WORDS;w++) olddom[w]=dom[w]; if(!in_dom(q)) return false;
    for(uint32_t ri:pr[q]) if((int)cnt[ri]+1>(int)rows[ri].cap){ res.overcap_rejects++; return false; }
    for(uint32_t ri:cpr[q]) if((int)ccnt[ri]+1>(int)cov[ri].cap){ res.cover_overcap_rejects++; return false; }
    remove_dom(q); for(uint32_t ri:pr[q]){ cnt[ri]++; touched.push_back(ri); } for(uint32_t ri:cpr[q]){ ccnt[ri]++; ctouched.push_back(ri); }
    for(uint32_t ri:touched) if(cnt[ri]==rows[ri].cap){ res.saturated_rows++; for(int p=1;p<=MAXP;p++) if(in_dom(p)&&bit4(rows[ri].word,p)){ remove_dom(p); res.saturation_removed_points++; update_margins_domain_remove(p); } }
    update_margins_select(q); return true;
  }
  bool force_points(const std::vector<int>& force){ for(int p:force){ if(!in_dom(p)){ res.forced_infeasible=true; return false; } std::vector<uint32_t> t,ct; uint64_t old[WORDS]; if(!try_select(p,t,ct,old)){ res.forced_infeasible=true; return false; } chosen.push_back(p); } return true; }
  void restore_pair_state(const std::vector<int16_t>& saved,const std::vector<int>& removed,const std::vector<int>& forced){ for(size_t i=0;i<pairs.size();i++) pair_margin[i]=saved[i]; for(int p:removed) setbit4(dom,p); for(int p:forced) clrbit4(mandatory,p); }
  void dfs(int minp){
    if(res.timeout) return; if((res.calls++ & 0x3FFFULL)==0 && timed()){ res.timeout=true; return; }
    int d=(int)chosen.size(); if(d>res.max_depth) res.max_depth=d;
    if(d==target){ if(!cover_possible(MAXP+1,0)) return; if(!terminal_pairs_ok()) return; res.solutions++; if(res.sol_head.size()<5){ auto s=chosen; std::sort(s.begin(),s.end()); res.sol_head.push_back(s); } return; }
    int need=target-d; int avail=avail_from(minp); if(avail<need){ res.global_shortage++; return; }
    res.pair_checks++; std::vector<int16_t> saved(pair_margin); std::vector<int> removed,forced;
    if(!propagate_pairs(minp,removed,forced)){ restore_pair_state(saved,removed,forced); return; }
    avail=avail_from(minp); if(avail<need){ res.global_shortage++; restore_pair_state(saved,removed,forced); return; }
    if(!cover_possible(minp,need)){ restore_pair_state(saved,removed,forced); return; }
    uint64_t prop_dom[WORDS]; for(int w=0;w<WORDS;w++) prop_dom[w]=dom[w];
    for(int q=minp;q<=MAXP;q++){
      if(MAXP-q+1<need) break; if(!in_dom(q)) continue; if(avail_from(q)<need) break; bool ismand=bit4(mandatory,q);
      std::vector<uint32_t> touched,ctouched; uint64_t old[WORDS]; std::vector<int16_t> child_margins(pair_margin); bool ok=try_select(q,touched,ctouched,old);
      if(ok){ std::vector<int> child_removed,child_forced; bool pair_ok=true; for(size_t pi=0;pi<pairs.size();pi++) if(pair_margin[pi]<0){ pair_ok=false; res.pair_prunes++; int dd=(int)chosen.size()+1; if(dd<(int)res.pair_depth.size()) res.pair_depth[dd]++; break; } if(pair_ok) pair_ok=propagate_pairs(q+1,child_removed,child_forced); if(pair_ok){ chosen.push_back(q); int nd=(int)chosen.size(); if(nd<(int)res.nodes.size()) res.nodes[nd]++; dfs(q+1); chosen.pop_back(); } for(auto it=touched.rbegin();it!=touched.rend();++it) cnt[*it]--; for(auto it=ctouched.rbegin();it!=ctouched.rend();++it) ccnt[*it]--; for(int w=0;w<WORDS;w++) dom[w]=prop_dom[w]; for(size_t i=0;i<pairs.size();i++) pair_margin[i]=child_margins[i]; for(int p:child_forced) clrbit4(mandatory,p); }
      if(res.timeout) break; if(ismand) break;
    }
    for(int w=0;w<WORDS;w++) dom[w]=prop_dom[w]; restore_pair_state(saved,removed,forced);
  }
  Result run(const uint64_t forbidden[WORDS],const std::vector<int>& force,int min_after){
    res=Result(); res.target=target; res.nodes.fill(0); res.pair_depth.fill(0); res.cover_depth.fill(0); res.nodes[0]=1; std::fill(cnt.begin(),cnt.end(),0); std::fill(ccnt.begin(),ccnt.end(),0); chosen.clear(); full_domain(); std::memset(mandatory,0,sizeof(mandatory)); for(int w=0;w<WORDS;w++) dom[w]&=~forbidden[w]; for(const auto& row:rows) if(row.cap==0){ int before=pop4(dom); for(int w=0;w<WORDS;w++) dom[w]&=~row.word[w]; res.initial_cap0_removed+=std::max(0,before-pop4(dom)); } init_pair_margins(); start=std::chrono::steady_clock::now(); if(force_points(force)){ int d=(int)chosen.size(); if(d<(int)res.nodes.size()) res.nodes[d]=std::max<uint64_t>(res.nodes[d],1); dfs(min_after); } res.elapsed_sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); res.complete=!res.timeout; return res;
  }
};
static std::string rjson(const Result&r){ std::ostringstream o; o<<"{\"target\":"<<r.target<<",\"elapsed_sec\":"<<std::fixed<<std::setprecision(6)<<r.elapsed_sec<<",\"timeout\":"<<(r.timeout?"true":"false")<<",\"complete\":"<<(r.complete?"true":"false")<<",\"forced_infeasible\":"<<(r.forced_infeasible?"true":"false")<<",\"recursive_calls\":"<<r.calls<<",\"candidate_tests\":"<<r.candidate_tests<<",\"overcap_rejects\":"<<r.overcap_rejects<<",\"cover_overcap_rejects\":"<<r.cover_overcap_rejects<<",\"global_shortage\":"<<r.global_shortage<<",\"pair_checks\":"<<r.pair_checks<<",\"pair_prunes\":"<<r.pair_prunes<<",\"pair_propagations\":"<<r.pair_propagations<<",\"pair_exclusions\":"<<r.pair_exclusions<<",\"pair_forces\":"<<r.pair_forces<<",\"pair_cascade_rounds\":"<<r.pair_cascade_rounds<<",\"cover_prunes\":"<<r.cover_prunes<<",\"cover_checks\":"<<r.cover_checks<<",\"cover_row_tests\":"<<r.cover_row_tests<<",\"cover_skips\":"<<r.cover_skips<<",\"saturated_rows\":"<<r.saturated_rows<<",\"saturation_removed_points\":"<<r.saturation_removed_points<<",\"initial_cap0_removed\":"<<r.initial_cap0_removed<<",\"solutions\":"<<r.solutions<<",\"max_depth\":"<<r.max_depth<<",\"node_count_by_depth\":"<<arr_json(r.nodes,std::min(31,r.target))<<",\"pair_prune_depth\":"<<arr_json(r.pair_depth,std::min(31,r.target))<<",\"cover_prune_depth\":"<<arr_json(r.cover_depth,std::min(31,r.target))<<",\"cover_certificates_head\":"<<certs_json(r.cover_certs)<<",\"solutions_head\":"<<sols_json(r.sol_head)<<"}"; return o.str(); }

int main(int argc,char**argv){
  std::string cons,pairpath,coverpath,outp,force_s,exclude_s; int target=19,cover_min_depth=999,cover_max_slack=-1,min_after=1; double lim=60;
  for(int i=1;i<argc;i++){ std::string a=argv[i]; if(a=="--constraints"&&i+1<argc) cons=argv[++i]; else if(a=="--pair-rows"&&i+1<argc) pairpath=argv[++i]; else if(a=="--cover-constraints"&&i+1<argc) coverpath=argv[++i]; else if(a=="--target"&&i+1<argc) target=std::stoi(argv[++i]); else if(a=="--timeout"&&i+1<argc) lim=std::stod(argv[++i]); else if(a=="--force"&&i+1<argc) force_s=argv[++i]; else if(a=="--exclude"&&i+1<argc) exclude_s=argv[++i]; else if(a=="--min-after"&&i+1<argc) min_after=std::stoi(argv[++i]); else if(a=="--cover-min-depth"&&i+1<argc) cover_min_depth=std::stoi(argv[++i]); else if(a=="--cover-max-slack"&&i+1<argc) cover_max_slack=std::stoi(argv[++i]); else if(a=="--output"&&i+1<argc) outp=argv[++i]; else { std::cerr<<"bad arg "<<a<<"\n"; return 2; } }
  if(cons.empty()||pairpath.empty()){ std::cerr<<"usage: --constraints FILE --pair-rows FILE [--cover-constraints FILE] --force list [--exclude list] --timeout S --output FILE\n"; return 2; }
  std::vector<Row> rows,pair_rows,cov; if(!load_rows(cons,rows)) return 1; if(!load_rows(pairpath,pair_rows)) return 1; if(!coverpath.empty()&&!load_rows(coverpath,cov)) return 1;
  auto pr=point_rows(rows); auto cpr=point_rows(cov); std::vector<int> force=parse_list(force_s), exclude=parse_list(exclude_s); uint64_t forbidden[WORDS]={0,0,0,0}; for(int p:exclude) setbit4(forbidden,p);
  Searcher S(rows,pr,cov,cpr,pair_rows,target,lim,cover_min_depth,cover_max_slack); Result r=S.run(forbidden,force,min_after); std::cout<<rjson(r)<<"\n";
  if(!outp.empty()){ std::ostringstream out; out<<"{\n  \"schema\": \"s0908_pair_cover_dfs_v1\",\n  \"semantics\": \"repaired signed-pair propagation plus residual-cover upper-bound pruning; no lower fill obligation\",\n  \"constraints_path\": \""<<cons<<"\",\n  \"pair_rows_path\": \""<<pairpath<<"\",\n  \"cover_constraints_path\": \""<<coverpath<<"\",\n  \"constraint_count\": "<<rows.size()<<",\n  \"pair_row_count\": "<<pair_rows.size()<<",\n  \"cover_constraint_count\": "<<cov.size()<<",\n  \"target\": "<<target<<",\n  \"force\": "<<vec_json(force)<<",\n  \"exclude\": "<<vec_json(exclude)<<",\n  \"min_after\": "<<min_after<<",\n  \"timeout_sec\": "<<lim<<",\n  \"cover_min_depth\": "<<cover_min_depth<<",\n  \"cover_max_slack\": "<<cover_max_slack<<",\n  \"result\": "<<rjson(r)<<"\n}\n"; std::ofstream f(outp); f<<out.str(); std::cerr<<"wrote "<<outp<<"\n"; }
  return 0;
}
