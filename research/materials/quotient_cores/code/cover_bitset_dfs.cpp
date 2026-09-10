// analysis: sound bitset DFS with residual-capacity cover pruning for E11 supports.
//
// Constraint rows (E11WANG1) are ordinary Wang upper bounds |S cap R| <= cap;
// their saturation removes future domain points, as in the analysis repaired
// runner.  Cover rows are also valid Wang upper bounds, but are used only for
// over-cap rejection and for the global-size residual-capacity test:
//
//   With selected P, future domain F, and need t=19-|P|, a row R with residual
//   capacity u=cap-|P cap R| permits at most u + |F\R| future choices.  If this
//   is < t then no size-t extension exists.  This is a consequence of the
//   global target size, not an obligation to fill unused row capacity.
//
// The cover row family may include omitted larger-capacity Wang rows.  Branch
// closure under these rows is still a valid exclusion for the exact E11 support
// problem because every cover row is a genuine Wang upper bound.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <vector>

static constexpr int MAXP = 255;
static constexpr int WORDS = 4;
static bool bit4(const uint64_t w[WORDS], int p){ return (w[p>>6]>>(p&63))&1ULL; }
static void setbit4(uint64_t w[WORDS], int p){ w[p>>6] |= 1ULL<<(p&63); }
static void clrbit4(uint64_t w[WORDS], int p){ w[p>>6] &= ~(1ULL<<(p&63)); }
static int pop4(const uint64_t w[WORDS]){ return __builtin_popcountll(w[0])+__builtin_popcountll(w[1])+__builtin_popcountll(w[2])+__builtin_popcountll(w[3]); }

struct Row { uint8_t cap=0, dim=0; uint16_t reserved=0; uint64_t word[WORDS]={0,0,0,0}; };
struct Cut { uint8_t K=0; uint64_t w1[WORDS]={0,0,0,0}; uint64_t w2[WORDS]={0,0,0,0}; uint8_t coeff[256]{}; };
struct Branch { int id=-1, rep=0; uint64_t forbid[WORDS]={0,0,0,0}; };
struct CoverCert { int row=-1, cap=0, count=0, residual=0, future_in=0, future_out=0, need=0, avail=0, depth=0; };
struct Result {
    int branch=-1, rep=0, target=0, max_depth=0; double elapsed_sec=0.0; bool timeout=false, complete=false, forced_infeasible=false;
    uint64_t calls=0, candidate_tests=0, overcap_rejects=0, cover_overcap_rejects=0, global_shortage=0;
    uint64_t mixed_prunes=0, mixed_checks=0, cover_checks=0, cover_row_tests=0, cover_prunes=0, cover_skips=0;
    uint64_t saturated_rows=0, saturation_removed_points=0, initial_cap0_removed=0, solutions=0;
    std::array<uint64_t,32> nodes{}; std::array<uint64_t,32> mixed_depth{}; std::array<uint64_t,32> cover_depth{};
    std::vector<std::vector<int>> sol_head; std::vector<CoverCert> cover_certs;
};
static std::string arr_json(const std::array<uint64_t,32>& a, int upto){ std::ostringstream o; o<<"["; for(int i=0;i<=upto && i<(int)a.size();i++){ if(i)o<<","; o<<a[i]; } o<<"]"; return o.str(); }
static std::string vec_json(const std::vector<int>& v){ std::ostringstream o; o<<"["; for(size_t i=0;i<v.size();i++){ if(i)o<<","; o<<v[i]; } o<<"]"; return o.str(); }
static std::string sols_json(const std::vector<std::vector<int>>& vv){ std::ostringstream o; o<<"["; for(size_t i=0;i<vv.size();i++){ if(i)o<<","; o<<vec_json(vv[i]); } o<<"]"; return o.str(); }
static std::string certs_json(const std::vector<CoverCert>& cc){ std::ostringstream o; o<<"["; for(size_t i=0;i<cc.size();i++){ if(i)o<<","; const auto& c=cc[i]; o<<"{\"row\":"<<c.row<<",\"cap\":"<<c.cap<<",\"count\":"<<c.count<<",\"residual\":"<<c.residual<<",\"future_in\":"<<c.future_in<<",\"future_out\":"<<c.future_out<<",\"need\":"<<c.need<<",\"avail\":"<<c.avail<<",\"depth\":"<<c.depth<<"}"; } o<<"]"; return o.str(); }

static bool load_rows(const std::string& path, std::vector<Row>& rows){
    if(path.empty()) return true;
    std::ifstream in(path, std::ios::binary); if(!in){ std::cerr<<"cannot open "<<path<<"\n"; return false; }
    char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"E11WANG1",8)!=0){ std::cerr<<"bad row magic for "<<path<<"\n"; return false; }
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); rows.resize(n);
    for(uint32_t i=0;i<n;i++){
        in.read(reinterpret_cast<char*>(&rows[i].cap),1); in.read(reinterpret_cast<char*>(&rows[i].dim),1); in.read(reinterpret_cast<char*>(&rows[i].reserved),2);
        for(int w=0;w<WORDS;w++) in.read(reinterpret_cast<char*>(&rows[i].word[w]),8);
    }
    if(!in){ std::cerr<<"short row read "<<path<<"\n"; return false; }
    return true;
}
static bool load_cuts(const std::string& path, std::vector<Cut>& cuts){
    if(path.empty()) return true;
    std::ifstream in(path, std::ios::binary); if(!in){ std::cerr<<"cannot open cuts "<<path<<"\n"; return false; }
    char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"MIXCUT1\0",8)!=0){ std::cerr<<"bad cut magic\n"; return false; }
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); cuts.resize(n);
    for(uint32_t i=0;i<n;i++){
        uint8_t flags; uint16_t reserved; in.read(reinterpret_cast<char*>(&cuts[i].K),1); in.read(reinterpret_cast<char*>(&flags),1); in.read(reinterpret_cast<char*>(&reserved),2);
        for(int w=0;w<WORDS;w++) in.read(reinterpret_cast<char*>(&cuts[i].w1[w]),8);
        for(int w=0;w<WORDS;w++) in.read(reinterpret_cast<char*>(&cuts[i].w2[w]),8);
        for(int p=1;p<=MAXP;p++) cuts[i].coeff[p] = bit4(cuts[i].w2,p)?2:(bit4(cuts[i].w1,p)?1:0);
    }
    if(!in){ std::cerr<<"short cut read\n"; return false; }
    return true;
}
static std::vector<std::vector<uint32_t>> point_rows(const std::vector<Row>& rows){
    std::vector<std::vector<uint32_t>> pr(256);
    for(uint32_t ri=0;ri<rows.size();ri++) for(int p=1;p<=MAXP;p++) if(bit4(rows[ri].word,p)) pr[p].push_back(ri);
    return pr;
}
static std::vector<Branch> branches(){
    const int reps[8]={1,4,5,8,10,40,42,80};
    const std::vector<std::vector<int>> members={
        {1,2,3}, {4,32,36}, {5,6,7,33,34,35,37,38,39},
        {8,9,12,13,16,18,20,22,24,27,28,31,64,65,72,73,96,97,108,109,128,130,144,146,160,162,180,182,192,195,216,219,224,227,252,255},
        {10,11,14,15,17,19,21,23,25,26,29,30,66,67,74,75,98,99,110,111,129,131,145,147,161,163,181,183,193,194,217,218,225,226,253,254},
        {40,41,44,45,48,50,52,54,56,59,60,63,68,69,76,77,100,101,104,105,132,134,148,150,164,166,176,178,196,199,220,223,228,231,248,251},
        {42,43,46,47,49,51,53,55,57,58,61,62,70,71,78,79,102,103,106,107,133,135,149,151,165,167,177,179,197,198,221,222,229,230,249,250},
        {80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,136,137,138,139,140,141,142,143,152,153,154,155,156,157,158,159,168,169,170,171,172,173,174,175,184,185,186,187,188,189,190,191,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247}
    };
    std::vector<Branch> out; uint64_t forbid[WORDS]={0,0,0,0};
    for(int i=0;i<8;i++){ Branch b; b.id=i; b.rep=reps[i]; for(int w=0;w<WORDS;w++) b.forbid[w]=forbid[w]; out.push_back(b); for(int p:members[i]) setbit4(forbid,p); }
    return out;
}
static std::vector<int> parse_list(const std::string& s){ std::vector<int> v; size_t pos=0; while(pos<s.size()){ size_t nx=s.find(',',pos); if(nx==std::string::npos) nx=s.size(); if(nx>pos){ int p=std::stoi(s.substr(pos,nx-pos)); if(1<=p&&p<=MAXP) v.push_back(p); } pos=nx+1; } std::sort(v.begin(),v.end()); v.erase(std::unique(v.begin(),v.end()),v.end()); return v; }

struct Searcher{
    const std::vector<Row>& rows; const std::vector<std::vector<uint32_t>>& pr;
    const std::vector<Row>& cov; const std::vector<std::vector<uint32_t>>& cpr;
    const std::vector<Cut>& cuts; int target; double limit; int cover_min_depth; int cover_max_slack; bool use_mixed;
    std::chrono::steady_clock::time_point start; std::vector<uint8_t> cnt, ccnt; std::vector<int16_t> lhs; uint64_t dom[WORDS]; std::vector<int> chosen; Result res;
    Searcher(const std::vector<Row>& r,const std::vector<std::vector<uint32_t>>& p,const std::vector<Row>& cr,const std::vector<std::vector<uint32_t>>& cp,const std::vector<Cut>& c,int t,double lim,int cmd,int cms):rows(r),pr(p),cov(cr),cpr(cp),cuts(c),target(t),limit(lim),cover_min_depth(cmd),cover_max_slack(cms),use_mixed(!c.empty()),cnt(r.size(),0),ccnt(cr.size(),0),lhs(c.size(),0){}
    bool timed() const { return limit>0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=limit; }
    void full_domain(){ dom[0]=dom[1]=dom[2]=dom[3]=~0ULL; dom[0]&=~1ULL; }
    bool in_dom(int p) const { return bit4(dom,p); }
    void remove_dom(int p){ clrbit4(dom,p); }
    int avail_from(int minp) const { int c=0; for(int p=minp;p<=MAXP;p++) if(in_dom(p)) c++; return c; }
    void future_words(int minp, uint64_t out[WORDS]) const { for(int w=0;w<WORDS;w++) out[w]=dom[w]; if(minp>1) for(int p=1;p<minp && p<=MAXP;p++) clrbit4(out,p); }
    bool mixed_possible(int minp,int need){
        if(!use_mixed) return true; res.mixed_checks += cuts.size(); uint64_t fut[WORDS]; future_words(minp,fut);
        for(size_t i=0;i<cuts.size();i++){
            uint64_t a1[WORDS],a2[WORDS]; for(int w=0;w<WORDS;w++){ a1[w]=fut[w]&cuts[i].w1[w]; a2[w]=fut[w]&cuts[i].w2[w]; }
            int c2=pop4(a2), c1=pop4(a1); int take2=std::min(c2,need); int take1=std::min(c1,need-take2); int ub=lhs[i]+2*take2+take1;
            if(ub < cuts[i].K){ res.mixed_prunes++; int d=(int)chosen.size(); if(d>=0 && d<(int)res.mixed_depth.size()) res.mixed_depth[d]++; return false; }
        }
        return true;
    }
    bool cover_possible(int minp,int need){
        if(cov.empty()) return true;
        uint64_t fut[WORDS]; future_words(minp,fut); int avail=pop4(fut); int depth=(int)chosen.size(); int slack=avail-need;
        // Terminal nodes and negative residuals must always be checked.  For
        // interior nodes, optional depth/slack thresholds keep this a targeted
        // strengthening rather than a full scan at every early branch.
        bool threshold = (need==0) || (depth>=cover_min_depth) || (cover_max_slack>=0 && slack<=cover_max_slack);
        if(!threshold){ res.cover_skips++; return true; }
        res.cover_checks++;
        for(size_t i=0;i<cov.size();i++){
            int u=(int)cov[i].cap - (int)ccnt[i];
            if(u>=need) continue;
            res.cover_row_tests++;
            if(u<0){ res.cover_prunes++; if(depth>=0 && depth<(int)res.cover_depth.size()) res.cover_depth[depth]++; if(res.cover_certs.size()<5) res.cover_certs.push_back({(int)i,(int)cov[i].cap,(int)ccnt[i],u,0,avail,need,avail,depth}); return false; }
            uint64_t a[WORDS]; for(int w=0;w<WORDS;w++) a[w]=fut[w]&cov[i].word[w]; int in=pop4(a); int outside=avail-in;
            if(u + outside < need){ res.cover_prunes++; if(depth>=0 && depth<(int)res.cover_depth.size()) res.cover_depth[depth]++; if(res.cover_certs.size()<5) res.cover_certs.push_back({(int)i,(int)cov[i].cap,(int)ccnt[i],u,in,outside,need,avail,depth}); return false; }
        }
        return true;
    }
    bool try_select(int q,std::vector<uint32_t>& touched,std::vector<uint32_t>& ctouched,uint64_t olddom[WORDS]){
        res.candidate_tests++; for(int w=0;w<WORDS;w++) olddom[w]=dom[w]; if(!in_dom(q)) return false;
        for(uint32_t ri:pr[q]) if((int)cnt[ri]+1>(int)rows[ri].cap){ res.overcap_rejects++; return false; }
        for(uint32_t ri:cpr[q]) if((int)ccnt[ri]+1>(int)cov[ri].cap){ res.cover_overcap_rejects++; return false; }
        remove_dom(q); for(uint32_t ri:pr[q]){ cnt[ri]++; touched.push_back(ri); } for(uint32_t ri:cpr[q]){ ccnt[ri]++; ctouched.push_back(ri); }
        for(size_t i=0;i<cuts.size();i++) lhs[i]+=cuts[i].coeff[q];
        for(uint32_t ri:touched){ if(cnt[ri]==rows[ri].cap){ res.saturated_rows++; int before=pop4(dom); for(int w=0;w<WORDS;w++) dom[w]&=~rows[ri].word[w]; int after=pop4(dom); if(before>after) res.saturation_removed_points += (before-after); } }
        return true;
    }
    void undo_select(int q,const std::vector<uint32_t>& touched,const std::vector<uint32_t>& ctouched,const uint64_t olddom[WORDS]){
        for(size_t i=0;i<cuts.size();i++) lhs[i]-=cuts[i].coeff[q]; for(auto it=touched.rbegin();it!=touched.rend();++it) cnt[*it]--; for(auto it=ctouched.rbegin();it!=ctouched.rend();++it) ccnt[*it]--; for(int w=0;w<WORDS;w++) dom[w]=olddom[w];
    }
    bool force_points(const std::vector<int>& force){ for(int p:force){ if(!in_dom(p)){ res.forced_infeasible=true; return false; } std::vector<uint32_t> touched,ctouched; uint64_t old[WORDS]; bool ok=try_select(p,touched,ctouched,old); if(!ok){ res.forced_infeasible=true; return false; } chosen.push_back(p); } return true; }
    void dfs(int minp){
        if(res.timeout) return; if((res.calls++ & 0x3FFFULL)==0 && timed()){ res.timeout=true; return; }
        int d=(int)chosen.size(); if(d>res.max_depth) res.max_depth=d; if(d==target){ if(!cover_possible(MAXP+1,0)) return; if(!mixed_possible(MAXP+1,0)) return; res.solutions++; if(res.sol_head.size()<5){ auto s=chosen; std::sort(s.begin(),s.end()); res.sol_head.push_back(s); } return; }
        int need=target-d; int avail=avail_from(minp); if(avail<need){ res.global_shortage++; return; } if(!cover_possible(minp,need)) return; if(!mixed_possible(minp,need)) return;
        for(int q=minp;q<=MAXP;q++){
            if(MAXP-q+1<need) break; if(!in_dom(q)) continue; if(avail_from(q)<need) break;
            std::vector<uint32_t> touched,ctouched; uint64_t old[WORDS]; bool ok=try_select(q,touched,ctouched,old);
            if(ok){ chosen.push_back(q); int nd=(int)chosen.size(); if(nd<(int)res.nodes.size()) res.nodes[nd]++; dfs(q+1); chosen.pop_back(); undo_select(q,touched,ctouched,old); }
            if(res.timeout) return;
        }
    }
    Result run(const uint64_t forbidden[WORDS],const std::vector<int>& force,int min_after,int branch,int rep){
        res=Result(); res.branch=branch; res.rep=rep; res.target=target; res.nodes.fill(0); res.mixed_depth.fill(0); res.cover_depth.fill(0); res.nodes[0]=1;
        std::fill(cnt.begin(),cnt.end(),0); std::fill(ccnt.begin(),ccnt.end(),0); std::fill(lhs.begin(),lhs.end(),0); chosen.clear(); full_domain(); for(int w=0;w<WORDS;w++) dom[w]&=~forbidden[w];
        for(const auto& row:rows) if(row.cap==0){ int before=pop4(dom); for(int w=0;w<WORDS;w++) dom[w]&=~row.word[w]; res.initial_cap0_removed += std::max(0,before-pop4(dom)); }
        start=std::chrono::steady_clock::now(); bool ok=force_points(force); if(ok){ int d=(int)chosen.size(); if(d<(int)res.nodes.size()) res.nodes[d]=std::max<uint64_t>(res.nodes[d],1); dfs(min_after); }
        res.elapsed_sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); res.complete=!res.timeout; return res;
    }
};
static std::string rjson(const Result& r){ std::ostringstream o; o<<"{\"branch\":"<<r.branch<<",\"rep\":"<<r.rep<<",\"target\":"<<r.target<<",\"elapsed_sec\":"<<std::fixed<<std::setprecision(6)<<r.elapsed_sec<<",\"timeout\":"<<(r.timeout?"true":"false")<<",\"complete\":"<<(r.complete?"true":"false")<<",\"forced_infeasible\":"<<(r.forced_infeasible?"true":"false")<<",\"recursive_calls\":"<<r.calls<<",\"candidate_tests\":"<<r.candidate_tests<<",\"overcap_rejects\":"<<r.overcap_rejects<<",\"cover_overcap_rejects\":"<<r.cover_overcap_rejects<<",\"global_shortage\":"<<r.global_shortage<<",\"mixed_prunes\":"<<r.mixed_prunes<<",\"mixed_checks\":"<<r.mixed_checks<<",\"cover_prunes\":"<<r.cover_prunes<<",\"cover_checks\":"<<r.cover_checks<<",\"cover_row_tests\":"<<r.cover_row_tests<<",\"cover_skips\":"<<r.cover_skips<<",\"saturated_rows\":"<<r.saturated_rows<<",\"saturation_removed_points\":"<<r.saturation_removed_points<<",\"initial_cap0_removed\":"<<r.initial_cap0_removed<<",\"solutions\":"<<r.solutions<<",\"max_depth\":"<<r.max_depth<<",\"node_count_by_depth\":"<<arr_json(r.nodes,std::min(31,r.target))<<",\"mixed_prune_depth\":"<<arr_json(r.mixed_depth,std::min(31,r.target))<<",\"cover_prune_depth\":"<<arr_json(r.cover_depth,std::min(31,r.target))<<",\"cover_certificates_head\":"<<certs_json(r.cover_certs)<<",\"solutions_head\":"<<sols_json(r.sol_head)<<"}"; return o.str(); }

int main(int argc,char**argv){
    std::string cons,covers,cuts,outp,force_s,exclude_s; int target=19,branch=-2,cover_min_depth=999; int cover_max_slack=-1; double lim=60.0;
    for(int i=1;i<argc;i++){ std::string a=argv[i]; if(a=="--constraints"&&i+1<argc) cons=argv[++i]; else if(a=="--cover-constraints"&&i+1<argc) covers=argv[++i]; else if(a=="--cuts"&&i+1<argc) cuts=argv[++i]; else if(a=="--output"&&i+1<argc) outp=argv[++i]; else if(a=="--target"&&i+1<argc) target=std::stoi(argv[++i]); else if(a=="--timeout"&&i+1<argc) lim=std::stod(argv[++i]); else if(a=="--branch"&&i+1<argc) branch=std::stoi(argv[++i]); else if(a=="--all-branches") branch=-1; else if(a=="--force"&&i+1<argc) force_s=argv[++i]; else if(a=="--exclude"&&i+1<argc) exclude_s=argv[++i]; else if(a=="--cover-min-depth"&&i+1<argc) cover_min_depth=std::stoi(argv[++i]); else if(a=="--cover-max-slack"&&i+1<argc) cover_max_slack=std::stoi(argv[++i]); else { std::cerr<<"bad arg "<<a<<"\n"; return 2; } }
    if(cons.empty()){ std::cerr<<"usage: --constraints FILE --target N [--cover-constraints FILE] [--cover-min-depth D] [--cover-max-slack S] [--cuts FILE] [--branch B|--all-branches] [--force a,b] [--exclude a,b] [--timeout S] [--output FILE]\n"; return 2; }
    std::vector<Row> rows,cov; if(!load_rows(cons,rows)) return 1; if(covers.empty()) cov.clear(); else if(!load_rows(covers,cov)) return 1; std::vector<Cut> cutv; if(!load_cuts(cuts,cutv)) return 1; auto pr=point_rows(rows); auto cpr=point_rows(cov);
    std::vector<int> force=parse_list(force_s), exclude=parse_list(exclude_s); uint64_t forbidden[WORDS]={0,0,0,0}; for(int p:exclude) setbit4(forbidden,p);
    std::vector<Result> results; if(branch>=-1){ for(auto& br:branches()){ if(branch>=0 && br.id!=branch) continue; uint64_t forb[WORDS]; for(int w=0;w<WORDS;w++) forb[w]=forbidden[w]|br.forbid[w]; auto f=force; f.push_back(br.rep); std::sort(f.begin(),f.end()); f.erase(std::unique(f.begin(),f.end()),f.end()); Searcher S(rows,pr,cov,cpr,cutv,target,lim,cover_min_depth,cover_max_slack); Result r=S.run(forb,f,br.rep+1,br.id,br.rep); results.push_back(r); std::cout<<rjson(r)<<"\n"; std::cout.flush(); } }
    else { Searcher S(rows,pr,cov,cpr,cutv,target,lim,cover_min_depth,cover_max_slack); Result r=S.run(forbidden,force,1,-1,0); results.push_back(r); std::cout<<rjson(r)<<"\n"; }
    bool all=true; uint64_t sol=0,calls=0,tests=0,over=0,coverover=0,shortage=0,mp=0,mchk=0,cp=0,cchk=0,crtests=0,cskips=0,sat=0,srem=0,init0=0; int md=0; std::array<uint64_t,32> nodes{},mpd{},cpd{}; nodes.fill(0); mpd.fill(0); cpd.fill(0);
    for(auto&r:results){ all&=r.complete; sol+=r.solutions; calls+=r.calls; tests+=r.candidate_tests; over+=r.overcap_rejects; coverover+=r.cover_overcap_rejects; shortage+=r.global_shortage; mp+=r.mixed_prunes; mchk+=r.mixed_checks; cp+=r.cover_prunes; cchk+=r.cover_checks; crtests+=r.cover_row_tests; cskips+=r.cover_skips; sat+=r.saturated_rows; srem+=r.saturation_removed_points; init0+=r.initial_cap0_removed; md=std::max(md,r.max_depth); for(int i=0;i<32;i++){ nodes[i]+=r.nodes[i]; mpd[i]+=r.mixed_depth[i]; cpd[i]+=r.cover_depth[i]; } }
    std::ostringstream out; out<<"{\n  \"schema\": \"s0908_cover_bitset_dfs_v1\",\n  \"semantics\": \"Wang upper-bound saturation plus sound residual-capacity one-row cover pruning; optional mixed lower-cut pruning\",\n  \"constraints_path\": \""<<cons<<"\",\n  \"cover_constraints_path\": \""<<covers<<"\",\n  \"cut_path\": \""<<cuts<<"\",\n  \"constraint_count\": "<<rows.size()<<",\n  \"cover_constraint_count\": "<<cov.size()<<",\n  \"mixed_cut_count\": "<<cutv.size()<<",\n  \"target\": "<<target<<",\n  \"time_limit_per_run_sec\": "<<lim<<",\n  \"cover_min_depth\": "<<cover_min_depth<<",\n  \"cover_max_slack\": "<<cover_max_slack<<",\n  \"all_complete\": "<<(all?"true":"false")<<",\n  \"total_solutions\": "<<sol<<",\n  \"global_max_depth\": "<<md<<",\n  \"total_recursive_calls\": "<<calls<<",\n  \"total_candidate_tests\": "<<tests<<",\n  \"total_overcap_rejects\": "<<over<<",\n  \"total_cover_overcap_rejects\": "<<coverover<<",\n  \"total_global_shortage\": "<<shortage<<",\n  \"total_mixed_prunes\": "<<mp<<",\n  \"total_mixed_checks\": "<<mchk<<",\n  \"total_cover_prunes\": "<<cp<<",\n  \"total_cover_checks\": "<<cchk<<",\n  \"total_cover_row_tests\": "<<crtests<<",\n  \"total_cover_skips\": "<<cskips<<",\n  \"total_saturated_rows\": "<<sat<<",\n  \"total_saturation_removed_points\": "<<srem<<",\n  \"total_initial_cap0_removed\": "<<init0<<",\n  \"total_node_count_by_depth\": "<<arr_json(nodes,std::min(31,target))<<",\n  \"total_mixed_prune_depth\": "<<arr_json(mpd,std::min(31,target))<<",\n  \"total_cover_prune_depth\": "<<arr_json(cpd,std::min(31,target))<<",\n  \"results\": [\n"; for(size_t i=0;i<results.size();i++){ out<<"    "<<rjson(results[i]); if(i+1<results.size()) out<<","; out<<"\n"; } out<<"  ]\n}\n";
    if(!outp.empty()){ std::ofstream f(outp); f<<out.str(); std::cerr<<"wrote "<<outp<<"\n"; }
    return 0;
}
