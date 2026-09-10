// analysis: sound E11 Wang domain DFS plus selected mixed-source lower cuts.
//
// Wang rows: upper bounds |S∩R|<=cap. Sound domain propagation: saturated
// upper rows remove future points in that row. No unused-capacity filling test.
//
// Mixed rows: lower bounds sum_p c_p x_p >= K with c_p in {0,1,2}.
// They are used only for pruning by an upper bound on possible future
// contribution from ordered points >= minq. This upper bound intentionally
// ignores domain removals/forbidden points, so it can be weak but not unsound.

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

static constexpr int MAXPTS = 255;
static bool bit4(const uint64_t w[4], int p){ return (w[p>>6]>>(p&63))&1ULL; }
static void setbit4(uint64_t w[4], int p){ w[p>>6] |= 1ULL<<(p&63); }

struct Constraint { uint8_t cap=0, dim=0; uint16_t reserved=0; uint64_t word[4]={0,0,0,0}; };
struct BranchSpec { int id=-1, rep=0; uint64_t forbid[4]={0,0,0,0}; };
struct MixedCut {
    uint8_t K=0; uint8_t coeff[256]{}; uint16_t suf1[257]{}; uint16_t suf2[257]{};
};
struct Result {
    int branch=-1, rep=0, target=0, max_depth=0; double elapsed_sec=0.0; bool timeout=false, complete=false, forced_infeasible=false;
    uint64_t recursive_calls=0, candidate_tests=0, overcap_rejects=0, global_shortage=0, mixed_prunes=0, mixed_checks=0;
    uint64_t saturated_rows=0, saturation_point_removals=0, solutions=0;
    std::array<uint64_t,32> node_count{}; std::array<uint64_t,32> mixed_prune_depth{}; std::vector<std::vector<int>> solutions_head;
};

static std::string arr_json(const std::array<uint64_t,32>& a, int upto){ std::ostringstream o; o<<"["; for(int i=0;i<=upto && i<(int)a.size();i++){ if(i)o<<","; o<<a[i]; } o<<"]"; return o.str(); }
static std::string vec_json(const std::vector<int>& v){ std::ostringstream o; o<<"["; for(size_t i=0;i<v.size();i++){ if(i)o<<","; o<<v[i]; } o<<"]"; return o.str(); }
static std::string sols_json(const std::vector<std::vector<int>>& sols){ std::ostringstream o; o<<"["; for(size_t i=0;i<sols.size();i++){ if(i)o<<","; o<<vec_json(sols[i]); } o<<"]"; return o.str(); }

static bool load_constraints(const std::string& path, std::vector<Constraint>& rows){
    std::ifstream in(path, std::ios::binary); if(!in){ std::cerr<<"cannot open "<<path<<"\n"; return false; }
    char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"E11WANG1",8)!=0){ std::cerr<<"bad Wang magic\n"; return false; }
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); rows.resize(n);
    for(uint32_t i=0;i<n;i++){
        in.read(reinterpret_cast<char*>(&rows[i].cap),1); in.read(reinterpret_cast<char*>(&rows[i].dim),1); in.read(reinterpret_cast<char*>(&rows[i].reserved),2);
        for(int j=0;j<4;j++) in.read(reinterpret_cast<char*>(&rows[i].word[j]),8);
    }
    if(!in){ std::cerr<<"short Wang read\n"; return false; } return true;
}
static bool load_cuts(const std::string& path, std::vector<MixedCut>& cuts){
    if(path.empty()) return true;
    std::ifstream in(path, std::ios::binary); if(!in){ std::cerr<<"cannot open cuts "<<path<<"\n"; return false; }
    char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"MIXCUT1\0",8)!=0){ std::cerr<<"bad cut magic\n"; return false; }
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); cuts.resize(n);
    for(uint32_t i=0;i<n;i++){
        uint8_t K, flags; uint16_t reserved; uint64_t w1[4], w2[4];
        in.read(reinterpret_cast<char*>(&K),1); in.read(reinterpret_cast<char*>(&flags),1); in.read(reinterpret_cast<char*>(&reserved),2);
        for(int j=0;j<4;j++) in.read(reinterpret_cast<char*>(&w1[j]),8);
        for(int j=0;j<4;j++) in.read(reinterpret_cast<char*>(&w2[j]),8);
        cuts[i].K=K;
        for(int p=1;p<=MAXPTS;p++) cuts[i].coeff[p] = bit4(w2,p) ? 2 : (bit4(w1,p) ? 1 : 0);
        cuts[i].suf1[256]=cuts[i].suf2[256]=0;
        for(int p=255;p>=1;p--){ cuts[i].suf1[p]=cuts[i].suf1[p+1]+(cuts[i].coeff[p]==1); cuts[i].suf2[p]=cuts[i].suf2[p+1]+(cuts[i].coeff[p]==2); }
    }
    if(!in){ std::cerr<<"short cut read\n"; return false; } return true;
}
static std::vector<std::vector<uint32_t>> point_rows_of(const std::vector<Constraint>& rows){
    std::vector<std::vector<uint32_t>> pr(256); for(uint32_t ri=0;ri<rows.size();ri++) for(int p=1;p<=MAXPTS;p++) if(bit4(rows[ri].word,p)) pr[p].push_back(ri); return pr;
}
static std::vector<BranchSpec> default_branches(){
    const int reps[8]={1,4,5,8,10,40,42,80};
    const std::vector<std::vector<int>> members={
        {1,2,3}, {4,32,36}, {5,6,7,33,34,35,37,38,39},
        {8,9,12,13,16,18,20,22,24,27,28,31,64,65,72,73,96,97,108,109,128,130,144,146,160,162,180,182,192,195,216,219,224,227,252,255},
        {10,11,14,15,17,19,21,23,25,26,29,30,66,67,74,75,98,99,110,111,129,131,145,147,161,163,181,183,193,194,217,218,225,226,253,254},
        {40,41,44,45,48,50,52,54,56,59,60,63,68,69,76,77,100,101,104,105,132,134,148,150,164,166,176,178,196,199,220,223,228,231,248,251},
        {42,43,46,47,49,51,53,55,57,58,61,62,70,71,78,79,102,103,106,107,133,135,149,151,165,167,177,179,197,198,221,222,229,230,249,250},
        {80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,136,137,138,139,140,141,142,143,152,153,154,155,156,157,158,159,168,169,170,171,172,173,174,175,184,185,186,187,188,189,190,191,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247}
    };
    std::vector<BranchSpec> out; uint64_t forb[4]={0,0,0,0};
    for(int i=0;i<8;i++){ BranchSpec b; b.id=i; b.rep=reps[i]; for(int w=0;w<4;w++) b.forbid[w]=forb[w]; out.push_back(b); for(int p:members[i]) setbit4(forb,p); }
    return out;
}
static std::vector<int> parse_list(const std::string& s){ std::vector<int> out; size_t pos=0; while(pos<s.size()){ size_t nx=s.find(',',pos); if(nx==std::string::npos) nx=s.size(); if(nx>pos){ int p=std::stoi(s.substr(pos,nx-pos)); if(1<=p&&p<=MAXPTS) out.push_back(p);} pos=nx+1;} std::sort(out.begin(),out.end()); out.erase(std::unique(out.begin(),out.end()),out.end()); return out; }

struct Searcher{
    const std::vector<Constraint>& rows; const std::vector<std::vector<uint32_t>>& pr; const std::vector<MixedCut>& cuts; int target; double limit;
    std::chrono::steady_clock::time_point start; std::vector<uint8_t> counts; std::vector<int16_t> lhs; std::vector<char> domain; std::vector<int> chosen; Result res;
    Searcher(const std::vector<Constraint>& r,const std::vector<std::vector<uint32_t>>& p,const std::vector<MixedCut>& c,int t,double l):rows(r),pr(p),cuts(c),target(t),limit(l),counts(r.size(),0),lhs(c.size(),0),domain(256,1){ domain[0]=0; }
    bool timed() const { return limit>0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=limit; }
    void remove_domain(int q,std::vector<int>& rem){ if(domain[q]){ domain[q]=0; rem.push_back(q); } }
    int avail_from(int minq) const { int c=0; for(int q=minq;q<=MAXPTS;q++) if(domain[q]) c++; return c; }
    bool mixed_possible(int minq,int need){
        res.mixed_checks += cuts.size(); if(cuts.empty()) return true; if(minq<1) minq=1; if(minq>256) minq=256;
        for(size_t i=0;i<cuts.size();i++){
            int c2 = cuts[i].suf2[minq], c1 = cuts[i].suf1[minq]; int take2 = std::min(c2, need); int take1 = std::min(c1, need-take2); int ub = lhs[i] + 2*take2 + take1;
            if(ub < cuts[i].K){ res.mixed_prunes++; int d=(int)chosen.size(); if(d>=0 && d<(int)res.mixed_prune_depth.size()) res.mixed_prune_depth[d]++; return false; }
        }
        return true;
    }
    bool try_select(int q,std::vector<uint32_t>& touched,std::vector<int>& removed){
        res.candidate_tests++; if(!domain[q]) return false;
        for(uint32_t ri:pr[q]) if((int)counts[ri]+1>(int)rows[ri].cap){ res.overcap_rejects++; return false; }
        remove_domain(q,removed); for(uint32_t ri:pr[q]){ counts[ri]++; touched.push_back(ri); }
        for(size_t i=0;i<cuts.size();i++) lhs[i] += cuts[i].coeff[q];
        for(uint32_t ri:touched){ if(counts[ri]==rows[ri].cap){ res.saturated_rows++; for(int w=0;w<4;w++){ uint64_t m=rows[ri].word[w]; while(m){ int bit=__builtin_ctzll(m); int s=w*64+bit; m&=m-1; if(s>=1&&s<=MAXPTS&&domain[s]){ res.saturation_point_removals++; remove_domain(s,removed); } } } } }
        return true;
    }
    void undo_select(int q,const std::vector<uint32_t>& touched,const std::vector<int>& removed){ for(size_t i=0;i<cuts.size();i++) lhs[i] -= cuts[i].coeff[q]; for(auto it=touched.rbegin();it!=touched.rend();++it) counts[*it]--; for(auto it=removed.rbegin();it!=removed.rend();++it) domain[*it]=1; }
    bool force_points(const std::vector<int>& force){ for(int p:force){ if(!domain[p]){res.forced_infeasible=true; return false;} std::vector<uint32_t> touched; std::vector<int> removed; bool ok=try_select(p,touched,removed); if(!ok){ undo_select(p,touched,removed); res.forced_infeasible=true; return false;} chosen.push_back(p);} return true; }
    void dfs(int minq){
        if(res.timeout) return; if((res.recursive_calls++ & 0x3FFFULL)==0 && timed()){res.timeout=true; return;} int depth=chosen.size(); if(depth>res.max_depth) res.max_depth=depth;
        if(depth==target){ res.solutions++; if(res.solutions_head.size()<5){ auto s=chosen; std::sort(s.begin(),s.end()); res.solutions_head.push_back(s);} return; }
        int need=target-depth; if(avail_from(minq)<need){ res.global_shortage++; return; } if(!mixed_possible(minq,need)) return;
        for(int q=minq;q<=MAXPTS;q++){
            if(MAXPTS-q+1<need) break; if(!domain[q]) continue; if(avail_from(q)<need) break;
            std::vector<uint32_t> touched; std::vector<int> removed; bool ok=try_select(q,touched,removed);
            if(ok){ chosen.push_back(q); int d=chosen.size(); if(d<(int)res.node_count.size()) res.node_count[d]++; if(mixed_possible(q+1,target-d)) dfs(q+1); chosen.pop_back(); }
            undo_select(q,touched,removed); if(res.timeout) return; if(res.solutions>100) return;
        }
    }
    Result run(uint64_t forbidden[4],const std::vector<int>& force,int min_after,int branch,int rep){
        res=Result(); res.branch=branch; res.rep=rep; res.target=target; res.node_count.fill(0); res.mixed_prune_depth.fill(0); res.node_count[0]=1; std::fill(counts.begin(),counts.end(),0); std::fill(lhs.begin(),lhs.end(),0); std::fill(domain.begin(),domain.end(),1); domain[0]=0; chosen.clear();
        for(int p=1;p<=MAXPTS;p++) if(bit4(forbidden,p)) domain[p]=0; start=std::chrono::steady_clock::now(); bool ok=force_points(force); if(ok){ int d=chosen.size(); if(d<(int)res.node_count.size()) res.node_count[d]=std::max<uint64_t>(res.node_count[d],1); dfs(min_after); }
        res.elapsed_sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); res.complete=!res.timeout; return res;
    }
};

static std::string rjson(const Result&r){ std::ostringstream o; o<<"{\"branch\":"<<r.branch<<",\"rep\":"<<r.rep<<",\"target\":"<<r.target<<",\"elapsed_sec\":"<<std::fixed<<std::setprecision(6)<<r.elapsed_sec<<",\"timeout\":"<<(r.timeout?"true":"false")<<",\"complete\":"<<(r.complete?"true":"false")<<",\"forced_infeasible\":"<<(r.forced_infeasible?"true":"false")<<",\"recursive_calls\":"<<r.recursive_calls<<",\"candidate_tests\":"<<r.candidate_tests<<",\"overcap_rejects\":"<<r.overcap_rejects<<",\"global_shortage\":"<<r.global_shortage<<",\"mixed_prunes\":"<<r.mixed_prunes<<",\"mixed_checks\":"<<r.mixed_checks<<",\"saturated_rows\":"<<r.saturated_rows<<",\"saturation_point_removals\":"<<r.saturation_point_removals<<",\"solutions\":"<<r.solutions<<",\"max_depth\":"<<r.max_depth<<",\"node_count_by_depth\":"<<arr_json(r.node_count,std::min(31,r.target))<<",\"mixed_prune_depth\":"<<arr_json(r.mixed_prune_depth,std::min(31,r.target))<<",\"solutions_head\":"<<sols_json(r.solutions_head)<<"}"; return o.str(); }

int main(int argc,char**argv){
    std::string cons,cuts_path,outp,force_s,exclude_s; int target=19, branch=-2; double lim=60.0;
    for(int i=1;i<argc;i++){ std::string a=argv[i]; if(a=="--constraints"&&i+1<argc) cons=argv[++i]; else if(a=="--cuts"&&i+1<argc) cuts_path=argv[++i]; else if(a=="--output"&&i+1<argc) outp=argv[++i]; else if(a=="--target"&&i+1<argc) target=std::stoi(argv[++i]); else if(a=="--timeout"&&i+1<argc) lim=std::stod(argv[++i]); else if(a=="--branch"&&i+1<argc) branch=std::stoi(argv[++i]); else if(a=="--all-branches") branch=-1; else if(a=="--force"&&i+1<argc) force_s=argv[++i]; else if(a=="--exclude"&&i+1<argc) exclude_s=argv[++i]; else { std::cerr<<"bad arg "<<a<<"\n"; return 2; } }
    if(cons.empty()){ std::cerr<<"usage: --constraints FILE --target N [--cuts FILE] [--branch B|--all-branches] [--force a,b] [--exclude a,b] [--timeout S] [--output FILE]\n"; return 2; }
    std::vector<Constraint> rows; if(!load_constraints(cons,rows)) return 1; auto pr=point_rows_of(rows); std::vector<MixedCut> cuts; if(!load_cuts(cuts_path,cuts)) return 1;
    std::vector<int> force=parse_list(force_s), exclude=parse_list(exclude_s); uint64_t forbidden[4]={0,0,0,0}; for(int p:exclude) setbit4(forbidden,p);
    std::vector<Result> results; auto branches=default_branches();
    if(branch>=-1){ for(auto& br:branches){ if(branch>=0 && br.id!=branch) continue; uint64_t forb[4]; for(int w=0;w<4;w++) forb[w]=forbidden[w]|br.forbid[w]; auto f=force; f.push_back(br.rep); std::sort(f.begin(),f.end()); f.erase(std::unique(f.begin(),f.end()),f.end()); Searcher S(rows,pr,cuts,target,lim); auto r=S.run(forb,f,br.rep+1,br.id,br.rep); results.push_back(r); std::cout<<rjson(r)<<"\n"; std::cout.flush(); } }
    else { Searcher S(rows,pr,cuts,target,lim); auto r=S.run(forbidden,force,1,-1,0); results.push_back(r); std::cout<<rjson(r)<<"\n"; }
    bool all=true; uint64_t sol=0,calls=0,tests=0,over=0,shortage=0,mpr=0,mchk=0,sat=0,satrem=0; int md=0; std::array<uint64_t,32> nodes{}; nodes.fill(0); std::array<uint64_t,32> mpd{}; mpd.fill(0);
    for(auto&r:results){ all&=r.complete; sol+=r.solutions; calls+=r.recursive_calls; tests+=r.candidate_tests; over+=r.overcap_rejects; shortage+=r.global_shortage; mpr+=r.mixed_prunes; mchk+=r.mixed_checks; sat+=r.saturated_rows; satrem+=r.saturation_point_removals; md=std::max(md,r.max_depth); for(int i=0;i<32;i++){nodes[i]+=r.node_count[i]; mpd[i]+=r.mixed_prune_depth[i];}}
    std::ostringstream out; out<<"{\n  \"schema\": \"s0908_sound_domain_mixed_dfs_v1\",\n  \"semantics\": \"Wang upper-bound saturation plus mixed lower-cut future-upper-bound pruning; no lower fill obligation for Wang rows\",\n  \"constraints_path\": \""<<cons<<"\",\n  \"cut_path\": \""<<cuts_path<<"\",\n  \"constraint_count\": "<<rows.size()<<",\n  \"mixed_cut_count\": "<<cuts.size()<<",\n  \"target\": "<<target<<",\n  \"time_limit_per_run_sec\": "<<lim<<",\n  \"all_complete\": "<<(all?"true":"false")<<",\n  \"total_solutions\": "<<sol<<",\n  \"global_max_depth\": "<<md<<",\n  \"total_recursive_calls\": "<<calls<<",\n  \"total_candidate_tests\": "<<tests<<",\n  \"total_overcap_rejects\": "<<over<<",\n  \"total_global_shortage\": "<<shortage<<",\n  \"total_mixed_prunes\": "<<mpr<<",\n  \"total_mixed_checks\": "<<mchk<<",\n  \"total_saturated_rows\": "<<sat<<",\n  \"total_saturation_point_removals\": "<<satrem<<",\n  \"total_node_count_by_depth\": "<<arr_json(nodes,std::min(31,target))<<",\n  \"total_mixed_prune_depth\": "<<arr_json(mpd,std::min(31,target))<<",\n  \"results\": [\n"; for(size_t i=0;i<results.size();i++){ out<<"    "<<rjson(results[i]); if(i+1<results.size()) out<<","; out<<"\n";} out<<"  ]\n}\n";
    if(!outp.empty()){ std::ofstream f(outp); f<<out.str(); std::cerr<<"wrote "<<outp<<"\n"; }
    return 0;
}
