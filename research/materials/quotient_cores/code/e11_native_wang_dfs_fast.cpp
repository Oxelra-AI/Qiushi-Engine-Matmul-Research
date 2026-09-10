// Faster native deterministic DFS for E11 Wang-admissible supports.
//
// Difference from e11_native_wang_dfs.cpp: avoids per-candidate vector allocation;
// increments counts along point_rows[q] and undoes the prefix of the same array.

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

struct Constraint { uint8_t cap; uint8_t dim; uint16_t reserved; uint64_t word[4]; };
struct BranchSpec { int id=-1; int rep=0; uint64_t forbid[4]={0,0,0,0}; };
struct BranchResult {
    int branch=-1, rep=0, max_depth=0; double elapsed_sec=0.0; bool timeout=false, complete=false;
    uint64_t recursive_calls=0, candidate_tests=0, candidate_violations=0, solutions=0;
    std::array<uint64_t,20> node_count{}; std::vector<std::vector<int>> solutions_head;
};
static bool bit4(const uint64_t w[4], int p){ return (w[p>>6]>>(p&63))&1ULL; }
static std::string arr_json(const std::array<uint64_t,20>& a){ std::ostringstream o; o<<"["; for(int i=0;i<20;i++){ if(i)o<<","; o<<a[i]; } o<<"]"; return o.str(); }
static std::string vec_json(const std::vector<int>& v){ std::ostringstream o; o<<"["; for(size_t i=0;i<v.size();i++){ if(i)o<<","; o<<v[i]; } o<<"]"; return o.str(); }

static bool load_constraints(const std::string& path, std::vector<Constraint>& rows){
    std::ifstream in(path, std::ios::binary); if(!in){ std::cerr<<"cannot open "<<path<<"\n"; return false; }
    char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"E11WANG1",8)!=0){ std::cerr<<"bad magic\n"; return false; }
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); rows.resize(n);
    for(uint32_t i=0;i<n;i++){
        in.read(reinterpret_cast<char*>(&rows[i].cap),1); in.read(reinterpret_cast<char*>(&rows[i].dim),1); in.read(reinterpret_cast<char*>(&rows[i].reserved),2);
        for(int j=0;j<4;j++) in.read(reinterpret_cast<char*>(&rows[i].word[j]),8);
    }
    if(!in){ std::cerr<<"short read\n"; return false; } return true;
}
static std::vector<std::vector<uint32_t>> point_rows_of(const std::vector<Constraint>& rows){
    std::vector<std::vector<uint32_t>> pr(256);
    for(uint32_t i=0;i<rows.size();i++) for(int p=1;p<=255;p++) if(bit4(rows[i].word,p)) pr[p].push_back(i);
    return pr;
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
    std::vector<BranchSpec> out; uint64_t forbid[4]={0,0,0,0};
    for(int i=0;i<8;i++){ BranchSpec b; b.id=i; b.rep=reps[i]; for(int w=0;w<4;w++) b.forbid[w]=forbid[w]; out.push_back(b); for(int p:members[i]) forbid[p>>6]|=1ULL<<(p&63); }
    return out;
}

struct Searcher{
    const std::vector<Constraint>& rows; const std::vector<std::vector<uint32_t>>& pr; int depth_target; double limit;
    std::chrono::steady_clock::time_point start; BranchResult res; std::vector<uint8_t> counts; std::vector<int> chosen; uint64_t allowed[4]; int store=5;
    Searcher(const std::vector<Constraint>& r, const std::vector<std::vector<uint32_t>>& p, int d, double l): rows(r),pr(p),depth_target(d),limit(l),counts(r.size(),0){ }
    bool timed() const { return limit>0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=limit; }
    bool is_allowed(int q) const { return bit4(allowed,q); }
    bool add_noalloc(int q, size_t& touched){
        const auto& L=pr[q]; touched=0; res.candidate_tests++;
        for(size_t i=0;i<L.size();i++){ uint32_t ri=L[i]; uint8_t nv=counts[ri]+1; counts[ri]=nv; touched=i+1; if(nv>rows[ri].cap){ res.candidate_violations++; return false; } }
        return true;
    }
    void undo_noalloc(int q, size_t touched){ const auto& L=pr[q]; for(size_t i=0;i<touched;i++) counts[L[i]]--; }
    void dfs(int minq, int depth){
        if(res.timeout) return; if((res.recursive_calls++ & 0x3FFFULL)==0 && timed()){ res.timeout=true; return; }
        if(depth>res.max_depth) res.max_depth=depth;
        if(depth==depth_target){ res.solutions++; if((int)res.solutions_head.size()<store) res.solutions_head.push_back(chosen); return; }
        int rem=depth_target-depth;
        for(int q=minq;q<=255;q++){
            if(256-q<rem) break; if(!is_allowed(q)) continue;
            size_t touched=0; bool ok=add_noalloc(q,touched);
            if(ok){ res.node_count[depth+1]++; chosen.push_back(q); dfs(q+1, depth+1); chosen.pop_back(); }
            undo_noalloc(q,touched); if(res.timeout) return;
        }
    }
    BranchResult run_branch(const BranchSpec& br){
        res=BranchResult(); res.branch=br.id; res.rep=br.rep; res.node_count.fill(0); res.node_count[0]=1; std::fill(counts.begin(),counts.end(),0); chosen.clear();
        allowed[0]=allowed[1]=allowed[2]=allowed[3]=~0ULL; allowed[0]&=~1ULL; for(int w=0;w<4;w++) allowed[w]&=~br.forbid[w]; start=std::chrono::steady_clock::now();
        size_t touched=0; bool ok=is_allowed(br.rep)&&add_noalloc(br.rep,touched);
        if(ok){ res.node_count[1]=1; chosen.push_back(br.rep); dfs(br.rep+1,1); chosen.pop_back(); }
        undo_noalloc(br.rep,touched); res.elapsed_sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count(); res.complete=!res.timeout; return res;
    }
};
static std::string bj(const BranchResult& r){
    std::ostringstream o; o<<"{\"branch\":"<<r.branch<<",\"rep\":"<<r.rep<<",\"elapsed_sec\":"<<std::fixed<<std::setprecision(6)<<r.elapsed_sec
     <<",\"timeout\":"<<(r.timeout?"true":"false")<<",\"complete\":"<<(r.complete?"true":"false")<<",\"recursive_calls\":"<<r.recursive_calls
     <<",\"candidate_tests\":"<<r.candidate_tests<<",\"candidate_violations\":"<<r.candidate_violations<<",\"max_depth\":"<<r.max_depth<<",\"solutions\":"<<r.solutions
     <<",\"node_count_by_depth\":"<<arr_json(r.node_count)<<",\"solutions_head\": [";
    for(size_t i=0;i<r.solutions_head.size();i++){ if(i)o<<","; o<<vec_json(r.solutions_head[i]); } o<<"]}"; return o.str();
}
int main(int argc,char**argv){
    std::string cons="data/wang_native/e11_wang_cap5.bin", outp="data/wang_native/native_dfs_fast_cap5.json"; int depth=19, only=-1; double lim=60.0;
    for(int i=1;i<argc;i++){ std::string a=argv[i]; if(a=="--constraints"&&i+1<argc) cons=argv[++i]; else if(a=="--out"&&i+1<argc) outp=argv[++i]; else if(a=="--depth"&&i+1<argc) depth=std::stoi(argv[++i]); else if(a=="--branch"&&i+1<argc) only=std::stoi(argv[++i]); else if(a=="--time-limit"&&i+1<argc) lim=std::stod(argv[++i]); else { std::cerr<<"bad arg "<<a<<"\n"; return 2; } }
    std::vector<Constraint> rows; if(!load_constraints(cons,rows)) return 1; auto pr=point_rows_of(rows); std::cerr<<"Loaded "<<rows.size()<<" constraints\n";
    auto t0=std::chrono::steady_clock::now(); Searcher S(rows,pr,depth,lim); std::vector<BranchResult> results;
    for(const auto& br: default_branches()){ if(only>=0&&br.id!=only) continue; std::cerr<<"Branch "<<br.id<<" rep "<<br.rep<<"\n"; auto r=S.run_branch(br); results.push_back(r); std::cout<<bj(r)<<"\n"; std::cout.flush(); }
    bool all=true; uint64_t sol=0; int md=0; std::array<uint64_t,20> nodes{}; nodes.fill(0); uint64_t calls=0, tests=0, viol=0;
    for(auto&r:results){ all&=r.complete; sol+=r.solutions; md=std::max(md,r.max_depth); calls+=r.recursive_calls; tests+=r.candidate_tests; viol+=r.candidate_violations; for(int d=0;d<20;d++) nodes[d]+=r.node_count[d]; }
    double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();
    std::ofstream out(outp); out<<"{\n  \"status\": \"ok\",\n  \"constraints_path\": \""<<cons<<"\",\n  \"constraint_count\": "<<rows.size()<<",\n  \"target_depth\": "<<depth<<",\n  \"per_branch_time_limit_sec\": "<<lim<<",\n  \"elapsed_sec\": "<<std::fixed<<std::setprecision(6)<<elapsed<<",\n  \"all_complete\": "<<(all?"true":"false")<<",\n  \"total_solutions\": "<<sol<<",\n  \"global_max_depth\": "<<md<<",\n  \"total_recursive_calls\": "<<calls<<",\n  \"total_candidate_tests\": "<<tests<<",\n  \"total_candidate_violations\": "<<viol<<",\n  \"total_node_count_by_depth\": "<<arr_json(nodes)<<",\n  \"branches\": [\n";
    for(size_t i=0;i<results.size();i++){ out<<"    "<<bj(results[i]); if(i+1<results.size()) out<<","; out<<"\n"; } out<<"  ]\n}\n"; std::cerr<<"Wrote "<<outp<<"\n"; return 0;
}
