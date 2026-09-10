// Bitset-domain DFS for E11 Wang constraints.
//
// Maintains candidate domains for future points instead of scanning all row
// memberships for every trial point.  For each Wang row with cap c, when the
// current occupancy reaches c we intersect the future domain with the complement
// of that row's point set.  For small cap constraints this is much faster and
// gives an exact deterministic exhaustive search when it completes.

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
struct Result { int branch=-1, rep=0, max_depth=0; double elapsed=0; bool timeout=false, complete=false; uint64_t calls=0, solutions=0, domain_nodes=0; std::array<uint64_t,20> node{}; std::vector<std::vector<int>> head; };
static bool bit4(const uint64_t w[4], int p){return (w[p>>6]>>(p&63))&1ULL;}
static int pc64(uint64_t x){return __builtin_popcountll(x);} 
static std::string arrj(const std::array<uint64_t,20>& a){std::ostringstream o;o<<"[";for(int i=0;i<20;i++){if(i)o<<",";o<<a[i];}o<<"]";return o.str();}
static std::string vecj(const std::vector<int>& v){std::ostringstream o;o<<"[";for(size_t i=0;i<v.size();i++){if(i)o<<",";o<<v[i];}o<<"]";return o.str();}

static bool load(const std::string& p, std::vector<Constraint>& rows){std::ifstream in(p,std::ios::binary);if(!in){std::cerr<<"open fail\n";return false;}char m[8];in.read(m,8);if(std::memcmp(m,"E11WANG1",8)){std::cerr<<"magic fail\n";return false;}uint32_t n;in.read((char*)&n,4);rows.resize(n);for(uint32_t i=0;i<n;i++){in.read((char*)&rows[i].cap,1);in.read((char*)&rows[i].dim,1);in.read((char*)&rows[i].reserved,2);for(int j=0;j<4;j++)in.read((char*)&rows[i].word[j],8);}return bool(in);} 
static std::vector<std::vector<uint32_t>> point_rows(const std::vector<Constraint>& rows){std::vector<std::vector<uint32_t>> pr(256);for(uint32_t i=0;i<rows.size();i++)for(int p=1;p<=255;p++)if(bit4(rows[i].word,p))pr[p].push_back(i);return pr;}
static void clear_leq(uint64_t w[4], int q){ // remove points <= q, and bit0
    if(q<0) return; int full=q>>6; int rem=q&63; for(int i=0;i<full;i++) w[i]=0; if(full<4){ uint64_t mask = (rem==63?~0ULL:((1ULL<<(rem+1))-1ULL)); w[full]&=~mask; } w[0]&=~1ULL;
}
static int bitset_count(const uint64_t w[4]){return pc64(w[0])+pc64(w[1])+pc64(w[2])+pc64(w[3]);}
static int next_bit(uint64_t w[4], int after){ for(int p=after+1;p<=255;p++) if(bit4(w,p)) return p; return 256; }
static void andnot(uint64_t dst[4], const uint64_t sub[4]){for(int i=0;i<4;i++) dst[i]&=~sub[i];}
static void band(uint64_t dst[4], const uint64_t src[4]){for(int i=0;i<4;i++) dst[i]&=src[i];}
static void copy4(uint64_t d[4], const uint64_t s[4]){for(int i=0;i<4;i++)d[i]=s[i];}
static bool empty4(const uint64_t w[4]){return !(w[0]|w[1]|w[2]|w[3]);}
static std::vector<BranchSpec> branches(){ const int reps[8]={1,4,5,8,10,40,42,80}; const std::vector<std::vector<int>> members={ {1,2,3},{4,32,36},{5,6,7,33,34,35,37,38,39},{8,9,12,13,16,18,20,22,24,27,28,31,64,65,72,73,96,97,108,109,128,130,144,146,160,162,180,182,192,195,216,219,224,227,252,255},{10,11,14,15,17,19,21,23,25,26,29,30,66,67,74,75,98,99,110,111,129,131,145,147,161,163,181,183,193,194,217,218,225,226,253,254},{40,41,44,45,48,50,52,54,56,59,60,63,68,69,76,77,100,101,104,105,132,134,148,150,164,166,176,178,196,199,220,223,228,231,248,251},{42,43,46,47,49,51,53,55,57,58,61,62,70,71,78,79,102,103,106,107,133,135,149,151,165,167,177,179,197,198,221,222,229,230,249,250},{80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,136,137,138,139,140,141,142,143,152,153,154,155,156,157,158,159,168,169,170,171,172,173,174,175,184,185,186,187,188,189,190,191,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247} }; std::vector<BranchSpec> out; uint64_t forb[4]={0,0,0,0}; for(int i=0;i<8;i++){BranchSpec b;b.id=i;b.rep=reps[i];for(int j=0;j<4;j++)b.forbid[j]=forb[j];out.push_back(b);for(int p:members[i])forb[p>>6]|=1ULL<<(p&63);} return out; }

struct Search{
    const std::vector<Constraint>& rows; const std::vector<std::vector<uint32_t>>& pr; int target; double limit; std::chrono::steady_clock::time_point st; std::vector<uint8_t> occ; std::vector<int> chosen; Result r;
    Search(const std::vector<Constraint>& R,const std::vector<std::vector<uint32_t>>& P,int t,double l):rows(R),pr(P),target(t),limit(l),occ(R.size(),0){}
    bool timeout(){return limit>0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count()>=limit;}
    void dfs(int depth, uint64_t domain[4]){
        if(r.timeout) return; if((r.calls++ & 0x3FFFULL)==0 && timeout()){r.timeout=true;return;} if(depth>r.max_depth)r.max_depth=depth;
        int rem=target-depth; if(bitset_count(domain)<rem) return;
        if(depth==target){r.solutions++; if(r.head.size()<5)r.head.push_back(chosen); return;}
        // enumerate candidates in current domain
        uint64_t iter[4]; copy4(iter,domain);
        while(!empty4(iter)){
            int q=next_bit(iter,0); if(q>255) break; iter[q>>6]&=~(1ULL<<(q&63));
            uint64_t ndom[4]; copy4(ndom,domain); clear_leq(ndom,q);
            bool ok=true;
            // add q; if a row becomes saturated, remove all its points from future domain.
            for(uint32_t ri: pr[q]){
                uint8_t nv=++occ[ri];
                if(nv>rows[ri].cap){ ok=false; }
                else if(nv==rows[ri].cap){ andnot(ndom, rows[ri].word); }
            }
            if(ok && bitset_count(ndom)>=rem-1){ r.node[depth+1]++; chosen.push_back(q); dfs(depth+1,ndom); chosen.pop_back(); }
            for(uint32_t ri: pr[q]) occ[ri]--; if(r.timeout)return;
        }
    }
    Result run_branch(const BranchSpec& b){ r=Result(); r.branch=b.id; r.rep=b.rep; r.node.fill(0); r.node[0]=1; std::fill(occ.begin(),occ.end(),0); chosen.clear(); st=std::chrono::steady_clock::now();
        uint64_t dom[4]={~0ULL,~0ULL,~0ULL,~0ULL}; dom[0]&=~1ULL; for(int i=0;i<4;i++) dom[i]&=~b.forbid[i];
        // force rep and create domain > rep with saturated rows removed
        uint64_t ndom[4]; copy4(ndom,dom); clear_leq(ndom,b.rep); bool ok=bit4(dom,b.rep);
        if(ok){ for(uint32_t ri: pr[b.rep]){ uint8_t nv=++occ[ri]; if(nv>rows[ri].cap) ok=false; else if(nv==rows[ri].cap) andnot(ndom,rows[ri].word); } }
        if(ok){ r.node[1]=1; chosen.push_back(b.rep); dfs(1,ndom); chosen.pop_back(); }
        if(ok){ for(uint32_t ri: pr[b.rep]) occ[ri]--; }
        r.elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count(); r.complete=!r.timeout; return r; }
};
static std::string rjson(const Result& r){std::ostringstream o;o<<"{\"branch\":"<<r.branch<<",\"rep\":"<<r.rep<<",\"elapsed_sec\":"<<std::fixed<<std::setprecision(6)<<r.elapsed<<",\"timeout\":"<<(r.timeout?"true":"false")<<",\"complete\":"<<(r.complete?"true":"false")<<",\"calls\":"<<r.calls<<",\"max_depth\":"<<r.max_depth<<",\"solutions\":"<<r.solutions<<",\"node_count_by_depth\":"<<arrj(r.node)<<",\"solutions_head\":["; for(size_t i=0;i<r.head.size();i++){if(i)o<<",";o<<vecj(r.head[i]);} o<<"]}"; return o.str();}
int main(int argc,char**argv){std::string cons="data/wang_native/e11_wang_cap5.bin",outp="data/wang_native/bitset_dfs.json";int depth=19,only=-1;double lim=60;for(int i=1;i<argc;i++){std::string a=argv[i];if(a=="--constraints"&&i+1<argc)cons=argv[++i];else if(a=="--out"&&i+1<argc)outp=argv[++i];else if(a=="--depth"&&i+1<argc)depth=std::stoi(argv[++i]);else if(a=="--branch"&&i+1<argc)only=std::stoi(argv[++i]);else if(a=="--time-limit"&&i+1<argc)lim=std::stod(argv[++i]);else{std::cerr<<"bad arg "<<a<<"\n";return 2;}}std::vector<Constraint> rows;if(!load(cons,rows))return 1;auto pr=point_rows(rows);std::cerr<<"Loaded "<<rows.size()<<" constraints\n";auto t0=std::chrono::steady_clock::now();Search S(rows,pr,depth,lim);std::vector<Result> res;for(auto&b:branches()){if(only>=0&&b.id!=only)continue;std::cerr<<"Branch "<<b.id<<" rep "<<b.rep<<"\n";auto rr=S.run_branch(b);res.push_back(rr);std::cout<<rjson(rr)<<"\n"<<std::flush;}bool all=true;uint64_t sol=0,calls=0;int md=0;std::array<uint64_t,20> nodes{};nodes.fill(0);for(auto&r:res){all&=r.complete;sol+=r.solutions;calls+=r.calls;md=std::max(md,r.max_depth);for(int d=0;d<20;d++)nodes[d]+=r.node[d];}double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();std::ofstream out(outp);out<<"{\n  \"status\": \"ok\",\n  \"constraints_path\": \""<<cons<<"\",\n  \"constraint_count\": "<<rows.size()<<",\n  \"target_depth\": "<<depth<<",\n  \"per_branch_time_limit_sec\": "<<lim<<",\n  \"elapsed_sec\": "<<std::fixed<<std::setprecision(6)<<el<<",\n  \"all_complete\": "<<(all?"true":"false")<<",\n  \"total_solutions\": "<<sol<<",\n  \"global_max_depth\": "<<md<<",\n  \"total_calls\": "<<calls<<",\n  \"total_node_count_by_depth\": "<<arrj(nodes)<<",\n  \"branches\": [\n";for(size_t i=0;i<res.size();i++){out<<"    "<<rjson(res[i]);if(i+1<res.size())out<<",";out<<"\n";}out<<"  ]\n}\n";std::cerr<<"Wrote "<<outp<<"\n";return 0;}
