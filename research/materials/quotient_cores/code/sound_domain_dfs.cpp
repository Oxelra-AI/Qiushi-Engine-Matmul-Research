// analysis: sound domain-propagation DFS for E11 Wang upper-bound rows.
//
// Semantics: each row is an upper bound |S cap R| <= cap. The only domain
// propagation used here is saturation: once count(R)==cap, no future point in R
// may be selected. There is no requirement to fill unused row capacity.
// Counter updates are transactional: only rows actually incremented are undone.
//
// Binary input format is E11WANG1 used by the peer native scripts.

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

struct Constraint {
    uint8_t cap = 0;
    uint8_t dim = 0;
    uint16_t reserved = 0;
    uint64_t word[4] = {0,0,0,0};
};

struct BranchSpec { int id=-1; int rep=0; uint64_t forbid[4]={0,0,0,0}; };

struct Result {
    int branch=-1, rep=0, target=0, max_point=MAXPTS, max_depth=0;
    double elapsed_sec=0.0;
    bool timeout=false, complete=false, forced_infeasible=false;
    uint64_t recursive_calls=0, candidate_tests=0, overcap_rejects=0, global_shortage=0;
    uint64_t saturated_rows=0, saturation_point_removals=0, initial_zero_cap_removals=0;
    uint64_t solutions=0;
    std::array<uint64_t, 32> node_count{};
    std::vector<std::vector<int>> solutions_head;
};

static bool bit4(const uint64_t w[4], int p){ return (w[p>>6]>>(p&63))&1ULL; }
static void setbit4(uint64_t w[4], int p){ w[p>>6] |= 1ULL<<(p&63); }

static std::string json_array_u64(const std::array<uint64_t,32>& a, int upto){
    std::ostringstream o; o << "[";
    for(int i=0;i<=upto && i<(int)a.size();i++){ if(i) o << ","; o << a[i]; }
    o << "]"; return o.str();
}
static std::string json_vec(const std::vector<int>& v){
    std::ostringstream o; o << "[";
    for(size_t i=0;i<v.size();i++){ if(i) o << ","; o << v[i]; }
    o << "]"; return o.str();
}
static std::string json_solutions(const std::vector<std::vector<int>>& sols){
    std::ostringstream o; o << "[";
    for(size_t i=0;i<sols.size();i++){ if(i) o << ","; o << json_vec(sols[i]); }
    o << "]"; return o.str();
}

static bool load_constraints(const std::string& path, std::vector<Constraint>& rows){
    std::ifstream in(path, std::ios::binary);
    if(!in){ std::cerr << "cannot open " << path << "\n"; return false; }
    char magic[8]; in.read(magic, 8);
    if(!in || std::memcmp(magic, "E11WANG1", 8)!=0){ std::cerr << "bad magic\n"; return false; }
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n), 4);
    rows.resize(n);
    for(uint32_t i=0;i<n;i++){
        in.read(reinterpret_cast<char*>(&rows[i].cap), 1);
        in.read(reinterpret_cast<char*>(&rows[i].dim), 1);
        in.read(reinterpret_cast<char*>(&rows[i].reserved), 2);
        for(int j=0;j<4;j++) in.read(reinterpret_cast<char*>(&rows[i].word[j]), 8);
    }
    if(!in){ std::cerr << "short read\n"; return false; }
    return true;
}

static std::vector<std::vector<uint32_t>> point_rows_of(const std::vector<Constraint>& rows, int max_point){
    std::vector<std::vector<uint32_t>> pr(max_point+1);
    for(uint32_t ri=0; ri<rows.size(); ri++){
        for(int p=1; p<=max_point; p++) if(bit4(rows[ri].word, p)) pr[p].push_back(ri);
    }
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
    for(int i=0;i<8;i++){
        BranchSpec b; b.id=i; b.rep=reps[i];
        for(int w=0;w<4;w++) b.forbid[w]=forbid[w];
        out.push_back(b);
        for(int p:members[i]) setbit4(forbid,p);
    }
    return out;
}

static std::vector<int> parse_list(const std::string& s){
    std::vector<int> out; size_t pos=0;
    while(pos<s.size()){
        size_t next=s.find(',', pos); if(next==std::string::npos) next=s.size();
        if(next>pos){ int p=std::stoi(s.substr(pos,next-pos)); if(p>=1 && p<=MAXPTS) out.push_back(p); }
        pos=next+1;
    }
    std::sort(out.begin(), out.end()); out.erase(std::unique(out.begin(), out.end()), out.end());
    return out;
}

struct Searcher {
    const std::vector<Constraint>& rows;
    const std::vector<std::vector<uint32_t>>& point_rows;
    int max_point=MAXPTS, target=19, store_limit=5;
    double time_limit=60.0;
    std::chrono::steady_clock::time_point start;
    std::vector<uint8_t> counts;
    std::vector<char> domain;
    std::vector<int> chosen;
    Result res;

    Searcher(const std::vector<Constraint>& r, const std::vector<std::vector<uint32_t>>& pr, int mp, int t, double lim)
        : rows(r), point_rows(pr), max_point(mp), target(t), time_limit(lim), counts(r.size(),0), domain(mp+1,1) {
        domain[0]=0;
    }
    bool timed() const { return time_limit>0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count() >= time_limit; }
    void remove_domain(int q, std::vector<int>& removed){ if(q>=1 && q<=max_point && domain[q]){ domain[q]=0; removed.push_back(q); } }
    int avail_from(int minq) const { int c=0; for(int q=minq;q<=max_point;q++) if(domain[q]) c++; return c; }
    void restore_removed(const std::vector<int>& removed){ for(auto it=removed.rbegin(); it!=removed.rend(); ++it) domain[*it]=1; }

    bool propagate_zero_caps(uint64_t forbidden[4]){
        std::vector<int> removed;
        for(int q=1;q<=max_point;q++) if(bit4(forbidden,q)) domain[q]=0;
        for(uint32_t ri=0; ri<rows.size(); ri++) if(rows[ri].cap==0){
            for(int w=0; w<4; w++){
                uint64_t m=rows[ri].word[w];
                while(m){ int bit=__builtin_ctzll(m); int q=w*64+bit; m&=m-1; if(q>=1 && q<=max_point) remove_domain(q, removed); }
            }
        }
        res.initial_zero_cap_removals = removed.size();
        return true;
    }

    bool try_select(int q, std::vector<uint32_t>& touched, std::vector<int>& removed){
        res.candidate_tests++;
        if(q<1 || q>max_point || !domain[q]) return false;
        const auto& L = point_rows[q];
        for(uint32_t ri: L){
            if((int)counts[ri] + 1 > (int)rows[ri].cap){ res.overcap_rejects++; return false; }
        }
        remove_domain(q, removed);
        for(uint32_t ri: L){ counts[ri]++; touched.push_back(ri); }
        for(uint32_t ri: touched){
            if(counts[ri] == rows[ri].cap){
                res.saturated_rows++;
                for(int w=0; w<4; w++){
                    uint64_t m=rows[ri].word[w];
                    while(m){
                        int bit=__builtin_ctzll(m); int s=w*64+bit; m&=m-1;
                        if(s>=1 && s<=max_point && domain[s]){ res.saturation_point_removals++; remove_domain(s, removed); }
                    }
                }
            }
        }
        return true;
    }
    void undo_select(const std::vector<uint32_t>& touched, const std::vector<int>& removed){
        for(auto it=touched.rbegin(); it!=touched.rend(); ++it) counts[*it]--;
        restore_removed(removed);
    }

    bool force_points(const std::vector<int>& force){
        for(int p: force){
            if(p<1 || p>max_point || !domain[p]) { res.forced_infeasible=true; return false; }
            std::vector<uint32_t> touched; std::vector<int> removed;
            bool ok = try_select(p, touched, removed);
            if(!ok){ undo_select(touched, removed); res.forced_infeasible=true; return false; }
            // Forced selections are permanent for this run, so deliberately keep
            // touched increments and removed domain entries. Store p in chosen.
            chosen.push_back(p);
        }
        return true;
    }

    void dfs(int minq){
        if(res.timeout) return;
        if((res.recursive_calls++ & 0x3FFFULL)==0 && timed()){ res.timeout=true; return; }
        int depth=(int)chosen.size();
        if(depth>res.max_depth) res.max_depth=depth;
        if(depth == target){
            res.solutions++;
            if((int)res.solutions_head.size()<store_limit){ auto sol=chosen; std::sort(sol.begin(), sol.end()); res.solutions_head.push_back(sol); }
            return;
        }
        int need = target - depth;
        if(avail_from(minq) < need){ res.global_shortage++; return; }
        for(int q=minq; q<=max_point; q++){
            if(max_point - q + 1 < need) break;
            if(!domain[q]) continue;
            if(avail_from(q) < need) break;
            std::vector<uint32_t> touched; std::vector<int> removed;
            bool ok = try_select(q, touched, removed);
            if(ok){
                chosen.push_back(q);
                int d=(int)chosen.size(); if(d<(int)res.node_count.size()) res.node_count[d]++;
                dfs(q+1);
                chosen.pop_back();
            }
            undo_select(touched, removed);
            if(res.timeout) return;
            if(res.solutions > 100) return;
        }
    }

    Result run(uint64_t forbidden[4], const std::vector<int>& force, int min_after_force, int branch, int rep){
        res=Result(); res.branch=branch; res.rep=rep; res.target=target; res.max_point=max_point; res.node_count.fill(0); res.node_count[0]=1;
        std::fill(counts.begin(), counts.end(), 0); std::fill(domain.begin(), domain.end(), 1); domain[0]=0; chosen.clear();
        start=std::chrono::steady_clock::now();
        propagate_zero_caps(forbidden);
        bool ok = force_points(force);
        if(ok){ int d=(int)chosen.size(); if(d<(int)res.node_count.size()) res.node_count[d]=std::max<uint64_t>(res.node_count[d],1); dfs(min_after_force); }
        res.elapsed_sec = std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        res.complete = !res.timeout;
        return res;
    }
};

static std::string result_json(const Result& r){
    std::ostringstream o;
    o << "{\"branch\":" << r.branch << ",\"rep\":" << r.rep << ",\"target\":" << r.target
      << ",\"max_point\":" << r.max_point << ",\"elapsed_sec\":" << std::fixed << std::setprecision(6) << r.elapsed_sec
      << ",\"timeout\":" << (r.timeout?"true":"false") << ",\"complete\":" << (r.complete?"true":"false")
      << ",\"forced_infeasible\":" << (r.forced_infeasible?"true":"false")
      << ",\"recursive_calls\":" << r.recursive_calls << ",\"candidate_tests\":" << r.candidate_tests
      << ",\"overcap_rejects\":" << r.overcap_rejects << ",\"global_shortage\":" << r.global_shortage
      << ",\"saturated_rows\":" << r.saturated_rows << ",\"saturation_point_removals\":" << r.saturation_point_removals
      << ",\"initial_zero_cap_removals\":" << r.initial_zero_cap_removals
      << ",\"solutions\":" << r.solutions << ",\"max_depth\":" << r.max_depth
      << ",\"node_count_by_depth\":" << json_array_u64(r.node_count, std::min(31,r.target))
      << ",\"solutions_head\":" << json_solutions(r.solutions_head) << "}";
    return o.str();
}

int main(int argc, char** argv){
    std::string cons="", outp="", force_s="", exclude_s="";
    int target=19, max_point=MAXPTS, only_branch=-2; // -2 means no branch mode; -1 all branches
    double lim=60.0;
    for(int i=1;i<argc;i++){
        std::string a=argv[i];
        if(a=="--constraints" && i+1<argc) cons=argv[++i];
        else if(a=="--output" && i+1<argc) outp=argv[++i];
        else if(a=="--target" && i+1<argc) target=std::stoi(argv[++i]);
        else if(a=="--max-point" && i+1<argc) max_point=std::stoi(argv[++i]);
        else if(a=="--timeout" && i+1<argc) lim=std::stod(argv[++i]);
        else if(a=="--branch" && i+1<argc) only_branch=std::stoi(argv[++i]);
        else if(a=="--all-branches") only_branch=-1;
        else if(a=="--force" && i+1<argc) force_s=argv[++i];
        else if(a=="--exclude" && i+1<argc) exclude_s=argv[++i];
        else { std::cerr << "bad arg " << a << "\n"; return 2; }
    }
    if(cons.empty()){ std::cerr << "usage: sound_domain_dfs --constraints FILE --target N [--branch B|--all-branches] [--force a,b] [--exclude a,b] [--max-point M] [--timeout S] [--output FILE]\n"; return 2; }
    if(max_point<1 || max_point>MAXPTS){ std::cerr << "bad max-point\n"; return 2; }
    std::vector<Constraint> rows; if(!load_constraints(cons, rows)) return 1;
    auto pr = point_rows_of(rows, max_point);
    std::vector<int> force = parse_list(force_s), exclude = parse_list(exclude_s);
    uint64_t forbidden[4]={0,0,0,0}; for(int p: exclude) setbit4(forbidden,p);
    std::vector<Result> results;
    auto run_one = [&](int branch, int rep, uint64_t forb[4], std::vector<int> f, int min_after){
        Searcher S(rows, pr, max_point, target, lim);
        return S.run(forb, f, min_after, branch, rep);
    };
    if(only_branch >= -1){
        auto branches = default_branches();
        for(const auto& br: branches){
            if(only_branch>=0 && br.id!=only_branch) continue;
            uint64_t forb[4]; for(int w=0;w<4;w++) forb[w]=forbidden[w] | br.forbid[w];
            auto f=force; f.push_back(br.rep); std::sort(f.begin(),f.end()); f.erase(std::unique(f.begin(),f.end()),f.end());
            Result r = run_one(br.id, br.rep, forb, f, br.rep+1);
            results.push_back(r); std::cout << result_json(r) << "\n"; std::cout.flush();
        }
    } else {
        Result r = run_one(-1, 0, forbidden, force, 1);
        results.push_back(r); std::cout << result_json(r) << "\n";
    }
    bool all_complete=true; uint64_t sol=0,calls=0,tests=0,over=0,shortage=0,satrows=0,satrem=0,zero=0; int md=0;
    std::array<uint64_t,32> nodes{}; nodes.fill(0);
    for(auto& r: results){
        all_complete &= r.complete; sol += r.solutions; calls += r.recursive_calls; tests += r.candidate_tests; over += r.overcap_rejects;
        shortage += r.global_shortage; satrows += r.saturated_rows; satrem += r.saturation_point_removals; zero += r.initial_zero_cap_removals; md=std::max(md,r.max_depth);
        for(size_t i=0;i<nodes.size();i++) nodes[i]+=r.node_count[i];
    }
    std::ostringstream out;
    out << "{\n  \"schema\": \"s0908_sound_domain_dfs_v1\",\n  \"semantics\": \"upper-bound rows only; saturation removes future points; no unused-capacity filling test; transactional counter undo\",\n"
        << "  \"constraints_path\": \"" << cons << "\",\n  \"constraint_count\": " << rows.size() << ",\n  \"target\": " << target << ",\n  \"max_point\": " << max_point << ",\n"
        << "  \"time_limit_per_run_sec\": " << lim << ",\n  \"all_complete\": " << (all_complete?"true":"false") << ",\n  \"total_solutions\": " << sol << ",\n"
        << "  \"global_max_depth\": " << md << ",\n  \"total_recursive_calls\": " << calls << ",\n  \"total_candidate_tests\": " << tests << ",\n"
        << "  \"total_overcap_rejects\": " << over << ",\n  \"total_global_shortage\": " << shortage << ",\n  \"total_saturated_rows\": " << satrows << ",\n"
        << "  \"total_saturation_point_removals\": " << satrem << ",\n  \"total_initial_zero_cap_removals\": " << zero << ",\n  \"total_node_count_by_depth\": " << json_array_u64(nodes, std::min(31,target)) << ",\n  \"results\": [\n";
    for(size_t i=0;i<results.size();i++){ out << "    " << result_json(results[i]); if(i+1<results.size()) out << ","; out << "\n"; }
    out << "  ]\n}\n";
    if(!outp.empty()){ std::ofstream f(outp); f << out.str(); std::cerr << "wrote " << outp << "\n"; }
    return 0;
}
