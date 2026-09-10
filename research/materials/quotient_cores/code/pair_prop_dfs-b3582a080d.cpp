// analysis: DFS with signed pair-inequality propagation for E11 support search.
//
// The signed pair inequality: for two Wang rows R,S with caps c_R,c_S,
//   sum_{p in O} x_p - sum_{p in I} x_p >= 19 - c_R - c_S
// where I=R∩S, O={1,...,255}\(R∪S).
//
// Maintained incrementally.  margin = cnt_O + avail_O - cnt_I - threshold.
// margin < 0:  infeasible.
// margin == 0: all future O-points MUST be selected; all future I-points
//              MUST be excluded from domain.  Exclusion cascades through
//              Wang saturation and other pair updates.

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

static constexpr int MAXP = 255;
static constexpr int WORDS = 4;
static bool bit4(const uint64_t w[WORDS], int p){ return (w[p>>6]>>(p&63))&1ULL; }
static void setbit4(uint64_t w[WORDS], int p){ w[p>>6] |= 1ULL<<(p&63); }
static void clrbit4(uint64_t w[WORDS], int p){ w[p>>6] &= ~(1ULL<<(p&63)); }
static int pop4(const uint64_t w[WORDS]){ return __builtin_popcountll(w[0])+__builtin_popcountll(w[1])+__builtin_popcountll(w[2])+__builtin_popcountll(w[3]); }

struct Row { uint8_t cap=0, dim=0; uint16_t reserved=0; uint64_t word[WORDS]={0,0,0,0}; };
struct Cut { uint8_t K=0; uint64_t w1[WORDS]={0,0,0,0}; uint64_t w2[WORDS]={0,0,0,0}; uint8_t coeff[256]{}; };
struct Branch { int id=-1, rep=0; uint64_t forbid[WORDS]={0,0,0,0}; };

struct PairIneq {
    uint64_t I[WORDS]; // intersection R∩S
    uint64_t O[WORDS]; // outside {1..255}\(R∪S)
    int threshold;      // 19 - c_R - c_S
    int I_size, O_size;
};

struct Result {
    int branch=-1, rep=0, target=0, max_depth=0; double elapsed_sec=0.0;
    bool timeout=false, complete=false, forced_infeasible=false;
    uint64_t calls=0, candidate_tests=0, overcap_rejects=0, global_shortage=0;
    uint64_t mixed_prunes=0, mixed_checks=0, saturated_rows=0, saturation_removed_points=0, initial_cap0_removed=0, solutions=0;
    uint64_t pair_checks=0, pair_prunes=0, pair_propagations=0, pair_exclusions=0, pair_forces=0;
    uint64_t pair_cascade_rounds=0;
    std::array<uint64_t,32> nodes{}, mixed_depth{}, pair_depth{};
    std::vector<std::vector<int>> sol_head;
};

static std::string arr_json(const std::array<uint64_t,32>& a, int upto){ std::ostringstream o; o<<"["; for(int i=0;i<=upto && i<(int)a.size();i++){ if(i)o<<","; o<<a[i]; } o<<"]"; return o.str(); }
static std::string vec_json(const std::vector<int>& v){ std::ostringstream o; o<<"["; for(size_t i=0;i<v.size();i++){ if(i)o<<","; o<<v[i]; } o<<"]"; return o.str(); }
static std::string sols_json(const std::vector<std::vector<int>>& vv){ std::ostringstream o; o<<"["; for(size_t i=0;i<vv.size();i++){ if(i)o<<","; o<<vec_json(vv[i]); } o<<"]"; return o.str(); }

static bool load_rows(const std::string& path, std::vector<Row>& rows){
    if(path.empty()) return true;
    std::ifstream in(path, std::ios::binary); if(!in) return false;
    char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"E11WANG1",8)!=0) return false;
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); rows.resize(n);
    for(uint32_t i=0;i<n;i++){
        in.read(reinterpret_cast<char*>(&rows[i].cap),1); in.read(reinterpret_cast<char*>(&rows[i].dim),1);
        in.read(reinterpret_cast<char*>(&rows[i].reserved),2);
        for(int w=0;w<WORDS;w++) in.read(reinterpret_cast<char*>(&rows[i].word[w]),8);
    }
    return (bool)in;
}
static bool load_cuts(const std::string& path, std::vector<Cut>& cuts){
    if(path.empty()) return true;
    std::ifstream in(path, std::ios::binary); if(!in) return false;
    char magic[8]; in.read(magic,8); if(!in || std::memcmp(magic,"MIXCUT1\0",8)!=0) return false;
    uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); cuts.resize(n);
    for(uint32_t i=0;i<n;i++){
        uint8_t flags; uint16_t reserved; in.read(reinterpret_cast<char*>(&cuts[i].K),1);
        in.read(reinterpret_cast<char*>(&flags),1); in.read(reinterpret_cast<char*>(&reserved),2);
        for(int w=0;w<WORDS;w++) in.read(reinterpret_cast<char*>(&cuts[i].w1[w]),8);
        for(int w=0;w<WORDS;w++) in.read(reinterpret_cast<char*>(&cuts[i].w2[w]),8);
        for(int p=1;p<=MAXP;p++) cuts[i].coeff[p] = bit4(cuts[i].w2,p)?2:(bit4(cuts[i].w1,p)?1:0);
    }
    return (bool)in;
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
static std::vector<int> parse_list(const std::string& s){
    std::vector<int> v; if(s.empty()) return v;
    size_t pos=0; while(pos<s.size()){ size_t nx=s.find(',',pos); if(nx==std::string::npos) nx=s.size();
    if(nx>pos){ int p=std::stoi(s.substr(pos,nx-pos)); if(1<=p&&p<=MAXP) v.push_back(p); } pos=nx+1; }
    std::sort(v.begin(),v.end()); v.erase(std::unique(v.begin(),v.end()),v.end()); return v;
}

struct Searcher{
    // Constraint rows (cap<=5 for saturation)
    const std::vector<Row>& rows;
    const std::vector<std::vector<uint32_t>>& pr;
    // Mixed-source lower cuts
    const std::vector<Cut>& cuts;
    // Pair inequalities
    std::vector<PairIneq> pairs;
    std::vector<std::vector<uint32_t>> pt_in_I; // pt_in_I[p] = pairs where p in I
    std::vector<std::vector<uint32_t>> pt_in_O; // pt_in_O[p] = pairs where p in O
    // State
    int target; double limit;
    std::chrono::steady_clock::time_point start;
    std::vector<uint8_t> cnt;
    std::vector<int16_t> lhs;
    std::vector<int16_t> pair_margin; // margin = cnt_O + avail_O - cnt_I - threshold
    uint64_t dom[WORDS];
    uint64_t mandatory[WORDS]; // points that MUST be selected (from tight pairs)
    std::vector<int> chosen;
    Result res;

    Searcher(const std::vector<Row>& r, const std::vector<std::vector<uint32_t>>& p,
             const std::vector<Cut>& c, const std::vector<Row>& pair_rows,
             int t, double lim)
        : rows(r), pr(p), cuts(c), target(t), limit(lim),
          cnt(r.size(),0), lhs(c.size(),0)
    {
        // Build pair inequalities from pair_rows
        int nr = (int)pair_rows.size();
        for(int i=0;i<nr;i++) for(int j=i+1;j<nr;j++){
            PairIneq pi;
            uint64_t U[WORDS];
            for(int w=0;w<WORDS;w++){
                pi.I[w] = pair_rows[i].word[w] & pair_rows[j].word[w];
                U[w] = pair_rows[i].word[w] | pair_rows[j].word[w];
                // O = all_points \ U.  all_points for [1..255]: bits 1..255 set
                pi.O[w] = ~U[w];
            }
            // Clear bit 0 (point 0 is not a valid point)
            pi.O[0] &= ~1ULL;
            // Also clear bits >= 256 in word 3
            // word 3 covers bits 192..255, all valid
            pi.threshold = target - (int)pair_rows[i].cap - (int)pair_rows[j].cap;
            pi.I_size = pop4(pi.I);
            pi.O_size = pop4(pi.O);
            if(pi.threshold > 0) // only add useful pairs
                pairs.push_back(pi);
        }
        pair_margin.resize(pairs.size(), 0);
        // Build point-to-pair indices
        pt_in_I.resize(256);
        pt_in_O.resize(256);
        for(uint32_t pi=0;pi<pairs.size();pi++){
            for(int p=1;p<=MAXP;p++){
                if(bit4(pairs[pi].I,p)) pt_in_I[p].push_back(pi);
                if(bit4(pairs[pi].O,p)) pt_in_O[p].push_back(pi);
            }
        }
        std::cerr << "Built " << pairs.size() << " pair inequalities from "
                  << nr << " rows\n";
    }

    bool timed() const { return limit>0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=limit; }
    void full_domain(){ dom[0]=dom[1]=dom[2]=dom[3]=~0ULL; dom[0]&=~1ULL; }
    bool in_dom(int p) const { return bit4(dom,p); }
    void remove_dom(int p){ clrbit4(dom,p); }
    int avail_from(int minp) const { int c=0; for(int p=minp;p<=MAXP;p++) if(in_dom(p)) c++; return c; }

    // Initialize pair margins from current domain
    void init_pair_margins(){
        for(size_t pi=0;pi<pairs.size();pi++){
            int ao=0;
            for(int p=1;p<=MAXP;p++) if(in_dom(p) && bit4(pairs[pi].O,p)) ao++;
            pair_margin[pi] = (int16_t)(ao - pairs[pi].threshold);
            // Initially cnt_O=0, cnt_I=0
        }
    }

    // After selecting point q: update pair margins
    // Selecting q in I: margin decreases by 1 (cnt_I++)
    // Selecting q in O: margin unchanged (cnt_O++ and avail_O--, net 0)
    // BUT: q is removed from domain, so if q is in O, avail_O decreased by 1
    //   and cnt_O increased by 1.  Net 0.  Correct.
    // Actually, q was already removed from domain (in remove_dom before calling this)
    // So avail_O already decreased.  cnt_O increases.  Net: margin stays same for O.
    // For I: cnt_I increases.  margin decreases by 1.
    void update_margins_select(int q){
        for(uint32_t pi : pt_in_I[q]) pair_margin[pi]--;
        // O: cnt_O++ offsets avail_O-- from domain removal.  No net change.
    }

    // After removing a point from domain (by saturation, not by selection):
    // If the point is in O of a pair: avail_O decreases, margin decreases.
    void update_margins_domain_remove(int q){
        for(uint32_t pi : pt_in_O[q]) pair_margin[pi]--;
    }

    // Run exclusion propagation for tight pairs.
    // Returns false if any pair becomes infeasible.
    // Modifies domain and pair_margins.
    // Records removed points in 'removed' for undo.
    bool propagate_pairs(int minp, std::vector<int>& removed, std::vector<int>& forced){
        bool changed = true;
        while(changed){
            changed = false;
            res.pair_cascade_rounds++;
            for(size_t pi=0;pi<pairs.size();pi++){
                if(pair_margin[pi] < 0){
                    res.pair_prunes++;
                    int d=(int)chosen.size();
                    if(d<(int)res.pair_depth.size()) res.pair_depth[d]++;
                    return false;
                }
                if(pair_margin[pi] == 0){
                    res.pair_propagations++;
                    // Exclude all future I-points from domain
                    for(int p=1;p<=MAXP;p++){
                        if(in_dom(p) && bit4(pairs[pi].I,p)){
                            remove_dom(p);
                            removed.push_back(p);
                            res.pair_exclusions++;
                            // This removal may affect OTHER pair margins
                            update_margins_domain_remove(p);
                            // Also may saturate Wang rows
                            for(uint32_t ri : pr[p]){
                                // Check if this row is now saturated
                                // cnt[ri] is the count of selected points in row ri
                                // We removed p from domain, not selected it
                                // A row becomes saturated when cnt == cap (all selected fill it)
                                // Domain removal of an unselected point doesn't change cnt
                                // But it may reduce the available points below what's needed
                                // This is handled by the main DFS global_shortage check
                            }
                            changed = true;
                        }
                    }
                    // Mark future O-points as mandatory
                    for(int p=minp;p<=MAXP;p++){
                        if(in_dom(p) && bit4(pairs[pi].O,p)){
                            if(!bit4(mandatory,p)){
                                setbit4(mandatory,p);
                                forced.push_back(p);
                                res.pair_forces++;
                            }
                        }
                    }
                }
            }
        }
        return true;
    }

    bool mixed_possible(int minp,int need){
        if(cuts.empty()) return true; res.mixed_checks += cuts.size();
        uint64_t fut[WORDS]; for(int w=0;w<WORDS;w++) fut[w]=dom[w];
        if(minp>1) for(int p=1;p<minp && p<=MAXP;p++) clrbit4(fut,p);
        for(size_t i=0;i<cuts.size();i++){
            uint64_t a1[WORDS],a2[WORDS]; for(int w=0;w<WORDS;w++){ a1[w]=fut[w]&cuts[i].w1[w]; a2[w]=fut[w]&cuts[i].w2[w]; }
            int c2=pop4(a2), c1=pop4(a1); int take2=std::min(c2,need); int take1=std::min(c1,need-take2);
            int ub=lhs[i]+2*take2+take1;
            if(ub < cuts[i].K){ res.mixed_prunes++; int d=(int)chosen.size(); if(d<(int)res.mixed_depth.size()) res.mixed_depth[d]++; return false; }
        }
        return true;
    }

    bool terminal_pairs_ok(){
        // At d=target no unselected future point can contribute.  The maintained
        // margin cnt_O + avail_O - cnt_I - threshold is only a search upper bound;
        // terminal support validity must be evaluated on the selected points alone.
        for(size_t pi=0; pi<pairs.size(); pi++){
            int lhs_sel = 0;
            for(int q : chosen){
                if(bit4(pairs[pi].O,q)) lhs_sel++;
                if(bit4(pairs[pi].I,q)) lhs_sel--;
            }
            if(lhs_sel < pairs[pi].threshold){
                res.pair_prunes++;
                int d=(int)chosen.size(); if(d<(int)res.pair_depth.size()) res.pair_depth[d]++;
                return false;
            }
        }
        return true;
    }

    bool try_select(int q, std::vector<uint32_t>& touched, uint64_t olddom[WORDS]){
        res.candidate_tests++;
        for(int w=0;w<WORDS;w++) olddom[w]=dom[w];
        if(!in_dom(q)) return false;
        for(uint32_t ri:pr[q]) if((int)cnt[ri]+1>(int)rows[ri].cap){ res.overcap_rejects++; return false; }
        remove_dom(q);
        for(uint32_t ri:pr[q]){ cnt[ri]++; touched.push_back(ri); }
        for(size_t i=0;i<cuts.size();i++) lhs[i]+=cuts[i].coeff[q];
        // Wang saturation
        for(uint32_t ri:touched){
            if(cnt[ri]==rows[ri].cap){
                res.saturated_rows++;
                for(int p=1;p<=MAXP;p++){
                    if(in_dom(p) && bit4(rows[ri].word,p)){
                        remove_dom(p);
                        res.saturation_removed_points++;
                        // Update pair margins for domain removal
                        update_margins_domain_remove(p);
                    }
                }
            }
        }
        // Update pair margins for the selection itself
        update_margins_select(q);
        return true;
    }

    void undo_select(int q, const std::vector<uint32_t>& touched, const uint64_t olddom[WORDS],
                     const std::vector<int16_t>& saved_margins, const std::vector<int>& removed,
                     const std::vector<int>& forced_mand){
        for(size_t i=0;i<cuts.size();i++) lhs[i]-=cuts[i].coeff[q];
        for(auto it=touched.rbegin();it!=touched.rend();++it) cnt[*it]--;
        for(int w=0;w<WORDS;w++) dom[w]=olddom[w];
        // Restore pair margins
        for(size_t i=0;i<pairs.size();i++) pair_margin[i]=saved_margins[i];
        // Restore mandatory bits
        for(int p : forced_mand) clrbit4(mandatory,p);
    }

    bool force_points(const std::vector<int>& force){
        for(int p:force){
            if(!in_dom(p)){ res.forced_infeasible=true; return false; }
            std::vector<uint32_t> touched; uint64_t old[WORDS];
            bool ok=try_select(p,touched,old);
            if(!ok){ res.forced_infeasible=true; return false; }
            chosen.push_back(p);
        }
        return true;
    }

    void dfs(int minp){
        if(res.timeout) return; if((res.calls++ & 0x3FFFULL)==0 && timed()){ res.timeout=true; return; }
        int d=(int)chosen.size(); if(d>res.max_depth) res.max_depth=d;
        if(d==target){
            if(!mixed_possible(MAXP+1,0)) return;
            if(!terminal_pairs_ok()) return;
            res.solutions++; if(res.sol_head.size()<5){ auto s=chosen; std::sort(s.begin(),s.end()); res.sol_head.push_back(s); }
            return;
        }
        int need=target-d;
        int avail=avail_from(minp);
        if(avail<need){ res.global_shortage++; return; }

        // Check pairs and propagate
        res.pair_checks++;
        std::vector<int16_t> saved_margins(pair_margin);
        std::vector<int> removed, forced_mand;
        if(!propagate_pairs(minp, removed, forced_mand)){
            // Restore before returning to the caller.  A failed propagation may
            // have removed domain points, changed margins, and marked mandatory
            // points before discovering a later infeasible pair.
            for(size_t i=0;i<pairs.size();i++) pair_margin[i]=saved_margins[i];
            for(int p:removed) setbit4(dom,p);
            for(int p:forced_mand) clrbit4(mandatory,p);
            return;
        }

        // After propagation, recheck availability
        avail=avail_from(minp);
        if(avail<need){ res.global_shortage++; 
            // Restore pair state
            for(size_t i=0;i<pairs.size();i++) pair_margin[i]=saved_margins[i];
            for(int p:removed) setbit4(dom,p);
            for(int p:forced_mand) clrbit4(mandatory,p);
            return; 
        }

        if(!mixed_possible(minp,need)){
            for(size_t i=0;i<pairs.size();i++) pair_margin[i]=saved_margins[i];
            for(int p:removed) setbit4(dom,p);
            for(int p:forced_mand) clrbit4(mandatory,p);
            return;
        }

        // Save domain after propagation for child undo
        uint64_t prop_dom[WORDS]; for(int w=0;w<WORDS;w++) prop_dom[w]=dom[w];

        for(int q=minp;q<=MAXP;q++){
            if(MAXP-q+1<need) break; if(!in_dom(q)) continue;
            if(avail_from(q)<need) break;

            bool is_mandatory = bit4(mandatory,q);

            std::vector<uint32_t> touched; uint64_t old[WORDS];
            std::vector<int16_t> child_margins(pair_margin);
            bool ok=try_select(q,touched,old);

            if(ok){
                // Check pairs after selection
                std::vector<int> child_removed, child_forced;
                bool pair_ok = true;
                for(size_t pi=0;pi<pairs.size();pi++){
                    if(pair_margin[pi]<0){ pair_ok=false; res.pair_prunes++; int dd=(int)chosen.size()+1; if(dd<(int)res.pair_depth.size()) res.pair_depth[dd]++; break; }
                }
                if(pair_ok){
                    // Propagate after this child selection
                    pair_ok = propagate_pairs(q+1, child_removed, child_forced);
                }
                if(pair_ok){
                    chosen.push_back(q);
                    int nd=(int)chosen.size(); if(nd<(int)res.nodes.size()) res.nodes[nd]++;
                    dfs(q+1);
                    chosen.pop_back();
                }
                // Undo child selection
                for(size_t i=0;i<cuts.size();i++) lhs[i]-=cuts[i].coeff[q];
                for(auto it=touched.rbegin();it!=touched.rend();++it) cnt[*it]--;
                for(int w=0;w<WORDS;w++) dom[w]=prop_dom[w]; // restore to post-propagation domain
                for(size_t i=0;i<pairs.size();i++) pair_margin[i]=child_margins[i];
                for(int p:child_forced) clrbit4(mandatory,p);
            }

            if(res.timeout) break;

            // If q was mandatory, we MUST select it.  Not selecting = infeasible.
            if(is_mandatory) break;
        }

        // Restore pre-propagation state for the caller.
        for(int w=0;w<WORDS;w++) dom[w]=prop_dom[w];
        for(int p:removed) setbit4(dom,p);
        for(size_t i=0;i<pairs.size();i++) pair_margin[i]=saved_margins[i];
        for(int p:forced_mand) clrbit4(mandatory,p);
    }

    Result run(const uint64_t forbidden[WORDS], const std::vector<int>& force, int min_after, int branch, int rep){
        res=Result(); res.branch=branch; res.rep=rep; res.target=target;
        res.nodes.fill(0); res.mixed_depth.fill(0); res.pair_depth.fill(0); res.nodes[0]=1;
        std::fill(cnt.begin(),cnt.end(),0); std::fill(lhs.begin(),lhs.end(),0);
        chosen.clear(); full_domain();
        std::memset(mandatory,0,sizeof(mandatory));
        for(int w=0;w<WORDS;w++) dom[w]&=~forbidden[w];
        for(const auto& row:rows) if(row.cap==0){
            int before=pop4(dom);
            for(int w=0;w<WORDS;w++) dom[w]&=~row.word[w];
            res.initial_cap0_removed += std::max(0,before-pop4(dom));
        }
        init_pair_margins();
        start=std::chrono::steady_clock::now();
        bool ok=force_points(force);
        if(ok){
            // Re-initialize margins after forcing (domain may have changed)
            // Actually, try_select already updated margins.  But force_points
            // doesn't propagate pairs.  Let's just re-init for safety.
            // No: the incremental updates in try_select are correct.
            int d=(int)chosen.size(); if(d<(int)res.nodes.size()) res.nodes[d]=std::max<uint64_t>(res.nodes[d],1);
            dfs(min_after);
        }
        res.elapsed_sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        res.complete=!res.timeout;
        return res;
    }
};

static std::string rjson(const Result& r){
    std::ostringstream o;
    o<<"{\"branch\":"<<r.branch<<",\"rep\":"<<r.rep<<",\"target\":"<<r.target
     <<",\"elapsed_sec\":"<<std::fixed<<std::setprecision(6)<<r.elapsed_sec
     <<",\"timeout\":"<<(r.timeout?"true":"false")
     <<",\"complete\":"<<(r.complete?"true":"false")
     <<",\"forced_infeasible\":"<<(r.forced_infeasible?"true":"false")
     <<",\"recursive_calls\":"<<r.calls
     <<",\"candidate_tests\":"<<r.candidate_tests
     <<",\"overcap_rejects\":"<<r.overcap_rejects
     <<",\"global_shortage\":"<<r.global_shortage
     <<",\"mixed_prunes\":"<<r.mixed_prunes
     <<",\"mixed_checks\":"<<r.mixed_checks
     <<",\"pair_checks\":"<<r.pair_checks
     <<",\"pair_prunes\":"<<r.pair_prunes
     <<",\"pair_propagations\":"<<r.pair_propagations
     <<",\"pair_exclusions\":"<<r.pair_exclusions
     <<",\"pair_forces\":"<<r.pair_forces
     <<",\"pair_cascade_rounds\":"<<r.pair_cascade_rounds
     <<",\"saturated_rows\":"<<r.saturated_rows
     <<",\"saturation_removed_points\":"<<r.saturation_removed_points
     <<",\"initial_cap0_removed\":"<<r.initial_cap0_removed
     <<",\"solutions\":"<<r.solutions
     <<",\"max_depth\":"<<r.max_depth
     <<",\"node_count_by_depth\":"<<arr_json(r.nodes,std::min(31,r.target))
     <<",\"mixed_prune_depth\":"<<arr_json(r.mixed_depth,std::min(31,r.target))
     <<",\"pair_prune_depth\":"<<arr_json(r.pair_depth,std::min(31,r.target))
     <<",\"solutions_head\":"<<sols_json(r.sol_head)<<"}";
    return o.str();
}

int main(int argc,char**argv){
    std::string cons,pair_rows_path,cuts_s,outp,force_s,exclude_s;
    int target=19,branch=-2; double lim=60.0;
    for(int i=1;i<argc;i++){ std::string a=argv[i];
        if(a=="--constraints"&&i+1<argc) cons=argv[++i];
        else if(a=="--pair-rows"&&i+1<argc) pair_rows_path=argv[++i];
        else if(a=="--cuts"&&i+1<argc) cuts_s=argv[++i];
        else if(a=="--output"&&i+1<argc) outp=argv[++i];
        else if(a=="--target"&&i+1<argc) target=std::stoi(argv[++i]);
        else if(a=="--timeout"&&i+1<argc) lim=std::stod(argv[++i]);
        else if(a=="--branch"&&i+1<argc) branch=std::stoi(argv[++i]);
        else if(a=="--all-branches") branch=-1;
        else if(a=="--force"&&i+1<argc) force_s=argv[++i];
        else if(a=="--exclude"&&i+1<argc) exclude_s=argv[++i];
        else { std::cerr<<"bad arg "<<a<<"\n"; return 2; }
    }
    if(cons.empty()||pair_rows_path.empty()){ std::cerr<<"usage: --constraints FILE --pair-rows FILE [--cuts FILE] [--branch B|--all-branches] [--force a,b] [--exclude a,b] [--timeout S] [--output FILE]\n"; return 2; }
    std::vector<Row> rows, pair_rows; std::vector<Cut> cutv;
    if(!load_rows(cons,rows)){ std::cerr<<"cannot load constraints\n"; return 1; }
    if(!load_rows(pair_rows_path,pair_rows)){ std::cerr<<"cannot load pair rows\n"; return 1; }
    if(!load_cuts(cuts_s,cutv)){ std::cerr<<"cannot load cuts\n"; return 1; }
    auto pr=point_rows(rows);
    std::vector<int> force=parse_list(force_s), exclude=parse_list(exclude_s);
    uint64_t forbidden[WORDS]={0,0,0,0}; for(int p:exclude) setbit4(forbidden,p);
    std::vector<Result> results;
    if(branch>=-1){
        for(auto& br:branches()){
            if(branch>=0 && br.id!=branch) continue;
            uint64_t forb[WORDS]; for(int w=0;w<WORDS;w++) forb[w]=forbidden[w]|br.forbid[w];
            auto f=force; f.push_back(br.rep); std::sort(f.begin(),f.end()); f.erase(std::unique(f.begin(),f.end()),f.end());
            Searcher S(rows,pr,cutv,pair_rows,target,lim);
            Result r=S.run(forb,f,br.rep+1,br.id,br.rep);
            results.push_back(r); std::cout<<rjson(r)<<"\n"; std::cout.flush();
        }
    } else {
        Searcher S(rows,pr,cutv,pair_rows,target,lim);
        Result r=S.run(forbidden,force,1,-1,0);
        results.push_back(r); std::cout<<rjson(r)<<"\n";
    }
    // Summary
    std::ostringstream out;
    out<<"{\n  \"schema\": \"s0908_pair_prop_dfs_v2_terminal_pair_checked\",\n  \"constraint_count\": "<<rows.size()<<",\n  \"pair_row_count\": "<<pair_rows.size()<<",\n  \"mixed_cut_count\": "<<cutv.size()<<",\n  \"target\": "<<target<<",\n  \"results\": [\n";
    for(size_t i=0;i<results.size();i++){ out<<"    "<<rjson(results[i]); if(i+1<results.size()) out<<","; out<<"\n"; }
    out<<"  ]\n}\n";
    if(!outp.empty()){ std::ofstream f(outp); f<<out.str(); std::cerr<<"wrote "<<outp<<"\n"; }
    return 0;
}
