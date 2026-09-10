// Fast stochastic violation minimizer for Wang constraints (E11WANG1 format).
// Hill-climbing with incremental violation updates.
// Usage: wang_hillclimb --constraints FILE --target N [--restarts R] [--timeout T]

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <numeric>
#include <random>
#include <string>
#include <vector>

static const int NPTS = 255;
static int NROWS = 0;

struct Row { uint8_t cap; uint16_t npts; std::vector<uint16_t> pts; };
static std::vector<Row> rows;
static std::vector<std::vector<int>> pt_rows; // pt_rows[p] = list of row indices

static std::vector<uint16_t> occ;      // occupancy per row
static std::vector<uint8_t> in_support; // 1 if point in support

static int violation_count = 0;
static int target_depth = 19;

static auto t_start = std::chrono::steady_clock::now();
static double elapsed_sec() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t_start).count();
}

static bool load_constraints(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "Cannot open %s\n", path); return false; }
    char magic[8];
    if (fread(magic, 1, 8, f) != 8) { fclose(f); return false; }
    if (memcmp(magic, "E11WANG1", 8) != 0) {
        fprintf(stderr, "Bad magic (need E11WANG1)\n"); fclose(f); return false;
    }
    uint32_t nrows;
    if (fread(&nrows, 4, 1, f) != 1) { fclose(f); return false; }
    NROWS = (int)nrows;
    rows.resize(NROWS);
    pt_rows.assign(NPTS + 1, std::vector<int>());
    
    for (int i = 0; i < NROWS; i++) {
        uint8_t cap, dim; uint16_t res;
        fread(&cap, 1, 1, f); fread(&dim, 1, 1, f); fread(&res, 2, 1, f);
        uint64_t words[4];
        fread(words, 8, 4, f);
        rows[i].cap = cap;
        for (int w = 0; w < 4; w++) {
            uint64_t m = words[w];
            while (m) {
                int b = __builtin_ctzll(m);
                int p = w * 64 + b;
                if (p >= 1 && p <= NPTS) rows[i].pts.push_back((uint16_t)p);
                m &= m - 1;
            }
        }
        rows[i].npts = (uint16_t)rows[i].pts.size();
        for (uint16_t p : rows[i].pts) pt_rows[p].push_back(i);
    }
    fclose(f);
    fprintf(stderr, "Loaded %d rows, %d points\n", NROWS, NPTS);
    return true;
}

static void init_support(const std::vector<int>& pts) {
    memset(in_support.data(), 0, NPTS + 1);
    occ.assign(NROWS, 0);
    violation_count = 0;
    for (int p : pts) {
        in_support[p] = 1;
        for (int ri : pt_rows[p]) {
            occ[ri]++;
        }
    }
    for (int ri = 0; ri < NROWS; ri++) {
        if (occ[ri] > rows[ri].cap) violation_count++;
    }
}

// Compute delta_violations for swap (p_out -> p_in) WITHOUT modifying state
static int swap_delta(int p_out, int p_in) {
    int delta = 0;
    // Rows containing p_out: occ decreases
    for (int ri : pt_rows[p_out]) {
        if (in_support[p_in] == 0 || 
            !std::binary_search(rows[ri].pts.begin(), rows[ri].pts.end(), (uint16_t)p_in)) {
            // p_in NOT in this row, so occ decreases by 1
            uint16_t cur = occ[ri];
            if (cur > rows[ri].cap && cur - 1 <= rows[ri].cap) delta--; // fixed
            else if (cur <= rows[ri].cap && cur - 1 > rows[ri].cap) delta++; // shouldn't happen
        }
        // If p_in IS in this row, occ doesn't change (remove p_out, add p_in)
    }
    // Rows containing p_in: occ increases
    for (int ri : pt_rows[p_in]) {
        if (!std::binary_search(rows[ri].pts.begin(), rows[ri].pts.end(), (uint16_t)p_out)) {
            // p_out NOT in this row, so occ increases by 1
            uint16_t cur = occ[ri];
            if (cur >= rows[ri].cap && cur + 1 > rows[ri].cap) delta++; // new violation
            // Note: cur+1 > cap means cur >= cap, so if cur == cap, adding makes it violated
            if (cur + 1 > rows[ri].cap && cur <= rows[ri].cap) {} // already counted above
            // Simplify: if cur == cap, delta++ (goes from non-violated to violated)
            // if cur > cap, no change (already violated)
            // if cur < cap, no change (still not violated)
        }
    }
    return delta;
}

// Apply swap
static void apply_swap(int p_out, int p_in) {
    in_support[p_out] = 0;
    for (int ri : pt_rows[p_out]) occ[ri]--;
    in_support[p_in] = 1;
    for (int ri : pt_rows[p_in]) occ[ri]++;
    // Recount violations
    violation_count = 0;
    for (int ri = 0; ri < NROWS; ri++)
        if (occ[ri] > rows[ri].cap) violation_count++;
}

int main(int argc, char** argv) {
    const char* cons_path = nullptr;
    const char* out_path = nullptr;
    int restarts = 100;
    double time_limit = 600.0;
    int seed = 42;
    
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--constraints") && i+1 < argc) cons_path = argv[++i];
        else if (!strcmp(argv[i], "--output") && i+1 < argc) out_path = argv[++i];
        else if (!strcmp(argv[i], "--target") && i+1 < argc) target_depth = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--restarts") && i+1 < argc) restarts = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--timeout") && i+1 < argc) time_limit = atof(argv[++i]);
        else if (!strcmp(argv[i], "--seed") && i+1 < argc) seed = atoi(argv[++i]);
    }
    if (!cons_path) { fprintf(stderr, "Need --constraints FILE\n"); return 1; }
    if (!load_constraints(cons_path)) return 1;
    
    // Sort each row's point list for binary_search
    for (auto& r : rows) std::sort(r.pts.begin(), r.pts.end());
    
    in_support.resize(NPTS + 1);
    
    std::mt19937 rng(seed);
    std::vector<int> all_pts(NPTS);
    std::iota(all_pts.begin(), all_pts.end(), 1);
    
    int global_best_viol = NROWS + 1;
    std::vector<int> global_best_support;
    std::vector<int> viol_history;
    int total_hill_steps = 0;
    
    t_start = std::chrono::steady_clock::now();
    
    for (int restart = 0; restart < restarts; restart++) {
        if (elapsed_sec() > time_limit) break;
        
        // Random initial support
        std::shuffle(all_pts.begin(), all_pts.end(), rng);
        std::vector<int> support(all_pts.begin(), all_pts.begin() + target_depth);
        std::sort(support.begin(), support.end());
        init_support(support);
        
        int init_viol = violation_count;
        
        // Hill-climb
        bool improved = true;
        int steps = 0;
        while (improved && violation_count > 0 && elapsed_sec() < time_limit) {
            improved = false;
            steps++;
            
            // Try all swaps, find best
            int best_delta = 0;
            int best_out = -1, best_in = -1;
            
            for (int si = 0; si < target_depth; si++) {
                int p_out = support[si];
                for (int p_in = 1; p_in <= NPTS; p_in++) {
                    if (in_support[p_in]) continue;
                    
                    // Quick delta computation
                    int delta = 0;
                    for (int ri : pt_rows[p_out]) {
                        bool p_in_here = std::binary_search(
                            rows[ri].pts.begin(), rows[ri].pts.end(), (uint16_t)p_in);
                        if (!p_in_here) {
                            uint16_t c = occ[ri];
                            if (c == rows[ri].cap + 1) delta--; // fix violation
                        }
                    }
                    for (int ri : pt_rows[p_in]) {
                        bool p_out_here = std::binary_search(
                            rows[ri].pts.begin(), rows[ri].pts.end(), (uint16_t)p_out);
                        if (!p_out_here) {
                            uint16_t c = occ[ri];
                            if (c == rows[ri].cap) delta++; // create violation
                        }
                    }
                    
                    if (delta < best_delta) {
                        best_delta = delta;
                        best_out = p_out;
                        best_in = p_in;
                    }
                }
            }
            
            if (best_delta < 0) {
                apply_swap(best_out, best_in);
                // Update support list
                for (auto& s : support) if (s == best_out) { s = best_in; break; }
                std::sort(support.begin(), support.end());
                improved = true;
            }
        }
        total_hill_steps += steps;
        
        viol_history.push_back(violation_count);
        if (violation_count < global_best_viol) {
            global_best_viol = violation_count;
            global_best_support = support;
        }
        
        fprintf(stderr, "restart %d: %d -> %d viols (%d steps), best=%d, %.1fs\n",
                restart, init_viol, violation_count, steps, global_best_viol, elapsed_sec());
        
        if (global_best_viol == 0) {
            fprintf(stderr, "FOUND ZERO-VIOLATION SUPPORT!\n");
            break;
        }
    }
    
    // Output JSON
    FILE* out = stdout;
    if (out_path) { out = fopen(out_path, "w"); if (!out) out = stdout; }
    
    fprintf(out, "{\n");
    fprintf(out, "  \"target\": %d,\n", target_depth);
    fprintf(out, "  \"nrows\": %d,\n", NROWS);
    fprintf(out, "  \"restarts_completed\": %d,\n", (int)viol_history.size());
    fprintf(out, "  \"total_hill_steps\": %d,\n", total_hill_steps);
    fprintf(out, "  \"best_violations\": %d,\n", global_best_viol);
    fprintf(out, "  \"elapsed_sec\": %.3f,\n", elapsed_sec());
    
    // Violation statistics
    int mn = *std::min_element(viol_history.begin(), viol_history.end());
    int mx = *std::max_element(viol_history.begin(), viol_history.end());
    double avg = std::accumulate(viol_history.begin(), viol_history.end(), 0.0) / viol_history.size();
    fprintf(out, "  \"min_violations\": %d,\n", mn);
    fprintf(out, "  \"max_violations\": %d,\n", mx);
    fprintf(out, "  \"mean_violations\": %.1f,\n", avg);
    
    // Best support
    fprintf(out, "  \"best_support\": [");
    for (int i = 0; i < (int)global_best_support.size(); i++) {
        if (i) fprintf(out, ",");
        fprintf(out, "%d", global_best_support[i]);
    }
    fprintf(out, "],\n");
    
    // Violation history
    fprintf(out, "  \"violation_history\": [");
    for (int i = 0; i < (int)viol_history.size(); i++) {
        if (i) fprintf(out, ",");
        fprintf(out, "%d", viol_history[i]);
    }
    fprintf(out, "]\n}\n");
    
    if (out != stdout) fclose(out);
    return 0;
}
