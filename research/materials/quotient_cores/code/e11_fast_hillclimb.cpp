/* E11 fast hill-climb for n=19 support search.
 * Uses precomputed per-point incidence for O(1) delta-violation.
 * 
 * Build: g++ -O2 -o e11_fast_hillclimb e11_fast_hillclimb.cpp
 * Usage: ./e11_fast_hillclimb <binary> <target> <trials> <steps> <seed>
 */
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
#include <vector>
#include <algorithm>
#include <random>

static const int NPTS = 255;  // quotient points 1..255

struct Row {
    uint64_t mask[4]; // 256-bit mask
    int cap;
};

std::vector<Row> rows;
int target;

// Per-point: which rows contain this point, pre-indexed
std::vector<std::vector<int>> pt_rows; // pt_rows[q] = list of row indices containing q

void load_binary(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "Cannot open %s\n", path); exit(1); }
    char magic[8];
    fread(magic, 1, 8, f);
    if (memcmp(magic, "E11WANG1", 8) != 0) {
        fprintf(stderr, "Bad magic\n"); exit(1);
    }
    uint64_t nrows;
    fread(&nrows, 8, 1, f);
    rows.resize(nrows);
    for (uint64_t i = 0; i < nrows; i++) {
        uint8_t buf[36];
        fread(buf, 1, 36, f);
        memcpy(rows[i].mask, buf, 32);
        int32_t cap;
        memcpy(&cap, buf + 32, 4);
        rows[i].cap = cap;
    }
    fclose(f);
    fprintf(stderr, "Loaded %lu rows\n", (unsigned long)nrows);
}

inline bool in_mask(const Row& r, int pt) {
    return (r.mask[pt >> 6] >> (pt & 63)) & 1;
}

void build_index() {
    pt_rows.resize(256);
    for (int i = 0; i < (int)rows.size(); i++) {
        if (rows[i].cap <= 0 || rows[i].cap >= target) continue;
        for (int q = 1; q <= NPTS; q++) {
            if (in_mask(rows[i], q)) {
                pt_rows[q].push_back(i);
            }
        }
    }
    size_t total = 0;
    for (int q = 1; q <= NPTS; q++) total += pt_rows[q].size();
    fprintf(stderr, "Index: %zu total entries\n", total);
}

// count[i] = number of selected points in row i
std::vector<int> cnt;

void init_counts() {
    cnt.assign(rows.size(), 0);
}

void add_point(int q) {
    for (int ri : pt_rows[q]) cnt[ri]++;
}

void remove_point(int q) {
    for (int ri : pt_rows[q]) cnt[ri]--;
}

int count_violations() {
    int v = 0;
    for (int i = 0; i < (int)rows.size(); i++) {
        if (rows[i].cap > 0 && rows[i].cap < target && cnt[i] > rows[i].cap) v++;
    }
    return v;
}

// Delta violations when swapping out old_q for new_q
int delta_violations(int old_q, int new_q) {
    int delta = 0;
    // Rows containing old_q: their count decreases by 1
    for (int ri : pt_rows[old_q]) {
        if (rows[ri].cap <= 0 || rows[ri].cap >= target) continue;
        bool was_viol = cnt[ri] > rows[ri].cap;
        bool now_viol = (cnt[ri] - 1) > rows[ri].cap;
        delta += (int)now_viol - (int)was_viol;
    }
    // Rows containing new_q: their count increases by 1
    for (int ri : pt_rows[new_q]) {
        if (rows[ri].cap <= 0 || rows[ri].cap >= target) continue;
        // Check if old_q is also in this row (count change would be 0)
        bool has_old = in_mask(rows[ri], old_q);
        int effective_cnt = cnt[ri] + (has_old ? -1 : 0);
        bool was_viol = effective_cnt > rows[ri].cap;
        bool now_viol = (effective_cnt + 1) > rows[ri].cap;
        delta += (int)now_viol - (int)was_viol;
    }
    return delta;
}

int main(int argc, char** argv) {
    if (argc < 6) {
        fprintf(stderr, "Usage: %s <binary> <target> <trials> <steps> <seed>\n", argv[0]);
        return 1;
    }
    load_binary(argv[1]);
    target = atoi(argv[2]);
    int trials = atoi(argv[3]);
    int max_steps = atoi(argv[4]);
    unsigned seed = atoi(argv[5]);

    // Compute multiplicity bounds
    std::vector<int> mult_bound(256, target);
    mult_bound[0] = 0;
    for (int i = 0; i < (int)rows.size(); i++) {
        if (rows[i].cap <= 0) continue;
        for (int q = 1; q <= NPTS; q++) {
            if (in_mask(rows[i], q) && rows[i].cap < mult_bound[q]) {
                mult_bound[q] = rows[i].cap;
            }
        }
    }

    build_index();

    int global_best = target * 100;
    std::vector<int> best_support;

    printf("{\"trials\":[");
    for (int trial = 0; trial < trials; trial++) {
        std::mt19937 rng(seed + trial);
        
        // Random initial support
        std::vector<int> pool;
        for (int q = 1; q <= NPTS; q++) {
            for (int c = 0; c < mult_bound[q]; c++) pool.push_back(q);
        }
        std::shuffle(pool.begin(), pool.end(), rng);
        
        std::vector<int> support(pool.begin(), pool.begin() + std::min(target, (int)pool.size()));
        std::sort(support.begin(), support.end());
        
        // Count multiplicities
        std::vector<int> mult(256, 0);
        for (int q : support) mult[q]++;
        
        // Initialize counts
        init_counts();
        for (int q : support) add_point(q);
        
        int best_viol = count_violations();
        std::vector<int> best_sup = support;
        
        for (int ARTIFACT = 0; ARTIFACT < max_steps && best_viol > 0; ARTIFACT++) {
            // Pick random point to remove
            int idx = rng() % support.size();
            int old_q = support[idx];
            
            // Pick random point to add (respecting mult bounds)
            std::vector<int> candidates;
            for (int q = 1; q <= NPTS; q++) {
                if (q != old_q && mult[q] < mult_bound[q]) {
                    candidates.push_back(q);
                }
            }
            if (candidates.empty()) continue;
            int new_q = candidates[rng() % candidates.size()];
            
            int d = delta_violations(old_q, new_q);
            if (d <= 0) {
                remove_point(old_q);
                mult[old_q]--;
                add_point(new_q);
                mult[new_q]++;
                support[idx] = new_q;
                
                int new_viol = best_viol + d;
                if (new_viol < best_viol) {
                    best_viol = new_viol;
                    best_sup = support;
                    std::sort(best_sup.begin(), best_sup.end());
                }
            }
        }
        
        if (trial > 0) printf(",");
        printf("{\"trial\":%d,\"violations\":%d", trial, best_viol);
        if (best_viol == 0) {
            printf(",\"support\":[");
            for (int i = 0; i < (int)best_sup.size(); i++) {
                if (i) printf(",");
                printf("%d", best_sup[i]);
            }
            printf("]");
        }
        printf("}\n");
        fflush(stdout);
        
        if (best_viol < global_best) {
            global_best = best_viol;
            best_support = best_sup;
        }
        if (best_viol == 0) {
            fprintf(stderr, "Trial %d: ZERO violations!\n", trial);
        } else if (trial % 10 == 0) {
            fprintf(stderr, "Trial %d: best=%d (global=%d)\n", trial, best_viol, global_best);
        }
    }
    printf("],\"global_best\":%d", global_best);
    if (!best_support.empty()) {
        printf(",\"best_support\":[");
        for (int i = 0; i < (int)best_support.size(); i++) {
            if (i) printf(",");
            printf("%d", best_support[i]);
        }
        printf("]");
    }
    printf("}\n");
    return 0;
}
