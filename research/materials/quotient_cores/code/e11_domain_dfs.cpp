// Domain-propagation DFS for E11 Wang support enumeration.
//
// Key improvement over the counter-only DFS: when a row's occupancy reaches
// its cap, all remaining points in that row are removed from the domain.
// Removals propagate: if a row's remaining points drop below (cap - count),
// the current branch is infeasible.
//
// Uses the E11WANG1 binary constraint format.
//
// Compile: g++ -O3 -march=native -std=c++17 -o e11_domain_dfs e11_domain_dfs.cpp
// Run: ./e11_domain_dfs --constraints FILE --target 19 --branch REP --timeout 3600

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>

static constexpr int NPTS = 255; // nonzero points 1..255

struct Row {
    uint8_t cap;
    uint8_t dim;
    uint8_t npts;      // number of points in this row
    uint8_t pts[7];    // up to 7 points (dim<=3 has <=7)
    // For dim>3 we only use counter-based checking
};

struct BigRow {
    uint8_t cap;
    uint16_t npts;
    // points stored in a separate flat array
};

// Constraint data
static int n_small_rows = 0; // dim <= 3, used for propagation
static int n_big_rows = 0;   // dim > 3, counter-only
static std::vector<Row> small_rows;
static std::vector<BigRow> big_rows;
static std::vector<uint8_t> big_row_pts; // flat storage for big row points
static std::vector<int> big_row_offsets;

// Per-point: which small rows contain it
static std::vector<std::vector<int>> pt_small_rows; // pt_small_rows[p] = list of small_row indices

// Per-point: which big rows contain it  
static std::vector<std::vector<int>> pt_big_rows;

// State arrays (per DFS level, stack-allocated)
static uint8_t small_count[500000]; // current occupancy per small row
static uint8_t small_remain[500000]; // remaining available points per small row
static uint8_t big_count[500000]; // current occupancy per big row

// Domain: which points are available
static bool domain[256]; // domain[p] = true if p is available
static int domain_size = NPTS;

// Undo stack for propagation
struct UndoEntry {
    int point; // point that was removed from domain
};
static std::vector<UndoEntry> undo_stack;
static std::vector<int> undo_marks; // stack of undo_stack.size() at each selection

// Stats
static uint64_t dfs_calls = 0;
static uint64_t solutions = 0;
static int max_depth = 0;
static uint64_t node_counts[20] = {};
static std::vector<std::vector<int>> solutions_head;
static int target_depth = 19;
static double time_limit = 3600.0;
static auto t_start = std::chrono::steady_clock::now();

// Branch: first point must be branch_rep, forbid points in earlier orbits
static int branch_rep = -1;
static bool forbidden_global[256] = {};

bool load_constraints(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "Cannot open %s\n", path); return false; }
    
    char magic[8];
    fread(magic, 1, 8, f);
    if (memcmp(magic, "E11WANG1", 8) != 0) {
        fprintf(stderr, "Bad magic\n"); fclose(f); return false;
    }
    
    uint32_t nrows;
    fread(&nrows, 4, 1, f);
    
    pt_small_rows.resize(256);
    pt_big_rows.resize(256);
    
    for (uint32_t i = 0; i < nrows; i++) {
        uint8_t cap, dim; uint16_t reserved;
        uint64_t mask[4];
        fread(&cap, 1, 1, f);
        fread(&dim, 1, 1, f);
        fread(&reserved, 2, 1, f);
        fread(mask, 8, 4, f);
        
        // Collect points
        std::vector<int> pts;
        for (int w = 0; w < 4; w++) {
            uint64_t m = mask[w];
            while (m) {
                int bit = __builtin_ctzll(m);
                int p = w * 64 + bit;
                if (p >= 1 && p <= 255) pts.push_back(p);
                m &= m - 1;
            }
        }
        
        if (dim <= 3 && pts.size() <= 7) {
            Row r;
            r.cap = cap;
            r.dim = dim;
            r.npts = (uint8_t)pts.size();
            for (int j = 0; j < (int)pts.size(); j++) r.pts[j] = pts[j];
            int idx = (int)small_rows.size();
            small_rows.push_back(r);
            for (int p : pts) pt_small_rows[p].push_back(idx);
        } else {
            BigRow br;
            br.cap = cap;
            br.npts = (uint16_t)pts.size();
            int idx = (int)big_rows.size();
            big_row_offsets.push_back((int)big_row_pts.size());
            for (int p : pts) {
                big_row_pts.push_back((uint8_t)p);
                pt_big_rows[p].push_back(idx);
            }
            big_rows.push_back(br);
        }
    }
    fclose(f);
    
    n_small_rows = (int)small_rows.size();
    n_big_rows = (int)big_rows.size();
    big_row_offsets.push_back((int)big_row_pts.size()); // sentinel
    
    fprintf(stderr, "Loaded %u constraints: %d small (dim<=3), %d big (dim>3)\n",
            nrows, n_small_rows, n_big_rows);
    return true;
}

// Remove a point from the domain and propagate.
// Returns false if propagation finds an infeasible state.
bool remove_point_propagate(int p, int needed) {
    if (!domain[p]) return true; // already removed
    domain[p] = false;
    domain_size--;
    undo_stack.push_back({p});
    
    // For each small row containing p: decrement remain
    for (int ri : pt_small_rows[p]) {
        small_remain[ri]--;
        // If remain < cap - count, infeasible
        if (small_remain[ri] < small_rows[ri].cap - small_count[ri]) {
            return false;
        }
        // Note: we don't propagate from remain reaching exactly (cap-count),
        // because that would mean we MUST select all remaining points in the row,
        // which is a stronger inference. For simplicity, we only propagate
        // when count reaches cap (done in select_point).
    }
    
    if (domain_size < needed) return false;
    return true;
}

// Select a point: add to set, increment counts, propagate removals.
// Returns false if infeasible.
bool select_point(int p, int depth) {
    int needed = target_depth - depth - 1; // points still needed after this
    undo_marks.push_back((int)undo_stack.size());
    
    // Remove p from domain (it's now selected, not available for future)
    domain[p] = false;
    domain_size--;
    undo_stack.push_back({p});
    
    // For each small row containing p
    for (int ri : pt_small_rows[p]) {
        small_count[ri]++;
        // Don't decrement remain for p itself (it was available, now selected)
        // Actually remain should decrease when domain changes, but p is still
        // "accounted for" - it's selected, not available but counted.
        // Let's track remain as "available points in domain" (not yet selected).
        // When p is selected: remain decreases by 1 (p leaves domain).
        // Already handled above.
        
        if (small_count[ri] == small_rows[ri].cap) {
            // Row saturated: remove all remaining available points in this row
            const Row& r = small_rows[ri];
            for (int j = 0; j < r.npts; j++) {
                int q = r.pts[j];
                if (domain[q]) {
                    if (!remove_point_propagate(q, needed)) return false;
                }
            }
        }
    }
    
    // For each big row containing p
    for (int ri : pt_big_rows[p]) {
        big_count[ri]++;
        if (big_count[ri] > big_rows[ri].cap) {
            return false; // over cap
        }
    }
    
    if (domain_size < needed) return false;
    return true;
}

// Undo the selection of a point (restore domain state)
void undo_select() {
    int mark = undo_marks.back();
    undo_marks.pop_back();
    
    // Restore domain entries
    while ((int)undo_stack.size() > mark) {
        int p = undo_stack.back().point;
        undo_stack.pop_back();
        domain[p] = true;
        domain_size++;
        // Restore small_remain
        for (int ri : pt_small_rows[p]) {
            small_remain[ri]++;
        }
    }
    
    // Note: we need to restore small_count and big_count for the selected point.
    // But the selected point is the first entry after mark.
    // Actually, the undo restores domain and remain but not count.
    // We handle count in the DFS caller.
}

// Restore counts for selected point p
void restore_counts(int p) {
    for (int ri : pt_small_rows[p]) {
        small_count[ri]--;
    }
    for (int ri : pt_big_rows[p]) {
        big_count[ri]--;
    }
}

int selected[20];

void dfs(int depth, int min_pt) {
    dfs_calls++;
    node_counts[depth]++;
    if (depth > max_depth) max_depth = depth;
    
    if (depth == target_depth) {
        solutions++;
        if (solutions <= 100) {
            std::vector<int> sol(selected, selected + depth);
            solutions_head.push_back(sol);
        }
        return;
    }
    
    if (dfs_calls % 2000000 == 0) {
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration<double>(now - t_start).count();
        if (elapsed > time_limit) return;
    }
    
    // Iterate over available points >= min_pt
    for (int p = min_pt; p <= NPTS; p++) {
        if (!domain[p]) continue;
        if (forbidden_global[p]) continue;
        if (solutions > 0 && solutions <= 100) {} // continue collecting
        if (solutions > 100) return; // enough solutions collected
        
        // Check: enough remaining points?
        // Simple check: count available points >= p
        int avail = 0;
        for (int q = p; q <= NPTS; q++) {
            if (domain[q] && !forbidden_global[q]) avail++;
        }
        if (avail < target_depth - depth) break;
        
        // Select p
        selected[depth] = p;
        bool ok = select_point(p, depth);
        if (ok) {
            dfs(depth + 1, p + 1);
            if (solutions > 100) { undo_select(); restore_counts(p); return; }
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - t_start).count();
            if (elapsed > time_limit) { undo_select(); restore_counts(p); return; }
        }
        undo_select();
        restore_counts(p);
    }
}

int main(int argc, char** argv) {
    const char* cons_path = nullptr;
    const char* out_path = nullptr;
    const char* orbit_path = nullptr;
    const char* exclude_str = nullptr;
    int branch = -1;
    
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--constraints") == 0 && i+1 < argc)
            cons_path = argv[++i];
        else if (strcmp(argv[i], "--output") == 0 && i+1 < argc)
            out_path = argv[++i];
        else if (strcmp(argv[i], "--target") == 0 && i+1 < argc)
            target_depth = atoi(argv[++i]);
        else if (strcmp(argv[i], "--branch") == 0 && i+1 < argc)
            branch = atoi(argv[++i]);
        else if (strcmp(argv[i], "--branch-rep") == 0 && i+1 < argc)
            branch_rep = atoi(argv[++i]);
        else if (strcmp(argv[i], "--orbits") == 0 && i+1 < argc)
            orbit_path = argv[++i];
        else if (strcmp(argv[i], "--timeout") == 0 && i+1 < argc)
            time_limit = atof(argv[++i]);
        else if (strcmp(argv[i], "--exclude") == 0 && i+1 < argc)
            exclude_str = argv[++i];
    }
    
    if (!cons_path) {
        fprintf(stderr, "Usage: %s --constraints FILE [--target N] [--branch B] [--branch-rep R] [--orbits FILE] [--timeout S] [--output FILE]\n", argv[0]);
        return 1;
    }
    
    if (!load_constraints(cons_path)) return 1;
    
    // Initialize state
    memset(small_count, 0, sizeof(uint8_t) * n_small_rows);
    memset(big_count, 0, sizeof(uint8_t) * n_big_rows);
    for (int i = 0; i < n_small_rows; i++) {
        small_remain[i] = small_rows[i].npts;
    }
    memset(domain, 0, sizeof(domain));
    for (int p = 1; p <= NPTS; p++) domain[p] = true;
    domain_size = NPTS;
    memset(forbidden_global, 0, sizeof(forbidden_global));
    
    // Exclude points (comma-separated list)
    int n_excluded = 0;
    if (exclude_str) {
        std::string es(exclude_str);
        size_t pos2 = 0;
        while (pos2 < es.size()) {
            size_t next = es.find(',', pos2);
            if (next == std::string::npos) next = es.size();
            int p = atoi(es.substr(pos2, next - pos2).c_str());
            if (p >= 1 && p <= 255) { forbidden_global[p] = true; n_excluded++; }
            pos2 = next + 1;
        }
        fprintf(stderr, "Excluded %d points from domain\n", n_excluded);
    }
    
    // Branch setup: read orbits, forbid earlier points, force first selected = branch_rep
    if (branch >= 0 && orbit_path) {
        // Simple parsing of orbit JSON to get orbit members
        // For robustness, we use the hardcoded orbit data from the verified orbits
        FILE* of = fopen(orbit_path, "r");
        if (!of) { fprintf(stderr, "Cannot open orbit file\n"); return 1; }
        // Read entire file
        fseek(of, 0, SEEK_END);
        long sz = ftell(of);
        fseek(of, 0, SEEK_SET);
        std::vector<char> buf(sz + 1);
        fread(buf.data(), 1, sz, of);
        buf[sz] = 0;
        fclose(of);
        
        // Parse orbits: find "point_orbits" -> "orbits" -> array of objects with "members"
        // Simple approach: find each orbit's members array
        std::vector<std::vector<int>> orbits;
        const char* pos = strstr(buf.data(), "\"orbits\"");
        if (!pos) { fprintf(stderr, "Cannot find orbits in JSON\n"); return 1; }
        pos = strchr(pos, '[');
        if (!pos) { fprintf(stderr, "Cannot find orbits array\n"); return 1; }
        
        // Parse array of orbit objects
        int depth_bracket = 0;
        int orb_idx = 0;
        while (*pos) {
            if (*pos == '{') {
                // Find "members" array
                const char* mp = strstr(pos, "\"members\"");
                if (!mp) break;
                mp = strchr(mp, '[');
                if (!mp) break;
                mp++;
                std::vector<int> members;
                while (*mp && *mp != ']') {
                    while (*mp == ' ' || *mp == '\n' || *mp == '\r' || *mp == ',') mp++;
                    if (*mp == ']') break;
                    int val = 0;
                    while (*mp >= '0' && *mp <= '9') { val = val * 10 + (*mp - '0'); mp++; }
                    members.push_back(val);
                }
                orbits.push_back(members);
                // Skip to end of this object
                int bd = 1;
                pos++;
                while (*pos && bd > 0) {
                    if (*pos == '{') bd++;
                    else if (*pos == '}') bd--;
                    pos++;
                }
            } else {
                pos++;
                if (*pos == ']') break; // end of orbits array
            }
        }
        
        fprintf(stderr, "Parsed %d orbits\n", (int)orbits.size());
        
        if (branch >= (int)orbits.size()) {
            fprintf(stderr, "Branch %d >= orbit count %d\n", branch, (int)orbits.size());
            return 1;
        }
        
        // Forbid all points in orbits 0..branch-1
        for (int o = 0; o < branch; o++) {
            for (int p : orbits[o]) {
                if (p >= 1 && p <= 255) forbidden_global[p] = true;
            }
        }
        
        // Set branch_rep
        if (branch_rep < 0) {
            // Use orbit representative (first member)
            branch_rep = orbits[branch][0];
        }
        
        int forbidden_count = 0;
        for (int p = 1; p <= 255; p++) if (forbidden_global[p]) forbidden_count++;
        fprintf(stderr, "Branch %d rep %d, forbidden %d points from earlier orbits\n",
                branch, branch_rep, forbidden_count);
    }
    
    t_start = std::chrono::steady_clock::now();
    
    if (branch_rep > 0) {
        // Force first selected point = branch_rep
        selected[0] = branch_rep;
        bool ok = select_point(branch_rep, 0);
        if (ok) {
            dfs(1, branch_rep + 1);
        }
        undo_select();
        restore_counts(branch_rep);
    } else {
        dfs(0, 1);
    }
    
    auto t_end = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(t_end - t_start).count();
    bool complete = (elapsed < time_limit - 1.0);
    
    // Output JSON
    FILE* out = stdout;
    if (out_path) {
        out = fopen(out_path, "w");
        if (!out) { fprintf(stderr, "Cannot open %s\n", out_path); out = stdout; }
    }
    
    fprintf(out, "{\"branch\":%d,\"rep\":%d,\"target\":%d,\"elapsed_sec\":%.6f,"
            "\"timeout\":%s,\"complete\":%s,\"dfs_calls\":%llu,\"solutions\":%llu,"
            "\"max_depth\":%d,\"node_count_by_depth\":[",
            branch, branch_rep, target_depth, elapsed,
            complete ? "false" : "true",
            complete ? "true" : "false",
            (unsigned long long)dfs_calls,
            (unsigned long long)solutions,
            max_depth);
    
    for (int d = 0; d <= target_depth; d++) {
        if (d > 0) fprintf(out, ",");
        fprintf(out, "%llu", (unsigned long long)node_counts[d]);
    }
    fprintf(out, "],\"solutions_head\":[");
    for (int i = 0; i < (int)solutions_head.size() && i < 10; i++) {
        if (i > 0) fprintf(out, ",");
        fprintf(out, "[");
        for (int j = 0; j < (int)solutions_head[i].size(); j++) {
            if (j > 0) fprintf(out, ",");
            fprintf(out, "%d", solutions_head[i][j]);
        }
        fprintf(out, "]");
    }
    fprintf(out, "]}\n");
    
    if (out != stdout) {
        fclose(out);
        fprintf(stderr, "Wrote %s\n", out_path);
    }
    
    fprintf(stderr, "DFS: %.1fs, %llu calls, %llu solutions, max_depth=%d, complete=%s\n",
            elapsed, (unsigned long long)dfs_calls, (unsigned long long)solutions,
            max_depth, complete ? "yes" : "no");
    
    return 0;
}
