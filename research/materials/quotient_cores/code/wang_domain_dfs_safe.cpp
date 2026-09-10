// Safe upper-bound-only domain DFS for Wang support enumeration.
//
// Supports two binary formats already produced in this investigation:
//   E11WANG1: 4 x 64-bit masks, points 1..255
//   WANG512\x01: 8 x 64-bit masks, points 1..511
//
// Mathematical model: choose a DISTINCT set of target_depth points.  For each
// Wang row, occupancy in its mask must be <= cap.  Forward propagation is only
// the sound upper-bound rule: once occupancy reaches cap, no further point in
// that row can be chosen, so remaining domain points in that row are removed.
// No lower-fill rule is used.
//
// This program is intentionally not a multiset enumerator.  Repeated directions
// must be handled by residual-cap reduction or by a separate multiset search.
//
// Orbit-branching should forbid points from earlier orbits in the initial
// domain and force one representative from the first occupied orbit.  The
// constraint masks themselves must remain unchanged; otherwise caps are weakened.

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

struct Row {
    uint32_t file_idx;
    uint8_t cap;
    uint8_t dim;
    uint16_t npts;
    std::vector<uint16_t> pts;
};

static int NPTS = 0;
static int MASK_WORDS = 0;
static std::vector<Row> small_rows; // dim<=3 and <=7 points: propagated
static std::vector<Row> big_rows;   // all other rows: counter only
static std::vector<std::vector<int>> pt_small_rows;
static std::vector<std::vector<int>> pt_big_rows;

static std::vector<uint8_t> small_count;
static std::vector<uint8_t> small_remain;
static std::vector<uint8_t> big_count;
static std::vector<uint8_t> domain;
static std::vector<uint8_t> forbidden;
static int domain_size = 0;
static int initial_forbidden_count = 0;
static int initial_domain_after_forbid = 0;
static int initial_domain_after_cap0 = 0;

struct UndoEntry { uint16_t point; };
static std::vector<UndoEntry> undo_stack;
static std::vector<int> undo_marks;

static std::vector<uint8_t> used_saturated_small;
static std::vector<uint8_t> used_overcap_small;
static std::vector<uint8_t> used_overcap_big;

static uint64_t dfs_calls = 0;
static uint64_t candidate_tests = 0;
static uint64_t solutions = 0;
static int max_depth = 0;
static std::vector<uint64_t> node_counts;
static std::vector<std::vector<int>> solutions_head;
static int selected_arr[64];
static int target_depth = 19;
static double time_limit = 3600.0;
static bool timed_out = false;
static bool early_solution_stop = false;
static uint64_t max_solutions = 100;
static auto t_start = std::chrono::steady_clock::now();

static std::vector<int> force_prefix;
static bool force_only = false;
static const char* out_path = nullptr;
static const char* used_path = nullptr;

static double elapsed_sec() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t_start).count();
}

static bool read_constraints(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "Cannot open %s\n", path); return false; }
    char magic[8];
    if (fread(magic, 1, 8, f) != 8) { fclose(f); return false; }
    if (memcmp(magic, "E11WANG1", 8) == 0) { NPTS = 255; MASK_WORDS = 4; }
    else if (memcmp(magic, "WANG512\x01", 8) == 0) { NPTS = 511; MASK_WORDS = 8; }
    else { fprintf(stderr, "Bad magic in %s\n", path); fclose(f); return false; }
    uint32_t nrows = 0;
    if (fread(&nrows, 4, 1, f) != 1) { fclose(f); return false; }

    pt_small_rows.assign(NPTS + 1, std::vector<int>());
    pt_big_rows.assign(NPTS + 1, std::vector<int>());

    for (uint32_t i = 0; i < nrows; i++) {
        uint8_t cap = 0, dim = 0; uint16_t reserved = 0;
        if (fread(&cap, 1, 1, f) != 1) { fclose(f); return false; }
        if (fread(&dim, 1, 1, f) != 1) { fclose(f); return false; }
        if (fread(&reserved, 2, 1, f) != 1) { fclose(f); return false; }
        std::vector<uint64_t> words(MASK_WORDS, 0);
        if (fread(words.data(), 8, MASK_WORDS, f) != (size_t)MASK_WORDS) { fclose(f); return false; }
        std::vector<uint16_t> pts;
        for (int w = 0; w < MASK_WORDS; w++) {
            uint64_t m = words[w];
            while (m) {
                int b = __builtin_ctzll(m);
                int p = w * 64 + b;
                if (p >= 1 && p <= NPTS) pts.push_back((uint16_t)p);
                m &= m - 1;
            }
        }
        Row r;
        r.file_idx = i; r.cap = cap; r.dim = dim; r.npts = (uint16_t)pts.size(); r.pts.swap(pts);
        if (r.dim <= 3 && r.npts <= 7) {
            int idx = (int)small_rows.size();
            small_rows.push_back(r);
            for (uint16_t p : small_rows.back().pts) pt_small_rows[p].push_back(idx);
        } else {
            int idx = (int)big_rows.size();
            big_rows.push_back(r);
            for (uint16_t p : big_rows.back().pts) pt_big_rows[p].push_back(idx);
        }
    }
    fclose(f);
    fprintf(stderr, "Loaded %u rows: %d small, %d big, NPTS=%d\n", nrows,
            (int)small_rows.size(), (int)big_rows.size(), NPTS);
    return true;
}

static std::vector<int> parse_points(const char* s) {
    std::vector<int> out;
    if (!s || !*s) return out;
    std::string x(s);
    size_t pos = 0;
    while (pos < x.size()) {
        size_t nxt = x.find(',', pos);
        if (nxt == std::string::npos) nxt = x.size();
        std::string tok = x.substr(pos, nxt - pos);
        if (!tok.empty()) out.push_back(atoi(tok.c_str()));
        pos = nxt + 1;
    }
    return out;
}

static void remove_domain_point_no_fail(int p) {
    if (!domain[p]) return;
    domain[p] = 0;
    domain_size--;
    undo_stack.push_back({(uint16_t)p});
    for (int ri : pt_small_rows[p]) {
        small_remain[ri]--;
    }
}

static void propagate_saturated_row(int ri) {
    used_saturated_small[ri] = 1;
    const Row& r = small_rows[ri];
    for (uint16_t q : r.pts) {
        if (domain[q]) remove_domain_point_no_fail((int)q);
    }
}

static bool select_point(int p, int depth) {
    undo_marks.push_back((int)undo_stack.size());
    remove_domain_point_no_fail(p);

    bool ok = true;
    for (int ri : pt_small_rows[p]) {
        small_count[ri]++;
        if (small_count[ri] > small_rows[ri].cap) {
            used_overcap_small[ri] = 1;
            ok = false;
        }
    }
    for (int ri : pt_big_rows[p]) {
        big_count[ri]++;
        if (big_count[ri] > big_rows[ri].cap) {
            used_overcap_big[ri] = 1;
            ok = false;
        }
    }
    if (!ok) return false;

    for (int ri : pt_small_rows[p]) {
        if (small_count[ri] == small_rows[ri].cap) propagate_saturated_row(ri);
    }
    return true;
}

static void undo_select(int p) {
    int mark = undo_marks.back();
    undo_marks.pop_back();
    while ((int)undo_stack.size() > mark) {
        int q = undo_stack.back().point;
        undo_stack.pop_back();
        if (!domain[q]) {
            domain[q] = 1;
            domain_size++;
            for (int ri : pt_small_rows[q]) small_remain[ri]++;
        }
    }
    for (int ri : pt_small_rows[p]) small_count[ri]--;
    for (int ri : pt_big_rows[p]) big_count[ri]--;
}

static int available_from(int min_pt) {
    int c = 0;
    for (int p = min_pt; p <= NPTS; p++) if (domain[p]) c++;
    return c;
}

static void dfs(int depth, int min_pt) {
    if (timed_out) return;
    dfs_calls++;
    if (depth >= (int)node_counts.size()) node_counts.resize(depth + 1, 0);
    node_counts[depth]++;
    if (depth > max_depth) max_depth = depth;
    if (depth == target_depth) {
        solutions++;
        if (solutions <= max_solutions) solutions_head.push_back(std::vector<int>(selected_arr, selected_arr + depth));
        if (solutions >= max_solutions) early_solution_stop = true;
        return;
    }
    if ((dfs_calls & ((1u << 13) - 1)) == 0) {
        if (elapsed_sec() > time_limit) { timed_out = true; return; }
    }
    int needed = target_depth - depth;
    if (available_from(min_pt) < needed) return;

    for (int p = min_pt; p <= NPTS; p++) {
        if (!domain[p]) continue;
        int avail = available_from(p);
        if (avail < needed) break;
        candidate_tests++;
        selected_arr[depth] = p;
        bool ok = select_point(p, depth);
        if (ok) dfs(depth + 1, p + 1);
        undo_select(p);
        if (early_solution_stop || timed_out) return;
        if ((candidate_tests & ((1u << 13) - 1)) == 0 && elapsed_sec() > time_limit) { timed_out = true; return; }
    }
}

static void initialize_domain() {
    domain.assign(NPTS + 1, 0);
    initial_forbidden_count = 0;
    for (int p = 1; p <= NPTS; p++) {
        if (forbidden[p]) initial_forbidden_count++;
        domain[p] = forbidden[p] ? 0 : 1;
    }
    domain_size = 0;
    for (int p = 1; p <= NPTS; p++) if (domain[p]) domain_size++;
    initial_domain_after_forbid = domain_size;
    small_remain.assign(small_rows.size(), 0);
    for (int ri = 0; ri < (int)small_rows.size(); ri++) {
        uint8_t cnt = 0;
        for (uint16_t p : small_rows[ri].pts) if (domain[p]) cnt++;
        small_remain[ri] = cnt;
    }
    // Initial cap-0 rows remove all their domain points. Repeat once over all
    // small rows; removals do not create new occupancy, so no queue is needed.
    undo_marks.push_back((int)undo_stack.size());
    for (int ri = 0; ri < (int)small_rows.size(); ri++) {
        if (small_rows[ri].cap == 0) propagate_saturated_row(ri);
    }
    undo_marks.pop_back(); // permanent domain restriction; do not undo.
    initial_domain_after_cap0 = domain_size;
}

static bool apply_force_prefix(int& depth, int& min_pt, std::string& reason) {
    int last = 0;
    for (int p : force_prefix) {
        if (p < 1 || p > NPTS) { reason = "force point out of range"; return false; }
        if (p <= last) { reason = "force prefix not strictly increasing/distinct"; return false; }
        if (!domain[p]) { reason = "force point unavailable before selection"; return false; }
        selected_arr[depth] = p;
        bool ok = select_point(p, depth);
        if (!ok) { reason = "force point violates a cap"; return false; }
        depth++;
        last = p;
        min_pt = p + 1;
        if (depth > target_depth) { reason = "force prefix longer than target"; return false; }
    }
    reason = "ok";
    return true;
}

static void write_used_rows() {
    if (!used_path) return;
    FILE* f = fopen(used_path, "w");
    if (!f) { fprintf(stderr, "Cannot open used-row output %s\n", used_path); return; }
    fprintf(f, "{\n");
    auto emit = [&](const char* name, const std::vector<uint8_t>& flags, const std::vector<Row>& rows) {
        fprintf(f, "  \"%s\": [", name);
        bool first = true;
        for (int i = 0; i < (int)flags.size(); i++) if (flags[i]) {
            if (!first) fprintf(f, ",");
            first = false;
            fprintf(f, "%u", rows[i].file_idx);
        }
        fprintf(f, "]");
    };
    emit("small_saturated_file_rows", used_saturated_small, small_rows); fprintf(f, ",\n");
    emit("small_overcap_file_rows", used_overcap_small, small_rows); fprintf(f, ",\n");
    emit("big_overcap_file_rows", used_overcap_big, big_rows); fprintf(f, "\n");
    fprintf(f, "}\n");
    fclose(f);
}

int main(int argc, char** argv) {
    const char* cons_path = nullptr;
    const char* exclude_str = nullptr;
    const char* force_str = nullptr;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--constraints") && i + 1 < argc) cons_path = argv[++i];
        else if (!strcmp(argv[i], "--output") && i + 1 < argc) out_path = argv[++i];
        else if (!strcmp(argv[i], "--used-output") && i + 1 < argc) used_path = argv[++i];
        else if (!strcmp(argv[i], "--target") && i + 1 < argc) target_depth = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--timeout") && i + 1 < argc) time_limit = atof(argv[++i]);
        else if (!strcmp(argv[i], "--max-solutions") && i + 1 < argc) max_solutions = strtoull(argv[++i], nullptr, 10);
        else if ((!strcmp(argv[i], "--exclude") || !strcmp(argv[i], "--forbid-set")) && i + 1 < argc) exclude_str = argv[++i];
        else if (!strcmp(argv[i], "--force-prefix") && i + 1 < argc) force_str = argv[++i];
        else if (!strcmp(argv[i], "--force-only")) force_only = true;
        else { fprintf(stderr, "Unknown or incomplete argument: %s\n", argv[i]); return 1; }
    }
    if (!cons_path) { fprintf(stderr, "Need --constraints FILE\n"); return 1; }
    if (!read_constraints(cons_path)) return 1;
    if (target_depth >= 64) { fprintf(stderr, "target too large\n"); return 1; }

    forbidden.assign(NPTS + 1, 0);
    for (int p : parse_points(exclude_str)) if (p >= 1 && p <= NPTS) forbidden[p] = 1;
    force_prefix = parse_points(force_str);

    small_count.assign(small_rows.size(), 0);
    big_count.assign(big_rows.size(), 0);
    used_saturated_small.assign(small_rows.size(), 0);
    used_overcap_small.assign(small_rows.size(), 0);
    used_overcap_big.assign(big_rows.size(), 0);
    node_counts.assign(target_depth + 1, 0);
    initialize_domain();

    t_start = std::chrono::steady_clock::now();
    int depth = 0;
    int min_pt = 1;
    std::string force_reason;
    bool forced_ok = apply_force_prefix(depth, min_pt, force_reason);
    bool forced_reached_target = forced_ok && (depth == target_depth);
    if (forced_ok) {
        if (force_only) {
            if (forced_reached_target) {
                dfs_calls = 1;
                node_counts[depth] = 1;
                max_depth = depth;
                solutions = 1;
                solutions_head.push_back(std::vector<int>(selected_arr, selected_arr + depth));
            } else {
                dfs(depth, min_pt);
            }
        } else {
            dfs(depth, min_pt);
        }
    }
    double elapsed = elapsed_sec();
    bool complete = !timed_out && !early_solution_stop;

    int saturated_count = 0, small_over_count = 0, big_over_count = 0;
    for (auto x : used_saturated_small) if (x) saturated_count++;
    for (auto x : used_overcap_small) if (x) small_over_count++;
    for (auto x : used_overcap_big) if (x) big_over_count++;
    write_used_rows();

    FILE* out = stdout;
    if (out_path) { out = fopen(out_path, "w"); if (!out) out = stdout; }
    fprintf(out, "{\"target\":%d,\"npts\":%d,\"elapsed_sec\":%.6f,\"timeout\":%s,\"early_solution_stop\":%s,\"complete\":%s,",
            target_depth, NPTS, elapsed, timed_out ? "true" : "false", early_solution_stop ? "true" : "false", complete ? "true" : "false");
    fprintf(out, "\"dfs_calls\":%llu,\"candidate_tests\":%llu,\"solutions\":%llu,\"max_depth\":%d,",
            (unsigned long long)dfs_calls, (unsigned long long)candidate_tests,
            (unsigned long long)solutions, max_depth);
    fprintf(out, "\"initial_forbidden_count\":%d,\"initial_domain_after_forbid\":%d,\"initial_domain_after_cap0\":%d,",
            initial_forbidden_count, initial_domain_after_forbid, initial_domain_after_cap0);
    fprintf(out, "\"force_prefix_size\":%d,\"forced_ok\":%s,\"forced_reached_target\":%s,\"force_reason\":\"%s\",",
            (int)force_prefix.size(), forced_ok ? "true" : "false", forced_reached_target ? "true" : "false", force_reason.c_str());
    fprintf(out, "\"used_small_saturation_count\":%d,\"used_small_overcap_count\":%d,\"used_big_overcap_count\":%d,",
            saturated_count, small_over_count, big_over_count);
    fprintf(out, "\"node_count_by_depth\":[");
    for (int d = 0; d <= target_depth; d++) { if (d) fprintf(out, ","); fprintf(out, "%llu", (unsigned long long)node_counts[d]); }
    fprintf(out, "],\"solutions_head\":[");
    for (int i = 0; i < (int)solutions_head.size() && i < 10; i++) {
        if (i) fprintf(out, ","); fprintf(out, "[");
        for (int j = 0; j < (int)solutions_head[i].size(); j++) { if (j) fprintf(out, ","); fprintf(out, "%d", solutions_head[i][j]); }
        fprintf(out, "]");
    }
    fprintf(out, "]}\n");
    if (out != stdout) { fclose(out); fprintf(stderr, "Wrote %s\n", out_path); }
    fprintf(stderr, "safe DFS: %.3fs, complete=%s, calls=%llu, sols=%llu, max_depth=%d, domain_after_forbid=%d, domain_after_cap0=%d, saturated_rows=%d\n",
            elapsed, complete ? "yes" : "no", (unsigned long long)dfs_calls,
            (unsigned long long)solutions, max_depth, initial_domain_after_forbid, initial_domain_after_cap0, saturated_count);
    return 0;
}
