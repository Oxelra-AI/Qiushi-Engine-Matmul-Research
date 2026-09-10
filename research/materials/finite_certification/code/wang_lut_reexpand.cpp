// Independent C++ re-expansion of Wang certificate A-side subspace orbits.
//
// This program parses the text-format Wang certificate directly, constructs
// canonical RREF keys over F_2^9, verifies the elementary A-slot generators are
// genuine matrix-multiplication tensor automorphisms with compensating B,C
// transforms, expands every certificate representative by BFS under generators
// of GL_3(F_2) x GL_3(F_2) plus A-transpose, and writes a complete key->value
// binary table.  It deliberately does not read the earlier research orbit cache or LUT.

#include <algorithm>
#include <array>
#include <chrono>
#include <cctype>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using u128 = unsigned __int128;

struct Key {
    uint64_t lo;
    uint64_t hi;
    bool operator==(const Key& o) const { return lo == o.lo && hi == o.hi; }
    bool operator<(const Key& o) const { return hi < o.hi || (hi == o.hi && lo < o.lo); }
};
struct KeyHash {
    size_t operator()(const Key& k) const noexcept {
        uint64_t x = k.lo ^ (k.hi + 0x9e3779b97f4a7c15ULL + (k.lo<<6) + (k.lo>>2));
        x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
        x ^= x >> 27; x *= 0x94d049bb133111ebULL;
        x ^= x >> 31;
        return (size_t)x;
    }
};

struct ValueRec { int lb; int cert_index; int dim; int proof_type; };
struct CertRec { int cert_index; int lb; std::vector<int> rows; int proof_type; };
struct BinRec { Key key; ValueRec val; };

static int msb(int x) { return x ? 31 - __builtin_clz((unsigned)x) : -1; }

std::vector<int> rref_basis(const std::vector<int>& rows) {
    std::array<int,9> basis{}; basis.fill(0);
    for (int raw : rows) {
        int x = raw & 0x1ff;
        if (!x) continue;
        bool changed = true;
        while (x && changed) {
            changed = false;
            for (int p = 8; p >= 0; --p) {
                if (basis[p] && ((x >> p) & 1)) { x ^= basis[p]; changed = true; }
            }
        }
        if (!x) continue;
        int p = msb(x);
        for (int q = 0; q < 9; ++q) if (basis[q] && ((basis[q] >> p) & 1)) basis[q] ^= x;
        basis[p] = x;
    }
    std::vector<int> out;
    for (int p = 8; p >= 0; --p) if (basis[p]) out.push_back(basis[p]);
    return out;
}

Key make_key_from_basis(const std::vector<int>& basis0) {
    std::vector<int> basis = rref_basis(basis0);
    u128 packed = 0;
    for (size_t i = 0; i < basis.size(); ++i) packed |= ((u128)(basis[i] & 0x1ff)) << (9*i);
    u128 key = (packed << 4) | (u128)basis.size();
    return Key{(uint64_t)key, (uint64_t)(key >> 64)};
}
int key_dim(const Key& k) { return (int)(k.lo & 0xfULL); }

std::vector<int> span_basis_from_key(const Key& k) {
    u128 key = ((u128)k.hi << 64) | (u128)k.lo;
    int d = (int)(key & 0xf);
    u128 packed = key >> 4;
    std::vector<int> rows;
    rows.reserve(d);
    for (int i = 0; i < d; ++i) rows.push_back((int)((packed >> (9*i)) & 0x1ff));
    return rows;
}

std::vector<int> decode_textproto_bytes_literal(const std::string& quoted) {
    size_t first = quoted.find('"');
    size_t last = quoted.rfind('"');
    if (first == std::string::npos || last == first) throw std::runtime_error("bad quoted bytes");
    std::vector<int> bytes;
    for (size_t i = first + 1; i < last; ++i) {
        unsigned char ch = quoted[i];
        if (ch == '\\' && i + 1 < last) {
            if (i + 3 < last && quoted[i+1] >= '0' && quoted[i+1] <= '7' && quoted[i+2] >= '0' && quoted[i+2] <= '7' && quoted[i+3] >= '0' && quoted[i+3] <= '7') {
                int v = (quoted[i+1]-'0')*64 + (quoted[i+2]-'0')*8 + (quoted[i+3]-'0');
                bytes.push_back(v & 0xff); i += 3;
            } else {
                char n = quoted[++i];
                if (n == 'n') bytes.push_back('\n');
                else if (n == 'r') bytes.push_back('\r');
                else if (n == 't') bytes.push_back('\t');
                else bytes.push_back((unsigned char)n);
            }
        } else bytes.push_back(ch);
    }
    return bytes;
}

std::vector<int> decode_constraints(const std::string& quoted) {
    std::vector<int> b = decode_textproto_bytes_literal(quoted);
    if (b.size() % 2) throw std::runtime_error("constraint byte length odd");
    std::vector<int> vals;
    for (size_t i = 0; i < b.size(); i += 2) vals.push_back((b[i] | (b[i+1] << 8)) & 0x1ff);
    return vals;
}

std::vector<CertRec> parse_cert(const std::string& path) {
    std::ifstream in(path, std::ios::binary);
    if (!in) throw std::runtime_error("cannot open cert " + path);
    std::stringstream ss; ss << in.rdbuf(); std::string text = ss.str();
    std::vector<CertRec> recs;
    size_t pos = 0;
    while (true) {
        size_t start = text.find("constrained_tensors", pos);
        if (start == std::string::npos) break;
        size_t brace = text.find('{', start);
        if (brace == std::string::npos) break;
        int depth = 0; size_t end = brace;
        for (; end < text.size(); ++end) {
            if (text[end] == '{') depth++;
            else if (text[end] == '}') { depth--; if (depth == 0) { end++; break; } }
        }
        std::string block = text.substr(brace + 1, end - brace - 2);
        pos = end;
        CertRec r; r.cert_index = 0; r.lb = -999; r.proof_type = 0;
        std::smatch m;
        if (std::regex_search(block, m, std::regex("\\n\\s*index:\\s*([0-9]+)"))) r.cert_index = std::stoi(m[1]);
        std::string nblock = std::string("\n") + block;
        if (std::regex_search(nblock, m, std::regex("\\n\\s*rank_lower_bound:\\s*(-?[0-9]+)"))) r.lb = std::stoi(m[1]);
        if (std::regex_search(nblock, m, std::regex("\\n\\s*constraints:\\s*(\"[^\\n]*\")"))) r.rows = decode_constraints(m[1]);
        else r.rows.clear();
        if (block.find("flatten_matrix_proof") != std::string::npos) r.proof_type = 1;
        else if (block.find("forced_product_proof") != std::string::npos) r.proof_type = 2;
        else if (block.find("backtracking_proof") != std::string::npos) r.proof_type = 3;
        else if (block.find("degenerate_proof") != std::string::npos) r.proof_type = 4;
        recs.push_back(r);
    }
    return recs;
}

using Mat = std::array<std::array<int,3>,3>;
Mat I3() { Mat M{}; for(int i=0;i<3;i++) for(int j=0;j<3;j++) M[i][j]=(i==j); return M; }
Mat transvection(int i,int j) { Mat M = I3(); M[i][j] ^= 1; return M; }
Mat bits_to_mat(int x) { Mat M{}; for(int i=0;i<3;i++) for(int j=0;j<3;j++) M[i][j]=(x>>(3*i+j))&1; return M; }
int mat_to_bits(const Mat& M) { int x=0; for(int i=0;i<3;i++) for(int j=0;j<3;j++) if(M[i][j]&1) x |= 1 << (3*i+j); return x; }
Mat mt(const Mat& A){ Mat B{}; for(int i=0;i<3;i++) for(int j=0;j<3;j++) B[i][j]=A[j][i]; return B; }
Mat mm(const Mat& A,const Mat& B){ Mat C{}; for(int i=0;i<3;i++) for(int j=0;j<3;j++){ int s=0; for(int k=0;k<3;k++) s ^= (A[i][k]&B[k][j]); C[i][j]=s; } return C; }
int tr_ABCt(int Ab,int Bb,int Cb){ Mat A=bits_to_mat(Ab), B=bits_to_mat(Bb), C=bits_to_mat(Cb); Mat X=mm(mm(A,B),mt(C)); return X[0][0]^X[1][1]^X[2][2]; }

struct Gen { int kind; Mat M; std::array<int,512> mapA; }; // kind: 0 left, 1 right, 2 transpose

int transform_A_point(int a, const Gen& g) {
    Mat A = bits_to_mat(a);
    if (g.kind == 2) return mat_to_bits(mt(A));
    if (g.kind == 0) return mat_to_bits(mm(mt(g.M), A));
    // transvections are self-inverse over F2, so Q^{-T}=Q^T.
    return mat_to_bits(mm(A, mt(g.M)));
}
int transform_B_point(int b, const Gen& g) {
    Mat B = bits_to_mat(b);
    if (g.kind == 2) throw std::runtime_error("transpose B handled separately");
    if (g.kind == 0) return b;
    // B' = Q^T B for right generator with R=I.
    return mat_to_bits(mm(mt(g.M), B));
}
int transform_C_point(int c, const Gen& g) {
    Mat C = bits_to_mat(c);
    if (g.kind == 2) throw std::runtime_error("transpose C handled separately");
    if (g.kind == 0) {
        // C' = P^{-1} C; transvection inverse equals itself.
        return mat_to_bits(mm(g.M, C));
    }
    return c;
}

std::vector<Gen> make_generators() {
    std::vector<Gen> gens;
    for(int i=0;i<3;i++) for(int j=0;j<3;j++) if(i!=j) {
        Gen L; L.kind=0; L.M=transvection(i,j); for(int a=0;a<512;a++) L.mapA[a]=transform_A_point(a,L); gens.push_back(L);
        Gen R; R.kind=1; R.M=transvection(i,j); for(int a=0;a<512;a++) R.mapA[a]=transform_A_point(a,R); gens.push_back(R);
    }
    Gen T; T.kind=2; T.M=I3(); for(int a=0;a<512;a++) T.mapA[a]=transform_A_point(a,T); gens.push_back(T);
    return gens;
}

bool verify_generators_preserve_T(const std::vector<Gen>& gens, std::string& err) {
    for (size_t gi=0; gi<gens.size(); ++gi) {
        const Gen& g = gens[gi];
        for (int ai=0; ai<9; ++ai) for (int bi=0; bi<9; ++bi) for (int ci=0; ci<9; ++ci) {
            int A = 1<<ai, B = 1<<bi, C = 1<<ci;
            int lhs, rhs = tr_ABCt(A,B,C);
            if (g.kind == 2) lhs = tr_ABCt(transform_A_point(A,g), C, B);
            else lhs = tr_ABCt(transform_A_point(A,g), transform_B_point(B,g), transform_C_point(C,g));
            if (lhs != rhs) { std::ostringstream os; os << "generator "<<gi<<" failed at "<<ai<<","<<bi<<","<<ci; err=os.str(); return false; }
        }
    }
    return true;
}

Key transform_key_by_gen(const Key& key, const Gen& g) {
    std::vector<int> basis = span_basis_from_key(key);
    std::vector<int> img; img.reserve(basis.size());
    for (int r: basis) img.push_back(g.mapA[r]);
    return make_key_from_basis(img);
}

uint64_t gaussian_binomial(int n, int k) {
    __int128 num=1, den=1;
    for(int i=0;i<k;i++){ num *= (((__int128)1<<n) - ((int64_t)1<<i)); den *= (((__int128)1<<k) - ((int64_t)1<<i)); }
    return (uint64_t)(num/den);
}

void write_u64(std::ofstream& out, uint64_t x){ for(int i=0;i<8;i++) out.put((char)((x>>(8*i))&0xff)); }
void write_u16(std::ofstream& out, uint16_t x){ out.put((char)(x&0xff)); out.put((char)((x>>8)&0xff)); }
void write_u8(std::ofstream& out, uint8_t x){ out.put((char)x); }

int main(int argc, char** argv) {
    std::string cert_path = "data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt";
    std::string out_bin = "data/wang_reexpand/reexpanded_lut.bin";
    std::string out_json = "data/wang_reexpand/reexpand_summary.json";
    for (int i=1;i<argc;i++) {
        std::string a=argv[i];
        if (a=="--cert" && i+1<argc) cert_path=argv[++i];
        else if (a=="--out-bin" && i+1<argc) out_bin=argv[++i];
        else if (a=="--out-json" && i+1<argc) out_json=argv[++i];
    }
    auto t0 = std::chrono::steady_clock::now();
    std::vector<CertRec> recs = parse_cert(cert_path);
    std::vector<Gen> gens = make_generators();
    std::string gen_err; bool gens_ok = verify_generators_preserve_T(gens, gen_err);
    if (!gens_ok) { std::cerr << gen_err << "\n"; return 2; }

    std::unordered_map<Key,ValueRec,KeyHash> global;
    global.reserve(9000000);
    std::vector<std::string> conflicts;
    std::array<uint64_t,10> count_by_dim{}; count_by_dim.fill(0);
    std::array<std::array<uint64_t, 25>,10> hist{}; for(auto& a:hist) a.fill(0);
    std::vector<int> orbit_sizes;
    orbit_sizes.reserve(recs.size());

    for (size_t ri=0; ri<recs.size(); ++ri) {
        const CertRec& rec = recs[ri];
        Key seed = make_key_from_basis(rec.rows);
        std::unordered_set<Key,KeyHash> local;
        local.reserve(1024);
        std::deque<Key> q;
        local.insert(seed); q.push_back(seed);
        while(!q.empty()) {
            Key cur = q.front(); q.pop_front();
            for (const auto& g: gens) {
                Key nxt = transform_key_by_gen(cur,g);
                if (local.find(nxt)==local.end()) { local.insert(nxt); q.push_back(nxt); }
            }
        }
        orbit_sizes.push_back((int)local.size());
        for (const Key& k: local) {
            auto it = global.find(k);
            if (it != global.end()) {
                if (it->second.cert_index != rec.cert_index || it->second.lb != rec.lb) {
                    if (conflicts.size() < 20) {
                        std::ostringstream os; os << "key hi="<<k.hi<<" lo="<<k.lo<<" old="<<it->second.cert_index<<":"<<it->second.lb<<" new="<<rec.cert_index<<":"<<rec.lb;
                        conflicts.push_back(os.str());
                    }
                }
            } else {
                int d = key_dim(k);
                global.emplace(k, ValueRec{rec.lb, rec.cert_index, d, rec.proof_type});
                count_by_dim[d]++;
                if (rec.lb >= 0 && rec.lb < 25) hist[d][rec.lb]++;
            }
        }
        if ((ri+1)%25==0 || ri+1==recs.size()) {
            auto now=std::chrono::steady_clock::now();
            double el=std::chrono::duration<double>(now-t0).count();
            std::cerr << "expanded " << (ri+1) << "/" << recs.size() << " global=" << global.size() << " elapsed=" << el << "s\n";
        }
    }
    uint64_t expected_total=0; bool coverage_ok = true;
    for(int d=0;d<=9;d++){ expected_total += gaussian_binomial(9,d); if(count_by_dim[d] != gaussian_binomial(9,d)) coverage_ok=false; }

    std::vector<BinRec> vec; vec.reserve(global.size());
    for (const auto& kv: global) vec.push_back(BinRec{kv.first, kv.second});
    std::sort(vec.begin(), vec.end(), [](const BinRec& a, const BinRec& b){ return a.key < b.key; });
    {
        std::ofstream out(out_bin, std::ios::binary);
        if (!out) throw std::runtime_error("cannot write bin");
        const char magic[8] = {'Q','W','R','E','X','P','1','\0'};
        out.write(magic,8); write_u64(out, (uint64_t)vec.size());
        for (const auto& r: vec) {
            write_u64(out, r.key.lo); write_u64(out, r.key.hi);
            write_u16(out, (uint16_t)r.val.cert_index);
            write_u16(out, (uint16_t)r.val.lb);
            write_u8(out, (uint8_t)r.val.dim);
            write_u8(out, (uint8_t)r.val.proof_type);
        }
    }
    auto t1 = std::chrono::steady_clock::now(); double elapsed = std::chrono::duration<double>(t1-t0).count();
    std::ofstream js(out_json);
    js << "{\n";
    js << "  \"schema\": \"wang_lut_reexpand_cpp_v1\",\n";
    js << "  \"cert_path\": \"" << cert_path << "\",\n";
    js << "  \"record_count\": " << recs.size() << ",\n";
    js << "  \"generator_count\": " << gens.size() << ",\n";
    js << "  \"generators_preserve_tensor\": true,\n";
    js << "  \"a_action\": \"A -> P^T A Q^{-T}; compensating B,C maps checked on all 729 basis triples per generator; transpose checked as (A,B,C)->(A^T,C,B)\",\n";
    js << "  \"subspace_count\": " << global.size() << ",\n";
    js << "  \"expected_subspace_count\": " << expected_total << ",\n";
    js << "  \"coverage_ok\": " << (coverage_ok?"true":"false") << ",\n";
    js << "  \"conflict_count\": " << conflicts.size() << ",\n";
    js << "  \"count_by_dimension\": {";
    for(int d=0;d<=9;d++){ if(d) js << ", "; js << "\""<<d<<"\": "<<count_by_dim[d]; }
    js << "},\n";
    js << "  \"expected_by_dimension\": {";
    for(int d=0;d<=9;d++){ if(d) js << ", "; js << "\""<<d<<"\": "<<gaussian_binomial(9,d); }
    js << "},\n";
    js << "  \"lb_hist_by_dimension\": {\n";
    for(int d=0;d<=9;d++){
        js << "    \""<<d<<"\": {"; bool first=true;
        for(int lb=0;lb<25;lb++) if(hist[d][lb]) { if(!first) js << ", "; first=false; js << "\""<<lb<<"\": "<<hist[d][lb]; }
        js << "}" << (d==9?"\n":" ,\n");
    }
    js << "  },\n";
    js << "  \"orbit_sizes\": [";
    for(size_t i=0;i<orbit_sizes.size();i++){ if(i) js << ", "; js << orbit_sizes[i]; }
    js << "],\n";
    js << "  \"binary_path\": \"" << out_bin << "\",\n";
    js << "  \"elapsed_sec\": " << elapsed << ",\n";
    js << "  \"ok\": " << ((coverage_ok && conflicts.empty() && global.size()==expected_total)?"true":"false") << "\n";
    js << "}\n";
    std::cout << "{\"ok\":" << ((coverage_ok && conflicts.empty() && global.size()==expected_total)?"true":"false")
              << ",\"subspace_count\":" << global.size() << ",\"expected\":" << expected_total
              << ",\"conflict_count\":" << conflicts.size() << ",\"elapsed_sec\":" << elapsed
              << ",\"binary_path\":\"" << out_bin << "\",\"summary\":\"" << out_json << "\"}\n";
    return (coverage_ok && conflicts.empty() && global.size()==expected_total) ? 0 : 1;
}
