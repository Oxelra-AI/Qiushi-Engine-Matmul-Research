// Domain-propagation DFS for full-tensor Wang constraints (512-bit masks).
// WANG512 format: 8-byte magic, uint32 nrows, per-row: cap(1)+dim(1)+res(2)+mask(8*8=64 bytes).
// Points range 1..511.
//
// g++ -O3 -march=native -std=c++17 -o e11_domain_dfs_512 e11_domain_dfs_512.cpp

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <string>
#include <chrono>

static constexpr int NPTS = 511;

struct Row { uint8_t cap, dim, npts; uint16_t pts[7]; };
struct BigRow { uint8_t cap; uint16_t npts; };

static std::vector<Row> small_rows;
static std::vector<BigRow> big_rows;
static std::vector<uint16_t> big_row_pts;
static std::vector<int> big_row_offsets;
static std::vector<std::vector<int>> pt_small_rows;
static std::vector<std::vector<int>> pt_big_rows;

static uint8_t small_count[900000];
static uint8_t small_remain[900000];
static uint8_t big_count[7200000];
static bool domain[512];
static int domain_size;
static bool forbidden[512];

struct Undo { int point; };
static std::vector<Undo> undo_stack;
static std::vector<int> undo_marks;

static uint64_t dfs_calls, solutions;
static int max_depth;
static uint64_t node_counts[22];
static std::vector<std::vector<int>> solutions_head;
static int target_depth = 20;
static double time_limit = 3600.0;
static auto t_start = std::chrono::steady_clock::now();

bool load(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) return false;
    char magic[8]; fread(magic,1,8,f);
    if (memcmp(magic,"WANG512\x01",8)!=0) { fclose(f); return false; }
    uint32_t nrows; fread(&nrows,4,1,f);
    
    pt_small_rows.resize(512);
    pt_big_rows.resize(512);
    
    for (uint32_t i = 0; i < nrows; i++) {
        uint8_t cap, dim; uint16_t res;
        uint64_t mask[8];
        fread(&cap,1,1,f); fread(&dim,1,1,f); fread(&res,2,1,f);
        fread(mask,8,8,f);
        std::vector<int> pts;
        for (int w=0;w<8;w++) {
            uint64_t m=mask[w];
            while(m){int b=__builtin_ctzll(m);int p=w*64+b;if(p>=1&&p<=511)pts.push_back(p);m&=m-1;}
        }
        if (dim<=3 && pts.size()<=7) {
            Row r; r.cap=cap; r.dim=dim; r.npts=pts.size();
            for(int j=0;j<(int)pts.size();j++) r.pts[j]=pts[j];
            int idx=small_rows.size();
            small_rows.push_back(r);
            for(int p:pts) pt_small_rows[p].push_back(idx);
        } else {
            BigRow br; br.cap=cap; br.npts=pts.size();
            int idx=big_rows.size();
            big_row_offsets.push_back(big_row_pts.size());
            for(int p:pts){big_row_pts.push_back(p);pt_big_rows[p].push_back(idx);}
            big_rows.push_back(br);
        }
    }
    fclose(f);
    big_row_offsets.push_back(big_row_pts.size());
    fprintf(stderr,"Loaded %u rows: %d small, %d big\n",nrows,(int)small_rows.size(),(int)big_rows.size());
    return true;
}

bool remove_prop(int p, int needed) {
    if(!domain[p]) return true;
    domain[p]=false; domain_size--;
    undo_stack.push_back({p});
    for(int ri:pt_small_rows[p]) {
        small_remain[ri]--;
        if(small_remain[ri]<small_rows[ri].cap-small_count[ri]) return false;
    }
    return domain_size>=needed;
}

bool select_point(int p, int depth) {
    int needed=target_depth-depth-1;
    undo_marks.push_back(undo_stack.size());
    domain[p]=false; domain_size--;
    undo_stack.push_back({p});
    
    for(int ri:pt_small_rows[p]) {
        small_count[ri]++;
        if(small_count[ri]>small_rows[ri].cap) return false;
        if(small_count[ri]==small_rows[ri].cap) {
            const Row& r=small_rows[ri];
            for(int j=0;j<r.npts;j++) {
                int q=r.pts[j];
                if(domain[q]) {
                    if(!remove_prop(q,needed)) return false;
                }
            }
        }
    }
    for(int ri:pt_big_rows[p]) {
        big_count[ri]++;
        if(big_count[ri]>big_rows[ri].cap) return false;
    }
    return domain_size>=needed;
}

void undo_select(int p) {
    int mark=undo_marks.back(); undo_marks.pop_back();
    while((int)undo_stack.size()>mark) {
        int q=undo_stack.back().point; undo_stack.pop_back();
        domain[q]=true; domain_size++;
        for(int ri:pt_small_rows[q]) small_remain[ri]++;
    }
    for(int ri:pt_small_rows[p]) small_count[ri]--;
    for(int ri:pt_big_rows[p]) big_count[ri]--;
}

int selected[22];

void dfs(int depth, int min_pt) {
    dfs_calls++; node_counts[depth]++;
    if(depth>max_depth) max_depth=depth;
    if(depth==target_depth) {
        solutions++;
        if(solutions<=100) solutions_head.push_back(std::vector<int>(selected,selected+depth));
        return;
    }
    if(dfs_calls%2000000==0) {
        double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t_start).count();
        if(el>time_limit) return;
    }
    for(int p=min_pt;p<=NPTS;p++) {
        if(!domain[p]||forbidden[p]) continue;
        int avail=0;
        for(int q=p;q<=NPTS;q++) if(domain[q]&&!forbidden[q]) avail++;
        if(avail<target_depth-depth) break;
        selected[depth]=p;
        if(select_point(p,depth)) {
            dfs(depth+1,p+1);
            if(solutions>100) { undo_select(p); return; }
            double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t_start).count();
            if(el>time_limit) { undo_select(p); return; }
        }
        undo_select(p);
    }
}

int main(int argc, char** argv) {
    const char *cpath=0, *opath=0, *excl=0;
    for(int i=1;i<argc;i++) {
        if(!strcmp(argv[i],"--constraints")&&i+1<argc) cpath=argv[++i];
        else if(!strcmp(argv[i],"--output")&&i+1<argc) opath=argv[++i];
        else if(!strcmp(argv[i],"--target")&&i+1<argc) target_depth=atoi(argv[++i]);
        else if(!strcmp(argv[i],"--timeout")&&i+1<argc) time_limit=atof(argv[++i]);
        else if(!strcmp(argv[i],"--exclude")&&i+1<argc) excl=argv[++i];
    }
    if(!cpath){fprintf(stderr,"Need --constraints\n");return 1;}
    if(!load(cpath)) return 1;
    
    memset(small_count,0,sizeof(uint8_t)*small_rows.size());
    memset(big_count,0,sizeof(uint8_t)*big_rows.size());
    for(int i=0;i<(int)small_rows.size();i++) small_remain[i]=small_rows[i].npts;
    memset(domain,0,sizeof(domain));
    for(int p=1;p<=NPTS;p++) domain[p]=true;
    domain_size=NPTS;
    memset(forbidden,0,sizeof(forbidden));
    
    if(excl) {
        std::string es(excl); size_t pos=0;
        while(pos<es.size()) {
            size_t nx=es.find(',',pos); if(nx==std::string::npos)nx=es.size();
            int p=atoi(es.substr(pos,nx-pos).c_str());
            if(p>=1&&p<=511){forbidden[p]=true;}
            pos=nx+1;
        }
    }
    // Exclude non-valid points: only rank>=2 points should be in domain
    // The constraint binary already only has rank>=2 points in masks,
    // but the DFS domain includes ALL 511 points. We need to exclude rank<2.
    // Actually, rank-1 points won't appear in any constraint mask (they were filtered),
    // so they won't trigger any cap increment. But they could be selected as "free" points.
    // We must exclude them from the domain.
    // rank-1 A-functionals: exactly the 49 rank-1 3x3 binary matrices.
    // These are matrices with exactly one nonzero entry.
    // In 9-bit: bit positions 0-8, so rank-1 = single bit set OR...
    // Actually rank-1 means the 3x3 matrix has rank 1, which includes
    // more than just single-entry matrices. Let me compute them.
    int n_forbidden_rank = 0;
    for (int a = 1; a <= 511; a++) {
        int rows[3] = {0, 0, 0};
        for (int idx = 0; idx < 9; idx++)
            if ((a >> idx) & 1) { int i = idx / 3, j = idx % 3; rows[i] |= 1 << j; }
        // Compute rank
        int basis[3] = {0, 0, 0}; int r = 0;
        for (int i = 0; i < 3; i++) {
            int x = rows[i];
            for (int p = 2; p >= 0; p--) {
                if ((x >> p) & 1) {
                    if (basis[p]) x ^= basis[p];
                    else { basis[p] = x; r++; break; }
                }
            }
        }
        if (r < 2) { forbidden[a] = true; n_forbidden_rank++; }
    }
    fprintf(stderr, "Excluded %d rank<2 points\n", n_forbidden_rank);
    
    t_start=std::chrono::steady_clock::now();
    dfs(0, 1);
    double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-t_start).count();
    bool complete=elapsed<time_limit-1;
    
    FILE*out=stdout;
    if(opath){out=fopen(opath,"w");if(!out)out=stdout;}
    fprintf(out,"{\"target\":%d,\"elapsed_sec\":%.6f,\"timeout\":%s,\"complete\":%s,"
        "\"dfs_calls\":%llu,\"solutions\":%llu,\"max_depth\":%d,\"node_count_by_depth\":[",
        target_depth,elapsed,complete?"false":"true",complete?"true":"false",
        (unsigned long long)dfs_calls,(unsigned long long)solutions,max_depth);
    for(int d=0;d<=target_depth;d++){if(d)fprintf(out,",");fprintf(out,"%llu",(unsigned long long)node_counts[d]);}
    fprintf(out,"],\"solutions_head\":[");
    for(int i=0;i<(int)solutions_head.size()&&i<10;i++){
        if(i)fprintf(out,",");fprintf(out,"[");
        for(int j=0;j<(int)solutions_head[i].size();j++){if(j)fprintf(out,",");fprintf(out,"%d",solutions_head[i][j]);}
        fprintf(out,"]");
    }
    fprintf(out,"]}\n");
    if(out!=stdout){fclose(out);fprintf(stderr,"Wrote %s\n",opath);}
    fprintf(stderr,"%.1fs %llu calls %llu sols depth=%d %s\n",elapsed,(unsigned long long)dfs_calls,(unsigned long long)solutions,max_depth,complete?"complete":"timeout");
    return 0;
}
