// Prefix-capable native DFS for E11 Wang constraints.
//
// Enumerates distinct supports of given target size with a sorted forced prefix.
// This is used for multiset cases: if repeated directions D have one extra copy,
// subtract D from caps in the input file and force D into the distinct support.

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

struct Constraint{uint8_t cap,dim;uint16_t res;uint64_t word[4];};
struct Result{double elapsed=0;bool timeout=false,complete=false,prefix_valid=true;int target=19,max_depth=0;uint64_t calls=0,tests=0,viol=0,solutions=0;std::array<uint64_t,20> node{};std::vector<int> prefix;std::vector<std::vector<int>> head;};
static bool bit4(const uint64_t w[4],int p){return (w[p>>6]>>(p&63))&1ULL;}
static bool load(const std::string&p,std::vector<Constraint>&r){std::ifstream in(p,std::ios::binary);if(!in){std::cerr<<"open fail "<<p<<"\n";return false;}char m[8];in.read(m,8);if(std::memcmp(m,"E11WANG1",8)){std::cerr<<"bad magic\n";return false;}uint32_t n;in.read((char*)&n,4);r.resize(n);for(uint32_t i=0;i<n;i++){in.read((char*)&r[i].cap,1);in.read((char*)&r[i].dim,1);in.read((char*)&r[i].res,2);for(int j=0;j<4;j++)in.read((char*)&r[i].word[j],8);}return bool(in);} 
static std::vector<std::vector<uint32_t>> point_rows(const std::vector<Constraint>&rows){std::vector<std::vector<uint32_t>>pr(256);for(uint32_t i=0;i<rows.size();i++)for(int p=1;p<=255;p++)if(bit4(rows[i].word,p))pr[p].push_back(i);return pr;}
static std::string arrj(const std::array<uint64_t,20>&a){std::ostringstream o;o<<"[";for(int i=0;i<20;i++){if(i)o<<",";o<<a[i];}o<<"]";return o.str();}
static std::string vecj(const std::vector<int>&v){std::ostringstream o;o<<"[";for(size_t i=0;i<v.size();i++){if(i)o<<",";o<<v[i];}o<<"]";return o.str();}
struct Search{const std::vector<Constraint>&rows;const std::vector<std::vector<uint32_t>>&pr;int target;double limit;std::chrono::steady_clock::time_point st;std::vector<uint8_t>cnt;std::vector<int>chosen;Result res;Search(const std::vector<Constraint>&r,const std::vector<std::vector<uint32_t>>&p,int t,double l):rows(r),pr(p),target(t),limit(l),cnt(r.size(),0){}
 bool timed(){return limit>0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count()>=limit;}
 bool add(int q,size_t&touched){const auto&L=pr[q];touched=0;res.tests++;for(size_t i=0;i<L.size();i++){uint32_t ri=L[i];uint8_t nv=cnt[ri]+1;cnt[ri]=nv;touched=i+1;if(nv>rows[ri].cap){res.viol++;return false;}}return true;}
 void undo(int q,size_t touched){const auto&L=pr[q];for(size_t i=0;i<touched;i++)cnt[L[i]]--;}
 void dfs(int minq,int depth){if(res.timeout)return;if((res.calls++&0x3FFFULL)==0&&timed()){res.timeout=true;return;}if(depth>res.max_depth)res.max_depth=depth;if(depth==target){res.solutions++;if(res.head.size()<5)res.head.push_back(chosen);return;}int rem=target-depth;for(int q=minq;q<=255;q++){if(256-q<rem)break;size_t touched=0;bool ok=add(q,touched);if(ok){res.node[depth+1]++;chosen.push_back(q);dfs(q+1,depth+1);chosen.pop_back();}undo(q,touched);if(res.timeout)return;}}
 Result run(std::vector<int> prefix){res=Result();res.node.fill(0);res.node[0]=1;res.target=target;res.prefix=prefix;std::fill(cnt.begin(),cnt.end(),0);chosen.clear();st=std::chrono::steady_clock::now();std::sort(prefix.begin(),prefix.end());if(std::unique(prefix.begin(),prefix.end())!=prefix.end())res.prefix_valid=false;std::vector<std::pair<int,size_t>> touched;int last=0;if(res.prefix_valid){for(size_t i=0;i<prefix.size();i++){int q=prefix[i];if(q<=last||q<1||q>255){res.prefix_valid=false;break;}size_t t=0;bool ok=add(q,t);touched.push_back({q,t});if(!ok){res.prefix_valid=false;break;}chosen.push_back(q);res.node[i+1]=1;last=q;}}
 if(res.prefix_valid && (int)prefix.size()<=target) dfs(last+1,(int)prefix.size());for(auto it=touched.rbegin();it!=touched.rend();++it)undo(it->first,it->second);res.elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count();res.complete=!res.timeout;return res;}};
static std::string rj(const Result&r){std::ostringstream o;o<<"{\"elapsed_sec\":"<<std::fixed<<std::setprecision(6)<<r.elapsed<<",\"timeout\":"<<(r.timeout?"true":"false")<<",\"complete\":"<<(r.complete?"true":"false")<<",\"prefix_valid\":"<<(r.prefix_valid?"true":"false")<<",\"target_depth\":"<<r.target<<",\"prefix\":"<<vecj(r.prefix)<<",\"calls\":"<<r.calls<<",\"candidate_tests\":"<<r.tests<<",\"candidate_violations\":"<<r.viol<<",\"max_depth\":"<<r.max_depth<<",\"solutions\":"<<r.solutions<<",\"node_count_by_depth\":"<<arrj(r.node)<<",\"solutions_head\":[";for(size_t i=0;i<r.head.size();i++){if(i)o<<",";o<<vecj(r.head[i]);}o<<"]}";return o.str();}
int main(int argc,char**argv){std::string cons,outp;int target=19;double lim=60;std::vector<int>prefix;for(int i=1;i<argc;i++){std::string a=argv[i];if(a=="--constraints"&&i+1<argc)cons=argv[++i];else if(a=="--out"&&i+1<argc)outp=argv[++i];else if(a=="--target-depth"&&i+1<argc)target=std::stoi(argv[++i]);else if(a=="--time-limit"&&i+1<argc)lim=std::stod(argv[++i]);else if(a=="--prefix"&&i+1<argc){std::stringstream ss(argv[++i]);std::string tok;while(std::getline(ss,tok,','))if(!tok.empty())prefix.push_back(std::stoi(tok));}else{std::cerr<<"bad arg "<<a<<"\n";return 2;}}if(cons.empty()||outp.empty()){std::cerr<<"need --constraints and --out\n";return 2;}std::vector<Constraint>rows;if(!load(cons,rows))return 1;auto pr=point_rows(rows);std::cerr<<"Loaded "<<rows.size()<<" constraints; prefix="<<vecj(prefix)<<" target="<<target<<"\n";Search S(rows,pr,target,lim);auto r=S.run(prefix);std::cout<<rj(r)<<"\n";std::ofstream out(outp);out<<"{\n  \"status\": \"ok\",\n  \"constraints_path\": \""<<cons<<"\",\n  \"constraint_count\": "<<rows.size()<<",\n  \"result\": "<<rj(r)<<"\n}\n";std::cerr<<"Wrote "<<outp<<"\n";return 0;}
