// Independent verification: no branch pruning, direct enumeration of optional
// free covers, all orientations of required edges.
#include <array>
#include <bit>
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>
using namespace std;
constexpr array<pair<int,int>,15> edges{{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
int pc(int x){return popcount((unsigned)x);}
int savings(const vector<int>& blocks){
 int mx=0;
 for(int choice=1;choice<(1<<(int)blocks.size());choice++){
  int all=0;
  for(int j=0;j<(int)blocks.size();j++)if(choice>>j&1)all|=blocks[j];
  mx=max(mx,pc(all)-pc(choice));
 }
 return mx;
}
int exact(int U,int V,const vector<pair<int,int>>& req){
 int best=100;
 for(int x=0;x<(1<<(int)req.size());x++){
  array<int,10> leaves{};
  for(int j=0;j<(int)req.size();j++){
   auto [a,b]=req[j];
   if(x>>j&1)swap(a,b);
   leaves[a]|=1<<b;
  }
  vector<int> u,v;
  int centers=0;
  for(int l:leaves)if(l){
   centers++;
   if(pc(l&U)>=2)u.push_back(l&U);
   if(pc(l&V)>=2)v.push_back(l&V);
  }
  int cost=(int)req.size()+centers+pc(U|V)-1-savings(u)-savings(v);
  best=min(best,cost);
 }
 return best;
}
int main(){
 int n,total;cin>>n>>total;
 array<int,10> adj{};
 for(auto [a,b]:edges){adj[a]|=1<<b;adj[b]|=1<<a;}
 vector<int> Q;
 for(int m=0;m<1024;m++){
  bool good=true;
  for(int i=0;i<10;i++)if(bool(m>>i&1)==bool(m&adj[i])){good=false;break;}
  if(good)Q.push_back(m);
 }
 if(Q.size()!=15)return 2;
 int dom=0,pairs=0,kept=0;
 map<int,pair<int,int>> H;
 for(int i=0;i<n;i++){
  int U,V,k;cin>>U>>V>>k;
  bool a=false,b=false;
  for(int q:Q){a|=bool(q&U)&&!(q&V);b|=bool(q&V)&&!(q&U);}
  if(!a||!b){dom++;pairs+=k;continue;}
  vector<pair<int,int>> R,B;
  for(auto [x,y]:edges){
   if(V>>x&1 && U>>y&1)swap(x,y);
   if((U>>x&1)&&(V>>y&1)&&(!(V&~adj[x])||!(U&~adj[y])))B.emplace_back(x,y);
   else R.emplace_back(x,y);
  }
  int val=exact(U,V,R);
  H[val].first++;H[val].second+=k;
  if(val<20){
   cout<<"survivor "<<U<<" "<<V<<" "<<val<<"\n";kept++;
   for(auto e:B){R.push_back(e);cout<<"extra "<<e.first<<" "<<e.second<<" "<<exact(U,V,R)<<"\n";R.pop_back();}
  }
 }
 cout<<"dominated "<<dom<<" "<<pairs<<" survivor orbits "<<kept<<"\n";
 for(auto [v,p]:H)cout<<v<<" "<<p.first<<" "<<p.second<<"\n";
}
