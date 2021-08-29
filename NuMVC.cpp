#include<iostream>
#include<algorithm>
#include<cstring>
#include<bitset>
#include<queue>
#include<vector>
#include<list>
#include<ctime>

#ifdef DEBUG
	#define dbg_printf(...) printf(__VA_ARGS__)
#else
	#define dbg_printf(...)
#endif

using namespace std;
const int maxN=751;
const int maxM=250100;
const int INF=1<<30;

int gamaSum;
double rou=0.3;
int maxSteps;

int N,M;

int edges[2*maxM],nxt[2*maxM],head[maxN];
int oriAdjTable[maxN][maxN],adjTable[maxN][maxN];
bitset<maxN>C,ansC,confChange;

list<int>L;

int dscore[maxN],weight[maxM],old[maxN];
int weightSum;

struct coverV{
	int u,num;
	coverV(int u_,int num_) : u(u_),num(num_){}
	bool operator<(const coverV&v)const{
		return num<v.num;
	}
};
int coverNum[maxN];
void greedy(bitset<maxN>&C){
	priority_queue<coverV>mostCover;
	memset(coverNum, 0, sizeof(coverNum));
	for(int i=1,e=2;i<=M;i++,e+=2){
		coverNum[edges[e]]++;
		coverNum[edges[e+1]]++;
	}
	for(int u=1;u<=N;u++)
		if(coverNum[u])
			mostCover.push(coverV(u,coverNum[u]));
	dbg_printf("greedy\n");
	while(!mostCover.empty()){
		coverV maxV=mostCover.top();
		mostCover.pop();
		int u=maxV.u;
		if(C[u]||maxV.num!=coverNum[u])continue;
		C[u]=1;
		dbg_printf("%d ",u);
		for(int e=head[u];e;e=nxt[e]){
			int v=edges[e];
			if(C[v])continue;
			if(--coverNum[v])
				mostCover.push(coverV(v,coverNum[v]));
		}
	}
	dbg_printf("\n");
}
void add(int u,int step){
	C[u]=1;
	old[u]=step;
	dscore[u]=-dscore[u];
	for(int e=head[u];e;e=nxt[e]){
		int v=edges[e],eNum=e>>1;
		confChange[v]=1;
		if(!C[v]){
			dscore[v]-=weight[eNum];
			auto removeL=find(L.begin(),L.end(),eNum);
			L.erase(removeL);
		}
		else dscore[v]+=weight[eNum];
	}
	dbg_printf("add:%d\n",u);
}
void remove(int u,int step){
	C[u]=0;
	confChange[u]=0;
	old[u]=step;
	dscore[u]=-dscore[u];
	for(int e=head[u];e;e=nxt[e]){
		int v=edges[e],eNum=e>>1;
		confChange[v]=1;
		if(C[v])
			dscore[v]-=weight[eNum];
		else{
			dscore[v]+=weight[eNum];
			L.push_back(eNum);
		}
	}
	dbg_printf("remove:%d\n",u);
}
void removeHighest(int step){
	int u=0,maxDscore=-INF;
	if(C.count()<=1)return;
	for(int i=1;i<=N;i++){
		if(C[i]&&(dscore[i]>maxDscore||(dscore[i]==maxDscore&&old[i]<old[u]))){
			u=i;
			maxDscore=dscore[i];
		}
	}
	remove(u,step);
}
void init(){
	memset(dscore,0,sizeof(dscore));
	C.reset();
	L.clear();
	confChange.set();
	memset(old,0,sizeof(old));
	weightSum=M;
	greedy(C);
	ansC=C;
	for(int i=1,e=2;i<=M;i++,e+=2){
		weight[i]=1;
		int u=edges[e],v=edges[e+1];
		if(C[u]&&!C[v])
			dscore[u]-=1;
		else if(C[v]&&!C[u])
			dscore[v]-=1;
	}
	dbg_printf("init\n");
}
void NuMVC(){
	init();
	for(int step=0;step<maxSteps;step++){
		if(L.empty()){
			ansC=C;
			removeHighest(step);
			continue;
		}
		removeHighest(step);
		int chosen=rand()%L.size();
		auto it=L.begin();
		while(chosen--)it++;
		int e=(*it)<<1;
		int v;
		int v1=edges[e],v2=edges[e+1];
		if(confChange[v1]&&!confChange[v2])v=v1;
		else if(confChange[v2]&&confChange[v1])v=v2;
		else if(dscore[v1]==dscore[v2])v=old[v1]<old[v2]?v1:v2;
		else v=dscore[v1]>dscore[v2]?v1:v2;
		add(v,step);
		weightSum+=L.size();
		for(auto it=L.begin();it!=L.end();it++){
			int e=*it;
			weight[e]++;
			e<<=1;
			dscore[edges[e]]++;
			dscore[edges[e+1]]++;
		}
		if(weightSum>=gamaSum){
			for(int i=1,e=2;i<=M;i++,e+=2){
				int dweight=weight[i];
				weight[i]=(weight[i]*10/3);
				dweight-=weight[i];
				weightSum-=dweight;
				int uu=edges[e],vv=edges[e+1];
				if(!C[uu]&&!C[vv]){
					dscore[uu]-=dweight;
					dscore[vv]-=dweight;
				}else if(C[uu]&&!C[vv])dscore[uu]+=dweight;
				else if(!C[uu]&&C[vv])dscore[vv]+=dweight;
			}
		}
	}
}
int main(){
	srand(time(NULL));
	while(scanf("%d%d",&N,&M)!=EOF){
		memset(head,0,sizeof(head));
		memset(oriAdjTable,0,sizeof(oriAdjTable));
		memset(adjTable,0,sizeof(adjTable));
		for(int i=1;i<=M;i++){
			int u,v;
			scanf("%d%d",&u,&v);
			oriAdjTable[u][v]=1;
			oriAdjTable[v][u]=1;
		}
		int tote=2;
		for(int u=1;u<N;u++)
			for(int v=u+1;v<=N;v++){
				if(!oriAdjTable[u][v]){
					adjTable[u][v]=adjTable[v][u]=tote>>1;
					edges[tote]=v;
					nxt[tote]=head[u];
					head[u]=tote++;
					edges[tote]=u;
					nxt[tote]=head[v];
					head[v]=tote++;
				}
			}
		M=tote/2-1;
		maxSteps=1000*N;
		gamaSum=N*M/2;
		NuMVC();
		printf("%lld\n",N-ansC.count());
		for(int i=1;i<=N;i++)
			if(!ansC[i])
				printf("%d ",i);
		printf("\n");
	}
	return 0;
}