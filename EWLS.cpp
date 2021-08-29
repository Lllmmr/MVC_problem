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
const int maxN=800;
const int maxM=260000;

int delta;
int maxSteps;

int N,M;

int edges[2*maxM],nxt[2*maxM],head[maxN];			//head数组是每个顶点对应的第一个边的下标
													//nxt是下一条边的下标
													//edges数组对应该边连向的顶点
int oriAdjTable[maxN][maxN],adjTable[maxN][maxN];	//原始图的邻接表和补图的邻接表
													//其中，adjTable[u][v]=0是表示无边连接
													//adjTable[u][v]=k时，其数字表示对应第几条边
													//该边的两个顶点分别是edges[2*k]和edges[2*k+1]

bitset<maxN>C,ansC;									//集合C和目前最优点覆盖，C[u]=1表示该点在点覆盖中
int ub;												//最优点覆盖中点的数量

list<int>L;											//未被覆盖的边
list<int>::iterator UL;

int dscore[maxN],weight[maxM];						//记录每个顶点的dscore和每条边的weight

struct coverV{
	int u,num;
	coverV(int u_,int num_) : u(u_),num(num_){}
	bool operator<(const coverV&v)const{
		return num<v.num;
	}
};
int coverNum[maxN];
void greedy(bitset<maxN>&C){						//贪心地将C扩展成点覆盖
	priority_queue<coverV>mostCover;				//用优先队列找到当前覆盖未被覆盖的边数最多的点
	memset(coverNum, 0, sizeof(coverNum));
	for(auto it=L.begin();it!=L.end();it++){
		int e=(*it)<<1;
		int u=edges[e],v=edges[e+1];
		coverNum[u]++;
		coverNum[v]++;
	}
	for(int u=1;u<=N;u++)
		if(coverNum[u])
			mostCover.push(coverV(u,coverNum[u]));
	dbg_printf("greedy\n");
	while(!mostCover.empty()){
		coverV maxV=mostCover.top();
		mostCover.pop();
		int u=maxV.u;
		if(C[u]||maxV.num!=coverNum[u])continue;	//若该点已经被加到C里，或者覆盖数已被修改
		C[u]=1;
		dbg_printf("%d ",u);
		for(int e=head[u];e;e=nxt[e]){				//修改邻接点的覆盖数
			int v=edges[e];
			if(C[v])continue;
			if(--coverNum[v])
				mostCover.push(coverV(v,coverNum[v]));
		}
	}
	dbg_printf("\n");
}

void add(int u){									//将结点u加入到C中
	C[u]=1;
	dscore[u]=-dscore[u];							//加入到C后，dscore值为原来的相反数
	for(int e=head[u];e;e=nxt[e]){
		int v=edges[e],eNum=e>>1;
		if(!C[v]){									//改变邻接点的dscore
			dscore[v]-=weight[eNum];
			auto removeL=find(L.begin(),L.end(),eNum);	//把这条边从L中删除
			if(removeL==UL)UL++;						//若删除的边就是UL，则需要将其后移，否则会造成错误
			L.erase(removeL);
		}
		else dscore[v]+=weight[eNum];
	}
	dbg_printf("add:%d\n",u);
}
void remove(int u){
	C[u]=0;											//将结点u移出C
	dscore[u]=-dscore[u];							//移出C后，dscore为原来的相反数
	for(int e=head[u];e;e=nxt[e]){
		int v=edges[e],eNum=e>>1;
		if(C[v])									//改变邻接点的dscore
			dscore[v]-=weight[eNum];
		else{
			dscore[v]+=weight[eNum];
			L.push_back(eNum);						//将该边加入L
		}
	}
	dbg_printf("remove:%d\n",u);
}

struct dscoreV{
	int u,dscorenum;
	dscoreV(int u_,int dscorenum_):u(u_),dscorenum(dscorenum_){}
	bool operator<(const dscoreV&v)const{
		return dscorenum<v.dscorenum;
	}
};
void removeSome(){
	priority_queue<dscoreV>maxDscore;				//用优先队列寻找当前dscore最大的结点
	for(int i=1;i<=N;i++)
		if(C[i])
			maxDscore.push(dscoreV(i,dscore[i]));
	int remainNum=C.count();
	dbg_printf("removeSome:\n");
	while(remainNum!=ub-delta&&!maxDscore.empty()){	//将结点数减少到ub-delta(要注意判断队列是否为空，可以减少的节点数有可能不够)
		dscoreV maxV=maxDscore.top();
		maxDscore.pop();
		int u=maxV.u;
		if(!C[u]||maxV.dscorenum!=dscore[u])continue;//若该点已经被删除，或者dscore被改变
		remainNum--;
		C[u]=0;
		dbg_printf("%d ",u);
		dscore[u]=-dscore[u];
		for(int e=head[u];e;e=nxt[e]){
			int v=edges[e],eNum=e>>1;
			if(C[v]){
				dscore[v]-=weight[eNum];
				maxDscore.push(dscoreV(v,dscore[v]));
			}
			else{
				dscore[v]+=weight[eNum];
				L.push_back(eNum);
			}
		}
	}
	dbg_printf("\n");
}


int S[maxN*maxN][2];
int SSize;
int tabuAdd,tabuRemove;
void getS(int v){									//得到S
	if(v==tabuAdd)return;							//判断v是不是刚刚移出的点
	dbg_printf("S:%d\n",v);
	for(int u=1;u<=N;u++){
		if(u==v||!C[u]||u==tabuRemove)continue;		//判断u是不是刚刚加进来的点
		else{
			int score=dscore[u]+dscore[v];
			int e=adjTable[u][v];
			if(e)
				score+=weight[e];
			if(score>0){
				dbg_printf("%d ",u);
				S[SSize][0]=u;
				S[SSize++][1]=v;
			}
		}
	}
	dbg_printf("\n");
}
void chooseOne(int&chosenU,int&chosenV){			//从S中随机选取一个
	int chosen=rand()%SSize;						
	chosenU=S[chosen][0];
	chosenV=S[chosen][1];
}
void chooseExchangePair(int &chosenU,int &chosenV){
	dbg_printf("chooseExchangePair\n");
	int e=L.front()<<1;								//先看开头第一个
	int u=edges[e],v=edges[e+1];
	SSize=0;
	getS(u);
	getS(v);
	if(SSize){
		chooseOne(chosenU,chosenV);
		return;
	}
	for(;UL!=L.end();UL++){							//再从UL开始看(UL之后都是还没看过的)
		int e=(*UL)<<1;
		int u=edges[e],v=edges[e+1];
		SSize=0;
		getS(u);
		getS(v);
		if(SSize){
			chooseOne(chosenU,chosenV);
			return;
		}
	}
}
void init(){										//初始化
	memset(dscore,0,sizeof(dscore));
	tabuAdd=tabuRemove=0;
	C.reset();
	L.clear();
	for(int i=1;i<=M;i++)
		L.push_back(i);
	greedy(C);										//贪心地得到C
	L.clear();
	ub=C.count();
	ansC=C;
	for(int i=1,e=2;i<=M;i++,e+=2){
		weight[i]=1;
		int u=edges[e],v=edges[e+1];
		if(C[u]&&!C[v])
			dscore[u]-=1;
		else if(C[v]&&!C[u])
			dscore[v]-=1;
	}
	removeSome();
	UL=L.begin();
	dbg_printf("init\n");
}
void EWLS(){
	init();
	for(int step=0;step<maxSteps;step++){
		if(!L.empty()&&C.count()){					//存在可以交换的点对
			int u=0,v=0;
			chooseExchangePair(u,v);
			if(!u){									//若没有找到，随机挑选一对
				dbg_printf("randomChoose:\n");
				int chosen=rand()%L.size();
				int chosenone;
				for(auto it=L.begin();it!=L.end();it++,chosen--){
					int e=*it;
					weight[e]++;
					e<<=1;
					int uu=edges[e],vv=edges[e+1];
					dscore[uu]++;
					dscore[vv]++;
					if(chosen==0)
						chosenone=*it;
				}
				int e=chosenone<<1;
				e+=rand()%2;
				v=edges[e];
				do{
					u=(rand()%N)+1;
				}while(!C[u]);
			}
			dbg_printf("Choose:%d %d\n",u,v);
			remove(u);
			add(v);
		}
		int curSize=C.count()+L.size();
		if(curSize<ub){							//比当前最优解好，更新最优解
			ub=curSize;
			ansC=C;
			greedy(ansC);						//贪心地扩张得到当前最优解答案
			removeSome();
		}
	}
}

int main(){
	srand(time(NULL));
	while(scanf("%d%d",&N,&M)!=EOF){
		maxSteps=4000*N;
		delta=1;
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
		EWLS();
		printf("%lld\n",N-ansC.count());
		for(int i=1;i<=N;i++)
			if(!ansC[i])
				printf("%d ",i);
		printf("\n");
	}
	return 0;
}