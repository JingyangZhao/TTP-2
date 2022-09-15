#include <iostream>
#include <cstdio>
#include <algorithm>
#include <vector>
#include <ctime>

using namespace std;


////
typedef long long s64;

const int INF = 2147483647;

const int MaxN = 400;
const int MaxM = 79800;

template <class T>
inline void tension(T &a, const T &b)
{
	if (b < a)
		a = b;
}
template <class T>
inline void relax(T &a, const T &b)
{
	if (b > a)
		a = b;
}
template <class T>
inline int size(const T &a)
{
	return (int)a.size();
}

inline int getint()
{
	char c;
	while (c = getchar(), '0' > c || c > '9');

	int res = c - '0';
	while (c = getchar(), '0' <= c && c <= '9')
		res = res * 10 + c - '0';
	return res;
}

const int MaxNX = MaxN + MaxN;

struct edge
{
	int v, u, w;

	edge(){}
	edge(const int &_v, const int &_u, const int &_w)
		: v(_v), u(_u), w(_w){}
};

int N, M;
edge mat[MaxNX + 1][MaxNX + 1];

int n_matches;
s64 tot_weight;
int mate[MaxNX + 1];
int lab[MaxNX + 1];

int q_n, q[MaxN];
int fa[MaxNX + 1], col[MaxNX + 1];
int slackv[MaxNX + 1];

int n_x;
int bel[MaxNX + 1], blofrom[MaxNX + 1][MaxN + 1];
vector<int> bloch[MaxNX + 1];

inline int e_delta(const edge &e) // does not work inside blossoms
{
	return lab[e.v] + lab[e.u] - mat[e.v][e.u].w * 2;
}
inline void update_slackv(int v, int x)
{
	if (!slackv[x] || e_delta(mat[v][x]) < e_delta(mat[slackv[x]][x]))
		slackv[x] = v;
}
inline void calc_slackv(int x)
{
	slackv[x] = 0;
	for (int v = 1; v <= N; v++)
		if (mat[v][x].w > 0 && bel[v] != x && col[bel[v]] == 0)
			update_slackv(v, x);
}
inline void q_push(int x)
{
	if (x <= N)
		q[q_n++] = x;
	else
	{
		for (int i = 0; i < size(bloch[x]); i++)
			q_push(bloch[x][i]);
	}
}
inline void set_mate(int xv, int xu)
{
	mate[xv] = mat[xv][xu].u;
	if (xv > N)
	{
		edge e = mat[xv][xu];
		int xr = blofrom[xv][e.v];
		int pr = find(bloch[xv].begin(), bloch[xv].end(), xr) - bloch[xv].begin();
		if (pr % 2 == 1)
		{
			reverse(bloch[xv].begin() + 1, bloch[xv].end());
			pr = size(bloch[xv]) - pr;
		}

		for (int i = 0; i < pr; i++)
			set_mate(bloch[xv][i], bloch[xv][i ^ 1]);
		set_mate(xr, xu);

		rotate(bloch[xv].begin(), bloch[xv].begin() + pr, bloch[xv].end());
	}
}
inline void set_bel(int x, int b)
{
	bel[x] = b;
	if (x > N)
	{
		for (int i = 0; i < size(bloch[x]); i++)
			set_bel(bloch[x][i], b);
	}
}
inline void augment(int xv, int xu)
{
	while (true)
	{
		int xnu = bel[mate[xv]];
		set_mate(xv, xu);
		if (!xnu)
			return;
		set_mate(xnu, bel[fa[xnu]]);
		xv = bel[fa[xnu]], xu = xnu;
	}
}
inline int get_lca(int xv, int xu)
{
	static bool book[MaxNX + 1];
	for (int x = 1; x <= n_x; x++)
		book[x] = false;
	while (xv || xu)
	{
		if (xv)
		{
			if (book[xv])
				return xv;
			book[xv] = true;
			xv = bel[mate[xv]];
			if (xv)
				xv = bel[fa[xv]];
		}
		swap(xv, xu);
	}
	return 0;
}
inline void add_blossom(int xv, int xa, int xu)
{
	int b = N + 1;
	while (b <= n_x && bel[b])
		b++;
	if (b > n_x)
		n_x++;

	lab[b] = 0;
	col[b] = 0;

	mate[b] = mate[xa];

	bloch[b].clear();
	bloch[b].push_back(xa);
	for (int x = xv; x != xa; x = bel[fa[bel[mate[x]]]])
		bloch[b].push_back(x), bloch[b].push_back(bel[mate[x]]), q_push(bel[mate[x]]);
	reverse(bloch[b].begin() + 1, bloch[b].end());
	for (int x = xu; x != xa; x = bel[fa[bel[mate[x]]]])
		bloch[b].push_back(x), bloch[b].push_back(bel[mate[x]]), q_push(bel[mate[x]]);

	set_bel(b, b);

	for (int x = 1; x <= n_x; x++)
	{
		mat[b][x].w = mat[x][b].w = 0;
		blofrom[b][x] = 0;
	}
	for (int i = 0; i < size(bloch[b]); i++)
	{
		int xs = bloch[b][i];
		for (int x = 1; x <= n_x; x++)
			if (mat[b][x].w == 0 || e_delta(mat[xs][x]) < e_delta(mat[b][x]))
				mat[b][x] = mat[xs][x], mat[x][b] = mat[x][xs];
		for (int x = 1; x <= n_x; x++)
			if (blofrom[xs][x])
				blofrom[b][x] = xs;
	}
	calc_slackv(b);
}
inline void expand_blossom1(int b) // lab[b] == 1
{
	for (int i = 0; i < size(bloch[b]); i++)
		set_bel(bloch[b][i], bloch[b][i]);

	int xr = blofrom[b][mat[b][fa[b]].v];
	int pr = find(bloch[b].begin(), bloch[b].end(), xr) - bloch[b].begin();
	if (pr % 2 == 1)
	{
		reverse(bloch[b].begin() + 1, bloch[b].end());
		pr = size(bloch[b]) - pr;
	}

	for (int i = 0; i < pr; i += 2)
	{
		int xs = bloch[b][i], xns = bloch[b][i + 1];
		fa[xs] = mat[xns][xs].v;
		col[xs] = 1, col[xns] = 0;
		slackv[xs] = 0, calc_slackv(xns);
		q_push(xns);
	}
	col[xr] = 1;
	fa[xr] = fa[b];
	for (int i = pr + 1; i < size(bloch[b]); i++)
	{
		int xs = bloch[b][i];
		col[xs] = -1;
		calc_slackv(xs);
	}

	bel[b] = 0;
}
inline void expand_blossom_final(int b) // at the final stage
{
	for (int i = 0; i < size(bloch[b]); i++)
	{
		if (bloch[b][i] > N && lab[bloch[b][i]] == 0)
			expand_blossom_final(bloch[b][i]);
		else
			set_bel(bloch[b][i], bloch[b][i]);
	}
	bel[b] = 0;
}

inline bool on_found_edge(const edge &e)
{
	int xv = bel[e.v], xu = bel[e.u];
	if (col[xu] == -1)
	{
		int nv = bel[mate[xu]];
		fa[xu] = e.v;
		col[xu] = 1, col[nv] = 0;
		slackv[xu] = slackv[nv] = 0;
		q_push(nv);
	}
	else if (col[xu] == 0)
	{
		int xa = get_lca(xv, xu);
		if (!xa)
		{
			augment(xv, xu), augment(xu, xv);
			for (int b = N + 1; b <= n_x; b++)
				if (bel[b] == b && lab[b] == 0)
					expand_blossom_final(b);
			return true;
		}
		else
			add_blossom(xv, xa, xu);
	}
	return false;
}

bool match()
{
	for (int x = 1; x <= n_x; x++)
		col[x] = -1, slackv[x] = 0;

	q_n = 0;
	for (int x = 1; x <= n_x; x++)
		if (bel[x] == x && !mate[x])
			fa[x] = 0, col[x] = 0, slackv[x] = 0, q_push(x);
	if (q_n == 0)
		return false;

	while (true)
	{
		for (int i = 0; i < q_n; i++)
		{
			int v = q[i];
			for (int u = 1; u <= N; u++)
				if (mat[v][u].w > 0 && bel[v] != bel[u])
				{
					int d = e_delta(mat[v][u]);
					if (d == 0)
					{
						if (on_found_edge(mat[v][u]))
							return true;
					}
					else if (col[bel[u]] == -1 || col[bel[u]] == 0)
						update_slackv(v, bel[u]);
				}
		}

		int d = INF;
		for (int v = 1; v <= N; v++)
			if (col[bel[v]] == 0)
				tension(d, lab[v]);
		for (int b = N + 1; b <= n_x; b++)
			if (bel[b] == b && col[b] == 1)
				tension(d, lab[b] / 2);
		for (int x = 1; x <= n_x; x++)
			if (bel[x] == x && slackv[x])
			{
				if (col[x] == -1)
					tension(d, e_delta(mat[slackv[x]][x]));
				else if (col[x] == 0)
					tension(d, e_delta(mat[slackv[x]][x]) / 2);
			}

		for (int v = 1; v <= N; v++)
		{
			if (col[bel[v]] == 0)
				lab[v] -= d;
			else if (col[bel[v]] == 1)
				lab[v] += d;
		}
		for (int b = N + 1; b <= n_x; b++)
			if (bel[b] == b)
			{
				if (col[bel[b]] == 0)
					lab[b] += d * 2;
				else if (col[bel[b]] == 1)
					lab[b] -= d * 2;
			}

		q_n = 0;
		for (int v = 1; v <= N; v++)
			if (lab[v] == 0) // all unmatched vertices' labels are zero! cheers!
				return false;
		for (int x = 1; x <= n_x; x++)
			if (bel[x] == x && slackv[x] && bel[slackv[x]] != x && e_delta(mat[slackv[x]][x]) == 0)
			{
				if (on_found_edge(mat[slackv[x]][x]))
					return true;
			}
		for (int b = N + 1; b <= n_x; b++)
			if (bel[b] == b && col[b] == 1 && lab[b] == 0)
				expand_blossom1(b);
	}
	return false;
}

void calc_max_weight_match()
{
	for (int v = 1; v <= N; v++)
		mate[v] = 0;

	n_x = N;
	n_matches = 0;
	tot_weight = 0;

	bel[0] = 0;
	for (int v = 1; v <= N; v++)
		bel[v] = v, bloch[v].clear();
	for (int v = 1; v <= N; v++)
		for (int u = 1; u <= N; u++)
			blofrom[v][u] = v == u ? v : 0;

	int w_max = 0;
	for (int v = 1; v <= N; v++)
		for (int u = 1; u <= N; u++)
			relax(w_max, mat[v][u].w);
	for (int v = 1; v <= N; v++)
		lab[v] = w_max;

	while (match())
		n_matches++;

	for (int v = 1; v <= N; v++)
		if (mate[v] && mate[v] < v)
			tot_weight += mat[v][mate[v]].w;
}
//the above functions are related to maximum weight perfect matching

//Minimum Weight Perfect Matching(MWPM)
//INPUT: team's number n, distance matrix D 
int MWPM(int n, vector<vector<int> > &D)
{
	N = n, M = N*(N-1)/2;
	for (int v = 1; v <= N; v++)
		for (int u = 1; u <= N; u++)
			mat[v][u] = edge(v, u, 0);
	
	for(int i=1; i<=N; i++)
		for(int j=i+1; j<=N; j++)
		{
			int w = D[i][j];
			//converting MWPM to maximum weight perfect matching problem
			//by adding a big number to each edge's weight
			w = -w+1000000;
			mat[i][j].w = mat[j][i].w = w;
		}
	//maximum weight matching probelm	
	calc_max_weight_match();
	
	//return the value of MWPMM
	return N/2*1000000-tot_weight;
}

int LB(vector<vector<int> > &D, int n)
{
	int sum = 0;
	for(int i=1; i<=n; i++)
		for(int j=1; j<=n; j++)
			sum += D[i][j];
	return sum+n*MWPM(n,D);;
}
void cpy(pair<int, int> *A, pair<int, int> *B)
{
	A->first = B->first; A->second = B->second;
}
void type_right(pair<int, int> *a, pair<int, int> *b, pair<int, int> *R, int s, int f, vector<vector<int> > &day, int d)
{
	if(s==1){
		day[a->first][d] = f*R->second; day[R->second][d] = -f*a->first;	
		day[a->second][d] = f*b->second; day[b->second][d] = -f*a->second;	
		day[b->first][d] = -f*R->first; day[R->first][d] = f*b->first;
	}
	else if(s==2){
		day[a->first][d] = f*b->second; day[b->second][d] = -f*a->first;
		day[a->second][d] = f*R->first; day[R->first][d] = -f*a->second;
		day[b->first][d] = -f*R->second; day[R->second][d] = f*b->first;
	}
	else if(s==3){
		day[a->first][d] = f*b->first; day[b->first][d] = -f*a->first;
		day[a->second][d] = f*R->first; day[R->first][d] = -f*a->second;
		day[b->second][d] = -f*R->second; day[R->second][d] = f*b->second;
	}
	else if(s==4){
		day[a->first][d] = f*b->second; day[b->second][d] = -f*a->first;
		day[a->second][d] = f*R->second; day[R->second][d] = -f*a->second;
		day[b->first][d] = -f*R->first; day[R->first][d] = f*b->first;
	}
}
void type_normal(pair<int, int> *a, pair<int, int> *b, int s, int f, vector<vector<int> > &day, int d)
{
	if(s==1){
		day[a->first][d] = f*b->first; day[a->second][d] = f*b->second;
		day[b->first][d] = -f*a->first; day[b->second][d] = -f*a->second;
	}
	else if(s==-1){
		day[a->first][d] = f*b->first; day[a->second][d] = -f*b->second;
		day[b->first][d] = -f*a->first; day[b->second][d] = f*a->second;
	}
	else if(s==2){
		day[a->first][d] = f*b->second; day[a->second][d] = f*b->first;
		day[b->first][d] = -f*a->second; day[b->second][d] = -f*a->first;
	}
	else if(s==-2){
		day[a->first][d] = f*b->second; day[a->second][d] = -f*b->first;
		day[b->first][d] = f*a->second; day[b->second][d] = -f*a->first;
	}
}

void type_S(pair<int, int> &a, int f, vector<vector<int> > &day, int d)
{
	day[a.first][d] = f*a.second; day[a.second][d] = -f*a.first;
}
void type_M(pair<int, int> *a, pair<int, int> *b, int d, vector<vector<int> > &day, int f)
{
	type_normal(a,b,1,f*1,day,d); type_normal(a,b,2,f*1,day,d+1);
	type_normal(a,b,1,-f*1,day,d+2); type_normal(a,b,2,-f*1,day,d+3);
}
void type_L(pair<int, int> *a, pair<int, int> *L, int d, vector<vector<int> > &day, int f)
{
	type_normal(a,L,1,f*1,day,d); type_normal(a,L,2,-f*1,day,d+1); 
	type_normal(a,L,1,-f*1,day,d+2); type_normal(a,L,2,f*1,day,d+3);
}
void swap_u(pair<int, int> *u)
{
	int temp=u->first; u->first=u->second; u->second=temp;
}
void type_penultimate(pair<int, int> *a, pair<int, int> *b, int d, vector<vector<int> > &day, vector<vector<int> > &D, int f, int FFF)
{
	if(f==-1) type_penultimate(b,a,d,day,D,-f,FFF);
	else{
		if( FFF*(D[a->first][b->first]+D[a->first][b->second])<FFF*(D[a->second][b->first]+D[a->second][b->second]) ) swap_u(a);
		type_normal(a,b,1,f*1,day,d); type_normal(a,b,-2,FFF,day,d+1);
		type_normal(a,b,1,-f,day,d+2); type_normal(a,b,-2,-FFF*1,day,d+3);
	}
} 
void type_last(pair<int, int> *a, pair<int, int> *b, int d, vector<vector<int> > &day, int f, int FFF)
{
	
	if(f==-1) type_last(b,a,d,day,-f,FFF);
	else
	{
		type_S(*a,FFF,day,d); type_S(*a,-FFF,day,d+5);//ahha aahh hhaa haah
		type_S(*b,FFF,day,d); type_S(*b,-FFF,day,d+5);
			
		type_normal(a,b,1,f*1,day,d+1); type_normal(a,b,-2,-FFF,day,d+2);
		type_normal(a,b,1,-f,day,d+3); type_normal(a,b,-2,FFF*1,day,d+4);
	}	
}
void type_R(pair<int, int> *a, pair<int, int> *b, pair<int, int> *R, int f, int fg, int num, vector<vector<int> > &day, int d)
{
	if(fg==0)//q=(m-1)/2 
	{
		//u_{m-2}---u_1
		type_right(a,b,R,1,f*1,day,d); type_right(a,b,R,3,f*1,day,d+1);
		type_right(a,b,R,1,-f*1,day,d+2); type_right(a,b,R,3,-f*1,day,d+3);
	}
	else if(fg>0)//1<=q<=(m-3)/2
	{
		if(fg%2==1)//odd---even
		{
			type_right(a,b,R,2,f*1,day,d); type_right(a,b,R,1,f*1,day,d+1);
			type_right(a,b,R,2,-f*1,day,d+2); type_right(a,b,R,1,-f*1,day,d+3);	
		}
		else//even---odd
		{
			type_right(a,b,R,4,f*1,day,d); type_right(a,b,R,3,f*1,day,d+1);
			type_right(a,b,R,4,-f*1,day,d+2); type_right(a,b,R,3,-f*1,day,d+3);			
		}
	}
	else// (m+1)/2 <= q <= m-2
	{
		if(fg%2==-1)//even---odd
		{
			type_right(a,b,R,3,f*1,day,d); type_right(a,b,R,4,f*1,day,d+1);
			type_right(a,b,R,3,-f*1,day,d+2); type_right(a,b,R,4,-f*1,day,d+3);			
		}
		else//odd---even
		{
			type_right(a,b,R,1,f*1,day,d); type_right(a,b,R,2,f*1,day,d+1);
			type_right(a,b,R,1,-f*1,day,d+2); type_right(a,b,R,2,-f*1,day,d+3);			
		}
	}
}
void type_LR_last(pair<int, int> *a, pair<int, int> *b, int FFF, int num, vector<vector<int> > &day, int d)
{
	type_S(*a,FFF,day,d); type_S(*b,FFF,day,d);
	type_S(*a,-FFF,day,d+5); type_S(*b,-FFF,day,d+5);
	type_normal(a,b,-2,-FFF,day,d+1); type_normal(a,b,-1,-FFF,day,d+2);
	type_normal(a,b,-2,FFF,day,d+3); type_normal(a,b,-1,FFF,day,d+4);
}
void type_X1(pair<int, int> *u, int s, int f, vector<vector<int> > &day, int d, int n)
{
	 
	if(s == 1){
		day[u[1].first][d] = f*u[2].first; day[u[1].second][d] = -f*u[n/2-2].first;	
		day[u[n/2-2].first][d] = f*u[1].second; day[u[n/2-2].second][d] = f*u[n/2-3].second;	
	}
	else if(s == 2){
		day[u[1].first][d] = -f*u[n/2-2].second; day[u[1].second][d] = f*u[2].first;
		day[u[n/2-2].first][d] = -f*u[n/2-3].second; day[u[n/2-2].second][d] = f*u[1].first;
	}
}
void type_X2(pair<int, int> *u, int s, int f, vector<vector<int> > &day, int d, int n, int i)
{
	int tt=n/2-2;

	int aa=i-1, bb=i+1;
	if(s==1){
		if(i%2==1){
			day[u[i].first][d] = f*u[bb].first; day[u[i].second][d] = f*u[aa].second;
		}
		else{
			day[u[i].first][d] = -f*u[aa].first; day[u[i].second][d] = -f*u[bb].second;
		}		
	}
	else if(s == 2){
		day[u[i].first][d] = -f*u[aa].second; day[u[i].second][d] = f*u[bb].first;
	}
}

void ro(vector<int> &bb, int k){
	int temp=bb[1];
	for(int i=1; i<k; i++) bb[i]=bb[i+1]; bb[k]=temp;
}
void xxx(int s, pair<int, int> *a, pair<int, int> *b, int k, int d, vector<vector<int> > &day, vector<vector<int> > &D, 
			int f, int FFF)
{
	vector<int> aa(k+1),bb(k+1);
	for(int i=1; i<=k; i++){
		aa[i]=i; bb[i]=i;
	}
	if(s==1){
		for(int i=1; i<=k; i++,d+=4,ro(bb,k)){
			for(int j=1; j<=k; j++) type_M(&a[aa[j]],&b[bb[j]],d,day,f);
		}
	}
	else if(s==2){
		for(int i=1; i<k; i++,d+=4,ro(bb,k)){
			for(int j=1; j<=k; j++)type_M(&a[aa[j]],&b[bb[j]],d,day,f);
		}
		for(int j=1; j<=k; j++)type_L(&a[aa[j]],&b[bb[j]],d,day,f);
	}
	vector<int >().swap(aa),vector<int >().swap(bb);
}

void gene(int m, pair<int, int> *a, pair<int, int> *b, int k, int d, vector<vector<int> > &day, vector<vector<int> > &D, int f, int FFF)
{
//	int f = FFF; //a--->b
	pair<int, int> u[m/k+1][k+1];
	
	for(int i=1; i<=m/(2*k); i++)
	{
		if(i==m/(2*k))
		{
			for(int j=1; j<=k; j++){
				cpy(&u[2*i-1][j], &a[(i-1)*k+j]);
				cpy(&u[2*i][j], &b[(i-1)*k+j]);
			}
		}
		else
		{
			for(int j=1; j<=k; j++)
			{
				cpy(&u[2*i-1][j], &b[(i-1)*k+j]);
				cpy(&u[2*i][j], &a[(i-1)*k+j]);
			}
		}
	}

	m=m/k;
	for(int i=1; i<=m-1; i++)
	{
		int o = 1-i; if(o<=0) o = m-1+o;
		int ff = -f, aa, bb;
		for(int j=1; j<=(m-2)/2; j++)
		{
			aa = o+j, bb = o-j;
			aa += 2*(m-1), bb +=  2*(m-1);
			aa = aa%(m-1), bb = bb%(m-1);
			if(aa==0) aa=(m-1); if(bb==0) bb=(m-1);

			if(i<m-2) xxx(1, u[aa], u[bb], k, d, day, D, ff, FFF);
			else if(i==m-2)
			{
				if(k==1) type_penultimate(&u[aa][k], &u[bb][k], d, day, D, ff, FFF);
				else xxx(1, u[aa], u[bb], k, d, day, D, ff, FFF);	
			}
			else
			{
				if(k==1) type_last(&u[aa][k], &u[bb][k], d, day, ff, FFF);
				else{
					pair<int, int> s_a[k+1]; pair<int, int> s_b[k+1];
					for(int i=1; i<=k; i++){ cpy(&s_a[i], &u[aa][i]); cpy(&s_b[i], &u[bb][i]); }
					gene(2*k, s_a, s_b, k/2, d, day, D, ff, FFF);
				}
			}
			ff = -ff;
		}
		
		if(i==1 && m>2) xxx(1, u[o], u[m], k, d, day, D, f, FFF);
		else if(i < m-2) xxx(2, u[o], u[m], k, d, day, D, -f, FFF);
		else if(i==m-2){
			if(k==1) type_penultimate(&u[o][k], &u[m][k], d, day, D, -f, FFF);
			else xxx(2, u[o], u[m], k, d, day, D, -f, FFF);
		}
		else{
			if(k==1) type_last(&u[o][k], &u[m][k], d, day, -f, FFF);
			else{
				
				pair<int, int> s_a[k+1]; pair<int, int> s_b[k+1];
				for(int i=1; i<=k; i++){ cpy(&s_a[i], &u[o][i]); cpy(&s_b[i], &u[m][i]); }
				gene(2*k, s_a, s_b, k/2, d, day, D, -f, FFF);
			}
		}
		d += 4*k; f=-f;
	}
}

int TTP_even(pair<int, int> *u, 
				int &num, vector<vector<int> > &day, int &FFF, vector<vector<int> > &D)
{
	int m=num/2, f = FFF;
	pair<int, int> a[m/2+1], b[m/2+1];
	for(int i=1; i<=m/2; i++){ cpy(&a[i], &u[2*i-1]); cpy(&b[i], &u[2*i]); }
	//pack k super-teams as a group-team
	int k=1, d=1;
	
	if(num==32) k=4;
	else if(m%4==0) k=2;
	else k=1; 
	
	gene(m, a, b, k, d, day, D, FFF, FFF);
	return 0;				
}
int TTP_odd(pair<int, int> *u, 
				int &num, vector<vector<int> > &day, int FFF, vector<vector<int> > &D)
{
	int m=num/2;
	int f = FFF;
	//The first m-2 slot 
	for(int i=1; i<=num/2-2; i++)
	{
		//u_0 means u_{m-2}
		int o = 1-i; if(o<=0) o = num/2-2+o;
		
		int B = (num/2+1)/2-i; if(B <= 0) B = num/2-2+B;
		int A = B-1; if(A <= 0) A = num/2-2+A;
		
		//Right game with super teams u_A, u_B, u_r;;;; A=B-1
		//u_A: aahh u_B: hhaa ;;; f=1
		if(num%8==2){
			if(i < (m-1)/2) type_R(&u[A], &u[B], &u[num/2], -f, i, num, day, 4*i-3);
			else if(i == (m-1)/2) type_R(&u[A], &u[B], &u[num/2], -f, 0, num, day, 4*i-3);
			else type_R(&u[A], &u[B], &u[num/2], -f, -i, num, day, 4*i-3);
		}
		else{
			if(i < (m-1)/2) type_R(&u[A], &u[B], &u[num/2], f, i+1, num, day, 4*i-3);
			else if(i == (m-1)/2) type_R(&u[A], &u[B], &u[num/2], f, 0, num, day, 4*i-3);
			else type_R(&u[A], &u[B], &u[num/2], f, -(i+1), num, day, 4*i-3);
		}
		
		//Middle game with super teams u_aa, u_bb;;;; u_aa is above u_bb 
		int ff = f, aa, bb;
		for(int j=1; j<=(num/2-5)/2; j++)
		{
			//mod(m-2) in case that aa<=0 or aa>m-2 or bb<=0 or bb>m-2
			aa = o+j, bb = o-j;
			aa += 2*(num/2-2), bb +=  2*(num/2-2);
			aa = aa%(num/2-2), bb = bb%(num/2-2);
			if(aa==0) aa=(num/2-2); if(bb==0) bb=(num/2-2);
			
			//u_aa: aahh u_bb: hhaa ;;;; ff=1
			type_M(&u[aa], &u[bb], 4*i-3, day, -ff);
			
			//In the next slot, The direction of all arrows changes
			ff = -ff;
		}
		//Left game with super teams u_l and u_o
		//u_o: ahha ;;;; f=1
		if(i==1) type_M(&u[o], &u[num/2-1], 4*i-3, day, f);
		else if(i<m-2) type_L(&u[o], &u[num/2-1], 4*i-3, day, -f);
		else
		{
			type_normal(&u[o],&u[num/2-1],1,-f*1,day,4*i-3); type_normal(&u[o],&u[num/2-1],-2,f*1,day,4*i-2); 
			type_normal(&u[o],&u[num/2-1],1,f*1,day,4*i-1); type_normal(&u[o],&u[num/2-1],-2,-f*1,day,4*i);
		}
			
		f=-f;
	}
	
	//Games at the last time slot except self game and -self game
	//Games with Super teams u_1, u_l and u_r
	//A1+S+A2-S-A2-A1 on the day of 2n-7---2n-2
	//A1 ;;; FFF=1  
	type_X1(u, 1, FFF, day, 2*num-7, num);
	type_S(u[1],FFF,day,2*num-6); type_S(u[num/2-2],FFF,day,2*num-6);
	type_X1(u, 2, FFF, day, 2*num-5, num);
	type_X1(u, 1, -FFF, day, 2*num-4, num); 
	type_X1(u, 2, -FFF, day, 2*num-3, num);
	type_S(u[1],-FFF,day,2*num-2); type_S(u[num/2-2],-FFF,day,2*num-2);
	
	type_LR_last(&u[num/2-1],&u[num/2],FFF,num,day,2*num-7);
	
	for(int i=2; i<=num/2-3; i++)
	{	
		type_X2(u, 1, FFF, day, 2*num-7, num, i);
		type_S(u[i],FFF,day,2*num-6);
		type_X2(u, 2, FFF, day, 2*num-5, num, i);
		type_X2(u, 1, -FFF, day, 2*num-4, num, i);
		type_X2(u, 2, -FFF, day, 2*num-3, num, i);
		type_S(u[i],-FFF,day,2*num-2);
	}
	return 0;	
}

//for showing the shcedule
void show_table(vector<vector<int> > &day, int n)
{
	printf("/**************table****************/\n"); 
	for(int i=1; i<=n; i++,printf("\n"))
		for(int j=1; j<=2*n-2; j++)
			printf("%3d",day[i][j]);
}

//check for the feasibility of our schedule
int check(int n, int f_check, vector<vector<int> > &day)
{
	if(f_check)
	{
		int num = n;
		//check for whether there is a missed game  
		vector<vector<int> > c(num+1, vector<int>(num+1));
		
		for(int i=1; i<=n; i++)
			for(int j=1; j<=n; j++){
				if(i!=j) c[i][j]=200;
			}	
		for(int i=1; i<=n; i++)
		{
			for(int j=1; j<=2*n-2; j++)
			{
				if(day[i][j]>0) c[i][day[i][j]] += (-100+1);
				else if(day[i][j]<0) c[i][-day[i][j]] += (-100-1);
			}
		}
		for(int i=1; i<=n; i++)
			for(int j=1; j<=n; j++){
				if(c[i][j]!=0){
					printf("%d %d\n", i, j);
					return -1;
				}
			}
			
		//check for the condition of TTP-2: bounded-by-2
		//Our schedule obviously satisfies the condition of TTP-2: no-repeat
		for(int i=1; i<=n; i++){
			for(int d=1; d<=n*2-4; d++){
				if(day[i][d]>0 && day[i][d+1]>0 && day[i][d+2]>0)
					return -1;
				if(day[i][d]<0 && day[i][d+1]<0 && day[i][d+2]<0){
					printf("team:%d day:%d\n", i, d);
					return -1;
				}
			}
		}
		
		for(int i=1; i<=n; i++){
			for(int d=1; d<=n*2-2; d++){
				int ooop = abs(day[i][d]);
				if(abs(day[ooop][d]) != i){
					printf("%d %d\n none asy!!!\n",i,d);
					return -1;
				}
			}
		}
		vector<vector<int> > fd(n+1, vector<int>(n+1));
		for(int i=1; i<=n; i++) for(int k=1; k<=2*n-2; k++)
			if(day[i][k]>0) fd[i][day[i][k]]=1;
		for(int i=1; i<=n; i++) for(int j=1; j<=n; j++)
			if(i!=j && fd[i][j]!=1) return -1;
			
		for(int i=0; i<=n; i++) vector<int>().swap(c[i]),vector<int>().swap(fd[i]); vector<vector<int> >().swap(c),vector<vector<int> >().swap(fd);
	}
	return 0;
} 

//calculate the total distance travelled by all teams
//according the schedule: &day
int dist(int n, vector<vector<int> > &day,  vector<vector<int> > &D)
{
	int res=0;
	
	for(int i=1; i<=n; i++)
	{
		int flag=0;
		for(int d=1; d<=2*n-2; d++)
		{
			if(d==2*n-2 && flag==0 && day[i][d]>0) res += 2*D[i][day[i][d]];	

			else if(day[i][d]<0) {
				if(flag==0) continue; 
				else{
					res += D[i][day[i][d-1]];flag=0;
				}
			}
			else
			{
				if(flag==0){
					res += D[i][day[i][d]];flag=1;
				}
				else{
					res += D[i][day[i][d]]+D[day[i][d-1]][day[i][d]];flag=0;
				}
			} 		
		}
	}

	return res;
}
int ttp(int n, vector<vector<int> > &D, vector<vector<int> > &day, pair<int, int> *u, int &FFF, int f_check)
{
	//generate schedule
	if(n%4==0) TTP_even(u, n, day, FFF, D);
	else TTP_odd(u, n, day, FFF, D);
	
	//check the correctness
	if(check(n, f_check, day)==-1) {printf("err"); return INT_MAX;}
	
	//show_table(day,n);
	//calculate the distance
	int res = dist(n, day, D);
	
	return res;
}
void swap_ui(int i, pair<int, int> *u)
{
	int temp=u[i].first; u[i].first=u[i].second; u[i].second=temp;
}
void swap_uij(int i, int j, pair<int, int> *u)
{
	int t1=u[i].first, t2=u[i].second;
	u[i].first=u[j].first, u[i].second=u[j].second; u[j].first=t1, u[j].second=t2;	
}

void random_order(int n, pair<int, int> *u)
{
	//random order super-teams and swap pair of teams in each super-team
	int m=n/2; pair<int, int> u_[m+1];
	
	vector<int> list_number; 
	
	for(int i=1; i<=m; i++) list_number.push_back(i);
	
	random_shuffle(list_number.begin(), list_number.end());
	
	for(int i=1; i<=m; i++) 
	{
		u_[i].first=u[list_number[i-1]].first, u_[i].second=u[list_number[i-1]].second;
		
		int r=rand(); 
		if(r%2==0) swap_ui(i, u_);
	}
	
	for(int i=1; i<=m; i++) u[i].first=u_[i].first, u[i].second=u_[i].second;
	
	vector<int>().swap(list_number);
}

int swap_super_team(int target, int n, int FFF, int &min, pair<int, int> *u, 
						vector<vector<int> > &temp_day, vector<vector<int> > &day, vector<vector<int> > &D, int f_check)
{
	int m=n/2, opt_flag=0;
	vector<pair<int, int> > list_m;
	for(int i=1; i<=m; i++) for(int j=i+1; j<=m; j++) list_m.push_back(make_pair(i,j));
	int flag=1;
	while(flag)
	{
		random_shuffle(list_m.begin(), list_m.end());
		for(int i=0; i<list_m.size(); i++) 
		{
			swap_uij(list_m[i].first, list_m[i].second, u);
			
			int temp=ttp(n, D, temp_day, u, FFF, f_check);
			
			if(temp<min) 
			{
				min=temp,flag=2,opt_flag=1;
				//if(temp<=target) for(int i=1; i<=n; i++) for(int j=1; j<=2*n-2; j++) day[i][j]=temp_day[i][j];
			} 
			else swap_uij(list_m[i].first, list_m[i].second, u);
		} flag--;
	}
	vector<pair<int, int> >().swap(list_m);
	return opt_flag;
}

int swap_team(int target, int n, int FFF, int &min, pair<int, int> *u, 
					vector<vector<int> > &temp_day, vector<vector<int> > &day, vector<vector<int> > &D, int f_check)
{
	vector<int > list_n;
	for(int i=1; i<=n/2; i++) list_n.push_back(i);
	int flag=1, opt_flag=0;
	while(flag)
	{
		random_shuffle(list_n.begin(), list_n.end());
		for(int i=0; i<list_n.size(); i++) 
		{
			swap_ui(list_n[i], u);
			int temp=ttp(n, D, temp_day, u, FFF, f_check);
			if(temp<min) 
			{
				min=temp,flag=2,opt_flag=1; 
				//if(temp<=target) for(int i=1; i<=n; i++) for(int j=1; j<=2*n-2; j++) day[i][j]=temp_day[i][j];
			} 
			else swap_ui(list_n[i], u);
		} flag--;
	}
	vector<int >().swap(list_n);
	return opt_flag;
}

/*********************************************************************************/
void get_schedule(int target, pair<int, int> *u, vector<vector<int> > &D, int n, int FFF, int &min,
			vector<vector<int> > &day, int f_check, int opt_flag)
{
	
	vector<vector<int> > temp_day(n+1, vector<int>(2*n-2+1));
	
	//random order super-teams
	random_order(n, u);
	
    //calculate schedule
	min = ttp(n, D, day, u, FFF, f_check);
	
	if(opt_flag) swap_super_team(target, n, FFF, min, u, temp_day, day, D, f_check), swap_team(target, n, FFF, min, u, temp_day, day, D, f_check);
	
	/*
	int init_flag=1;
	while(opt_flag>0)
	{
		opt_flag=0;
		if(swap_super_team(target, n, FFF, min, u, temp_day, day, D, f_check)==0 && init_flag==0)
			break;
		opt_flag=swap_team(target, n, FFF, min, u, temp_day, day, D, f_check);
		init_flag=0;
	}
	*/
	
	for(int i=0; i<=n; i++) vector<int>().swap(temp_day[i]); vector<vector<int> >().swap(temp_day);
}

void read_D(FILE *fp, vector<vector<int> > &D, int n)
{
	if(!fp) printf("eee"),exit(0);
	for(int i=1; i<=n; i++) for(int j=1; j<=n; j++) fscanf(fp,"%d",&D[i][j]);
	fclose(fp);
}

int main()
{	
	clock_t init_time; init_time=clock();
	int FFF=1, opt=1, f_check=0;
	
	//////////////////17 instances of even n/2
	printf("even n/2:\n");
	for(int k=1; k<=8; k++) {srand(0);
		int n=40-4*(k-1); char *s = "Galaxy"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 		
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;	
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	for(int k=1; k<=5; k++) {srand(0);
		int n=32-4*(k-1); char *s = "NFL"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 		
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	
	for(int k=1; k<=2; k++){srand(0);
		int n=16-4*(k-1); char *s = "NL"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	
	for(int k=1; k<=1; k++){srand(0);
		int n=12-4*(k-1); char *s = "Super"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	
	for(int k=1; k<=1; k++){srand(0);
		int n=24-4*(k-1); char *s = "Brazil"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	
	//////////////////16 instances of odd n/2
	printf("odd n/2:\n");
	for(int k=1; k<=8; k++) {srand(0);
		int n=38-4*(k-1); char *s = "Galaxy"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 		
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;	
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	for(int k=1; k<=4; k++) {srand(0);
		int n=30-4*(k-1); char *s = "NFL"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 		
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	
	for(int k=1; k<=2; k++){srand(0);
		int n=14-4*(k-1); char *s = "NL"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	
	for(int k=1; k<=2; k++){srand(0);
		int n=14-4*(k-1); char *s = "Super"; char *buf = new char[strlen(s) + sizeof(n) + 1]; sprintf(buf, "%s%d.txt", s, n);
		FILE *fp=fopen(buf,"r"); vector<vector<int> > D(n+1,vector<int>(n+1)); read_D(fp, D, n); vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); 
		int lb=LB(D,n); pair<int, int> u[n/2+1]; for (int v = 1, f=1; v <= n; v++) if(mate[v]!=-1) u[f]=make_pair(v,mate[v]), mate[mate[v]]=-1, f++;
		int min=INT_MAX, target=0; get_schedule(target, u, D, n, FFF, min, day, f_check , opt); printf("%d\n", min);
		for(int i=0; i<=n; i++) vector<int>().swap(day[i]),vector<int>().swap(D[i]); vector<vector<int> >().swap(day),vector<vector<int> >().swap(D); delete s; delete [] buf;
	}
	printf("the total running time: %f\n", (clock()-init_time)/1000.0);
	
	
	/* the example for n=8 */
	if(0)
	{
		int n=8; pair<int, int> u[n/2+1];
		for (int i=1; i<=n/2; i++) u[i]=make_pair(2*i-1, 2*i);
		vector<vector<int> > day(n+1, vector<int>(2*n-2+1)); vector<vector<int> > D(n+1,vector<int>(n+1));
		int d=1, f=1, F=1;
		type_M(&u[2], &u[1], 4*d-3, day, 1); type_M(&u[3], &u[4], 4*d-3, day, 1);
		d++;
		type_penultimate(&u[3], &u[1], 4*d-3, day, D, 1, 1); type_penultimate(&u[2], &u[4], 4*d-3, day, D, 1, 1);
		d++;
		type_last(&u[4], &u[1], 4*d-3, day, 1, 1); type_last(&u[3], &u[2], 4*d-3, day, 1, 1);
		
		show_table(day, n);
	}
	return 0;
}
