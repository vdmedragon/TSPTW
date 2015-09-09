//#include "gurobi_c++.h"
//#include <vector>
//#include <set>
//#include <map>
//#include <sstream>
//#include <algorithm>
//
//// some changes
//
//using std::cout;
//
//using namespace std;
//
//#define MAXN 222
//struct OriginalGraph
//{
//	int N0; //number of vertices;
//	int tau[MAXN][MAXN]; //distance matrix
//	int e[MAXN], l[MAXN]; //time windows
//};
//
//#define NODE pair<int, int>
//#define S_IT set<int>::iterator 
//#define M_NODE_S_NODE_IT map<NODE, set <NODE> >::iterator
//
//struct PartialTimeExpandedGraph{
//	int N0;
//	set<int> NT[MAXN]; //for each terminal i, we associate with i set of time t that node i_t is in the set of N_T
//	map<NODE, set <NODE> > AT; //we associate with each node (i,t) in N_T, a set of nodes (j,t') associated with it; that means; the arc (i,t) - (j,t') is in A_T
//};
//
//struct VarIndex{
//	int i, t, j, t_prime;
//
//	VarIndex(int ii, int tt, int jj, int tt_prime)
//	{
//		i = ii;
//		j = jj;
//		t = tt;
//		t_prime = tt_prime;
//	}
//
//	VarIndex()
//	{
//		i = j = t = t_prime = -1;
//	}
//
//	friend bool operator < (const VarIndex &idx1, const VarIndex &idx2)
//	{
//		if (idx1.i < idx2.i)
//			return true;
//		else if (idx1.i == idx2.i)
//			if (idx1.t < idx2.t)
//				return true;
//			else if (idx1.t == idx2.t)
//				if (idx1.j < idx2.j)
//					return true;
//				else if (idx1.j == idx2.j)
//					if (idx1.t_prime < idx2.t_prime)
//						return true;
//		return false;
//	}
//};
//
//
////graph information
//OriginalGraph G;
//PartialTimeExpandedGraph PTEG;
//
////model information
//GRBEnv *env = new GRBEnv();
//GRBModel model(*env);
//
//map<VarIndex, GRBVar> x_a;
//map<string, GRBLinExpr> constraintSet;
//
//vector<VarIndex> deletedVarList;
//vector<VarIndex> addedVarList;
//vector<NODE> addedNodeList;
//
//bool subTourElimination = false;
//
////reading original graph
////http://iridia.ulb.ac.be/~manuel/tsptw-instances
//
//void readOriginalGraph(OriginalGraph &G, char *INPUT)
//{
//	freopen(INPUT, "rt", stdin);
//
//	cin >> G.N0;
//
//	double tmp;
//
//	for (int i = 0; i < G.N0; i++)
//		for (int j = 0; j < G.N0; j++)
//		{
//			cin >> tmp;
//			G.tau[i][j] = (int)(tmp);
//		}
//
//	for (int i = 0; i < G.N0; i++)
//		cin >> G.e[i] >> G.l[i];
//
//	fclose(stdin);
//}
//
//void readOriginalGraph_rfsilva(OriginalGraph &G, char *INPUT)
//{
//	freopen(INPUT, "rt", stdin);
//
//	//string stmp;
//	//std::getline(cin, stmp);
//	//std::getline(cin, stmp);
//
//	int id;
//	double x[MAXN], y[MAXN], d[MAXN], rt[MAXN], dt[MAXN], st[MAXN];
//
//	for (int i = 0;; i++)
//	{
//		cin >> id >> x[i] >> y[i] >> d[i] >> rt[i] >> dt[i] >> st[i];
//		G.e[i] = rt[i], G.l[i] = dt[i];
//		if (id == 999) {
//			G.N0 = i;
//			break;
//		}
//	}
//
//	for (int i = 0; i < G.N0; i++)
//		for (int j = i + 1; j < G.N0; j++)
//		{
//			double dist = sqrt((x[i] - x[j])*(x[i] - x[j]) + (y[i] - y[j])*(y[i] - y[j]));
//			G.tau[i][j] = G.tau[j][i] = dist;
//		}
//
//	fclose(stdin);
//}
