
//http://stackoverflow.com/questions/10046485/error-lnk2005-already-defined

#ifndef MY_TSPTW
#define MY_TSPTW

#include "gurobi_c++.h"
#include <vector>
#include <set>
#include <map>
#include <sstream>
#include <algorithm>
#include <cmath>
#include <cstring>

using std::cout;

using namespace std;

#define MAXN 222

#define DEBUGLINE 8

namespace
{

	struct OriginalGraph
	{
		int N0; //number of vertices;
		int tau[MAXN][MAXN]; //distance matrix
		double rtau[MAXN][MAXN];
		int e[MAXN], l[MAXN]; //time windows
		int ee[MAXN], ll[MAXN]; 
		int p[MAXN];
		int pred[MAXN][MAXN];
	};

	#define NODE pair<int, int>
	#define S_IT set<int>::iterator 
	#define M_NODE_S_NODE_IT map<NODE, set <NODE> >::iterator

	set< int > usedArcs;
	int nbIters = 0;
	bool globalChange;
	bool changeVarType = false;
	bool MIP = false;
	set<pair<int, int> > allSubTour;

	struct PartialTimeExpandedGraph{
		int N0;
		set<int> NT[MAXN]; //for each terminal i, we associate with i set of time t that node i_t is in the set of N_T
		map<NODE, set <NODE> > AT; //we associate with each node (i,t) in N_T, a set of nodes (j,t') associated with it; that means; the arc (i,t) - (j,t') is in A_T
	};

	//graph information
	OriginalGraph G;
	PartialTimeExpandedGraph PTEG;
	
	bool DEBUG = false;

	struct VarIndex{
		int i, t, j, t_prime;

		VarIndex(int ii, int tt, int jj, int tt_prime)
		{
			i = ii;
			j = jj;
			t = tt;
			t_prime = tt_prime;
		}

		VarIndex()
		{
			i = j = t = t_prime = -1;
		}

		friend bool operator < (const VarIndex &idx1, const VarIndex &idx2)
		{
			if (idx1.i < idx2.i)
				return true;
			else if (idx1.i == idx2.i)
				if (idx1.t < idx2.t)
					return true;
				else if (idx1.t == idx2.t)
					if (idx1.j < idx2.j)
						return true;
					else if (idx1.j == idx2.j)
						if (idx1.t_prime < idx2.t_prime)
							return true;
			return false;
		}

		friend ostream& operator << (ostream &out, VarIndex arc)
		{
			out << "(" << arc.i << ',' << arc.t << ")-(" << arc.j << "," << arc.t_prime << ")";
			return out;
		}
	};
	/**********************************************************Display function******************************************************************/
	void printAddedNodeList(set<NODE> &addedNodeList)
	{
		for (set<NODE>::iterator it = addedNodeList.begin(); it != addedNodeList.end(); it++)
			cout << "(" << (*it).first << "," << (*it).second << ")," << endl;
	}

	void printAddedArcsList(set<VarIndex> &addedArcsList)
	{
		for (set<VarIndex>::iterator it = addedArcsList.begin(); it != addedArcsList.end(); it++)
			cout << "(" << it->i << "," << it->t << ")-(" << it->j << "," << it->t_prime << ")," << endl;
	}
	
	void printRemovedArcsList(set<VarIndex> &removedArcsList)
	{
		for (set<VarIndex>::iterator it = removedArcsList.begin(); it != removedArcsList.end(); it++)
			cout << "(" << it->i << "," << it->t << ")-(" << it->j << "," << it->t_prime << ")," << endl;
	}
	/**********************************************************Comparison functions******************************************************************/
	inline bool varIndexCmp(const VarIndex &a, const VarIndex &b)
	{
		return (a.i < b.i || (a.i == b.i && a.t < b.t));
	}

	inline bool orderedbyTime(const VarIndex &a, const VarIndex &b)
	{
		return (a.t < b.t || (a.t == b.t && a.i<b.i));
	}

	inline bool orderedbyTimeNode(const NODE &a, const NODE &b)
	{
		return (a.second < b.second);
	}

	inline bool isTheSameArc(const VarIndex &a, const VarIndex &b)
	{
		return (a.i == b.i && a.t == b.t && a.j == b.j && a.t_prime == b.t_prime);
	}

	inline bool isValidArc(const VarIndex &a)
	{
		return (a.t >= G.e[a.i] && a.t <= G.l[a.i] && a.t_prime >= G.e[a.j] && a.t_prime <= G.l[a.j]);
	}

	inline bool tooLate(const VarIndex &a)
	{
		return (a.t_prime > G.l[a.j]);
	}

	void addNodeArcToModel(OriginalGraph &G, PartialTimeExpandedGraph &PTEG, set<VarIndex> &deletedVarList, set<VarIndex> &addedVarList, set<NODE> &addedNodeList);
	/**********************************************************Global variable information section******************************************************************/

	//model and variable decleration 
	GRBEnv *env = new GRBEnv();
	GRBModel model(*env);

	map<VarIndex, GRBVar> x_a;
	map<string, GRBLinExpr> constraintSet;
	map<string, GRBLinExpr> constraintSetST;

	set<VarIndex> deletedVarList;
	set<VarIndex> addedVarList;
	set<NODE> addedNodeList;

	set<VarIndex> newArcs;
	
	map<VarIndex, string> newArcNames;

	vector<double> arcValues;

	bool subTourElimination = false;

	struct varInfo
	{
		double val;
		VarIndex arc;
		int id;
	};

	inline bool cmpVarInfo(const varInfo &a, const varInfo &b)
	{
		return (a.val < b.val);
	}

	/**********************************************************Utility functions******************************************************************/

	//reading original graph
	//http://iridia.ulb.ac.be/~manuel/tsptw-instances

	void readOriginalGraph(OriginalGraph &G, char *INPUT)
	{
		freopen(INPUT, "rt", stdin);

		cin >> G.N0;

		double tmp;

		for (int i = 0; i < G.N0; i++)
			for (int j = 0; j < G.N0; j++)
			{
				cin >> tmp;
				G.tau[i][j] = (int)(tmp);
			}

		for (int i = 0; i < G.N0; i++)
			cin >> G.e[i] >> G.l[i];

		fclose(stdin);
	}

	void readOriginalGraph_Ascheuer(OriginalGraph &G, char *INPUT)
	{
		freopen(INPUT, "rt", stdin);
		cin >> G.N0;
		for (int i = 0; i < G.N0; i++)
			for (int j = 0; j < G.N0; j++)
			{
				double distance;
				cin >> distance;
				G.tau[i][j] = G.rtau[i][j] = distance;
				if (i!=j) G.tau[i][j] = max(1, G.tau[i][j]);
			}
		for (int i = 0; i < G.N0; i++)
			cin >> G.e[i] >> G.l[i];

		for (int i = 1; i < G.N0; i++)
		{
			G.e[i] = max(G.e[i], G.tau[0][i]);
			G.ee[i] = G.e[i];
			G.ll[i] = G.l[i];
			G.p[i] = i;
		}

		for (int i = 0; i < G.N0; i++)
		{
			int p = i;
			for (int j = i + 1; j < G.N0; j++)
				if (G.ee[j] < G.ee[p])
					p = j;

			if (p != i)
				swap(G.ee[i], G.ee[p]), swap(G.ll[i], G.ll[p]);
		}
	}

	void readOriginalGraph_rfsilva(OriginalGraph &G, char *INPUT)
	{
		freopen(INPUT, "rt", stdin);

		//string stmp;
		//std::getline(cin, stmp);
		//std::getline(cin, stmp);

		int id;
		double x[MAXN], y[MAXN], d[MAXN], rt[MAXN], dt[MAXN], st[MAXN];

		for (int i = 0;; i++)
		{
			cin >> id >> x[i] >> y[i] >> d[i] >> rt[i] >> dt[i] >> st[i];
			G.e[i] = rt[i], G.l[i] = dt[i];
			if (id == 999) {
				G.N0 = i;
				break;
			}
		}

		for (int i = 0; i < G.N0; i++)
			for (int j = i + 1; j < G.N0; j++)
			{
				double dist = sqrt((x[i] - x[j])*(x[i] - x[j]) + (y[i] - y[j])*(y[i] - y[j]));
				G.tau[i][j] = G.tau[j][i] = G.rtau[i][j]=G.rtau[j][i]=dist;
			}

		for (int i = 1; i < G.N0; i++)
			G.e[i] = max(G.e[i], G.tau[0][i]);

		fclose(stdin);
	}

	void testReadingGraph(OriginalGraph &G)
	{
		cout << "Number of terminal: " << G.N0 << endl;

		for (int i = 0; i < G.N0; i++)
		{
			for (int j = 0; j < G.N0; j++)
				cout << G.tau[i][j] << " ";
			cout << endl;
		}
		cout << "Time windows" << endl;
		for (int i = 0; i < G.N0; i++)
			cout << i+1<<":"<<G.e[i] << " " << G.l[i] << endl;
	}


	/**********************************************************Algorithmic functions******************************************************************/

	//Algorithm 2: Create initial graph 
	void CreateInitialParitalGraph(OriginalGraph &G, //original graph
		PartialTimeExpandedGraph &PTEG //initial partially time-expanded graph
		)
	{
		//list of nodes in the partial graph
		for (int i = 0; i < G.N0; i++)
		{
		 	if (i!=0) PTEG.NT[i].insert(0);
			PTEG.NT[i].insert(G.e[i]);
			PTEG.NT[i].insert(G.l[i]);
		}

		//adding arcs, 
		for (int i = 0; i < G.N0; i++) //all terminals
			for (S_IT t_it = PTEG.NT[i].begin(); t_it != PTEG.NT[i].end(); t_it++) //all time points associated with each terminal
			
			{
				int t = *t_it;
				NODE source = make_pair(i, t); //current vertex s

				//add crossing arcs
				for (int j = 0; j < G.N0; j++)
					{
						if (i == j) continue;

						
						//find largest t' such that (j,t') in N_T and t' - t \leq \tau_{ij} - nghia la co canh noi duoc 2 dinh nay
						int tau_ij = G.tau[i][j];

						if (t + tau_ij > G.l[j]) continue; //do not consider this arc because it violates time window constraint

						S_IT loc = PTEG.NT[j].upper_bound(t + tau_ij);
						loc--;
						int t_prime = *loc;

						NODE dest = make_pair(j, t_prime); //next vertex
						

						PTEG.AT[source].insert(dest); //add an arc from source to dest -

					}
				//add a new holding arc

				S_IT next = t_it; next++;

				if (next != PTEG.NT[i].end())
				{
					int t_prime = *next;

					assert(t != t_prime);

					NODE dest = make_pair(i, t_prime);
					PTEG.AT[source].insert(dest); //holding arc
				}
			}
	}

	void CreateInitialParitalGraphWithOutZero(OriginalGraph &G, //original graph
		PartialTimeExpandedGraph &PTEG //initial partially time-expanded graph
		)
	{
		//list of nodes in the partial graph
		for (int i = 0; i < G.N0; i++)
		{
			//PTEG.NT[i].insert(0); 
			PTEG.NT[i].insert(G.e[i]);
			PTEG.NT[i].insert(G.l[i]);
		}

		//adding arcs, 
		for (int i = 0; i < G.N0; i++) //all terminals
			for (S_IT t_it = PTEG.NT[i].begin(); t_it != PTEG.NT[i].end(); t_it++) //all time points associated with each terminal

			{
				int t = *t_it;
				NODE source = make_pair(i, t); //current vertex s
				
				if (DEBUG)
					cout << "Creating arcs for node : (" << i << "," << t << ")" << endl;
				
				if (i == 0 && t == G.l[0]) //no outgoing arcs regarding the depot at its closing time point
					continue;

				//add crossing arcs
				for (int j = 0; j < G.N0; j++)
				{
					if (i == j) //same terminal/continue
						continue;	 				

					//find largest t' such that (j,t') in N_T and t' - t \leq \tau_{ij} - nghia la co canh noi duoc 2 dinh nay
					int tau_ij = G.tau[i][j];
					double rtau_ij = G.rtau[i][j];

	 				if (t + tau_ij > G.l[j]) continue; //do not consider this arc because it violates time window constraint
					if (t + rtau_ij > G.l[j]) continue;

					
					S_IT loc = PTEG.NT[j].upper_bound(t + tau_ij);
					
					if (loc!= PTEG.NT[j].begin())
						loc--;
 
					int t_prime = *loc;

					NODE dest = make_pair(j, t_prime); //next vertex


					PTEG.AT[source].insert(dest); //add an arc from source to dest -
					
					if (DEBUG)
					{
						if (t + tau_ij < G.e[j])
							cout << "Waiting at " << j << " because of early arrival with departure from " << i << " at time point " << t << endl;
						cout << "(" << i << "," << t << ")-(" << j << "," << t_prime << ")" << endl;

					}

				}
				//add a holding arc

				S_IT next = t_it; next++;

				if (next != PTEG.NT[i].end())
				{
					int t_prime = *next;

					//assert(t != t_prime);
					if (t != t_prime)
					{
						NODE dest = make_pair(i, t_prime);
						PTEG.AT[source].insert(dest); //holding arc
					}
				}
			}
	}

	//in this version, (i,t) connects to (j,t') if t'>= t+ tau_ij because we can wait at j
	//(i,t) can connect to (j,t') if l(j) >= t+ tau(i,j)
	void CreateInitialParitalGraph1(OriginalGraph &G, //original graph
		PartialTimeExpandedGraph &PTEG //initial partially time-expanded graph
		)
	{
		//list of nodes in the partial graph
		for (int i = 0; i < G.N0; i++)
		{
			PTEG.NT[i].insert(0);
			PTEG.NT[i].insert(G.e[i]);
			PTEG.NT[i].insert(G.l[i]);
		}

		//adding arcs, 
		for (int i = 0; i < G.N0; i++) //all terminals
			for (S_IT t_it = PTEG.NT[i].begin(); t_it != PTEG.NT[i].end(); t_it++) //all time points associated with each terminal
			{
				int t = *t_it;
				NODE source = make_pair(i, t); //current vertex s

				//add crossing arcs
				for (int j = 0; j < G.N0; j++)
					if (i != j) //different terminal
					{

						//find largest t' such that (j,t') in N_T and t' - t \leq \tau_{ij} - nghia la co canh noi duoc 2 dinh nay
						int tau_ij = G.tau[i][j];

						//if (t + tau_ij > G.l[j]) continue; //do not consider this arc because it violates time window constraint

						S_IT loc = PTEG.NT[j].upper_bound(t + tau_ij);
						loc--;
						int t_prime = *loc;

						NODE dest = make_pair(j, t_prime); //next vertex

						PTEG.AT[source].insert(dest); //add an arc from source to dest -

					}
				//add a new holding arc

				S_IT next = t_it; next++;

				if (next != PTEG.NT[i].end())
				{
					int t_prime = *next;

					assert(t != t_prime);

					NODE dest = make_pair(i, t_prime);
					PTEG.AT[source].insert(dest);
				}
			}
	}

	//Algorithm 4: REFINE - adding new arcs related to the new node.
	//insert a new node (i,t_new) to the partially time expanded graph PTEG
	//addedNodeList will contain new added nodes
	//addedVarList will contain list of being added arcs/variables related to new added nodes during the refine function
	//deletedVarList will contain list of being removed arcs/variables related to new added/nodes during the refine function

	bool REFINE(int i, int t_new, OriginalGraph &G, PartialTimeExpandedGraph &PTEG, set<NODE> &addedNodeList, set<VarIndex> &addedVarList, set<VarIndex> &deletedVarList)
	{
		//add new node
		//cout << "Trying to add new node" << "(" << i << "," << t_new << ")" << endl;
		std::pair<std::set<int>::iterator, bool> loc = PTEG.NT[i].insert(t_new); //location of new added node
 

		if (loc.second == false)
		{
			//cout << "This node is already in the model!" << endl;
			
			return false;
		}

 		addedNodeList.insert(NODE(i, t_new));

		//prev and succ node
		S_IT cur = loc.first;
		S_IT prev = cur; prev--;
		S_IT next = cur; next++;

		assert(next != PTEG.NT[i].end());

		 

		int t_k = *prev;
		int t_k_plus_one = *next;

		assert(t_k < t_new && t_new < t_k_plus_one);
		 

		//remove the holding arc (i,t_k) - (i,t_k_plus_one) - step 2
		NODE prev_node = make_pair(i, t_k);
		NODE succ_node = make_pair(i, t_k_plus_one);

		//if (DEBUG)
		//{
		//	cout << "Prev node : (" << i << "," << t_k << endl;
		//	cout << "Succ node : (" << i << "," << t_k_plus_one << endl;
		//	cout << "Curr node : (" << i << "," << t_new << endl;
		//}
		
		PTEG.AT[prev_node].erase(succ_node);

		deletedVarList.insert(VarIndex(i, t_k, i, t_k_plus_one)); //remove the corresponding variable from the model

		//new node associated to new time point - step 2
		NODE new_node = make_pair(i, t_new);

		//adding two new holding arcs
		PTEG.AT[prev_node].insert(new_node);
		PTEG.AT[new_node].insert(succ_node);
		
		assert(t_new != t_k && t_new != t_k_plus_one);
		if (t_new != t_k)
			addedVarList.insert(VarIndex(i, t_k, i, t_new)); //will be adding these two new variables associated with these two holding arcs
		if (t_new != t_k_plus_one)
			addedVarList.insert(VarIndex(i, t_new, i, t_k_plus_one));

		//adding new crossing arcs from new added node - step 3

		for (set<NODE>::iterator jt_node_it = PTEG.AT[prev_node].begin(); jt_node_it != PTEG.AT[prev_node].end(); jt_node_it++)
		{
			NODE jt_node = *jt_node_it;
			PTEG.AT[new_node].insert(jt_node);

			int j = jt_node.first;
			int t = jt_node.second;
			
			if (i == j) 
				continue; //holding arc

			//add more condition here
			if (t_new + G.tau[i][j] > G.l[j]) //cannot add this arc because of time window condition
				continue;

			if (t_new + G.tau[i][j] < G.e[i])
				t = G.e[i];
			//if (DEBUG) 
			//	cout << "New arc: " << VarIndex(i, t_new, j, t) << endl;
			addedVarList.insert(VarIndex(i, t_new, j, t)); //will be adding new variables associated with these crossing arcs
		}
		 
		return true;
	}


	//Algorithm 5: RESTORE -  restore longest-feasible-arc property
	//restore the longest-feasible-arc property related to the new added node (i,t_new) to the partially time expanded graph PTEG
	//addedVarList will contain list of being added arcs/variables related to new added nodes during the restoration function
	//deletedVarList will contain list of being removed arcs/variables related to new added/nodes during the restoration function

	void RESTORE(int i, int t_new, OriginalGraph &G, PartialTimeExpandedGraph &PTEG, set<VarIndex> &addedVarList, set<VarIndex> &deletedVarList)
	{

		S_IT loc = PTEG.NT[i].find(t_new); //located the location of new added time point related to terminal i

		S_IT cur = loc;
		S_IT prev = cur; prev--; //prev node
		S_IT next = cur; next++; //succ node

		int t_k = *prev;
		int t_k_plus_one = *next;

		//recover longest-feasible-path property
		NODE prev_node = make_pair(i, t_k);
		NODE new_node = make_pair(i, t_new);
		
		for (set<NODE>::iterator jt_node_it = PTEG.AT[prev_node].begin(); jt_node_it != PTEG.AT[prev_node].end(); jt_node_it++) //travese the list of arcs associated to prev_node - line 1
		{
			NODE jt_node = *jt_node_it; // = (j,t) 

			int j = jt_node.first; //dest - terminal
			int t = jt_node.second; //dest - time period

			if (i == j) //holding arc, not lengthen 
				continue;

			if (t_new + G.tau[i][j] > G.l[j])
			{
				addedVarList.erase(VarIndex(i, t_new, j, t)); //will remove associated variable from the model - do not add this arc to the model
				continue;
			}
			
			S_IT succ_tprime_it = PTEG.NT[j].upper_bound(t_new + G.tau[i][j]); //line 2, find successor of t'
			
			 

			S_IT t_prime_it = succ_tprime_it; //t' now
			if (t_prime_it != PTEG.NT[j].begin()) //in the case t_new + tau_ij < e[j]
				t_prime_it--;

			int t_prime = *t_prime_it;

			if (t_prime != t) //line 3
			{
				assert(t_new + G.tau[i][j] <= G.l[j]);

				PTEG.AT[new_node].erase(jt_node); //erase old arc related to new_node line 4
				  
				addedVarList.erase(VarIndex(i, t_new, j, t)); //will remove associated variable from the model - do not add this arc to the model

				NODE jtprime_node = make_pair(j, t_prime);

				PTEG.AT[new_node].insert(jtprime_node); //arc new arc related to new_node to enforce longest_feasiblity_path property

				addedVarList.insert(VarIndex(i, t_new, j, t_prime)); //will add associated variable to the model
			}
		}

		for (map<NODE, set<NODE> >::iterator jt_node_it = PTEG.AT.begin(); jt_node_it != PTEG.AT.end(); jt_node_it++) //line 7
		{
			NODE jt_node = jt_node_it->first;
			set<NODE> s_jt = jt_node_it->second;

			int t = jt_node.second;
			int j = jt_node.first;

			if (i == j)
				continue;

			if (t + G.tau[j][i] >= t_new && t + G.tau[j][i] <= G.l[i]) //line 7 condition; the distance between two terminals is not so long and not so late
				if (s_jt.find(prev_node) != s_jt.end()) //if there is an arc from jt-node to the prev node; replace with the new arc to enforce longest_ feasible_path
				{
					PTEG.AT[jt_node].erase(prev_node);

					deletedVarList.insert(VarIndex(j, t, i, t_k)); //will remove the variable associated with this arc from the model

					PTEG.AT[jt_node].insert(new_node);

					addedVarList.insert(VarIndex(j, t, i, t_new)); //will add the variable associated with this arc to the model
				}
		}
	}

	//Algorithm 3  - lengthen the arc (i,t) - (j,t_prime) to solve infeasibility due to short arc.
	//First, add a new node to the partial network by REFINE function
	//Second, restore the longest-feasible-arc property regarding the new added node
	void LENGTHEN_ARC(int i, int t, int j, int t_prime, OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
	{

		assert(t + G.tau[i][j] <= G.l[j]);

		REFINE(j, max(t + G.tau[i][j], G.e[i]), G, PTEG, addedNodeList, addedVarList, deletedVarList); //add a new node named (j, t + G.tau[i][j]) to the partially network
		cout << "Finish added new arcs!Done!" << endl;
		RESTORE(j, max(t + G.tau[i][j],G.e[i]), G, PTEG, addedVarList, deletedVarList); //restore the longest-feasible-arc property
		cout << "Finish lengthen an old arc!Done!" << endl;
	}

	bool ARC_MODIFICATION(VarIndex old_arc, VarIndex new_arc)
	{
		
		if (x_a.find(new_arc) != x_a.end())
		{
			if (DEBUG) cout << "The arc "<< new_arc << " is already in the model" << endl;
			
			addedVarList.erase(new_arc);
			
			return false;
		}
		
		//addedVarList.insert(new_arc);
		//deletedVarList.insert(old_arc);

		bool added_arc = REFINE(new_arc.j, new_arc.t_prime, G,PTEG, addedNodeList, addedVarList, deletedVarList);

		if (DEBUG) cout << "Finish added nodes && related arcs!Done!" << endl;
		if (added_arc == true)
		{
			RESTORE(new_arc.j, new_arc.t_prime, G, PTEG, addedVarList, deletedVarList);
			if (DEBUG) cout << "Finish lengthen arcs!Done!" << endl;

		}
		return true; 
	}

	void UpdateManyTimeForShortCycle(vector<NODE> &cycle)
	{
		int curTime = cycle[0].second; //la thoi diem bat dau cua diem thap nhat
		int prevTime = -1;
		int nbModificationArcs = 0;
		bool change = false;

		for (int idx = 1; ; idx++)
		{

			addedNodeList.clear();
			addedVarList.clear();
			deletedVarList.clear();

			//if (change) //perform only 1 change
			//	break; 

			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			prevTime = curTime;
			curTime = max(curTime + G.tau[i][j], G.e[j]);

			VarIndex old_arc(i, t, j, t_prime); //old arc in the list

			VarIndex new_arc(i, prevTime, j, curTime); //new arc

			//cout << "************************************" << endl;
			//cout << "Is trying to remove old arc" << old_arc << endl;
			//cout << "Is trying to add new arc" << new_arc << endl;

			if (i == j && prevTime == curTime && t_prime > curTime)
			{
				//cout << "Holding arcs! Do nothing!" << endl;
				curTime = t_prime;
				continue;
			}

			if (isTheSameArc(old_arc, new_arc) && curTime <= G.l[j])
			{
				//cout << "They are same arc! Already lengthened so cannnot remove!" << endl;
				continue; //this arc is already lengthened. 
			}
			else if (isTheSameArc(old_arc, new_arc) && curTime > G.l[j])
			{
				deletedVarList.insert(old_arc); //remove because this arc violate time window constraint at j
			}


			if (!tooLate(new_arc) && t != prevTime) //nghia la old_arc va new_arc xuat phat tu hai diem khac nhau, giu old arc
			{
				//cout << "Keep old arcs while adding new arcs because they depart at different time!" << endl;

				deletedVarList.erase(old_arc);
				//continue; 
			}
			else if (!tooLate(new_arc))
			{
				//cout << "Is able to remove old arc! Two arcs depart from a same time!" << endl;
				deletedVarList.insert(old_arc); //xoa old_arc
			}

			if (isValidArc(new_arc)) //them duoc arc moi, cac diem deu thoa man time window
			{
				nbModificationArcs++;
				addedVarList.insert(new_arc);
				ARC_MODIFICATION(old_arc, new_arc);
			}
			else
			{
				//cout << "New arc is too late!Cannot added!Keep old arcs! " << endl;
				if (t == prevTime)
				{
					//cout << "Previous arc is lengthened! So remove old arc!" << endl;
					deletedVarList.insert(old_arc);
				}
			}

			//actually adding arcs to the model
			addNodeArcToModel(G, PTEG, deletedVarList, addedVarList, addedNodeList);

			change = deletedVarList.size() + addedVarList.size() + addedNodeList.size() > 0;

			for (set<VarIndex>::iterator it = addedVarList.begin(); it != addedVarList.end(); it++)
			{
				 
				ostringstream sname;
				sname << "x(" << it->i << "," << it->t << ")(" << it->j << "," << it->t_prime << ")";
				newArcNames[*it] = sname.str();
				cout << "create:x(" << it->i << "," << it->t << ")(" << it->j << "," << it->t_prime << ")" << endl;
				cout << "Insert:"<<sname.str() << endl;
			}
			//if (DEBUG) cout << "New nodes:";
			//cout << addedNodeList.size() << endl;
			////printAddedNodeList(addedNodeList);
			////if (addedNodeList.size() == 0) cout << "No new nodes" << endl;

			//if (DEBUG) cout << "New added arcs:";
			//cout << addedVarList.size() << endl;

			////if (addedVarList.size()) cout << endl;
			////printAddedArcsList(addedVarList);
			////if (addedVarList.size() == 0) cout << "No new arcs " << endl;

			//if (DEBUG) cout << "Old removed arcs:";
			//cout << deletedVarList.size() << endl;

			//if (deletedVarList.size()) cout << endl;
			//printRemovedArcsList(deletedVarList);
			//if (deletedVarList.size() == 0) cout << "No removed arcs" << endl;
		}
		return ;

	}

	//update each node to its correct location if we move along this cycle
	//remove violated arcs if this cycle has
	int UpdateOnlyASingArcFollowingCycle(vector<NODE> &cycle, int violatedTerminal)
	{
		int curTime = cycle[0].second; //la thoi diem bat dau cua diem thap nhat
		int prevTime = -1;
		int nbModificationArcs = 0;
		bool change = false;

		for (int idx = 1; idx <= violatedTerminal; idx++)
		{

			addedNodeList.clear();
			addedVarList.clear();
			deletedVarList.clear();

			if (change) //perform only 1 change
				break; 

			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			prevTime = curTime;
			curTime = max(curTime + G.tau[i][j], G.e[j]);

			VarIndex old_arc(i, t, j, t_prime); //old arc in the list

			VarIndex new_arc(i, prevTime, j, curTime); //new arc

			//cout << "************************************" << endl;
			//cout << "Is trying to remove old arc" << old_arc << endl;
			//cout << "Is trying to add new arc" << new_arc << endl;

			if (i == j && prevTime == curTime && t_prime > curTime)
			{
				//cout << "Holding arcs! Do nothing!" << endl;
				curTime = t_prime;
				continue;
			}

			if (isTheSameArc(old_arc, new_arc) && curTime <= G.l[j])
			{
				//cout << "They are same arc! Already lengthened so cannnot remove!" << endl;
				continue; //this arc is already lengthened. 
			}
			else if (isTheSameArc(old_arc, new_arc) && curTime > G.l[j])
			{
				deletedVarList.insert(old_arc); //remove because this arc violate time window constraint at j
			}


			if (!tooLate(new_arc) && t != prevTime) //nghia la old_arc va new_arc xuat phat tu hai diem khac nhau, giu old arc
			{
				//cout << "Keep old arcs while adding new arcs because they depart at different time!" << endl;

				deletedVarList.erase(old_arc);
				//continue; 
			}
			else if (!tooLate(new_arc))
			{
				//cout << "Is able to remove old arc! Two arcs depart from a same time!" << endl;
				deletedVarList.insert(old_arc); //xoa old_arc
			}

			if (isValidArc(new_arc)) //them duoc arc moi, cac diem deu thoa man time window
			{
				nbModificationArcs++;
				addedVarList.insert(new_arc);
				ARC_MODIFICATION(old_arc, new_arc);
			}
			else
			{
				//cout << "New arc is too late!Cannot added! " << endl;
				if (t == prevTime)
				{
					//cout << "Previous arc is lengthened! So remove old arc!" << endl;
					deletedVarList.insert(old_arc);
				}
			}

			//actually adding arcs to the model
			addNodeArcToModel(G, PTEG, deletedVarList, addedVarList, addedNodeList);

			change = deletedVarList.size() + addedVarList.size() + addedNodeList.size() > 0;

			for (set<VarIndex>::iterator it = addedVarList.begin(); it != addedVarList.end(); it++)
			{
				 
				ostringstream sname;
				sname << "x(" << it->i << "," << it->t << ")(" << it->j << "," << it->t_prime << ")";
				newArcNames[*it] = sname.str();
	 
			}
			 

			for (set<VarIndex>::iterator it = deletedVarList.begin(); it != deletedVarList.end(); it++)
			{
 				ostringstream sname;
				sname << "x(" << it->i << "," << it->t << ")(" << it->j << "," << it->t_prime << ")";
				newArcNames.erase(*it);
			}

			if (DEBUG) cout << "New nodes:";
			cout << addedNodeList.size() << endl;
			//printAddedNodeList(addedNodeList);
			//if (addedNodeList.size() == 0) cout << "No new nodes" << endl;

			if (DEBUG) cout << "New added arcs:";
			cout << addedVarList.size() << endl;

			//if (addedVarList.size()) cout << endl;
			//printAddedArcsList(addedVarList);
			//if (addedVarList.size() == 0) cout << "No new arcs " << endl;

			if (DEBUG) cout << "Old removed arcs:";
			cout << deletedVarList.size() << endl;

			//if (deletedVarList.size()) cout << endl;
			//printRemovedArcsList(deletedVarList);
			//if (deletedVarList.size() == 0) cout << "No removed arcs" << endl;
		}
		return 0;
		//return nbModificationArcs;
	}

	int UpdateASingleArcFollowingCycle(vector<NODE> &cycle, int violatedTerminal)
	{
		int curTime = cycle[0].second; //la thoi diem bat dau cua diem thap nhat
		int prevTime = -1;
		int nbModificationArcs = 0;
		bool change = false;

		for (int idx = 1; idx <= violatedTerminal; idx++)
		{

			addedNodeList.clear();
			addedVarList.clear();
			deletedVarList.clear();

			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			prevTime = curTime;
			curTime = max(curTime + G.tau[i][j], G.e[j]);

			VarIndex old_arc(i, t, j, t_prime); //old arc in the list

			VarIndex new_arc(i, prevTime, j, curTime); //new arc

			//cout << "************************************" << endl;
			//cout << "Is trying to remove old arc" << old_arc << endl;
			//cout << "Is trying to add new arc" << new_arc << endl;

			if (i == j && prevTime == curTime && t_prime > curTime)
			{
				//cout << "Holding arcs! Do nothing!" << endl;
				curTime = t_prime;
				continue;
			}

			if (isTheSameArc(old_arc, new_arc) && curTime <= G.l[j])
			{
				//cout << "They are same arc! Already lengthened so cannnot remove!" << endl;
				continue; //this arc is already lengthened. 
			}
			else if (isTheSameArc(old_arc, new_arc) && curTime > G.l[j])
			{
				deletedVarList.insert(old_arc); //remove because this arc violate time window constraint at j
			}


			if (!tooLate(new_arc) && t != prevTime) //nghia la old_arc va new_arc xuat phat tu hai diem khac nhau, giu old arc
			{
				//cout << "Keep old arcs while adding new arcs because they depart at different time!" << endl;

				deletedVarList.erase(old_arc);
				//continue; 
			}
			else if (!tooLate(new_arc))
			{
				//cout << "Is able to remove old arc! Two arcs depart from a same time!" << endl;
				deletedVarList.insert(old_arc); //xoa old_arc
			}

			if (isValidArc(new_arc)) //them duoc arc moi, cac diem deu thoa man time window
			{
				nbModificationArcs++;
				addedVarList.insert(new_arc);
				ARC_MODIFICATION(old_arc, new_arc);
			}
			else
			{
				//cout << "New arc is too late!Cannot added! " << endl;
				if (t == prevTime)
				{
					//cout << "Previous arc is lengthened! So remove old arc!" << endl;
					deletedVarList.insert(old_arc);
				}
			}

			//actually adding arcs to the model
			addNodeArcToModel(G, PTEG, deletedVarList, addedVarList, addedNodeList);

			change = deletedVarList.size() + addedVarList.size() + addedNodeList.size() > 0;

			for (set<VarIndex>::iterator it = addedVarList.begin(); it != addedVarList.end(); it++)
			{
				 
				ostringstream sname;
				sname << "x(" << it->i << "," << it->t << ")(" << it->j << "," << it->t_prime << ")";
				newArcNames[*it] = sname.str();
 
			}

			for (set<VarIndex>::iterator it = deletedVarList.begin(); it != deletedVarList.end(); it++)
			{
				newArcNames.erase(*it);
			}

			if (change)
				return 1;
			
			if (DEBUG) cout << "New nodes:";
			cout << addedNodeList.size() << endl;
			//printAddedNodeList(addedNodeList);
			//if (addedNodeList.size() == 0) cout << "No new nodes" << endl;

			if (DEBUG) cout << "New added arcs:";
			cout << addedVarList.size() << endl;

			//if (addedVarList.size()) cout << endl;
			//printAddedArcsList(addedVarList);
			//if (addedVarList.size() == 0) cout << "No new arcs " << endl;

			if (DEBUG) cout << "Old removed arcs:";
			cout << deletedVarList.size() << endl;

			//if (deletedVarList.size()) cout << endl;
			//printRemovedArcsList(deletedVarList);
			//if (deletedVarList.size() == 0) cout << "No removed arcs" << endl;
		}
		return 0;
		//return nbModificationArcs;
	}

	//update each node to its correct location if we move along this cycle
	//remove violated arcs if this cycle has
	int UpdateArcsFollowingCycle(vector<NODE> &cycle, int violatedTerminal)
	{
		int curTime = cycle[0].second; //la thoi diem bat dau cua diem thap nhat
		int prevTime = -1;
		int nbModificationArcs = 0;
		bool change = false;

		for (int idx = 1; idx <= violatedTerminal; idx++)
		{

			addedNodeList.clear();
			addedVarList.clear();
			deletedVarList.clear();

			//if (change) //perform only 1 change
			//	break; 

			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			if (j == 0)
				break;

			prevTime = curTime;
			curTime = max(curTime + G.tau[i][j], G.e[j]);

			VarIndex old_arc(i, t, j, t_prime); //old arc in the list
			 
			VarIndex new_arc(i, prevTime, j, curTime); //new arc

			//if (DEBUG)
			//{
			//	cout << "************************************" << endl;
			//	cout << "Is trying to remove old arc" << old_arc << endl;
			//	cout << "Is trying to add new arc" << new_arc << endl;

			//}
			
			if (i == j && prevTime == curTime && t_prime > curTime)
			{
				if (DEBUG) 
					cout << "Holding arcs! Do nothing!" << endl;
				curTime = t_prime;
				continue;	
			}

			if (isTheSameArc(old_arc, new_arc) && curTime <= G.l[j])
			{
				if (DEBUG) cout << "They are same arc! Already lengthened so cannnot remove!" << endl;
				continue; //this arc is already lengthened. 
			}
			else if (isTheSameArc(old_arc, new_arc) && curTime > G.l[j])
			{
				deletedVarList.insert(old_arc); //remove because this arc violate time window constraint at j
			}


			if (!tooLate(new_arc) && t != prevTime) //nghia la old_arc va new_arc xuat phat tu hai diem khac nhau, giu old arc
			{
				if (DEBUG)  cout << "Keep old arcs while adding new arcs because they depart at different time!" << endl;

				deletedVarList.erase(old_arc);
				//continue; 
			}
			else if (!tooLate(new_arc))
			{
				if (DEBUG) cout << "Is able to remove old arc! Two arcs depart from a same time!" << endl;
				deletedVarList.insert(old_arc); //xoa old_arc
			}
			
			if (isValidArc(new_arc)) //them duoc arc moi, cac diem deu thoa man time window
			{
				nbModificationArcs++;
				addedVarList.insert(new_arc);
				ARC_MODIFICATION(old_arc, new_arc);
			}
			else
			{
				if (DEBUG) cout << "New arc is too late!Cannot added! " << endl;
				if (t == prevTime)
				{
					if (DEBUG)  cout << "Previous arc is lengthened! So remove old arc!" << endl;
					deletedVarList.insert(old_arc);
				}
			}

			//actually adding arcs to the model
			addNodeArcToModel(G, PTEG, deletedVarList, addedVarList, addedNodeList);

			change = deletedVarList.size() + addedVarList.size() + addedNodeList.size() > 0;
			
			for (set<VarIndex>::iterator it = addedVarList.begin(); it != addedVarList.end(); it++)
			{
				newArcs.insert(*it);
				ostringstream sname;
				sname << "x(" << it->i << "," << it->t << ")(" << it->j << "," << it->t_prime << ")";
				newArcNames[*it] = sname.str();
			}

			for (set<VarIndex>::iterator it = deletedVarList.begin(); it != deletedVarList.end(); it++)
			{
 				newArcNames.erase(*it);
			}
				
			
			
			//if (DEBUG) { 
			//	cout << "New nodes:" << addedNodeList.size() << endl; 
			//	printAddedNodeList(addedNodeList);
			//	if (addedNodeList.size() == 0) cout << "No new nodes" << endl;

			//	cout << "New added arcs:" << addedVarList.size() << endl;
			//	printAddedArcsList(addedVarList);
			//	if (addedVarList.size() == 0) cout << "no new arcs " << endl;

			//	cout << "Old removed arcs:" << deletedVarList.size() << endl;
			//	if (deletedVarList.size()) cout << endl;
			//	printRemovedArcsList(deletedVarList);

			//	if (deletedVarList.size() == 0) cout << "No removed arcs" << endl;
			//}
		}
		return 0;
		//return nbModificationArcs;
	}
	/**********************************************************Initial model generation function******************************************************************/

	bool InitialModelGeneration(OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
	{
		try {

			model.set(GRB_StringAttr_ModelName, "TSPTW_coded_by_MinhDV");

			// Create variables

			for (map<NODE, set<NODE> >::iterator i_t_it = PTEG.AT.begin(); i_t_it != PTEG.AT.end(); i_t_it++) //duyet moi canh
			{
				NODE it_node = i_t_it->first;
				set<NODE> s_it = i_t_it->second;

				int i = it_node.first;
				int t = it_node.second;


				//create x_a or arcs variables
				for (set<NODE>::iterator j_tprime_it = s_it.begin(); j_tprime_it != s_it.end(); j_tprime_it++) //traverse all nodes (j,t') that are adjacent with (i,t)
				{
					NODE j_tprime_node = *j_tprime_it;
					int j = j_tprime_node.first;
					int t_prime = j_tprime_node.second;

					//if (i == j)
					//	continue;

					ostringstream var_name;
					var_name << "x(" << i << "," << t << ")(" << j << "," << t_prime << ")";

					GRBVar new_arc = model.addVar(0.0, 1.0, 0.0, GRB_CONTINUOUS, var_name.str()); //add the variable associated to this arc to the model

					x_a[VarIndex(i, t, j, t_prime)] = new_arc;

				}
			}

			//update new added variables
			model.update(); //put it here because of lazy updates

			//create and update objective function
			for (map<VarIndex, GRBVar>::iterator varIndex_it = x_a.begin(); varIndex_it != x_a.end(); varIndex_it++)
			{
				int i = varIndex_it->first.i;
				int j = varIndex_it->first.j;

				//no penalty
				if (i!=j)
					(varIndex_it->second).set(GRB_DoubleAttr_Obj, G.rtau[i][j]);
				
				//adding penalty to backward arcs
				//if (i != j)
				//	if (varIndex_it->first.t <= varIndex_it->first.t_prime)
				//		(varIndex_it->second).set(GRB_DoubleAttr_Obj, G.rtau[i][j]);
				//	else
				//		(varIndex_it->second).set(GRB_DoubleAttr_Obj, 1e6);  //a big value to prevent backward arcs.

			}
			// The objective is to minimize the total cost of arcs
			model.set(GRB_IntAttr_ModelSense, GRB_MINIMIZE);

			//model.update();

			//Add 1st set of constraint - depot constraint
			NODE depotOut = make_pair(0, G.e[0]);
			GRBLinExpr depotOutExp = 0; //first set of constraint

			for (set<NODE>::iterator jt_node_it = PTEG.AT[depotOut].begin(); jt_node_it != PTEG.AT[depotOut].end(); jt_node_it++)
			{
				NODE jt_node = *jt_node_it;
				int j = jt_node.first;
				int t = jt_node.second;

				if (j != 0)
					depotOutExp += x_a[VarIndex(0, G.e[0], j, t)];
			}

			ostringstream depotOutConstraint;
			depotOutConstraint << "DepotOutConstraint";
			model.addConstr(depotOutExp == 1, depotOutConstraint.str());

			//model.update();

			constraintSet[depotOutConstraint.str()] = depotOutExp;

		
			//Add 2nd set of constraint - Flow balance constraints
			map<NODE, GRBLinExpr> flowBalanceConstraints; //2nd set of constraint ; set of flow balance constraint, one of each node

			for (map<NODE, set<NODE> >::iterator it_node_it = PTEG.AT.begin(); it_node_it != PTEG.AT.end(); it_node_it++)
			{
				NODE it_node = it_node_it->first;
				set<NODE> s_it = it_node_it->second;

				int i = it_node.first;
				int t = it_node.second;


				for (set<NODE>::iterator jtprime_node_it = s_it.begin(); jtprime_node_it != s_it.end(); jtprime_node_it++)
				{
					NODE j_tprime_node = *jtprime_node_it;

					int j = j_tprime_node.first;
					int t_prime = j_tprime_node.second;
					
					if (i == j)  //no holding arcs,
						continue;
					
					if (i != 0 || (t != G.e[0] && t != G.l[0])) //flow balance at every intermediate node
						flowBalanceConstraints[NODE(i, t)] += x_a[VarIndex(i, t, j, t_prime)];
					
					if (j != 0 || (t_prime != G.e[0] && t_prime != G.l[0]))  //flow balance at every intermediate node 
						flowBalanceConstraints[NODE(j, t_prime)] -= x_a[VarIndex(i, t, j, t_prime)];
				}
			}

			for (map<NODE, set<NODE> >::iterator it_node_it = PTEG.AT.begin(); it_node_it != PTEG.AT.end(); it_node_it++) //line 7
			{
				NODE it_node = it_node_it->first;
				set<NODE> s_it = it_node_it->second;

				int i = it_node.first;
				int t = it_node.second;

				if (i == 0 && (t == G.e[0] || t == G.l[0]))
					continue;

				ostringstream flowConstraint;
				flowConstraint << "FlowConstraint_" << i << "." << t;
				model.addConstr(flowBalanceConstraints[NODE(i, t)] == 0, flowConstraint.str());

				constraintSet[flowConstraint.str()] = flowBalanceConstraints[NODE(i, t)];
			}

			//model.update();

			//Add 3rd set of constraints
			vector<GRBLinExpr> visitedOnce; //third set of constraints		

			for (int i = 0; i < G.N0; i++)
			{
				GRBLinExpr visitedOnceExp = 0;
				for (set<int>::iterator t_it = PTEG.NT[i].begin(); t_it != PTEG.NT[i].end(); t_it++) //travese all time points t associated with i
				{
					int t = *t_it;
					NODE it_node = make_pair(i, t);

					for (set<NODE>::iterator j_tprime_it = PTEG.AT[it_node].begin(); j_tprime_it != PTEG.AT[it_node].end(); j_tprime_it++) //all nodes connected with (i,t)
					{
						NODE jt_node = *j_tprime_it;
						int j = jt_node.first;
						int tprime = jt_node.second;

						if (i!=j) //going out
							visitedOnceExp += x_a[VarIndex(i, t, j, tprime)];

					}
				}

				visitedOnce.push_back(visitedOnceExp);

				ostringstream visitedOnceConstraint;
				visitedOnceConstraint << "visitedOnceConstraint_" << i;
				model.addConstr(visitedOnce[i] == 1, visitedOnceConstraint.str()); //each terminal is visited once

				constraintSet[visitedOnceConstraint.str()] = visitedOnce[i];
			}

			//Add subtour constraint length 2
			//map < pair<int, int >, GRBLinExpr > mSubToursLength2;

			//for (int i = 1; i < G.N0; i++)
			//	for (int j = i + 1; j < G.N0; j++)
			//		if (G.tau[i][j] + G.tau[j][i] < 1e6)
			//			mSubToursLength2[make_pair(i, j)] = GRBLinExpr(0.0);

			//for (map<NODE, set<NODE> >::iterator i_t_it = PTEG.AT.begin(); i_t_it != PTEG.AT.end(); i_t_it++) //duyet moi canh
			//{
			//	NODE it_node = i_t_it->first;
			//	set<NODE> s_it = i_t_it->second;

			//	int i = it_node.first;
			//	int t = it_node.second;


			//	//create x_a or arcs variables
			//	for (set<NODE>::iterator j_tprime_it = s_it.begin(); j_tprime_it != s_it.end(); j_tprime_it++) //traverse all nodes (j,t') that are adjacent with (i,t)
			//	{
			//		NODE j_tprime_node = *j_tprime_it;
			//		int j = j_tprime_node.first;
			//		int t_prime = j_tprime_node.second;

			//		int u = min(i, j);
			//		int v = max(i, j);

			//		mSubToursLength2[make_pair(u, v)] += x_a[VarIndex(i, t, j, t_prime)];

			//	}
			//}

			//for (int i = 1; i < G.N0; i++)
			//	for (int j = i + 1; j < G.N0; j++)
			//	{
			//		if (G.tau[i][j] == 1e6 || G.tau[j][i] == 1e6)
			//			continue; 

			//		ostringstream subTour;
			//		subTour << "SubTour_" << i << "." << j;
			//		model.addConstr(mSubToursLength2[make_pair(i, j)] <= 1, subTour.str()); //sub tour constraint length 2
			//		constraintSet[subTour.str()] = mSubToursLength2[make_pair(i, j)];
			//	}

			//update entire model

			model.update();

		}
		catch (GRBException e) {
			cout << "Error code = " << e.getErrorCode() << "in Inital Model Generation" << endl;
			cout << e.getMessage() << endl;
			exit(0);
		}
		catch (...) {
			cout << "Exception during optimization" << endl;
			return false;
		}

		return true;
	}

	/**********************************************************Model modification*****************************************************************************/

	void addNodeArcToModel(OriginalGraph &G, PartialTimeExpandedGraph &PTEG, set<VarIndex> &deletedVarList, set<VarIndex> &addedVarList, set<NODE> &addedNodeList)
	{
		try{
			if (DEBUG) 
				cout << "Model modification!" << endl;
			set<string> newConstraints;

			
			assert(addedNodeList.size() <= 1); //add no more than one node each time

			int ii = -1, tt = -1;

			if (addedNodeList.size())
				ii = addedNodeList.begin()->first, tt = addedNodeList.begin()->second;

			constraintSet.clear();
			newConstraints.clear();

			//add constraints related to the new node
			for (set<NODE>::iterator it = addedNodeList.begin(); it != addedNodeList.end();it++)
			 
			{
				 
				int i = it->first;
				int t = it->second;

				 
				if (i == 0 && t == G.e[0])
					continue;

				//if (DEBUG) cout << "New node : (" << i << "," << t << ")" << endl;

				ostringstream flowConstraint;
				flowConstraint << "FlowConstraint_" << i << "." << t;

				model.addConstr(GRBLinExpr(0.0) == 0, flowConstraint.str());

				newConstraints.insert(flowConstraint.str());
				constraintSet[flowConstraint.str()] = GRBLinExpr(0.0);
				//model.update();
				//constraintSet[flowConstraint.str()] = model.getRow( model.getConstrByName(flowConstraint.str()));
			}

			model.update();
			
			for (set<VarIndex>::iterator it = deletedVarList.begin(); it!=deletedVarList.end(); it++)
			{
				model.remove(x_a[*it]); //remove variables from the model

				x_a.erase(*it); //remove variable from variables' list

				int i = it->i;
				int t = it->t;
				int j = it->j;
				int t_prime = it->t_prime;

				PTEG.AT[NODE(i, t)].erase(NODE(j, t_prime)); //remove arcs from arcs' list
			}

			model.update();

			//cout << " Remove old variables!Done!" << endl;

			constraintSet.clear();

			for (set<VarIndex>::iterator it = addedVarList.begin(); it!= addedVarList.end(); it++)
			{
				int i = it->i;
				int t = it->t;
				int j = it->j;
				int t_prime = it->t_prime;

				if (i == j)
				{
					//addedVarList.erase(it);
					continue;
				}
				//if (ii == i && tt == t) cout << "Related new added nodes" << i<<"."<<t<< endl;
				 

				ostringstream var_name;

				var_name << "x(" << i << "," << t << ")(" << j << "," << t_prime << ")";
				
				if (DEBUG) 
					cout << "Create new arcs" << var_name.str() << endl;

				GRBVar new_arc;
				
				if (MIP)
					new_arc = model.addVar(0.0, 1.0, (i != j ? G.rtau[i][j] : 0), GRB_BINARY, var_name.str()); //add the variable associated to this arc to the model
				else
					new_arc = model.addVar(0.0, 1.0, (i != j ? G.rtau[i][j] : 0), GRB_CONTINUOUS, var_name.str()); //add the variable associated to this arc to the model


					


				x_a[VarIndex(i, t, j, t_prime)] = new_arc;

				//cout << "Adding a new arc!Done!" << endl;
				//model.update();
				if (DEBUG) cout << "Change depot constraint!Done!" << endl;

				if (i == 0 && t == G.e[0])
				{
					ostringstream depotOutConstraint;
					depotOutConstraint << "DepotOutConstraint";
					
					newConstraints.insert(depotOutConstraint.str());

					if (constraintSet.find(depotOutConstraint.str()) == constraintSet.end())
						constraintSet[depotOutConstraint.str()] = model.getRow(model.getConstrByName(depotOutConstraint.str()));
					constraintSet[depotOutConstraint.str()] += new_arc;
				}

				if (DEBUG) cout << "Change   flow constraint from (i,t) !" << endl;


				if (i != 0 || (t != G.e[0] && t != G.l[0]))
				{
					//modified  constraint related to node (i,t)
					ostringstream flowConstraint1;
					flowConstraint1 << "FlowConstraint_" << i << "." << t;

					newConstraints.insert(flowConstraint1.str());

					if (constraintSet.find(flowConstraint1.str()) == constraintSet.end())
						constraintSet[flowConstraint1.str()] = model.getRow(model.getConstrByName(flowConstraint1.str()));
					constraintSet[flowConstraint1.str()] += new_arc;

				}

				if (DEBUG) cout << "Change   flow constraint from (j,t') !" << endl;
				//cout << "Change 1st flow constraint!Done!" << endl;
				if (j != 0 || (t_prime != G.e[0] && t_prime != G.l[0]))
				{
					ostringstream flowConstraint2;
					flowConstraint2 << "FlowConstraint_" << j << "." << t_prime;

					newConstraints.insert(flowConstraint2.str());

					if (constraintSet.find(flowConstraint2.str()) == constraintSet.end())
						constraintSet[flowConstraint2.str()] = model.getRow(model.getConstrByName(flowConstraint2.str()));

					constraintSet[flowConstraint2.str()] -= new_arc;
				}


				//cout << "Change 2nd flow constraint!Done!" << endl;
				//cout << "changed visited once constraint at " << i<< endl;
				ostringstream visitedOnceConstraint;
				visitedOnceConstraint << "visitedOnceConstraint_" << i;

 				newConstraints.insert(visitedOnceConstraint.str());

				if (constraintSet.find(visitedOnceConstraint.str()) == constraintSet.end())
					constraintSet[visitedOnceConstraint.str()] = model.getRow(model.getConstrByName(visitedOnceConstraint.str()));
				constraintSet[visitedOnceConstraint.str()] += new_arc;
				//cout << "Change visited once constraint!Done!" << endl;

			//	//update subtour constraints
			//	if (i != 0 && j!= 0 && G.tau[i][j]+G.tau[j][i]<1e6)
			//	{
			//		ostringstream subTour;
			//		subTour << "SubTour_" << min(i, j) << "." << max(i, j);

			//		newConstraints.insert(subTour.str());

			//		if (constraintSet.find(subTour.str()) == constraintSet.end())
			//			constraintSet[subTour.str()] = model.getRow(model.getConstrByName(subTour.str()));

			//		constraintSet[subTour.str()] += new_arc;
			//	}


					//update subtour constraints
				if (MIP)
					if (i != 0 && j!= 0)
					{
						ostringstream subTour;

						if (t_prime >= t && allSubTour.find(make_pair(i,t)) !=allSubTour.end())
						{
							subTour << "NoSubTour_" << i << "." << t;

							newConstraints.insert(subTour.str());
							try
							{
								if (constraintSet.find(subTour.str()) == constraintSet.end())
									constraintSet[subTour.str()] = model.getRow(model.getConstrByName(subTour.str()));
							}
							catch (GRBException e)
							{
								;
							}

							constraintSet[subTour.str()] += new_arc;
						}

						if (t_prime <= t)
						{
							subTour << "NoSubTour_" << j << "." << t_prime;

							newConstraints.insert(subTour.str());

							try
							{
								if (constraintSet.find(subTour.str()) == constraintSet.end())
									constraintSet[subTour.str()] = model.getRow(model.getConstrByName(subTour.str()));
							}
							catch (GRBException e)
							{
								;
							}

							constraintSet[subTour.str()] += new_arc;

						}
					}
			}

			model.update();

 
			//cout << "Number of new constraints: " << newConstraints.size() << endl;
			//cout << "Adding new variables!Done!" << endl;
		 

			for (set<string>::iterator it = newConstraints.begin(); it != newConstraints.end(); it++)
			{
				string cons_name = *it;

				try
				{
					GRBConstr rem_cons = model.getConstrByName(cons_name);

					model.remove(rem_cons);

				}
				catch (GRBException e)
				{
					;
				}

				if (cons_name[0] == 'D')
					model.addConstr(constraintSet[cons_name] == 1, cons_name);
				else if (cons_name[0] == 'F')
					model.addConstr(constraintSet[cons_name] == 0, cons_name);
				else if (cons_name[0] == 'v')
					model.addConstr(constraintSet[cons_name] == 1, cons_name);
				else if (cons_name[0] == 'S')
					model.addConstr(constraintSet[cons_name] <= 1, cons_name);
				else if (cons_name[0] == 'N')
					model.addConstr(constraintSet[cons_name] <= 1, cons_name);
				else cout << "Something wrong!" << endl;

				//cout << "Done add new constraint" << endl;

			}
			model.update();
			//cout << "****************************************************************************" << endl;
		}

		catch (GRBException e) {
			model.update();
			model.write("model_in.lp");
			cout << "Error code in addNodeArcToModel " << e.getErrorCode() << endl;
			cout << e.getMessage() << endl;
			exit(0);
		}
		catch (...) {
			cout << "Exception during optimization" << endl;
			/*return false;*/
		}
	}


	/**********************************************************Build Cycles from Selected Arcs******************************************************************/
	bool buildCycles(vector<VarIndex> selectedArcs, vector<vector<NODE> > &cycles)
	{
		bool *mark = new bool[selectedArcs.size() + 1];

		for (int k = 0; k < selectedArcs.size(); k++) mark[k] = false;

		sort(selectedArcs.begin(), selectedArcs.end(), varIndexCmp);

		for (int k = 0; k < selectedArcs.size(); k++)
			if (mark[k] == false)
			{
				//cout << k << endl;

				mark[k] = true;

				int i = selectedArcs[k].i;
				int t = selectedArcs[k].t;
				int j = selectedArcs[k].j;
				int t_prime = selectedArcs[k].t_prime;

				int ii = j, tt = t_prime;

				vector<NODE> curCycle;
				curCycle.push_back(NODE(i, t));
				curCycle.push_back(NODE(j, t_prime));

				while (true)
				{
					vector<VarIndex>::iterator pos = lower_bound(selectedArcs.begin(), selectedArcs.end(), VarIndex(ii, tt, 0, 0), varIndexCmp);

					if (pos == selectedArcs.end()) break; //no cycle

					VarIndex varIndex = *pos;
					if (varIndex.i != ii || varIndex.t != tt) break;

					ii = varIndex.j;
					tt = varIndex.t_prime;

					curCycle.push_back(NODE(ii, tt));

					mark[pos - selectedArcs.begin()] = 1;

					if (ii == i && tt == t) break; //found a cycle


				}

				//sort(curCycle.begin(), curCycle.end(), orderedbyTimeNode);

				if (curCycle[0].first != curCycle[curCycle.size() - 1].first)
				{
					cout << "Not a cycles!!!!!!!!!!!!!!!!!!!!!!!!" << endl;
					return 0;
				}
				cycles.push_back(curCycle);

			}
		
		return 1;
	}

	
	bool buildCycles2(vector<VarIndex> selectedArcs, vector<vector<NODE> > &cycles)
	{
		cout << "Cycle extraction in buildCycles2" << endl;
		bool *mark = new bool[selectedArcs.size() + 1];

		for (int k = 0; k < selectedArcs.size(); k++) mark[k] = false;

		sort(selectedArcs.begin(), selectedArcs.end(), varIndexCmp);

		
		usedArcs.clear();

		for (int k = 0; k < selectedArcs.size(); k++)
			if (mark[k] == false)
			{
				//cout << "New cycle:" << endl;

				mark[k] = true;

				int i = selectedArcs[k].i;
				int t = selectedArcs[k].t;
				int j = selectedArcs[k].j;
				int t_prime = selectedArcs[k].t_prime;

				int ii = j, tt = t_prime;

				vector<NODE> curCycle;
				curCycle.push_back(NODE(i, t));
				curCycle.push_back(NODE(j, t_prime));

				//cout << "(" << i << "," << t << ")-(" << j << "," << t_prime << ")-";
				//usedArcs.insert(k);

				while (true)
				{
					vector<VarIndex>::iterator pos = lower_bound(selectedArcs.begin(), selectedArcs.end(), VarIndex(ii, tt, 0, 0), varIndexCmp);

					if (pos == selectedArcs.end()) break; //no cycle
					if (mark[pos - selectedArcs.begin()]) break;

					VarIndex varIndex = *pos;
					if (varIndex.i != ii || varIndex.t != tt) break;

					ii = varIndex.j;
					tt = varIndex.t_prime;

					 

					//cout << "(" << ii << "," << tt << ")-";


					curCycle.push_back(NODE(ii, tt));
	
					mark[pos - selectedArcs.begin()] = 1;

					if (ii == i && tt == t) break; //found a cycle

					 
				}

				//sort(curCycle.begin(), curCycle.end(), orderedbyTimeNode);

				cycles.push_back(curCycle);

			}

		return 1;
	}

	void smallCycleExtraction(vector<NODE> &path, vector<vector<NODE> > &cycles)
	{
		vector<NODE> cycle;

		cycle.push_back(*path.rbegin());

		path.pop_back();
		while (1)
		{
			cycle.push_back(*path.rbegin());
			path.pop_back();
			if (cycle[0].first == cycle.back().first && cycle[0].second == cycle.back().second)
				break;
		}

		cycles.push_back(cycle);

	}

	vector<int> cycleIndex;
	set<pair <int, int> > usedVertex;

	

	bool buildCyclesRelaxation(vector<VarIndex> selectedArcs, vector<vector<NODE> > &cycles)
	{
	//	cout << "IN buildCycles1 procedure" << endl;

		bool *mark = new bool[selectedArcs.size() + 1];

		for (int k = 0; k < selectedArcs.size(); k++) mark[k] = false;
		  
		sort(selectedArcs.begin(), selectedArcs.end(), varIndexCmp);

		bool usedArcs[10000];

		bool foundaCycle = true;

		for (int k = 0; k < selectedArcs.size(); k++)
			if (mark[k] == false)
			{
				//cout << k << endl;

				memset(usedArcs, 0, sizeof(usedArcs));
				cycleIndex.clear();
				usedVertex.clear();

				int i = selectedArcs[k].i;
				int t = selectedArcs[k].t;
				int j = selectedArcs[k].j;
				int t_prime = selectedArcs[k].t_prime;

				int ii = j, tt = t_prime;

				vector<NODE> curCycle;
				curCycle.clear();
				curCycle.push_back(NODE(i, t));
				curCycle.push_back(NODE(j, t_prime));

				
				usedArcs[k] = true;
				for (int p = 0; p < selectedArcs.size(); p++)
					usedArcs[p] = mark[p];
				 
				cycleIndex.push_back(k);
			
				usedVertex.insert(make_pair(j, t_prime));
			 
				//if (DEBUG) 
				//if (nbIters == DEBUGLINE)	cout << "Starting of a new cycle: (" << i << "," << t << ")-(" << j << "," << t_prime << ")-";
				
				foundaCycle = false;
				while (true)
				{	 
					int p = lower_bound(selectedArcs.begin(), selectedArcs.end(), VarIndex(ii, tt, 0, 0), varIndexCmp) - selectedArcs.begin();
				 
					//cout << p << " " << selectedArcs[p].i << " "<< selectedArcs[p].t << endl;
					while ((mark[p] == true || usedArcs[p] == true) && (arcValues[p]<0.0001) && selectedArcs[p].i == ii && selectedArcs[p].t == tt && p < selectedArcs.size())
						p++;
					
					if (selectedArcs[p].i != ii || selectedArcs[p].t != tt)
					{
						//cout << "Not found an end point when finding (" << ii << "," << tt << ")" << endl;
						//cout << "The amount of flow: ";
						//for (int p = 0; p < selectedArcs.size(); p++)
						//	if (selectedArcs[p].i == ii && selectedArcs[p].t == tt)
						//		cout << arcValues[p] << endl;
						////exit(0);
						globalChange = true;
						break;
					}
						
					 
					//assert(mark[p] == false && p!= selectedArcs.size());
					assert(selectedArcs[p].i == ii && selectedArcs[p].t == tt);
					assert(arcValues[p] >= 0.0001);

					usedArcs[p] = true;
					cycleIndex.push_back(p);

					VarIndex varIndex = selectedArcs[p];
		
					ii = varIndex.j;
					tt = varIndex.t_prime;

					//if (DEBUG) 
					//if (nbIters == DEBUGLINE)
					//	cout << "(" << ii << "," << tt << ")-";

					curCycle.push_back(NODE(ii, tt));

					if (ii == i && tt == t)
					{
//						cout << endl;
						foundaCycle = true;
						break; //found a cycle
					}

					if ((usedVertex.find(make_pair(ii, tt)) != usedVertex.end())) //have a cycle
					{
						//cout <<endl<< "Found a sub cycle: ";
						smallCycleExtraction(curCycle,	 cycles); //extract that cycle

						vector<int> thisCycleIndex;
						double cycleFlow = 1e6;
						for (int i = 0; i + 1 < cycles.back().size(); i++)
						{
							
							thisCycleIndex.push_back(cycleIndex.back()), cycleIndex.pop_back();
							usedVertex.erase(cycles.back()[i]);
							cycleFlow = min(cycleFlow, arcValues[thisCycleIndex.back()]);
						}


						reverse(cycles.back().begin(), cycles.back().end());
						//reverse(thisCycleIndex.begin(), thisCycleIndex.end());
						 
						//for (int i = 0; i < cycles.back().size(); i++)
						//{
						//	cout << "(" << cycles.back()[i].first << "," <<  cycles.back()[i].second << ")-";
						//	
						//}
						//cout << " with flow: " << cycleFlow << endl;

						//cout << "Number of vertices of the subcycle:" << cycles.back().size() << endl;
						//cout << "Number of arcs of the subcycle:" << thisCycleIndex.size() << endl;

						for (int i = 0; i < thisCycleIndex.size(); i++)
						{
							arcValues[thisCycleIndex[i]] -= cycleFlow;
							if (arcValues[thisCycleIndex[i]] < 0.0001)
								mark[thisCycleIndex[i]] = true;
							usedArcs[thisCycleIndex[i]] = false;
						}
						
						//cout << "Con lai : ";
						//for (int i = 0; i < curCycle.size(); i++)
						//	cout << "(" << curCycle[i].first << "," << curCycle[i].second << ")-";
						//cout << endl;
						//cout << "Expand new arcs:";
						//
						////ii = curCycle.back().first;
						////tt = curCycle.back().second;
						//cout << "Starting with (" << ii << "," << tt << ")" << endl;
						
						curCycle.push_back(NODE(ii, tt));
						//cout << "here" << endl;
					}

					//if (nbIters==26) cout << "there aaaaaaaaaaa" << endl;
					usedVertex.insert(make_pair(ii, tt));
					 
				}

				//sort(curCycle.begin(), curCycle.end(), orderedbyTimeNode);

				//if (curCycle[0].first != curCycle[curCycle.size() - 1].first)
				//{
				//	cout << "Not a cycles!!!!!!!!!!!!!!!!!!!!!!!!" << endl;
				//	return 0;
				//}
				 
				if (foundaCycle)
				{
					double flow = 1e6;
					for (int i = 0; i < cycleIndex.size(); i++)
						flow = min(flow, arcValues[cycleIndex[i]]);

					for (int i = 0; i < cycleIndex.size(); i++)
					{
						arcValues[cycleIndex[i]] -= flow;
						if (arcValues[cycleIndex[i]] <= 0.0001)
						{
							mark[cycleIndex[i]] = true;
							arcValues[cycleIndex[i]] = 0.0;
						}

					}
					//cout << "New cycle from start:";
					//for (int i = 0; i < curCycle.size(); i++)
					//{
					//	cout << "(" << curCycle[i].first << "," << curCycle[i].second << ")-";

					//}
					//
					//cout << " with flow = " << flow << endl;

					cycles.push_back(curCycle);
				}

			}

		return 1;
	}

	//bool buildCyclesRelaxation(vector<varInfo> selectedVars,vector<VarIndex> selectedArcs, vector<vector<NODE> > &cycles)
	//{
	//	bool *mark = new bool[selectedArcs.size() + 1];

	//	for (int k = 0; k < selectedArcs.size(); k++) mark[k] = false;

	//	sort(selectedVars.begin(), selectedVars.end(), cmpVarInfo);

	//	sort(selectedArcs.begin(), selectedArcs.end(), varIndexCmp);

	//	int usedIndex[MAXN];

	//	for (int kk = 0; kk < selectedVars.size(); kk++)
	//		if (selectedVars[kk].val)
	//		{
	//			//cout << k << endl;
	//			memset(usedIndex, 0, sizeof(usedIndex)); 

	//			//mark[k] = true;

	//			int k = selectedVars[kk].id;

	//			usedIndex[k] = 1;
	//			

	//			int i = selectedArcs[k].i;
	//			int t = selectedArcs[k].t;
	//			int j = selectedArcs[k].j;
	//			int t_prime = selectedArcs[k].t_prime;

	//			int ii = j, tt = t_prime;

	//			vector<NODE> curCycle;
	//			curCycle.push_back(NODE(i, t));
	//			curCycle.push_back(NODE(j, t_prime));

	//			cout << "(" << i << "," << t << ")-(" << j << "," << t_prime << ")-"<<k;
	//			
	//			bool alreadyUsed = false;
	//			vector<int> arcIndex;
	//			
	//			arcIndex.push_back(k);
	//			double flow = arcValues[k];
	//			

	//			while (true)
	//			{
	//				vector<VarIndex>::iterator pos = lower_bound(selectedArcs.begin(), selectedArcs.end(), VarIndex(ii, tt, 0, 0), varIndexCmp);
	//				
	//				if (pos == selectedArcs.end()) break; //no cycle
	//				
	//				
	//				while (pos->i == ii && pos->t == tt && (usedIndex[pos - selectedArcs.begin()] == 1 || mark[pos - selectedArcs.begin()] == 1) && pos != selectedArcs.end())
	//					pos++;
	//					
	//				if (pos == selectedArcs.end() || pos->i !=ii || pos->t !=tt)
	//				{
	//					cout << "Recheck the code" << endl;
	//					alreadyUsed = true; 
	//					break;
	//				}

	//				arcIndex.push_back(pos - selectedArcs.begin());
	//				usedIndex[pos - selectedArcs.begin()] = 1;

	//				flow = min(flow, arcValues[pos - selectedArcs.begin()]);

	//				VarIndex varIndex = *pos;
	//				if (varIndex.i != ii || varIndex.t != tt) break;

	//				ii = varIndex.j;
	//				tt = varIndex.t_prime;
	//				cout << "(" << ii << ',' << tt << ")-" << pos - selectedArcs.begin();
	//				curCycle.push_back(NODE(ii, tt));

	//				mark[pos - selectedArcs.begin()] = 1;

	//				if (ii == i && tt == t) break; //found a cycle


	//			}
	//			cout << "Het"<<endl;
	//			//sort(curCycle.begin(), curCycle.end(), orderedbyTimeNode);

	//			//if (alreadyUsed == false && curCycle[0].first != curCycle[curCycle.size() - 1].first)
	//			//{
	//			//	cout << "Not a cycles!!!!!!!!!!!!!!!!!!!!!!!!" << endl;
	//			//	return 0;
	//			//}

	//			//if (alreadyUsed == false)
	//			cycles.push_back(curCycle);
	//			cout << "Flow : "<<flow << endl;
	//			for (int i = 0; i < arcIndex.size(); i++)
	//			{
	//				arcValues[arcIndex[i]] -= flow;
	//				if (arcValues[arcIndex[i]] == 0.0)
	//					mark[arcIndex[i]] = true;
	//			}
	//		}

	//	return 1;
	//}

	void earliestFirst(vector < vector<NODE> > &cycles)
	{
		for (int k = 0; k < cycles.size(); k++)
		{
			if (cycles[k][0].first == cycles[k][cycles[k].size() - 1].first && cycles[k][0].second == cycles[k][cycles[k].size() - 1].second)
			{
				int pp = 0;
				for (int p = 1; p < cycles[k].size(); p++)
					if (cycles[k][p].second < cycles[k][pp].second)
						pp = p;

				if (pp == 0) continue;
				cycles[k].erase(cycles[k].begin());

				for (int p = 1; p < pp; p++)
				{
					cycles[k].push_back(cycles[k][0]);
					cycles[k].erase(cycles[k].begin());
				}

				cycles[k].push_back(cycles[k][0]);
			}
		}
	}

	/**********************************************************Checking time window function******************************************************************/
	int travellingTimeWindowCondition(vector<NODE>  &cycle)
	{

		
		double curTime = G.e[0];

		for (int idx = 1; idx + 1 < cycle.size(); idx++)
		{
			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			if (curTime + G.rtau[i][j] > G.l[j]) //violation of time windows at node j
			{
				//lengthen it? it is not true ...
				cout << "Arrive too late at terminal " << j << " indexed "<< idx<<endl;
				return idx;
				 

			}
			else
				curTime = max(curTime + G.rtau[i][j], (double)G.e[j]);
		}
		return -1;
	}

	int firstNonLiftedNode(vector<NODE>  &cycle)
	{
		int curTime = cycle[0].second;

		for (int idx = 1; idx + 1 < cycle.size(); idx++)
		{
			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			if (curTime > t_prime) //still not lifted yet
			{
				return idx;
			}
			else
				curTime = max(curTime + G.tau[i][j], G.e[j]);
		}
		return -1;
	}
	int firstViolatedNode(vector<NODE>  &cycle)
	{
		int curTime = cycle[0].second;

		for (int idx = 1; idx < cycle.size(); idx++)
		{
			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			if (curTime + G.tau[i][j] > G.l[j])
				return idx;
			
			curTime = max(curTime + G.tau[i][j], G.e[j]);
		}
		return -1;
	}


	/**********************************************************Constraints to handle violation time-windows******************************************************************/
	void addTimeWindowsViolationConstraint(vector<NODE> &cycles, int terminalIndex)
	{
		try{
			cout << "Adding time window constraint " << endl;
			GRBLinExpr timeWindowCon = 0;
			bool noSubTour = false;
			for (int idx = 1; idx <= terminalIndex; idx++)
			{
				int i = cycles[idx - 1].first;
				int t = cycles[idx - 1].second;
				int j = cycles[idx].first;
				int t_prime = cycles[idx].second;

				timeWindowCon += x_a[VarIndex(i, t, j, t_prime)];
			}


			cout << "Is adding a new time window constraint" << endl;

			ostringstream timeWindowCons;
			timeWindowCons << "TimeWindow_" << cycles[0].first << "." << cycles[terminalIndex].first;
			model.addConstr(timeWindowCon <= terminalIndex - 1, timeWindowCons.str());


			model.update();
		}

		catch (GRBException e) {
			cout << "Error code = " << e.getErrorCode() << "in addTimeWIndowsViolationConstraint" << endl;
			cout << e.getMessage() << endl;
			exit(0);
		}
		catch (...) {
			cout << "Exception during optimization" << endl;
			/*return false;*/
		}
	}

	//void updateSubTourLength2Constraints(set<VarIndex > &newArcs)
	//{

	//	try{

	//		map<string, GRBLinExpr > mSubToursLength2;
	//		constraintSetST.clear();

	//		for (int i = 1; i < G.N0; i++)
	//			for (int j = i + 1; j < G.N0; j++)
	//				if (G.tau[i][j] + G.tau[j][i] < 1e6)
	//			{
	//				ostringstream subTour;
	//				subTour << "SubTour_" << i << "." << j;
	//				//cout << subTour.str() << endl;
	//				//mSubToursLength2[subTour.str()] = model.getRow(model.getConstrByName(subTour.str()));
	//				constraintSetST[subTour.str()] = model.getRow(model.getConstrByName(subTour.str()));
	//				model.remove(model.getConstrByName(subTour.str()));
	//			}

	//		model.update();
	//		//cout << "Size" << newArcs.size()<< endl;
	//		for (set<VarIndex>::iterator it = newArcs.begin(); it != newArcs.end(); it++)
	//		{

	//			//assert(x_a.find(*it) != x_a.end());

	//			int i = min(it->i, it->j);
	//			int j = max(it->i, it->j);
	//			
	//			if (i == j) continue; 
	//			ostringstream subTour;
	//			subTour << "SubTour_" << i << "." << j;

	//			//mSubToursLength2[subTour.str()] += x_a[*it];
	//			constraintSetST[subTour.str()] += x_a[*it];
	//		}

	//		//for (map<string, GRBLinExpr>::iterator it = mSubToursLength2.begin(); it != mSubToursLength2.end(); it++)
	//			//model.addConstr(it->second <= 1, it->first);

	//		for (map<string, GRBLinExpr>::iterator it = constraintSetST.begin(); it != constraintSetST.end(); it++)
	//			model.addConstr(it->second <= 1, it->first);

	//		model.update();
	//	}
	//	catch (GRBException e) {
	//		cout << "Error code = " << e.getErrorCode() << "in updateSubTourLength2Constraints" << endl;
	//		cout << e.getMessage() << endl;
	//		exit(0);
	//	}
	//	catch (...) {
	//		cout << "Exception during optimization" << endl;
	//		/*return false;*/
	//	}
	//}

	void updateSubTourLength2ConstraintsVarName(map<VarIndex ,string > &newArcNames)
	{

		try{

 			constraintSetST.clear();

			for (int i = 1; i < G.N0; i++)
				for (int j = i + 1; j < G.N0; j++)
					if (G.tau[i][j] + G.tau[j][i] < 1e6)
					{
						ostringstream subTour;
						subTour << "SubTour_" << i << "." << j;

						//cout << subTour.str() << endl;

						constraintSetST[subTour.str()] = model.getRow(model.getConstrByName(subTour.str()));

						model.remove(model.getConstrByName(subTour.str()));
					}

			model.update();
 	 
			for (map<VarIndex, string>::iterator it = newArcNames.begin(); it != newArcNames.end(); it++ )
			{

				//assert(x_a.find(*it) != x_a.end());

				int i = min((it->first).i, (it->first).j);
				int j = max((it->first).i, (it->first).j);

				if (i == j) 
					continue;
				ostringstream subTour;
				
				subTour << "SubTour_" << i << "." << j;
				constraintSetST[subTour.str()] += model.getVarByName(it->second);
				
			}

			for (map<string, GRBLinExpr>::iterator it = constraintSetST.begin(); it != constraintSetST.end(); it++)
				model.addConstr(it->second <= 1, it->first);

			model.update();
		}
		catch (GRBException e) {
			cout << "Error code = " << e.getErrorCode() << "in updateSubTourLength2ConstraintsVarName" << endl;
			cout << e.getMessage() << endl;
			exit(0);
		}
		catch (...) {
			cout << "Exception during optimization" << endl;
			/*return false;*/
		}
	}

	void preprocessingPrecedenceConstraints(OriginalGraph &G)
	{
		for (int i = 1; i < G.N0; i++)
			G.pred[0][i] = 1;
		
		bool nochange;
		//for (;;)
		{
			nochange = false;

			for (int i = 0; i < G.N0; i++)
				for (int j = 0; j < G.N0; j++)
					if (G.e[j] + G.tau[j][i] > G.l[i])
						if (G.pred[i][j] != 1)
							nochange = G.pred[i][j] = 1;

			bool change = true;
			while (change)
			{
				change = false;
				for (int i = 0; i < G.N0; i++)
					for (int j = 0; j < G.N0; j++)
						if (G.pred[i][j] == 1)
							for (int k = 0; k < G.N0; k++)
								if (G.pred[j][k] == 1)
									if (G.pred[i][k] == 0)
										nochange = change = G.pred[i][k] = 1;
			}


			//for (int i = 0; i < G.N0; i++)
			//	for (int j = 0; j < G.N0; j++)
			//	{
			//		bool b=true;
			//		for (int k = 0; k < G.N0; k++)
			//			if (k != i && k != j)
			//			{
			//				bool b1 = G.pred[k][i] | G.pred[k][j] | G.e[i] + G.tau[i][j] + G.tau[j][k] > G.l[k];
			//				bool b2 = G.pred[i][k] | G.pred[j][k] | G.e[k] + G.tau[k][i] + G.tau[i][j] > G.l[j];
			//				b = b & b1 & b2;
			//			}
			//		if (b)
			//			G.tau[i][j] = 1e6;

			//	}

			for (int i = 1; i < G.N0; i++)
				for (int j = 1; j < G.N0; j++)
					if (G.pred[i][j])
						G.rtau[j][i] = G.tau[j][i] = 1e6;

			for (int i = 0; i < G.N0; i++)
				for (int j = 0; j < G.N0; j++)
					if (G.l[i] <= G.e[j])
						for (int k = 0; k < G.N0; k++)
							if (G.l[i] <= G.e[k] && G.l[k] <= G.e[j])
							{

								G.tau[i][j] = 1e6;
								break;
							}

			for (int i = 0; i < G.N0; i++)
				for (int j = 0; j < G.N0; j++)
					if (i != j)
						for (int k = 0; k < G.N0; k++)
							if (i != k && j != k)
								if (G.pred[i][j] && G.pred[j][k])
									G.rtau[i][k] = G.tau[i][k] = 1e6;

			for (int i = 1; i < G.N0; i++)
				for (int j = 1; j < G.N0; j++)
					if (G.pred[i][j])
						G.pred[0][j] = 1, G.tau[i][0] = G.rtau[i][0] = G.rtau[0][j] = G.tau[0][j] = 1e6;

			do
			{
				bool change = false;
				for (int i = 1; i < G.N0; i++)
				{
					int vmin = 1e9;
					for (int j = 0; j < G.N0; j++)
						if (i != j && G.tau[j][i] != 1e6)
							vmin = min(vmin, G.e[j] + G.tau[j][i]); //find earliest possible arrive from j to i 
					if (G.e[i] < min(G.l[i], vmin))
						nochange = change = true, G.e[i] = max(G.e[i], min(G.l[i], vmin)); //- increase e[i] if possible

					vmin = 1e9;
					for (int j = 0; j < G.N0; j++)
						if (i != j && G.tau[i][j] != 1e6)
							vmin = min(vmin, G.e[j] - G.tau[i][j]); //find earliest possible departure from j to i 
					if (G.e[i] < min(G.l[i], vmin))
						nochange =  change = true, G.e[i] = max(G.e[i], min(G.l[i], vmin)); //- increase e[i] if possible


					int vmax = 0;
					for (int j = 0; j < G.N0; j++)
						if (i != j && G.tau[j][i] != 1e6)
							vmax = max(vmax, G.l[j] + G.tau[j][i]); //lastest possible arrive time point from j to i -

					if (G.l[i] > max(G.e[i], vmax))
						nochange =  change = true, G.l[i] = min(G.l[i], max(G.e[i], vmax)); // decrease l[i] if posible

					vmax = 0;
					for (int j = 0; j < G.N0; j++)
						if (i != j && G.tau[i][j] != 1e6)
							vmax = max(vmax, G.l[j] - G.tau[i][j]); //find latest departure time from i to j - 

					if (G.l[i] > max(G.e[i], vmax))
						nochange = change = true, G.l[i] = min(G.l[i], max(G.e[i], vmax)); // decrease l[i] if possible
				}
				if (change == false)
					break;
			} while (1);

			if (nochange == false)
				;
		}


	}

}
#endif