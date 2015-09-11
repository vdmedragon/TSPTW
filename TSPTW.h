
//http://stackoverflow.com/questions/10046485/error-lnk2005-already-defined

#ifndef MY_TSPTW
#define MY_TSPTW

#include "gurobi_c++.h"
#include <vector>
#include <set>
#include <map>
#include <sstream>
#include <algorithm>

using std::cout;

using namespace std;

#define MAXN 222

struct OriginalGraph
{
	int N0; //number of vertices;
	int tau[MAXN][MAXN]; //distance matrix
	int e[MAXN], l[MAXN]; //time windows
};

#define NODE pair<int, int>
#define S_IT set<int>::iterator 
#define M_NODE_S_NODE_IT map<NODE, set <NODE> >::iterator

struct PartialTimeExpandedGraph{
	int N0;
	set<int> NT[MAXN]; //for each terminal i, we associate with i set of time t that node i_t is in the set of N_T
	map<NODE, set <NODE> > AT; //we associate with each node (i,t) in N_T, a set of nodes (j,t') associated with it; that means; the arc (i,t) - (j,t') is in A_T
};

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
};
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

/**********************************************************Global variable information section******************************************************************/

namespace
{
	//graph information
	OriginalGraph G;
	PartialTimeExpandedGraph PTEG;

	//model and variable decleration 
	GRBEnv *env = new GRBEnv();
	GRBModel model(*env);

	map<VarIndex, GRBVar> x_a;
	map<string, GRBLinExpr> constraintSet;

	vector<VarIndex> deletedVarList;
	vector<VarIndex> addedVarList;
	vector<NODE> addedNodeList;

	bool subTourElimination = false;



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
				G.tau[i][j] = G.tau[j][i] = dist;
			}

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
			cout << G.e[i] << " " << G.l[i] << endl;
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

	void REFINE(int i, int t_new, OriginalGraph &G, PartialTimeExpandedGraph &PTEG, vector<NODE> &addedNodeList, vector<VarIndex> &addedVarList, vector<VarIndex> &deletedVarList)
	{
		//add new node
		std::pair<std::set<int>::iterator, bool> loc = PTEG.NT[i].insert(t_new); //location of new added node
		if (loc.second == false) return;

		//assert(loc.second == true);//fail nghia la dinh nay da duoc them vao
		addedNodeList.push_back(NODE(i, t_new));

		//prev and succ node
		S_IT cur = loc.first;
		S_IT prev = cur; prev--;
		S_IT next = cur; next++;

		assert(next != PTEG.NT[i].end());


		int t_k = *prev;
		int t_k_plus_one = *next;

		//remove the holding arc (i,t_k) - (i,t_k_plus_one) - step 2
		NODE prev_node = make_pair(i, t_k);
		NODE succ_node = make_pair(i, t_k_plus_one);

		PTEG.AT[prev_node].erase(succ_node);

		deletedVarList.push_back(VarIndex(i, t_k, i, t_k_plus_one)); //remove the corresponding variable from the model

		//new node associated to new time point - step 2
		NODE new_node = make_pair(i, t_new);

		//adding two new holding arcs
		PTEG.AT[prev_node].insert(new_node);
		PTEG.AT[new_node].insert(succ_node);
		addedVarList.push_back(VarIndex(i, t_k, i, t_new)); //will be adding these two new variables associated with these two holding arcs
		addedVarList.push_back(VarIndex(i, t_new, i, t_k_plus_one));

		//adding new crossing arcs from new added node - step 3

		for (set<NODE>::iterator jt_node_it = PTEG.AT[prev_node].begin(); jt_node_it != PTEG.AT[prev_node].end(); jt_node_it++)
		{
			NODE jt_node = *jt_node_it;
			PTEG.AT[new_node].insert(jt_node);

			int j = jt_node.first;
			int t = jt_node.second;

			addedVarList.push_back(VarIndex(i, t_new, j, t)); //will be adding new variables associated with these crossing arcs
		}
	}


	//Algorithm 5: RESTORE -  restore longest-feasible-arc property
	//restore the longest-feasible-arc property related to the new added node (i,t_new) to the partially time expanded graph PTEG
	//addedVarList will contain list of being added arcs/variables related to new added nodes during the restoration function
	//deletedVarList will contain list of being removed arcs/variables related to new added/nodes during the restoration function

	void RESTORE(int i, int t_new, OriginalGraph &G, PartialTimeExpandedGraph &PTEG, vector<VarIndex> &addedVarList, vector<VarIndex> &deletedVarList)
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

			S_IT succ_tprime_it = PTEG.NT[j].upper_bound(t_new + G.tau[i][j]); //line 2, find successor of t'
			S_IT t_prime_it = --succ_tprime_it; //t' now

			int t_prime = *t_prime_it;

			if (t_prime != t) //line 3
			{
				PTEG.AT[new_node].erase(jt_node); //erase old arc related to new_node line 4

				deletedVarList.push_back(VarIndex(i, t_new, j, t)); //will remove associated variable from the model

				NODE jtprime_node = make_pair(j, t_prime);

				PTEG.AT[new_node].insert(jtprime_node); //arc new arc related to new_node to enforce longest_feasiblity_path property

				addedVarList.push_back(VarIndex(i, t_new, j, t_prime)); //will add associated variable to the model
			}
		}

		for (map<NODE, set<NODE> >::iterator jt_node_it = PTEG.AT.begin(); jt_node_it != PTEG.AT.end(); jt_node_it++) //line 7
		{
			NODE jt_node = jt_node_it->first;
			set<NODE> s_jt = jt_node_it->second;

			int t = jt_node.second;
			int j = jt_node.first;

			if (t + G.tau[j][i] >= t_new) //line 7 condition; the distance between two terminals is not so long
				if (s_jt.find(prev_node) != s_jt.end()) //if there is an arc from jt-node to the prev node; replace with the new arc to enforce longest_ feasible_path
				{
					PTEG.AT[jt_node].erase(prev_node);

					deletedVarList.push_back(VarIndex(j, t, i, t_k)); //will remove the variable associated with this arc from the model

					PTEG.AT[jt_node].insert(new_node);

					addedVarList.push_back(VarIndex(j, t, i, t_new)); //will add the variable associated with this arc to the model
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

	void ADD_ARC(int i, int t, int j, int t_prime, OriginalGraph &G, PartialTimeExpandedGraph &PTEG, vector<NODE> &addNodeList, vector<VarIndex> &addedVarList, vector<VarIndex> &deletedVarList)
	{
		
		PTEG.NT[j].insert(t_prime); //new time point

		addedVarList.push_back(VarIndex(i, t, j, t_prime));


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

					ostringstream var_name;
					var_name << "x(" << i << "," << t << ")(" << j << "," << t_prime << ")";

					GRBVar new_arc = model.addVar(0.0, 1.0, 0.0, GRB_BINARY, var_name.str()); //add the variable associated to this arc to the model

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

				(varIndex_it->second).set(GRB_DoubleAttr_Obj, G.tau[i][j]);
			}
			// The objective is to minimize the total cost of arcs
			model.set(GRB_IntAttr_ModelSense, GRB_MINIMIZE);

			model.update();

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

			model.update();

			constraintSet[depotOutConstraint.str()] = depotOutExp;

			////Add 1st depot in constraint
			//NODE depotIn = make_pair(0, G.l[0]);
			//GRBLinExpr depotInExp = 0; //first set of constraint

			//for (map<NODE,set<NODE>>::iterator it_node_it = PTEG.AT.begin(); it_node_it != PTEG.AT.end(); it_node_it++)
			//{
			//	NODE it_node = it_node_it->first;
			//	int i = it_node.first;
			//	int t = it_node.second;

			//	if (i != 0)
			//	{
			//		set<NODE> s = it_node_it->second;
			//		if (s.find(NODE(0, G.l[0])) != s.end()) //(i,t) connects with (0,l[0])
			//			depotOutExp += x_a[VarIndex(i, t, 0, G.l[0])];
			//	}
			//		
			//}

			//ostringstream depotInConstraint;
			//depotInConstraint << "DepotInConstraint";
			//model.addConstr(depotInExp == 1, depotInConstraint.str());

			//model.update();

			//constraintSet[depotInConstraint.str()] = depotInExp;


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

					if (i != 0 || (t != G.e[0] && t != G.l[0])) flowBalanceConstraints[NODE(i, t)] += x_a[VarIndex(i, t, j, t_prime)];
					if (j != 0 || (t_prime != G.e[0] && t_prime != G.l[0]))   flowBalanceConstraints[NODE(j, t_prime)] -= x_a[VarIndex(i, t, j, t_prime)];
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

			model.update();

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
						visitedOnceExp += x_a[VarIndex(i, t, j, tprime)];

					}
				}

				visitedOnce.push_back(visitedOnceExp);

				ostringstream visitedOnceConstraint;
				visitedOnceConstraint << "visitedOnceConstraint_" << i;
				model.addConstr(visitedOnce[i] == 1, visitedOnceConstraint.str()); //each terminal is visited once

				constraintSet[visitedOnceConstraint.str()] = visitedOnce[i];
			}


			//update entire model
			model.update();

		}
		catch (GRBException e) {
			cout << "Error code = " << e.getErrorCode() << endl;
			cout << e.getMessage() << endl;
			return false;
		}
		catch (...) {
			cout << "Exception during optimization" << endl;
			return false;
		}

		return true;
	}

	/**********************************************************Build Cycles from Selected Arcs******************************************************************/
	void buildCycles(vector<VarIndex> selectedArcs, vector<vector<NODE>> &cycles)
	{
		bool *mark = new bool[selectedArcs.size() + 1];

		for (int k = 0; k < selectedArcs.size(); k++) mark[k] = false;

		sort(selectedArcs.begin(), selectedArcs.end(), varIndexCmp);

		for (int k = 0; k < selectedArcs.size(); k++)
			if (mark[k] == false)
			{
				cout << k << endl;

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

				cycles.push_back(curCycle);

			}
	}

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
	bool travellingTimeWindowCondition(vector<NODE>  &cycle, int &violatedTerminal)
	{

		
		int curTime = G.e[0];

		for (int idx = 1; idx + 1 < cycle.size(); idx++)
		{
			NODE prev = cycle[idx - 1];
			NODE cur = cycle[idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			if (curTime + G.tau[i][j] > G.l[j]) //violation of time windows at node j
			{
				//lengthen it? it is not true ...
				cout << "Arrive too late at terminal " << j << "indexed "<< idx<<endl;
				violatedTerminal = idx;
				return false;

			}
			else
				curTime = max(curTime + G.tau[i][j], G.e[j]);
		}
		return true;
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
			cout << "Error code = " << e.getErrorCode() << endl;
			cout << e.getMessage() << endl;
			/*	return false;*/
		}
		catch (...) {
			cout << "Exception during optimization" << endl;
			/*return false;*/
		}
	}

}
#endif