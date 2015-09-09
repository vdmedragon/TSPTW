/* Copyright 2014, Gurobi Optimization, Inc. */

/* This example formulates and solves the following simple MIP model:

     buildCycles    x +   y + 2 z
     subject to  x + 2 y + 3 z <= 4
                 x +   y       >= 1
     x, y, z binary
*/

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

 
//graph information
OriginalGraph G;
PartialTimeExpandedGraph PTEG;

//model information
GRBEnv *env = new GRBEnv();
GRBModel model(*env);

map<VarIndex, GRBVar> x_a;
map<string, GRBLinExpr> constraintSet;

vector<VarIndex> deletedVarList;
vector<VarIndex> addedVarList;
vector<NODE> addedNodeList;

bool subTourElimination = false;

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

	for (int i=0;;i++)
	{
		cin >> id >> x[i] >> y[i] >> d[i] >> rt[i] >> dt[i] >> st[i];
		G.e[i] = rt[i], G.l[i] = dt[i];
		if (id == 999) {
			G.N0 = i;
			break;
		}
	}

	for (int i = 0; i < G.N0; i++)
		for (int j = i+1; j < G.N0; j++)
		{
			double dist = sqrt((x[i] - x[j])*(x[i] - x[j]) + (y[i] - y[j])*(y[i] - y[j]));
			G.tau[i][j] = G.tau[j][i] = dist;
		}

	fclose(stdin);
}

void testReadingGraph(OriginalGraph &G)
{
	cout << "Number of terminal: "<<G.N0 << endl;

	for (int i = 0; i < G.N0; i++)
	{
		for (int j = 0; j < G.N0; j++)
			cout << G.tau[i][j]<<" ";
		cout << endl;
	}
	cout << "Time windows" << endl;
	for (int i = 0; i < G.N0; i++)
		cout << G.e[i] << " " << G.l[i] << endl;
}

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
				if (i != j)
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
void REFINE(int i, int t_new, OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
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
	
	deletedVarList.push_back(VarIndex(i, t_k, i, t_k_plus_one)); //remove this variable from the model
 
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
void RESTORE(int i, int t_new, OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
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
void LENGTHEN_ARC(int i, int t, int j, int t_prime, OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
{
 
	assert(t + G.tau[i][j] <= G.l[j]);
	
	REFINE(j, t + G.tau[i][j], G, PTEG); //add a new node named (j, t + G.tau[i][j]) to the partially network
	cout << "Finish added new arcs!Done!" << endl;
	RESTORE(j, t + G.tau[i][j], G, PTEG); //restore the longest-feasible-arc property
	cout << "Finish lengthen an old arc!Done!" << endl;
}

void subTourEliminationConstraint()
{
	try
	{ 
		map<NODE, GRBLinExpr> visitedOnceConstraints; //2nd set of constraint ; set of flow balance constraint, one of each node

		for (map<NODE, set<NODE> >::iterator it_node_it = PTEG.AT.begin(); it_node_it != PTEG.AT.end(); it_node_it++)
		{
			NODE it_node = it_node_it->first;
			set<NODE> s_it = it_node_it->second;

			int i = it_node.first;
			int t = it_node.second;

			if ((i == 0 && t == G.e[0]) || (i == 0 && t == G.l[0])) continue;

			//add the condition that each intermediate arc only have 
			for (set<NODE>::iterator jtprime_node_it = s_it.begin(); jtprime_node_it != s_it.end(); jtprime_node_it++)
			{
				NODE j_tprime_node = *jtprime_node_it;

				int j = j_tprime_node.first;
				int t_prime = j_tprime_node.second;

				if (t_prime >= t)
					visitedOnceConstraints[NODE(i, t)] += x_a[VarIndex(i, t, j, t_prime)]; //outgoing of (i,t), go up
				else
					visitedOnceConstraints[NODE(j, t_prime)] += x_a[VarIndex(i, t, j, t_prime)]; //incoming of (j,t_prime) go down

			}
		}

		for (map<NODE, set<NODE> >::iterator it_node_it = PTEG.AT.begin(); it_node_it != PTEG.AT.end(); it_node_it++) //line 7
		{
			NODE it_node = it_node_it->first;
			set<NODE> s_it = it_node_it->second;

			int i = it_node.first;
			int t = it_node.second;

			ostringstream visitedOnceConstraint;
			visitedOnceConstraint << "visitedOnceConstraint" << i << "." << t;
			model.addConstr(visitedOnceConstraints[NODE(i, t)] <= 1, visitedOnceConstraint.str()); //each terminal is visited at most 1 time.

		}
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

bool ModelGeneration(OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
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
				var_name << "x("<<i<<","<<t<<")("<<j<<","<<t_prime<<")";
				
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
		NODE depot = make_pair(0, G.e[0]);
		GRBLinExpr depotExp = 0; //first set of constraint
		
		for (set<NODE>::iterator jt_node_it = PTEG.AT[depot].begin(); jt_node_it != PTEG.AT[depot].end(); jt_node_it++)
		{
			NODE jt_node = *jt_node_it;
			int j = jt_node.first;
			int t = jt_node.second;

			//depotExp += x_aaa[mapOfIndices[VarIndex(0, G.e[0], j, t)]];
			depotExp += x_a[VarIndex(0, G.e[0], j, t)];
		}

		ostringstream depotConstraint;
		depotConstraint << "DepotConstraint";
		model.addConstr(depotExp == 1, depotConstraint.str());
		
		model.update();

		constraintSet[depotConstraint.str()] = depotExp;

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
					if (j!=0 || (t_prime != G.e[0] && t_prime!= G.l[0]))   flowBalanceConstraints[NODE(j, t_prime)] -= x_a[VarIndex(i, t, j, t_prime)];
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
			GRBLinExpr tmp = 0;
			for (set<int>::iterator t_it = PTEG.NT[i].begin(); t_it != PTEG.NT[i].end(); t_it++) //travese all time points t associated with i
			{
				int t = *t_it;
				NODE it_node = make_pair(i, t);

				for (set<NODE>::iterator j_tprime_it = PTEG.AT[it_node].begin(); j_tprime_it != PTEG.AT[it_node].end(); j_tprime_it++) //all nodes connected with (i,t)
				{
					NODE jt_node = *j_tprime_it;
					int j = jt_node.first;
					int tprime = jt_node.second;
						tmp += x_a[VarIndex(i, t, j, tprime)];
					 
				}
			}

			visitedOnce.push_back(tmp);

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


void modifyCurrentModel()
{
	//remove variables and update the model
	for (int i = 0; i < deletedVarList.size(); i++)
		model.remove(x_a[deletedVarList[i]]);

	model.update();

	//add new variables associated with new arcs and update the model
	for (int k = 0; k < addedVarList.size(); k++)
	{
		int i = addedVarList[k].i;
		int t = addedVarList[k].t;
		int j = addedVarList[k].j;
		int t_prime = addedVarList[k].t_prime;

		//extract flow constraint related to node (i,t)
		ostringstream flowConstraint;
		flowConstraint << "FlowConstraint_" << i << "." << t;

		GRBConstr curConstraint = model.getConstrByName(flowConstraint.str());
		GRBLinExpr curLinExpr = model.getRow(curConstraint);
	}
}

void resetModel(OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
{

	GRBConstr *Constr = model.getConstrs();
	int nbConstraints = model.get(GRB_IntAttr_NumConstrs);

	cout << "Number of constraints" << nbConstraints << endl;
	while (nbConstraints)
	{
		model.remove(Constr[nbConstraints - 1]);
		nbConstraints--;
		//cout << "Current number of constraints" << nbConstraint << endl;
	}

	model.update();

	cout << "Removing constraints! Done!" << endl;

	GRBVar *Var = model.getVars();
	int nbVars = model.get(GRB_IntAttr_NumVars);
	while (nbVars)
	{
		model.remove(Var[nbVars-1]);
		nbVars--;
	}

	cout << "Removing variables! Done!" << endl;
	
	model.update();

	model.setObjective(GRBLinExpr(0.0), GRB_MINIMIZE);

	cout << "Reset objective function!Done!" << endl;
	model.update();

	ModelGeneration(G, PTEG);
}

void resetModel(OriginalGraph &G, PartialTimeExpandedGraph &PTEG, vector<VarIndex> &deletedVarList, vector<VarIndex> &addedVarList,vector<NODE> &addedNodeList)
{
	try{
		cout << "Resetting a model" << endl;
		set<string> newConstraints;

		int ii = -1, tt = -1;
		if (addedNodeList.size())
			ii = addedNodeList[0].first, tt = addedNodeList[0].second;

		//add constraints related to the new node
		for (int k = 0; k < addedNodeList.size(); k++)
		{
			int i = addedNodeList[k].first;
			int t = addedNodeList[k].second;

			if (i == 0 && t == G.e[0])
				continue;

			ostringstream flowConstraint;
			flowConstraint << "FlowConstraint_" << i << "." << t;

			model.addConstr(GRBLinExpr(0.0) == 0, flowConstraint.str());
			
			newConstraints.insert(flowConstraint.str());

			constraintSet[flowConstraint.str()] = GRBLinExpr(0.0);
		}

		model.update();

		for (int k = 0; k < deletedVarList.size(); k++)
		{
			model.remove(x_a[deletedVarList[k]]); //remove variables from the model
			 
			x_a.erase(deletedVarList[k]); //remove variable from variables' list

			int i = deletedVarList[k].i;
			int t = deletedVarList[k].t;
			int j = deletedVarList[k].j;
			int t_prime = deletedVarList[k].t_prime;

			PTEG.AT[NODE(i, t)].erase(NODE(j, t_prime)); //remove arcs from arcs' list
		}

		model.update();

		//cout << " Remove old variables!Done!" << endl;

		for (int k = 0; k < addedVarList.size(); k++)
		{
			int i = addedVarList[k].i;
			int t = addedVarList[k].t;
			int j = addedVarList[k].j;
			int t_prime = addedVarList[k].t_prime;

			//if (ii == i && tt == t) cout << "Related new added nodes" << i<<"."<<t<< endl;

			ostringstream var_name;

			var_name << "x(" << i << "," << t << ")(" << j << "," << t_prime << ")";

			GRBVar new_arc = model.addVar(0.0, 1.0, G.tau[i][j], GRB_BINARY, var_name.str()); //add the variable associated to this arc to the model

			x_a[VarIndex(i, t, j, t_prime)] = new_arc;

			//cout << "Adding a new arc!Done!" << endl;

			if (i == 0 && t == G.e[0])
			{
				ostringstream depotConstraint;
				depotConstraint << "DepotConstraint";

				constraintSet[depotConstraint.str()] += new_arc;
				newConstraints.insert(depotConstraint.str());
			}

			//if (i != 0 || t != G.e[0])
			if (i != 0 || (t != G.e[0] && t!= G.l[0]))
			{
				//modified  constraint related to node (i,t)
				ostringstream flowConstraint1;
				flowConstraint1 << "FlowConstraint_" << i << "." << t;

				constraintSet[flowConstraint1.str()] += new_arc;
				newConstraints.insert(flowConstraint1.str());

				//GRBConstr curConstraint1 = model.getConstrByName(flowConstraint1.str());
				//GRBLinExpr curLinExpr1 = model.getRow(curConstraint1);
				//curLinExpr1 += new_arc;

			}


			//cout << "Change 1st flow constraint!Done!" << endl;
			//if (j != 0 || t_prime != G.e[0])
			if (j != 0 || (t_prime != G.e[0] && t_prime != G.l[0]))
			{
				ostringstream flowConstraint2;
				flowConstraint2 << "FlowConstraint_" << j << "." << t_prime;

				constraintSet[flowConstraint2.str()] -= new_arc;
				newConstraints.insert(flowConstraint2.str());

				//GRBConstr curConstraint2 = model.getConstrByName(flowConstraint2.str());
				//GRBLinExpr curLinExpr2 = model.getRow(curConstraint2);
				//curLinExpr2 -= new_arc;

			}


			//cout << "Change 2nd flow constraint!Done!" << endl;

			ostringstream visitedOnceConstraint;
			visitedOnceConstraint << "visitedOnceConstraint_" << i;

			constraintSet[visitedOnceConstraint.str()] += new_arc;
			newConstraints.insert(visitedOnceConstraint.str());

			//GRBConstr curConstraint3 = model.getConstrByName(visitedOnceConstraint.str());
			//GRBLinExpr curLinExpr3 = model.getRow(curConstraint3);
			//curLinExpr3 += new_arc;

			//cout << "Change visited once constraint!Done!" << endl;
		}

		model.update();

		return;

		cout << "Number of new constraints: "<<newConstraints.size() << endl;
		//cout << "Adding new variables!Done!" << endl;
		for (set<string>::iterator it = newConstraints.begin(); it != newConstraints.end(); it++)
		{
			string cons_name = *it;
			cout << "Current constraints:" << cons_name << endl;

			//if (cons_name[0] == 'D')
			//{
			//	cout << "Remove depot here" << endl;
			//	exit(0);
			//}
			GRBConstr rem_cons = model.getConstrByName(cons_name);

			model.remove(rem_cons);

			//model.update();

			if (cons_name[0] == 'D')
				model.addConstr(constraintSet[cons_name] == 1, cons_name);
			else if (cons_name[0] == 'F')
				model.addConstr(constraintSet[cons_name] == 0, cons_name);
			else if (cons_name[0] == 'v')
				model.addConstr(constraintSet[cons_name] == 1, cons_name);
			else cout << "Something wrong!" << endl;

			model.update();
		}
		
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

inline bool varIndexCmp(const VarIndex &a, const VarIndex &b)
{
	return (a.i < b.i || (a.i == b.i && a.t < b.t)); 
}

inline bool orderedbyTime(const VarIndex &a, const VarIndex &b)
{
	return (a.t < b.t || (a.t==b.t && a.i<b.i));
}

inline bool orderedbyTimeNode(const NODE &a, const NODE &b)
{
	return (a.second < b.second);
}

void buildCycles(vector<VarIndex> selectedArcs, vector<vector<NODE>> &cycles)
{
	bool *mark = new bool[selectedArcs.size()+1];

	for (int k = 0; k < selectedArcs.size(); k++) mark[k] = false;

	sort(selectedArcs.begin(), selectedArcs.end(), varIndexCmp);

	for (int k = 0; k < selectedArcs.size(); k++)
		if (mark[k]==false)
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

//check if the sum of used arcs' cost is equal to the objective value
bool totalCostCondition(vector<VarIndex> &selectedArcs)
{
	int totalCost = 0;
	int objVal = model.get(GRB_DoubleAttr_ObjVal);

	//check the total cost
	for (int k = 0; k < selectedArcs.size(); k++)
	{
		int i = selectedArcs[k].i;
		int j = selectedArcs[k].j;
		if (i != j)
		{
			totalCost += G.tau[i][j];
			//cout << i << " " << j << ":" << G.tau[i][j] << endl;
		}
	}
	return (totalCost == objVal);
}


bool visitedOnceCondition(vector<VarIndex> &selectedArcs)
{
 	int *mark = new int[G.N0 - 1];

	//check if the selected arcs are satisfied the condition that each terminal is visted exactly once
	for (int i = 0; i < G.N0; i++)
		mark[i] = 0;

	for (int k = 0; k < selectedArcs.size(); k++)
		if ((selectedArcs[k].i != selectedArcs[k].j) && mark[selectedArcs[k].j])
		{
			cout << " Terminal " << selectedArcs[k].j << " visted more than one time!" << endl;
			cout << " Verify the model, please!" << endl;

			for (int k = 0; k < selectedArcs.size(); k++)
				cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;

			return false;
		}
		else
			if (selectedArcs[k].i != selectedArcs[k].j)
				mark[selectedArcs[k].j]++;
	return true;
}

void addSubTourEliminationConstraints(vector<vector<NODE>> &cycles)
{
	try{

		for (int k = 0; k < cycles.size(); k++)
		{

			if (cycles[k][0].first == cycles[k][cycles[k].size() - 1].first && cycles[k][0].second == cycles[k][cycles[k].size() - 1].second)
			{
				cout << "Adding subtour constraint " << k << endl;
				GRBLinExpr subTour = 0;
				bool noSubTour = false;
				for (int idx = 1; idx < cycles[k].size(); idx++)
				{
					int i = cycles[k][idx-1].first;
					int t = cycles[k][idx-1].second;
					int j = cycles[k][idx].first;
					int t_prime = cycles[k][idx].second;

					subTour += x_a[VarIndex(i, t, j, t_prime)];
				}

				if (noSubTour == false)
				{
					cout << "Is adding a new subtour constraint" << k << endl;

					ostringstream subTourCons;
					subTourCons << "SubTour_" << cycles[k][0].first << "." << cycles[k][0].second;
					model.addConstr(subTour <= cycles[k].size() - 2, subTourCons.str());
				}


			}
		}
		
		model.update();
		
		return;

		set<string> newConstraints;

		//add crossing arcs connecting sub-tours
		for (int k = 0; k < cycles.size(); k++)
			for (int l = 0; l < cycles.size(); l++)
				if (k!=l)
			{
				for (int p = 0; p < cycles[k].size(); p++)
					for (int q = 0; q < cycles[l].size(); q++)
					{
						int i = cycles[k][p].first;
						int t = cycles[k][p].second;
						int j = cycles[l][q].first;
						int t_prime = cycles[l][q].second;

						//if ((((t_prime >= t) && (t + G.tau[i][j] <= G.l[j])) || ((t_prime < t) && (t + G.tau[i][j] <= G.l[j])))  && (x_a.find(VarIndex(i, t, j, t_prime)) == x_a.end()))
						if (t + G.tau[i][j] <= G.l[j] && (x_a.find(VarIndex(i, t, j, t_prime)) == x_a.end()))
						{
							//add a new variable
							ostringstream var_name;
							var_name << "x(" << i << "," << t << ")(" << j << "," << t_prime << ")";
							
							//cout << "New crossing arc:" << var_name.str() << endl;

							GRBVar new_arc = model.addVar(0.0, 1.0, G.tau[i][j], GRB_BINARY, var_name.str()); //add the variable associated to this arc to the model

							x_a[VarIndex(i, t, j, t_prime)] = new_arc;
							//update constraints
							//modified associated constraint related to node (i,t)
							
							//if (i != 0|| t != G.e[0])
							if (i != 0 || (t != G.e[0] && t != G.l[0]))
							{
								ostringstream flowConstraint1;
								flowConstraint1 << "FlowConstraint_" << i << "." << t;

								newConstraints.insert(flowConstraint1.str());
								constraintSet[flowConstraint1.str()] += new_arc;
							}
							//cout << "Change 1st flow constraint!Done!" << endl;

							//if (j != 0 || t_prime != G.e[0])
							if (j != 0 || (t_prime != G.e[0] && t_prime != G.l[0]))
							{
								ostringstream flowConstraint2;
								flowConstraint2 << "FlowConstraint_" << j << "." << t_prime;

								newConstraints.insert(flowConstraint2.str());
								constraintSet[flowConstraint2.str()] += new_arc;
							}
						}
					}
			}
		
		

		cout << "Number of new constraints: " << newConstraints.size() << endl;
		//cout << "Adding new variables!Done!" << endl;
		for (set<string>::iterator it = newConstraints.begin(); it != newConstraints.end(); it++)
		{
			string cons_name = *it;
			cout << "Current constraints:" << cons_name << endl;

			GRBConstr rem_cons = model.getConstrByName(cons_name);

			//if (cons_name[0] == 'D')
			//{
			//	cout << "WTH! Depot here" << endl;
			//	exit(0);
			//}

			model.remove(rem_cons);

			if (cons_name[0] == 'D')
				model.addConstr(constraintSet[cons_name] == 1, cons_name);
			else if (cons_name[0] == 'F')
				model.addConstr(constraintSet[cons_name] == 0, cons_name);
			else if (cons_name[0] == 'v')
				model.addConstr(constraintSet[cons_name] == 1, cons_name);
			else cout << "Something wrong!" << endl;
			
			model.update();
		}

		

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

//check if any node is outside of its time-window
bool nodeTimeWindowsCondition(vector<VarIndex> &selectedArcs, vector<VarIndex> &deletedVarList, set<VarIndex> &sLengthenArcs)
{
	//check if we have a feasible cycle
	for (int k = 0; k < selectedArcs.size(); k++)
	{
		int i = selectedArcs[k].i;
		int t = selectedArcs[k].t;
		int j = selectedArcs[k].j;
		int t_prime = selectedArcs[k].t_prime;

		bool outsidetheWindow1 = (t < G.e[i] || t > G.l[i] || t_prime < G.e[j] || t_prime > G.l[j]);
		bool outsidetheWindow2 = 0 & (t + G.tau[i][j] > G.l[j]);

		if (outsidetheWindow1 || outsidetheWindow2)
		{
			 
			cout << "Violation of time windows at (" << i << "," << t << "),(" << j << "," << t_prime << ") in first checking function!" << endl;
			deletedVarList.push_back(VarIndex(i, t, j, t_prime));
			if (t_prime < t + G.tau[i][j] && t + G.tau[i][j]<=G.l[j]) //neu lengthen no thi no lai nhay ra ngoai
			{
				cout << "Lengthen this arc" << endl;
				LENGTHEN_ARC(i, t, j, t_prime, G, PTEG);
				sLengthenArcs.insert(VarIndex(i, t, j, t_prime));
			}
			else cout << "Fail to lengthen this node because the new node is out of the time window!" << endl;
		
			return false;

		}
	}
	return true;
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

bool travellingTimeWindowCondition(vector < vector<NODE> > &cycles, set<VarIndex> &sLengthenArcs)
{
	for (int k = 0; k < cycles.size(); k++)
	{
		int curTime = cycles[k][0].second;

		for (int idx = 1; idx + 1 < cycles[k].size(); idx++)
		{
			NODE prev = cycles[k][idx - 1];
			NODE cur = cycles[k][idx];

			int i = prev.first, t = prev.second;
			int j = cur.first, t_prime = cur.second;

			if (curTime + G.tau[i][j] > G.l[j]) //violation of time windows
			{
				 
				cout << "Violation of time windows at (" << i << "," << t << "),(" << j << "," << t_prime << ") in seoond checking function!" << endl;

				//check if this arc is already lengthen
				if (sLengthenArcs.find(VarIndex(i, t, j, t_prime)) == sLengthenArcs.end())
					continue;

				deletedVarList.push_back(VarIndex(i, t, j, t_prime));
				if (t_prime < t + G.tau[i][j] && t + G.tau[i][j] <= G.l[j])
				{
					cout << "Lengthen this arc" << endl;
					LENGTHEN_ARC(i, t, j, t_prime, G, PTEG);

				}
				return false;
			}
		}
	}

}
//Algorithm 1 - SOLVE_TSPTW

bool SOLVE_TSPTW(OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
{
	//create the partially time-expanded network D_T
	CreateInitialParitalGraph(G, PTEG);
	
	cout << "Test the initial graph" << endl;
	
	cout << "Number of copies of each terminal: ";
	for (int i = 0; i < G.N0; i++)
		cout << PTEG.NT[i].size() << " ";
	cout << endl;

	cout << "Number of arcs at each node" << endl;
	for (map<NODE, set<NODE>>::iterator it = PTEG.AT.begin(); it != PTEG.AT.end(); it++)
		cout << "(" << (it->first).first << "," << (it->first).second << "):" << (it->second).size() << endl;

	//generate the first model
	ModelGeneration(G, PTEG); //always have feasible solutions
	
	//write model
	cout << "Test the model by writing it out:" << endl;
	
	model.write("tsp_ori.lp");

	//model.optimize();

	//if (model.get(GRB_IntAttr_Status) == GRB_INFEASIBLE)
	//{
	//	cout << "Something may be wrong!" << endl;
	//	return 0;
	//}


	//return 1;

	bool solved = false;
	double Obj = -1, lastObj =-1 ;
	try
	{
		while (solved == false)
		{


			// Optimize model

			model.optimize();

			if (model.get(GRB_IntAttr_Status) == GRB_INFEASIBLE)
			{
				cout << "Model is infeasible!" << endl;

				model.write("tsp_in.lp");
				exit(0);
				//reset the model to include new nodes/arcs as well as remove old nodes/arcs
				resetModel(G, PTEG);
				continue;
			}

			lastObj = Obj;

			//objective value
			cout << "Obj: " << (Obj = model.get(GRB_DoubleAttr_ObjVal)) << endl;


			if (model.get(GRB_IntAttr_Status) == GRB_OPTIMAL)
				cout << "Solve to optimality!" << endl;

			if (model.get(GRB_IntAttr_Status) == GRB_SUBOPTIMAL)
				cout << "Has feasible solution but not to optimality!" << endl;

			//set of selected arcs
			vector<VarIndex> selectedArcs;
			selectedArcs.clear();

			//traverse the variable list and extract variables' value
			for (map<VarIndex, GRBVar>::iterator var_it = x_a.begin(); var_it != x_a.end(); var_it++)
			{
				VarIndex idx = var_it->first;
				GRBVar arc_var = var_it->second;

				if (arc_var.get(GRB_DoubleAttr_X) == 1.0)
					selectedArcs.push_back(idx);
			}



			//display selected arcs
			cout << "Selected Arcs" << endl;
			for (int k = 0; k < selectedArcs.size(); k++)
				cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;


			if (totalCostCondition(selectedArcs)==false)
			{
				cout << "Total cost of selected arcs is different with the objective value" << endl;
				cout << "Wrong in the extraction of variables' value!" << endl;
				return 0;
			}

			set<VarIndex> sLengthenArcs;

			//check if we violate time window condition any any node

			bool feasiblePath = nodeTimeWindowsCondition(selectedArcs, deletedVarList, sLengthenArcs);

			cout << "Here" << endl;
			vector < vector<NODE> > cycles;
			buildCycles(selectedArcs, cycles);
			earliestFirst(cycles);

			//list of cycles
			cout << "List of cycles after moving the earliest node to the first position" << endl;
			for (int i = 0; i < cycles.size(); i++)
			{
				for (int j = 0; j < cycles[i].size(); j++)
					cout << "(" << cycles[i][j].first << "," << cycles[i][j].second << ")-";
				cout << endl;
			}

			feasiblePath = travellingTimeWindowCondition(cycles, sLengthenArcs);
			cout << "Done!" << endl;
			//if (visitedOnceCondition(selectedArcs) == false)
			//{
			//	//adding subtour elimination constraints
			//	addSubTourEliminationConstraints(cycles);
			//	subTourElimination = false;
			//}

			feasiblePath = false;

			if (feasiblePath == true)
			{
				cout << "Found optimal solution!" << endl;

				cout << "Convergence with the objective value = " << Obj << endl;

				//display selected arcs

				for (int k = 0; k < selectedArcs.size(); k++)
					cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;

				if (subTourElimination == false)
				{
					subTourElimination = true;
					
					continue ;
				}

				return 1;
			}

			else
			{
				//reset the model to include new nodes/arcs as well as remove old nodes/arcs
				//resetModel(G, PTEG);
				//model.update();
				
				resetModel(G, PTEG, deletedVarList, addedVarList,addedNodeList);
				
				cout << "Done!" << endl;
				if (deletedVarList.size() + addedNodeList.size() + addedVarList.size() == 0)
				{
					addSubTourEliminationConstraints(cycles);
				
					//model.write("tsp2.lp");

					//exit(0);
				}

				deletedVarList.clear();
				addedNodeList.clear();
				addedVarList.clear();
			
				model.write("tsp1.lp");
				//return 1;
			}

		}
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


	return 1;
}
int main(int   argc,
     char *argv[])
{

	cout << "File name:" << argv[1] << endl;

	//readOriginalGraph(G, argv[1]);
	readOriginalGraph_rfsilva(G, argv[1]);

	testReadingGraph(G);

	//return 0;

	SOLVE_TSPTW(G, PTEG);

	return 0;
}
