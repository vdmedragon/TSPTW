
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

using std::cout;

using namespace std;

#define MAXN 222

namespace
{

	struct OriginalGraph
	{
		int N0; //number of vertices;
		int tau[MAXN][MAXN]; //distance matrix
		int rtau[MAXN][MAXN];
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

	//graph information
	OriginalGraph G;
	PartialTimeExpandedGraph PTEG;

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

	set<VarIndex> deletedVarList;
	set<VarIndex> addedVarList;
	set<NODE> addedNodeList;

	 

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
				
				//cout << "(" << i << "," << t << ")" << endl;
				
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

					//if (t + tau_ij < G.e[j])
					//	cout << "Waiting at " << j << " because of early arrival with departure from "<< i<< " at time point "<<t<<endl;
					//cout << "(" << i << "," << t << ")-(" << j << "," << t_prime << ")" << endl;
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
		cout << "Trying to add new node" << "(" << i << "," << t_new << ")" << endl;
		std::pair<std::set<int>::iterator, bool> loc = PTEG.NT[i].insert(t_new); //location of new added node
 

		if (loc.second == false)
		{
			cout << "This node is already in the model!" << endl;
			
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
			cout << "The arc "<< new_arc << " is already in the model" << endl;
			
			addedVarList.erase(new_arc);
			
			return false;
		}
		
		//addedVarList.insert(new_arc);
		//deletedVarList.insert(old_arc);

		bool added_arc = REFINE(new_arc.j, new_arc.t_prime, G,PTEG, addedNodeList, addedVarList, deletedVarList);
		cout << "Finish added nodes && related arcs!Done!" << endl;
		if (added_arc == true)
		{
			RESTORE(new_arc.j, new_arc.t_prime, G, PTEG, addedVarList, deletedVarList);
			cout << "Finish lengthen arcs!Done!" << endl;

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

			cout << "************************************" << endl;
			cout << "Is trying to remove old arc" << old_arc << endl;
			cout << "Is trying to add new arc" << new_arc << endl;

			if (i == j && prevTime == curTime && t_prime > curTime)
			{
				cout << "Holding arcs! Do nothing!" << endl;
				curTime = t_prime;
				continue;
			}

			if (isTheSameArc(old_arc, new_arc) && curTime <= G.l[j])
			{
				cout << "They are same arc! Already lengthened so cannnot remove!" << endl;
				continue; //this arc is already lengthened. 
			}
			else if (isTheSameArc(old_arc, new_arc) && curTime > G.l[j])
			{
				deletedVarList.insert(old_arc); //remove because this arc violate time window constraint at j
			}


			if (!tooLate(new_arc) && t != prevTime) //nghia la old_arc va new_arc xuat phat tu hai diem khac nhau, giu old arc
			{
				cout << "Keep old arcs while adding new arcs because they depart at different time!" << endl;

				deletedVarList.erase(old_arc);
				//continue; 
			}
			else if (!tooLate(new_arc))
			{
				cout << "Is able to remove old arc! Two arcs depart from a same time!" << endl;
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
				cout << "New arc is too late!Cannot added! " << endl;
				if (t == prevTime)
				{
					cout << "Previous arc is lengthened! So remove old arc!" << endl;
					deletedVarList.insert(old_arc);
				}
			}

			//actually adding arcs to the model
			addNodeArcToModel(G, PTEG, deletedVarList, addedVarList, addedNodeList);

			change = deletedVarList.size() + addedVarList.size() + addedNodeList.size() > 0;

			nbModificationArcs += deletedVarList.size() + addedVarList.size() + addedNodeList.size();

			cout << "New nodes:";
			cout << addedNodeList.size() << endl;
			//printAddedNodeList(addedNodeList);
			//if (addedNodeList.size() == 0) cout << "No new nodes" << endl;

			cout << "New added arcs:";
			cout << addedVarList.size() << endl;

			//if (addedVarList.size()) cout << endl;
			//printAddedArcsList(addedVarList);
			//if (addedVarList.size() == 0) cout << "No new arcs " << endl;

			cout << "Old removed arcs:";
			cout << deletedVarList.size() << endl;

			//if (deletedVarList.size()) cout << endl;
			//printRemovedArcsList(deletedVarList);
			//if (deletedVarList.size() == 0) cout << "No removed arcs" << endl;
		}
		return ;

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

			prevTime = curTime;
			curTime = max(curTime + G.tau[i][j], G.e[j]);

			VarIndex old_arc(i, t, j, t_prime); //old arc in the list
			 
			VarIndex new_arc(i, prevTime, j, curTime); //new arc

			cout << "************************************" << endl;
			cout << "Is trying to remove old arc" << old_arc << endl;
			cout << "Is trying to add new arc" << new_arc << endl;
			
			if (i == j && prevTime == curTime && t_prime > curTime)
			{
				cout << "Holding arcs! Do nothing!" << endl;
				curTime = t_prime;
				continue;	
			}

			if (isTheSameArc(old_arc, new_arc) && curTime <= G.l[j])
			{
				cout << "They are same arc! Already lengthened so cannnot remove!" << endl;
				continue; //this arc is already lengthened. 
			}
			else if (isTheSameArc(old_arc, new_arc) && curTime > G.l[j])
			{
				deletedVarList.insert(old_arc); //remove because this arc violate time window constraint at j
			}


			if (!tooLate(new_arc) && t != prevTime) //nghia la old_arc va new_arc xuat phat tu hai diem khac nhau, giu old arc
			{
				cout << "Keep old arcs while adding new arcs because they depart at different time!" << endl;

				deletedVarList.erase(old_arc);
				//continue; 
			}
			else if (!tooLate(new_arc))
			{
				cout << "Is able to remove old arc! Two arcs depart from a same time!" << endl;
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
				cout << "New arc is too late!Cannot added! " << endl;
				if (t == prevTime)
				{
					cout << "Previous arc is lengthened! So remove old arc!"<<endl;
					deletedVarList.insert(old_arc);
				}
			}

			//actually adding arcs to the model
			addNodeArcToModel(G, PTEG, deletedVarList, addedVarList, addedNodeList);

			change = deletedVarList.size() + addedVarList.size() + addedNodeList.size() > 0;
			
			nbModificationArcs += deletedVarList.size() + addedVarList.size() + addedNodeList.size();
			
			cout << "New nodes:";
			cout << addedNodeList.size() << endl; 
			//printAddedNodeList(addedNodeList);
			//if (addedNodeList.size() == 0) cout << "No new nodes" << endl;

			cout << "New added arcs:";
			cout << addedVarList.size() << endl;

			//if (addedVarList.size()) cout << endl;
			//printAddedArcsList(addedVarList);
			//if (addedVarList.size() == 0) cout << "No new arcs " << endl;

			cout << "Old removed arcs:";
			cout << deletedVarList.size() << endl;

			//if (deletedVarList.size()) cout << endl;
			//printRemovedArcsList(deletedVarList);
			//if (deletedVarList.size() == 0) cout << "No removed arcs" << endl;
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

				(varIndex_it->second).set(GRB_DoubleAttr_Obj, G.rtau[i][j]);
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

			//for (map<NODE,set<NODE> >::iterator it_node_it = PTEG.AT.begin(); it_node_it != PTEG.AT.end(); it_node_it++)
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
			cout << "Model modification!" << endl;
			set<string> newConstraints;

			
			assert(addedNodeList.size() <= 1); //add no more than one node each time

			int ii = -1, tt = -1;

			if (addedNodeList.size())
				ii = addedNodeList.begin()->first, tt = addedNodeList.begin()->second;

			//cout << " AAAAAAAAAAAAA" << endl;
			//add constraints related to the new node
			for (set<NODE>::iterator it = addedNodeList.begin(); it != addedNodeList.end();it++)
			 
			{
				 
				int i = it->first;
				int t = it->second;

				if (i == 0 && t == G.e[0])
					continue;

				ostringstream flowConstraint;
				flowConstraint << "FlowConstraint_" << i << "." << t;

				model.addConstr(GRBLinExpr(0.0) == 0, flowConstraint.str());

				newConstraints.insert(flowConstraint.str());
				model.update();
				constraintSet[flowConstraint.str()] = model.getRow( model.getConstrByName(flowConstraint.str()));
			}

			model.update();
			//cout << " AAAAAAAAAAAAA" << endl;
			//			//add constraints related to the new node
			//for (int k = 0; k < addedNodeList.size(); k++)
			//{
			//	int i = addedNodeList[k].first;
			//	int t = addedNodeList[k].second;

			//	if (i == 0 && t == G.e[0])
			//		continue;

			//	ostringstream flowConstraint;
			//	flowConstraint << "FlowConstraint_" << i << "." << t;

			//	model.addConstr(GRBLinExpr(0.0) == 0, flowConstraint.str());

			//	newConstraints.insert(flowConstraint.str());

			//	constraintSet[flowConstraint.str()] = model.getRow( model.getConstrByName(flowConstraint.str()));
			//}
			//cout << " AAAAAAAAAAAAA" << endl;
			
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

				//if (ii == i && tt == t) cout << "Related new added nodes" << i<<"."<<t<< endl;

				ostringstream var_name;

				var_name << "x(" << i << "," << t << ")(" << j << "," << t_prime << ")";

				GRBVar new_arc = model.addVar(0.0, 1.0, G.rtau[i][j], GRB_BINARY, var_name.str()); //add the variable associated to this arc to the model

				x_a[VarIndex(i, t, j, t_prime)] = new_arc;

				//cout << "Adding a new arc!Done!" << endl;
				model.update();

				if (i == 0 && t == G.e[0])
				{
					ostringstream depotOutConstraint;
					depotOutConstraint << "DepotOutConstraint";
					
					newConstraints.insert(depotOutConstraint.str());

					if (constraintSet.find(depotOutConstraint.str()) == constraintSet.end())
						constraintSet[depotOutConstraint.str()] = model.getRow(model.getConstrByName(depotOutConstraint.str()));
					constraintSet[depotOutConstraint.str()] += new_arc;
				}

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

				ostringstream visitedOnceConstraint;
				visitedOnceConstraint << "visitedOnceConstraint_" << i;

 				newConstraints.insert(visitedOnceConstraint.str());

				if (constraintSet.find(visitedOnceConstraint.str()) == constraintSet.end())
					constraintSet[visitedOnceConstraint.str()] = model.getRow(model.getConstrByName(visitedOnceConstraint.str()));
				constraintSet[visitedOnceConstraint.str()] += new_arc;
				//cout << "Change visited once constraint!Done!" << endl;
			}

			model.update();

 
			cout << "Number of new constraints: " << newConstraints.size() << endl;
			//cout << "Adding new variables!Done!" << endl;
		 

			for (set<string>::iterator it = newConstraints.begin(); it != newConstraints.end(); it++)
			{
				string cons_name = *it;

				//model.addConstr(constraintSet["xxx"] == 1, "yyy");

				//cout << "Current constraints:" << cons_name << endl;

				GRBConstr rem_cons = model.getConstrByName(cons_name);
 				model.remove(rem_cons);
				
				model.update();


				if (cons_name[0] == 'D')
				{
					//cout << "we are here" << endl;
					//if (constraintSet.find(cons_name) == constraintSet.end())
					//{
					//	cout << "Not found this constraint!" << endl;
					//	return;
					//}

					model.addConstr(constraintSet[cons_name] == 1, cons_name);
					//cout << "we are ok!" << endl;
				}
				else if (cons_name[0] == 'F')
					model.addConstr(constraintSet[cons_name] == 0, cons_name);
				else if (cons_name[0] == 'v')
					model.addConstr(constraintSet[cons_name] == 1, cons_name);
				else cout << "Something wrong!" << endl;

				//cout << "Done add new constraint" << endl;
				//model.update();
			}
			model.update();
		}

		catch (GRBException e) {
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
				violatedTerminal = idx;
				return false;

			}
			else
				curTime = max(curTime + G.rtau[i][j], (double)G.e[j]);
		}
		return true;
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


}
#endif