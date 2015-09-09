#include "gurobi_c++.h"
#include "TSPTW.h"
#include <vector>
#include <set>
#include <map>
#include <sstream>
#include <algorithm>

// some changes

using std::cout;

using namespace std;

//OriginalGraph G;
//
//OriginalGraph G;
//PartialTimeExpandedGraph PTEG;
//
////model and variable decleration 
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

	InitialModelGeneration(G, PTEG);
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


//Algorithm 1 - SOLVE_TSPTW

//bool SOLVE_TSPTW(OriginalGraph &G, PartialTimeExpandedGraph &PTEG)
//{
//	//create the partially time-expanded network D_T
//	CreateInitialParitalGraph(G, PTEG);
//	
//	cout << "Test the initial graph" << endl;
//	
//	cout << "Number of copies of each terminal: ";
//	for (int i = 0; i < G.N0; i++)
//		cout << PTEG.NT[i].size() << " ";
//	cout << endl;
//
//	cout << "Number of arcs at each node" << endl;
//	for (map<NODE, set<NODE>>::iterator it = PTEG.AT.begin(); it != PTEG.AT.end(); it++)
//		cout << "(" << (it->first).first << "," << (it->first).second << "):" << (it->second).size() << endl;
//
//	//generate the first model
//	InitialModelGeneration(G, PTEG); //always have feasible solutions
//	
//	//write model
//	cout << "Test the model by writing it out:" << endl;
//	
//	model.write("tsp_ori.lp");
//
//	//model.optimize();
//
//	//if (model.get(GRB_IntAttr_Status) == GRB_INFEASIBLE)
//	//{
//	//	cout << "Something may be wrong!" << endl;
//	//	return 0;
//	//}
//
//
//	//return 1;
//
//	bool solved = false;
//	double Obj = -1, lastObj =-1 ;
//	try
//	{
//		while (solved == false)
//		{
//
//
//			// Optimize model
//
//			model.optimize();
//
//			if (model.get(GRB_IntAttr_Status) == GRB_INFEASIBLE)
//			{
//				cout << "Model is infeasible!" << endl;
//
//				model.write("tsp_in.lp");
//				exit(0);
//				//reset the model to include new nodes/arcs as well as remove old nodes/arcs
//				resetModel(G, PTEG);
//				continue;
//			}
//
//			lastObj = Obj;
//
//			//objective value
//			cout << "Obj: " << (Obj = model.get(GRB_DoubleAttr_ObjVal)) << endl;
//
//
//			if (model.get(GRB_IntAttr_Status) == GRB_OPTIMAL)
//				cout << "Solve to optimality!" << endl;
//
//			if (model.get(GRB_IntAttr_Status) == GRB_SUBOPTIMAL)
//				cout << "Has feasible solution but not to optimality!" << endl;
//
//			//set of selected arcs
//			vector<VarIndex> selectedArcs;
//			selectedArcs.clear();
//
//			//traverse the variable list and extract variables' value
//			for (map<VarIndex, GRBVar>::iterator var_it = x_a.begin(); var_it != x_a.end(); var_it++)
//			{
//				VarIndex idx = var_it->first;
//				GRBVar arc_var = var_it->second;
//
//				if (arc_var.get(GRB_DoubleAttr_X) == 1.0)
//					selectedArcs.push_back(idx);
//			}
//
//
//
//			//display selected arcs
//			cout << "Selected Arcs" << endl;
//			for (int k = 0; k < selectedArcs.size(); k++)
//				cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;
//
//
//			if (totalCostCondition(selectedArcs)==false)
//			{
//				cout << "Total cost of selected arcs is different with the objective value" << endl;
//				cout << "Wrong in the extraction of variables' value!" << endl;
//				return 0;
//			}
//
//			set<VarIndex> sLengthenArcs;
//
//			//check if we violate time window condition any any node
//
//			bool feasiblePath = nodeTimeWindowsCondition(selectedArcs, deletedVarList, sLengthenArcs);
//
//			cout << "Here" << endl;
//			vector < vector<NODE> > cycles;
//			buildCycles(selectedArcs, cycles);
//			earliestFirst(cycles);
//
//			//list of cycles
//			cout << "List of cycles after moving the earliest node to the first position" << endl;
//			for (int i = 0; i < cycles.size(); i++)
//			{
//				for (int j = 0; j < cycles[i].size(); j++)
//					cout << "(" << cycles[i][j].first << "," << cycles[i][j].second << ")-";
//				cout << endl;
//			}
//
//			int xxx;
//			feasiblePath = travellingTimeWindowCondition(cycles,xxx);
//			cout << "Done!" << endl;
//			//if (visitedOnceCondition(selectedArcs) == false)
//			//{
//			//	//adding subtour elimination constraints
//			//	addSubTourEliminationConstraints(cycles);
//			//	subTourElimination = false;
//			//}
//
//			feasiblePath = false;
//
//			if (feasiblePath == true)
//			{
//				cout << "Found optimal solution!" << endl;
//
//				cout << "Convergence with the objective value = " << Obj << endl;
//
//				//display selected arcs
//
//				for (int k = 0; k < selectedArcs.size(); k++)
//					cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;
//
//				if (subTourElimination == false)
//				{
//					subTourElimination = true;
//					
//					continue ;
//				}
//
//				return 1;
//			}
//
//			else
//			{
//				//reset the model to include new nodes/arcs as well as remove old nodes/arcs
//				//resetModel(G, PTEG);
//				//model.update();
//				
//				resetModel(G, PTEG, deletedVarList, addedVarList,addedNodeList);
//				
//				cout << "Done!" << endl;
//				if (deletedVarList.size() + addedNodeList.size() + addedVarList.size() == 0)
//				{
//					addSubTourEliminationConstraints(cycles);
//				
//					//model.write("tsp2.lp");
//
//					//exit(0);
//				}
//
//				deletedVarList.clear();
//				addedNodeList.clear();
//				addedVarList.clear();
//			
//				model.write("tsp1.lp");
//				//return 1;
//			}
//
//		}
//	}
//	catch (GRBException e) {
//		cout << "Error code = " << e.getErrorCode() << endl;
//		cout << e.getMessage() << endl;
//		/*	return false;*/
//	}
//	catch (...) {
//		cout << "Exception during optimization" << endl;
//		/*return false;*/
//	}
//
//
//	return 1;
//}

//int main(int   argc,
//     char *argv[])
//{
//
//	cout << "File name:" << argv[1] << endl;
//
//	//readOriginalGraph(G, argv[1]);
//	readOriginalGraph_rfsilva(G, argv[1]);
//
//	testReadingGraph(G);
//
//	//return 0;
//
//	SOLVE_TSPTW(G, PTEG);
//
//	return 0;
//}
