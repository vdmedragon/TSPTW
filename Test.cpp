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
 

 
void addSubTourEliminationConstraints1(vector<vector<NODE>> &cycles)
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
					int i = cycles[k][idx - 1].first;
					int t = cycles[k][idx - 1].second;
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

void Test1()
{

	bool solved = false;
	double Obj = -1, lastObj = -1;
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

			////display selected arcs
			//cout << "Selected Arcs" << endl;
			//for (int k = 0; k < selectedArcs.size(); k++)
			//	cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;

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

			exit(0);

			if (cycles.size()>1) //we have more than we sub-tours
				addSubTourEliminationConstraints1(cycles); //remove them

			else //checking time windows constraints
			{
				int violatedTerminal = -1;
				travellingTimeWindowCondition(cycles[0], violatedTerminal);

				if (violatedTerminal != -1) //violation of time window at a terminal
					addTimeWindowsViolationConstraint(cycles[0], violatedTerminal);
				else
					break; //we have a good solution
			}



			deletedVarList.clear();
			addedNodeList.clear();
			addedVarList.clear();

			model.write("tsp1.lp");

			//break; 

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

//test the modification of constraints when new nodes are added/removed.
void Test2()
{


	bool solved = false;
	double Obj = -1, lastObj = -1;
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
			}

			lastObj = Obj;

			//objective value
			cout << "Obj: " << (Obj = model.get(GRB_DoubleAttr_ObjVal)) << endl;


			if (model.get(GRB_IntAttr_Status) == GRB_OPTIMAL)
				cout << "Solve to optimality!" << endl;

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

			////display selected arcs
			//cout << "Selected Arcs" << endl;
			//for (int k = 0; k < selectedArcs.size(); k++)
			//	cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;

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


			if (cycles.size()>1) //we have more than we sub-tours
				addSubTourEliminationConstraints1(cycles); //remove them

			else //checking time windows constraints
			{
				int violatedTerminal = -1;
				travellingTimeWindowCondition(cycles[0], violatedTerminal);

				vector<NODE> cycle = cycles[0];

				if (violatedTerminal != -1) //violation of time window at a terminal
				{
					//addTimeWindowsViolationConstraint(cycles[0], violatedTerminal);
					int curTime = G.e[0];
					int prevTime = -1;
					for (int idx = 1; idx  <= violatedTerminal; idx++)
					{
						NODE prev = cycle[idx - 1];
						NODE cur = cycle[idx];

						int i = prev.first, t = prev.second;
						int j = cur.first, t_prime = cur.second;
						
						prevTime = curTime;
						curTime = max(curTime + G.tau[i][j], G.e[j]);

						LENGTHEN_ARC(i, prevTime, j, curTime,G,PTEG);
					}
			
				}
					
				else
					break; //we have a good solution
			}



			deletedVarList.clear();
			addedNodeList.clear();
			addedVarList.clear();

			model.write("tsp1.lp");

			//break; 

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

int main(int   argc,
	char *argv[])
{

	cout << "File name:" << argv[1] << endl;

	//readOriginalGraph(G, argv[1]);
	readOriginalGraph_rfsilva(G, argv[1]);

	testReadingGraph(G);

	CreateInitialParitalGraph(G, PTEG);

	InitialModelGeneration(G, PTEG);

	model.write("tsp_ori.lp");

	return 0;
}