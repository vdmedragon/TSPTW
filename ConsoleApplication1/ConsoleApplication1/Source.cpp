#include "gurobi_c++.h"
#include "Header.h"
#include <vector>
#include <set>
#include <map>
#include <sstream>
#include <algorithm>
#include <ctime>
// some changes

using std::cout;

using namespace std;

int nbSubTours = 0;
int nbArcsLengthened = 0;
int AverageOrder = 0;
int nbIters = 0;
int unknownreason = 0;

vector<pair<int, int> > numberofCycles;
vector<pair<int, int> > nbArcsTooShort;
vector<pair<int, int> > Orderof1stInfeasibleTW;
vector<pair<int, int> > objFunction;
vector<pair<int, int> > nbArcLengthened;

void addSubTourEliminationConstraints1(vector<vector<NODE> > &cycles)
{
	try{

		cout << "Adding new subtour constraint " << cycles.size() << endl;
		for (int k = 0; k < cycles.size(); k++)
		{

			if (cycles[k][0].first == cycles[k][cycles[k].size() - 1].first && cycles[k][0].second == cycles[k][cycles[k].size() - 1].second)
			{
				//cout << "Adding subtour constraint " << k << endl;
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
					//cout << "Is adding a new subtour constraint" << k << endl;

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

void addSubTourEliminationConstraintsNoFirstCycle(vector<vector<NODE> > &cycles)
{
	try{
		cout << "Adding new sub tour constraints :" << cycles.size() - 1 << endl;

		for (int k = 1; k < cycles.size(); k++)
		{

			if (cycles[k][0].first == cycles[k][cycles[k].size() - 1].first && cycles[k][0].second == cycles[k][cycles[k].size() - 1].second)
			{
				//cout << "Adding subtour constraint " << k + 1 << endl;
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
					//cout << "Is adding a new subtour constraint" << k << endl;

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

//void Test1()
//{
//
//	bool solved = false;
//	double Obj = -1, lastObj = -1;
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
//			}
//
//			lastObj = Obj;
//
//			//objective value
//			cout << "Obj: " << (Obj = model.get(GRB_DoubleAttr_ObjVal)) << endl;
//
//			if (Obj == 208)
//			{
//				model.write("wth.lp");
//				exit(0);
//			}
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
//			////display selected arcs
//			//cout << "Selected Arcs" << endl;
//			//for (int k = 0; k < selectedArcs.size(); k++)
//			//	cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;
//
//			vector < vector<NODE> > cycles;
//
//			buildCycles(selectedArcs, cycles);
//
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
//			exit(0);
//
//			if (cycles.size()>1) //we have more than we sub-tours
//				addSubTourEliminationConstraints1(cycles); //remove them
//
//			else //checking time windows constraints
//			{
//				int violatedTerminal = -1;
//				travellingTimeWindowCondition(cycles[0], violatedTerminal);
//
//				if (violatedTerminal != -1) //violation of time window at a terminal
//					addTimeWindowsViolationConstraint(cycles[0], violatedTerminal);
//				else
//					break; //we have a good solution
//			}
//
//
//
//			deletedVarList.clear();
//			addedNodeList.clear();
//			addedVarList.clear();
//
//			model.write("tsp1.lp");
//
//			//break; 
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
//}

//test the modification of constraints when new nodes are added/removed.
void Test2()
{

	int start_s = clock();

	bool solved = false;
	double Obj = -1, lastObj = -1;

	vector < vector<NODE> > cycles;

	try
	{
		while (solved == false)
		{

			cycles.clear();
			nbIters++;
			cout << "Iter " << nbIters << endl;

			if (nbIters == 2000)
			{
				model.write("tsp2000.lp");
				exit(0);
			}
			//Optimize model

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

			//if (Obj < lastObj)
			//{
			//	assert(1 == 0);
			//}


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

				if (arc_var.get(GRB_DoubleAttr_X) > 0.5)
					selectedArcs.push_back(idx);
			}

			////display selected arcs
			//cout << "Selected Arcs" << endl;
			//for (int k = 0; k < selectedArcs.size(); k++)
			//	cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;



			buildCycles(selectedArcs, cycles);

			earliestFirst(cycles);
			cout << "Number of cycles: " << cycles.size() << endl;
			//list of cycles
			cout << "List of cycles after moving the earliest node to the first position" << endl;
			for (int i = 0; i < cycles.size(); i++)
			{
				cout << "Cycle " << i + 1 << ":";
				for (int j = 0; j < cycles[i].size(); j++)
					cout << "(" << cycles[i][j].first << "," << cycles[i][j].second << ")-";
				cout << endl;
			}


			if (cycles.size()>1) //we have more than we sub-tours
			{

				//addSubTourEliminationConstraints1(cycles); //remove them

				int firstNonLiftedNodeIndex = firstNonLiftedNode(cycles[0]);

				if (firstNonLiftedNodeIndex != -1) //co canh vi pham
				{
					UpdateArcsFollowingCycle(cycles[0], firstNonLiftedNodeIndex);
					addSubTourEliminationConstraintsNoFirstCycle(cycles); //remove them
				}

				else
				{
					int nbArcs = UpdateArcsFollowingCycle(cycles[0], cycles[0].size() - 2);
					if (nbArcs) //co canh nhac duoc
						addSubTourEliminationConstraintsNoFirstCycle(cycles);
					else //moi canh deu da nhac
						addSubTourEliminationConstraints1(cycles);
				}

				//for (int k = 0; k < cycles.size(); k++)
				//{
				//	int firstNonLiftedNodeIndex = firstNonLiftedNode(cycles[k]);
				//	if (firstNonLiftedNodeIndex != -1)
				//	{
				//		aaa;
				//	}

				//}
			}
			else //checking time windows constraints
			{
				int violatedTerminal = -1;
				travellingTimeWindowCondition(cycles[0], violatedTerminal);

				vector<NODE> cycle = cycles[0];

				if (violatedTerminal != -1) //violation of time window at a terminal
				{
					int nbArcTooShort = UpdateArcsFollowingCycle(cycle, violatedTerminal);
					nbArcsTooShort.push_back(make_pair(nbIters, nbArcTooShort));
				}

				else
				{
					cout << "Obtain feasible solution regarding time window!" << endl;
					cout << "Obj = " << Obj << endl;

					for (int k = 0; k < cycles[0].size(); k++)
						cout << cycles[0][k].first + 1 << "-";
					cout << endl << "Execution time: " << (clock() - start_s) / double(CLOCKS_PER_SEC) << endl;

					return; //we have a good solution
				}

			}

			deletedVarList.clear();
			addedNodeList.clear();
			addedVarList.clear();

			int stop_s = clock();

			if ((stop_s - start_s) / double(CLOCKS_PER_SEC) > 36000)
			{
				cout << "Stop do run qua lau !" << endl;
				break;
			}

			cout << "************************************************************************************" << endl;
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


	for (int i = 0; i < cycles.size(); i++)
	{
		cout << "Solution: ";
		for (int j = 1; j < cycles[i].size(); j++)
			if (cycles[i][j].first != cycles[i][j - 1].first)
				cout << cycles[i][j - 1].first + 1 << "-";
		cout << cycles[i][cycles[i].size() - 1].first + 1 << endl;
		//if (i==0) cout << 1 << endl;
		//else cout << endl;
	}

	unknownreason = 1;

}

int main(int   argc,
	char *argv[])
{

	cout << "File name:" << argv[1] << endl;
	freopen(argv[1], "rt", stdin);
	//readOriginalGraph(G, argv[1]);
	readOriginalGraph_rfsilva(G, argv[1]);

	cout << "Starting the solution procedure!" << endl;
	//testReadingGraph(G);

	//CreateInitialParitalGraph(G, PTEG);
	CreateInitialParitalGraphWithOutZero(G, PTEG);

	//
	InitialModelGeneration(G, PTEG);



	model.write("tsp_ori.lp");
	//return 0;
	model.getEnv().set(GRB_IntParam_OutputFlag, 0);
	model.getEnv().set(GRB_IntParam_Threads, 1);
	int start_s = clock();

	freopen(argv[2], "wt", stdout);

	Test2();

	if (unknownreason)
	{
		string lpmodel(argv[2]);
		lpmodel += ".lp";
		model.write(lpmodel);

	}

	return 0;
}