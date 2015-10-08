#include "gurobi_c++.h"
#include "TSPTW.h"
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

int unknownreason = 0;


GRBModel tmpModel(*env);

vector<pair<int, int> > numberofCycles;
vector<pair<int, int> > nbArcsTooShort;
vector<pair<int, int> > Orderof1stInfeasibleTW;
vector<pair<int, int> > objFunction;
vector<pair<int, int> > nbArcLengthened;



void addaSingleSubTourConstraint(vector<NODE> &cycle)
{

	try{

		if (DEBUG)
		{
			for (int i = 0; i < cycle.size(); i++)
				cout << "(" << cycle[i].first << "," << cycle[i].second << ")-";
			cout << endl;
		}

		if (cycle[0].first == cycle[cycle.size() - 1].first && cycle[0].second == cycle[cycle.size() - 1].second)
		{
				 
			GRBLinExpr subTour = 0;
			bool noSubTour = false;
			for (int idx = 1; idx < cycle.size(); idx++)
			{
				int i = cycle[idx - 1].first;
				int t = cycle[idx - 1].second;
				int j = cycle[idx].first;
				int t_prime = cycle[idx].second;

				subTour += x_a[VarIndex(i, t, j, t_prime)];
			}

			if (noSubTour == false)
			{
				//cout << "Is adding a new subtour constraint" << k << endl;

				ostringstream subTourCons;
				subTourCons << "SubTour_" << cycle[0].first << "." << cycle[0].second;
				model.addConstr(subTour <= cycle.size() - 2, subTourCons.str());
			}
		}
	}

	catch (GRBException e) {
		cout << "Error code = " << e.getErrorCode() << "in AddSingleSubTourConstraint"<<endl;
		cout << e.getMessage() << endl;
		exit(0);
	}
	catch (...) {
		cout << "Exception during optimization" << endl;
		/*return false;*/
	}

}
void addSubTourEliminationConstraints1(vector<vector<NODE> > &cycles)
{
	try{

		cout << "Adding new subtour constraint " << cycles.size() << endl;
		for (int k = 0; k < cycles.size(); k++)
			addaSingleSubTourConstraint(cycles[k]);
		model.update();
	}

	catch (GRBException e) {
		cout << "Error code = " << e.getErrorCode() << "in addSubTourEliminationConstraint" << endl;
		cout << e.getMessage() << endl;
		exit(0);
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
			addaSingleSubTourConstraint(cycles[k]);

		model.update();
	}

	catch (GRBException e) {
		cout << "Error code = " << e.getErrorCode() << "in addSubTourConstraintNoFirstCycle"<<endl;
		cout << e.getMessage() << endl;
		exit(0);
	}
	catch (...) {
		cout << "Exception during optimization" << endl;
		/*return false;*/
	}
}

//display all cycles;
void displayCycles(vector<vector<NODE> > cycles)
{
	for (int i = 0; i < cycles.size(); i++)
	{
		cout << "Cycle " << i + 1 << ":";
		for (int j = 0; j < cycles[i].size(); j++)
			cout << "(" << cycles[i][j].first << "," << cycles[i][j].second << ")-";
		cout << endl;
	}
}

//lift many arcs - true if we lift some nodes, false if no nodes
bool liftUntilViolatedNode(vector<NODE> cycle)
{
	int firstNonLiftedNodeIndex = firstViolatedNode(cycle);
	
	if (DEBUG)
		if (firstNonLiftedNodeIndex != -1)
			cout << "Violation appears at terminal " << cycle[firstNonLiftedNodeIndex].first << " with index " << firstNonLiftedNodeIndex << endl;
		else
			cout << "No violated node on this cycle!" << endl;
	
	if (firstNonLiftedNodeIndex != -1) //co canh vi pham
	{
		UpdateArcsFollowingCycle(cycle, firstNonLiftedNodeIndex);
		return 1;
	}
	else return 0;
	
}

void LiftOnlyFirstCycle(vector< vector <NODE> > cycles)
{
	int firstNonLiftedNodeIndex = firstNonLiftedNode(cycles[0]);

	if (firstNonLiftedNodeIndex != -1) //co canh vi pham
	{
		cout << " Cycle 0 has non lifted nodes! Add all subtour constraints except the first! " << endl;
		UpdateArcsFollowingCycle(cycles[0], firstNonLiftedNodeIndex);
		addSubTourEliminationConstraintsNoFirstCycle(cycles); //remove them
	}

	else
	{
		cout << "Try to lift some nodes from the first cycle " << endl;
		int nbArcs = UpdateASingleArcFollowingCycle(cycles[0], cycles[0].size() - 2);
		//cout << "****************AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA*****************************" << endl;
		if (nbArcs) //co canh nhac duoc
		{
			cout << "Add add subtours except 0 " << endl;
			addSubTourEliminationConstraintsNoFirstCycle(cycles);
		}
		else //moi canh deu da nhac
		{
			cout << " Add all subtours " << endl;
			addSubTourEliminationConstraints1(cycles);
		}
	}
}

void LiftManyCyclesExceptFirstCycle(vector< vector <NODE> > cycles)
{
	for (int k = 0; k < cycles.size(); k++)
	{
		//cout << "Lifting cycle numbered " << k << endl;
		bool change = liftUntilViolatedNode(cycles[k]); //do the lift
		if (change == false && k > 0)
		{
			if (cycles[k].size() > 2)
				UpdateArcsFollowingCycle(cycles[k], cycles[k].size() - 1); //no time-window violation but we perform lift 
			else
				addaSingleSubTourConstraint(cycles[k]);

		}
		//else if (k == 0 && change == false)
		//	addaSingleSubTourConstraint(cycles[0]); //cycle 0, add subtour constraint
		//cout << "*************************************" << endl;
	}
}

void LiftManyCyclesExceptFirstCycleAndUpdateSubToursLength2(vector< vector <NODE> > cycles)
{
	
	for (int k = 0; k < cycles.size(); k++)
	{
		//cout << "Lifting cycle numbered " << k << endl;
		bool change = liftUntilViolatedNode(cycles[k]); //do the lift
		//if (change == false && k > 0)
		//{
		//	if (cycles[k].size() > 1)
		//		UpdateArcsFollowingCycle(cycles[k], cycles[k].size() - 1); //no time-window violation but we perform lift if cycle >= 3

		//}
		if (change == false && k > 0)
		{
			if (cycles[k].size() > 2)
				UpdateArcsFollowingCycle(cycles[k], cycles[k].size() - 1); //no time-window violation but we perform lift if cycle >= 3

		}
		else if (change == false && k == 0 && MIP)
			addaSingleSubTourConstraint(cycles[0]);
	}

	//if (MIP)
	//	updateSubTourLength2ConstraintsVarName(newArcNames);

	globalChange = globalChange | (newArcNames.size() > 0);
	cout << "Number of new arcs:" << newArcNames.size() << endl;
	newArcNames.clear();
 
}

void LiftManyCyclesAndSubtourCycleLength2(vector< vector <NODE> > cycles)
{
	for (int k = 0; k < cycles.size(); k++)
	{
		//cout << "Lifting cycle numbered " << k << endl;
		bool change = liftUntilViolatedNode(cycles[k]); //do the lift
		if (change == false && k > 0)
		{
			if (cycles[k].size() > 2)
				UpdateArcsFollowingCycle(cycles[k], cycles[k].size() - 1); //no time-window violation but we perform lift 
			else
				addaSingleSubTourConstraint(cycles[k]);

		}
			
		else if (k==0 && change ==false)
			addaSingleSubTourConstraint(cycles[0]); //cycle 0, add subtour constraint
		//cout << "*************************************" << endl;
	}
}

void addAllSubTourConstraints(vector< vector <NODE> > cycles)
{
	for (int k = 0; k < cycles.size(); k++)
	{
		
		bool change = liftUntilViolatedNode(cycles[k]); //do the lift
		if (change == false)
				addaSingleSubTourConstraint(cycles[k]);

	}
}

void LiftCycleLength2(vector<NODE> cycle)
{
	int i = cycle[0].first;
	int t = cycle[0].second;
	int j = cycle[1].first;
	int t_prime = cycle[1].second;

	int curTime = t, prevTime = t_prime;

	deletedVarList.insert(VarIndex(i, t, j, t_prime));
	
	set<NODE> saddedNodes;
	set<VarIndex> saddedVars;
	set<VarIndex> sdeletedVars;

	for (int k = 0; ;k++)
	{

		
		//ARC_MODIFICATION(old_arc, new_arc);
		//
		////actually adding arcs to the model
		//addNodeArcToModel(G, PTEG, deletedVarList, addedVarList, addedNodeList);

	}

 
}

void splitStringTerminal(string s, int &i, int &j)
{
	i = 0;
	int k;
	for (k = 2; s[k] != ','; k++)
		i = i * 10 + s[k] - '0';
	k++;
	for (; s[k] != '('; k++)
		;
	k++;
	j = 0;
	for (; s[k] != ','; k++)
		j = j * 10 + s[k] - '0';
}

void splitStringAll(string s, int &i, int &t, int &j, int &t_prime)
{
	int k;
	i = 0;
	for (k = 2; s[k] != ','; k++)
		i = i * 10 + s[k] - '0';
	t = 0; k++;
	for (; s[k] != ')'; k++)
		t =t*10 + s[k]-'0';
	k += 2;

	j = 0;
	for (; s[k] != ','; k++)
		j = j * 10 + s[k] - '0';
	k++;
	t_prime = 0;
	for (; s[k] != ')'; k++)
		t_prime = t_prime * 10 + s[k] - '0';
}

void splitStringTime(string s, int &t, int &t_prime)
{
	t = 0;
	int k;
	for (k = 2; s[k] != ','; k++) ;
	for (k = 2; s[k] != ')'; k++);
		t = t * 10 + s[k] - '0';
	k++;
	
	for (; s[k] != ','; k++)	;
	k++;
	t_prime = 0;
	for (; s[k] != ')'; k++)
		t_prime = t_prime * 10 + s[k] - '0';
}


void addAllSubTourLength2()
{
	
	//Add subtour constraint length 2
	map < pair<int, int >, GRBLinExpr > mSubToursLength2;

	for (int i = 1; i < G.N0; i++)
		for (int j = i + 1; j < G.N0; j++)
			if (G.tau[i][j] + G.tau[j][i] < 1e6)
				mSubToursLength2[make_pair(i, j)] = GRBLinExpr(0.0);

	GRBVar *var = model.getVars();
	for (int k = 0; k < model.get(GRB_IntAttr_NumVars); k++)
	{
		string name = var[k].get(GRB_StringAttr_VarName);
		int i, j;
		
		splitStringTerminal(name, i, j);
		
		if (G.tau[i][j] + G.tau[j][i] > 1e6)
			continue;
		
		int u = min(i, j);
		int v = max(i, j);

		mSubToursLength2[make_pair(u, v)] += var[k];
	}

	for (int i = 1; i < G.N0; i++)
		for (int j = i + 1; j < G.N0; j++)
		{
			if (G.tau[i][j] + G.tau[j][i] > 1e6)
				continue; 
			ostringstream subTour;
			subTour << "SubTour_" << i << "." << j;
			model.addConstr(mSubToursLength2[make_pair(i, j)] <= 1, subTour.str()); //sub tour constraint length 2
			constraintSet[subTour.str()] = mSubToursLength2[make_pair(i, j)];
		}

	model.update();
}

void addAllSubTourLength2Type2()
{

	
	//Add subtour constraint length 2
	map < pair<int, int>, GRBLinExpr > mSubToursLength2;

	GRBVar *var = model.getVars();
	for (int k = 0; k < model.get(GRB_IntAttr_NumVars); k++)
	{
		string name = var[k].get(GRB_StringAttr_VarName);
		int i, j, t, t_prime;

		splitStringAll(name, i, t, j , t_prime);

		if (i == j || i == 0 || j == 0)
			continue;

		if (t_prime >= t)  //forward arc
			mSubToursLength2[make_pair(i,t)] += var[k];

		if (t >= t_prime) //backward arc
		{
			mSubToursLength2[make_pair(j, t_prime)] += var[k];
			//allSubTour.insert(make_pair(j, t_prime));
		}
			
	}

	for (map< pair<int, int>, GRBLinExpr>::iterator it = mSubToursLength2.begin(); it != mSubToursLength2.end(); it++)
		//if (allSubTour.find(it->first) != allSubTour.end())
		{
			ostringstream subTour;
			subTour << "NoSubTour_" << it->first.first << "." << it->first.second;
			model.addConstr(it->second <= 1, subTour.str()); //sub tour constraint length 2
		}

	model.update();
	cout << "Here" << endl;
}

void fixedArcs(vector<VarIndex> selectedArcs)
{
	int cnt1 = 0;
	bool able[MAXN][MAXN];
	memset(able, 0, sizeof(able));
	for (int k = 0; k < selectedArcs.size(); k++)
		able[selectedArcs[k].i][selectedArcs[k].j] = 1, cnt1++;

	//model.set(GRB_CharAttr_VType, model.getVars(), GRB_BINARY, model.get(GRB_IntAttr_NumVars));

	int cnt = 0;
	GRBVar *var = model.getVars();
	for (int k = 0; k < model.get(GRB_IntAttr_NumVars); k++)
	{
		string name = var[k].get(GRB_StringAttr_VarName);
		int i, j;
		//cout << name << endl;
		splitStringTerminal(name, i, j);
		
	
		if (able[i][j] == 0)
			var[k].set(GRB_DoubleAttr_UB, 0.0);
		else
			var[k].set(GRB_CharAttr_VType, GRB_BINARY), cnt++;
	}
	cout << endl << cnt1 << " " << cnt << " " << model.get(GRB_IntAttr_NumVars) << endl;

}

void fixeNoBackWardArcs(vector<VarIndex> selectedArcs)
{
	int cnt1 = 0;

	int cnt = 0;
	GRBVar *var = model.getVars();
	for (int k = 0; k < model.get(GRB_IntAttr_NumVars); k++)
	{
		string name = var[k].get(GRB_StringAttr_VarName);
		int t, t_prime;
		//cout << name << endl;
		splitStringTerminal(name, t, t_prime);
		if (t > t_prime)
			var[k].set(GRB_DoubleAttr_UB, 0.0), cnt1++;
		else
			var[k].set(GRB_CharAttr_VType, GRB_BINARY), cnt++;
	}
	cout << endl << cnt1 << " " << cnt << " " << model.get(GRB_IntAttr_NumVars) << endl;

}

void changeAllToBinaryAndAddSubTours()
{
	GRBVar *var = model.getVars();
	for (int k = 0; k < model.get(GRB_IntAttr_NumVars); k++)
		var[k].set(GRB_CharAttr_VType, GRB_BINARY);

	cout << model.get(GRB_IntAttr_NumVars) << endl;

	//fixeNoBackWardArcs(selectedArcs);
	addAllSubTourLength2Type2();
	model.update();

}

void changeSomeToBinaryAndAddSubTours()
{
	GRBVar *var = model.getVars();
	for (int k = 0; k < model.get(GRB_IntAttr_NumVars); k++)
		if (var[k].get(GRB_DoubleAttr_X) > 0.0 && var[k].get(GRB_DoubleAttr_X) < 1.0)
			var[k].set(GRB_CharAttr_VType, GRB_BINARY);

	cout << model.get(GRB_IntAttr_NumVars) << endl;

	//fixeNoBackWardArcs(selectedArcs);
	//addAllSubTourLength2Type2();
	model.update();

}

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

			 
			 //Optimize model
			//tmpModel = model.presolve();

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
			vector<varInfo> selectedVars;

			selectedArcs.clear();
			arcValues.clear();

			//model.write("model.lp");

			//traverse the variable list and extract variables' value
			for (map<VarIndex, GRBVar>::iterator var_it = x_a.begin(); var_it != x_a.end(); var_it++)
			{
				VarIndex idx = var_it->first;
				GRBVar arc_var = var_it->second;
				
				//cout << "Extract variable :" << idx << endl;
				
				if (arc_var.get(GRB_DoubleAttr_X) > 0.01)
				{
					selectedArcs.push_back(idx);
					arcValues.push_back(arc_var.get(GRB_DoubleAttr_X));
					//selectedVars.push_back((varInfo){arc_var.get(GRB_DoubleAttr_X), idx, selectedArcs.size()-1 });
				}
			}

			////display selected arcs
			//cout << "Selected Arcs" << endl;
			//for (int k = 0; k < selectedArcs.size(); k++)
			//	cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << " : " << arcValues[k] << endl;

			////display selected arcs
			//if (MIP)
			//{
			//	cout << "Selected Arcs" << endl;
			//	for (int k = 0; k < selectedArcs.size(); k++)
			//		cout << k<<":(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ") : " << arcValues[k] << endl;;
			//	cout << endl;

			//}

			//bool validSolution = buildCycles2(selectedArcs, cycles);
			
			//bool validSolution = buildCyclesRelaxation(selectedVars, selectedArcs, cycles);
			//exit(0);


			bool validSolution;
			if (MIP == false)
				validSolution = buildCyclesRelaxation(selectedArcs, cycles);
			else 
				validSolution = buildCycles(selectedArcs, cycles);
			 
			 

			if (validSolution == false)
			{
				cout << "Selected Arcs" << endl;
				for (int k = 0; k < selectedArcs.size(); k++)
					cout << "(" << selectedArcs[k].i << "," << selectedArcs[k].t << ")-(" << selectedArcs[k].j << "," << selectedArcs[k].t_prime << ")" << endl;

				displayCycles(cycles);
				model.write("wrong.lp");
				exit(0);
			}
			
			//model.write("correct.lp");

			earliestFirst(cycles);
			
			cout << "Number of cycles: " << cycles.size() << endl;
			//list of cycles
			//cout << "List of cycles after moving the earliest node to the first position" << endl;
			if (MIP == true)
				displayCycles(cycles);

			//if (Obj < lastObj)
			//{
			//	model.write("zzz.lp");
			//	exit(0);
			//}
			//
			//model.write("xxx.lp");

			globalChange = false;

			if (cycles.size()>1) //we have more than we sub-tours
			{

				////addSubTourEliminationConstraints1(cycles); //remove them

				//LiftOnlyFirstCycle(cycles);
				
				//LiftManyCyclesAndSubtourCycleLength2(cycles);

				//LiftManyCyclesExceptFirstCycle(cycles);
				LiftManyCyclesExceptFirstCycleAndUpdateSubToursLength2(cycles);

				//if (MIP == false)
				//	LiftManyCyclesExceptFirstCycleAndUpdateSubToursLength2(cycles);
				//else
				//	addAllSubTourConstraints(cycles);
			}
			else //checking time windows constraints
			{
				int violatedTerminal = travellingTimeWindowCondition(cycles[0]);

				vector<NODE> cycle = cycles[0];

				if (violatedTerminal != -1) //violation of time window at a terminal
				{
					UpdateArcsFollowingCycle(cycle, violatedTerminal);
					
					//if (MIP)
					//	updateSubTourLength2ConstraintsVarName(newArcNames);
					
					globalChange = globalChange | (newArcNames.size() > 0);

					cout << " Number of new arcs: " << newArcNames.size() << endl;
					newArcNames.clear();
 				}
					

				else
				{
					cout << "Obtain feasible solution regarding time window!" << endl;
					cout << "Obj = " << Obj << endl;
					
					for (int k = 0; k < cycles[0].size(); k++)
						cout << cycles[0][k].first + 1 << " ";
					cout << endl << "Execution time: " << (clock() - start_s) / double(CLOCKS_PER_SEC) << endl;

 					cout << "Optimization done! " << endl;
			
					return; //we have a good solution
				}
					
			}
			 
			if (globalChange == false)
			{
				if (changeVarType == false)
				{
					

					//REMEMBER TO MODIFY ADDNODEARCTOMODEL

					//addAllSubTourLength2();
					changeSomeToBinaryAndAddSubTours();

					MIP = changeVarType = true;
					MIP = changeVarType = false, globalChange = true;

					//model.write("final.lp");
					//exit(0);
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
		cout << "Error code = " << e.getErrorCode() << "in Test2"<<endl;
		cout << e.getMessage() << endl;
		exit(0);
	}
	catch (...) {
		cout << "Exception during optimization" << endl;
		/*return false;*/
	}
	
	 
	for (int i = 0; i < cycles.size(); i++)
	{
		cout << "Solution: ";
		for (int j = 1; j < cycles[i].size(); j++)
			if (cycles[i][j].first != cycles[i][j-1].first)
				cout << cycles[i][j-1].first + 1<< "-";
		cout << cycles[i][cycles[i].size() - 1].first + 1 << endl;
		//if (i==0) cout << 1 << endl;
		//else cout << endl;
	} 

	//unknownreason = 1;

}



int main(int   argc,
	char *argv[])
{

	cout << "File name:" << argv[1] << endl;

	//readOriginalGraph(G, argv[1]);
	//readOriginalGraph_rfsilva(G, argv[1]);
	readOriginalGraph_Ascheuer(G, argv[1]);
	//testReadingGraph(G);
	
	
	preprocessingPrecedenceConstraints(G);

	//for (int i = 0; i < G.N0; i++)
	//	cout << i+1<<":"<<G.e[i] << " " << G.l[i] << endl;

	
	cout << "Starting the solution procedure!" << endl;
	//testReadingGraph(G);

	//CreateInitialParitalGraph(G, PTEG);
	CreateInitialParitalGraphWithOutZero(G, PTEG);

	 
	InitialModelGeneration(G, PTEG);

	
	
	//model.write("tsp_ori.lp");
	//return 0;
	model.getEnv().set(GRB_IntParam_OutputFlag, 0);
	model.getEnv().set(GRB_IntParam_Threads, 1);
	int start_s = clock();


	//freopen(argv[2], "wt", stdout);

 	Test2();
	
	if (unknownreason)
	{
		string lpmodel(argv[2]);
		lpmodel += ".lp";
		model.write(lpmodel);

	}
	//model.write("final.lp");

	return 0;
}