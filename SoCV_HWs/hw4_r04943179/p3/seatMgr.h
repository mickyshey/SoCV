// file name [ seatMgr.h ]

#include <iostream>
#include <vector>

#include "sat.h"

using namespace std;

class SeatMgr
{
public:
	SeatMgr() { _s.initialize(); }
	~SeatMgr() {}

	void createMatrix(unsigned num);
	void reportMatrix();

//	constraint
	void addConstraint(const vector<string>& tokens);
	void addAssign(unsigned man, unsigned seat);
	void addAssignNot(unsigned man, unsigned seat);
	void addLessThan(unsigned man1, unsigned man2);
	void addAdjacent(unsigned man1, unsigned man2);
	void addAdjacentNot(unsigned man1, unsigned man2);

//	solve
	void solve();
private:
	
	vector< vector <Var> > _seatMatrix;
	SatSolver _s;
};
