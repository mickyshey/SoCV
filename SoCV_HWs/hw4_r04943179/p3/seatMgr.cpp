// file name [ seatMgr.cpp ]

#include <iostream>
#include <cassert>

#include "seatMgr.h"

// 	1. Construct the seatMatrix
//	2. Add basic seat assignment constraint
void
SeatMgr::createMatrix(unsigned num)
{
	Var v;
	for( unsigned i = 0; i < num; ++i ) {
		vector<Var> vVar;
		for( unsigned j = 0; j < num; ++j ) {
			v = _s.newVar();
			vVar.push_back(v);
		}
		_seatMatrix.push_back(vVar);
	}

	vec<Lit> lits;
	vec<Lit> lits2;
//	(g00 + g01 + g02)
//	(g00 + g10 + g20)
	for( unsigned i = 0; i < num; ++i ) {
		for( unsigned j = 0; j < num; ++j ) {
			v = _seatMatrix[i][j];
			lits.push(Lit(v));
			v = _seatMatrix[j][i];
			lits2.push(Lit(v));
		}
		_s.addClause(lits);
		_s.addClause(lits2);
		lits.clear();
		lits2.clear();
	}
//	(~g00 + ~g01)(~g00 + ~g02)(~g01 + ~g02)
//	(~g00 + ~g10)(~g00 + ~g20)(~g10 + ~g20)
	for( unsigned i = 0; i < num; ++i ) {
		for( unsigned j = 0; j < num; ++j ) {
			for( unsigned k = j + 1; k < num; ++k ) {
				//cout << "i: " << i << ", j: " << j << ", k: " << k << endl;
				v = _seatMatrix[i][j];
				//cout << v << " ";
				lits.push(~Lit(v));
				v = _seatMatrix[i][k];
				//cout << v << endl;
				lits.push(~Lit(v));	
				_s.addClause(lits);
				lits.clear();
				v = _seatMatrix[j][i];
				//cout << v << " ";
				lits.push(~Lit(v));
				v = _seatMatrix[k][i];
				//cout << v << endl;
				lits.push(~Lit(v));	
				_s.addClause(lits);
				lits.clear();
			} 
		}
	}
}

void
SeatMgr::reportMatrix()
{
	unsigned num = _seatMatrix.size();
	for( unsigned i = 0; i < num; ++i ) {
		for( unsigned j = 0; j < num; ++ j) {
			cout << _seatMatrix[i][j] << " ";	
		}
		cout << endl;
	}
}

void
SeatMgr::addConstraint(const vector<string>& tokens)
{
	assert(tokens.size() == 3);
	unsigned arg1 = stoi(tokens[1]);
	unsigned arg2 = stoi(tokens[2]);
	if( tokens[0] == "Assign" ) addAssign(arg1, arg2);
	else if( tokens[0] == "AssignNot" ) addAssignNot(arg1, arg2);
	else if( tokens[0] == "LessThan" ) addLessThan(arg1, arg2);
	else if( tokens[0] == "Adjacent" ) addAdjacent(arg1, arg2);
	else if( tokens[0] == "AdjacentNot" ) addAdjacentNot(arg1, arg2);
	else assert(0);
}

void
SeatMgr::addAssign(unsigned man, unsigned seat)
{
	Var v = _seatMatrix[man][seat];
	_s.assertProperty(v, true);
}

void
SeatMgr::addAssignNot(unsigned man, unsigned seat)
{
	Var v = _seatMatrix[man][seat];
	_s.assertProperty(v, false);
}

void
SeatMgr::addLessThan(unsigned man1, unsigned man2)
{
	vec<Lit> lits;
	Var v;
	unsigned num = _seatMatrix.size();
	for( unsigned i = 0; i < num; ++i ) {
		//cout << "i: " << i << endl;
		v = _seatMatrix[man1][i];
		//cout << v << " ";
		lits.push(~Lit(v));
		for( unsigned j = i + 1; j < num; ++j ) {
			v = _seatMatrix[man2][j];
			//cout << v << " ";
			lits.push(Lit(v));
		}
		//cout << endl;
		_s.addClause(lits);
		lits.clear();
	}
}

void
SeatMgr::addAdjacent(unsigned man1, unsigned man2)
{
	vec<Lit> lits;
	Var v;
	unsigned num = _seatMatrix.size();
	//cout << "first" << endl;
	v = _seatMatrix[man1][0];
	//cout << v << " ";
	lits.push(~Lit(v));
	v = _seatMatrix[man2][1];
	//cout << v << endl;
	lits.push(Lit(v));
	_s.addClause(lits);
	lits.clear();
	for( unsigned i = 1; i < num - 1; ++i ) {
		//cout << "i: " << i << endl;
		v = _seatMatrix[man1][i];
		//cout << v << " ";
		lits.push(~Lit(v));
		v = _seatMatrix[man2][i - 1];
		//cout << v << " ";
		lits.push(Lit(v));
		v = _seatMatrix[man2][i + 1];
		//cout << v << endl;
		lits.push(Lit(v));
		_s.addClause(lits);
		lits.clear();
	}
	//cout << "last" << endl;
	v = _seatMatrix[man1][num - 1];
	//cout << v << " ";
	lits.push(~Lit(v));
	v = _seatMatrix[man2][num - 2];
	//cout << v << endl;
	lits.push(Lit(v));
	_s.addClause(lits);
	lits.clear();
}

void
SeatMgr::addAdjacentNot(unsigned man1, unsigned man2)
{
	vec<Lit> lits;
	Var v;
	unsigned num = _seatMatrix.size();
	//cout << "first" << endl;
	v = _seatMatrix[man1][0];
	//cout << v << " ";
	lits.push(~Lit(v));
	v = _seatMatrix[man2][1];
	//cout << v << endl;
	lits.push(~Lit(v));
	_s.addClause(lits);
	lits.clear();
	for( unsigned i = 1; i < num - 1; ++i ) {
		//cout << "i: " << i << endl;
		v = _seatMatrix[man1][i];
		//cout << v << " ";
		lits.push(~Lit(v));
		v = _seatMatrix[man2][i - 1];
		//cout << v << endl;
		lits.push(~Lit(v));
		_s.addClause(lits);
		lits.clear();

		v = _seatMatrix[man1][i];
		//cout << v << " ";
		lits.push(~Lit(v));
		v = _seatMatrix[man2][i + 1];
		//cout << v << endl;
		lits.push(~Lit(v));
		_s.addClause(lits);
		lits.clear();
	}
	//cout << "last" << endl;
	v = _seatMatrix[man1][num - 1];
	//cout << v << " ";
	lits.push(~Lit(v));
	v = _seatMatrix[man2][num - 2];
	//cout << v << endl;
	lits.push(~Lit(v));
	_s.addClause(lits);
	lits.clear();
}

void
SeatMgr::solve()
{
	if( _s.solve() ) {
		cout << "Satisfiable assignment:" << endl;
		unsigned num = _seatMatrix.size();
		Var v;
		for( unsigned i = 0; i < num; ++i ) {
			cout << i << "(";
			for( unsigned j = 0; j < num; ++j ) {
				v = _seatMatrix[j][i];
				if( _s.getValue(v) == 1 ) {
					cout << j << ")";
					break;
				}
			}
			if( i == num - 1 ) { cout << endl; break; }
			cout << ", ";
		} 
	}
	else {
		cout << "No satisfiable assignment can be found." << endl;
	}
}
