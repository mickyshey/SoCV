// file name [ seatAss.cpp ]

#include <iostream>
#include <fstream>
#include <string>

#include "sat.h"
#include "seatMgr.h"
#include "parse.h"

using namespace std;

int main(int argc, char** argv) {
	ifstream f;
	f.open(argv[1]);
	string s;

	SeatMgr seatMgr;
	getline(f, s);
	seatMgr.createMatrix(stoi(s));
	//seatMgr.reportMatrix();

	vector<string> tokens;
	while(getline(f, s)) {
		tokens = split(s, " \t\r(,)\n");
		//for( unsigned i = 0; i < tokens.size(); ++i )
		//	cout << tokens[i] << " ";
		//cout << endl;
		seatMgr.addConstraint(tokens);
	}

	seatMgr.solve();

	f.close();
}
