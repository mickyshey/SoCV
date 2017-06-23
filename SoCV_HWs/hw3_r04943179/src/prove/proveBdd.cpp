/****************************************************************************
  FileName     [ proveBdd.cpp ]
  PackageName  [ prove ]
  Synopsis     [ For BDD-based verification ]
  Author       [ ]
  Copyright    [ Copyleft(c) 2010 LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include <iostream>
#include <iomanip>
#include "v3NtkUtil.h"
#include "v3StrUtil.h"
#include "v3Msg.h"
#include "bddMgrV.h"

void
BddMgrV::buildPInitialState()
{
   // TODO : remember to set _initState
   // Set Initial State to All Zero
   V3NtkHandler* const handler = v3Handler.getCurHandler();
   V3Ntk* const ntk = handler -> getNtk();
   BddNodeV initState = BddNodeV::_one;
   for( unsigned i = 0, n = ntk -> getLatchSize(); i < n; ++i ) {
      const V3NetId& nId = ntk -> getLatch(i);
      BddNodeV tmp = getBddNodeV(nId.id);
	  initState &= ~tmp;
   }
   _initState = initState; 
}

void
BddMgrV::buildPTransRelation()
{
   // TODO : remember to set _tr, _tri
   V3NtkHandler* const handler = v3Handler.getCurHandler();
   V3Ntk* const ntk = handler -> getNtk();
   BddNodeV tri = BddNodeV::_one; 
   for( unsigned i = 0, n = ntk -> getLatchSize(); i < n; ++i ) {
      const V3NetId& nId = ntk -> getLatch(i);
	  const V3NetId& cId = ntk -> getInputNetId(nId, 0);
      BddNodeV nState = getBddNodeV(handler -> getNetNameOrFormedWithId(nId) + "_ns");
	  BddNodeV nFunc = cId.cp ? ~getBddNodeV(cId.id) : getBddNodeV(cId.id);
      tri &= ~(nState ^ nFunc);
   }
   _tri = tri;
   BddNodeV tr = tri;
   for( unsigned i = 0, n = ntk -> getInputSize(); i < n; ++i )
      tr = tr.exist(i + 1);
   _tr = tr;
}

void
BddMgrV::buildPImage( int level )
{
   // TODO : remember to add _reachStates and set _isFixed
   // Note:: _reachStates record the set of reachable states
   if( _isFixed ) {
      cout << "Fixed point is reached (time : " << _reachStates.size() << ")" << endl;	
	  return; 
   }
   V3NtkHandler* const handler = v3Handler.getCurHandler();
   V3Ntk* const ntk = handler -> getNtk();
   unsigned cStateIdx = ntk -> getInputSize() + ntk -> getInoutSize();
   BddNodeV tr = _tr;
   for( int i = 0, n = level; i < n; ++i ) {
   	  cout << "Computing reachable state (time : " << _reachStates.size() << " )...\r" << std::flush;
   	  cout << setw(50) << "\r";
      BddNodeV reachStates = getPReachState();
      BddNodeV nextReachStates = reachStates & tr;
	  for( unsigned j = cStateIdx, m = cStateIdx + ntk -> getLatchSize(); j < m; ++j )
	     nextReachStates = nextReachStates.exist(j + 1);			// exist(current state) 
	  bool isMoved;
	  nextReachStates = nextReachStates.nodeMove(cStateIdx + ntk -> getLatchSize() + 1, cStateIdx + 1, isMoved);		// replace next state v with current state v
	  if( nextReachStates == reachStates ) {
	     _isFixed = true;	
      	 cout << "Fixed point is reached (time : " << _reachStates.size() << ")" << endl;	
		 return;
	  }
	  else _reachStates.push_back(nextReachStates);
   }
}

void 
BddMgrV::runPCheckProperty( const string &name, BddNodeV monitor )
{
   // TODO : prove the correctness of AG(~monitor)
   BddNodeV reachStates = getPReachState();
   BddNodeV intersect = reachStates & monitor;
   if( intersect == BddNodeV::_zero ) {
      cout << "Monitor \"" << name << "\" is safe";
	  if( !_isFixed ) cout << " up to time " << _reachStates.size();
	  cout << "." << endl;
   }
   else {
      //cout << "bug found ... start genning Cex ... " << endl;
      V3NtkHandler* const handler = v3Handler.getCurHandler();
      V3Ntk* const ntk = handler -> getNtk();

	  vector<BddNodeV> vPi;
	  BddNodeV cube = intersect.getCube();
	  BddNodeV pi = getPI(cube);
      BddNodeV cState = getCState(cube);
	  vPi.push_back(pi);
      unsigned cStateIdx = ntk -> getInputSize() + ntk -> getInoutSize();
	  bool isMoved;
	  for( unsigned i = 0, n = _reachStates.size(); i < n; ++i ) {
		 BddNodeV nState = cState.nodeMove(cStateIdx + 1, cStateIdx + ntk -> getLatchSize() + 1, isMoved );		// replace X with Y
         nState &= _tri;
		 unsigned ith = 0;
		 while( 1 ) {
			cube = nState.getCube(ith);
			cState = getCState(cube);
    		intersect = cState & (i == _reachStates.size() - 1 ? _initState : _reachStates[_reachStates.size() - i - 2]);
		    if( intersect != BddNodeV::_zero ) {
			   pi = getPI(cube);
			   vPi.push_back(pi);
			   break;
			}
			cout << "no match, get next cube ..." << endl;
			++ith;
		 }
		 if( cState == _initState ) break;
	  }
	  if( cState != _initState ) cout << "something wrong !!" << endl;
	  for( unsigned i = 0, n = vPi.size(); i < n; ++i ) {
	     string s = vPi[i].toString();
		 cout << i << ": ";
		 if( s.size() ) {
			vector<string> tokens;
			string token;
			size_t begin = 0;
			while( begin != string::npos ) {
				begin = v3StrGetTok(s, token, begin);
				tokens.push_back(token);
			}
			unsigned idx = 0;
			for( unsigned j = 0, m = ntk -> getInputSize(); j < m; ++j ) {		// take care of missing level, i.e. (1) !(2) (4) ...
				string tmp = tokens[idx];
				unsigned iii = tmp[tmp.find_first_of("(") + 1] - '0';
				if( iii > j + 1 ) cout << "1"; 							// don't-care -> 1
				else {
					if( tmp.find_first_of("(") ) cout << "0";
					else cout << "1";	
				++idx;
				}
			}
			/*size_t idx = 0;
		    while( 1 ) {
			   idx = s.find_first_of("(", idx);
			   if( idx == string::npos ) break;
			   if( s[idx - 1] == '!' ) cout << "0";
			   else cout << "1";
			   ++idx;
			}*/
		 }
		 else{
		    for( unsigned j = 0, m = ntk -> getInputSize(); j < m; ++j )
			   cout << "1";
		 }		 
		 cout << endl;
	  }
   }
}

BddNodeV
BddMgrV::getPI(BddNodeV b)
{
   V3NtkHandler* const handler = v3Handler.getCurHandler();
   V3Ntk* const ntk = handler -> getNtk();
   unsigned cStateIdx = ntk -> getInputSize() + ntk -> getInoutSize();
   unsigned nStateIdx = cStateIdx + ntk -> getLatchSize();
   BddNodeV tmp = b;
   for( unsigned i = cStateIdx, n = nStateIdx; i < n; ++i ) 							// exist X
      tmp = tmp.exist(i + 1);
   for( unsigned i = nStateIdx, n = nStateIdx + ntk -> getLatchSize(); i < n; ++i ) 	// exist Y
	  tmp = tmp.exist(i + 1);
   return tmp; 
}

BddNodeV
BddMgrV::getCState(BddNodeV b)
{
   V3NtkHandler* const handler = v3Handler.getCurHandler();
   V3Ntk* const ntk = handler -> getNtk();
   unsigned nStateIdx = ntk -> getInputSize() + ntk -> getInoutSize() + ntk -> getLatchSize();
   BddNodeV tmp = b;
   for( unsigned i = 0, n = ntk -> getInputSize(); i < n; ++i ) 								// exist I
      tmp = tmp.exist(i + 1);
   for( unsigned i = nStateIdx, n = nStateIdx + ntk -> getLatchSize(); i < n; ++i ) 			// exist Y
	  tmp = tmp.exist(i + 1);
   return tmp;
}
