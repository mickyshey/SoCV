/****************************************************************************
  FileName     [ PDRDef.h ]
  PackageName  [ pdr ]
  Synopsis     [ Define pdr basic classes ]
  Author       [ ]
  Copyright    [ Copyright(c) 2016 DVLab, GIEE, NTU, Taiwan ]
 ****************************************************************************/

#define show_address 0

#include <iostream>
#include <vector>
#include "v3Ntk.h"

#ifndef PDRDEF_H
#define PDRDEF_H

using namespace std;

class Value3 {
  // This is not dual rail encoding,
  // If the _dontCare is one it means it's X,
  // Otherwise it's decided by _bit
 public:
  Value3() : _bit(0), _dontCare(1) {}
  Value3(bool b, bool d): _bit(b), _dontCare(d) {}
  Value3(const Value3& a) {
    _bit = a._bit;
    _dontCare = a._dontCare;
  }
  Value3 operator & (Value3 a) const {
/*
    if ((_bit == 0 && _dontCare == 0) || a == Value3(0, 0)) return Value3(0, 0);
    else if (a._dontCare || _dontCare) return Value3(0, 1);
    else return Value3(1, 0);
*/
		if( a._dontCare || _dontCare ) return Value3(0, 1);
		else return Value3(a._bit & _bit, 0);
  }
  Value3 operator & (bool a) const {
/*
    if (a == 0) return Value3(0, 0);
    else if (_dontCare) return Value3(0, 1);
    else return Value3(1, 0);
*/
		if( _dontCare ) return Value3(0, 1);
		else return Value3(a & _bit, 0);
  }
  Value3 operator | (Value3 a) const {
/*
    if ((_bit == 1 && _dontCare == 0) || a == Value3(1,0)) return Value3(1, 0);
    else if (a._dontCare || _dontCare) return Value3(0, 1);
    else return Value3(0, 0);
*/
		if( a._dontCare || _dontCare ) return Value3(0, 1);
		else return Value3(a._bit | _bit, 0);
  }
  Value3 operator | (bool a) const {
/*
    if (a) return Value3(1, 0);
    else if (_dontCare) return Value3(0, 1);
    else return Value3(0, 0);
*/
		if( _dontCare ) return Value3(0, 1);
		else return Value3(a | _bit, 0);
  }
  Value3 operator ~ () const {
    if (_dontCare) return Value3(0, 1);
    else return Value3(~_bit, 0);
    //else return Value3(!_bit, 0);
  }
  bool operator == (const Value3& a) const {
/*
    if (_dontCare ^ a._dontCare) return false;
    else if (_dontCare && a._dontCare) return true;
    else if (_bit == a._bit) return true;
    else return false;
*/
		if( a._dontCare ^ _dontCare ) return false;
		else return ((a._dontCare & _dontCare) || (a._bit && _bit));
  }
  bool operator != (const Value3& a) const {
    return !((*this) == a);
  }
  bool _bit;
  bool _dontCare;
};

class Cube {
 public:
  Cube(){
    // cube is all zeros for default constructor
    _latchValues = new Value3[_L];
    for (unsigned i = 0; i < _L; ++i) {
      _latchValues[i]._bit = 0;
      _latchValues[i]._dontCare = 0;
    }
	// modified by r04943179
	_states.clear();
	_signature = 0;
	// end of modification
  }
  Cube(bool* b) {
    _latchValues = new Value3[_L];
    for (unsigned i = 0; i < _L; ++i){
      _latchValues[i]._bit = b[i];
    }
  }
  Cube(bool* b, bool* d) {
    _latchValues = new Value3[_L];
    for (unsigned i = 0; i < _L; ++i) {
      _latchValues[i]._bit = b[i];
      _latchValues[i]._dontCare = d[i];
    }
  }
  Cube(Cube* c) {
    if (c->_latchValues) {
      _latchValues = new Value3[_L];
      for (unsigned i = 0; i < _L; ++i) {
        _latchValues[i] = c->_latchValues[i];
      }
    } else {
      _latchValues = NULL;
    }
	// modified by r04943179
	setStates(c -> getStates());
	// end of modification
  }
  Cube(const Cube& c) {
    if (c._latchValues) {
      _latchValues = new Value3[_L];
      for (unsigned i = 0; i < _L; ++i) {
        _latchValues[i] = c._latchValues[i];
      }
    } else {
      _latchValues = NULL;
    }
	// modified by r04943179
	setStates(c.getStates());
	// end of modification
  }
  ~Cube() {
    if (_latchValues) {
      delete [] _latchValues;
    }
    _latchValues = NULL;
  }
	// better approach using sigature-based algorithm
	// TODO
  bool subsumes(Cube* s) const {
    for (unsigned i = 0; i < _L; ++i) {
      if (!_latchValues[i]._dontCare) {
        if (s->_latchValues[i]._dontCare) return false;
        if (s->_latchValues[i]._bit != _latchValues[i]._bit) return false;
      }
    }
    return true;
  }
  void show() {
    // debug fuction
    for (unsigned i = _L - 1; i != 0; --i) {
      if (_latchValues[i]._dontCare) cerr << "X";
      else cerr << ((_latchValues[i]._bit) ? "1" : "0");
    }
    if (_latchValues[0]._dontCare) cerr << "X";
    else cerr << ((_latchValues[0]._bit) ? "1" : "0");
    cerr << endl;
  }

	// modified by r04943179
	const vector<V3NetId>& getStates() const { return _states; }
	const size_t getSignature() const { return _signature; }
	void setStates(const vector<V3NetId>& v);
	void showStates() const;
	vector<V3NetId>		_states;
	size_t					_signature;
	// end of modification
  static unsigned _L;               // latch size
  Value3*         _latchValues;     // latch values
};

inline void Cube::showStates() const {
	for( unsigned i = 0; i < _states.size(); ++i ) {
		std::cout << _states[i].id << "[" << _states[i].cp << "] ";
	}
	std::cout << std::endl;
}

inline void Cube::setStates(const vector<V3NetId>& v) {
	_states = v; _signature = 0;
	// change the signature according to states
	// TODO
}

class TCube
{
 public:
  TCube(): _cube(NULL), _frame(-1) {
    cerr << "NULL constructor" << endl;
  }
  TCube(Cube* c, unsigned d): _cube(c), _frame((int)d) {
    if (show_address) {
      cerr << "default constructor" << endl;
      cerr << c << endl;
    }
  }
  TCube(const TCube& t) {
    if (show_address) {
      cerr << "copy constructor" << endl;
      cerr << _cube << endl;
      cerr << t._cube << endl;
    }
    _cube = t._cube;
    _frame = t._frame;
  }
  ~TCube(){
    if (show_address) cerr << "destructor" << endl;
  }
  TCube& operator = (const TCube& t){
    if (show_address) {
      cerr << "= constructor" << endl;
      cerr << _cube << endl;
      cerr << t._cube << endl;
    }
    _cube = t._cube;
    _frame = t._frame;
    return (*this);
  }
  friend bool operator > (const TCube& l, const TCube& r) { return l._frame > r._frame; }

  Cube* _cube;
  int   _frame; // -1 = frame_null, INT_MAX = INF
};

#endif
