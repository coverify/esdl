// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.data.packer;

import esdl.data.bstr;
import esdl.data.bvec;
import esdl.base.core: SimTime;

import std.traits;

struct packer
{
  BitString!false data;		// string of bits

  alias data this;

  private size_t _unpackIndex;
  size_t unpackIndex() {
    return _unpackIndex;
  }

  private size_t _packIndex;
  size_t packIndex() {
    return _packIndex;
  }

  void pack(T)(T t, bool bigEndian=false)
    if(is(T == SimTime) || is(T == SimTime) || isFloatingPoint!T) {
      alias _bvec!(false, false, 8*T.sizeof) V;
      V v = t.toBits();
      this.pack(v, bigEndian);
    }

  void unpack(T)(T t, bool bigEndian=false)
    if(is(T == SimTime) || is(T == SimTime) || isFloatingPoint!T) {
      alias _bvec!(false, false, 8*T.sizeof) V;
      V v;
      this.unpack(v, bigEndian);
      t.fromBits(v);
    }

  void pack(T)(T t, bool bigEndian=false, size_t count = 0)
    if (is(T == bool) || isBitVector!T || isIntegral!T) {
      static if(isBitVector!T && T.IS4STATE) {
	this.pack(t.aVal, bigEndian, count);
	this.pack(t.bVal, bigEndian, count);
      }
      else {
	data.pushBack(t, bigEndian, count);
	if(count == 0) {
	  _packIndex += BitLength!T;
	}
	else {
	  assert(count <= BitLength!T);
	  _packIndex += count;
	}
      }
    }

  void unpack(T)(ref T t, bool bigEndian=false, size_t count = 0)
    if (is(T == bool) || isBitVector!T || isIntegral!T) {
      static if(isBitVector!T && T.IS4STATE) {
	_bvec!(T.ISSIGNED, false, T.SIZE) aval;
	_bvec!(T.ISSIGNED, false, T.SIZE) bval;
	this.unpack(aval, bigEndian, count);
	t.setAval(aval);
	this.unpack(bval, bigEndian, count);
	t.setBval(bval);
      }
      else {
	data.getFront(t, _unpackIndex, bigEndian, count);
	if(count == 0) {
	  _unpackIndex += BitLength!T;
	}
	else {
	  assert(count <= BitLength!T);
	  _unpackIndex += count;
	}
      }
    }

  void packReset() {
    _packIndex = 0;
    data.clear();
  }

  void unpackReset() {
    _unpackIndex = 0;
  }
}
