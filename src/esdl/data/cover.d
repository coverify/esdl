// Written in the D programming language.

// Copyright: Coverify Systems Technology 2016
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.data.cover;		// Coverage

// mixin template Coverage {
// }

struct CoverPoint(alias t, string BINS="") {
  import std.traits: isIntegral;
  import esdl.data.bvec: isBitVector;
  alias T = typeof(t);
  static assert(isIntegral!T || isBitVector!T || is(T: bool),
		"Only integral, bitvec, or bool values can be covered."
		~ " Unable to cover a value of type: " ~ T.stringof);
  T* _point; // = &t;
  // the number of bins and which one is hit is made out by the
  // sample function
  int[] _bins;	     // We keep a count of how many times a bin is hit
  int _pos;	     // position of t the covergoup; -1 otherwise
  void _initPoint(G)(G g) {
    auto _outer = g.outer;
    assert (_outer !is null);
    static if (__traits(hasMember, g, t.stringof)) {
      _point = &(__traits(getMember, g, t.stringof));
      assert(_point !is null);
    }
    else static if (__traits(hasMember, g.outer, t.stringof)) {
      _point = &(__traits(getMember, _outer, t.stringof));
      assert(_point !is null);
    }
    else {
      _point = &(t);
      assert(_point !is null);
    }
    static if (isIntegral!T) {
      _bins.length = 64;
    }
    else static if (is(T == bool)) {
      _bins.length = 2;
    }
    else {
      static if (T.SIZE > 6) {
	_bins.length = 64;
      }
      else {
	_bins.length = T.max - T.min;
      }
    }
  }
  
  void _initPos(int pos) {
    _pos = pos;
  }

  auto getBins() {
    return _bins;
  }
  
  static if(BINS == "") {
    void sample(int argc) {
      if (_pos >= argc) {}
      else {
	static if (isIntegral!T) {
	  size_t range = cast(size_t) T.max - cast(size_t) T.min;
	  size_t size = (range/2 + 1)/32;
	  size_t slot = (cast(size_t) *_point - cast(size_t) T.min)/size;
	  import std.conv;
	  assert(slot < _bins.length, "slot is: " ~ slot.to!string);
	  assert(slot >= 0);
	  _bins[slot]++;
	}
      }
    }
  }
}

class CoverGroup {		// Base Class
  bool _isInitialized;		// true if the CoverGroup has been initialized
}

private void initialize(G, int I=0)(G g) if (is(G: CoverGroup)) {
  static if (I == 0) {
    if (g._isInitialized) return;
    else g._isInitialized = true;
  }
  static if (I >= G.tupleof.length) {
    return;
  }
  else {
    alias E = typeof(g.tupleof[I]);
    static if (is (E: CoverPoint!(t, S), alias t, string S)) {
      g.tupleof[I]._initPoint(g);
      int index = findElementIndex!(t.stringof, G);
      g.tupleof[I]._initPos(index);
    }
    initialize!(G, I+1)(g);
  }
 }

private void samplePoints(int I, int N, G)(G g) if (is(G: CoverGroup)) {
  static if (I >= G.tupleof.length) {
    return;
  }
  else {
    alias E = typeof(g.tupleof[I]);
    static if (is (E: CoverPoint!(t, S), alias t, string S)) {
      g.tupleof[I].sample(N);
    }
    samplePoints!(I+1, N)(g);
  }
 }


public void sample(G, V...)(G g, V v) if (is(G: CoverGroup)) {
  // navigate through the class elements of G to know the CoverPoint
  // instantiations as well as any Integral/BitVector instances
  sampleArgs!(0)(g, v);
  initialize(g);
  // Now look for all the coverpoints
  samplePoints!(0, V.length)(g);
 }

private void sampleArgs(int I, G, V...)(G g, V v) {
  import std.traits: isAssignable;
  static if (V.length == 0) {
    return;
  }
  else {
    alias VAL_TUPLE = getIntElements!G;
    alias N = VAL_TUPLE[I];
    static assert (isAssignable!(typeof(G.tupleof[N]), V[0]),
		   "Method sample called with argument of type " ~
		   V[0].stringof ~ " at position " ~ I.stringof ~
		   " is not assignable to type " ~
		   typeof(G.tupleof[N]).stringof);
    static if (I == 0) {
      static assert (VAL_TUPLE.length >= V.length,
		     "Method sample called with " ~ V.length.stringof ~
		     " arguments, while it can take only " ~
		     VAL_TUPLE.length.stringof ~
		     " arguments for covergroup of type: " ~ G.stringof);
    }
    g.tupleof[N] = v[0];
    sampleArgs!(I+1)(g, v[1..$]);
  }
}

// return a tuple of integral elements
private template getIntElements(G, int N=0, I...) {
  import std.traits: isIntegral;
  import esdl.data.bvec: isBitVector;
  static if (N == G.tupleof.length) {
    enum getIntElements = I;
  }
  else {
    alias T = typeof(G.tupleof[N]);
    static if (isBitVector!T || isIntegral!T || is(T == bool)) {
      enum getIntElements = getIntElements!(G, N+1, I, N);
    }
    else {
      enum getIntElements = getIntElements!(G, N+1, I);
    }
  }
}

private template findElementIndex(string E, G, int I=0, int N=0) {
  import std.traits: isIntegral;
  import esdl.data.bvec: isBitVector;
  static if(I >= G.tupleof.length) {
    enum findElementIndex = -1;
  } else {
    alias T = typeof(G.tupleof[I]);
    static if (isBitVector!T || isIntegral!T || is(T == bool)) {
      static if (E == G.tupleof[I].stringof) {
	enum findElementIndex = N;
      }
      else {
	enum findElementIndex =  findElementIndex!(E, G, I+1, N+1);
      }
    }
    else {
      enum findElementIndex = findElementIndex!(E, G, I+1, N);
    }
  }
}

private template nthIntElement(alias g, int N, int I=0) {
  import std.traits: isIntegral;
  import esdl.data.bvec: isBitVector;
  static assert(I < g.tupleof.length);
  alias T = typeof(g.tupleof[I]);
  static if (isBitVector!T || isIntegral!T || is(T == bool)) {
    static if (N == 0) {
      enum nthIntElement = g.tupleof[I];
    }
    else {
      enum nthIntElement = nthIntElement!(g, N-1, I+1);
    }
  }
  else {
      enum nthIntElement = nthIntElement!(g, N, I+1);
  }
}

private template countIntElements(G, int COUNT=0, int I=0) {
  import std.traits: isIntegral;
  import esdl.data.bvec: isBitVector;
  static if (I != G.tupleof.length) {
    alias T = typeof(G.tupleof[I]);
    static if (isBitVector!T || isIntegral!T || is(T == bool)) {
      enum countIntElements = countIntElements!(G, COUNT+1, I+1);
    }
    else {
      enum countIntElements = countIntElements!(G, COUNT, I+1);
    }
  }
  else {
    enum countIntElements = COUNT;
  }
}
