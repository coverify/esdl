// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2015
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.rand.meta;

import std.traits: isIntegral, isBoolean, isArray, isSomeChar, PointerTarget;
import esdl.data.bvec: isBitVector;
import esdl.data.queue: isQueue, Queue;
import esdl.data.bstr;

import std.exception: enforce;
import std.range: ElementType;

import esdl.rand.misc;
import esdl.rand.expr: CstVecValue, CstVarVisitorExpr;
import esdl.rand.base: CstBlock, CstVecPrim, CstPredicate,
  CstVarNodeIntf, CstObjectIntf, CstObjArrIntf, CstVisitorPredicate;
import esdl.rand.vecx: CstVecIdx, CstVecArrIdx;
import esdl.rand.objx: CstObjIdx, CstObjArrIdx;
import esdl.rand.proxy;
import esdl.rand.func;

/// C++ type static_cast for down-casting when you are sure
private import std.typetuple: staticIndexOf, TypeTuple;
private import std.traits: BaseClassesTuple; // required for staticIndexOf


// static alias Unconst(T) = T;
// static alias Unconst(T: const U, U) = U;

T _esdl__staticCast(T, F)(const F from)
  if (is (F == class) && is (T == class)
     // make sure that F is indeed amongst the base classes of T
     && staticIndexOf!(F, BaseClassesTuple!T) != -1
     )
    in {
      // assert statement will not be compiled for production release
      assert((from is null) || cast(T)from !is null);
    }
body {
  return cast(T) cast(void*) from;
 }

struct _esdl__VALUE {}
struct _esdl__ARG {}
enum _esdl__UNDEFINED;

template _esdl__RandProxyType(T, int I, P, int PI)
{
  import std.traits;
  alias L = typeof(T.tupleof[I]);
  static if (isArray!L || isQueue!L) alias E = LeafElementType!L;
  enum rand RAND = getRandAttr!(T, I);
  static if ((! RAND.hasProxy()) ||
	     _esdl__TypeHasNorandAttr!L ||
	     (is (L: _esdl__Norand))) {
    alias _esdl__RandProxyType = _esdl__UNDEFINED;
  }
  else static if ((isArray!L ||
		   isQueue!L ) && (isBitVector!E ||
				   isIntegral!E ||
				   isBoolean!E ||
				   // isSomeChar!E || // exclude strings
				   is (E == enum))) {
    alias _esdl__RandProxyType = CstVecArrIdx!(L, RAND, 0, I, P, PI);
  }
  else static if (isBitVector!L ||
		  isIntegral!L ||
		  isBoolean!L ||
		  // isSomeChar!L || // exclude chars
		  is (L == enum)) {
    alias _esdl__RandProxyType = CstVecIdx!(L, RAND, 0, I, P, PI);
  }
  else static if ((isArray!L || isQueue!L) &&
		  (is (E == class) || is (E == struct) ||
		   (is (E == U*, U) && is (U == struct)))) {
    alias _esdl__RandProxyType = CstObjArrIdx!(L, RAND, 0, I, P, PI);
  }
  else static if (is (L == class) || is (L == struct) ||
		  (is (L == U*, U) && is (U == struct))) {
    alias _esdl__RandProxyType = CstObjIdx!(L, RAND, 0, I, P, PI);
  }
  else {
    alias _esdl__RandProxyType = _esdl__UNDEFINED;
  }
}

void _esdl__doConstrainElems(P, int I=0)(P p, _esdl__Proxy proxy) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0]: _esdl__Proxy) &&
	     is (B[0] == class)) {
    static if (! is (B[0] == _esdl__Proxy)) {
      B[0] b = p;			// super object
      _esdl__doConstrainElems(b, proxy);
    }
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q: _esdl__ConstraintBase)) {
      static if (p.tupleof[I].stringof != "p._esdl__cstWith") {
	// import std.stdio;
	// writeln("Adding constraint: ", p.tupleof[I].stringof);
	foreach (pred; p.tupleof[I].getCstBlock()._preds) {
	  // writeln("Adding predicate: ", pred.name());
	  proxy.addNewPredicate(pred);
	}
      }
    }
    static if (is (Q: CstObjectIntf)//  ||
	       // is (Q: CstObjArrIntf)
	       ) {
      static if (P.tupleof[I]._esdl__ISRAND) {
	if (p.tupleof[I].isRand())
	  p.tupleof[I]._esdl__doConstrain(proxy);
      }
    }
    _esdl__doConstrainElems!(P, I+1)(p, proxy);
  }
}

void _esdl__doRandomizeElems(P, int I=0)(P p, _esdl__RandGen randGen) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0]: _esdl__Proxy) &&
	     is (B[0] == class)) {
    static if (! is (B[0] == _esdl__Proxy)) {
      B[0] b = p;			// super object
      _esdl__doRandomizeElems(b, randGen);
    }
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q: CstVarNodeIntf)) {
      static if (P.tupleof[I]._esdl__ISRAND) {
	if (p.tupleof[I].isRand())
	  p.tupleof[I]._esdl__doRandomize(randGen);
      }
    }
    _esdl__doRandomizeElems!(P, I+1)(p, randGen);
  }
}

void _esdl__doInitRandsElems(P, int I=0)(P p) {
  // static if (I == 0 &&
  // 	     is (P B == super) &&
  // 	     is (B[0]: _esdl__Proxy) &&
  // 	     is (B[0] == class)) {
  //   B[0] b = p;			// super object
  //   _esdl__doInitRandsElems(b);
  // }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    // pragma(msg, "#" ~ Q.stringof);
    static if (is (Q: CstVarNodeIntf)) {
      static if (Q._esdl__HASPROXY // && Q._esdl__ISRAND // not just @rand
		 ) {
	// pragma(msg, "#" ~ Q.stringof);
	alias T = typeof(p._esdl__outer);
	static if (is (T == class)) { // class
	  enum NAME = __traits(identifier, T.tupleof[Q._esdl__INDEX]);
	}
	else { // struct
	  alias U = PointerTarget!T;
	  enum NAME = __traits(identifier, U.tupleof[Q._esdl__INDEX]);
	}
	T t = p._esdl__outer;
	if (t !is null) {
	  alias M = typeof(t.tupleof[Q._esdl__INDEX]);
	  static if (is (M == class) ||
		     (is (M == U*, U) && is (U == struct))) { // class or struct*
	    p.tupleof[I] = new Q(NAME, p, t.tupleof[Q._esdl__INDEX]);
	  }
	  else {
	    p.tupleof[I] = new Q(NAME, p, &(t.tupleof[Q._esdl__INDEX]));
	  }
	}
	else {
	  p.tupleof[I] = new Q(NAME, p, null);
	}
      }
    }
    _esdl__doInitRandsElems!(P, I+1)(p);
  }
}

void _esdl__doInitCstsElems(P, int I=0)(P p) {
  // static if (I == 0 &&
  // 	     is (P B == super) &&
  // 	     is (B[0]: _esdl__Proxy) &&
  // 	     is (B[0] == class)) {
  //   B[0] b = p;			// super object
  //   _esdl__doInitCstsElems(b);
  // }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    // pragma(msg, Q.stringof);
    static if (is (Q: _esdl__ConstraintBase)) {
      p.tupleof[I] = p.new Q(p, p.tupleof[I].stringof[2..$]);
    }
    _esdl__doInitCstsElems!(P, I+1)(p);
  }
}

void _esdl__doSetOuterElems(P, int I=0)(P p, bool changed) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0]: _esdl__Proxy) &&
	     is (B[0] == class)) {
    static if (! is (B[0] == _esdl__Proxy)) {
      B[0] b = p;			// super object
      _esdl__doSetOuterElems(b, changed);
    }
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q == CstVecIdx!(L, RAND, N, IDX, P, PIDX),
		   L, rand RAND, int N, int IDX, P, int PIDX)) {
      static if (Q._esdl__HASPROXY) {
	if (p.tupleof[I] !is null) {
	  p.tupleof[I]._esdl__setValRef(&(p._esdl__outer.tupleof[IDX]));
	}
      }
    }
    static if (is (Q == CstObjIdx!(L, RAND, N, IDX, P, PIDX),
		   L, rand RAND, int N, int IDX, P, int PIDX)) {
      static if (Q._esdl__HASPROXY) {
	static if (is (L == struct)) {
	  if (p.tupleof[I] !is null) {
	    p.tupleof[I]._esdl__setValRef(&(p._esdl__outer.tupleof[IDX]));
	  }
	}
	else {
	  if (p.tupleof[I] !is null) {
	    p.tupleof[I]._esdl__setValRef(p._esdl__outer.tupleof[IDX]);
	  }
	}
      }
    }
    static if (is (Q == CstVecArrIdx!(L, RAND, N, IDX, P, PIDX),
		   L, rand RAND, int N, int IDX, P, int PIDX)) {
      static if (Q._esdl__HASPROXY) {
	if (p.tupleof[I] !is null) {
	  p.tupleof[I]._esdl__setValRef(&(p._esdl__outer.tupleof[IDX]));
	}
      }
    }
    static if (is (Q == CstObjArrIdx!(L, RAND, N, IDX, P, PIDX),
		   L, rand RAND, int N, int IDX, P, int PIDX)) {
      static if (Q._esdl__HASPROXY) {
	if (p.tupleof[I] !is null) {
	  p.tupleof[I]._esdl__setValRef(&(p._esdl__outer.tupleof[IDX]));
	}
      }
    }
    _esdl__doSetOuterElems!(P, I+1)(p, changed);
  }
}

template _esdl__RandDeclVars(T, int I, PT, int PI)
{
  static if (I == T.tupleof.length) {
    enum _esdl__RandDeclVars = "";
  }
  else {
    enum rand RAND = getRandAttr!(T, I);
    static if ((! RAND.hasProxy()) ||
	       is (typeof(T.tupleof[I]): _esdl__Norand) ||
	       is (_esdl__RandProxyType!(T, I, PT, PI) == _esdl__UNDEFINED)
	       ) {
      enum string _esdl__RandDeclVars = _esdl__RandDeclVars!(T, I+1, PT, PI);
    }
    else {
      // pragma(msg, I);
      // pragma(msg, __traits(identifier, T.tupleof[I]));
      static if (is (T == U*, U) && is (U == struct)) {
	enum string _esdl__RandDeclVars =
	  "  _esdl__RandProxyType!(_esdl__T, " ~ I.stringof ~
	  ", _esdl__PROXYT, " ~ PI.stringof ~ ") " ~
	  __traits(identifier, U.tupleof[I]) ~ ";\n" ~
	  _esdl__RandDeclVars!(T, I+1, PT, PI+1);
      }
      else {
	enum string _esdl__RandDeclVars =
	  "  _esdl__RandProxyType!(_esdl__T, " ~ I.stringof ~
	  ", _esdl__PROXYT, " ~ PI.stringof ~ ") " ~
          __traits(identifier, T.tupleof[I]) ~ ";\n" ~
	  _esdl__RandDeclVars!(T, I+1, PT, PI+1);
      }
    }
  }
}

template _esdl__ConstraintsDecl(T, int I=0)
{
  static if(I == T.tupleof.length) {
    enum _esdl__ConstraintsDecl = "";
  }
  else {
    alias L = typeof(T.tupleof[I]);
    static if (isArray!L || isQueue!L) alias E = LeafElementType!L;
    static if (is (T == U*, U) && is (U == struct)) {
      enum NAME = __traits(identifier, U.tupleof[I]);
    }
    else {
      enum NAME = __traits(identifier, T.tupleof[I]);
    }
    // skip the constraints and _esdl__ variables
    static if (is (L f == Constraint!(C, F, N),
		   immutable (char)[] C, immutable (char)[] F, size_t N)) {
      enum CONSTRAINT = _esdl__constraintParams!(T, I).CONSTRAINT;
      enum FILE = _esdl__constraintParams!(T, I).FILE;
      enum LINE = _esdl__constraintParams!(T, I).LINE;
      enum _esdl__ConstraintsDecl =
	"  enum string _esdl__CONSTRAINT_" ~ NAME ~
	" = _esdl__constraintParams!(_esdl__T, " ~ I.stringof ~ ").CONSTRAINT;\n" ~
	"  enum string _esdl__FILE_" ~ NAME ~
	" = _esdl__constraintParams!(_esdl__T, " ~ I.stringof ~ ").FILE;\n" ~
	"  enum size_t _esdl__LINE_" ~ NAME ~
	" = _esdl__constraintParams!(_esdl__T, " ~ I.stringof ~ ").LINE;\n" ~
	// "  CstBlock _esdl__cst_block_" ~ NAME ~ ";\n" ~
	// cast(string) constraintXlate("this", CONSTRAINT, FILE, LINE, NAME) ~
	"  _esdl__Constraint!(_esdl__CONSTRAINT_" ~ NAME ~
	", _esdl__FILE_" ~ NAME ~ ", _esdl__LINE_" ~ NAME ~ ") " ~
	NAME ~ ";\n" ~ _esdl__ConstraintsDecl!(T, I+1);
    }
    else static if ((isArray!L || isQueue!L) &&
		    (isIntegral!E || is (E == bool) ||
		     is (E == struct) || is (E == class))) {
      enum _esdl__ConstraintsDecl =
	"  _esdl__Constraint!(\"" ~ NAME ~ "\") _esdl__visitorCst_"
	~ NAME ~ ";\n"  ~ _esdl__ConstraintsDecl!(T, I+1);
    }
    else {
      enum _esdl__ConstraintsDecl = _esdl__ConstraintsDecl!(T, I+1);
    }
  }
}

template _esdl__constraintParams(T, int I)
{
  alias L = typeof(T.tupleof[I]);
  static if(is(L f == Constraint!(C, F, N),
	       immutable (char)[] C, immutable (char)[] F, size_t N)) {
    enum string CONSTRAINT = C;
    enum string FILE = F;
    enum size_t LINE = N;
  }
  else {
    static assert(false);
  }
}

template _esdl__ConstraintsDefDecl(T)
{
  enum _esdl__ConstraintsDefDecl =
    "  _esdl__Constraint!(_esdl__ConstraintDefaults!(_esdl__T, 0), \"#DEFAULT#\", 0) _esdl__defaultConstraint;\n";
}

template _esdl__ConstraintDefaults(T, int I=0)
{
  static if(I == T.tupleof.length) {
    enum _esdl__ConstraintDefaults = "";
  }
  else {
    alias RAND = getRandAttr!(T, I);
    static if (RAND.isRand) {
      static if (is (T == U*, U) && is (U == struct)) {
	enum string _esdl__ConstraintDefaults =
	  _esdl__ConstraintDefaults!(__traits(identifier, U.tupleof[I]), 0, RAND) ~
	  _esdl__ConstraintDefaults!(T, I+1);
      }
      else {
	enum string _esdl__ConstraintDefaults =
	  _esdl__ConstraintDefaults!(__traits(identifier, T.tupleof[I]), 0, RAND) ~
	  _esdl__ConstraintDefaults!(T, I+1);
      }
    }
    else {
      enum string _esdl__ConstraintDefaults = _esdl__ConstraintDefaults!(T, I+1);
    }
      
  }
}

template _esdl__ConstraintDefaults(string NAME, int I, rand RAND) {
  enum uint LENGTH = RAND[I];
  enum uint NEXTL = RAND[I+1];
  static if (LENGTH == uint.max) {
    enum string _esdl__ConstraintDefaults = "";
  }
  else {
    static if (I == 0) {
      enum string ARR = NAME;
    }
    else {
      enum J = I - 1;
      enum string ARR = "_esdl__elem_" ~ NAME ~ "_" ~ J.stringof;
    }
    enum string ELEM = "_esdl__elem_" ~ NAME ~ "_" ~ I.stringof;
    enum string _esdl__ConstraintDefaultsLength = ARR ~ ".length <= "
      ~ LENGTH.stringof ~ ";\n";
    
    static if (NEXTL == uint.max) {
      enum string _esdl__ConstraintDefaults = _esdl__ConstraintDefaultsLength;
    }
    else {
      enum string _esdl__ConstraintDefaults = _esdl__ConstraintDefaultsLength
	~ "foreach(" ~ ELEM ~ "; " ~ ARR ~ ") {\n" ~
	_esdl__ConstraintDefaults!(NAME, I+1, RAND) ~ "}";
    }
  }
}

void _esdl__randomize(T) (T t, _esdl__ConstraintBase withCst = null) {

  t._esdl__initProxy();
  
  if (withCst is null && t._esdl__proxyInst._esdl__cstWith !is null) {
    t._esdl__proxyInst._esdl__cstWith = withCst;
    t._esdl__proxyInst._esdl__cstWithChanged = true;
  }
  else {
    t._esdl__proxyInst._esdl__cstWithChanged = false;
  }

  static if(__traits(compiles, t.preRandomize())) {
    t.preRandomize();
  }

  t._esdl__proxyInst.reset();

  if (withCst !is null) {
    foreach (pred; withCst.getCstBlock()._preds) {
      t._esdl__proxyInst.addNewPredicate(pred);
    }
  }
  
  t._esdl__proxyInst._esdl__doConstrain(t._esdl__proxyInst);
  t._esdl__proxyInst.solve();
  t._esdl__proxyInst._esdl__doRandomize(t._esdl__proxyInst._esdl__getRandGen);

  static if(__traits(compiles, t.postRandomize())) {
    t.postRandomize();
  }

}


class Randomizable {
  mixin Randomization;
}

mixin template Randomization()
{
  enum bool _esdl__HasRandomizationMixin = true;
  // While making _esdl__ProxyRand class non-static nested class
  // also works as far as dlang compilers are concerned, do not do
  // that since in that case _esdl__outer object would have an
  // implicit pointer to the outer object which can not be changed

  static if (is (typeof(this) == class)) {
    static class _esdl__ProxyRand(_esdl__T): _esdl__ProxyBase!_esdl__T
    {
      mixin _esdl__ProxyMixin!_esdl__T;

      _esdl__T _esdl__outer;
      _esdl__T _esdl__getRef()() {return _esdl__outer;}
      
      void _esdl__setValRef()(_esdl__T outer) {
	if (_esdl__outer !is outer) {
	  _esdl__outer = outer;
	  this._esdl__doSetOuter(true);
	}
      }
      this(_esdl__Proxy parent, _esdl__T outer) {
	_esdl__outer = outer;
	super(parent, outer);
	_esdl__doInitRandsElems(this);
	_esdl__doInitCstsElems(this);
      }
    }
  }
  else static if (is (typeof(this) == struct)) {
    static class _esdl__ProxyRand(_esdl__T): _esdl__ProxyBase!_esdl__T
    {
      mixin _esdl__ProxyMixin!_esdl__T;
      _esdl__T* _esdl__outer;
      _esdl__T* _esdl__getRef() {return _esdl__outer;}
      void _esdl__setValRef()(ref _esdl__T outer) {
	if (_esdl__outer !is &outer) {
	  _esdl__outer = &outer;
	  this._esdl__doSetOuter(true);
	}
      }
      void _esdl__setValRef()(_esdl__T* outer) {
	if (_esdl__outer !is outer) {
	  _esdl__outer = outer;
	  this._esdl__doSetOuter(true);
	}
      }
      this(_esdl__Proxy parent, _esdl__T* outer) {
	_esdl__outer = outer;
	super(parent);
	_esdl__doInitRandsElems(this);
	_esdl__doInitCstsElems(this);
      }
    }
  }
  else {
    static assert (false, "mixin Randomization is allowed only inside a class or a struct; not " ~
		   typeof(this).stringof);
  }


  alias _esdl__ProxyType = _esdl__ProxyResolve!(typeof(this));

  // final auto _esdl__randEval(string NAME)() {
  //   return mixin(NAME);
  // }

  static if(// is(_esdl__T: Randomizable) ||
	    __traits(compiles, _esdl__proxyInst)) {
    static assert (is (typeof(this) == class),
		   typeof(this).stringof ~ " is not a class"); // only classes can have a base class
    override void _esdl__virtualRandomize(_esdl__ConstraintBase withCst = null) {
      _esdl__randomize(this, withCst);
    }
    _esdl__ProxyType _esdl__getProxy()() {
      return _esdl__staticCast!_esdl__ProxyType(_esdl__proxyInst);
    }
    override void _esdl__initProxy() {
      assert(this !is null);
      if (_esdl__proxyInst is null) {
	_esdl__proxyInst =
	  new _esdl__ProxyType(null, this);
	static if(__traits(compiles, _esdl__seedRandom())) {
	  _esdl__seedRandom();
	}
      }
      else {
	_esdl__getProxy()._esdl__doSetOuter(false);
      }
    }
  }
  else {
    @rand(false) _esdl__Proxy _esdl__proxyInst;
    _esdl__ProxyType _esdl__getProxy()() {
      return _esdl__staticCast!_esdl__ProxyType(_esdl__proxyInst);
    }
    void _esdl__virtualRandomize(_esdl__ConstraintBase withCst = null) {
      _esdl__randomize(this, withCst);
    }
    void seedRandom(int seed) {
      if (_esdl__proxyInst is null) {
	_esdl__initProxy();
      }
      _esdl__proxyInst.seedRandom(seed);
    }
    bool _esdl__isRandSeeded() {
      if (_esdl__proxyInst is null) {
	return false;
      }
      else {
	return _esdl__proxyInst.isRandomSeeded;
      }
    }
    uint _esdl__getRandomSeed() {
      if (_esdl__proxyInst is null) {
	return 0;
      }
      else {
	return _esdl__proxyInst.getRandomSeed();
      }
    }
    alias srandom = seedRandom;	// SV names the similar method srandom
    void _esdl__initProxy() {
      if (_esdl__proxyInst is null) {
	static if (is (typeof(this) == class)) {
	  _esdl__proxyInst =
	    new _esdl__ProxyType(null, this);
	}
	else {
	  _esdl__proxyInst =
	    new _esdl__ProxyType(null, &this);
	}
	static if(__traits(compiles, _esdl__seedRandom())) {
	  _esdl__seedRandom();
	}
      }
      else {
	_esdl__getProxy()._esdl__doSetOuter(false);
      }
    }
  }
}

class _esdl__ProxyNoRand(_esdl__T)
  if (is (_esdl__T == class) ||
      (is (_esdl__T == U*, U) && is (U == struct))):
    _esdl__ProxyBase!_esdl__T
      {
	mixin _esdl__ProxyMixin!_esdl__T;

	_esdl__T _esdl__outer;
	_esdl__T _esdl__getRef()() {return _esdl__outer;}
	void _esdl__setValRef()(_esdl__T outer) {
	  if (_esdl__outer !is outer) {
	    _esdl__outer = outer;
	    this._esdl__doSetOuter(true);
	  }
	}
	this(_esdl__Proxy parent, _esdl__T outer) {
	  _esdl__outer = outer;
	  super(parent, outer);
	  _esdl__doInitRandsElems(this);
	  _esdl__doInitCstsElems(this);
	}

      }

class _esdl__ProxyNoRand(_esdl__T)
  if (is (_esdl__T == struct)):
    _esdl__ProxyBase!_esdl__T
      {
	mixin _esdl__ProxyMixin!_esdl__T;

	_esdl__T* _esdl__outer;
	_esdl__T* _esdl__getRef() {return _esdl__outer;}
	void _esdl__setValRef()(ref _esdl__T outer) {
	  if (_esdl__outer !is &outer) {
	    _esdl__outer = &outer;
	    this._esdl__doSetOuter(true);
	  }
	}
	void _esdl__setValRef()(_esdl__T* outer) {
	  if (_esdl__outer !is outer) {
	    _esdl__outer = outer;
	    this._esdl__doSetOuter(true);
	  }
	}
	this(_esdl__Proxy parent, _esdl__T* outer) {
	  _esdl__outer = outer;
	  super(parent);
	  _esdl__doInitRandsElems(this);
	  _esdl__doInitCstsElems(this);
	}
      }

mixin template _esdl__ProxyMixin(_esdl__T)
{
  import std.traits: isIntegral, isBoolean;
  import esdl.data.bvec: isBitVector;

  alias _esdl__PROXYT = typeof(this);

  debug(CSTPARSER) {
    pragma(msg, "// Proxy Declarations START \n");
    pragma(msg, _esdl__RandDeclVars!(_esdl__T, 0, _esdl__PROXYT, 0));
    pragma(msg, _esdl__ConstraintsDefDecl!_esdl__T);
    pragma(msg, _esdl__ConstraintsDecl!_esdl__T);
    pragma(msg, "// Proxy Declarations END \n");
  }

  mixin (_esdl__RandDeclVars!(_esdl__T, 0, _esdl__PROXYT, 0));
  mixin (_esdl__ConstraintsDefDecl!_esdl__T);
  mixin (_esdl__ConstraintsDecl!_esdl__T);

  class _esdl__Constraint(string OBJ): _esdl__ConstraintBase
  {
    this(_esdl__Proxy eng, string name) {
      super(eng, name, OBJ);
    }
    override CstBlock makeCstBlock() {
      CstBlock _esdl__block = new CstBlock();
      _esdl__block ~= new CstVisitorPredicate(this, 0, this.outer, 0,
					      new CstVarVisitorExpr(mixin(OBJ)));
      return _esdl__block;
    }
  }

  class _esdl__Constraint(string _esdl__CstString, string FILE, size_t LINE):
    Constraint!(_esdl__CstString, FILE, LINE)
  {
    this(_esdl__Proxy eng, string name) {
      super(eng, name);
    }
    debug(CSTPARSER) {
      pragma(msg, "// constraintXlate! STARTS\n");
      pragma(msg, constraintXlate("this.outer", _esdl__CstString, FILE, LINE));
      pragma(msg, "// constraintXlate! ENDS\n");
    }
    mixin(constraintXlate("this.outer", _esdl__CstString, FILE, LINE));
  }

  class _esdl__ConstraintWith(string _esdl__CstString, string FILE, size_t LINE, ARGS...): // size_t N):
    Constraint!(_esdl__CstString, FILE, LINE)
  {
    import std.typecons;

    Tuple!(ARGS) _withArgs;

    void withArgs(ARGS...)(ARGS values) if(allIntengral!ARGS) {
      // static assert(ARGS.length == N);
      foreach(i, ref v; values) {
    	_withArgs[i] = v;
      }
    }

    this(ARGS...)(_esdl__Proxy eng, string name, ARGS args) {
      super(eng, name);
      // writeln("pointer: ", &(args[0]));
      foreach (i, arg; args) {
	_withArgs[i] = arg;
      }
    }

    ref auto _esdl__arg(size_t VAR)() {
      static assert(VAR < _withArgs.length, "Can not map specified constraint with argument: @" ~
      		    VAR.stringof);
      return _withArgs[VAR];
    }

    mixin(constraintXlate("this.outer", _esdl__CstString, FILE, LINE));
    debug(CSTPARSER) {
      pragma(msg, "// randomizeWith! STARTS\n");
      pragma(msg, constraintXlate("this.outer", _esdl__CstString, FILE, LINE));
      pragma(msg, "// randomizeWith! ENDS\n");
    }
  }

  void _esdl__with(string _esdl__CstString, string FILE, size_t LINE, ARGS...)(ARGS values) {
    auto cstWith = new _esdl__ConstraintWith!(_esdl__CstString, FILE, LINE, ARGS)(this, "randWith", values);
    // cstWith.withArgs(values);
    _esdl__cstWith = cstWith;
  }


  override void _esdl__doConstrain(_esdl__Proxy proxy) {
    _esdl__doConstrainElems(this, proxy);
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    _esdl__doRandomizeElems(this, randGen);
  }

  void _esdl__doSetOuter()(bool changed) {
    _esdl__doSetOuterElems(this, changed);
  }

  debug(CSTSOLVER) {
    enum bool _esdl__DEBUGSOVER = true;
  }
  else {
    enum bool _esdl__DEBUGSOVER = false;
  }

  override bool _esdl__debugSolver() {
    return _esdl__DEBUGSOVER;
  }
}

auto ref _esdl__sym(L)(ref L l, string name,
		       _esdl__Proxy parent) {
  import std.traits: isIntegral, isBoolean, isArray, isSomeChar;
  import esdl.data.queue: Queue, isQueue;
  static if (isIntegral!L || isBitVector!L ||
	     isBoolean!L || isSomeChar!L || is (L == enum)) {
    // import std.stdio;
    // writeln("Creating VarVec, ", name);
    return new CstVecIdx!(L, rand(true, true), 0, -1, _esdl__VALUE)(name, parent, l);
  }
  else static if (isArray!L || isQueue!L) {
    // import std.stdio;
    // writeln("Creating VarVecArr, ", name);
    return new CstVecArrIdx!(L, rand(true, true), 0, -1, _esdl__VALUE)(name, parent, l);
  }
  else {
    if (l is null) {
      l = new L(name, parent, parent._esdl__outer.tupleof[L._esdl__INDEX]);
    }
    return l;
  }
}

auto _esdl__sym(L)(L l, string name,
		   _esdl__Proxy parent)
  if (isIntegral!L || isBitVector!L ||
      isBoolean!L || isSomeChar!L || is (L == enum)) {
    return new CstVecValue!L(l); // CstVecValue!L.allocate(l);
  }

struct _esdl__rand_type_proxy(T, P)
{
  string _name;
  P _parent;

  this(string name, P parent) {
    _name = name;
    _parent = parent;
  }
  
  auto _esdl__dot(string S)() {
    return esdl.rand.meta._esdl__sym(__traits(getMember, T, S), S, _parent);
  }
}

// V is a type
auto _esdl__sym(V, S)(string name, S parent) {
  return _esdl__rand_type_proxy!(V, S)(name, parent);
}

// or else
auto _esdl__sym(alias V, S)(string name, S parent) {
  alias L = typeof(V);
  import std.traits: isIntegral, isBoolean, isArray, isSomeChar;
  import esdl.data.queue: Queue, isQueue;
  static if (isIntegral!L || isBitVector!L ||
	     isBoolean!L || isSomeChar!L || is (L == enum)) {
    static if (isLvalue!V) {
      // import std.stdio;
      // writeln("Creating VarVec, ", name);
      return new CstVecIdx!(L, rand(true, true), 0, -1, _esdl__VALUE)(name, parent, V);
    }
    else {
      return new CstVecValue!L(V); // CstVecValue!L.allocate(l);
    }
  }
  else static if (isArray!L || isQueue!L) {
    // import std.stdio;
    // writeln("Creating VarVecArr, ", name);
    return new CstVecArrIdx!(L, rand(true, true), 0, -1, _esdl__VALUE)(name, parent, V);
  }
  else {
    // import std.stdio;
    // assert (parent !is null);
    // writeln(V.stringof);
    // writeln(VS);
    // writeln(__traits(getMember, parent, VS).stringof);
    // if (__traits(getMember, parent, VS) is null) {
    //   __traits(getMember, parent, VS) = new L(name, parent, parent._esdl__outer.tupleof[L._esdl__INDEX]);
    // }
    if (V is null) {
      L._esdl__PROXYT p = parent;
      if (p is null) {
	V = new L(name, parent, null);
      }
      else {
	alias M = typeof(p._esdl__outer.tupleof[L._esdl__INDEX]);
	static if (is (M == class) ||
		   (is (M == U*, U) && is (U == struct))) {
	  V = new L(name, parent, p._esdl__outer.tupleof[L._esdl__INDEX]);
	}
	else {
	  V = new L(name, parent, &(p._esdl__outer.tupleof[L._esdl__INDEX]));
	}
      }
    }
    return V;
    // return __traits(getMember, parent, VS);
  }
}

auto _esdl__dot(string S, RV)(RV rv)
{
  return __traits(getMember, rv, S);
}


auto _esdl__arg_proxy(L, S)(string name, ref L arg, S parent) {
  import std.traits: isIntegral, isBoolean, isArray, isSomeChar;
  import esdl.data.queue: Queue, isQueue;
  // pragma(msg, L.stringof);
  static if (isIntegral!L || isBitVector!L ||
	     isBoolean!L || isSomeChar!L || is (L == enum)) {
    // import std.stdio;
    // writeln("Creating VarVec, ", name);
    return new CstVecIdx!(L, rand(true, true), 0, -1, _esdl__ARG, -1)(name, parent, &arg);
  }
  else {
    static assert(false);
  }
}

template _esdl__ProxyResolve(T) {
  // pragma(msg, "_esdl__ProxyResolve called for: " ~ T.stringof);
  // static if(__traits(compiles, T._esdl__hasRandomization)) {
  static if (is (T == class) || is (T == struct)) {
    // pragma(msg, T.stringof);
    static if (__traits(compiles, T._esdl__HasRandomizationMixin)) {
      // pragma(msg, "ProxyRand: ", T.stringof);
      alias _esdl__ProxyResolve = T._esdl__ProxyRand!T;
    }
    else {
      // pragma(msg, "ProxyNoRand: ", T.stringof);
      alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
    }
  }
  // else static if (is (T == struct)) {
  //   alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
  // }
  else static if (is (T == U*, U) && is (U == struct)) {
    alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
  }
  else {
    static assert(false, "Unable to resolve proxy for type: " ~ T.stringof);
  }
}

// For a given class, this template returns the Proxy for first
// class in the ancestory that has Randomization mixin -- if there is
// none, returns _esdl__Proxy
template _esdl__ProxyBase(T) {
  static if (is (T == class) &&
	     is (T B == super) &&
	     is (B[0] == class) &&
	     (! _esdl__TypeHasNorandAttr!(B[0])) &&
	     (! is (B[0] == Object))) {
    alias U = B[0];
    alias _esdl__ProxyBase = _esdl__ProxyResolve!U;
  }
  else {
    alias _esdl__ProxyBase = _esdl__Proxy;
  }
}

void randomizeWith(string C, string FILE=__FILE__, size_t LINE=__LINE__, T, ARGS...)(ref T t, ARGS values)
  if (is (T == class) && allIntengral!ARGS) {
    t._esdl__initProxy();
    // The idea is that if the end-user has used the randomization
    // mixin then _esdl__RandType would be already available as an
    // alias and we can use virtual randomize method in such an
    // eventuality.
    // static if(is(typeof(t._esdl__RandType) == T)) {
    if (t._esdl__proxyInst._esdl__cstWith is null ||
	t._esdl__proxyInst._esdl__cstWith._constraint != C) {
      t._esdl__getProxy()._esdl__with!(C, FILE, LINE)(values);
      t._esdl__proxyInst._esdl__cstWithChanged = true;
      // auto withCst =
      //	new Constraint!(C, "_esdl__withCst",
      //			T, ARGS.length)(t, "_esdl__withCst");
      // withCst.withArgs(values);
      // t._esdl__proxyInst._esdl__cstWith = withCst;
    }
    else {
      alias CONSTRAINT = _esdl__ProxyResolve!T._esdl__ConstraintWith!(C, FILE, LINE, ARGS);
      auto cstWith = _esdl__staticCast!CONSTRAINT(t._esdl__proxyInst._esdl__cstWith);
      cstWith.withArgs(values);
      t._esdl__proxyInst._esdl__cstWithChanged = false;
    }
    t._esdl__virtualRandomize(t._esdl__proxyInst._esdl__cstWith);
  }

void randomize(T)(T t) {
  // FIXME
  // first check if the there are @rand or Constraint definitions but
  // missing mixin Randomization for some of the hierarchies
  t._esdl__virtualRandomize();
}

// FIXME add bitvectors to this template filter
template allIntengral(ARGS...) {
  static if(ARGS.length == 0) {
    enum bool allIntengral = true;
  }
  else static if (isIntegral!(ARGS[0]) || isBitVector!(ARGS[0]) ||
		  isBoolean!(ARGS[0]) || isSomeChar!(ARGS[0]) || is (ARGS[0] == enum)) {
    enum bool allIntengral = allIntengral!(ARGS[1..$]);
  }
  else enum bool allIntengral = false;
}
