// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2015
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.rand.meta;

import esdl.solver.obdd;
import esdl.solver.bdd;

import std.traits: isIntegral, isBoolean, isArray, isStaticArray,
  isDynamicArray, isSomeChar, PointerTarget;
import esdl.data.bvec: isBitVector;
import esdl.data.bstr;

import std.exception: enforce;
import std.range: ElementType;

import esdl.rand.misc;
import esdl.rand.expr: CstVecValue;
import esdl.rand.base: CstBlock, _esdl__Proxy, CstVecPrim, CstPredicate,
  CstVarIntf, CstObjIntf, CstObjArrIntf;
import esdl.rand.vecx: CstVecIdx, CstVecArrIdx;
import esdl.rand.objx: CstObjIdx, CstObjArrIdx;
import esdl.rand.proxy;

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

template _esdl__RandProxyType(T, P, int I)
{
  import std.traits;
  alias L = typeof(T.tupleof[I]);
  static if (isArray!L) alias E = LeafElementType!L;
  enum rand RAND = getRandAttr!(T, I);
  static if (isArray!L && (isBitVector!E ||
			   isIntegral!E ||
			   isBoolean!E ||
			   isSomeChar!E ||
			   is (E == enum))) {
    alias _esdl__RandProxyType = CstVecArrIdx!(L, RAND, 0, P, I);
  }
  else static if (isBitVector!L || isIntegral!L ||
		  isBoolean!L || isSomeChar!L || is (L == enum)) {
    alias _esdl__RandProxyType = CstVecIdx!(L, RAND, 0, P, I);
  }
  else static if(isArray!L && (is (E == class) || is (E == struct) ||
			       (is (E == U*, U) && is (U == struct)))) {
    alias _esdl__RandProxyType = CstObjArrIdx!(L, RAND, 0, P, I);
  }
  else static if (is (L == class) || is (L == struct) ||
		  (is (L == U*, U) && is (U == struct))) {
    alias _esdl__RandProxyType = CstObjIdx!(L, RAND, 0, P, I);
  }
}

void _esdl__doConstrainElems(P, int I=0)(P p, _esdl__ProxyRoot proxy) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0] : _esdl__ProxyRoot) &&
	     is (B[0] == class)) {
    B[0] b = p;			// super object
    _esdl__doConstrainElems(b, proxy);
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q == Constraint!(C, F, N),
		   immutable (char)[] C, immutable (char)[] F, size_t N)) {
      foreach (pred; p.tupleof[I].getCstBlock()._preds) {
	proxy.addPredicate(pred);
      }
    }
    static if (is (Q: CstObjIntf) ||
	       is (Q: CstObjArrIntf)) {
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
	     is (B[0] : _esdl__ProxyRoot) &&
	     is (B[0] == class)) {
    B[0] b = p;			// super object
    _esdl__doRandomizeElems(b, randGen);
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q: CstVarIntf)) {
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
  // 	     is (B[0] : _esdl__ProxyRoot) &&
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
    static if (is (Q: CstVarIntf)) {
      static if (Q._esdl__HASPROXY && Q._esdl__ISRAND) {
	alias T = typeof(p._esdl__outer);
	static if (is (T == class)) { // class
	  enum NAME = __traits(identifier, T.tupleof[Q._esdl__INDEX]);
	}
	else { // struct
	  alias U = PointerTarget!T;
	  enum NAME = __traits(identifier, U.tupleof[Q._esdl__INDEX]);
	}
	T t = p._esdl__outer;
	p.tupleof[I] = new Q(NAME, t.tupleof[Q._esdl__INDEX], p);
      }
    }
    _esdl__doInitRandsElems!(P, I+1)(p);
  }
}

void _esdl__doInitCstsElems(P, int I=0)(P p) {
  // static if (I == 0 &&
  // 	     is (P B == super) &&
  // 	     is (B[0] : _esdl__ProxyRoot) &&
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
    static if (is (Q == Constraint!(C, F, N),
		   immutable (char)[] C, immutable (char)[] F, size_t N)) {
      p.tupleof[I] = p.new p._esdl__Constraint!(C, F, N)
	(p, p.tupleof[I].stringof[2..$]);
    }
    _esdl__doInitCstsElems!(P, I+1)(p);
  }
}

void _esdl__doSetOuterElems(P, int I=0)(P p, bool changed) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0] : _esdl__ProxyRoot) &&
	     is (B[0] == class)) {
    B[0] b = p;			// super object
    _esdl__doSetOuterElems(b, changed);
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q == CstVecIdx!(L, RAND, N, P, IDX),
		   L, rand RAND, int N, P, int IDX)) {
      static if (Q._esdl__HASPROXY) {
	if (p.tupleof[I] !is null) {
	  p.tupleof[I]._esdl__setValRef(p._esdl__outer.tupleof[IDX]);
	}
      }
    }
    static if (is (Q == CstObjIdx!(L, RAND, N, P, IDX),
		   L, rand RAND, int N, P, int IDX)) {
      static if (Q._esdl__HASPROXY) {
	static if (is (L == U*, U) && is(U == struct)) {
	  if (p.tupleof[I] !is null) {
	    p.tupleof[I]._esdl__setValRef(* (p._esdl__outer.tupleof[IDX]));
	  }
	}
	else {
	  if (p.tupleof[I] !is null) {
	    p.tupleof[I]._esdl__setValRef(p._esdl__outer.tupleof[IDX]);
	  }
	}
      }
    }
    static if (is (Q == CstVecArrIdx!(L, RAND, N, P, IDX),
		   L, rand RAND, int N, P, int IDX)) {
      static if (Q._esdl__HASPROXY) {
	if (p.tupleof[I] !is null) {
	  p.tupleof[I]._esdl__setValRef(p._esdl__outer.tupleof[IDX]);
	}
      }
    }
    static if (is (Q == CstObjArrIdx!(L, RAND, N, IDX),
		   L, rand RAND, int N, int IDX)) {
      static if (Q._esdl__HASPROXY) {
	if (p.tupleof[I] !is null) {
	  p.tupleof[I]._esdl__setValRef(p._esdl__outer.tupleof[IDX]);
	}
      }
    }
    _esdl__doSetOuterElems!(P, I+1)(p, changed);
  }
}

template _esdl__RandDeclVars(T, int I=0)
{
  static if(I == T.tupleof.length) {
    enum _esdl__RandDeclVars = "";
  }
  else {
    enum rand RAND = getRandAttr!(T, I);
    static if ((! RAND.hasProxy()) ||
	       is (typeof(T.tupleof[I]): _esdl__Norand)) {
      enum string _esdl__RandDeclVars = _esdl__RandDeclVars!(T, I+1);
    }
    else {
      // pragma(msg, I);
      // pragma(msg, __traits(identifier, T.tupleof[I]));
      enum string _esdl__RandDeclVars =
	"  _esdl__RandProxyType!(_esdl__T, _esdl__PROXYT, " ~ I.stringof ~ ") " ~
	__traits(identifier, T.tupleof[I]) ~ ";\n" ~
	_esdl__RandDeclVars!(T, I+1);
    }
  }
}

template _esdl__ConstraintsDefDecl(T)
{
  enum _esdl__ConstraintsDefDecl =
    "  Constraint!(_esdl__ConstraintDefaults!(_esdl__T, 0), \"#DEFAULT#\", 0) _esdl__defaultConstraint;\n";
}

template _esdl__ConstraintDefaults(T, int I=0)
{
  static if(I == T.tupleof.length) {
    enum _esdl__ConstraintDefaults = "";
  }
  else {
    alias RAND = getRandAttr!(T, I);
    static if (RAND.isRand) {
      enum string _esdl__ConstraintDefaults =
	_esdl__ConstraintDefaults!(__traits(identifier, T.tupleof[I]), 0, RAND) ~
	_esdl__ConstraintDefaults!(T, I+1);
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

template _esdl__ConstraintsDecl(T, int I=0)
{
  static if(I == T.tupleof.length) {
    enum _esdl__ConstraintsDecl = "";
  }
  else {
    alias L = typeof(T.tupleof[I]);
    enum NAME = __traits(identifier, T.tupleof[I]);
    // skip the constraints and _esdl__ variables
    static if(is(L f == Constraint!(C, F, N),
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
	"  Constraint!(_esdl__CONSTRAINT_" ~ NAME ~
	", _esdl__FILE_" ~ NAME ~ ", _esdl__LINE_" ~ NAME ~ ") " ~
	NAME ~ ";\n" ~ _esdl__ConstraintsDecl!(T, I+1);
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

void _esdl__randomize(T) (T t, _esdl__ConstraintBase withCst = null) {

  t._esdl__initProxy();
  
  if(withCst is null && t._esdl__proxyInst._esdl__cstWith !is null) {
    t._esdl__proxyInst._esdl__cstWith = withCst;
    t._esdl__proxyInst._esdl__cstWithChanged = true;
  }
  else {
    t._esdl__proxyInst._esdl__cstWithChanged = false;
  }

  useBuddy(CstBddSolver.buddy);

  static if(__traits(compiles, t.preRandomize())) {
    t.preRandomize();
  }

  t._esdl__proxyInst.reset();
  t._esdl__proxyInst._esdl__doConstrain(t._esdl__proxyInst);
  t._esdl__proxyInst.solve();
  t._esdl__proxyInst._esdl__doRandomize(t._esdl__proxyInst._esdl__getRandGen);

  static if(__traits(compiles, t.postRandomize())) {
    t.postRandomize();
  }

}


// generates the code for rand structure inside the class object getting
// randomized
string _esdl__randsMixin(T, ST)() {
  // T t;
  // string rand_decls = _esdl__RandDeclFuncs!T ~ _esdl__RandDeclVars!T;

  string rand_decls = _esdl__RandDeclVars!(T);
  string cst_decls = _esdl__ConstraintsDefDecl!T ~ _esdl__ConstraintsDecl!T;


  string randsMixin = rand_decls ~ cst_decls;

  return randsMixin;
}

class Randomizable {
  mixin Randomization;
}

mixin template Randomization()
{
  import esdl.solver.bdd: CstBddSolver;
  alias _esdl__T = typeof(this);
  
  // While making _esdl__ProxyRand class non-static nested class
  // also works as far as dlang compilers are concerned, do not do
  // that since in that case _esdl__outer object would have an
  // implicit pointer to the outer object which can not be changed
  static class _esdl__ProxyRand: _esdl__ProxyBase!_esdl__T
  {
    _esdl__T _esdl__outer;
    void _esdl__setValRef()(_esdl__T outer) {
      if (_esdl__outer !is outer) {
	_esdl__outer = outer;
	this._esdl__doSetOuter(true);
      }
    }
    this(string name, _esdl__T outer,
	 _esdl__Proxy parent) {
      assert (outer !is null);
      _esdl__outer = outer;
      // static if(_esdl__baseHasRandomization!_esdl__T) {
      super(name, outer, parent);
      // }
      // else {
      // 	super(name, parent);
      // }
      _esdl__doInitRandsElems(this);
      _esdl__doInitCstsElems(this);
    }

    mixin _esdl__ProxyMixin;
  }

  enum bool _esdl__hasRandomization = true;
  alias _esdl__Type = typeof(this);

  static _esdl__Type _esdl__thisHasRandomization()() {
    return null;
  }

  alias _esdl__ProxyType = _esdl__ProxyResolve!_esdl__Type;

  // final auto _esdl__randEval(string NAME)() {
  //   return mixin(NAME);
  // }

  static if(// is(_esdl__T: Randomizable) ||
	    __traits(compiles, _esdl__proxyInst)) {
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
	  new _esdl__ProxyType(typeid(_esdl__Type).stringof[8..$-1],
				this, null);
	static if(__traits(compiles, _esdl__setupProxy())) {
	  _esdl__setupProxy();
	}
      }
      else {
	_esdl__getProxy()._esdl__doSetOuter(false);
      }
    }
  }
  else {
    @rand(false) _esdl__ProxyRoot _esdl__proxyInst;
    _esdl__ProxyType _esdl__getProxy()() {
      return _esdl__staticCast!_esdl__ProxyType(_esdl__proxyInst);
    }
    void _esdl__virtualRandomize(_esdl__ConstraintBase withCst = null) {
      _esdl__randomize(this, withCst);
    }
    void useThisBuddy() {
      import esdl.solver.obdd;
      useBuddy(CstBddSolver.buddy);
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
	_esdl__proxyInst =
	  new _esdl__ProxyType(typeid(_esdl__Type).stringof[8..$-1],
				this, null);
	static if(__traits(compiles, _esdl__setupProxy())) {
	  _esdl__setupProxy();
	}
      }
      else {
	_esdl__getProxy()._esdl__doSetOuter(false);
      }
    }
  }
  // static if(_esdl__baseHasRandomization!_esdl__Type) {
  // }
}

class _esdl__ProxyNoRand(_esdl__T) if (is (_esdl__T == class)):
  _esdl__ProxyBase!_esdl__T
    {
      _esdl__T _esdl__outer;
      void _esdl__setValRef()(_esdl__T outer) {
	if (_esdl__outer !is outer) {
	  _esdl__outer = outer;
	  this._esdl__doSetOuter(true);
	}
      }
      this(string name, _esdl__T outer,
	   _esdl__Proxy parent) {
	_esdl__outer = outer;
	// static if(_esdl__baseHasRandomization!_esdl__T) {
	super(name, outer, parent);
	// }
	// else {
	//   super(name, parent);
	// }
	_esdl__doInitRandsElems(this);
	_esdl__doInitCstsElems(this);
      }

      mixin _esdl__ProxyMixin;
    }

class _esdl__ProxyNoRand(_esdl__T) if (is (_esdl__T == struct)):
  _esdl__ProxyBase!_esdl__T
    {
      _esdl__T* _esdl__outer;
      void _esdl__setValRef(ref _esdl__T outer) {
	if (_esdl__outer !is &outer) {
	  _esdl__outer = &outer;
	  this._esdl__doSetOuter(true);
	}
      }
      this(string name, ref _esdl__T outer,
	   _esdl__Proxy parent) {
	_esdl__outer = &outer;
	// static if(_esdl__baseHasRandomization!_esdl__T) {
	super(name, parent);
	// }
	// else {
	//   super(name, parent);
	// }
	_esdl__doInitRandsElems(this);
	_esdl__doInitCstsElems(this);
      }

      mixin _esdl__ProxyMixin;
    }

mixin template _esdl__ProxyMixin()
{
  alias _esdl__PROXYT = typeof(this);

  import std.traits: isIntegral, isBoolean;
  import esdl.data.bvec: isBitVector;

  class _esdl__Constraint(string _esdl__CstString, string FILE, size_t LINE):
    Constraint!(_esdl__CstString, FILE, LINE)
  {
    this(_esdl__ProxyRoot eng, string name) {
      super(eng, name);
    }
    // This mixin writes out the bdd functions after parsing the
    // constraint string at compile time
    // CstBlock _esdl__cst_block;
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

    this(ARGS...)(string name, ARGS args) {
      super(this.outer, name);
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

    // This mixin writes out the bdd functions after parsing the
    // constraint string at compile time
    // CstBlock _esdl__cst_block;
    mixin(constraintXlate("this.outer", _esdl__CstString, FILE, LINE));
    debug(CSTPARSER) {
      pragma(msg, "// randomizeWith! STARTS\n");
      pragma(msg, constraintXlate("this.outer", _esdl__CstString, FILE, LINE));
      pragma(msg, "// randomizeWith! ENDS\n");
    }
  }

  void _esdl__with(string _esdl__CstString, string FILE, size_t LINE, ARGS...)(ARGS values) {
    auto cstWith = new _esdl__ConstraintWith!(_esdl__CstString, FILE, LINE, ARGS)("randWith", values);
    // cstWith.withArgs(values);
    _esdl__cstWith = cstWith;
  }

  debug(CSTPARSER) {
    pragma(msg, "// _esdl__randsMixin!" ~ _esdl__T.stringof ~ " STARTS \n");
    pragma(msg, _esdl__randsMixin!(_esdl__T, _esdl__PROXYT));
    pragma(msg, "// _esdl__randsMixin!" ~ _esdl__T.stringof ~ " ENDS \n");
  }

  mixin(_esdl__randsMixin!(_esdl__T, _esdl__PROXYT));


  override void _esdl__doConstrain(_esdl__ProxyRoot proxy) {
    _esdl__doConstrainElems(this, proxy);
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    _esdl__doRandomizeElems(this, randGen);
  }

  void _esdl__doSetOuter()(bool changed) {
    _esdl__doSetOuterElems(this, changed);
  }

}

auto ref _esdl__rand_proxy(L)(ref L l, string name,
			      _esdl__Proxy parent) {
  import std.traits: isIntegral, isBoolean, isArray, isSomeChar;
  static if (isIntegral!L || isBitVector!L ||
	     isBoolean!L || isSomeChar!L || is (L == enum)) {
    // import std.stdio;
    // writeln("Creating VarVec, ", name);
    return new CstVecIdx!(L, rand(true, true), 0, -1)(name, l, parent);
  }
  else static if (isArray!L) {
    // import std.stdio;
    // writeln("Creating VarVecArr, ", name);
    return new CstVecArrIdx!(L, rand(true, true), 0, -1)(name, l, parent);
  }
  else {
    if (l is null) {
      l = new L(name, this._esdl__outer.tupleof[L._esdl__INDEX], this);
    }
    return l;
  }
}

auto _esdl__rand_proxy(L)(L l, string name,
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
  
  auto _esdl__rand_term_chain(string S)(Object dummy) {
    return _esdl__rand_proxy!(__traits(getMember, T, S))(S, _parent);
  }
}

// V is a type
auto _esdl__rand_proxy(V, // string VS,
		       S)(string name, S parent) {
  return _esdl__rand_type_proxy!(V, S)(name, parent);
}

// or else
auto _esdl__rand_proxy(alias V, // string VS,
		       S)(string name, S parent) {
  alias L = typeof(V);
  import std.traits: isIntegral, isBoolean, isArray, isSomeChar;
  static if (isIntegral!L || isBitVector!L ||
	     isBoolean!L || isSomeChar!L || is (L == enum)) {
    static if (isLvalue!V) {
      // import std.stdio;
      // writeln("Creating VarVec, ", name);
      return new CstVecIdx!(L, rand(true, true), 0, -1)(name, V, parent);
    }
    else {
      return new CstVecValue!L(V); // CstVecValue!L.allocate(l);
    }
  }
  else static if (isArray!L) {
    // import std.stdio;
    // writeln("Creating VarVecArr, ", name);
    return new CstVecArrIdx!(L, rand(true, true), 0, -1)(name, V, parent);
  }
  else {
    // import std.stdio;
    assert (parent !is null);
    // writeln(V.stringof);
    // writeln(VS);
    // writeln(__traits(getMember, parent, VS).stringof);
    // if (__traits(getMember, parent, VS) is null) {
    //   __traits(getMember, parent, VS) = new L(name, parent._esdl__outer.tupleof[L._esdl__INDEX], parent);
    // }
    if (V is null) {
      L._esdl__PROXYT p = parent;
      V = new L(name, p._esdl__outer.tupleof[L._esdl__INDEX], parent);
    }
    return V;
    // return __traits(getMember, parent, VS);
  }
}

template _esdl__ProxyResolve(T) {
  // static if(__traits(compiles, T._esdl__hasRandomization)) {
  static if (is(T == class)) {
    static if (__traits(compiles, T._esdl__ProxyRand)) {
      alias _esdl__ProxyResolve = T._esdl__ProxyRand;
    }
    else {
      alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
    }
  }
  else {
    alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
  }
}

// For a given class, this template returns the Proxy for first
// class in the ancestory that has Randomization mixin -- if there is
// none, returns _esdl__ProxyRoot
template _esdl__ProxyBase(T) {
  static if (is (T == class) &&
	     is (T B == super) &&
	     is (B[0] == class) &&
	     (! hasNorandHierAttr!(B[0])) &&
	     (! is (B[0] == Object))) {
    alias U = B[0];
    // check if the base class has Randomization
    // static if(__traits(compiles, _esdl__ProxyResolve!U)) {
    // static if(__traits(compiles, U._esdl__thisHasRandomization()) &&
    // 	      is(U == typeof(U._esdl__thisHasRandomization()))) {
    alias _esdl__ProxyBase = _esdl__ProxyResolve!U;
    // }
    // else {
    //   alias _esdl__ProxyBase = _esdl__ProxyBase!U;
    // }
  }
  else {
    alias _esdl__ProxyBase = _esdl__ProxyRoot;
  }
}

void randomizeWith(string C, string FILE=__FILE__, size_t LINE=__LINE__, T, ARGS...)(ref T t, ARGS values)
  if(is(T == class) && allIntengral!ARGS) {
    t._esdl__initProxy();
    // The idea is that if the end-user has used the randomization
    // mixin then _esdl__RandType would be already available as an
    // alias and we can use virtual randomize method in such an
    // eventuality.
    // static if(is(typeof(t._esdl__RandType) == T)) {
    if(t._esdl__proxyInst._esdl__cstWith is null ||
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
