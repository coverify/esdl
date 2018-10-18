// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.rand;
import esdl.data.bvec;

int FFFF = 20;

class Foo
{
  // mixin Randomization;
  // {
  alias _esdl__T = typeof(this);
  
  // While making _esdl__SolverNested class non-static nested class
  // also works as far as dlang compilers are concerned, do not do
  // that since in that case _esdl__outer object would have an
  // implicit pointer to the outer object which can not be changed
  static class _esdl__SolverNested: _esdl__SolverBase!_esdl__T
  {
    _esdl__T _esdl__outer;
    void _esdl__setValRef()(_esdl__T outer) {
      if (_esdl__outer !is outer) {
	_esdl__outer = outer;
	_esdl__setObjOuter(true);
      }
    }
    this(uint seed, bool isSeeded, string name, _esdl__T outer,
	 _esdl__SolverRoot parent=null) {
      _esdl__outer = outer;
      static if(_esdl__baseHasRandomization!_esdl__T) {
	super(seed, isSeeded, name, outer, parent);
      }
      else {
	super(seed, isSeeded, name, parent);
      }
      _esdl__initRands();
      _esdl__initCsts();
    }


    class _esdl__Constraint(string _esdl__CstString):
      Constraint!_esdl__CstString
    {
      this(string name) {
	super(this.outer, name, cast(uint) this.outer._esdl__cstsList.length);
      }
      // This mixin writes out the bdd functions after parsing the
      // constraint string at compile time
      mixin(constraintXlate(_esdl__CstString));
      debug(CONSTRAINTS) {
	pragma(msg, constraintXlate(_esdl__CstString));
      }
    }

    class _esdl__Constraint(string _esdl__CstString, string NAME):
      Constraint!_esdl__CstString
    {
      this() {
	super(this.outer, NAME,
	      cast(uint) this.outer._esdl__cstsList.length);
      }
      // This mixin writes out the bdd functions after parsing the
      // constraint string at compile time
      // mixin(constraintXlate(_esdl__CstString));
      override CstBlock getCstExpr() {
	mixin("return this.outer._esdl__cst_func_" ~ NAME ~ "();");
      }
	
      debug(CONSTRAINTS) {
	pragma(msg, constraintXlate(_esdl__CstString));
      }
    }

    class _esdl__Constraint(string _esdl__CstString, ARGS...): // size_t N):
      Constraint!_esdl__CstString
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
	super(this.outer, name, cast(uint) this.outer._esdl__cstsList.length);
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
      mixin(constraintXlate(_esdl__CstString));
      debug(CONSTRAINTS) {
	pragma(msg, "// randomizeWith!\n");
	pragma(msg, constraintXlate(_esdl__CstString));
      }
    }

    void _esdl__with(string _esdl__CstString, ARGS...)(ARGS values) {
      auto cstWith = new _esdl__Constraint!(_esdl__CstString, ARGS)("randWith", values);
      // cstWith.withArgs(values);
      _esdl__cstWith = cstWith;
    }

    auto ref _esdl__vec(L)(ref L l, string name="unnamed") {
      import std.traits: isIntegral, isBoolean, isArray;
      static if (isIntegral!L || isBitVector!L || isBoolean!L) {
	// import std.stdio;
	// writeln("Creating VarVec, ", name);
	return new CstVec!(L, _esdl__norand, 0)(name, l);
      }
      else static if (isArray!L) {
	// import std.stdio;
	// writeln("Creating VarVecArr, ", name);
	return new CstVec!(L, _esdl__norand, 0)(name, l);
      }
      else {
	return l;
      }
    }

    auto const ref _esdl__vec(L)(const ref L l, string name="unnamed") {
      import std.traits: isIntegral, isBoolean, isArray;
      static if (isIntegral!L || isBitVector!L || isBoolean!L) {
	// import std.stdio;
	// writeln("Creating VarVec, ", name);
	return new CstVec!(L, _esdl__norand, 0)(name, l);
      }
      else static if (isArray!L) {
	// import std.stdio;
	// writeln("Creating VarVecArr, ", name);
	return new CstVec!(L, _esdl__norand, 0)(name, l);
      }
      else {
	return l;
      }
    }


    auto _esdl__vec(L)(L l, string name="unnamed") {
      import std.traits: isIntegral, isBoolean;
      import esdl.data.bvec: isBitVector;
      static if (isIntegral!L || isBitVector!L || isBoolean!L) {
	return CstVal!L.allocate(l);
      }
      else {
	return l;
      }
    }
  
    mixin(_esdl__randsMixin!_esdl__T);

    debug(CONSTRAINTS) {
      pragma(msg, "// _esdl__randsMixin!" ~ _esdl__T.stringof ~ "\n");
      pragma(msg, _esdl__randsMixin!_esdl__T);
    }
    // mixin _esdl__SolverMixin;
  }

  enum bool _esdl__hasRandomization = true;
  alias _esdl__Type = typeof(this);

  static _esdl__Type _esdl__thisHasRandomization()() {
    return null;
  }

  alias _esdl__SolverType = _esdl__SolverResolve!_esdl__Type;

  // final auto _esdl__randEval(string NAME)() {
  //   return mixin(NAME);
  // }

  static if(// is(_esdl__T: Randomizable) ||
	    __traits(compiles, _esdl__solverInst)) {
    override void _esdl__virtualRandomize(_esdl__ConstraintBase withCst = null) {
      _esdl__randomize(this, withCst);
    }
    override _esdl__SolverType _esdl__getSolver() {
      return _esdl__staticCast!_esdl__SolverType(_esdl__solverInst);
    }
    override void _esdl__initSolver() {
      if (_esdl__solverInst is null) {
	_esdl__solverInst =
	  new _esdl__SolverType(_esdl__randSeed, _esdl__randSeeded,
				typeid(_esdl__Type).stringof[8..$-1], this);
	static if(__traits(compiles, _esdl__setupSolver())) {
	  _esdl__setupSolver();
	}
      }
      else {
	_esdl__getSolver()._esdl__setObjOuter(false);
      }
    }
  }
  else {
    @rand!false _esdl__SolverRoot _esdl__solverInst;
    @rand!false uint _esdl__randSeed;
    @rand!false bool _esdl__randSeeded;
    _esdl__SolverType _esdl__getSolver() {
      return _esdl__staticCast!_esdl__SolverType(_esdl__solverInst);
    }
    void _esdl__virtualRandomize(_esdl__ConstraintBase withCst = null) {
      _esdl__randomize(this, withCst);
    }
    void useThisBuddy() {
      import esdl.rand.obdd;
      useBuddy(_esdl__solverInst._esdl__buddy);
    }
    void seedRandom(int seed) {
      _esdl__randSeed = seed;
      _esdl__randSeeded = true;
      if(_esdl__solverInst !is null) {
	_esdl__solverInst._esdl__rGen.seed(seed);
      }
    }
    bool _esdl__isRandSeeded() {
      return _esdl__randSeeded;
    }
    alias srandom = seedRandom;	// SV names the similar method srandom
    void _esdl__initSolver() {
      if (_esdl__solverInst is null) {
	_esdl__solverInst =
	  new _esdl__SolverType(_esdl__randSeed, _esdl__randSeeded,
				typeid(_esdl__Type).stringof[8..$-1], this);
	static if(__traits(compiles, _esdl__setupSolver())) {
	  _esdl__setupSolver();
	}
      }
      else {
	_esdl__getSolver()._esdl__setObjOuter(false);
      }
    }
  }
  // static if(_esdl__baseHasRandomization!_esdl__Type) {
  // }
  @rand!(8,8) byte[][] foo;
  void display() {
    import std.stdio;
    writeln(foo);
  }
  Constraint!q{
    foo.length > 4;
    foreach(i, ff; foo) {
      ff.length > 4;
      foreach(j, f; ff) {
	f == j + 2;
	f < 20;
      }
    }
  } aconst;
}

void main() {
  Foo foo = new Foo;
  for (size_t i=0; i!=2; ++i) {
    foo.randomize();
    foo.display();
  }
  import std.stdio;
  writeln("End of program");
}
