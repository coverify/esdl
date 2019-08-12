module esdl.rand.solver;
import esdl.rand.obdd;

import esdl.rand.base: CstVecPrim, CstStage, CstBddExpr,
  CstDomain, CstPredicate, CstBlock, _esdl__Solver;
import esdl.rand.misc;
import esdl.data.folder;
import std.container: Array;
import std.array;

abstract class _esdl__ConstraintBase: _esdl__Norand
{
  this(_esdl__SolverRoot eng, string name, string constraint, uint index) {
    _cstEng = eng;
    _name = name;
    _constraint = constraint;
    _index = index;
  }
  immutable @rand!false string _constraint;
  protected @rand!false bool _enabled = true;
  protected @rand!false _esdl__SolverRoot _cstEng;
  protected @rand!false string _name;
  // index in the constraint Database
  protected @rand!false uint _index;

  bool isEnabled() {
    return _enabled;
  }

  void enable() {
    _enabled = true;
  }

  void disable() {
    _enabled = false;
  }

  BDD getConstraintBDD() {
    BDD retval = _cstEng._esdl__buddy.one();
    return retval;
  }

  string name() {
    return _name;
  }

  abstract CstBlock getCstExpr();
}

static char[] constraintXlate(string SOLVER, string CST,
			      string FILE, size_t LINE, string NAME="") {
  import esdl.rand.cstx;
  CstParser parser = CstParser(CST, FILE, LINE);
  return parser.translate(SOLVER, NAME);
}

abstract class Constraint(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__)
  : _esdl__ConstraintBase
{
  this(_esdl__SolverRoot eng, string name, uint index) {
    super(eng, name, CONSTRAINT, index);
  }
};


template _esdl__baseHasRandomization(T) {
  static if(is(T B == super)
	    && is(B[0] == class)) {
    alias U = B[0];
    static if(__traits(compiles, U._esdl__hasRandomization)) {
      enum bool _esdl__baseHasRandomization = true;
    }
    else {
      enum bool _esdl__baseHasRandomization = _esdl__baseHasRandomization!U;
    }
  }
  else {
    enum bool _esdl__baseHasRandomization = false;
  }
}


abstract class _esdl__SolverRoot: _esdl__Solver
{
  // Keep a list of constraints in the class
  _esdl__ConstraintBase[] _esdl__cstsList;
  _esdl__ConstraintBase _esdl__cstWith;
  bool _esdl__cstWithChanged;

  CstBlock _esdl__cstExprs;

  CstStage[] savedStages;

  Array!ulong _solveValue;
  
  this(string name, _esdl__SolverRoot parent, bool isSeeded, uint seed) {
    super(name, parent, isSeeded, seed);
    if (parent is null) {
      _esdl__cstExprs = new CstBlock();
    }
  }

  // overridden by Randomization mixin -- see meta.d
  void _esdl__initRands() {}
  void _esdl__initCsts() {}
  void _esdl__doRandomize(_esdl__RandGen randGen) {}

  // void obsoleteSolve() { // (T)(T t) {
  //   // writeln("Solving BDD for number of constraints = ", _esdl__cstsList.length);
  //   uint lap = 0;
  //   // if (_domains.length is 0 // || _esdl__cstWithChanged is true
  //   // 	) {
  //   if (_esdl__cstExprs.isEmpty || _esdl__cstWithChanged is true) {
  //     initPreds();
  //   }

  //   CstStage[] unsolvedStages;

  //   int stageIndx=0;
  //   CstPredicate[] unrolledPreds = _esdl__cstExprs._exprs;	// unstaged Expressions -- all
  //   CstPredicate[] toResolvePreds;   			// need resolution wrt LAP logic
  //   CstPredicate[] unresolvedPreds;			// need resolution wrt LAP logic
    
  //   // import std.stdio;
  //   // writeln("There are ", unrolledPreds.length, " number of unsolved expressions");
  //   // writeln("There are ", _cstRndDomains.length, " number of domains");

  //   while(unrolledPreds.length > 0 || unsolvedStages.length > 0) {
  //     lap += 1;

  //     CstStage[] cstStages = unsolvedStages;
  //     unsolvedStages.length = 0;

  //     CstPredicate[] cstExprs = unrolledPreds;
  //     unrolledPreds.length = 0;
  //     toResolvePreds = unresolvedPreds;
  //     unresolvedPreds.length = 0;

  //     CstBddExpr[] uwExprs;	// unwound expressions

  //     // unroll all the unrollable expressions
  //     foreach(expr; cstExprs) {
  // 	// import std.stdio;
  // 	// writeln("Unrolling: ", expr.name());
  // 	// auto unwound = expr.unroll();
  // 	// for (size_t i=0; i!=unwound.length; ++i) {
  // 	//   writeln("Unwound as: ", unwound[i].name());
  // 	// }
  // 	expr.unroll(lap, unrolledPreds, unrolledPreds, toResolvePreds// uwExprs
  // 		    );
  //     }

  //     // foreach(expr; uwExprs) {
  //     // 	// if(expr.itrVars().length is 0) {
  //     // 	if(expr.hasUnresolvedIndx()) {
  //     // 	  import std.stdio;
  //     // 	  writeln("Adding expression ", expr.name(), " to unresolved");
  //     // 	  expr.resolveLap(lap);
  //     // 	  unrolledPreds ~= expr;
  //     // 	}
  //     // 	// else {
  //     // 	//   toResolvePreds ~= expr;
  //     // 	// }
  //     // }

  //     foreach (pred; toResolvePreds) {
  // 	// import std.stdio;
  // 	uint elap = pred.getExpr().resolveLap();
  // 	// writefln("Unroll Lap of the pred %s is %s", pred.name() , lap);
  // 	if (elap == lap) {
  // 	  unresolvedPreds ~= pred;
  // 	}
  // 	else {
  // 	  // import std.stdio;
  // 	  // writeln("Adding pred ", pred.name(), " to stage");
  // 	  addCstStage(pred, cstStages);
  // 	}
  //     }

  //     foreach(stage; cstStages) {
  // 	if(stage !is null) {
  // 	  solveStage(stage, stageIndx);
  // 	}
  // 	else {
  // 	  // assert(stage._domVars.length !is 0);
  // 	  unsolvedStages ~= stage;
  // 	}
  //     }
  //   }
  // }

  Folder!CstPredicate _allPreds;

  Folder!CstStage _solveStages;

  void initPreds() {
    assert(_root is this);
    _esdl__cstExprs._esdl__reset(); // start empty

    // take all the constraints -- even if disabled
    foreach(ref _esdl__ConstraintBase cst; _esdl__cstsList) {
      _esdl__cstExprs ~= cst.getCstExpr();
    }

    if(_esdl__cstWith !is null) {
      _esdl__cstExprs ~= _esdl__cstWith.getCstExpr();
    }

    foreach (pred; _esdl__cstExprs._preds) {
      _allPreds ~= pred;
    }
  }
  
  void solve() {
    assert(_root is this);
    this._cycle += 1;
    
    int stageIndx=0;

    if (_esdl__cstExprs.isEmpty || _esdl__cstWithChanged is true) {
      initPreds();
    }

    // reset all bins
    _rolledPreds.reset();
    _unrolledPreds.reset();
    _resolvedPreds.reset();
    _toSolvePreds.reset();
    _solvePreds.reset();
    _unresolvedPreds.reset();
    _toUnresolvedPreds.reset();

    _resolvedMonoPreds.reset();
    _solveMonoPreds.reset();

    foreach (pred; _allPreds) {
      if (pred.isRolled()) {
	_rolledPreds ~= pred;
      }
      else if (pred.hasDeps()) {
	_unresolvedPreds ~= pred;
      }
      else {
	procResolved(pred);
	// _resolvedPreds ~= pred;
      }
    }

    foreach (pred; _rolledPreds) {
      pred.randomizeDeps();
    }

    solveValDomains();
    
    while (_resolvedMonoPreds.length > 0 ||
	   _resolvedPreds.length > 0 ||
	   _unresolvedPreds.length > 0) {
      // import std.stdio;

      // if (_resolvedMonoPreds.length > 0) {
      // 	writeln("Here for _resolvedMonoPreds: ", _resolvedMonoPreds.length);
      // }
      // if (_resolvedPreds.length > 0) {
      // 	writeln("Here for _resolvedPreds: ", _resolvedPreds.length);
      // }
      // if (_unresolvedPreds.length > 0) {
      // 	writeln("Here for _unresolvedPreds: ", _unresolvedPreds.length);
      // }
      // if (_unrolledPreds.length > 0) {
      // 	writeln("Here for _unrolledPreds: ", _unrolledPreds.length);
      // }
      // _lap, like _cycle starts with 1
      // this is to avoid default values
      _lap += 1;
      // writeln("Lap: ", _lap);

      _toUnrolledPreds.swop(_unrolledPreds);
      _toUnrolledPreds.reset();
      foreach (pred; _unrolledPreds) {
	pred.randomizeDepsRolled();
      }
      
      _unrolledPreds.reset();

      foreach (pred; _rolledPreds) {
	pred.markAsUnresolvedRolled(_lap);
      }

      foreach (pred; _unresolvedPreds) {
	pred.randomizeDeps();
      }

      foreach (pred; _unresolvedPreds) {
	if (pred.isResolved()) {
	  procResolved(pred);
	}
	else {
	  _toUnresolvedPreds ~= pred;
	  pred.markAsUnresolved(_lap);
	}
      }

      _resolvedMonoPreds.swop(_toSolvePreds);

      foreach (pred; _toSolvePreds) {
	// import std.stdio;
	// writeln("Mono: ", pred.name());
	if (! procMonoDomain(pred)) {
	  // writeln("Mono Unsolved: ", pred.name());
	  _resolvedPreds ~= pred;
	}
      }
      _toSolvePreds.reset();
      
      _resolvedPreds.swop(_toSolvePreds);

      foreach (pred; _toSolvePreds) {
	if (pred.isMarkedUnresolved(_lap)) {
	  _resolvedPreds ~= pred;
	}
	else {
	  if (! procMaybeMonoDomain(pred)) {
	    addCstStage(pred);
	  }
	}
      }

      foreach(stage; _solveStages) {
	if(stage !is null) {
	  solveStage(stage, stageIndx);
	}
      }
      _solveStages.reset();
      _toSolvePreds.reset();

      _unresolvedPreds.reset();
      _unresolvedPreds.swop(_toUnresolvedPreds);
    }
  }

  void solveStage(CstStage stage, ref int stageIndx) {
    import std.conv;
    CstPredicate[] preds = stage._predicates;

    // foreach (pred; preds) {
    //   import std.stdio;
    //   writeln("Solver: ", pred.name(), " update: ", pred.hasUpdate());
    // }
    BDD solveBDD = _esdl__buddy.one();
    foreach(vec; stage._domVars) {
      if(vec.stage is stage) {
	if(vec.bddvec(_esdl__buddy).isNull()) {
	  vec.bddvec(_esdl__buddy).buildVec(vec.domIndex, vec.signed);
	}
      }
    }

    // make the bdd tree
    bool updated = false;
    foreach (pred; preds) {
      updated |= pred.hasUpdate();
    }
    // import std.stdio;
    // writeln("Saved Stages: ", savedStages.length);
    // writeln("Saved Stages Index: ", stageIndx);
    // if (savedStages.length > stageIndx) {
    //   foreach (pred; savedStages[stageIndx]._predicates) {
    // 	writeln("saved: ", pred.name());
    //   }
    //   writeln("Comparison: ", savedStages[stageIndx]._predicates[0] == stage._predicates[0]);
    // }
    // foreach (pred; stage._predicates) {
    //   writeln("saved: ", pred.name());
    // }
    if ((! updated) &&
	savedStages.length > stageIndx &&
	savedStages[stageIndx]._predicates == stage._predicates) {
      // import std.stdio;
      // writeln("Reusing previous BDD solution");
      stage._solveBDD = savedStages[stageIndx]._solveBDD;
      stage._bddDist = savedStages[stageIndx]._bddDist;
      solveBDD = stage._solveBDD;
    }
    else {
      foreach(vec; stage._domVars) {
	BDD primBdd = vec.getPrimBdd(_esdl__buddy);
	if(! primBdd.isOne()) {
	  solveBDD = solveBDD & primBdd;
	}
      }
      foreach(pred; preds) {
	solveBDD = solveBDD & pred.getExpr().getBDD(stage, _esdl__buddy);
	// writeln(pred.name());
      }
      stage._solveBDD = solveBDD;
      stage._bddDist.clear();
      solveBDD.satDist(stage._bddDist);
    }


    // import std.stdio;
    // writeln("bddDist: ", stage._bddDist);
    
    auto solution = solveBDD.randSatOne(this._esdl__rGen.get(),
					stage._bddDist);
    auto solVecs = solution.toVector();

    byte[] bits;
    if(solVecs.length != 0) {
      bits = solVecs[0];
    }

    foreach (vec; stage._domVars) {
      ulong v;
      enum WORDSIZE = 8 * v.sizeof;
      auto bitvals = solveBDD.getIndices(vec.domIndex);
      auto NUMWORDS = (bitvals.length+WORDSIZE-1)/WORDSIZE;
      
      if (_solveValue.length < NUMWORDS) {
	_solveValue.length = NUMWORDS;
      }
      foreach (i, ref j; bitvals) {
	uint pos = (cast(uint) i) % WORDSIZE;
	uint word = (cast(uint) i) / WORDSIZE;
	if (bits.length == 0 || bits[j] == -1) {
	  v = v + ((cast(size_t) _esdl__rGen.flip()) << pos);
	}
	else if (bits[j] == 1) {
	  v = v + ((cast(ulong) 1) << pos);
	}
	if (pos == WORDSIZE - 1 || i == bitvals.length - 1) {
	  _solveValue[word] = v;
	  v = 0;
	}
      }
      vec.setVal(array(_solveValue[0..NUMWORDS]));
    }
    stage.id(stageIndx);

    // foreach (vec; stage._domVars) {
    //   vec.execCbs();
    // }
    

    // save for future reference
    while (savedStages.length <= stageIndx) {
      savedStages ~= new CstStage();
    }
    assert(savedStages[stageIndx] !is stage);

    savedStages[stageIndx].copyFrom(stage);

    stageIndx += 1;
  }

  // list of constraint preds to solve at a given stage
  // void addCstStage(CstVecPrim prim, ref CstStage[] cstStages) {
  //   assert (prim !is null);
  //   if(prim.stage() is null) {
  //     CstStage stage = new CstStage();
  //     cstStages ~= stage;
  //     prim.stage = stage;
  //     stage._domVars ~= prim;
  //     // cstStages[stage]._domVars ~= prim;
  //   }
  // }

  void addCstStage(CstPredicate pred) {
    // uint stage = cast(uint) _solveStages.length;
    // auto vecs = pred.getExpr().getRndDomains(true);
    auto vecs = pred.getDomains();
    // auto vecs = pred._vars;
    // import std.stdio;
    // foreach (vec; vecs) writeln(vec.name());
    CstStage stage;
    foreach (ref vec; vecs) {
      if (! vec.solved()) {
	assert(vec !is null);
	if (vec.stage() is null) {
	  // import std.stdio;
	  // writeln("new stage for vec: ", vec.name());
	  // writeln("pred: ", pred.name());
	  if (stage is null) {
	    stage = new CstStage();
	    _solveStages ~= stage;
	  }
	  vec.stage = stage;
	  stage._domVars ~= vec;
	  // _solveStages[stage]._domVars ~= vec;
	}
	if (stage !is vec.stage()) { // need to merge stages
	  // import std.stdio;
	  // writeln("merging");
	  mergeCstStages(stage, vec.stage());
	  stage = vec.stage();
	}
      }
    }
    if (stage is null) {
      stage = new CstStage();
      _solveStages ~= stage;
    }
    // import std.stdio;
    // writeln(pred.name());
    // assert (stage !is null);
    // writeln(stage._predicates.length);
    stage._predicates ~= pred;
  }

  void mergeCstStages(CstStage fromStage, CstStage toStage) {
    if(fromStage is null) {
      // fromStage has not been created yet
      return;
    }
    foreach(ref vec; fromStage._domVars) {
      vec.stage = toStage;
    }
    toStage._domVars ~= fromStage._domVars;
    toStage._predicates ~= fromStage._predicates;
    if(_solveStages[$-1] is fromStage) {
      _solveStages.length = _solveStages.length - 1;
    }
    else {
      fromStage._domVars.length = 0;
      fromStage._predicates.length = 0;
    }
  }

  void initDomains() { // (T)(T t) {
    assert(_root is this);
    // int[] domList;
    

    // foreach (dom; _cstRndDomains) dom.reset();
    
    // this._domIndex = 0;
    // _domains.length = 0;
    // _cstRndDomains.length = 0;
    
    // _esdl__buddy.clearAllDomains();

    
    // foreach(stmt; _esdl__cstExprs._exprs) {
    //   addDomains(stmt.getRndDomains(false));
    // }
  }

  // void addDomains(CstDomain[] domains) {
  //   uint[] domList;

  //   // foreach (vec; domains) {
  //   //   assert(vec.domIndex == uint.max);
  //   //   // vec.domIndex = uint.max;
  //   // }

  //   foreach(vec; domains) {
  //     if(vec.domIndex == uint.max) {
  // 	vec.domIndex = this._domIndex++;
  // 	domList ~= vec.bitcount;
  //     }
  //   }
  //   _domains ~= _esdl__buddy.extDomVec(domList);
  // }

  void printSolution() {
    // import std.stdio;
    // writeln("There are solutions: ", _theBDD.satCount());
    // writeln("Distribution: ", dist);
    // auto randSol = _theBDD.randSat(randGen, dist);
    // auto solution = _theBDD.fullSatOne();
    // solution.printSetWith_Domains();
  }
}
