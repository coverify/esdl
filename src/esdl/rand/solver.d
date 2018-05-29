module esdl.rand.solver;
import esdl.rand.obdd;

import esdl.rand.expr: CstBlock, CstVarPrim, CstStage,
  CstBddExpr, // , CstValAllocator
  CstDomain;
import esdl.rand.base;


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

static char[] constraintXlate(string CST, string NAME="") {
  import esdl.rand.cstx;
  CstParser parser = CstParser(CST);
  return parser.translate(NAME);
}

abstract class Constraint(string C): _esdl__ConstraintBase
{
  this(_esdl__SolverRoot eng, string name, uint index) {
    super(eng, name, C, index);
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

abstract class _esdl__SolverRoot {
  // Keep a list of constraints in the class
  _esdl__ConstraintBase[] _esdl__cstsList;
  _esdl__ConstraintBase _esdl__cstWith;
  bool _esdl__cstWithChanged;

  // ParseTree parseList[];
  CstVarPrim[] _esdl__randsList;
  _esdl__RandGen _esdl__rGen;

  _esdl__RandGen _esdl__getRandGen() {
    return _esdl__rGen;
  }

  Buddy _esdl__buddy;

  BddDomain[] _domains;

  CstDomain[] _cstDomains;

  uint _domIndex = 0;
  
  // compositional parent -- not inheritance based
  _esdl__SolverRoot _parent = null;

  bool _esdl__isSeeded = false;

  CstBlock _esdl__cstEqns;

  CstStage[] savedStages;
  
  this(uint seed, bool isSeeded, string name,
       _esdl__SolverRoot parent=null) {
    debug(NOCONSTRAINTS) {
      assert(false, "Constraint engine started");
    }
    _esdl__rGen = new _esdl__RandGen(seed);
    _esdl__isSeeded = isSeeded;
    if(parent is null) {
      _esdl__buddy = new Buddy(400, 400);
      _esdl__cstEqns = new CstBlock();
    }
    else {
      _parent = parent;
    }
  }

  ~this() {
    _esdl__cstsList.length   = 0;
    _esdl__cstWith           = null;
    _esdl__cstWithChanged    = true;
    _esdl__randsList.length  = 0;
  }

  // overridden by Randomization mixin -- see meta.d
  void _esdl__initRands() {}
  void _esdl__initCsts() {}
  void _esdl__doRandomize(_esdl__RandGen randGen) {}

  void solve() { // (T)(T t) {
    // writeln("Solving BDD for number of constraints = ", _esdl__cstsList.length);
    uint lap = 0;
    if (_domains.length is 0 // || _esdl__cstWithChanged is true
	) {
      initDomains();

      // _esdl__cstEqns._esdl__reset(); // start empty
    
      // take all the constraints -- even if disabled
      // if (_esdl__cstEqns.isEmpty()) {
      // foreach(ref _esdl__ConstraintBase cst; _esdl__cstsList) {
      // 	_esdl__cstEqns ~= cst.getCstExpr();
      // }
      // if(_esdl__cstWith !is null) {
      // 	_esdl__cstEqns ~= _esdl__cstWith.getCstExpr();
      // }
      //}

    }

    // CstValAllocator.mark();

    CstStage[] unsolvedStages;	// unresolved stages -- all

    int stageIdx=0;
    CstBddExpr[] unsolvedExprs = _esdl__cstEqns._exprs;	// unstaged Expressions -- all
    // if(_esdl__cstWith !is null) {
    //   unsolvedExprs ~= _esdl__cstWith.getCstExpr()._exprs;
    // }
    while(unsolvedExprs.length > 0 || unsolvedStages.length > 0) {
      lap += 1;
      
      CstBddExpr[] cstExprs = unsolvedExprs;
      unsolvedExprs.length = 0;
      CstStage[] cstStages = unsolvedStages;
      unsolvedStages.length = 0;

      CstBddExpr[] uwExprs;	// unwound expressions
      CstBddExpr[] solveExprs;

      // unwind all the unwindable expressions
      foreach(expr; cstExprs) {
	// import std.stdio;
	// writeln("Unwinding: ", expr.name());
	// auto unwound = expr.unwind();
	// for (size_t i=0; i!=unwound.length; ++i)
	//   {
	//     writeln("Unwound as: ", unwound[i].name());
	//   }
	uwExprs ~= expr.unwind();
      }

      foreach(expr; uwExprs) {
	// if(expr.itrVars().length is 0) {
	if(expr.hasUnresolvedIdx()) {
	  // import std.stdio;
	  // writeln("Adding expression ", expr.name(), " to staged");
	  expr.resolveLap(lap);
	  unsolvedExprs ~= expr;
	}
	else {
	  solveExprs ~= expr;
	}
      }

      foreach (expr; solveExprs) {
	// import std.stdio;
	uint elap = expr.resolveLap();
	// writefln("Unwind Lap of the expr %s is %s", expr.name() , lap);
	if (elap == lap) {
	  unsolvedExprs ~= expr;
	}
	else {
	  addCstStage(expr, cstStages);
	}
      }

      foreach(stage; cstStages) {
	if(stage !is null) {
	  solveStage(stage, stageIdx);
	}
	else {
	  // assert(stage._domVars.length !is 0);
	  unsolvedStages ~= stage;
	}
      }
      
    }

    // CstValAllocator.reset();
    
  }

  void solveStage(CstStage stage, ref int stageIdx) {
    import std.conv;
    // initialize the bdd vectors
    BDD solveBDD = _esdl__buddy.one();
    foreach(vec; stage._domVars) {
      if(vec.stage is stage) {
	if(vec.bddvec.isNull()) {
	  vec.bddvec.buildVec(_domains[vec.domIndex], vec.signed);
	}
      }
    }

    // make the bdd tree
    auto exprs = stage._bddExprs;
    bool refreshed = false;
    foreach (expr; exprs) {
      refreshed |= expr.refresh(stage, _esdl__buddy);
    }
    if ((! refreshed) &&
	savedStages.length > stageIdx &&
	savedStages[stageIdx]._bddExprs == stage._bddExprs) {
      stage._solveBDD = savedStages[stageIdx]._solveBDD;
      solveBDD = stage._solveBDD;
    }
    else {
      foreach(vec; stage._domVars) {
	BDD primBdd = vec.getPrimBdd(_esdl__buddy);
	if(! primBdd.isOne()) {
	  solveBDD = solveBDD & primBdd;
	}
      }
      foreach(expr; exprs) {
	// import std.stdio;
	// writeln(expr.name());
	solveBDD = solveBDD & expr.getBDD(stage, _esdl__buddy);
	// writeln(expr.name());
      }
      stage._solveBDD = solveBDD;
    }

    double[uint] bddDist;
    solveBDD.satDist(bddDist);

    auto solution = solveBDD.randSatOne(this._esdl__rGen.get(),
					bddDist);
    auto solVecs = solution.toVector();

    byte[] bits;
    if(solVecs.length != 0) {
      bits = solVecs[0];
    }

    foreach (vec; stage._domVars) {
      ulong v;
      enum WORDSIZE = 8 * v.sizeof;
      auto bitvals = solveBDD.getIndices(vec.domIndex);
      foreach (uint i, ref j; bitvals) {
	uint pos = i % WORDSIZE;
	uint word = i / WORDSIZE;
	if (bits.length == 0 || bits[j] == -1) {
	  v = v + ((cast(size_t) _esdl__rGen.flip()) << pos);
	}
	else if (bits[j] == 1) {
	  v = v + ((cast(ulong) 1) << pos);
	}
	if (pos == WORDSIZE - 1 || i == bitvals.length - 1) {
	  vec.collate(v, word);
	  v = 0;
	}
      }
    }
    stage.id(stageIdx);

    // save for future reference
    while (savedStages.length <= stageIdx) {
      savedStages ~= new CstStage();
    }
    assert(savedStages[stageIdx] !is stage);
    auto swapping = stage;
    stage = savedStages[stageIdx];
    savedStages[stageIdx++] = swapping;
  }

  // list of constraint eqns to solve at a given stage
  // void addCstStage(CstVarPrim prim, ref CstStage[] cstStages) {
  //   assert (prim !is null);
  //   if(prim.stage() is null) {
  //     CstStage stage = new CstStage();
  //     cstStages ~= stage;
  //     prim.stage = stage;
  //     stage._domVars ~= prim;
  //     // cstStages[stage]._domVars ~= prim;
  //   }
  // }

  void addCstStage(CstBddExpr expr, ref CstStage[] cstStages) {
    // uint stage = cast(uint) _cstStages.length;
    auto vecs = expr.getRndDomains();
    CstStage stage;
    foreach (ref vec; vecs) {
      if (! vec.solved()) {
	assert(vec !is null);
	if (vec.stage() is null) {
	  if (stage is null) {
	    stage = new CstStage();
	    cstStages ~= stage;
	  }
	  vec.stage = stage;
	  stage._domVars ~= vec;
	  // cstStages[stage]._domVars ~= vec;
	}
	if (stage !is vec.stage()) { // need to merge stages
	  mergeCstStages(stage, vec.stage(), cstStages);
	  stage = vec.stage();
	}
      }
    }
    if (stage is null) {
      stage = new CstStage();
      cstStages ~= stage;
    }
    // import std.stdio;
    // writeln(expr.name());
    // assert (stage !is null);
    // writeln(stage._bddExprs.length);
    stage._bddExprs ~= expr;
  }

  void mergeCstStages(CstStage fromStage, CstStage toStage,
		      ref CstStage[] cstStages) {
    if(fromStage is null) {
      // fromStage has not been created yet
      return;
    }
    foreach(ref vec; fromStage._domVars) {
      vec.stage = toStage;
    }
    toStage._domVars ~= fromStage._domVars;
    toStage._bddExprs ~= fromStage._bddExprs;
    if(cstStages[$-1] is fromStage) {
      cstStages.length -= 1;
    }
    else {
      fromStage._domVars.length = 0;
      fromStage._bddExprs.length = 0;
    }
  }

  void initDomains() { // (T)(T t) {
    int[] domList;
    

    foreach (dom; _cstDomains) dom.reset();
    
    this._domIndex = 0;
    _domains.length = 0;
    _cstDomains.length = 0;
    
    _esdl__buddy.clearAllDomains();

    _esdl__cstEqns._esdl__reset(); // start empty

    // take all the constraints -- even if disabled
    foreach(ref _esdl__ConstraintBase cst; _esdl__cstsList) {
      _esdl__cstEqns ~= cst.getCstExpr();
    }

    if(_esdl__cstWith !is null) {
      _esdl__cstEqns ~= _esdl__cstWith.getCstExpr();
    }

    
    foreach(stmt; _esdl__cstEqns._exprs) {
      addDomains(stmt.getRndDomains());
    }
  }

  void addDomains(CstDomain[] domains) {
    int[] domList;

    // foreach (vec; domains) {
    //   assert(vec.domIndex == uint.max);
    //   // vec.domIndex = uint.max;
    // }

    foreach(vec; domains) {
      if(vec.domIndex == uint.max) {
	vec.domIndex = this._domIndex++;
	domList ~= vec.bitcount;
      }
    }
    _domains ~= _esdl__buddy.extDomain(domList);
  }

  void printSolution() {
    // import std.stdio;
    // writeln("There are solutions: ", _theBDD.satCount());
    // writeln("Distribution: ", dist);
    // auto randSol = _theBDD.randSat(randGen, dist);
    // auto solution = _theBDD.fullSatOne();
    // solution.printSetWith_Domains();
  }
}
