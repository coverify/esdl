module esdl.solver.z3;
import std.stdio;
import std.conv: to;


import std.container: Array;
// import std.array;

import esdl.solver.base;
import esdl.solver.z3expr;
import esdl.rand.expr;
import esdl.rand.base;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.misc;
import esdl.intf.z3.z3;
import esdl.intf.z3.api.z3_types: Z3_ast;
import esdl.intf.z3.api.z3_api: Z3_mk_int64, Z3_mk_unsigned_int64;

import std.algorithm.searching: canFind;

private import std.typetuple: staticIndexOf, TypeTuple;
private import std.traits: BaseClassesTuple; // required for staticIndexOf


struct Z3Term
{
  import std.conv: to;
  
  enum Type: ubyte { BOOLEXPR, BVEXPR, ULONG }

  BoolExpr _boolExpr;
  BvExpr _bvExpr;
  ulong   _ulong;

  Type _type;

  bool opEquals()(const ref Z3Term other) const {
    // this is placeholder so that Array!Z3Term can compile
    assert (false);
  }

  ref BvExpr toBv() return {
    if (_type != Type.BVEXPR) assert(false, "Expected a BVEXPR, got "
				     ~ _type.to!string);
    return _bvExpr;
  }

  ref BoolExpr toBool() return {
    if (_type != Type.BOOLEXPR) assert(false, "Expected a BOOLEXPR, got "
				       ~ _type.to!string);
    return _boolExpr;
  }

  ulong toUlong() {
    if (_type != Type.ULONG) assert(false, "Expected a ULONG, got "
				    ~ _type.to!string);
    return _ulong;
  }

  // workaround for https://issues.dlang.org/show_bug.cgi?id=20876
  this(this) { }
  // this(ref Z3Term other) {
  //   _boolExpr = other._boolExpr;
  //   _bvExpr = other._bvExpr;
  //   _ulong = other._ulong;
  //   _type = other._type;
  // }

  this(ref BvExpr expr) {
    _bvExpr = expr;
    _type = Type.BVEXPR;
  }

  this(BvExpr expr) {
    _bvExpr = expr;
    _type = Type.BVEXPR;
  }

  this(ref BoolExpr expr) {
    _boolExpr = expr;
    _type = Type.BOOLEXPR;
  }

  this(BoolExpr expr) {
    _boolExpr = expr;
    _type = Type.BOOLEXPR;
  }

  this(ulong expr) {
    _ulong = expr;
    _type = Type.ULONG;
  }

}

struct BvVar
{
  enum State: ubyte {INIT, STABLE, VARIABLE}
  BvExpr _dom;
  long   _val;
  State  _state;

  BoolExpr _rule;

  alias _dom this;
  
  this(BvExpr dom) {
    _dom = dom;
    _val = 0;
    _state = State.INIT;
  }

  ref BvVar opAssign(ref BvExpr dom) return {
    assert (_dom.isNull());
    _dom = dom;
    _val = 0;
    _state = State.INIT;
    return this;
  }

  BvExpr getValExpr() {
    Sort sort = _dom.getSort();
    Context context = _dom.context();
    Z3_ast r;
    if (_dom.isSigned()) r = Z3_mk_int64(context, _val, sort);
    else        r = Z3_mk_unsigned_int64(context, _val, sort);
    return BvExpr(context, r, _dom.isSigned());
  }

  ref BoolExpr getRule() return {
    return _rule;
  }
  
  void update(CstDomain dom, CstZ3Solver solver) {
    assert (dom.isSolved());
    long val = dom.value();
    if (_val != val) {
      _val = val;
      BoolExpr rule = eq(_dom, getValExpr());
      _rule = rule;
      final switch (_state) {
      case State.INIT:
	_state = State.STABLE;
	solver._countStable += 1;
	break;
      case State.STABLE:
	_state = State.VARIABLE;
	solver._countStable -= 1;
	solver._countVariable += 1;
	break;
      case State.VARIABLE:
	solver._refreshVar = true;
	break;
      }
    }
    else {
      final switch (_state) {
      case State.INIT:
	BoolExpr rule = eq(_dom, getValExpr());
	_rule = rule;
	_state = State.STABLE;
	solver._countStable += 1;
	break;
      case State.STABLE:
	break;
      case State.VARIABLE:
	break;
      }
    }
  }
}

class CstZ3Solver: CstSolver
{
  
  Z3Term[] _evalStack;

  Z3Term _term;

  BvExpr[] _domains;
  BvVar[] _variables;

  Context _context;

  Solver _solver;
  Optimize _optimize;
  bool _needOptimize;

  _esdl__Proxy _proxy;

  uint _countStable;
  uint _countVariable;

  // whether some variables have changed and a refresh required
  bool _refreshVar;	   // whether the variable values need refresh
  byte _pushSolverCount;   // balance number of pushed z3 context has
  byte _pushOptimizeCount; // balance number of pushed z3 context has

  uint _seed;

  Z3_ast[] _vector;

  CstVectorOp _state;
  // the group is used only for the purpose of constructing the Z3 solver
  // otherwise the solver identifies with the signature only
  this(string signature, CstPredGroup group) {
    import std.stdio;
    super(signature);

    _proxy = group.getProxy();

    setParam("auto_config", false);
    setParam("smt.phase_selection", 5);
    Config cfg = new Config();
    _context = new Context(cfg);

    // _vector = BvExprVector(_context);
    
    CstDomain[] doms = group.domains();
    _domains.length = doms.length;

    foreach (i, ref dom; _domains) {
      import std.string: format;
      // import std.stdio;
      // writeln("Adding Z3 Domain for @rand ", doms[i].name());
      auto d = BvExpr(_context, format("_dom%s", i), doms[i].bitcount, doms[i].signed());
      dom = d;
    }

    CstDomain[] vars = group.variables();
    _variables.length = vars.length;

    foreach (i, ref var; _variables) {
      import std.string: format;
      // import std.stdio;
      // writeln("Adding Z3 Domain for variable ", vars[i].name());
      auto d = BvExpr(_context, format("_var%s", i), vars[i].bitcount, vars[i].signed());
      var = d;
    }

    Solver solver = Solver(_context);
    _solver = solver;

    if (group.hasSoftConstraints()) {
      _needOptimize = true;
      Optimize optimize = Optimize(_context);
      _optimize = optimize;
    }

    foreach (dom; doms) {
      if (dom.visitDomain(this)) {
	assert(_evalStack.length == 1);
	addRule(_solver, _evalStack[0].toBool());
	if (_needOptimize) addRule(_optimize, _evalStack[0].toBool());
	_evalStack.length = 0;
      }
    }
    
    foreach (pred; group.predicates()) {
      // import std.stdio;
      // writeln("Working on: ", pred.name());
      if (pred.group() !is group) {
	assert (false, "Group Violation " ~ pred.name());
      }
      pred.visit(this);
      assert(_evalStack.length == 1);
      uint softWeight = pred.getSoftWeight();
      if (softWeight == 0) {
	addRule(_solver, _evalStack[0].toBool());
	if (_needOptimize) addRule(_optimize, _evalStack[0].toBool());
      }
      else {
	// ignore the soft constraint
	assert (_needOptimize);
	addRule(_optimize, _evalStack[0].toBool(), softWeight, "@soft");
      }
      _evalStack.length = 0;
    }

    _seed = _proxy._esdl__rGen.gen!uint();
    _solver.set("random_seed", _seed);
    

    // if (_needOptimize) this.pushOptimize();
    // this.pushSolver();

    // If there are no soft constraints and no variables, we still need a push
    // to make sure that we get an SMT solver and we can rondomize results
    _solver.push();

    // writeln("auto_config: ", getParam("auto_config"));
    // writeln("smt.phase_selection: ", getParam("smt.phase_selection"));
    // writeln("smt.arith.random_initial_value: ", getParam("smt.arith.random_initial_value"));
    // writeln("smt.random_seed: ", getParam("smt.random_seed"));
    // writeln("sat.phase: ", getParam("sat.phase"));
    // writeln("sat.random_seed: ", getParam("sat.random_seed"));
  }

  override string describe() {
    return "Z3 SMT Solver"  ~ super.describe();
  }

  // BvVar.State varState;

  enum State: ubyte
  {   NULL,			// Does not exist, no action          pop n push n
      INIT,			// Did not exist, create now          pop n push y
      NONE,			// exists, no action needed           pop n push n
      PROD,			// exists, need to rework             pop y push y
      TEAR,                     // exists, no longer required         pop y push n
      DONE			// has been destroyed - end           pop n push n
  }

  ubyte pushLevel(State state) {
    if (state <= State.NULL || state >= State.TEAR) return 0;
    else return 1;
  }

  State _stableState;
  State _variableState;
  State _assumptionState;
  
  void pushOptimize() {
    assert(_pushOptimizeCount <= 2);
    _pushOptimizeCount += 1;
    _optimize.push();
  }

  void pushSolver() {
    assert(_pushSolverCount <= 2);
    _pushSolverCount += 1;
    _solver.push();
  }

  void popOptimize() {
    assert(_pushOptimizeCount >= 0);
    _pushOptimizeCount -= 1;
    _optimize.pop();
  }

  void popSolver() {
    assert(_pushSolverCount >= 0);
    _pushSolverCount -= 1;
    _solver.pop();
  }

  bool[] _assumptionFlags;

  bool _optimizeInit = false;

  Expr[] optimize() {
    Expr[] assumptions;
    bool[] assumptionFlags;
    Model model = _optimize.getModel();
    assert (_optimize.objectives.size() == 1);
    auto objective = _optimize.objectives[0];
    if (objective.isAdd) {	// multiple soft constraints
      for (uint i=0; i!=objective.numArgs(); ++i) {
	auto subObjective = objective.arg(i);
	assert (subObjective.isIte());
	// writeln("Objective: ", subObjective._ast.toString());
	// writeln("Assertion: ", subObjective.numArgs());
	// writeln("Objective: ", subObjective.arg(0)._ast.toString());
	// writeln(model.eval(subObjective)._ast.toString());
	if (model.eval(subObjective).getNumeralDouble() < 0.01) { // == 0.0
	  assumptionFlags ~= true;
	  Expr assumption = subObjective.arg(0);
	  // writeln("Objective: ", assumption._ast.toString());
	  assumptions ~= subObjective.arg(0);
	}
	else {
	  assumptionFlags ~= false;
	}
      }
    }
    else {			// single soft constraint
      assert (objective.isIte());
      // writeln("Objective: ", subObjective._ast.toString());
      // writeln("Assertion: ", subObjective.numArgs());
      // writeln("Objective: ", subObjective.arg(0)._ast.toString());
      // writeln(model.eval(subObjective)._ast.toString());
      if (model.eval(objective).getNumeralDouble() < 0.01) { // == 0.0
	assumptionFlags ~= true;
	Expr assumption = objective.arg(0);
	// writeln("Objective: ", assumption._ast.toString());
	assumptions ~= objective.arg(0);
      }
      else {
	assumptionFlags ~= false;
      }
    }

    if (_assumptionFlags != assumptionFlags) {
      if (_assumptionFlags.length == 0) {
	_assumptionState = State.INIT;
      }
      else {
	_assumptionState = State.PROD;
      }
      _assumptionFlags = assumptionFlags;
    }
    else {
      _assumptionState = State.NONE;
    }
    return assumptions[];
  }
  
  override bool solve(CstPredGroup group) {
    updateVars(group);
    if (_needOptimize) {
      if (updateOptimize() || (_optimizeInit is false)) {
	if (_proxy._esdl__debugSolver()) {
	  import std.stdio;
	  writeln(_optimize);
	}
	_optimize.check();
	Expr[] assumptions = optimize();
	_optimizeInit = true;
	updateSolver(assumptions);
      }
    }
    else {
      updateSolver();
    }
    
    updateVarState(_variableState);
    updateVarState(_stableState);
    updateVarState(_assumptionState);

    assert (pushLevel(_variableState) + pushLevel(_stableState) +
	    pushLevel(_assumptionState) == _pushSolverCount,
	    "_variableState: " ~ _variableState.to!string() ~
	    " _stableState: " ~ _stableState.to!string() ~
	    " _assumptionState: " ~ _assumptionState.to!string() ~
	    " _pushSolverCount: " ~ _pushSolverCount.to!string());
    
    if (_needOptimize) {
      assert (pushLevel(_variableState) +
	      pushLevel(_stableState) == _pushOptimizeCount,
	      "_variableState: " ~ _variableState.to!string() ~
	      " _stableState: " ~ _stableState.to!string() ~
	      " _pushOptimizeCount: " ~ _pushSolverCount.to!string());
    }
    
    CstDomain[] doms = group.domains();

    if (_proxy._esdl__debugSolver()) {
      import std.stdio;
      writeln(_solver);
    }
    _solver.check();
    // writeln(_solver.check());
    // writeln(_solver.getModel());
    auto model = _solver.getModel();
    foreach (i, ref dom; _domains) {
      // import std.string: format;
      // string value;
      BvExpr vdom = dom.mapTo(model, true);
      ulong vlong = vdom.getNumeralInt64();
      doms[i].setVal(vlong);
      // writeln("Value for Domain ", doms[i].name(), ": ",
      // 	      vdom.getNumeralInt64());
      // writeln(vdom.getNumeralInt64());
      // vdom.isNumeral(value);
      // writeln(value);
    }

    return true;
  }

  void updateVarState(ref State state) {
    final switch (state) {
    case State.NULL: break;
    case State.INIT: state = State.NONE; break;
    case State.NONE: break;
    case State.PROD: state = State.NONE; break;
    case State.TEAR: state = State.DONE; break;
    case State.DONE: break;
    }
  }
  
  void updateVars(CstPredGroup group) {
    
    CstDomain[] vars = group.variables();
    _refreshVar = false;
    uint pcountStable = _countStable;
    uint pcountVariable = _countVariable;
    foreach (i, ref var; _variables) var.update(vars[i], this);
    assert (_countStable + _countVariable == _variables.length);
    // import std.stdio;
    // writeln("refresh: ", _refreshVar,
    // 	    " prev counts: ", pcountStable, ", ", pcountVariable,
    // 	    " now counts: ", _countStable, ", ", _countVariable);

    if (pcountStable == 0) {
      assert (_stableState is State.NULL || _stableState is State.DONE);
      if (_countStable > 0) {
	assert (_stableState is State.NULL);
	_stableState = State.INIT;
      }
    }
      
    if (pcountStable != 0) {
      assert (_stableState is State.NONE);
      if (_countStable == 0) _stableState = State.TEAR;
      else if (_countStable != pcountStable) {
	assert (_countStable < pcountStable);
	_stableState = State.PROD;
      }
    }

    if (pcountVariable == 0) {
      assert (_variableState is State.NULL);
      if (_countVariable > 0) {
	_variableState = State.INIT;
      }
    }
      
    if (pcountVariable != 0) {
      assert (_variableState is State.NONE);
      if (_countVariable == 0) {
	assert (false);
      }
      else if (_refreshVar || _countVariable != pcountVariable) {
	assert (_countVariable >= pcountVariable);
	_variableState = State.PROD;
      }
    }
  }

  bool updateOptimize() {
    bool hasUpdated;
    if (_variableState == State.PROD) {
      hasUpdated = true;
      this.popOptimize();		// for variables
    }
    if (_stableState == State.PROD || _stableState == State.TEAR) {
      hasUpdated = true;
      this.popOptimize();		// for constants
    }

    // process constants -- if required
    if (_stableState == State.PROD || _stableState == State.INIT) {
      hasUpdated = true;
      this.pushOptimize();
      foreach (i, ref var; _variables) {
	if (var._state == BvVar.State.STABLE)
	  addRule(_optimize, var.getRule());
      }
    }
    if (_variableState == State.PROD || _variableState == State.INIT) {
      hasUpdated = true;
      this.pushOptimize();
      foreach (i, ref var; _variables) {
	if (var._state == BvVar.State.VARIABLE)
	  addRule(_optimize, var.getRule());
      }
    }
    return hasUpdated;
  }

  void updateSolver(Expr[] assumptions=[]) {
    if (_variableState == State.PROD) {
      this.popSolver();		// for variables
    }
    if (_stableState == State.PROD ||
	_stableState == State.TEAR ||
	_stableState == State.INIT) {
      if (_assumptionState == State.PROD || _assumptionState == State.NONE) {
	this.popSolver();	// for assumptions
      }
    }
    else {
      if (_assumptionState == State.PROD) {
	this.popSolver();	// for assumptions
      }
    }
    if (_stableState == State.PROD || _stableState == State.TEAR) {
      this.popSolver();		// for constants
    }

    // process constants -- if required
    if (_stableState == State.PROD || _stableState == State.INIT) {
      this.pushSolver();
      foreach (i, ref var; _variables) {
	if (var._state == BvVar.State.STABLE)
	  addRule(_solver, var.getRule());
      }
    }
    if (_stableState == State.PROD || _stableState == State.TEAR ||
	_stableState == State.INIT) {
      if (_assumptionState != State.NULL) {
	this.pushSolver();
	foreach (assumption; assumptions) {
	  _solver.add(assumption);
	}
      }
    }
    else {
      if (_assumptionState == State.PROD || _assumptionState == State.INIT) {
	this.pushSolver();
	foreach (assumption; assumptions) {
	  _solver.add(assumption);
	}
      }
    }
      
    if (_variableState == State.INIT || _variableState == State.PROD) {
      this.pushSolver();
      foreach (i, ref var; _variables) {
	if (var._state == BvVar.State.VARIABLE)
	  addRule(_solver, var.getRule());
      }
    }
  }

  override void pushToEvalStack(CstDomain domain) {
    // import std.stdio;
    uint n = domain.annotation();
    // writeln("push: ", domain.name(), " annotation: ", n);
    // writeln("_domains has a length: ", _domains.length);

    if (domain.isSolved()) { // is a variable
      pushToEvalStack(_variables[n]);
    }
    else {
      pushToEvalStack(_domains[n]);
    }

  }

  override void pushToEvalStack(CstValue value) {
    // writeln("push: value ", value.value());
    BvExpr bv = bvNumVal(_context, value.value(),
			 value.bitcount(), value.signed());
    pushToEvalStack(bv);
  }

  override void pushToEvalStack(ulong value, uint bitcount, bool signed) {
    BvExpr bv = bvNumVal(_context, value, bitcount, signed);
    pushToEvalStack(bv);
  }

  override void pushToEvalStack(bool value) {
    BoolExpr bb = boolVal(_context, value);
    pushToEvalStack(bb);
  }

  override void pushIndexToEvalStack(ulong value) {
    // writeln("push: ", value);
    _evalStack ~= Z3Term(value);
  }

  override void processEvalStack(CstUnaryOp op) {
    // writeln("eval: CstUnaryOp ", op);
    final switch (op) {
    case CstUnaryOp.NOT:
      BvExpr e = compliment(_evalStack[$-1].toBv());
      popEvalStack();
      pushToEvalStack(e);
      break;
    case CstUnaryOp.NEG:
      BvExpr e = neg(_evalStack[$-1].toBv());
      popEvalStack();
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstBinaryOp op) {
    // writeln("eval: CstBinaryOp ", op);
    final switch (op) {
    case CstBinaryOp.AND:
      BvExpr e = bvand(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.OR:
      BvExpr e = bvor(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.XOR:
      BvExpr e = bvxor(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.ADD:
      BvExpr e = add(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.SUB:
      BvExpr e = sub(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.MUL:
      BvExpr e = mul(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.DIV:
      BvExpr e = div(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.REM:
      BvExpr e = rem(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.LSH:
      BvExpr e = lsh(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.RSH:			// Arith shift right ">>"
      BvExpr e = rsh(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstBinaryOp.LRSH:			// Logic shift right ">>>"
      BvExpr e = lrsh(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstCompareOp op) {
    // writeln("eval: CstCompareOp ", op);
    final switch (op) {
    case CstCompareOp.LTH:
      BoolExpr e = lt(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstCompareOp.LTE:
      BoolExpr e = le(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstCompareOp.GTH:
      BoolExpr e = gt(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstCompareOp.GTE:
      BoolExpr e = ge(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstCompareOp.EQU:
      BoolExpr e = eq(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstCompareOp.NEQ:
      BoolExpr e = neq(_evalStack[$-2].toBv(), _evalStack[$-1].toBv());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstLogicOp op) {
    // writeln("eval: CstLogicOp ", op);
    final switch (op) {
    case CstLogicOp.LOGICAND:
      BoolExpr e = and(_evalStack[$-2].toBool(), _evalStack[$-1].toBool());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICOR:
      BoolExpr e = or(_evalStack[$-2].toBool(), _evalStack[$-1].toBool());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICIMP:
      BoolExpr e = implies(_evalStack[$-2].toBool(), _evalStack[$-1].toBool());
      popEvalStack(2);
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICNOT:
      BoolExpr e = not(_evalStack[$-1].toBool());
      popEvalStack();
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstSliceOp op) {
    // assert (op == CstSliceOp.SLICE);
    final switch (op) {
    case CstSliceOp.SLICE:
      BvExpr e = _evalStack[$-3].toBv().extract(cast(uint) _evalStack[$-1].toUlong() - 1,
						cast(uint) _evalStack[$-2].toUlong());
      popEvalStack(3);
      pushToEvalStack(e);
      break;
    case CstSliceOp.SLICEINC:
      BvExpr e = _evalStack[$-3].toBv().extract(cast(uint) _evalStack[$-1].toUlong(),
						cast(uint) _evalStack[$-2].toUlong());
      popEvalStack(3);
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstVectorOp op) {
    // import std.conv: to;
    // assert (false, "CstVectorOp is handled only by SMT solvers: " ~ op.to!string());
    // final switch (op) {
    // case CstVectorOp.NONE:
    //   assert (false, "Unexpected op: CstVectorOp.NONE");
    // case
    //   CstVectorOp.BEGIN_INT,
    //   CstVectorOp.BEGIN_UINT,
    //   CstVectorOp.BEGIN_LONG,
    //   CstVectorOp.BEGIN_ULONG:
    //   assert (_state is CstVectorOp.NONE);
    //   _state = op;
    //   _vector.length = 0;
    //   // BvExprVector vector = BvExprVector(_context);
    //   // _vector = vector;
    //   break;
    // case CstVectorOp.SUM:
    //   BvExpr e = sum(_vector);
    //   pushToEvalStack(e);
    //   _state = CstVectorOp.NONE;
    //   break;
    // case CstVectorOp.MULT:
    //   // BoolExpr e = mul(_vector);
    //   // pushToEvalStack(e);
    //   // _state = CstVectorOp.NONE;
    //   assert(false, "TBD");
    //   // break;
    // }
  }

  override void processEvalStack(CstInsideOp op) {
    final switch (op) {
    case CstInsideOp.INSIDE:
      _term = _evalStack[$-1];
      popEvalStack();
      break;
    case CstInsideOp.EQUAL:
      BoolExpr e = eq(_term.toBv(), _evalStack[$-1].toBv());
      popEvalStack();
      pushToEvalStack(e);
      processEvalStack(CstLogicOp.LOGICOR);
      break;
    case CstInsideOp.RANGE:
      BoolExpr upper = lt(_term.toBv(), _evalStack[$-1].toBv());
      BoolExpr lower = ge(_term.toBv(), _evalStack[$-2].toBv());
      popEvalStack(2);
      pushToEvalStack(upper);
      pushToEvalStack(lower);
      processEvalStack(CstLogicOp.LOGICAND);
      processEvalStack(CstLogicOp.LOGICOR);
      break;
    case CstInsideOp.RANGEINCL:
      BoolExpr upper = le(_term.toBv(), _evalStack[$-1].toBv());
      BoolExpr lower = ge(_term.toBv(), _evalStack[$-2].toBv());
      popEvalStack(2);
      pushToEvalStack(upper);
      pushToEvalStack(lower);
      processEvalStack(CstLogicOp.LOGICAND);
      processEvalStack(CstLogicOp.LOGICOR);
      break;
    case CstInsideOp.DONE:
      _term = Z3Term.init;
      break;
    }
  }

  override void processEvalStack(CstUniqueOp op) {
    import esdl.intf.z3.api;
    final switch(op) {
    case CstUniqueOp.INIT:
      foreach (uv; _vector) {
	Z3_dec_ref(_context, uv);
      }
      _vector.length = 0;
      break;
    case CstUniqueOp.INT:
    case CstUniqueOp.UINT:
      assert (_evalStack.length > 0);
      BvExpr bv = _evalStack[$-1].toBv();
      bool signed = bv.isSigned();
      uint size = bv.size();
      assert (size <= 32);
      uint extBy = 32 - size;
      popEvalStack();

      Z3_ast uv = bv.getAST();
      if (extBy > 0) {
	if (signed) uv = Z3_mk_sign_ext(_context, extBy, uv);
	else uv = Z3_mk_zero_ext(_context, extBy, uv);
      }

      Z3_inc_ref(_context, uv);
      _vector ~= uv;
      break;
    case CstUniqueOp.LONG:
    case CstUniqueOp.ULONG:
      assert (_evalStack.length > 0);
      BvExpr bv = _evalStack[$-1].toBv();
      bool signed = bv.isSigned();
      uint size = bv.size();
      assert (size <= 64);
      uint extBy = 64 - size;
      popEvalStack();

      Z3_ast uv = bv.getAST();
      if (extBy > 0) {
	if (signed) uv = Z3_mk_sign_ext(_context, extBy, uv);
	else uv = Z3_mk_zero_ext(_context, extBy, uv);
      }

      Z3_inc_ref(_context, uv);
      _vector ~= uv;
      break;
    case CstUniqueOp.UNIQUE:
      if (_vector.length == 0) {
	pushToEvalStack(true);
      }
      else {
	Z3_ast r = Z3_mk_distinct(_context, cast(uint) _vector.length, _vector.ptr);
	_context.checkError();
	BoolExpr be = BoolExpr(_context, r);
	pushToEvalStack(be);
	// destroy the _vector
	foreach (uv; _vector) {
	  Z3_dec_ref(_context, uv);
	}
	_vector.length = 0;
      }
      break;
    }
  }

  void popEvalStack(uint count = 1) {
    assert (_evalStack.length >= count);
    _evalStack.length = _evalStack.length - count;
  }
  
  void pushToEvalStack(ref BvExpr vec) {
    Z3Term term = Z3Term(vec);
    pushToEvalStack(term);
  }
  
  void pushToEvalStack(ref BoolExpr b) {
    Z3Term term = Z3Term(b);
    pushToEvalStack(term);
  }  

  void pushToEvalStack(ref Z3Term term) {
    // writeln("Pushing on _evalStack: ", term.toString());
    _evalStack ~= term;
    // writeln("After PUSH _evalStack is of size: ", _evalStack.length);
  }
}
