module esdl.solver.buddy;


import std.container;
import std.array;

import esdl.solver.base;
import esdl.rand.expr;
import esdl.rand.base;
import esdl.rand.pred;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.misc;
import esdl.solver.obdd;

import esdl.data.bvec: ubvec;

import std.algorithm.searching: canFind;

private import std.typetuple: staticIndexOf, TypeTuple;
private import std.traits: BaseClassesTuple; // required for staticIndexOf

class BuddyContext
{
  bdd _bdd;
  Buddy _buddy;
  double[uint] _bddDist;
  bool _update = true;

  BDD getBDD() { return BDD(_bdd, _buddy); }

  this(Buddy buddy) {
    _buddy = buddy;
    _bdd = _buddy.one();
    _bddStack.reserve(10);
  }

  bdd[] _bddStack;		// to be used with push/pop

  void push() {
    _buddy.addRef(_bdd);
    _bddStack ~= _bdd;
  }

  void pop() {
    _update = true;
    _buddy.delRef(_bdd);
    _bdd = _bddStack[$-1];
    // _buddy.addRef(_bdd);
    _bddStack.length = _bddStack.length - 1;
  }

  void addRule(BDD rule) {
    _update = true;
    _buddy.delRef(_bdd);
    _bdd = getBDD() & rule;
    _buddy.addRef(_bdd);
  }

  void updateDist() {
    if (_update) {
      _update = false;
      _bddDist.clear();
      getBDD().satDist(_bddDist);
    }
  }

  void print() {
    import std.stdio;
    writeln("BDD Context: ");
    writeln("_bdd: ", _bdd);
    writeln("_bddStack Length: ", _bddStack.length);
    foreach(b; _bddStack) {
      writeln("index: ", b);
    }
  }
}

struct BuddyTerm
{
  import std.conv: to;

  enum Type: ubyte { INVALID, BOOLEXPR, BVEXPR, ULONG }

  bdd    _boolExpr;
  bddvec _bvExpr;
  ulong  _ulong;

  Buddy  _buddy;

  Type _type;

  void print() {
    import std.stdio;
    writeln("BuddyTerm: ");
    writeln("Type: ", _type);
    writeln("BddVec: ", _bvExpr.bitvec);
    writeln("BDD: ", _boolExpr);
  }

  void delRef() {
    final switch (_type) {
    case Type.INVALID: break;
    case Type.BOOLEXPR: _buddy.delRef(_boolExpr); break;
    case Type.BVEXPR: _buddy.delRef(_bvExpr); break;
    case Type.ULONG: break;
    }
  }
  
  void addRef() {
    final switch (_type) {
    case Type.INVALID: break;
    case Type.BOOLEXPR: _buddy.addRef(_boolExpr); break;
    case Type.BVEXPR: _buddy.addRef(_bvExpr); break;
    case Type.ULONG: break;
    }
  }
  
  BddVec toBv() return {
    if (_type != Type.BVEXPR) assert(false, "Expected a BVEXPR, got "
				     ~ _type.to!string);
    return BddVec(_bvExpr);
  }

  BDD toBool() return {
    if (_type != Type.BOOLEXPR) assert(false, "Expected a BOOLEXPR, got "
				       ~ _type.to!string);
    return BDD(_boolExpr, _buddy);
  }

  ulong toUlong() {
    if (_type != Type.ULONG) assert(false, "Expected a ULONG, got "
				    ~ _type.to!string);
    return _ulong;
  }

  // ~this() {
  //   import std.stdio;
  //   if (_type == Type.BOOLEXPR) {
  //     writeln("BuddyTerm Destroying: ", _index, " id: ", _id, " type: ", _type, " BDD: ", _boolExpr._index);
  //   }
    
  //   if (_type == Type.BVEXPR) {
  //     writeln("BuddyTerm Destroying: ", _index, " id: ", _id, " type: ", _type, " BddVec: ", _bvExpr.bitvec);
  //   }
  // }

  // @disable this(this);
  // workaround for https://issues.dlang.org/show_bug.cgi?id=20876

  this(this) {
    this.addRef();
  }

  // this(ref BuddyTerm other) {
  //   _boolExpr = other._boolExpr;
  //   _bvExpr = other._bvExpr;
  //   _ulong = other._ulong;
  //   _type = other._type;
  // }

  ref BuddyTerm opAssign(ref BuddyTerm other) return {
    this.delRef();
    _boolExpr = other._boolExpr;
    _bvExpr = other._bvExpr;
    _ulong = other._ulong;
    _buddy = other._buddy;
    _type = other._type;
    this.addRef();
    return this;
  }

  this(ref BddVec expr, Buddy buddy) {
    _bvExpr = expr;
    _type = Type.BVEXPR;
    _buddy = buddy;
    this.addRef();
  }

  this(BddVec expr, Buddy buddy) {
    _bvExpr = expr;
    _type = Type.BVEXPR;
    _buddy = buddy;
    this.addRef();
  }

  this(ref BDD expr, Buddy buddy) {
    this.delRef();
    _boolExpr = expr;
    _type = Type.BOOLEXPR;
    _buddy = buddy;
    this.addRef();
  }

  this(BDD expr, Buddy buddy) {
    this.delRef();
    _boolExpr = expr;
    _type = Type.BOOLEXPR;
    _buddy = buddy;
    this.addRef();
  }

  this(ulong expr, Buddy buddy) {
    this.delRef();
    _ulong = expr;
    _type = Type.ULONG;
    _buddy = buddy;
    this.addRef();
  }

  string toString() {
    import std.string: format;
    string str;
    final switch (_type) {
    case Type.INVALID: 
      str = format("type: %s", _type);
      break;
    case Type.ULONG:
      str = format("type: %s, val: %s", _type, _ulong);
      break;
    case Type.BVEXPR:
      str = format("type: %s, val: %s", _type, _bvExpr.bitvec);
      break;
    case Type.BOOLEXPR:
      str = format("type: %s, val: %s", _type, _boolExpr);
      break;
    }
    return str;
  }
}

struct BuddyRndDomain
{
  enum Type: ubyte { BOOLEXPR, BVEXPR }

  Type   _type;

  bddvec _bvDom;
  bdd    _boolDom;

  Buddy  _buddy;

  // alias _bvDom this;
  
  this(BddVec dom, Buddy buddy) {
    _bvDom = dom;
    _buddy = buddy;
    _type = Type.BVEXPR;
    this.addRef();
  }

  this(BDD dom, Buddy buddy) {
    _boolDom = dom;
    _buddy = buddy;
    _type = Type.BOOLEXPR;
    this.addRef();
  }

  void delRef() {
    final switch (_type) {
    case Type.BOOLEXPR: _buddy.delRef(_boolDom); break;
    case Type.BVEXPR: _buddy.delRef(_bvDom); break;
    }
  }
  
  void addRef() {
    final switch (_type) {
    case Type.BOOLEXPR: _buddy.addRef(_boolDom); break;
    case Type.BVEXPR: _buddy.addRef(_bvDom); break;
    }
  }
  
  void print() {
    import std.stdio;
    writeln(_bvDom.bitvec);
    writeln(_boolDom);
  }
  
  BddVec toBv() return {
    import std.conv: to;
    if (_type != Type.BVEXPR) assert(false, "Expected a BVEXPR, got "
				     ~ _type.to!string);
    return BddVec(_bvDom);
  }

  BDD toBool() return {
    import std.conv: to;
    if (_type != Type.BOOLEXPR) assert(false, "Expected a BOOLEXPR, got "
				       ~ _type.to!string);
    return BDD(_boolDom, _buddy);
  }

  // ~this() {
  //   print();
  // }

}

struct BuddyVarDomain
{
  enum Type: ubyte { BOOLEXPR, BVEXPR }

  enum State: ubyte {INIT, CONST, VAR}

  Type   _type;

  bddvec _bvDom;
  bdd    _boolDom;

  Buddy  _buddy;

  long   _bvVal;
  bool   _boolVal;
  
  State  _state;

  // alias _bvDom this;
  
  this(BddVec dom, Buddy buddy) {
    _bvDom = dom;
    _bvVal = 0;
    _type = Type.BVEXPR;
    _state = State.INIT;
    _buddy = buddy;
    this.addRef();
  }

  this(BDD dom, Buddy buddy) {
    _boolDom = dom;
    _boolVal = false;
    _type = Type.BOOLEXPR;
    _state = State.INIT;
    _buddy = buddy;
    this.addRef();
  }

  void delRef() {
    final switch (_type) {
    case Type.BOOLEXPR: _buddy.delRef(_boolDom); break;
    case Type.BVEXPR: _buddy.delRef(_bvDom); break;
    }
  }
  
  void addRef() {
    final switch (_type) {
    case Type.BOOLEXPR: _buddy.addRef(_boolDom); break;
    case Type.BVEXPR: _buddy.addRef(_bvDom); break;
    }
  }
  
  BddVec getBvValExpr() {
    assert (_type == Type.BVEXPR);
    return _bvDom._buddy.buildVec(_bvDom.length, _bvVal, _bvDom.signed());
  }

  BDD getBoolValExpr() {
    assert (_type == Type.BOOLEXPR);
    if (_boolVal) return _buddy.one();
    else          return _buddy.zero();
  }

  BDD getRule() {
    if (_type == Type.BVEXPR) {
      return BddVec(_bvDom).equ(getBvValExpr());
    }
    else {
      return BDD(_boolDom, _buddy).biimp(getBoolValExpr());
    }
  }
  
  void update(CstDomBase dom, CstBuddySolver solver) {
    assert (dom.isSolved());
    bool updated = false;

    if (dom.isBool()) {
      bool val = dom.getBool();
      if (_boolVal != val) {
	_boolVal = val;
	updated = true;
      }
    }
    else {
      long val = dom.value();
      if (_bvVal != val) {
	_bvVal = val;
	updated = true;
      }
    }
    
    if (updated) {
      final switch (_state) {
      case State.INIT:
	_state = State.CONST;
	solver._count0 += 1;
	break;
      case State.CONST:
	_state = State.VAR;
	solver._count0 -= 1;
	solver._count1 += 1;
	break;
      case State.VAR:
	solver._refreshVar = true;
	break;
      }
    }
    else {
      final switch (_state) {
      case State.INIT:
	_state = State.CONST;
	solver._count0 += 1;
	break;
      case State.CONST:
	break;
      case State.VAR:
	break;
      }
    }
  }
}

class CstBuddySolver: CstSolver
{
  Buddy _esdl__buddy;

  BuddyTerm[] _evalStack;

  BuddyTerm _term;		// for inside constraint processing

  BuddyRndDomain[] _domains;
  BuddyVarDomain[] _variables;

  BuddyContext _context;

  _esdl__Proxy _proxy;

  void print() {
    import std.stdio;
    writeln("CstBuddySolver:");
    writeln("_evalStack: ", _evalStack.length);
    _term.print();
    writeln("_domains: ", _domains.length);
    foreach (dom; _domains) {
      dom.print();
    }
    writeln("_variables: ", _variables.length);
  }

  // ~this() {
  //   print();
  // }
  
  uint _count0;
  uint _count1;

  // whether some variables have changed and a refresh required
  bool _refreshVar;	    // whether the variable values need refresh
  ubyte _pushCount;	    // balance number of pushed z3 context has


  Buddy buddy() {
    if (_esdl__buddy is null) {
      _esdl__buddy = new Buddy(1000, 1000);
    }
    return _esdl__buddy;
  }


  this(string signature, CstSolverAgent agent) {
    Buddy.enableBddGC();

    super(signature);

    _proxy = agent.getProxy();

    if (_esdl__buddy is null) {
      _esdl__buddy = new Buddy(1000, 1000);
    }

    _context = new BuddyContext(_esdl__buddy);

    CstDomBase[] doms = agent.annotatedDoms();

    _domains.length = doms.length;

    foreach (i, ref dom; _domains) {
      // import std.stdio;
      // writeln("Adding Buddy Domain for @rand ", doms[i].name(), " of size: ", doms[i].bitcount);
      if (doms[i].isBool()) {
	auto d = _context._buddy.createDomain(); // , doms[i].bitcount, doms[i].signed());
	dom = BuddyRndDomain(d, _esdl__buddy);
      }
      else {
	auto d = _esdl__buddy.createDomVec(doms[i].bitcount, doms[i].signed());
	dom = BuddyRndDomain(d, _esdl__buddy);
      }
    }

    CstDomBase[] vars = agent.annotatedVars();
    _variables.length = vars.length;

    foreach (i, ref var; _variables) {
      // import std.stdio;
      // writeln("Adding Buddy Domain for variable ", vars[i].name(), " of length: ", vars[i].bitcount);
      if (vars[i].isBool()) {
	auto d = _esdl__buddy.createDomain();
	var = BuddyVarDomain(d, _esdl__buddy);
      }
      else {
	auto d = _esdl__buddy.createDomVec(vars[i].bitcount, vars[i].signed());
	var = BuddyVarDomain(d, _esdl__buddy);
      }
    }

    foreach (dom; doms) {
      if (dom.visitDomain(this)) {
	assert(_evalStack.length == 1);
	_context.addRule(_evalStack[0].toBool());
	_evalStack.length = 0;
      }
    }

    foreach (pred; agent.predicates()) {
      // import std.stdio;
      // writeln("Buddy Working on: ", pred.name());
      // if (pred.agent() !is agent) {
      // 	assert (false, "Solver Violation " ~ pred.name());
      // }
      assert (! pred.isGuard());
      // import std.stdio;
      // writeln(pred.describe());
      pred.visit(this);
      _context.addRule(_evalStack[0].toBool());
      popEvalStack();
      assert(_evalStack.length == 0);
      // writeln("We are here too");
      // _evalStack.length = 0;
    }

    this.push();

  }

  override string describe() {
    return "OBDD Solver\n" ~ super.describe();
  }

  BuddyVarDomain.State varState;

  void push() {
    assert(_pushCount <= 2);
    _pushCount += 1;
    _context.push();
  }

  void pop() {
    assert(_pushCount >= 0);
    _pushCount -= 1;
    _context.pop();
  }

  override bool solve(CstSolverAgent agent) {
    Buddy.enableBddGC();
    
    CstDomBase[] doms = agent.annotatedDoms();
    updateVars(agent);
    _context.updateDist();

    ubvec!MAXBDDLEVELS vec;

    vec = _proxy._esdl__rGen.gen!(ubvec!MAXBDDLEVELS);

    uint sol = _context.getBDD().getRandSat(vec, _proxy._esdl__rGen.get(),
					    _context._bddDist);
    // import std.stdio;
    // writeln (vec);

    // BDD solution = _context.getBDD().randSatOne(_proxy._esdl__rGen.get(),
    // 						_context._bddDist);
    // byte[][] solVecs = solution.toVector();

    // byte[] bits;
    // if (solVecs.length != 0) {
    //   bits = solVecs[0];
    // }
    
    foreach (n, ref dom; doms) {
      auto bitindices = _context.getBDD().getIndices(cast(uint) n);

      if (dom.isBool()) {
	assert (bitindices.length == 1);
	int index = bitindices[0];
	dom.setBool(vec[index]);
	// if (bits.length == 0 || bits[index] == -1) {
	//   dom.setBool(_proxy._esdl__rGen.flip());
	// }
	// else {
	//   dom.setBool(bits[index] == 1);
	// }
      }
      else {
	ulong v;
	ulong[MAXBDDLEVELS/64] _solveValue;	// max bdd level MAXBDDLEVELS
  

	enum WORDSIZE = 8 * v.sizeof;

	auto NUMWORDS = (bitindices.length+WORDSIZE-1)/WORDSIZE;
	assert (NUMWORDS <= 2);
      
	foreach (i, ref j; bitindices) {
	  uint pos = (cast(uint) i) % WORDSIZE;
	  uint word = (cast(uint) i) / WORDSIZE;
	  v = v + ((vec[j] ? 1UL : 0UL) << pos);
	  // if (bits.length == 0 || bits[j] == -1) {
	  //   v = v + ((cast(size_t) _proxy._esdl__rGen.flip()) << pos);
	  // }
	  // else if (bits[j] == 1) {
	  //   v = v + ((cast(ulong) 1) << pos);
	  // }
	  if (pos == WORDSIZE - 1 || i == bitindices.length - 1) {
	    _solveValue[word] = v;
	    v = 0;
	  }
	}
	
	dom.setVal(array(_solveValue[0..NUMWORDS]));
      }
    }
    // _context.print();
    // this.print();
    Buddy.disableBddGC();
    return true;
  }
  
  void updateVars(CstSolverAgent agent) {
    CstDomBase[] vars = agent.annotatedVars();
    _refreshVar = false;
    uint pcount0 = _count0;
    uint pcount1 = _count1;
    foreach (i, ref var; _variables) var.update(vars[i], this);
    assert (_count0 + _count1 == _variables.length);
    // import std.stdio;
    // writeln("refresh: ", _refreshVar,
    // 	    " prev counts: ", pcount0, ", ", pcount1,
    // 	    " now counts: ", _count0, ", ", _count1);

    if (_refreshVar || (pcount1 != 0 && pcount1 != _count1))
      pop();			// for variables
    if (pcount0 != 0 && pcount0 != _count0)
      pop();			// for constants

    // process constants -- if required
    if (pcount0 != _count0 && _count0 > 0) {
      push();
      foreach (i, ref var; _variables) {
	if (var._state == BuddyVarDomain.State.CONST)
	  _context.addRule(var.getRule());
      }
    }
    if (_refreshVar || pcount1 != _count1) {
      push();
      foreach (i, ref var; _variables) {
	if (var._state == BuddyVarDomain.State.VAR)
	  _context.addRule(var.getRule());
      }
    }
  }

  override void pushToEvalStack(CstDomBase domain) {
    uint n = domain.annotation();
    // writeln("push: ", domain.name(), " annotation: ", n);
    // writeln("_domains has a length: ", _domains.length);
    if (domain.isSolved()) { // is a variable
      if (domain.isBool()) pushToEvalStack(BDD(_variables[n]._boolDom, _esdl__buddy));
      else                 pushToEvalStack(BddVec(_variables[n]._bvDom));
    }
    else {
      BuddyRndDomain dom = _domains[n];
      if (dom._type == BuddyRndDomain.Type.BVEXPR)
	pushToEvalStack(dom.toBv());
      else
	pushToEvalStack(dom.toBool());
    }
  }

  override void pushToEvalStack(CstVecValueBase value) {
    // writeln("push: value ", value.value());
    BddVec v = _esdl__buddy.buildVec(value.bitcount(),
				     value.value(), value.signed);
    pushToEvalStack(v);
  }

  override void pushToEvalStack(ulong value, uint bitcount, bool signed) {
    BddVec v = _esdl__buddy.buildVec(bitcount, value, signed);
    pushToEvalStack(v);
  }

  override void pushToEvalStack(bool value) {
    // writeln("push: ", value);
    if (value) {
      BuddyTerm e = BuddyTerm(BDD(BddTrue, _esdl__buddy), _esdl__buddy);
      pushToEvalStack(e);
    }
    else {
      BuddyTerm e = BuddyTerm(BDD(BddFalse, _esdl__buddy), _esdl__buddy);
      pushToEvalStack(e);
    }
  }

  override void pushIndexToEvalStack(ulong value) {
    // writeln("push: ", value);
    BuddyTerm e = BuddyTerm(value, _esdl__buddy);
    pushToEvalStack(e);
  }

  override void processEvalStack(CstUnaryOp op) {
    // writeln("eval: CstUnaryOp ", op);
    final switch (op) {
    case CstUnaryOp.NOT:
      BddVec e = ~ (_evalStack[$-1].toBv());
      popEvalStack();
      // _evalStack.length = _evalStack.length - 1;
      pushToEvalStack(e);
      break;
    case CstUnaryOp.NEG:
      BddVec e = - (_evalStack[$-1].toBv());
      popEvalStack();
      // _evalStack.length = _evalStack.length - 1;
      pushToEvalStack(e);
      break;
    }
  }
  override void processEvalStack(CstBinaryOp op) {
    // writeln("eval: CstBinaryOp ", op);
    final switch (op) {
    case CstBinaryOp.AND:
      BddVec e = _evalStack[$-2].toBv() & _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.OR:
      BddVec e = _evalStack[$-2].toBv() | _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.XOR:
      BddVec e = _evalStack[$-2].toBv() ^ _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.ADD:
      BddVec e = _evalStack[$-2].toBv() + _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.SUB:
      BddVec e = _evalStack[$-2].toBv() - _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.MUL:
      BddVec e = _evalStack[$-2].toBv() * _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.DIV:
      BddVec e = _evalStack[$-2].toBv() / _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.REM:
      BddVec e = _evalStack[$-2].toBv() % _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.LSH:
      BddVec e = _evalStack[$-2].toBv() << _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.RSH:			// Arith shift right ">>"
      BddVec e = _evalStack[$-2].toBv() >> _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstBinaryOp.LRSH:			// Logic shift right ">>>"
      BddVec e = _evalStack[$-2].toBv() >>> _evalStack[$-1].toBv();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstCompareOp op) {
    // writeln("eval: CstCompareOp ", op);
    final switch (op) {
    case CstCompareOp.LTH:
      BDD e = _evalStack[$-2].toBv().lth(_evalStack[$-1].toBv());
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstCompareOp.LTE:
      BDD e = _evalStack[$-2].toBv().lte(_evalStack[$-1].toBv());
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstCompareOp.GTH:
      BDD e = _evalStack[$-2].toBv().gth(_evalStack[$-1].toBv());
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstCompareOp.GTE:
      BDD e = _evalStack[$-2].toBv().gte(_evalStack[$-1].toBv());
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstCompareOp.EQU:
      BDD e = _evalStack[$-2].toBv().equ(_evalStack[$-1].toBv());
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstCompareOp.NEQ:
      BDD e = _evalStack[$-2].toBv().neq(_evalStack[$-1].toBv());
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    }
  }
  override void processEvalStack(CstLogicOp op) {
    // writeln("eval: CstLogicOp ", op);
    final switch (op) {
    case CstLogicOp.LOGICAND:
      BDD e = _evalStack[$-2].toBool() & _evalStack[$-1].toBool();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICOR:
      BDD e = _evalStack[$-2].toBool() | _evalStack[$-1].toBool();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICIMP:
      BDD e = _evalStack[$-2].toBool() >> _evalStack[$-1].toBool();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICNOT:
      BDD e = ~ _evalStack[$-1].toBool();
      popEvalStack();
      // _evalStack.length = _evalStack.length - 1;
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICEQ:
      BDD e = _evalStack[$-2].toBool().biimp(_evalStack[$-1].toBool());
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    case CstLogicOp.LOGICNEQ:
      BDD e = _evalStack[$-2].toBool() ^ _evalStack[$-1].toBool();
      popEvalStack(2);
      // _evalStack.length = _evalStack.length - 2;
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstSliceOp op) {
    final switch (op) {
    case CstSliceOp.SLICE:
      BddVec e = _evalStack[$-3].toBv()[cast(uint) _evalStack[$-2].toUlong() ..
					cast(uint) _evalStack[$-1].toUlong()];
      popEvalStack(3);
      // _evalStack.length = _evalStack.length - 3;
      pushToEvalStack(e);
      break;
    case CstSliceOp.SLICEINC:
      BddVec e = _evalStack[$-3].toBv()[cast(uint) _evalStack[$-2].toUlong() ..
					cast(uint) _evalStack[$-1].toUlong() + 1];
      popEvalStack(3);
      // _evalStack.length = _evalStack.length - 3;
      pushToEvalStack(e);
      break;
    }
  }

  override void processEvalStack(CstVectorOp op) {
    assert (false, "CstVectorOp is handled only by SMT solvers");
  }

  override void processEvalStack(CstInsideOp op) {
    final switch (op) {
    case CstInsideOp.INSIDE:
      _term = _evalStack[$-1];
      popEvalStack();
      break;
    case CstInsideOp.EQUAL:
      BDD e = _term.toBv().equ(_evalStack[$-1].toBv());
      popEvalStack();
      pushToEvalStack(e);
      processEvalStack(CstLogicOp.LOGICOR);
      break;
    case CstInsideOp.RANGE:
      BDD upper = _term.toBv().lth(_evalStack[$-1].toBv());
      BDD lower = _term.toBv().gte(_evalStack[$-2].toBv());
      popEvalStack(2);
      pushToEvalStack(upper);
      pushToEvalStack(lower);
      processEvalStack(CstLogicOp.LOGICAND);
      processEvalStack(CstLogicOp.LOGICOR);
      break;
    case CstInsideOp.RANGEINCL:
      BDD upper = _term.toBv().lte(_evalStack[$-1].toBv());
      BDD lower = _term.toBv().gte(_evalStack[$-2].toBv());
      popEvalStack(2);
      pushToEvalStack(upper);
      pushToEvalStack(lower);
      processEvalStack(CstLogicOp.LOGICAND);
      processEvalStack(CstLogicOp.LOGICOR);
      break;
    case CstInsideOp.DONE:
      BuddyTerm init;
      _term = init;
      break;
    }
  }

  override void processEvalStack(CstUniqueOp op) {
    assert(false, "TBD");
  }

  void popEvalStack(uint count=1) {
    assert (_evalStack.length >= count);
    for (size_t i=0; i!=count; ++i) {
      _evalStack[$-1-i].delRef();
      _evalStack[$-1-i]._type = BuddyTerm.Type.INVALID;
    }
    _evalStack.length = _evalStack.length - count;
    // for (size_t i=0; i!=count; ++i) {
    //   // BuddyTerm invalid = BuddyTerm();
    //   // _evalStack[$-1] = invalid;
    //   _evalStack.length = _evalStack.length - 1;
    // }
    // writeln("After POP _evalStack is of size: ", _evalStack.length);
  }

  void pushToEvalStack(ref BddVec vec) {
    BuddyTerm term = BuddyTerm(vec, _esdl__buddy);
    pushToEvalStack(term);
  }
  
  void pushToEvalStack(ref BDD b) {
    BuddyTerm term = BuddyTerm(b, _esdl__buddy);
    pushToEvalStack(term);
  }  

  void pushToEvalStack(ref BuddyTerm term) {
    // writeln("Pushing on _evalStack: ", term.toString());
    _evalStack ~= term;
    // writeln("After PUSH _evalStack is of size: ", _evalStack.length);
  }
    
  void pushToEvalStack(BddVec vec) {
    BuddyTerm term = BuddyTerm(vec, _esdl__buddy);
    pushToEvalStack(term);
  }
  
  void pushToEvalStack(BDD b) {
    BuddyTerm term = BuddyTerm(b, _esdl__buddy);
    pushToEvalStack(term);
  }  

  void pushToEvalStack(BuddyTerm term) {
    // writeln("Pushing on _evalStack: ", term.toString());
    _evalStack ~= term;
    // writeln("After PUSH _evalStack is of size: ", _evalStack.length);
  }
    
}
