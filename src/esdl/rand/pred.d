module esdl.rand.pred;

import std.algorithm;
import std.array;
import std.container.array;

import esdl.data.folder;
import esdl.data.charbuf;
import esdl.rand.proxy: _esdl__Proxy, _esdl__ConstraintBase;
import esdl.rand.misc;
import esdl.rand.base: CstDomBase, CstDomSet, CstIterCallback, DomType,
  CstDepCallback, CstScope, CstIterator, CstVecNodeIntf,
  CstVecTerm, CstLogicTerm, CstDepIntf;
import esdl.rand.base: CstValue, CstVarNodeIntf;

import esdl.solver.base;
import esdl.solver.mono: CstMonoSolver;
import esdl.solver.z3: CstZ3Solver;
import esdl.solver.buddy: CstBuddySolver;
import esdl.rand.vecx: CstVector, CstVecArr;
import esdl.rand.domain: CstArrLength;

struct Hash
{
  size_t hash;
  
  this (size_t h) nothrow {
    hash = h;
  }
  
  enum uint m = 0x5bd1e995;
  enum uint r = 24;
  void modify (uint c){
    uint k = c * m;
    k ^= k >> r;
    hash = (hash * m) ^ (k * m);
  }
  void modify (string s){
    modify(calcHash(s));
  }

  uint calcHash(scope const(char)[] data) @nogc nothrow pure @safe
  {
    return calcHash(cast(const(ubyte)[])data);
  }
  
  uint calcHash(scope const(ubyte)[] data) @nogc nothrow pure @safe
  {
    uint h = cast(uint) data.length;
    while (data.length >= 4)
      {
        uint k = data[3] << 24 | data[2] << 16 | data[1] << 8 | data[0];
        k *= m;
        k ^= k >> r;
        h = (h * m) ^ (k * m);
        data = data[4..$];
      }
    switch (data.length & 3)
      {
      case 3:
        h ^= data[2] << 16;
        goto case;
      case 2:
        h ^= data[1] << 8;
        goto case;
      case 1:
        h ^= data[0];
        h *= m;
        goto default;
      default:
        break;
      }
    h ^= h >> 13;
    h *= m;
    h ^= h >> 15;
    return h;
  }
}

// hash map number keys

// tried to use ascii where possible

// ! -> 33
// : -> 58
// >> -> > -> 62
// ( -> 40
// ) -> 41
//   -> 32
// .. -> . -> 46
// DIST -> d -> 100
// [ -> 91
// ] -> 93
// NOT -> N -> 78
// NEG -> ~ -> 126
// ! INSIDE -> \ -> 92
// INSIDE -> / -> 47
// UNIQUE -> u -> 117
// Visitor: -> v -> 118
// := -> @ -> 64
// :/ -> * -> 42
// V -> 86
// R -> 82
// # -> 35
// U -> 85
// S -> 83
// bool -> 0



class CstPredGroup			// group of related predicates
{
  __gshared uint _count;
  immutable uint _id;

  // solve cycle for which this group is getting processed. If this
  // _cycle matches solver _cycle, that would mean this group is
  // already processed
  uint _cycle;

  bool _hasSoftConstraints;
  bool _hasVectorConstraints;
  bool _hasUniqueConstraints;
  bool _hasDistContraints;

  bool hasSoftConstraints() {
    return _hasSoftConstraints;
  }

  bool hasVectorConstraints() {
    return _hasVectorConstraints;
  }
  
  bool hasUniqueConstraints() {
    return _hasUniqueConstraints;
  }
  
  bool hasDistConstraints() {
    return _hasDistContraints;
  }

  void markDist() {
    _hasDistContraints = true;
    _state = State.NEEDSYNC;	// mark that we need to reassign a solver
  }
  // List of predicates permanently in this group
  Folder!(CstPredicate, "preds") _preds;
  Folder!(CstPredicate, "guards") _guards;
  Folder!(CstPredicate, "dynPreds") _dynPreds;

  CstPredicate _distPred;

  Folder!(CstPredicate, "predList") _predList;
  Folder!(CstPredicate, "guardList") _guardList;
  Folder!(CstPredicate, "dynPredList") _dynPredList;

  CstPredicate[] predicates() {
    return _preds[];
  }

  _esdl__Proxy _proxy;
  
  this(_esdl__Proxy proxy) {
    _proxy = proxy;
    synchronized (typeid(CstPredGroup)) {
      _id = _count++;
    }
  }

  _esdl__Proxy getProxy() {
    return _proxy;
  }

  void addPredicate(CstPredicate pred) {
    _predList ~= pred;
  }

  void addGuard(CstPredicate pred) {
    _guardList ~= pred;
  }

  void addDynPredicate(CstPredicate pred) {
    _dynPredList ~= pred;
  }

  // The flag _hasDynamicBinding gets set if there is at least one
  // predicate that has a dynamically resolvable constraint --
  // typically that would mean a random variable dependancy as part of index 
  bool _hasDynamicBinding;

  Folder!(CstDomBase, "doms") _doms;
  uint addDomain(CstDomBase dom) {
    uint index = cast (uint) _doms.length;
    _doms ~= dom;
    return index;
  }

  CstDomBase[] domains() {
    return _doms[];
  }
  
  Folder!(CstDomSet, "domArrs") _domArrs;
  void addDomainArr(CstDomSet domArr) {
    _domArrs ~= domArr;
  }

  CstDomSet[] domainArrs() {
    return _domArrs[];
  }
  
  Folder!(CstDomBase, "vars") _vars;
  uint addVariable(CstDomBase var) {
    uint index = cast (uint) _vars.length;
    _vars ~= var;
    return index;
  }

  CstDomBase[] variables() {
    return _vars[];
  }

  Folder!(CstDomSet, "varArrs") _varArrs;
  void addVariableArr(CstDomSet varArr) {
    _varArrs ~= varArr;
  }

  // If there are groups that are related. This will only be true if
  // the _hasDynamicBinding flag is true
  Folder!(CstPredGroup, "boundGroups") _boundGroups;

  void setGroupContext(CstPredicate solvablePred, uint level) {
    import std.algorithm.sorting: sort; 
    
    solvablePred.setGroupContext(this, level);

    setOrderAndBools();
  }

  void setOrderAndBools(){
    
    _hasSoftConstraints = false;
    _hasVectorConstraints = false;
    _hasUniqueConstraints = false;
    _hasDistContraints = false;

    _state = State.NEEDSYNC;	// mark that we need to reassign a solver

    foreach (pred; _preds) pred._group = null;
    _preds.reset();
    foreach (pred; sort!((x, y) => x.name() < y.name())(_predList[])) {
      if (pred.withDist()) this.markDist();
      pred._group = this;
      if (pred._soft != 0) _hasSoftConstraints = true;
      if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
      if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
      _preds ~= pred;
    }
    foreach (pred; _guards) pred._group = null;
    _guards.reset();
    foreach (pred; sort!((x, y) => x.name() < y.name())(_guardList[])) {
      pred._group = this;
      _guards ~= pred;
    }
    foreach (pred; _dynPreds) pred._group = null;
    _dynPreds.reset();
    foreach (pred; sort!((x, y) => x.name() < y.name())(_dynPredList[])) {
      pred._group = this;
      if (pred._soft != 0) _hasSoftConstraints = true;
      if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
      if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
      _dynPreds ~= pred;
    }
    if (_distPred !is null) _distPred._group = this;
    
    // for the next cycle
    _predList.reset();
    _guardList.reset();
    _dynPredList.reset();
    
  }

  void setAnnotation() {
    foreach (i, dom; _doms) {
      assert (dom !is null);
      dom.setAnnotation(cast(uint) i);
    }
    foreach (i, dom; _vars) {
      assert (dom !is null);
      dom.setAnnotation(cast(uint) i);
    }
  }

  void annotate() {
    _doms.reset();
    _vars.reset();

    if (_distPred !is null) _distPred.annotate(this);
    foreach (pred; _preds) pred.annotate(this);
  }

  static Charbuf _sig;
  
  string signature() {
    _sig.reset();
    _sig ~= "GROUP:\n";
    foreach (pred; _preds) {
      if (! hasDistConstraints || pred.isGuardEnabled())
	pred.writeSignature(_sig);
    }
    return _sig.toString();
  }

  override size_t toHash() @trusted nothrow {
    import std.exception:assumeWontThrow;
    return assumeWontThrow(getHash());
  }
  
  bool _hasHashBeenCalculated = false;
  
  Hash _hash;
  
  size_t getHash(){
    if (_hasHashBeenCalculated){
      return _hash.hash;
    }
    _hash = Hash(cast(uint) _preds.length);
    foreach (pred; _preds){
      if (! hasDistConstraints || pred.isGuardEnabled())
	pred.calcHash(_hash);
    }
    return _hash.hash;
  }

  public enum State: ubyte
  {   INIT,
      NEEDSYNC,
      SOLVED
      }

  State _state;
  
  void reset() {
    _state = State.INIT;

    if (_distPred !is null) {
      // _distPred.reset;
      _distPred = null;
    }

    // Now handled in proxy
    // foreach (pred; _preds) pred.reset();
  }

  void needSync() {
    _state = State.NEEDSYNC;
  }

  void markSolved() {
    _state = State.SOLVED;
  }

  bool isSolved() {
    return _state == State.SOLVED;
  }

  CstSolver _solver;

  void solve() {
    // import std.stdio;
    // writeln("Solving: ", this.describe());
    if (_proxy._esdl__debugSolver()) {
      import std.stdio;
      writeln(describe());
    }

    if (_distPred is null || (! _distPred.distDomain().isRand())) {
      if (_state is State.NEEDSYNC) {
	annotate();
	string sig = signature();

	if (_proxy._esdl__debugSolver()) {
	  import std.stdio;
	  writeln(sig);
	}

	CstSolver* solverp = sig in _proxy._solvers;
	// _hasHashBeenCalculated = false;
	// CstSolver* solverp = this in _proxy._solvers;

	if (solverp !is null) {
	  _solver = *solverp;
	  _solver.solve(this);
	}
	else {
	  if (_hasSoftConstraints || _hasVectorConstraints) {
	    if (_proxy._esdl__debugSolver()) {
	      import std.stdio;
	      writeln("Invoking Z3 because of Soft/Vector Constraints");
	      writeln("_preds: ", _preds[]);
	      foreach (pred; _preds) {
		writeln(pred.describe());
	      }
	      writeln(describe());
	    }
	    _solver = new CstZ3Solver(sig, this);
	    _solver.solve(this);
	  }
	  else {
	    bool monoFlag = false;
	    if (_preds.length == 1 && _preds[0].isVisitor()) {
	      // _preds[0]._dom.forceResolve(_proxy);
	      _preds[0]._state = CstPredicate.State.SOLVED;
	      _proxy.addSolvedDomain(_preds[0]._dom);
	      monoFlag = true;
	    }
	    else if (_doms.length == 1 && (! _doms[0].isBool())) {
	      if (_doms[0].bitcount() < 32) {
		_solver = new CstMonoSolver!int(sig, this);
	      }
	      else if (_doms[0].bitcount == 32) {
		if(_doms[0].signed()) {
		  _solver = new CstMonoSolver!int(sig, this);
		}
		else{
		  _solver = new CstMonoSolver!uint(sig, this);
		}
	      }
	      else if (_doms[0].bitcount < 64) {
		_solver = new CstMonoSolver!long(sig, this);
	      }
	      else if (_doms[0].bitcount == 64) {
		if(_doms[0].signed()) {
		  _solver = new CstMonoSolver!long(sig, this);
		}
		else {
		  _solver = new CstMonoSolver!ulong(sig, this);
		}
	      }
	      if ( _solver !is null ) {
		monoFlag = _solver.solve(this);
	      }
	    }
	    if (! monoFlag) {
	      uint totalBits;
	      uint domBits;
	      foreach (dom; _doms) {
		// assert (! dom.isProperDist());
		uint domBC = dom.bitcount();
		totalBits += domBC;
		domBits += domBC;
	      }
	      foreach (var; _vars) totalBits += var.bitcount();
	      if (totalBits > 32 || _hasUniqueConstraints) {
		if (_proxy._esdl__debugSolver()) {
		  import std.stdio;
		  writeln("Invoking Z3 because of > 32 bits");
		  writeln(describe());
		}
		_solver = new CstZ3Solver(sig, this);
		_solver.solve(this);
	      }
	      else {
		_solver = new CstBuddySolver(sig, this);
		_solver.solve(this);
	      }
	    }
	  }
	  // _hasHashBeenCalculated = true;
	  // if (_solver !is null) _proxy._solvers[this] = _solver;
	  if (_solver !is null) _proxy._solvers[sig] = _solver;
	}
      }
      else {
	// import std.stdio;
	// writeln(_solver.describe());
	// writeln("We are here");
	setAnnotation();
	if (_solver !is null) _solver.solve(this);
      }
      // import std.stdio;
      // writeln(_solver.describe());
      // _solver.solve(this);
      foreach (pred; _preds) {
	// import std.stdio;
	// writeln("Marking Solved: ", pred.name());
	pred.markPredSolved();
      }
    }
    else {
      assert (_distPred.isGuardEnabled());
      CstDistSolverBase dist = _distPred._expr.getDist();
      CstDomBase distDomain = _distPred.distDomain();
      dist.reset();
      foreach (wp; _preds) {
	if (wp.isGuardEnabled()) {
	  // import std.stdio;
	  // writeln(wp.describe());
	  bool compat = wp._expr.isCompatWithDist(distDomain);
	  if (compat is false) assert (false, "can only use != operator on distributed domains");
	  wp._expr.visit(dist);
	  wp.markPredSolved();
	}
	else {
	  wp.markPredSolved();
	}
      }
      dist.uniform(distDomain, _proxy._esdl__getRandGen());
      _proxy.addSolvedDomain(distDomain);
      _distPred.markPredSolved();
    }


    foreach (guard; _guards) {
      if (! guard.tryResolve(_proxy)) {
	assert (false, "Unresolved Guard: " ~ guard.name());
      }
      // else {
      // 	import std.stdio;
      // 	writeln("Resolved Guard: ", guard.name());
      // }
    }
    this.markSolved();

    foreach (dom; _doms) dom.setAnnotation(uint.max);
    foreach (dom; _vars) dom.setAnnotation(uint.max);
    
  }
      

  string describe() {
    import std.conv: to;
    string description = "CstPredGroup Id: " ~ _id.to!string() ~ '\n';
    if (_preds.length > 0) {
      description ~= "  Predicates:\n";
      foreach (pred; _preds) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_distPred !is null) {
      description ~= "  Dist Predicate:\n";
      description ~= "    " ~ _distPred.name() ~ '\n';
    }
    if (_guards.length > 0) {
      description ~= "  Guards:\n";
      foreach (pred; _guards) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_dynPreds.length > 0) {
      description ~= "  Dynamic Predicates:\n";
      foreach (pred; _dynPreds) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_hasSoftConstraints) {
      description ~= "  Has Soft Constraints: True\n";
    }
    else {
      description ~= "  Has Soft Constraints: False\n";
    }
    return description;
  }
}

class CstPredicate: CstIterCallback, CstDepCallback, CstDepIntf
{
  string name() {
    import std.conv;
    if (_parent is null) {
      return _constraint.fullName() ~ '/' ~
	(_isGuard ? "guard_" : "pred_") ~
	_statement.to!string() ~ '%' ~ _id.to!string();
    }
    else {
      return _parent.name() ~
	'[' ~ _unrollIterVal.to!string() ~ ']' ~'%' ~ _id.to!string();
    }
  }

  string fullName() {
    return name();
  }

  bool isVisitor() {
    return false;
  }

  void visit(CstSolver solver, bool inv=false) {
    if (_guard is null) {
      _expr.visit(solver);
      if (inv) solver.processEvalStack(CstLogicOp.LOGICNOT);
    }
    else {
      assert (this.isGuard() || inv is false);
      _guard.visit(solver, _guardInv);
      _expr.visit(solver);
      if (inv) solver.processEvalStack(CstLogicOp.LOGICNOT);
      if (this.isGuard()) solver.processEvalStack(CstLogicOp.LOGICAND);
      else                solver.processEvalStack(CstLogicOp.LOGICIMP);
    }
  }
  // alias _expr this;

  enum State: byte { INIT, UNROLLED, COLLATED, DISABLED, GROUPED, SOLVED }

  bool isUnrolled() {
    return _state == State.UNROLLED;
  }


  void hasDistDomain(bool v) {
    _hasDistDomain = v;
  }
  bool hasDistDomain() {
    return _hasDistDomain;
  }

  bool withDist() {
    if (getDom() is null) return false;
    // else {
    //   getDom().isProperDist();
    // }
    return _hasDistDomain || isDist();
  }
  
  _esdl__ConstraintBase _constraint;
  uint _statement;
  bool _hasDistDomain;
  bool _domainContextSet;

  _esdl__Proxy _proxy;
  CstScope _scope;
  CstLogicTerm _expr;
  CstPredicate _parent;
  CstPredicate _guard;

  bool _isGuard;

  bool isGuard() { return _isGuard; }

  bool _guardInv;
  bool guardInv() { return _guardInv; }
    
  bool isGuardEnabled() {
    if (_guard is null) return true;
    else {
      auto gv = _guard._expr.eval();
      return gv ^ _guardInv;
    }
  }
  
  // When urolling, disable the previously unrolled constraints
  // if not required -- if the length is less now
  bool _isInRange = true;

  bool isEnabled() {
    if (_parent is null)
      return _constraint.isEnabled() && isInRange() && _proxy.isRand();
    else return _constraint.isEnabled() && isInRange() && _proxy.isRand() && _parent.isEnabled();
  }

  bool isInRange() {
    if (_parent is null) return _isInRange;
    else return _isInRange && _parent.isInRange();
  }

  bool isCollated() {
    return _state == State.COLLATED;
  }
  
  bool isDisabled() {
    return _state == State.DISABLED;
  }
  
  uint _level;
  uint _unrollCycle;
  bool _markResolve = true;

  CstVectorOp _vectorOp = CstVectorOp.NONE;
  bool _uniqueFlag = false;
  void setUniqueFlag() { _uniqueFlag = true; }
  uint _soft = 0;

  uint getSoftWeight() { return _soft; }

  State _state = State.INIT;

  void reset() {
    _state = State.INIT;
  }

  Folder!(CstPredicate, "uwPreds") _uwPreds;
  size_t _uwLength;
  
  __gshared uint _count;
  immutable uint _id;

  this(_esdl__ConstraintBase cst, CstPredicate guard, bool guardInv,
       uint stmt, _esdl__Proxy proxy, uint soft, CstLogicTerm expr,
       bool isGuard, CstPredicate parent=null,
       CstIterator unrollIter=null, uint unrollIterVal=0 // ,
       // CstIterator[] iters ...
       ) {
    synchronized (typeid(CstPredicate)) {
      _id = _count++;
    }
    assert(proxy !is null);
    _constraint = cst;
    _guard = guard;
    _guardInv = guardInv,
    _soft = soft;
    _statement = stmt;
    _proxy = proxy;
    _unrollIterVal = unrollIterVal;
    _isInRange = true;
    if (parent is null) {
      _scope = _proxy.currentScope();
      _level = 0;
    }
    else {
      _scope = parent._scope;
      _level = parent._level + 1;
    }
    assert(_scope !is null);
    _expr = expr;

    _isGuard = isGuard;

    _parent = parent;
    
    if (_parent is null) {
      _scope.getIterators(_parsedIters, _level);
    }
    else {
      _parsedIters =
	_parent._iters[1..$].
	map!(tr => tr.unrollIterator(unrollIter,
				     unrollIterVal)).array;
    }
      
    this.setPredContext();

    // setDomainContext is now being called on the newly unrolled predicates
    // using procUnrolledNewPredicates method in the proxy
    // if (parent !is null) this.setDomainContext(this); // unrolled

    debug(CSTPREDS) {
      import std.stdio;
      stdout.writeln(this.describe());
    }
  }

  _esdl__Proxy getProxy()() {
    assert(_proxy !is null);
    return _proxy;
  }

  void doResolve() {
    if (_iters.length == 0) {
      _markResolve = true;
      return;
    }
  }

  void doUnroll() {
    import std.conv: to;
    bool guardUnrolled = false;
    if (_unrollCycle == _proxy._cycle) { // already executed
      return;
    }

    _proxy.registerUnrolled(this);
    assert (_state != State.UNROLLED,
	    "Unexpected State: " ~ _state.to!string());
    _state = State.UNROLLED;
    // check if all the dependencies are resolved
    // foreach (dep; _deps) {
    //   if (! dep.isSolved()) {
    // 	return;
    //   }
    // }
    CstIterator iter = _iters[0];

    if (_guard !is null && _guard._iters.length > 0 &&
	_guard._iters[0] is iter) {
      _guard.doUnroll();
      guardUnrolled = true;
    }
    
    if (iter.getLenVec().isSolved()) {
      this.unroll(iter, guardUnrolled);
      _unrollCycle = _proxy._cycle;
    }
  }

  uint _currLen;
  
  void unroll(CstIterator iter, bool guardUnrolled) {
    assert (iter is _iters[0]);

    if (! iter.isUnrollable()) {
      assert(false, "CstIterator is not unrollabe yet: "
	     ~ this.describe());
    }

    auto prevLen = _currLen;
    _currLen = cast(uint) iter.size();
    auto builtLen = _uwPreds.length;
    // import std.stdio;
    // writeln("size is ", _currLen);

    if (_uwPreds.length < _currLen) _uwPreds.length = _currLen;
    
    for (uint i=0; i != _uwPreds.length; ++i) {
      if (i < _currLen) {
	if (i >= builtLen) {
	  CstPredicate _uwPred = _uwPreds[i];
	  assert (_uwPred is null);
	  CstPredicate guard = _guard;
	  if (guardUnrolled) guard = _guard._uwPreds[i];
	  _uwPred = new CstPredicate(_constraint, guard, _guardInv, _statement,
				     _proxy, _soft, _expr.unroll(iter, iter.mapIter(i)),
				     _isGuard, this, iter, i// ,
				     // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
				     );
	  _uwPreds[i] = _uwPred;
	  _proxy.addUnrolledNewPredicate(_uwPred);
	}
	else if (i >= prevLen) {
	  _uwPreds[i]._isInRange = true;
	}
	_proxy.addUnrolledPredicate(_uwPreds[i]);
      }
      else {
	_uwPreds[i]._isInRange = false;
      }
    }
  }

  final bool isResolved(bool force=false) {
    if (_markResolve || force) {
      _markResolve = false;
      foreach (dep; _deps) {
	if (! dep.isResolvedDep()) {
	  return false;
	}
      }
      // All _idxs are rolled into _deps
      // foreach (idx; _idxs) {
      // 	if (! idx.isSolved()) {
      // 	  return false;
      // 	}
      // }
      if (this.isGuard()) {
	tryResolve(_proxy);
      }
      return true;
    }
    return false;
  }

  // Excl. Conds -- The special case of mono and dist preds
  CstDomBase _dom;	    	// would be null if multiple domains
  CstDomBase getDom() {
    return _dom;
  }
  
  CstDomBase[] _rnds;
  CstDomSet[] _rndArrs;
  CstDomBase[] _dynRnds;
  CstDomBase[] _vars;
  CstDomSet[] _varArrs;
  CstValue[]  _vals;
  CstDepIntf[] _deps;
  CstDepIntf[] _idxs;
  CstDomBase[] _bitIdxs;
  CstIterator[] _iters;
  CstIterator[] _parsedIters;
  CstIterator[] _varIters;

  CstIterator _unrollIter;
  uint _unrollIterVal;

  uint _unresolveLap;

  bool isDynamic() {
    if (_dynRnds.length > 0) return true;
    else return false;
  }

  final CstDomBase[] getRnds() {
    return _rnds;
  }

  final CstDomBase[] getVars() {
    return _vars;
  }

  final CstValue[] getVals() {
    return _vals;
  }

  final CstDomBase[] getDomains() {
    return _rnds;
  }

  final CstDomSet[] getDomArrs(){
    return _rndArrs;
  }

  // final void tryResolveDepsRolled() {
  //   for (size_t i=0; i!=_uwLength; ++i) {
  //     _uwPreds[i].tryResolveDeps();
  //   }
  // }

  // final void markAsUnresolvedRolled(uint lap) {
  //   if (this.isRolled()) {
  //     this.markAsUnresolved(lap);
  //   }
  //   // else if (_iters.length > 1) {
  //   //   for (size_t i=0; i!=_uwLength; ++i) {
  //   // 	_uwPreds[i].markAsUnresolvedRolled(lap);
  //   //   }
  //   // }
  // }
  
  final void markAsUnresolved(uint lap) {
    if (_unresolveLap != lap) {	 // already marked -- avoid infinite recursion
      _unresolveLap = lap;
      foreach (rnd; _rnds) rnd.markAsUnresolved(lap);
      foreach (rndArr; _rndArrs) rndArr.markAsUnresolved(lap, true);
    }
  }

  final bool isMarkedUnresolved(uint lap) {
    if (_parent !is null) {
      if (_parent.isMarkedUnresolved(lap)) {
	return true;
      }
    }
    return (_unresolveLap == lap);
  }

  // final bool markIfUnresolved(uint lap) {
  //   if (_deps.length > 0 || _iter !is null) {
  //     this.markAsUnresolved(lap);
  //     return true;
  //   }
  //   return false;
  // }

  final bool isRolled() {
    if (this._iters.length > 0 &&
	_unrollCycle != _proxy._cycle) {
      return true;
    }
    return false;
  }

  // No longer required -- Taken care of by _state (UNROLLED)
  // used by setGroupContext to find if the predicate has been unrolled and
  // therefor it should not be considered for grouping
  // final bool hasUnrolled() {
  //   if (this._iters.length == 0 ||
  // 	_unrollCycle != _proxy._cycle) {
  //     return false;
  //   }
  //   return true;
  // }
  
  final bool hasDeps() {
    return this._deps.length > 0;
  }

  final bool solvable() {
    return _deps.length == 0 && _iters.length == 0;
  }
  
  bool hasDynamicBinding() {
    return _dynRnds.length > 0;
  }

  final void setPredContext() {
    _expr.setPredContext(this);
  }

  final void setDomainContext(CstPredicate pred, bool thisPred=true) {
    if (thisPred) {
      if (_domainContextSet) return;
      else _domainContextSet = true;
    }

    CstDomBase[] dists;
      
    _expr.setDomainContext(pred, pred._rnds, pred._rndArrs, pred._vars,
			   pred._varArrs, dists, pred._vals, pred._varIters,
			   pred._idxs, pred._bitIdxs, pred._deps);

    if (dists.length > 0) {
      if (thisPred is true && dists.length == 1 &&
	  _rnds.length == 0 && _rndArrs.length == 0) {
	assert (dists[0].isDist());
	pred._rnds ~= dists[0];
      }
      else {
	foreach (dist; dists) {
	  if (! pred._vars.canFind(dist)) pred._vars ~= dist;
	  if (! pred._deps.canFind(dist)) pred._deps ~= dist;
	}
      }
    }
      

    if (thisPred && _rnds.length == 1 && _rndArrs.length == 0)
      _dom = _rnds[0];

    // if (this is pred && this.isDist()) {
    //   assert (_rnds.length == 1 && _rndArrs.length == 0);
    // }

    
    if (_guard !is null) {
      if (_distDomain !is null && thisPred is true) { // processing a dist predicate
	// assert (thisPred is true);
	assert (_dom !is null && _dom == _distDomain);
	pred._deps ~= _guard;
      }
      else if (_dom !is null && _dom.isDist()) {
	// assert (thisPred is true);
	pred._deps ~= _guard;
      }
      else {
	_guard.setDomainContext(pred, false);
      }
    }

    if (thisPred) {
    
      // foreach (varIter; varIters) {
      //   import std.stdio;
      //   stdout.writeln("Found Iterator: ", varIter.name());
      // }
      // if (_iters.length > 0) {
      //   _len = _iters[0].getLenVec();
      // }
    
      if (! getExpr().isOrderingExpr()) {
	foreach (rnd; _rnds) {
	  rnd.registerRndPred(this);
	  if (! rnd.isStatic()) {
	    _dynRnds ~= rnd;
	  }
	}
	foreach (rnd; _rndArrs) {
	  rnd.registerRndPred(this);
	}
      }

      // foreach (var; _vars) var.registerVarPred(this);

      if ((! this.isVisitor()) && (! this.isGuard()) && _rndArrs.length == 0) {
	// assert (_rnds.length != 0, this.describe());
	if (_rnds.length > 1) {
	  foreach (rnd; _rnds) {
	    rnd._type = DomType.MULTI;
	  }
	}
	else if (! this.isDist()) {
	  if (_rnds.length == 1) {
	    auto rnd = _rnds[0];
	    if (rnd._type == DomType.TRUEMONO) {
	      if (_vars.length > 0) {
		rnd._type = DomType.LAZYMONO;
	      }
	      if (_idxs.length > 0) {
		assert(! rnd.isStatic());
		rnd._type = DomType.INDEXEDMONO;
	      }
	    }
	  }
	}
      }

      // When the parent unrolls, its dependencies would already be take care of
      // if (_parent !is null) {
      //   CstDomBase[] _foundDeps = _deps ~ _idxs;
      //   _deps = _foundDeps.filter!(dep => (! canFind(_parent._deps, dep))).array;
      // }

      foreach (idx; _idxs) if (! idx.isResolvedDep())
			     if (! _deps.canFind(idx)) _deps ~= idx;
      foreach (idx; _bitIdxs) if (! idx.isSolved())
				if (! _deps.canFind(idx)) _deps ~= idx;
    
      foreach (dep; _deps) dep.registerDepPred(this);

      // if (this.isGuard()) {
      // 	foreach (dep; _rnds) dep.registerDepPred(this);
      // }

      // For now treat _idxs as _deps since _idxs are merged with _deps
      // foreach (idx; _idxs) idx.registerIdxPred(this);

      // take only the parsed iterators that are found in the expression
      // as well
      // _iters = pasredIters.filter!(itr =>
      // 				 canFind(varIters, itr)).array;
      if (isVisitor()) {
	_iters = _varIters;
      }
      else {
	_iters = _parsedIters.filter!(itr =>
				      canFind!((CstIterator a, CstIterator b) => a == b)
				      (_varIters, itr)).array;
      }
    
      if (_iters.length != 0) _iters[0].registerRolled(this);
    }
  }

  void procDependency(CstDepIntf dep) {
    // import std.stdio;
    // writeln("Removing dep from rnds: ", dep.name());
    CstDomBase dom = cast (CstDomBase) dep;
    if (dom !is null) {
      auto index = countUntil(_rnds, dep);
      if (index >= 0) {
	_rnds[index] = _rnds[$-1];
	_rnds.length -= 1;
	_vars ~= dom;
	dom.purgeRndPred(this);
      }
    }
    if (_guard !is null) _guard.procDependency(dep);
  }
  
  void procDomainContext() {
    import std.algorithm.searching: canFind;
    foreach (rnd; _rnds) {
      foreach (dep; rnd.getDeps()) {
	if (! _deps.canFind(dep)) _deps ~= dep;
      }
    }
    foreach (rnd; _rndArrs) {
      foreach (dep; rnd.getDeps()) {
	if (! _deps.canFind(dep)) _deps ~= dep;
      }
    }
    if (! isVisitor())
      foreach (dep; _deps) this.procDependency(dep);
  }

  CstLogicTerm getExpr() {
    return _expr;
  }

  void tryResolveDeps(_esdl__Proxy proxy) {
    foreach (dep; _deps) dep.tryResolve(proxy);
    foreach (dep; _idxs) dep.tryResolve(proxy);
  }

  bool hasUpdate() {
    foreach (var; _vars) {
      if (var.hasChanged()) {
	return true;
      }
    }
    foreach (idx; _idxs) {
      if (idx.hasChanged()) {
	return true;
      }
    }
    return false;
  }

  string describe() {
    import std.string:format;
    import std.conv: to;
    string description = "Predicate Name: " ~ name() ~ "\n";
    description ~= "Predicate ID: " ~ _id.to!string() ~ "\n    ";
    description ~= "State: " ~ _state.to!string() ~ "\n    ";
    description ~= "Is In Range? " ~ _isInRange.to!string ~ "\n    ";
    description ~= "Expr: " ~ _expr.describe() ~ "\n    ";
    description ~= "Context Set? " ~ _domainContextSet.to!string() ~ "\n    ";
    description ~= _scope.describe();
    description ~= format("    Level: %s\n", _level);
    if (_iters.length > 0) {
      description ~= "    Iterators: \n";
      foreach (iter; _iters) {
	description ~= "\t" ~ iter.fullName() ~ "\n";
      }
    }
    if (_rnds.length > 0) {
      description ~= "    Domains: \n";
      foreach (rnd; _rnds) {
	description ~= "\t" ~ rnd.fullName() ~ "\n";
      }
    }
    if (_dynRnds.length > 0) {
      description ~= "    Dyn Domains: \n";
      foreach (rnd; _dynRnds) {
	description ~= "\t" ~ rnd.fullName() ~ "\n";
      }
    }
    if (_vars.length > 0) {
      description ~= "    Variables: \n";
      foreach (var; _vars) {
	description ~= "\t" ~ var.fullName() ~ "\n";
      }
    }
    if (_vals.length > 0) {
      description ~= "    Values: \n";
      foreach (val; _vals) {
	description ~= "\t" ~ val.describe() ~ "\n";
      }
    }
    if (_idxs.length > 0) {
      description ~= "    Indexes: \n";
      foreach (idx; _idxs) {
	description ~= "\t" ~ idx.fullName() ~ "\n";
      }
    }
    if (_bitIdxs.length > 0) {
      description ~= "    Bit Indexes: \n";
      foreach (idx; _bitIdxs) {
	description ~= "\t" ~ idx.fullName() ~ "\n";
      }
    }
    if (_deps.length > 0) {
      description ~= "    Depends: \n";
      foreach (dep; _deps) {
	description ~= "\t" ~ dep.fullName() ~ "\n";
      }
    }
    description ~= "\n";
    return description;
  }

  CstPredGroup _group;

  CstPredGroup group() {
    return _group;
  }

  void setProxyContext(_esdl__Proxy proxy){
    // import std.stdio;
    // writeln("setProxyContext: ", this.describe());

    foreach (dom; _rnds) {
      if (! dom.inRange()) {
	// import std.stdio;
	// writeln(this.describe());
	// writeln(_guard.describe());
	if (_guard is null || _guard._expr.eval()) {
	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
	}
	_state = State.DISABLED;
	return;
      }
    }

    foreach (dom; _vars) {
      if (! dom.inRange()) {
	// import std.stdio;
	// writeln(this.describe());
	// writeln(_guard.describe());
	if (_guard is null || _guard._expr.eval()) {
	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
	}
	_state = State.DISABLED;
	return;
      }
    }
    proxy.addGroupPredicate(this);

    foreach (dom; _rnds) {
      if (dom._state is CstDomBase.State.INIT && (! dom.isSolved())) {
	dom.setProxyContext(proxy);
      }
    }
    foreach (arr; _rndArrs) {
      if (arr._state is CstDomSet.State.INIT) {
	arr.setProxyContext(proxy);
      }
    }
  }

   void setGroupContext(CstPredGroup group, uint level) {
    
    
    assert(getOrderLevel() == level - 1, "unexpected error in solving before constraints");
      
    foreach (dom; _rnds) {
      assert(dom.getOrderLevel() != level, "unexpected error in solving before constraints");
      if (dom.getOrderLevel < level - 1){
	assert(dom.isSolved(), "unexpected error in solving before constraints");
      }
    } 
    
    addPredicateToGroup(group);
    
    foreach (dom; _rnds) {
      if (dom._state is CstDomBase.State.COLLATED && (! dom.isSolved())) {
	dom.setGroupContext(group, level);
      }
    }
    foreach (arr; _rndArrs) {
      if (arr._state is CstDomSet.State.COLLATED // && (! arr.isSolved())
	  ) {
	arr.setGroupContext(group, level);
      }
    }
  }

  void addPredicateToGroup(CstPredGroup group){
    _state = State.GROUPED;
    
    if (_group !is group) {
      assert(_group is null,
  	     "A predicate may be added to a group, but group should not change");
    }
    
    if (this.isDynamic()) {
      if (this.withDist()) { assert (false); } // group.addWithDistPredicate(this);
      else                 group.addDynPredicate(this);
    }
    else if (this.isDist()) {
      assert (group.hasDistConstraints());
      if (this.isGuardEnabled()) {
  	if (group._distPred !is null) {
  	  assert (false,
  		  "It is illegal to have more than one dist predicate active on the same domain");
  	}
  	group._distPred = this;
      }
      else {
  	group.addPredicate(this);
      }
    }
    else if (this.isGuard()) {
      group.addGuard(this);
    }
    else {
      group.addPredicate(this);
    }
    
  }
  // void setGroupContext(CstPredGroup group) {
  //   // import std.stdio;
  //   // writeln("setGroupContext: ", this.describe());
  //   foreach (dom; _rnds) {
  //     if (! dom.inRange()) {
  // 	// import std.stdio;
  // 	// writeln(this.describe());
  // 	// writeln(_guard.describe());
  // 	if (_guard is null || _guard._expr.eval()) {
  // 	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
  // 	}
  // 	return;
  //     }
  //   }

  //   foreach (dom; _vars) {
  //     if (! dom.inRange()) {
  // 	// import std.stdio;
  // 	// writeln(this.describe());
  // 	// writeln(_guard.describe());
  // 	if (_guard is null || _guard._expr.eval()) {
  // 	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
  // 	}
  // 	return;
  //     }
  //   }

  //   _state = State.GROUPED;
  //   if (_group !is group) {
  //     assert(_group is null,
  // 	     "A predicate may be added to a group, but group should not change");
  //     group.needSync();
  //   }
  //   if (_rndArrs.length != 0) group.needSync();
  //   if (_bitIdxs.length != 0) group.needSync();
  //   if (this.isDynamic()) {
  //     if (this.withDist()) { assert (false); } // group.addWithDistPredicate(this);
  //     else                 group.addDynPredicate(this);
  //   }
  //   else if (this.isDist()) {
  //     assert (group.hasDistConstraints());
  //     if (this.isGuardEnabled()) {
  // 	if (group._distPred !is null) {
  // 	  assert (false,
  // 		  "It is illegal to have more than one dist predicate active on the same domain");
  // 	}
  // 	group._distPred = this;
  //     }
  //     else {
  // 	group.addPredicate(this);
  //     }
  //   }
  //   else if (this.isGuard()) {
  //     group.addGuard(this);
  //   }
  //   else {
  //     group.addPredicate(this);
  //   }
  //   foreach (dom; _rnds) {
  //     // import std.stdio;
  //     // writeln("setGroupContext: ", dom.name());
  //     // if (dom.group is null && (! dom.isSolved())) {
  //     if (dom._state is CstDomBase.State.INIT && (! dom.isSolved())) {
  // 	dom.setGroupContext(group);
  //     }
  //   }
  //   foreach (arr; _rndArrs) {
  //     // import std.stdio;
  //     // writeln("setGroupContext: ", arr.name());
  //     // if (arr.group is null && (! arr.isSolved())) {
  //     if (arr._state is CstDomSet.State.INIT // && (! arr.isSolved())
  // 	  ) {
  // 	arr.setGroupContext(group);
  //     }
  //   }
  // }

  void annotate(CstPredGroup group, bool recurse=false) {
    // import std.stdio;
    // writeln("Annotating: ", this.describe());
    assert ((! this.isGuard()) || recurse);
    if (_guard !is null) _guard.annotate(group, true);

    foreach (rnd; this._rnds) {
      rnd.annotate(group);
    }
    foreach (rndArr; this._rndArrs) {
      group.addDomainArr(rndArr);
      foreach (rnd; rndArr[]) {
	rnd.annotate(group);
      }
    }
    foreach (var; this._vars) {
      var.annotate(group);
    }
    foreach (varArr; this._varArrs) {
      group.addVariableArr(varArr);
      foreach (var; varArr[]) {
	var.annotate(group);
      }
    }
  }

  void writeSignature(ref Charbuf str) {
    import std.format: sformat;
    if (_soft != 0) {
      char[16] buff;
      str ~= '!';
      str ~=  sformat(buff[], "%d", _soft); // _soft.to!string();
      str ~= ':';
    }
    if (_guard !is null) {
      if (_guardInv) str ~= " ! ";
      _guard.writeSignature(str);
      str ~= " >> ";
    }
    _expr.writeExprString(str);
  }

  void calcHash(ref Hash hash){
    hash.modify(33);
    hash.modify(_soft);
    hash.modify(58);
    if (_guard !is null) {
      _guard.calcHash(hash);
      if (_guardInv) hash.modify(33);
      hash.modify(62);
    }
    _expr.calcHash(hash);
  }

  bool isDist() { return _distDomain !is null; }
  CstDomBase _distDomain;
  void distDomain(CstDomBase vec) {
    assert (_distDomain is null);
    _distDomain = vec;
  }
  CstDomBase distDomain() {
    return _distDomain;
  }

  void markPredSolved() {
    import std.conv: to;
    // import std.stdio;
    // writeln("marking predicate solved: ", describe());
    assert (this.isGuard() || this.isVisitor() || _state == State.GROUPED,
	    "State is: " ~ _state.to!string());
    _state = State.SOLVED;

    this.execDepCbs();
  }

  bool tryResolveFixed(_esdl__Proxy proxy) {
    assert (isGuard());
    if (_rnds.length > 0 || _vars.length > 0) return false;
    else return tryResolve(proxy);
  }
  
  bool tryResolve(_esdl__Proxy proxy) {
    assert (isGuard());
    if (_varArrs.length > 0 || _rndArrs.length > 0) return false;
    else {
      bool success = true;
      foreach (rnd; _rnds) {
	if (! rnd.tryResolve(proxy)) {
	  success = false;
	}
      }
      if (success) {
	this.markPredSolved();
	proxy.solvedSome();
      }
      return success;
    }
  }
  
  bool isResolvedDep() {
    return isSolved();
  }

  bool isSolved() {
    return (_state == State.SOLVED);
  }

  CstDepCallback[] _depCbs;
  void registerDepPred(CstDepCallback depCb) {
    foreach (cb; _depCbs) {
      if (cb is depCb) {
	return;
      }
    }
    _depCbs ~= depCb;
  }

  void registerIdxPred(CstDepCallback depCb) {
    assert (false);
  }

  bool hasChanged() {
    assert (false);
  }

  void execDepCbs() {
    foreach (cb; _depCbs) {
      cb.doResolve();
    }
  }

  CstDomBase getDomain() { return null; }

  uint _orderLevel = 0;

  uint getOrderLevel(){
    return _orderLevel;
  }
  
  void setOrderLevel(uint level){
    _orderLevel = level;
  }
  
}

class CstVisitorPredicate: CstPredicate
{
  this(_esdl__ConstraintBase cst, CstPredicate guard, bool guardInv, uint stmt,
       _esdl__Proxy proxy, uint soft, CstLogicTerm expr, bool isGuard, CstPredicate parent=null,
       CstIterator unrollIter=null, uint unrollIterVal=0// ,
       // CstIterator[] iters ...
       ) {
    assert (guard is null);
    // import std.stdio;
    // writeln("Creating a visitor predicate: ", cst.name());
    super(cst, guard, guardInv, stmt, proxy, soft, expr, isGuard, parent, unrollIter, unrollIterVal);
  }

  override bool isVisitor() {
    return true;
  }

  override void unroll(CstIterator iter, bool guardUnrolled) {
    // import std.stdio;
    // writeln("Unrolling Visitor");
    assert (iter is _iters[0]);

    if (! iter.isUnrollable()) {
      assert (false, "CstIterator is not unrollabe yet: "
	      ~ this.describe());
    }
    auto currLen = iter.size();
    auto prevLen = _uwPreds.length;
    // import std.stdio;
    // writeln("size is ", currLen);

    if (currLen > prevLen) {
      // import std.stdio;
      // writeln("Need to unroll ", currLen - _uwPreds.length, " times");
      for (uint i = cast(uint) _uwPreds.length;
	   i != currLen; ++i) {
	// import std.stdio;
	// writeln("i: ", i, " mapped: ", iter.mapIter(i));
	_uwPreds ~= new CstVisitorPredicate(_constraint, _guard, _guardInv, _statement, _proxy, _soft,
					    _expr.unroll(iter, iter.mapIter(i)), false, this, iter, i// ,
					    // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
					    );
      }
      for (size_t i=prevLen; i!=currLen; ++i) {
	_uwPreds[i].setDomainContext(_uwPreds[i]);
      }
    }

    // Do not use foreach here since we may have more elements in the
    // array than the current value of currLen
    for (size_t i=0; i!=currLen; ++i) {
      if (_uwPreds[i]._iters.length == 0) { // completely unrolled
	_uwPreds[i]._expr.scan();
	// import std.stdio;
	// writeln("Collecting constraints from: ", _uwPreds[i]._expr.describe());
      }
      else {
	_proxy.addUnrolledPredicate(_uwPreds[i]);
      }
    }

    _uwLength = currLen;
  }
}
