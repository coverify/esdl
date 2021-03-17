module esdl.rand.pred;

import std.algorithm;
import std.array;
import std.container.array;

import esdl.data.folder;
import esdl.data.charbuf;
import esdl.rand.proxy: _esdl__Proxy, _esdl__ConstraintBase;
import esdl.rand.misc;
import esdl.rand.base: CstDomain, CstDomSet, CstIterCallback, DomType,
  CstDepCallback, CstScope, CstLogicExpr, CstIterator, CstVecNodeIntf;
import esdl.rand.expr: CstValue;

import esdl.solver.base;
import esdl.solver.mono: CstMonoSolver;
import esdl.solver.z3: CstZ3Solver;
import esdl.solver.buddy: CstBuddySolver;

class CstPredGroup			// group of related predicates
{
  // solve cycle for which this group is getting processed. If this
  // _cycle matches solver _cycle, that would mean this group is
  // already processed
  uint _cycle;

  bool _hasSoftConstraints;
  bool _hasVectorConstraints;
  bool _hasUniqueConstraints;

  bool hasSoftConstraints() {
    return _hasSoftConstraints;
  }

  bool hasVectorConstraints() {
    return _hasVectorConstraints;
  }
  
  bool hasUniqueConstraints() {
    return _hasUniqueConstraints;
  }
  
  // List of predicates permanently in this group
  Folder!(CstPredicate, "preds") _preds;
  Folder!(CstPredicate, "dynPreds") _dynPreds;

  Folder!(CstPredicate, "distPreds") _distPreds;
  Folder!(CstPredicate, "withDistPreds") _withDistPreds;
  
  Folder!(CstPredicate, "predList") _predList;
  Folder!(CstPredicate, "dynPredList") _dynPredList;
  Folder!(CstPredicate, "distPredList") _distPredList;
  Folder!(CstPredicate, "withDistPredList") _withDistPredList;
  
  CstPredicate[] predicates() {
    return _preds[];
  }

  _esdl__Proxy _proxy;
  __gshared uint _count;
  immutable uint _id;
  
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

  void addDynPredicate(CstPredicate pred) {
    _dynPredList ~= pred;
  }

  void addDistPredicate(CstPredicate pred) {
    _distPredList ~= pred;
  }

  void addWithDistPredicate(CstPredicate pred) {
    _withDistPredList ~= pred;
  }

  // The flag _hasDynamicBinding gets set if there is at least one
  // predicate that has a dynamically resolvable constraint --
  // typically that would mean a random variable dependancy as part of index 
  bool _hasDynamicBinding;

  Folder!(CstDomain, "doms") _doms;
  uint addDomain(CstDomain dom) {
    uint index = cast (uint) _doms.length;
    _doms ~= dom;
    return index;
  }

  Folder!(CstDomain, "distDoms") _distDoms;
  uint addDistDomain(CstDomain dom) {
    uint index = cast (uint) _distDoms.length;
    _distDoms ~= dom;
    return index;
  }

  Folder!(CstDomain, "rnds") _rnds;
  uint addRandom(CstDomain rnd) {
    uint index = cast (uint) _rnds.length;
    _rnds ~= rnd;
    return index;
  }


  CstDomain[] domains() {
    return _doms[];
  }
  
  CstDomSet[] domainArrs() {
    return _domArrs[];
  }
  
  Folder!(CstDomain, "vars") _vars;
  uint addVariable(CstDomain var) {
    uint index = cast (uint) _vars.length;
    _vars ~= var;
    return index;
  }

  CstDomain[] variables() {
    return _vars[];
  }

  Folder!(CstDomSet, "domArrs") _domArrs;
  
  void addDomainArr(CstDomSet domArr) {
    _domArrs ~= domArr;
  }

  Folder!(CstDomSet, "varArrs") _varArrs;
  
  void addVariableArr(CstDomSet varArr) {
    _varArrs ~= varArr;
  }

  // If there are groups that are related. This will only be true if
  // the _hasDynamicBinding flag is true
  Folder!(CstPredGroup, "boundGroups") _boundGroups;

  void setGroupContext(CstPredicate solvablePred) {
    import std.algorithm.sorting: sort;
    solvablePred.setGroupContext(this);
    
    if (_state is State.NEEDSYNC ||
	_proxy.needSync() is true ||
	_predList.length != _preds.length ||
	_dynPredList.length != _dynPreds.length ||
	_distPredList.length != _distPreds.length ||
	_withDistPredList.length != _withDistPreds.length) {

      _hasSoftConstraints = false;
      _hasVectorConstraints = false;
      _hasUniqueConstraints = false;

      _state = State.NEEDSYNC;	// mark that we need to reassign a solver
      foreach (pred; _preds) pred._group = null;
      _preds.reset();
      foreach (pred; sort!((x, y) => x.name() < y.name())(_predList[])) {
	pred._group = this;
	if (pred._soft != 0) _hasSoftConstraints = true;
	if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
	if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
	_preds ~= pred;
      }
      foreach (pred; _distPreds) pred._group = null;
      _distPreds.reset();
      foreach (pred; sort!((x, y) => x.name() < y.name())(_distPredList[])) {
	pred._group = this;
	if (pred._soft != 0) _hasSoftConstraints = true;
	if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
	if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
	_distPreds ~= pred;
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
      foreach (pred; _withDistPreds) pred._group = null;
      _withDistPreds.reset();
      foreach (pred; sort!((x, y) => x.name() < y.name())(_withDistPredList[])) {
	pred._group = this;
	if (pred._soft != 0) _hasSoftConstraints = true;
	if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
	if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
	_withDistPreds ~= pred;
      }
    }
    // for the next cycle
    _predList.reset();
    _distPredList.reset();
    _dynPredList.reset();
    _withDistPredList.reset();
  }

  void annotate() {
    foreach (pred; _preds) pred.annotate(this, false);
    foreach (pred; _distPreds) {
      // import std.stdio;
      // writeln("Annotating: ", pred.name);
      pred.annotate(this, true);
    }
  }

  Charbuf _sig;
  
  string signature() {
    _sig.reset();
    _sig ~= "GROUP:\n";
    foreach (pred; _preds) {
      pred.writeSignature(_sig);
    }
    foreach (pred; _distPreds) {
      pred.writeSignature(_sig);
    }
    foreach (pred; _withDistPreds) {
      pred.writeSignature(_sig);
    }
    return _sig.toString();
  }
  
  public enum State: ubyte
  {   INIT,
      NEEDSYNC,
      SOLVED
      }

  State _state;
  
  void reset() {
    _state = State.INIT;
    foreach (pred; _preds) {
      pred.reset();
    }
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

    if (_state is State.NEEDSYNC) {
      _doms.reset();
      _vars.reset();
      annotate();
      string sig = signature();

      if (_proxy._esdl__debugSolver()) {
	import std.stdio;
	writeln(sig);
      }

      CstSolver* solverp = sig in _proxy._solvers;

      if (solverp !is null) {
	_solver = *solverp;
	_solver.solve(this);
      }
      else if (_doms.length == 0) {
	assert (_solver is null);
	_solver = null;
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
	  if (_doms.length == 1) {
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
	      assert (! dom.isProperDist());
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
	_proxy._solvers[sig] = _solver;
      }
      foreach (var; _vars) {
	var._domN = uint.max;
      }
    }
    else {
      // import std.stdio;
      // writeln(_solver.describe());
      // writeln("We are here");
      if (_solver !is null) _solver.solve(this);
    }

    foreach (rnd; _rnds) {
      // import std.stdio;
      // writeln("Randomizing: ", rnd.name());
      rnd.randomizeWithoutConstraints(_proxy);
    }

    foreach (pred; _distPreds) {
      // import std.stdio;
      // writeln("Working on: ", pred.name());
      pred.markSolved();
    }
    // import std.stdio;
    // writeln(_solver.describe());
    // _solver.solve(this);
    foreach (pred; _preds) {
      pred.markSolved();
    }
    this.markSolved();
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
    if (_distPreds.length > 0) {
      description ~= "  Dist Predicates:\n";
      foreach (pred; _distPreds) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_dynPreds.length > 0) {
      description ~= "  Dynamic Predicates:\n";
      foreach (pred; _dynPreds) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_withDistPreds.length > 0) {
      description ~= "  With Dist Predicates:\n";
      foreach (pred; _withDistPreds) {
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

class CstPredicate: CstIterCallback, CstDepCallback
{
  string name() {
    import std.conv;
    if (_parent is null) {
      return _constraint.fullName() ~ '/' ~
	_statement.to!string() ~ '%' ~ _id.to!string();
    }
    else {
      return _parent.name() ~
	'[' ~ _unrollIterVal.to!string() ~ ']' ~'%' ~ _id.to!string();
    }
  }

  bool isVisitor() {
    return false;
  }

  void visit(CstSolver solver) {
    if (_guard is null) {
      _expr.visit(solver);
    }
    else {
      _guard.visit(solver);
      if (_guardInv)
	solver.processEvalStack(CstLogicOp.LOGICNOT);
      _expr.visit(solver);
      if (this.isGuard())
	solver.processEvalStack(CstLogicOp.LOGICAND);
      else
	solver.processEvalStack(CstLogicOp.LOGICIMP);
    }
  }
  // alias _expr this;

  enum State: byte { INIT = 0, GROUPED = 1, SOLVED = 2 }

  bool _markBefore;

  bool _hasDistDomain;

  void hasDistDomain(bool v) {
    _hasDistDomain = v;
  }
  bool hasDistDomain() {
    return _hasDistDomain;
  }

  bool withDist() {
    return _hasDistDomain || isDist();
  }
  
  _esdl__ConstraintBase _constraint;
  uint _statement;
  _esdl__Proxy _proxy;
  CstScope _scope;
  CstLogicExpr _expr;
  CstPredicate _parent;
  CstPredicate _guard;

  bool _isGuard;

  bool isGuard() { return _isGuard; }

  bool _guardInv;
  bool guardInv() { return _guardInv; }
    
  bool isGuardEnabled() {
    // if (_guard is null) return true;
    // else {
    //   auto gv = _guard.evaluate();
      
    // }
    return true;
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

  void setmarkBefore(bool a){
    _markBefore = a;
  }
  bool getmarkBefore(){
    return _markBefore;
  }
  
  void reset() {
    _state = State.INIT;
  }

  Folder!(CstPredicate, "uwPreds") _uwPreds;
  size_t _uwLength;
  
  __gshared uint _count;
  immutable uint _id;

  this(_esdl__ConstraintBase cst, CstPredicate guard, bool guardInv,
       uint stmt, _esdl__Proxy proxy, uint soft, CstLogicExpr expr,
       bool isGuard, CstPredicate parent=null,
       CstIterator unrollIter=null, uint unrollIterVal=0 // ,
       // CstIterator[] iters ...
       ) {
    synchronized(typeid(CstPredicate)) {
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
      
    this.setDomainContext(this);

    debug(CSTPREDS) {
      import std.stdio;
      stderr.writeln(this.describe());
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
    else {
      doUnroll();
    }
  }

  void doUnroll() {
    bool guardUnrolled = false;
    if (_unrollCycle == _proxy._cycle) { // already executed
      return;
    }
    // check if all the dependencies are resolved
    // foreach (dep; _deps) {
    //   if (! dep.isSolved()) {
    // 	return;
    //   }
    // }
    CstIterator iter = _iters[0];

    if (_guard !is null && _guard._iters[0] is iter) {
      _guard.doUnroll();
      guardUnrolled = true;
    }
    
    if (iter.getLenVec().isSolved()) {
      this.unroll(iter, guardUnrolled);
      _unrollCycle = _proxy._cycle;
    }
  }
  
  void unroll(CstIterator iter, bool guardUnrolled) {
    assert (iter is _iters[0]);

    if (! iter.isUnrollable()) {
      assert(false, "CstIterator is not unrollabe yet: "
	     ~ this.describe());
    }
    auto currLen = iter.size();
    // import std.stdio;
    // writeln("size is ", currLen);

    if (currLen > _uwPreds.length) {
      // import std.stdio;
      // writeln("Need to unroll ", currLen - _uwPreds.length, " times");
      for (uint i = cast(uint) _uwPreds.length;
	   i != currLen; ++i) {
	// import std.stdio;
	// writeln("i: ", i, " mapped: ", iter.mapIter(i));
	if (_guard is null) {
	  _uwPreds ~= new CstPredicate(_constraint, null, false, _statement, _proxy, _soft,
				       _expr.unroll(iter, iter.mapIter(i)), _isGuard, this, iter, i// ,
				       // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
				       );
	}
	else {
	  if (guardUnrolled) {
	    _uwPreds ~= new CstPredicate(_constraint, _guard._uwPreds[i],
					 _guardInv, _statement, _proxy, _soft,
					 _expr.unroll(iter, iter.mapIter(i)),
					 _isGuard, this, iter, i// ,
					 // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
					 );
	  }
	  else {
	    _uwPreds ~= new CstPredicate(_constraint, _guard,
					 _guardInv, _statement, _proxy, _soft,
					 _expr.unroll(iter, iter.mapIter(i)),
					 _isGuard, this, iter, i// ,
					 // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
					 );
	  }
	}
      }
    }

    // Do not use foreach here since we may have more elements in the
    // array than the current value of currLen
    for (size_t i=0; i!=currLen; ++i) {
      _proxy.addUnrolledPredicate(_uwPreds[i]);
    }

    _uwLength = currLen;
  }

  final bool isResolved(bool force=false) {
    if (_markResolve || force) {
      _markResolve = false;
      foreach (dep; _deps) {
	if (! dep.isSolved()) {
	  return false;
	}
      }
      // All _idxs are rolled into _deps
      // foreach (idx; _idxs) {
      // 	if (! idx.isSolved()) {
      // 	  return false;
      // 	}
      // }
      return true;
    }
    return false;
  }

  // Excl. Conds -- The special case of mono and dist preds
  CstDomain _dom;	    	// would be null if multiple domains
  CstDomain getDom() {
    return _dom;
  }
  
  CstDomain[] _rnds;
  CstDomSet[] _rndArrs;
  CstDomain[] _dynRnds;
  CstDomain[] _vars;
  CstDomSet[] _varArrs;
  CstValue[]  _vals;
  CstVecNodeIntf[] _deps;
  CstVecNodeIntf[] _idxs;
  CstDomain[] _bitIdxs;
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

  final CstDomain[] getRnds() {
    return _rnds;
  }

  final CstDomain[] getVars() {
    return _vars;
  }

  final CstValue[] getVals() {
    return _vals;
  }

  final CstDomain[] getDomains() {
    return _rnds;
  }

  // final void randomizeDepsRolled() {
  //   for (size_t i=0; i!=_uwLength; ++i) {
  //     _uwPreds[i].randomizeDeps();
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
  
  final bool hasDeps() {
    return this._deps.length > 0;
  }

  final bool solvable() {
    return _deps.length == 0 && _iters.length == 0;
  }
  
  bool hasDynamicBinding() {
    return _dynRnds.length > 0;
  }

  final void setDomainContext(CstPredicate pred) {
    
    _expr.setDomainContext(pred, pred._rnds, pred._rndArrs, pred._vars,
			   pred._varArrs, pred._vals, pred._varIters,
			   pred._idxs, pred._bitIdxs, pred._deps);

    if (this is pred && _rnds.length == 1 && _rndArrs.length == 0)
      _dom = _rnds[0];

    // if (this is pred && this.isDist()) {
    //   assert (_rnds.length == 1 && _rndArrs.length == 0);
    // }

    if (_guard !is null) {
      _guard.setDomainContext(pred);
    }

    if (this is pred) {
    
      // foreach (varIter; varIters) {
      //   import std.stdio;
      //   stderr.writeln("Found Iterator: ", varIter.name());
      // }
      // if (_iters.length > 0) {
      //   _len = _iters[0].getLenVec();
      // }
    
      if(! getExpr().isOrderingExpr()){
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
	assert (_rnds.length != 0, this.describe());
	if (_rnds.length > 1) {
	  foreach (rnd; _rnds) {
	    rnd._type = DomType.MULTI;
	  }
	}
	else if (! this.isDist()) {
	  assert(_rnds.length == 1);
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

      // When the parent unrolls, its dependencies would already be take care of
      // if (_parent !is null) {
      //   CstDomain[] _foundDeps = _deps ~ _idxs;
      //   _deps = _foundDeps.filter!(dep => (! canFind(_parent._deps, dep))).array;
      // }

      foreach (idx; _idxs) if (! idx.isSolved()) _deps ~= idx;
      foreach (idx; _bitIdxs) if (! idx.isSolved()) _deps ~= idx;
    
      foreach (dep; _deps) dep.registerDepPred(this);

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

  CstLogicExpr getExpr() {
    return _expr;
  }

  void randomizeDeps(_esdl__Proxy proxy) {
    foreach (dep; _deps) dep.randomizeIfUnconstrained(proxy);
    foreach (dep; _idxs) dep.randomizeIfUnconstrained(proxy);
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
    string description = "    Predicate ID: " ~ _id.to!string() ~ "\n    ";
    description ~= "Expr: " ~ _expr.describe() ~ "\n    ";
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

  void setGroupContext(CstPredGroup group) {
    _state = State.GROUPED;
    if (_group !is group) {
      assert(_group is null,
	     "A predicate may be added to a group, but group should not change");
      group.needSync();
    }
    if (_rndArrs.length != 0) group.needSync();
    if (_bitIdxs.length != 0) group.needSync();
    if (this.isDynamic()) {
      if (this.withDist()) { assert (false); } // group.addWithDistPredicate(this);
      else                 group.addDynPredicate(this);
    }
    else {
      if (this.isDist())        group.addDistPredicate(this);
      else if (this.withDist()) group.addWithDistPredicate(this);
      else                      group.addPredicate(this);
    }
    foreach (dom; _rnds) {
      // if (dom.group is null && (! dom.isSolved())) {
      if (dom._state is CstDomain.State.INIT && (! dom.isSolved())) {
	dom.setGroupContext(group);
      }
    }
    foreach (arr; _rndArrs) {
      // if (arr.group is null && (! arr.isSolved())) {
      if (arr._state is CstDomSet.State.INIT // && (! arr.isSolved())
	  ) {
	arr.setGroupContext(group);
      }
    }
  }

  void annotate(CstPredGroup group, bool withDist) {
    assert (! this.isGuard());
    foreach (rnd; this._rnds) {
      rnd.annotate(group, withDist);
    }
    foreach (rndArr; this._rndArrs) {
      group.addDomainArr(rndArr);
      foreach (rnd; rndArr[]) {
	rnd.annotate(group, withDist);
      }
    }
    foreach (var; this._vars) {
      var.annotate(group, withDist);
    }
    foreach (varArr; this._varArrs) {
      group.addVariableArr(varArr);
      foreach (var; varArr[]) {
	var.annotate(group, withDist);
      }
    }
  }

  void writeSignature(ref Charbuf str) {
    import std.conv: to;
    if (_soft != 0) {
      str ~= '!';
      str ~= _soft.to!string();
      str ~= ':';
    }
    if (_guard !is null) {
      if (_guardInv) str ~= " ! ";
      _guard.writeSignature(str);
      str ~= " >> ";
    }
    _expr.writeExprString(str);
  }

  bool isDist() { return _distDomain !is null; }
  CstDomain _distDomain;
  void distDomain(CstDomain vec) {
    assert (_distDomain is null);
    _distDomain = vec;
  }
  CstDomain distDomain() {
    return _distDomain;
  }

  void markSolved() {
    assert (_state == State.GROUPED);
    _state = State.SOLVED;
  }
  
  bool isSolved() {
    return (_state == State.SOLVED);
  }
}

class CstVisitorPredicate: CstPredicate
{
  this(_esdl__ConstraintBase cst, CstPredicate guard, bool guardInv, uint stmt,
       _esdl__Proxy proxy, uint soft, CstLogicExpr expr, bool isGuard, CstPredicate parent=null,
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
    // import std.stdio;
    // writeln("size is ", currLen);

    if (currLen > _uwPreds.length) {
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
