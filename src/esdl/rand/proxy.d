module esdl.rand.proxy;

import esdl.solver.base: CstSolver, CstDistSolverBase;
import esdl.rand.base: CstVecPrim, CstScope, CstDomBase,
  CstObjectVoid, CstVarNodeIntf, CstObjectIntf, CstObjStub,
  CstIterator, CstDomSet, CstVarGlobIntf, CstVecNodeIntf;
import esdl.rand.pred: CstPredicate;
import esdl.rand.agent: CstSolverAgent;
import esdl.rand.cstr: _esdl__ConstraintBase;
import esdl.solver.dist: CstDistPredSolver;
import esdl.rand.misc;
import esdl.data.vector;

import std.algorithm.searching: canFind;
import esdl.rand.parser: CstParseData, CstParser;
import esdl.base.rand: _esdl__RandGen, getRandGen;
// import esdl.base.alloc: make;
import std.algorithm.mutation: swap;


abstract class _esdl__Proxy: CstObjectVoid, CstObjectIntf, rand.barrier
{
  immutable bool _esdl__isRootProxy;

  // private _esdl__ConstraintBase[string] _esdl__cstNames;

  // void _esdl__addConstraintName(_esdl__ConstraintBase cst) {
  //   auto cstName = cst._esdl__getName();
  //   _esdl__ConstraintBase* prevCst = cstName in _esdl__cstNames;
  //   if (prevCst !is null) {
  //     prevCst.markOverridden();
  //     _esdl__cstNames[cstName] = cst;
  //   }
  //   else {
  //     _esdl__cstNames[cstName] = cst;
  //   }
  // }

  // _esdl__stub provides the interface to the objx instance
  // would be null for root proxy
  CstObjStub _esdl__stub;

  final void _esdl__setStub(CstObjStub stub) {
    _esdl__stub = stub;
  }

  _esdl__CstProcessor _esdl__getProc() {
    return _esdl__stub._esdl__getProc();
  }
  
  _esdl__Proxy _esdl__getProxy() {
    return this;
  }

  string _esdl__name() {
    return _esdl__stub._esdl__name();
  }
  
  string _esdl__getFullName() {
    return _esdl__stub._esdl__getFullName();
  }
  string _esdl__getName() {
    return _esdl__stub._esdl__getName();
  }
  
  bool _esdl__isRand() {
    assert (_esdl__stub !is null);
    return _esdl__stub._esdl__isRand();
  }
  
  bool _esdl__isDomainInRange() {
    assert (_esdl__stub !is null);
    return _esdl__stub._esdl__isDomainInRange();
  }

  override bool _esdl__depsAreResolved() {
    assert (_esdl__stub !is null);
    return _esdl__stub._esdl__depsAreResolved();
  }

  _esdl__Proxy _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
    assert (_esdl__stub !is null);
    return _esdl__stub._esdl__unroll(iter, n, proc)._esdl__getProxy();
  }

  override _esdl__Proxy _esdl__getResolvedNode(_esdl__CstProcessor proc) {
    assert (false);
  }

  // the root proxy is always static
  bool _esdl__isStatic() {
    assert (_esdl__stub !is null);
    return _esdl__stub._esdl__isStatic();
  }

  bool _esdl__isReal() {
    assert (_esdl__stub !is null);
    return _esdl__stub._esdl__isReal();
  }

  bool _esdl__isRolled(_esdl__CstProcessor proc) {
    assert (_esdl__stub !is null);
    return _esdl__stub._esdl__isRolled(proc);
  }

  final bool _esdl__isRoot() {
    return _esdl__isRootProxy;
  }

  version (CACHEDPROXIES) {
    // Caches
    Vector!(_esdl__Proxy, "cachedProxies") _esdl__cachedProxies;
    private bool _esdl__cacheNeedsReset;

    final void _esdl__addCachedProxy(_esdl__Proxy proxy) {
      _esdl__cacheNeedsReset = true;
      assert (_esdl__isRoot());
      _esdl__cachedProxies ~= proxy;
    }

    final void _esdl__resetCaches() {
      assert (_esdl__isRoot());
      if (_esdl__cacheNeedsReset) {
	foreach (proxy; _esdl__cachedProxies[]) {
	  proxy._esdl__resetCache();
	}
	_esdl__cachedProxies.reset();
	_esdl__cachedProxies.clear();
	_esdl__cacheNeedsReset = false;
      }
    }

    void _esdl__resetCache() { }
  }

  // CstObjNodeIntf
  final CstIterator _esdl__iter() { return null; }
  final CstVarNodeIntf _esdl__getChild(ulong n) { assert (false); }
  void _esdl__scan(_esdl__CstProcessor proc) { }		// when an object is unrolled

  CstVarGlobIntf[string] _esdl__globalLookups;

  void _esdl__addGlobalLookup(CstVarGlobIntf global, string lookup) {
    assert(lookup !in _esdl__globalLookups);
    _esdl__globalLookups[lookup] = global;
  }

  CstVarGlobIntf _esdl__getGlobalLookup(string lookup) {
    auto global = lookup in _esdl__globalLookups;
    if (global !is null) return *global;
    else return null;
  }

  Vector!(_esdl__ConstraintBase, "globalVisitors") _esdl__globalVisitors;

  void _esdl__addGlobalVisitor(_esdl__ConstraintBase visitor) {
    _esdl__globalVisitors ~= visitor;
  }

  void _esdl__setContextGlobalVisitors(_esdl__CstProcessor proc) {
    foreach (visitor; _esdl__globalVisitors[]) {
      visitor.doSetDomainContext(proc);
      visitor.doProcDomainContext(proc);
    }
  }

  _esdl__ConstraintBase[] _esdl__getGlobalVisitors() {
    return _esdl__globalVisitors[];
  }


  
  // Scope for foreach
  CstScope _esdl__rootScope;
  CstScope _esdl__currentScope;

  void _esdl__pushScope(CstIterator iter) {
    assert (_esdl__currentScope !is null);
    _esdl__currentScope = _esdl__currentScope.push(iter);
  }

  void _esdl__popScope() {
    assert (_esdl__currentScope !is null);
    assert (_esdl__currentScope !is _esdl__rootScope);
    _esdl__currentScope = _esdl__currentScope.pop();
  }

  CstScope _esdl__getCurrentScope() {
    assert (_esdl__currentScope !is null);
    return _esdl__currentScope;
  }

  abstract bool _esdl__debugSolver();

  // overridden by Randomization mixin -- see meta.d
  abstract void _esdl__doRandomize(_esdl__RandGen randGen);
  abstract void _esdl__doConstrain(_esdl__CstProcessor proc, bool callPreRandomize);

  // Keep a list of constraints in the class
  _esdl__ConstraintBase _esdl__lambdaCst;


  this(CstObjStub stub) {
    if (stub._esdl__isRoot()) _esdl__isRootProxy = true;

    _esdl__stub = stub;
    
    // scopes for constraint parsing
    _esdl__rootScope = new CstScope(null, null);
    _esdl__currentScope = _esdl__rootScope;

  }

}

class _esdl__CstProcessor
{
  this(CstObjStub stub) {
    _stub = stub;
    _debugSolver = _stub._esdl__debugSolver();
    _randGen = new _esdl__RandGen(_seed);
    assert (_randGen !is null);
  }
  
  immutable bool _debugSolver;
  final bool debugSolver() {
    return _debugSolver;
  }
  
  CstObjStub _stub;

  uint _seed;
  bool _seeded = false;

  uint getRandomSeed() {
    return _seed;
  }

  bool isRandomSeeded() {
    return _seeded;
  }

  void seedRandom(uint seed) {
    _seeded = true;
    _seed = seed;
    _randGen.seed(seed);    
  }
  
  _esdl__RandGen _randGen;

  final _esdl__RandGen getRandGen() {
    return _randGen;
  }
  
  static CstSolverAgent _agent;
  static CstDistPredSolver _distPredSolver;

  static getPredSolver() {
    if (_agent is null) _agent = new CstSolverAgent();
    return _agent;
  }

  static getDistPredSolver() {
    if (_distPredSolver is null) _distPredSolver = new CstDistPredSolver();
    return _distPredSolver;
  }

  Vector!(CstVecNodeIntf, "lambdaCstDoms") _esdl__lambdaCstDoms;

  final void _esdl__addLambdaCstDom(CstVecNodeIntf dom) {
    _esdl__lambdaCstDoms ~= dom;
  }

  final void _esdl__doResetLambdaPreds() {
    foreach (lambdaCstDom; _esdl__lambdaCstDoms) lambdaCstDom.resetLambdaPreds();
    _esdl__lambdaCstDoms.reset();
    // reset lambda arg visitors
    _esdl__argVisitors.reset();
  }

  Vector!(_esdl__ConstraintBase, "argVisitors") _esdl__argVisitors;

  void _esdl__addArgVisitor(_esdl__ConstraintBase visitor) {
    _esdl__argVisitors ~= visitor;
  }

  void _esdl__setContextArgVisitors(_esdl__CstProcessor proc) {
    foreach (visitor; _esdl__argVisitors) {
      visitor.doSetDomainContext(proc);
      visitor.doProcDomainContext(proc);
    }
  }

  _esdl__ConstraintBase[] _esdl__getArgVisitors() {
    return _esdl__argVisitors[];
  }

  Vector!(CstPredicate, "unrolledNewPreds") _unrolledNewPreds;

  void addUnrolledNewPredicate(CstPredicate pred) {
    _unrolledNewPreds ~= pred;
  }

  void procUnrolledNewPredicates() {
    foreach (pred; _unrolledNewPreds) pred.doSetDomainContext(pred, this);
    foreach (pred; _unrolledNewPreds) pred.doProcDomainContext(this);
    _unrolledNewPreds.reset();
  }

  // Vector!(CstPredicate, "predsThatUnrolled") _predsThatUnrolled;
  // void registerUnrolled(CstPredicate pred) {
  //   _predsThatUnrolled ~= pred;
  // }

  Vector!(CstPredicate, "newPreds") _newPreds;
  Vector!(CstPredicate, "toNewPreds") _toNewPreds;
  // Vector!(CstPredicate, "unrolledPreds") _unrolledPreds;
  // Vector!(CstPredicate, "toUnrolledPreds") _toUnrolledPreds;
  
  Vector!(CstPredicate, "rolledPreds") _rolledPreds;
  Vector!(CstPredicate, "toRolledPreds") _toRolledPreds;

  Vector!(CstPredicate, "resolvedPreds") _resolvedPreds;
  Vector!(CstPredicate, "toResolvedPreds") _toResolvedPreds;

  Vector!(CstPredicate, "resolvedDistPreds") _resolvedDistPreds;
  Vector!(CstPredicate, "toResolvedDistPreds") _toResolvedDistPreds;

  Vector!(CstPredicate, "solvePreds") _solvePreds;

  Vector!(CstPredicate, "unresolvedPreds") _unresolvedPreds;
  Vector!(CstPredicate, "toUnresolvedPreds") _toUnresolvedPreds;

  Vector!(CstPredicate, "predGuards") _predGuards;

  Vector!(CstDomBase, "solvedDomains") _solvedDomains;
  Vector!(CstDomSet, "solvedDomainArrs") _solvedDomainArrs;
  
  // Vector!(CstSolverAgent, "solvedSolvers") _solvedSolvers;

  
  Vector!(CstPredicate, "collatedPredicates") _collatedPredicates;
  Vector!(CstDomBase, "collatedDomains") _collatedDomains;
  Vector!(CstDomSet, "collatedDomArrs") _collatedDomArrs;
  
  Vector!(CstVarNodeIntf, "beforeSolve") _beforeSolve;
  Vector!(CstVarNodeIntf, "afterSolve") _afterSolve;

  void collatePredicate (CstPredicate pred){
    _collatedPredicates ~= pred;
    pred._orderLevel = 0;
    pred._state = CstPredicate.State.COLLATED;
  }

  void collateDomain (CstDomBase dom){
    _collatedDomains ~= dom;
    dom._orderLevel = 0;
    dom._state = CstDomBase.State.COLLATED;
  }
  
  void collateDomArr (CstDomSet domArr){
    _collatedDomArrs ~= domArr;
    domArr._orderLevel = 0;
    domArr._state = CstDomSet.State.COLLATED;
  }

  Vector!(CstIterator, "itersWithCbs") _itersWithCbs;

  void printSolver (){
    import std.stdio;
    writeln("\nPreds: ");
    foreach (pred; _collatedPredicates){
      writeln(pred._esdl__getName(), ", ", pred._esdl__getOrderLevel);
    }
    writeln("Doms: ");
    foreach (dom; _collatedDomains){
      writeln(dom._esdl__getFullName(), ", ", dom._esdl__getOrderLevel);
    }
    writeln("DomArrs: ");
    foreach (dom; _collatedDomArrs){
      writeln(dom._esdl__getFullName(), ", ", dom._esdl__getOrderLevel);
    }
  }
  
  bool markDependents(uint level){ // returns true if some domains are marked

    _beforeSolve.reset();
    _afterSolve.reset();

    foreach (dom; _collatedDomains) {

      if (dom.isSolved()) { //isSolved
	assert(level == 1 || dom._esdl__getOrderLevel < level - 1);
	continue;
      }
      
      CstVarNodeIntf [] dependents = dom.getDependents();
      
      if (dependents.length == 0) continue;
      
      foreach (domSec; _collatedDomains){
	if (domSec.isDependent(dependents)){
	  _beforeSolve ~= dom;
	  _afterSolve ~= domSec;
	  domSec._esdl__setOrder(SolveOrder.LATER);
	}
      }
      foreach (domArrSec; _collatedDomArrs){
	if (domArrSec.isDependent(dependents)){
	  _beforeSolve ~= dom;
	  _afterSolve ~= domArrSec;
	  domArrSec._esdl__setOrder(SolveOrder.LATER);
	}
      }
    }
    foreach (domArr; _collatedDomArrs) {

      if (domArr._esdl__getOrderLevel() < level-1) { //isSolved -- TBD
	continue;
      }
      
      CstVarNodeIntf [] dependents = domArr.getDependents();
      
      if (dependents.length == 0) continue;
      
      foreach (domSec; _collatedDomains){
	if (domSec.isDependent(dependents)){
	  _beforeSolve ~= domArr;
	  _afterSolve ~= domSec;
	  domSec._esdl__setOrder(SolveOrder.LATER);
	}
      }
      foreach (domArrSec; _collatedDomArrs){
	if (domArrSec.isDependent(dependents)){
	  _beforeSolve ~= domArr;
	  _afterSolve ~= domArrSec;
	  domArrSec._esdl__setOrder(SolveOrder.LATER);
	}
      }
    }

    // CstVarNodeIntf [] beforeElems;
    
    foreach (i, elem; _beforeSolve[]) {
      assert (elem._esdl__getOrderLevel() >= level - 1, "unexpected error in solve before constraints");
      assert (_afterSolve[i]._esdl__getOrderLevel() >= level - 1, "unexpected error in solve before constraints");
      if (elem._esdl__getOrder() == SolveOrder.UNDECIDED) elem._esdl__setOrder(SolveOrder.NOW);
    }
    foreach (elem; _afterSolve[]) {
      elem._esdl__markOrderedAfter(level);
    }
    foreach (elem; _afterSolve[]) {
      elem._esdl__setOrder(SolveOrder.UNDECIDED);
    }
    foreach (elem; _beforeSolve[]){
      elem._esdl__setOrder(SolveOrder.UNDECIDED);
    }
    return _beforeSolve.length > 0;
  }

  // void markBase(CstDomBase base, CstDomBase dom, uint level){
  //   foreach (child; dom.getSolvedBefore()){
  //     child._esdl__markOrderedAfter(base, level);
  //     markBase(base, child, level);
  //   }
  // }

  // CstVarNodeIntf getBase(CstVarNodeIntf dom, ulong maxIter){
  //   for (int i = 0; i < maxIter; i ++){
  //     if (dom.getSolvedAfter().length == 0){
  // 	return dom;
  //     }
  //     dom = dom.getSolvedAfter()[0];
  //   }
  //   return null;
  // }

  void addSolvedDomain(CstDomBase domain) {
    _solvedDomains ~= domain;
  }

  void addSolvedDomainArr(CstDomSet domain) {
    _solvedDomainArrs ~= domain;
  }


  // the integer variable _lap is incremented everytime a set of @rand
  // variables is made available for constraint solving. This 
  // variable is used for:
  // 1. marking the predicates that have unresolved dependencies
  //    and/or have a relation with such predicates. When some
  //    predicated are resolved it may lead to some of these
  //    predicates becoming available
  uint _lap;
  // _cycle is incremented once everytime randomize function is
  // called. The use of this variable within a @rand variable is to
  // indicate that the variable has been solved. Within a predicate,
  // this variable indicates that the predicate has been solved for
  // the indiated randomization cycle. There are two more places where
  // this variable is used:
  // 1. To indicate that iterator has been unrolled for a vec array in
  //    a given randomization cycle.
  // 2. To indicate that the index expression has been resolved for a
  //    vec/vec-array for the indicated randomization cycle
  uint _cycle;

  // // CstDomBase[] _cstRndDomains;
  // CstDomBase[] _esdl__cstValDomains;

  // void updateValDomains() {
  //   foreach (dom; _esdl__cstValDomains) {
  //     dom.updateVal();
  //   }
  // }
  
  void reset() {
    // _solvedDomains is from previous cycle
    foreach (dom; _solvedDomains) dom.reset();
    foreach (domArr; _solvedDomainArrs) domArr.reset();
    // reset all bins
    _newPreds.reset();
    _toNewPreds.reset();
    _predGuards.reset();
    // _unrolledPreds.reset();
    // _toUnrolledPreds.reset();
    _rolledPreds.reset();
    _toRolledPreds.reset();
    _toResolvedPreds.reset();
    _resolvedPreds.reset();
    _toResolvedDistPreds.reset();
    _resolvedDistPreds.reset();
    _unresolvedPreds.reset();
    _toUnresolvedPreds.reset();
    _solvedDomains.reset();
    _solvedDomainArrs.reset();
    // updateValDomains();
  }
  
  private bool _solvedSome = false;
  void solvedSome() { _solvedSome = true; }

  void solve() {
    this._cycle += 1;
    while (// _newPreds.length > 0 ||
	   _toNewPreds.length > 0 ||
	   // _unrolledPreds.length > 0 ||
	   // _toUnrolledPreds.length > 0 ||
	   _toResolvedPreds.length > 0 ||
	   _toResolvedDistPreds.length > 0 ||
	   _toUnresolvedPreds.length > 0 ||
	   _toRolledPreds.length > 0) {
      assert (_newPreds.length == 0);
      // assert (_unrolledPreds.length == 0);
      assert (_resolvedPreds.length == 0);
      assert (_resolvedDistPreds.length == 0);

      if (_debugSolver) {
	import std.stdio;
	if (_toNewPreds.length > 0) {
	  stdout.writeln("_toNewPreds: ");
	  foreach (predicate; _toNewPreds) stdout.writeln(predicate.describe());
	}
	// if (_toUnrolledPreds.length > 0) {
	//   stdout.writeln("_toUnrolledPreds: ");
	//   foreach (predicate; _toUnrolledPreds) stdout.writeln(predicate.describe());
	// }
	if (_toResolvedPreds.length > 0) {
	  stdout.writeln("_toResolvedPreds: ");
	  foreach (predicate; _toResolvedPreds) stdout.writeln(predicate.describe());
	}
	if (_toResolvedDistPreds.length > 0) {
	  stdout.writeln("_toResolvedDistPreds: ");
	  foreach (predicate; _toResolvedDistPreds) stdout.writeln(predicate.describe());
	}
	if (_toUnresolvedPreds.length > 0) {
	  stdout.writeln("_toUresolvedPreds: ");
	  foreach (predicate; _toUnresolvedPreds) stdout.writeln(predicate.describe());
	}
	if (_toRolledPreds.length > 0) {
	  stdout.writeln("_toRolledPreds: ");
	  foreach (predicate; _toRolledPreds) stdout.writeln(predicate.describe());
	}
      }

      _solvedSome = false;
      // import std.stdio;

      // if (_newPreds.length > 0) {
      // 	writeln("Here for _newPreds: ", _newPreds.length);
      // }
      // if (_unrolledPreds.length > 0) {
      // 	writeln("Here for _unrolledPreds: ", _unrolledPreds.length);
      // }
      // if (_unresolvedPreds.length > 0) {
      // 	writeln("Here for _unresolvedPreds: ", _unresolvedPreds.length);
      // }
      // if (_toRolledPreds.length > 0) {
      // 	writeln("Here for _toRolledPreds: ", _toRolledPreds.length);
      // }

      // Predicate unrolling across array of objects may result in
      // registration of new constraints (via visitor predicates), so
      // it is important to process unrolled predicates before dealing
      // with new predicates

      _resolvedPreds.swap(_toResolvedPreds);
      _resolvedDistPreds.swap(_toResolvedDistPreds);
      _unresolvedPreds.swap(_toUnresolvedPreds);

      if (// _toUnrolledPreds.length > 0 ||
	  _toNewPreds.length > 0) {
	// _unrolledPreds.swap(_toUnrolledPreds);
	_newPreds.swap(_toNewPreds);

	// foreach (pred; _unrolledPreds) {
	//   // import std.stdio;
	//   // writeln("Setting Domain Context on Unrolled Predicate: ", pred._esdl__getName());
	//   pred.doSetDomainContext(pred);
	// }

	// foreach (pred; _newPreds) {
	//   // import std.stdio;
	//   // writeln("Setting Domain Context on new Predicate: ", pred._esdl__getName());
	//   pred.doSetDomainContext(pred);
	// }

	// foreach (pred; _unrolledPreds) procUnrolledPredicate(pred);
	foreach (pred; _newPreds) procNewPredicate(pred);

	// _unrolledPreds.reset();
	_newPreds.reset();
	solvedSome();

      }
      
      // _lap, like _cycle starts with 1
      // this is to avoid default values
      _lap += 1;

      // writeln("Lap: ", _lap);

      _rolledPreds.reset();
      _rolledPreds.swap(_toRolledPreds);

      foreach (pred; _rolledPreds) {
	if (pred._esdl__isRolled(this)) {
	  pred.markAsUnresolved(_lap);
	  _toRolledPreds ~= pred;
	}
	else {
	  _solvedSome = true;
	}
      }

      foreach (pred; _unresolvedPreds) {
	if (pred.checkResolved(this)) {
	  _solvedSome = true;
	  if (! pred.isBlocked()) {
	    pred.markResolved();
	    if (pred.isDistPredicate()) {
	      // make sure that the domain is rand
	      assert (pred._distDomain !is null);
	      if (pred._distDomain._esdl__isRand())
		_toResolvedDistPreds ~= pred;
	      else
		_toResolvedPreds ~= pred;
	    }
	    else
	      _toResolvedPreds ~= pred;
	  }
	}
	else {
	  _toUnresolvedPreds ~= pred;
	}
      }

      _unresolvedPreds.reset();
      
      foreach (pred; _toUnresolvedPreds) {
	  // import std.stdio;
	  // writeln(pred._esdl__getName(), " mark unresolved: ", _lap);
	  pred.markAsUnresolved(_lap);
      }
      
      // _resolvedDistPreds will proceed to solver
      // irrespective of whether a related predicate
      // is still not resolved
      foreach (distPred; _resolvedDistPreds) {
	_solvedSome = true;
	assert (! distPred.isBlocked());
	CstDistPredSolver agent = getDistPredSolver();
	agent.initialize(this);
	CstDomBase distDom = distPred._distDomain;
	assert (distDom !is null && ! distDom.isSolved());
	agent.distPred(distPred);
	foreach (pred; distDom._resolvedDomainPreds) {
	  if (pred.isGrouped()) assert (pred.isDistPredicate());
	  else {
	    assert (pred.isResolved() || pred.isBlocked(),
		    pred._esdl__getFullName());
	    if (pred.isEnabled() && pred.isResolved() && ! pred.isBlocked()) {
	      if (pred.isCompatWithDist(distDom))
		agent.addPredicate(pred);
	    }
	  }
	}
	agent.solve(this);
      }

      _resolvedDistPreds.reset();

      foreach (pred; _resolvedPreds) {
	if (pred.isSolved() || pred.isBlocked()  || (! pred.isInRange())) {
	  _solvedSome = true;
	  continue;
	}
	if (pred.isMarkedUnresolved(_lap)) {
	  _toResolvedPreds ~= pred;
	}
	else {
	  _solvePreds ~= pred;
	}
      }

      solvePreds();
      
      _resolvedPreds.reset();


      // Now we reset the predicates as they get added to the solve cycle
      // foreach (pred; _solvePreds) {
      // 	import std.conv: to;
      // 	assert (pred.isSolved() || pred.isBlocked() || pred.isUnrolled() ||
      // 		(! pred.isInRange()) ||	pred.isGuard(),
      // 		"Pred: " ~ pred._esdl__getName() ~ "\nState: " ~ pred._state.to!string());
      // 	pred.reset();
      // }
      
      if (_solvedSome is false) {
	import std.stdio;
	if (_toResolvedPreds.length > 0) {
	  stdout.writeln("_toResolvedPreds: ");
	  foreach (predicate; _toResolvedPreds) stdout.writeln(predicate.describe());
	}
	if (_resolvedPreds.length > 0) {
	  stdout.writeln("_resolvedPreds: ");
	  foreach (predicate; _resolvedPreds) stdout.writeln(predicate.describe());
	}
	if (_toResolvedDistPreds.length > 0) {
	  stdout.writeln("_toResolvedDistPreds: ");
	  foreach (predicate; _toResolvedDistPreds) stdout.writeln(predicate.describe());
	}
	if (_resolvedDistPreds.length > 0) {
	  stdout.writeln("_resolvedDistPreds: ");
	  foreach (predicate; _resolvedDistPreds) stdout.writeln(predicate.describe());
	}
	if (_toUnresolvedPreds.length > 0) {
	  stdout.writeln("_toUresolvedPreds: ");
	  foreach (predicate; _toUnresolvedPreds) stdout.writeln(predicate.describe());
	}
	if (_toRolledPreds.length > 0) {
	  stdout.writeln("_toRolledPreds: ");
	  foreach (predicate; _toRolledPreds) stdout.writeln(predicate.describe());
	}
	assert (false, "Infinite loop in constraint solver");
      }

    }

    foreach (iter; _itersWithCbs) iter.reset();
    _itersWithCbs.reset();

    // foreach (agent; _solvedSolvers) {
    //   agent.reset();
    //   _solvedDomains ~= agent.domains();
    //   _solvedDomainArrs ~= agent.domainArrs();
    // }
    // _solvedSolvers.reset();

    // foreach (pred; _predsThatUnrolled) {
    //   pred.reset();
    // }
    // _predsThatUnrolled.reset();
  }

  final void solvePreds() {
    // Work on _solvePreds
    foreach (pred; _solvePreds) {
      assert (! pred.isGuard());
	  
      if (pred.isSolved() || pred.isBlocked() || (! pred.isInRange())) {
	_solvedSome = true;
	continue;
      }
      pred.setProcContext(this);
	  
      // makeSolverDomains();
      uint level = 0;
      while (markDependents(++level)){
	if (_debugSolver) {
	  printSolver();
	}
	solveMarkedPreds(level);
      }
      if (_debugSolver) {
	printSolver();
      }
      if (level == 1) {
	solveAll();
      }
      else {
	solveMarkedPreds(level);
      }
      // resetLevels();

      _collatedPredicates.reset();
      _collatedDomains.reset();
      _collatedDomArrs.reset();
	  
      // }
    }

    _solvePreds.reset();
  }

  void addNewPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln("Adding: ", pred.describe());
    pred.initialize();
    _toNewPreds ~= pred;
  }

  void procNewPredicate(CstPredicate pred) {
    bool resolved = pred.tryResolveAllDeps(this);
    if (pred._iters.length == 0) {
      if (pred.isGuard()) {
	if (resolved) pred.procResolvedGuard();
	else _predGuards ~= pred;
      }
      // else if (pred.checkResolved(proc, true)) _toResolvedPreds ~= pred;
      else if (resolved) {
	pred.processResolved(this);
	if (! pred.isBlocked()) {
	  pred.markResolved();
	  if (pred.isDistPredicate()) {
	    assert (pred._distDomain !is null);
	    if (pred._distDomain._esdl__isRand())
	      _toResolvedDistPreds ~= pred;
	    else
	      _toResolvedPreds ~= pred;
	  }
	  else 
	    _toResolvedPreds ~= pred;
	}
      }
      else {
	_toUnresolvedPreds ~= pred;
      }
    }
    else {
      CstIterator iter = pred._iters[0];
      if (iter.isUnrollable()) pred.doUnroll(this);
      else {
	if (iter._iterCbs.length == 0) _itersWithCbs ~= iter;
	iter.registerRolled(pred);
      }
      // A visitor needs to move ahead since we need to have
      // a visitor to prioritize solving of array lengths
      if (pred.isVisitor()) {
	pred.markResolved();
	_toResolvedPreds ~= pred;
      }
      else
	_toRolledPreds   ~= pred;
    }
  }

  void solveMarkedPreds(uint level) {
    foreach (pred; _collatedPredicates) {
      if (! pred.isGuard() && pred.isCollated()) {
	if (pred._esdl__getOrderLevel() == level - 1 && ! (pred.isSolved)) {
	  CstSolverAgent agent = getPredSolver();
	  agent.initialize(this);
	  if (pred.isDistPredicate()) agent.markDist();
	  assert (! agent.isSolved(),
		  "Solver can not be solved when the predicate is still not solved; agent: " ~
		  agent.describe() ~ " predicate: " ~ pred.describe());
	  agent.setSolverContext(pred, level);

	  agent.solve(this);
	  _solvedDomains ~= agent.annotatedDoms();
	  _solvedDomainArrs ~= agent.annotatedDomArrs();
	  agent.reset();
	  // _solvedSolvers ~= agent;
	  _solvedSome = true;
	}
	else if (pred._esdl__getOrderLevel() == level){
	  assert( !(pred.isSolved()), "unexpected error in solving predicates");
	}
	else {
	  assert(pred.isSolved(), "unexpected error in solving predicates");
	}
      }
    }
    foreach (dom; _collatedDomains) {
      if (dom._esdl__getOrderLevel() == level){
	assert( !(dom.isSolved()), "unexpected error in solving predicates");
      }
      else if (dom._esdl__getOrderLevel() == level - 1){
	if ( !(dom.isSolved())){
	  dom.randomizeWithoutConstraints(this);
	}
      }
    }
  }

  void solveAll() {
    scope (success) {
      _solvedSome = true;
    }
    if (_collatedPredicates.length == 0) {
      return;
    }
    auto pred1 = _collatedPredicates[0];
    CstSolverAgent agent = getPredSolver();
    agent.initialize(this);
    if (pred1.isDistPredicate()) agent.markDist();
    assert (! agent.isSolved(),
	    "Solver can not be solved when the predicate is still not solved; agent: " ~
	    agent.describe() ~ " predicate: " ~ pred1.describe());
     
    foreach (pred; _collatedPredicates) {
      if (pred.isCollated()) {
	pred.sendPredToSolver(agent);
      }
    }
    agent.setOrderAndBools();
    agent.solve(this);
    _solvedDomains ~= agent.annotatedDoms();
    _solvedDomainArrs ~= agent.annotatedDomArrs();
    agent.reset();
    // _solvedSolvers ~= agent;
  }
  // void resetLevels(){
  //   foreach (elem: _collatedDomains[]){
  //     elem._orderLevel = 0;
  //   }
  //   foreach (elem: _collatedDomArrs[]){
  //     elem._orderLevel = 0;
  //   }
  // }

}
