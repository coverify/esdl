module esdl.rand.proxy;

import esdl.solver.base: CstSolver, CstDistSolverBase;
import esdl.rand.base: CstVecPrim, CstScope, CstDomBase,
  DomType, CstObjectVoid, CstVarNodeIntf, CstObjectIntf,
  CstIterator, CstDomSet, CstVarGlobIntf, CstVecNodeIntf;
import esdl.rand.pred: CstPredicate, CstPredHandler;
import esdl.rand.misc;
import esdl.data.folder;
import esdl.data.charbuf;

import std.container: Array;
import std.algorithm.searching: canFind;
import std.array;
import esdl.rand.cstx: CstParseData, CstParser;
import esdl.base.rand: _esdl__RandGen, getRandGen;


static CstParseData constraintXlate(string PROXY, string CST,
				    string FILE, size_t LINE, string NAME="") {
  CstParser parser = CstParser(CST, FILE, LINE);
  return parser.translate(PROXY, NAME);
}

abstract class _esdl__ConstraintBase: rand.disable
{
  this(_esdl__Proxy proxy, string name, string constraint) {
    _proxy = proxy;
    _name = name;
    _constraint = constraint;
  }
  immutable string _constraint;
  immutable string _name;
  protected bool _overridden = false;
  protected _esdl__Proxy _proxy;

  void markOverridden() {
    _overridden = true;
  }
  
  bool isEnabled() {
    return constraintMode() && ! _overridden;
  }

  void enable() {
    constraintMode(true);
  }

  void disable() {
    constraintMode(false);
  }

  void constraintMode(bool mode) { // overridden in derived class
    assert(false);
  }

  bool constraintMode() { // overridden in derived class
    return true;
  }

  string name() {
    return _name;
  }

  string fullName() {
    return _proxy.fullName() ~ _name;
  }

  final _esdl__Proxy getProxy() {
    return _proxy;
  }

  void _esdl__initCst() { }

  void _esdl__updateCst() { }
  
  abstract void makeConstraints();
  abstract void doSetDomainContext();
  abstract void doProcDomainContext();

  abstract CstPredicate[] getConstraintGuards();
  abstract CstPredicate[] getConstraints();
  abstract string getCode();
  abstract bool isLambdaConstraint();
  abstract bool isVisitorConstraint();

  void _esdl__doSetOuter() {
    assert (false, "Overridden in _esdl__ConstraintWithImpl");
  }
}


// struct wrapper for the main user interface
// it has to be a struct, because the user may not wait for a class object to
// constructed before he can call API methods like constraint_mode
alias constraint = Constraint;

struct Constraint(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__)
{
  enum bool _esdl__TypeHasRandBarrier = true;
  alias CstType = _esdl__Constraint!(CONSTRAINT, FILE, LINE);

  bool _mode = true;

  alias constraint_mode = constraintMode;

  void constraintMode(bool mode) {
    _mode = mode;
  }

  bool constraintMode() {
    return _mode;
  }

}

abstract class _esdl__Constraint(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__)
  : _esdl__ConstraintBase, rand.barrier
{
  import esdl.rand.vecx: CstVector;
  
  alias CstBoolVar = CstVector!(bool, rand(true, true), 0);
  
  debug(CSTPARSER) {
    pragma(msg, "/* Constraint Specification STARTS\n");
    pragma(msg, CONSTRAINT);
    pragma(msg, "\nConstraint Specification ENDS */");
    pragma(msg, "// cstDecls STARTS\n");
    pragma(msg, CST_PARSE_DATA.cstDecls);
    pragma(msg, "// cstDecls ENDS\n");
    pragma(msg, "// cstDefines STARTS\n");
    pragma(msg, CST_PARSE_DATA.cstDefines);
    pragma(msg, "// cstDefines! ENDS\n");
    pragma(msg, "// guardDecls STARTS\n");
    pragma(msg, CST_PARSE_DATA.guardDecls);
    pragma(msg, "// guardDecls! ENDS\n");
    pragma(msg, "// guardInits STARTS\n");
    pragma(msg, CST_PARSE_DATA.guardInits);
    pragma(msg, "// guardUpdts! ENDS\n");
    pragma(msg, CST_PARSE_DATA.guardUpdts);
    pragma(msg, "// guardUpdts! ENDS\n");
  }
    
  enum CstParseData CST_PARSE_DATA = constraintXlate("this.outer", CONSTRAINT, FILE, LINE);

  protected CstPredicate[] _preds;
  protected CstPredicate[] _guards;
  
  protected bool _initialized;

  this(_esdl__Proxy eng, string name) {
    super(eng, name, CONSTRAINT);
  }

  final override CstPredicate[] getConstraintGuards() {
    assert (_initialized);
    return _guards;
  }

  final override CstPredicate[] getConstraints() {
    assert (_initialized);
    return _preds;
  }

  final override void doSetDomainContext() {
    foreach (pred; _guards) pred.doSetDomainContext(pred);
    foreach (pred; _preds)  pred.doSetDomainContext(pred);
  }

  final override void doProcDomainContext() {
    foreach (pred; _guards) pred.doProcDomainContext();
    foreach (pred; _preds)  pred.doProcDomainContext();
  }

  override string getCode() {
    return CONSTRAINT;
  }

}


// template _esdl__baseHasRandomization(T) {
//   static if(is(T B == super)
// 	    && is(B[0] == class)) {
//     alias U = B[0];
//     static if(__traits(compiles, U._esdl__hasRandomization)) {
//       enum bool _esdl__baseHasRandomization = true;
//     }
//     else {
//       enum bool _esdl__baseHasRandomization = _esdl__baseHasRandomization!U;
//     }
//   }
//   else {
//     enum bool _esdl__baseHasRandomization = false;
//   }
// }
// class CstDomBasePair {
//   CstDomBase dom1;
//   CstDomBase dom2;
//   CstDomBase getFirst(){
//     return dom1;
//   }
//   CstDomBase getSecond(){
//     return dom2;
//   }
//   this( CstDomBase d1,  CstDomBase d2){
//     dom1 = d1;
//     dom2 = d2;
//   }
// }

abstract class _esdl__Proxy: CstObjectVoid, CstObjectIntf, rand.barrier
{
  // CstDomBase[] _cstRndDomains;
  CstDomBase[] _cstValDomains;

  // compositional parent -- not inheritance based
  // _esdl__Proxy _parent;
  _esdl__Proxy _root;

  private _esdl__ConstraintBase[string] _cstNames;

  void addConstraintName(_esdl__ConstraintBase cst) {
    auto cstName = cst.name();
    _esdl__ConstraintBase* prevCst = cstName in _cstNames;
    if (prevCst !is null) {
      prevCst.markOverridden();
      _cstNames[cstName] = cst;
    }
    else {
      _cstNames[cstName] = cst;
    }
  }

  // _esdl__objIntf provides the interface to the objx instance
  // would be null for root proxy
  CstObjectIntf _esdl__objIntf;

  _esdl__Proxy _esdl__getProxy() {
    return this;
  }
  
  string fullName() {
    if (_esdl__objIntf is null) return "";
    else {
      return _esdl__objIntf.fullName();
    }
  }
  string name() {
    if (_esdl__objIntf is null) return "";
    else {
      return _esdl__objIntf.name();
    }
  }
  
  bool isRand() {
    if (_esdl__objIntf is null) return true; // root proxy
    else {
      return _esdl__objIntf.isRand();
    }
  }
  
  bool inRange() {
    if (_esdl__objIntf is null) return true; // root proxy
    else {
      return _esdl__objIntf.inRange();
    }
  }

  override bool depsAreResolved() {
    if (_esdl__objIntf is null) return true; // root proxy
    else {
      return _esdl__objIntf.depsAreResolved();
    }
  }

  _esdl__Proxy unroll(CstIterator iter, ulong n) {
    if (_esdl__objIntf is null) return this;
    else {
      return _esdl__objIntf.unroll(iter, n)._esdl__getProxy();
    }
  }

  // the root proxy is always static
  bool isStatic() {
    if (_esdl__objIntf is null) return true;
    else {
      return _esdl__objIntf.isStatic();
    }
  }

  bool isReal() {
    if (_esdl__objIntf is null) return true;
    else {
      return _esdl__objIntf.isReal();
    }
  }

  bool isRolled() {
    if (_esdl__objIntf is null) return false;
    else {
      return _esdl__objIntf.isRolled();
    }
  }

  
  _esdl__Proxy getProxyRoot() {
    if (_root is null) { return this; }
    else return _root;
  }

  // CstObjNodeIntf
  final bool _esdl__isObjArray() { return false; }
  final CstIterator _esdl__iter() { return null; }
  final CstVarNodeIntf _esdl__getChild(ulong n) { assert (false); }
  void scan() { }		// when an object is unrolled


  static CstPredHandler _predHandler;

  static getPredHandler() {
    if (_predHandler is null) _predHandler = new CstPredHandler();
    return _predHandler;
  }

  static CstSolver[string] _solvers;

  CstVarGlobIntf[string] _globalLookups;

  void addGlobalLookup(CstVarGlobIntf global, string lookup) {
    assert(lookup !in _globalLookups);
    _globalLookups[lookup] = global;
  }

  CstVarGlobIntf getGlobalLookup(string lookup) {
    auto global = lookup in _globalLookups;
    if (global !is null) return *global;
    else return null;
  }

  Folder!(_esdl__ConstraintBase, "globalVisitors") _globalVisitors;

  void addGlobalVisitor(_esdl__ConstraintBase visitor) {
    _globalVisitors ~= visitor;
  }

  void setContextGlobalVisitors() {
    foreach (visitor; _globalVisitors[]) {
      visitor.doSetDomainContext();
      visitor.doProcDomainContext();
    }
  }

  _esdl__ConstraintBase[] getGlobalVisitors() {
    return _globalVisitors[];
  }

  Folder!(_esdl__ConstraintBase, "argVisitors") _argVisitors;

  void addArgVisitor(_esdl__ConstraintBase visitor) {
    _argVisitors ~= visitor;
  }

  void setContextArgVisitors() {
    foreach (visitor; _argVisitors) {
      visitor.doSetDomainContext();
      visitor.doProcDomainContext();
    }
  }

  _esdl__ConstraintBase[] getArgVisitors() {
    return _argVisitors[];
  }

  Folder!(CstPredicate, "unrolledNewPreds") _unrolledNewPreds;

  void addUnrolledNewPredicate(CstPredicate pred) {
    _unrolledNewPreds ~= pred;
  }

  void procUnrolledNewPredicates() {
    foreach (pred; _unrolledNewPreds) pred.doSetDomainContext(pred);
    foreach (pred; _unrolledNewPreds) pred.doProcDomainContext();
    _unrolledNewPreds.reset();
  }

  Folder!(CstPredicate, "predsThatUnrolled") _predsThatUnrolled;
  void registerUnrolled(CstPredicate pred) {
    _predsThatUnrolled ~= pred;
  }

  Folder!(CstPredicate, "newPreds") _newPreds;
  Folder!(CstPredicate, "toNewPreds") _toNewPreds;
  Folder!(CstPredicate, "unrolledPreds") _unrolledPreds;
  Folder!(CstPredicate, "toUnrolledPreds") _toUnrolledPreds;
  
  Folder!(CstPredicate, "rolledPreds") _rolledPreds;
  Folder!(CstPredicate, "toRolledPreds") _toRolledPreds;
  Folder!(CstPredicate, "resolvedPreds") _resolvedPreds;
  Folder!(CstPredicate, "toResolvedPreds") _toResolvedPreds;

  Folder!(CstPredicate, "toSolvePreds") _toSolvePreds;

  Folder!(CstPredicate, "_solvePreds") _solvePreds;

  Folder!(CstPredicate, "unresolvedPreds") _unresolvedPreds;
  Folder!(CstPredicate, "toUnresolvedPreds") _toUnresolvedPreds;

  // Folder!(CstPredicate, "resolvedDistPreds") _resolvedDistPreds;
  Folder!(CstPredicate, "resolvedMonoPreds") _resolvedMonoPreds;

  Folder!(CstDomBase, "solvedDomains") _solvedDomains;
  Folder!(CstDomSet, "solvedDomainArrs") _solvedDomainArrs;
  
  // Folder!(CstPredHandler, "solvedHandlers") _solvedHandlers;

  
  Folder!(CstPredicate, "collatedPredicates") _collatedPredicates;
  Folder!(CstDomBase, "collatedDomains") _collatedDomains;
  Folder!(CstDomSet, "collatedDomArrs") _collatedDomArrs;
  
  Folder!(CstVarNodeIntf, "beforeSolve") _beforeSolve;
  Folder!(CstVarNodeIntf, "afterSolve") _afterSolve;

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

  Folder!(CstVecNodeIntf, "lambdaCstDoms") _lambdaCstDoms;

  final void addLambdaCstDom(CstVecNodeIntf dom) {
    _lambdaCstDoms ~= dom;
  }

  final void doResetLambdaPreds() {
    foreach (lambdaCstDom; _lambdaCstDoms) lambdaCstDom.resetLambdaPreds();
    _lambdaCstDoms.reset();
    // reset lambda arg visitors
    _argVisitors.reset();
  }

  void printHandler (){
    import std.stdio;
    writeln("\nPreds: ");
    foreach (pred; _collatedPredicates){
      writeln(pred.name(), ", ", pred.getOrderLevel);
    }
    writeln("Doms: ");
    foreach (dom; _collatedDomains){
      writeln(dom.fullName(), ", ", dom.getOrderLevel);
    }
    writeln("DomArrs: ");
    foreach (dom; _collatedDomArrs){
      writeln(dom.fullName(), ", ", dom.getOrderLevel);
    }
  }
  
  bool markDependents(uint level){ // returns true if some domains are marked

    _beforeSolve.reset();
    _afterSolve.reset();

    foreach (dom; _collatedDomains) {

      if (dom.isSolved()) { //isSolved
	assert(level == 1 || dom.getOrderLevel < level - 1);
	continue;
      }
      
      CstVarNodeIntf [] dependents = dom.getDependents();
      
      if (dependents.length == 0) continue;
      
      foreach (domSec; _collatedDomains){
	if (domSec.isDependent(dependents)){
	  _beforeSolve ~= dom;
	  _afterSolve ~= domSec;
	  domSec.setOrder(SolveOrder.LATER);
	}
      }
      foreach (domArrSec; _collatedDomArrs){
	if (domArrSec.isDependent(dependents)){
	  _beforeSolve ~= dom;
	  _afterSolve ~= domArrSec;
	  domArrSec.setOrder(SolveOrder.LATER);
	}
      }
    }
    foreach (domArr; _collatedDomArrs) {

      if (domArr.getOrderLevel() < level-1) { //isSolved -- TBD
	continue;
      }
      
      CstVarNodeIntf [] dependents = domArr.getDependents();
      
      if (dependents.length == 0) continue;
      
      foreach (domSec; _collatedDomains){
	if (domSec.isDependent(dependents)){
	  _beforeSolve ~= domArr;
	  _afterSolve ~= domSec;
	  domSec.setOrder(SolveOrder.LATER);
	}
      }
      foreach (domArrSec; _collatedDomArrs){
	if (domArrSec.isDependent(dependents)){
	  _beforeSolve ~= domArr;
	  _afterSolve ~= domArrSec;
	  domArrSec.setOrder(SolveOrder.LATER);
	}
      }
    }

    // CstVarNodeIntf [] beforeElems;
    
    foreach (i, elem; _beforeSolve[]) {
      assert (elem.getOrderLevel() >= level - 1, "unexpected error in solve before constraints");
      assert (_afterSolve[i].getOrderLevel() >= level - 1, "unexpected error in solve before constraints");
      if (elem.getOrder() == SolveOrder.UNDECIDED) elem.setOrder(SolveOrder.NOW);
    }
    foreach (elem; _afterSolve[]) {
      elem.markOrderedAfter(level);
    }
    foreach (elem; _afterSolve[]) {
      elem.setOrder(SolveOrder.UNDECIDED);
    }
    foreach (elem; _beforeSolve[]){
      elem.setOrder(SolveOrder.UNDECIDED);
    }
    return _beforeSolve.length > 0;
  }

  // void markBase(CstDomBase base, CstDomBase dom, uint level){
  //   foreach (child; dom.getSolvedBefore()){
  //     child.markOrderedAfter(base, level);
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

  void updateValDomains() {
    foreach (dom; _cstValDomains) {
      dom.updateVal();
    }
  }
  
  _esdl__RandGen _esdl__rGen;

  _esdl__RandGen _esdl__getRandGen() {
    assert(_root is this);
    return _root._esdl__rGen;
  }

  uint _esdl__seed;
  uint _esdl__varN;

  uint indexVar() {
    return _esdl__varN++;
  }
  
  bool _esdl__seeded = false;

  uint getRandomSeed() {
    assert(_root is this);
    return _esdl__seed;
  }

  bool isRandomSeeded() {
    assert(_root is this);
    return _esdl__seeded;
  }

  void seedRandom(uint seed) {
    assert(_root is this);
    _esdl__seeded = true;
    _esdl__seed = seed;
    _esdl__rGen.seed(seed);    
  }
  
  
  // Scope for foreach
  CstScope _rootScope;
  CstScope _currentScope;

  void pushScope(CstIterator iter) {
    assert (_currentScope !is null);
    _currentScope = _currentScope.push(iter);
  }

  void popScope() {
    assert (_currentScope !is null);
    assert (_currentScope !is _rootScope);
    _currentScope = _currentScope.pop();
  }

  CstScope currentScope() {
    assert (_currentScope !is null);
    return _currentScope;
  }

  abstract bool _esdl__debugSolver();

  // Keep a list of constraints in the class
  _esdl__ConstraintBase _esdl__lambdaCst;

  _esdl__Proxy _esdl__createProxyInst(_esdl__Proxy parent,
				      CstObjectIntf obj, void* outer) {
    assert (false,
	    "Override _esdl__createProxyInst in the derived proxy class");
  }

  _esdl__Proxy _esdl__createProxyInst(_esdl__Proxy parent,
				      CstObjectIntf obj, Object outer) {
    assert (false,
	    "Override _esdl__createProxyInst in the derived proxy class");
  }

  this(_esdl__Proxy parent, CstObjectIntf obj, Object outer) {
    this(parent, obj);
  }

  this(_esdl__Proxy parent, CstObjectIntf obj, void* outer) {
    this(parent, obj);
  }

  this(_esdl__Proxy parent, CstObjectIntf obj) {
    _esdl__objIntf = obj;
    import std.random: Random, uniform;
    debug(NOCONSTRAINTS) {
      assert(false, "Constraint engine started");
    }
    else {
      import esdl.base.core: Procedure;
      auto proc = Procedure.self;
      if (proc !is null) {
	_esdl__seed = 0; // uniform!(uint)(procRgen);
      }
      else {
	// no active simulation -- use global rand generator
	_esdl__seed = 0; // uniform!(uint)();
      }
    }
    _esdl__rGen = new _esdl__RandGen(_esdl__seed);

    if (parent is null) {
      _root = this;
    }
    else {
      _root = parent.getProxyRoot();
    }
    // scopes for constraint parsing
    _rootScope = new CstScope(null, null);
    _currentScope = _rootScope;

  }

  // overridden by Randomization mixin -- see meta.d
  abstract void _esdl__doRandomize(_esdl__RandGen randGen);
  abstract void _esdl__doConstrain(_esdl__Proxy proxy, bool callPreRandomize);


  void reset() {
    // _solvedDomains is from previous cycle
    foreach (dom; _solvedDomains) {
      dom.reset();
    }
    foreach (domArr; _solvedDomainArrs) {
      domArr.reset();
    }
    // reset all bins
    _newPreds.reset();
    _toNewPreds.reset();
    _unrolledPreds.reset();
    _toUnrolledPreds.reset();
    _rolledPreds.reset();
    _toRolledPreds.reset();
    _resolvedPreds.reset();
    _toResolvedPreds.reset();
    _toSolvePreds.reset();
    _unresolvedPreds.reset();
    _toUnresolvedPreds.reset();
    // _resolvedDistPreds.reset();
    _resolvedMonoPreds.reset();
    _solvedDomains.reset();
    _solvedDomainArrs.reset();
    updateValDomains();
  }
  
  private bool _solvedSome = false;
  void solvedSome() { _solvedSome = true; }

  void solve() {
    assert(_root is this);
    this._cycle += 1;
    while (// _newPreds.length > 0 ||
	   _toNewPreds.length > 0 ||
	   // _unrolledPreds.length > 0 ||
	   _toUnrolledPreds.length > 0 ||
	   // _resolvedMonoPreds.length > 0 ||
	   // _resolvedPreds.length > 0 ||
	   _toResolvedPreds.length > 0 ||
	   _toUnresolvedPreds.length > 0 ||
	   _toRolledPreds.length > 0) {
      assert (_newPreds.length == 0);
      assert (_unrolledPreds.length == 0);
      assert (_resolvedPreds.length == 0);

      if (_esdl__debugSolver) {
	import std.stdio;
	if (_toNewPreds.length > 0) {
	  stdout.writeln("_toNewPreds: ");
	  foreach (predicate; _toNewPreds) stdout.writeln(predicate.describe());
	}
	if (_toUnrolledPreds.length > 0) {
	  stdout.writeln("_toUnrolledPreds: ");
	  foreach (predicate; _toUnrolledPreds) stdout.writeln(predicate.describe());
	}
	if (_toResolvedPreds.length > 0) {
	  stdout.writeln("_toResolvedPreds: ");
	  foreach (predicate; _toResolvedPreds) stdout.writeln(predicate.describe());
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
      // if (_resolvedPreds.length > 0) {
      // 	writeln("Here for _resolvedPreds: ", _resolvedPreds.length);
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
      _unresolvedPreds.swap(_toUnresolvedPreds);

      if (_toUnrolledPreds.length > 0 || _toNewPreds.length > 0) {
	_unrolledPreds.swap(_toUnrolledPreds);
	_newPreds.swap(_toNewPreds);

	// foreach (pred; _unrolledPreds) {
	//   // import std.stdio;
	//   // writeln("Setting Domain Context on Unrolled Predicate: ", pred.name());
	//   pred.doSetDomainContext(pred);
	// }

	// foreach (pred; _newPreds) {
	//   // import std.stdio;
	//   // writeln("Setting Domain Context on new Predicate: ", pred.name());
	//   pred.doSetDomainContext(pred);
	// }

	foreach (pred; _unrolledPreds) procUnrolledPredicate(pred);
	foreach (pred; _newPreds) procNewPredicate(pred);

	_unrolledPreds.reset();
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
	if (pred.isRolled()) {
	  pred.markAsUnresolved(_lap);
	  _toRolledPreds ~= pred;
	}
	else {
	  _solvedSome = true;
	}
      }

      foreach (pred; _unresolvedPreds) {
	if (pred.predDepsAreResolved()) {
	  procResolved(pred);
	  _solvedSome = true;
	}
	else {
	  _toUnresolvedPreds ~= pred;
	}
      }

      _unresolvedPreds.reset();
      
      foreach (pred; _toUnresolvedPreds) {
	  // import std.stdio;
	  // writeln(pred.name(), " mark unresolved: ", _lap);
	  pred.markAsUnresolved(_lap);
      }
      
      
      // now the normal _resolvedPreds
      _resolvedPreds.swap(_toSolvePreds);
      
      foreach (pred; _toSolvePreds) {
	if (pred.isMarkedUnresolved(_lap)) {
	  _toResolvedPreds ~= pred;
	}
	else {
	  _solvePreds ~= pred;
	}
      }

      _toSolvePreds.reset();

       // Work on _solvePreds
      foreach (pred; _solvePreds) {
	if (! pred.isGuard()) {
	  if (pred.isSolved() || pred.isBlocked() || (! pred.isInRange())) {
	    _solvedSome = true;
	    continue;
	  }
	  pred.setProxyContext(this);
	  
	  // makeHandlerDomains();
	  uint level = 0;
	  while (markDependents(++level)){
	    if (_esdl__debugSolver) {
	      printHandler();
	    }
	    solveMarkedPreds(level);
	  }
	  if (_esdl__debugSolver) {
	    printHandler();
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
	  
	}
      }

      // Now we reset the predicates as they get added to the solve cycle
      // foreach (pred; _solvePreds) {
      // 	import std.conv: to;
      // 	assert (pred.isSolved() || pred.isBlocked() || pred.isUnrolled() ||
      // 		(! pred.isInRange()) ||	pred.isGuard(),
      // 		"Pred: " ~ pred.name() ~ "\nState: " ~ pred._state.to!string());
      // 	pred.reset();
      // }
      
      if (_solvedSome is false) {
	import std.stdio;
	// if (_resolvedDistPreds.length > 0) {
	//   stdout.writeln("_resolvedDistPreds: ");
	//   foreach (predicate; _resolvedDistPreds) stdout.writeln(predicate.describe());
	// }
	// if (_resolvedMonoPreds.length > 0) {
	//   stdout.writeln("_resolvedMonoPreds: ");
	//   foreach (predicate; _resolvedMonoPreds) stdout.writeln(predicate.describe());
	// }
	if (_toResolvedPreds.length > 0) {
	  stdout.writeln("_toResolvedPreds: ");
	  foreach (predicate; _toResolvedPreds) stdout.writeln(predicate.describe());
	}
	if (_resolvedPreds.length > 0) {
	  stdout.writeln("_resolvedPreds: ");
	  foreach (predicate; _resolvedPreds) stdout.writeln(predicate.describe());
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

      _solvePreds.reset();

    }
    // foreach (handler; _solvedHandlers) {
    //   handler.reset();
    //   _solvedDomains ~= handler.domains();
    //   _solvedDomainArrs ~= handler.domainArrs();
    // }
    // _solvedHandlers.reset();

    foreach (pred; _predsThatUnrolled) {
      pred.reset();
    }
    _predsThatUnrolled.reset();
  }

  // CstDomBase solveDist(CstPredicate pred) {
  //   if (_esdl__debugSolver) {
  //     import std.stdio;
  //     writeln("Solving Dist Predicate: ", pred.describe());
  //   }
  //   CstDomBase distDom = pred.distDomain();
  //   CstPredicate[] distPreds = distDom._unresolvedDomainPreds();
  //   // long[] toRemove;
  //   CstDistSolverBase dist = pred._expr.getDist();
  //   dist.reset();
  //   foreach (predicate; distPreds){
  //     CstVecTerm ex = predicate._expr.isCompatWithDist(distDom);
  //     // isCompatWithDist returns rhs if the predicate is of != type,
  //     // otherwise it returns null
  //     if (predicate.getUnresolvedRnds().length == 1 && ! predicate.isDist()) {
  // 	if (ex is null) {
  // 	  assert (false, "can only use != operator on distributed domains");
  // 	}
  // 	dist.purge(ex.evaluate());
  //     }
  //   }
  //   dist.uniform(distDom, _esdl__getRandGen());
  //   return distDom;
  // }

  void procResolved(CstPredicate pred) {
    // assert (pred._unresolvedRnds.length > 0 || pred._unresolvedRndArrs.length > 0 || pred.isGuard(),
    // 	    pred.describe());
    // if (pred.isDist()) {
    //   _resolvedDistPreds ~= pred;
    // }
    // // else if (pred._unresolvedRnds.length == 1 &&
    // // 	     pred._unresolvedRndArrs.length == 0 &&
    // // 	     pred._unresolvedRnds[0]._type <= DomType.LAZYMONO//  &&
    // // 	     // pred._unresolvedRnds[0]._esdl__parentIsConstrained() is false
    // // 	     ) {
    // //   _resolvedMonoPreds ~= pred;
    // //   // procMonoDomain(pred._unresolvedRnds[0], pred);
    // // }
    // else
    pred.processResolved();
    if (pred.isGuard()) pred.procResolvedGuard();
    else               _toResolvedPreds ~= pred;
  }

  void addNewPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln("Adding: ", pred.describe());
    pred.initialize();
    _toNewPreds ~= pred;
  }

  void addUnrolledPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln("Adding : ", pred.name());
    pred.initialize();
    _toUnrolledPreds ~= pred;
  }

  void procNewPredicate(CstPredicate pred) {
    pred.tryResolveDeps(this);
    if (pred.isVisitor()) {
      procResolved(pred);
    }
    else if (pred._iters.length > 0) {
      _toRolledPreds ~= pred;
    }
    else if (pred._deps.length > 0) {
      bool allDepsResolved = true;
      foreach (dep; pred._deps) {
	if (! dep.isResolved()) {
	  allDepsResolved = false;
	  break;
	}
      }
      if (allDepsResolved) {
	// import std.stdio;
	// writeln("All Deps resolved: ", pred.name());
	procResolved(pred);
      }
      else _toUnresolvedPreds ~= pred;
    }
    else {
      procResolved(pred);
    }
  }

  void procUnrolledPredicate(CstPredicate pred) {
    pred.tryResolveDeps(this);
    if (pred.isVisitor()) {
      procResolved(pred);
    }
    else if (pred._iters.length == 0) {
      if (pred.predDepsAreResolved(true)) {
	// import std.stdio;
	// writeln("Predicate marked as resolved: ", pred.name());
	procResolved(pred);
      }
      else {
	_toUnresolvedPreds ~= pred;
      }
    }
    else {
      _toRolledPreds ~= pred;
    }
  }

  void solveMarkedPreds(uint level) {
    foreach (pred; _collatedPredicates) {
      if (! pred.isGuard() && pred.isCollated()) {
	if (pred.getOrderLevel() == level - 1 && ! (pred.isSolved)) {
	  CstPredHandler handler = null;
	  if (handler is null) {
	    handler = getPredHandler();
	    handler.initialize(this);
	    // if (_esdl__debugSolver) {
	    //   import std.stdio;
	    //   writeln("Created new handler ", handler._id, " for predicate: ", pred.describe());
	    // }
	  }
	  // else if (_esdl__debugSolver) {
	  //   import std.stdio;
	  //   writeln("Reuse handler ", handler._id, " for predicate: ", pred.describe());
	  // }
	  if (pred.withDist()) handler.markDist();
	  assert (! handler.isSolved(),
		  "Handler can not be solved when the predicate is still not solved; handler: " ~
		  handler.describe() ~ " predicate: " ~ pred.describe());
	  handler.setBatchContext(pred, level);

	  handler.solve();
	  _solvedDomains ~= handler.domains();
	  _solvedDomainArrs ~= handler.domainArrs();
	  handler.reset();
	  // _solvedHandlers ~= handler;
	  _solvedSome = true;
	}
	else if (pred.getOrderLevel() == level){
	  assert( !(pred.isSolved()), "unexpected error in solving predicates");
	}
	else {
	  assert(pred.isSolved(), "unexpected error in solving predicates");
	}
      }
    }
    foreach (dom; _collatedDomains) {
      if (dom.getOrderLevel() == level){
	assert( !(dom.isSolved()), "unexpected error in solving predicates");
      }
      else if (dom.getOrderLevel() == level - 1){
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
    CstPredHandler handler = null;
    if (handler is null) {
      handler = getPredHandler();
      handler.initialize(this);
      // if (_esdl__debugSolver) {
      // 	import std.stdio;
      // 	writeln("Created new handler ", handler._id, " for predicate: ", pred1.describe());
      // }
    }
    // else if (_esdl__debugSolver) {
    //   import std.stdio;
    //   writeln("Reuse handler ", handler._id, " for predicate: ", pred1.describe());
    // }
    if (pred1.withDist()) handler.markDist();
    assert (! handler.isSolved(),
	    "Handler can not be solved when the predicate is still not solved; handler: " ~
	    handler.describe() ~ " predicate: " ~ pred1.describe());
     
    foreach (pred; _collatedPredicates) {
      if (pred.isCollated()) {
	pred.sendPredToHandler(handler);
      }
    }
    handler.setOrderAndBools();
    handler.solve();
    _solvedDomains ~= handler.domains();
    _solvedDomainArrs ~= handler.domainArrs();
    handler.reset();
    // _solvedHandlers ~= handler;
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
