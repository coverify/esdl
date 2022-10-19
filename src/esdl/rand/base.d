module esdl.rand.base;

import std.traits: isIntegral, isBoolean;
import std.algorithm: canFind;
import std.random: uniform;
import std.range: isRandomAccessRange;

import esdl.solver.base;

import esdl.rand.domain: CstVecValue;
import esdl.rand.expr: CstVecArrExpr, CstVecSliceExpr, CstRangeExpr,
  CstInsideSetElem, CstVec2LogicExpr, CstLogic2LogicExpr, CstVec2VecExpr,
  CstNotLogicExpr, CstNegVecExpr, CstInsideArrExpr;
import esdl.rand.pred: CstPredicate, Hash;
import esdl.rand.agent: CstSolverAgent;
import esdl.rand.proxy: _esdl__Proxy, _esdl__CstProcessor;
import esdl.rand.misc: CstVectorOp, CstLogicOp, CstCompareOp,
  CstBinaryOp, SolveOrder, DomainContextEnum, CstVecType, _esdl__Sigbuf;

import esdl.base.rand: _esdl__RandGen, getRandGen;

import esdl.data.bvec: isBitVector;
import esdl.data.vector;

interface CstVarNodeIntf {
  bool _esdl__isRand();
  _esdl__Proxy _esdl__getRootProxy();
  string _esdl__getName();
  string _esdl__getFullName();
  bool _esdl__isDomainInRange();
  void _esdl__setOrder(SolveOrder order);
  SolveOrder _esdl__getOrder();
  uint _esdl__getOrderLevel();
  void _esdl__markOrderedAfter(uint level);

  CstVarNodeIntf _esdl__getResolvedNode(_esdl__CstProcessor proc);
  bool _esdl__depsAreResolved();
  
  bool _esdl__isObjArray();
  CstIterator _esdl__iter();
  CstVarNodeIntf _esdl__getChild(ulong n);
  void _esdl__scan(_esdl__CstProcessor proc);			// when an object is unrolled
}

interface CstDepIntf {
  string _esdl__getName();
  string _esdl__getFullName();

  abstract bool hasChanged();

  abstract void registerIdxPred(CstDepCallback idxCb);
  abstract void registerDepPred(CstDepCallback depCb);
  abstract bool isDepResolved();
  abstract bool tryResolveDep(_esdl__CstProcessor proc);

  abstract CstDomBase getDomain();
}

interface CstVecNodeIntf: CstVarNodeIntf, CstDepIntf {

  // This function is used in setDomainArrContext to register all the
  // predicates with the domain variables that this predicate
  // constrains
  abstract void registerRndPred(CstPredicate rndPred, _esdl__CstProcessor proc);  

  abstract void setSolverContext(CstSolverAgent agent);
  abstract void setProcContext(_esdl__CstProcessor proc);
  abstract void reset();

  abstract void resetLambdaPreds();
}

interface CstVectorIntf: CstVecNodeIntf { }

interface CstVecArrIntf: CstVecNodeIntf {
  CstDomBase _esdl__nthLeaf(uint idx);
  uint _esdl__leafsCount();

  struct Range {
    CstVecArrIntf _arr;
    uint _idx;
    uint _size;

    this(CstVecArrIntf arr) {
      _arr = arr;
      _idx = 0;
      _size = _arr._esdl__leafsCount();
    }

    bool empty() {
      return _size == 0;
    }

    void popFront() {
      _idx += 1;
      _size -= 1;
    }

    CstDomBase front() {
      return _arr._esdl__nthLeaf(_idx);
    }

    uint length() {
      return _size;
    }
  }

  final Range opSlice() {
    return Range(this);
  }

}

interface CstObjNodeIntf: CstVarNodeIntf {}

interface CstObjectIntf: CstObjNodeIntf
{
  string _esdl__getFullName();
  string _esdl__getName();
  bool _esdl__isRand();
  bool _esdl__isDomainInRange();
  CstObjectIntf _esdl__unroll(CstIterator iter, ulong n,
			      _esdl__CstProcessor proc);
  _esdl__Proxy _esdl__getProxy();
  bool _esdl__isStatic();
  bool _esdl__isReal();
  bool _esdl__isRolled(_esdl__CstProcessor proc);
}

interface CstObjArrIntf: CstObjNodeIntf {

  CstObjectIntf _esdl__nthLeaf(uint idx);
  uint _esdl__leafsCount();

  struct Range {
    CstObjArrIntf _arr;
    uint _idx;
    uint _size;

    this(CstObjArrIntf arr) {
      _arr = arr;
      _idx = 0;
      _size = _arr._esdl__leafsCount();
    }

    bool empty() {
      return _size == 0;
    }

    void popFront() {
      _idx += 1;
      _size -= 1;
    }

    auto front() {
      return _arr._esdl__nthLeaf(_idx);
    }

    auto length() {
      return _size;
    }
  }

  final Range opSlice() {
    return Range(this);
  }

}

interface CstVarGlobIntf
{
  void _esdl__fixRef();
}

abstract class CstObjectStubBase { }
abstract class CstObjArrStubBase { }

abstract class CstObjectVoid: CstObjVoid { }
abstract class CstObjArrVoid: CstObjVoid { }

abstract class CstVectorVoid: CstVecVoid { }
abstract class CstVecArrVoid: CstVecVoid { }

abstract class CstObjVoid: CstVarVoid { }
abstract class CstVecVoid: CstVarVoid { }
abstract class CstVarVoid { }

class CstScope {
  this(CstScope parent, CstIterator iter) {
    _parent = parent;
    _iter = iter;
    if (_parent !is null) parent._children ~= this;
    if (_parent is null) _level = 0;
    else _level = _parent.getLevel() + 1;
  }

  bool isRelated(CstDepIntf dep) {
    if (_parent && _parent.isRelated(dep)) return true;
    else if (_iter is null) return false;
    else if (_iter.getLenVec == dep) return true;
    else return false;
  }
  
  CstScope pop() {
    return _parent;
  }

  CstScope push(CstIterator iter) {
    CstScope childScope;
    foreach (child; _children) {
      if (child._iter is iter) {
	childScope = child;
	break;
      }
    }
    if (childScope is null) {
      childScope = new CstScope(this, iter);
    }
    return childScope;
  }

  uint getLevel() {
    return _level;
  }

  void getIterators(T)(ref T iters, uint level) {
    if (_level == level) return;
    else {
      assert (_iter !is null);
      assert (_parent !is null);
      _parent.getIterators(iters, level);
      iters ~= _iter;
    }
  }

  CstScope _parent;
  CstScope[] _children;
  CstIterator _iter;
  uint _level;

  string describe() {
    import std.string: format;
    string description = format("Scope:\n\tLevel: %s\n\tIter: %s\n",
				_level, (_iter is null) ?
				"NONE" : _iter._esdl__getName());
    return description;
  }
}

enum DomDistEnum: ubyte
{   NONE = 0,
    DETECT = 1,
    PROPER = 2
    }

abstract class CstDomBase: CstVecVoid, CstTerm, CstVectorIntf
{

  public enum State: ubyte { INIT, COLLATED, GROUPED, SOLVED }

  uint         _domN = uint.max;
  uint         _varN = uint.max;


  _esdl__Proxy _root;

  string _esdl__name;

  this(string name, _esdl__Proxy root) {
    _esdl__name = name;
    _root = root;
  }

  string _esdl__getName() {
    return _esdl__name;
  }

  // Dependencies
  CstDepIntf[] _deps;

  void addDep(CstDepIntf dep) { if (! _deps.canFind(dep)) _deps ~= dep; }
  CstDepIntf[] getDeps() { return _deps; }
  
  abstract string _esdl__getFullName();
  // abstract void collate(ulong v, int word=0);
  abstract void setVal(ulong[] v, _esdl__CstProcessor proc);
  abstract void setVal(ulong v, _esdl__CstProcessor proc);

  abstract bool isBool();
  abstract void setBool(bool v, _esdl__CstProcessor proc);
  abstract bool getBool();
  
  // abstract uint domIndex();
  // abstract void domIndex(uint s);
  abstract bool _esdl__isRand();
  abstract bool signed();
  abstract uint bitcount();
  abstract _esdl__Proxy _esdl__getRootProxy();
  abstract void _esdl__doRandomize(_esdl__RandGen randGen);
  abstract CstDomBase _esdl__getResolvedNode(_esdl__CstProcessor proc);
  abstract bool updateVal(_esdl__CstProcessor proc);
  abstract bool hasChanged();
  abstract bool _esdl__isStatic();
  abstract bool _esdl__isRolled(_esdl__CstProcessor proc);
  // abstract void registerRndPred(CstPredicate rndPred, _esdl__CstProcessor proc);
  abstract CstDomSet getParentDomSet();
  abstract long evaluate();

  override void _esdl__markOrderedAfter(uint level) {
    if (_orderLevel == level) return;
    assert (_orderLevel == level - 1);
    _orderLevel = level;
    CstPredicate[] preds = _resolvedDomainPreds[];
    foreach (pred; preds){
      if (pred._esdl__getOrderLevel() < level) {
	assert(pred._esdl__getOrderLevel() == level - 1, "unexpected error in ordering");
	pred._esdl__setOrderLevel(level);
	CstDomBase[] doms = pred.getUnresolvedRnds();
	foreach (dom; doms) {
	  if (dom._orderVar != SolveOrder.NOW && !dom.isSolved()) {
	    dom._esdl__markOrderedAfter(level);
	  }
	}
	CstDomSet[] domArrs = pred.getUnresolvedRndArrs();
	foreach (domArr; domArrs) {
	  if (domArr._orderVar != SolveOrder.NOW ) {
	    domArr._esdl__markOrderedAfter(level);
	  }
	}
      }
    }
  }

  uint _orderLevel = 0;
      
  override uint _esdl__getOrderLevel(){
    return _orderLevel;
  }

  void _esdl__setOrderLevel(uint lev){
    _orderLevel = lev;
  }

  // CstVarNodeIntf [] _solvedAfter;
  // CstVarNodeIntf [] getSolvedAfter() {
  //   return _solvedAfter;
  // }
  // void addSolvedAfter(CstVarNodeIntf dependent){
  //   _solvedAfter ~= dependent;
  // }
  // CstVarNodeIntf [] _solvedBefore;
  // CstVarNodeIntf [] getSolvedBefore() {
  //   return _solvedBefore;
  // }
  // void addSolvedBefore(CstVarNodeIntf dependent){
  //   _solvedBefore ~= dependent;
  // }
  
  SolveOrder _orderVar = SolveOrder.UNDECIDED;
  
  override void _esdl__setOrder(SolveOrder order){
    _orderVar = order;
  }

  override SolveOrder _esdl__getOrder() {
    return _orderVar;
  }
  // abstract void registerVarPred(CstPredicate varPred);  
  // abstract void registerDepPred(CstDepCallback depCb);
  // abstract void registerIdxPred(CstDepCallback idxCb);

  // CstVecNodeIntf
  final bool _esdl__isVecArray() {return false;}
  final CstIterator _esdl__iter() {return null;}
  final CstVarNodeIntf _esdl__getChild(ulong n) {assert (false);}

  // normally null, unless the domain has a dist constraint
  CstPredicate _distPredicate;

  final CstPredicate getDistPred() { return _distPredicate; }
  final void setDistPred(CstPredicate pred) { _distPredicate = pred; }
  
  abstract long value();
  
  bool tryResolveDep(_esdl__CstProcessor proc) {
    //
    // import std.stdio;
    // writeln("Trying to Resolve: ", this._esdl__getFullName());
    import std.algorithm.iteration: filter;
    if (! this._esdl__depsAreResolved()) {
      // this dependency itself has unresolved dependencies
      return false;
    }
    else { // deps are resolved, so _esdl__getResolvedNode will not fail
      auto resolved = this._esdl__getResolvedNode(proc);
      if (resolved.isDepResolved()) {
	// if (resolved !is this) resolved.execCbs(proc);
	// this.markSolved(proc);
	return true;
      }
      else {
	if (resolved is this) {
	  if (_unresolvedDomainPreds.length + _lambdaDomainPreds.length == 0 ||
	      (_unresolvedDomainPreds[].filter!(pred => ! pred.isGuard()).empty() &&
	       _lambdaDomainPreds[].filter!(pred => ! pred.isGuard()).empty())) {
	    randomizeWithoutConstraints(proc);
	    return true;
	  }
	}
	else {
	  if (resolved._unresolvedDomainPreds.length + this._unresolvedDomainPreds.length +
	      resolved._lambdaDomainPreds.length + this._lambdaDomainPreds.length == 0 ||
	      (_unresolvedDomainPreds[].filter!(pred => ! pred.isGuard()).empty() &&
	       resolved._unresolvedDomainPreds[].filter!(pred => ! pred.isGuard()).empty() &&
	       _lambdaDomainPreds[].filter!(pred => ! pred.isGuard()).empty() &&
	       resolved._lambdaDomainPreds[].filter!(pred => ! pred.isGuard()).empty())) {
	    // we point to resolved node inside randomizeWithoutConstraints
	    randomizeWithoutConstraints(proc);
	    return true;
	  }
	}
      }
      return false;
    }
  }
  
  void randomizeWithoutConstraints(_esdl__CstProcessor proc) {
    assert (this._esdl__depsAreResolved());
    auto resolved = this._esdl__getResolvedNode(proc);
    if (this._esdl__isRand())
      resolved._esdl__doRandomize(proc.getRandGen());
    proc.solvedSome();
    resolved.markSolved(proc);
    proc.addSolvedDomain(resolved);
    if (this !is resolved) {
      this.markSolved(proc);
      proc.addSolvedDomain(this);
    }
  }

  void markSolved(_esdl__CstProcessor proc) {
    if (_state == State.SOLVED) return;
    if (proc.debugSolver()) {
      import std.stdio;
      writeln("Marking ", this._esdl__getName(), " as SOLVED");
    }
    // _resolvedDomainPreds.reset(); // now done in reset()
    assert (_state != State.SOLVED, this._esdl__getName() ~
	    " already marked as solved");
    _state = State.SOLVED;
    proc.addSolvedDomain(this);
    this.execCbs(proc);
  }

  bool isMarkedSolved() {
    return _state == State.SOLVED;
  }
  
  final override bool isDepResolved() {
    return isSolved();
  }

  final bool isSolved() {
    if (_esdl__isRand()) {
      if (_state == State.SOLVED) return true;
      else return false;
    }
    else return true;
  }

  CstVarNodeIntf[] _dependents;

  void orderBefore(CstVarNodeIntf a){
    _dependents ~= a;
  }

  auto getOrdered(){
    return _dependents;
  }

  final CstVarNodeIntf[] getDependents(){
    if (getParentDomSet !is null) {
      return getOrdered() ~ getParentDomSet().getDependents();
    }
    else return getOrdered();
  }

  final bool isDependent(CstVarNodeIntf [] depArr){
    import std.algorithm.searching : canFind;
    if (getParentDomSet() is null) return depArr.canFind(this);
    else return (depArr.canFind(this) || getParentDomSet().isDependent(depArr));
  }
      
  

  // Callbacks
  Vector!(CstDepCallback, "depCbs") _depCbs;

  Vector!(CstPredicate, "resolvedDomainPreds") _resolvedDomainPreds;
  Vector!(CstPredicate, "unresolvedDomainPreds") _unresolvedDomainPreds;
  Vector!(CstPredicate, "lambdaDomainPreds") _lambdaDomainPreds;

  final void addResolvedPred(CstPredicate pred) {
    _resolvedDomainPreds ~= pred;
  }
  
  final void addUnresolvedPred(CstPredicate pred) {
    _unresolvedDomainPreds ~= pred;
  }
  
  final void addLambdaPred(CstPredicate pred) {
    _lambdaDomainPreds ~= pred;
  }
  
  override void registerRndPred(CstPredicate rndPred, _esdl__CstProcessor proc) {
    if (rndPred.isLambdaPred()) {
      if (! _lambdaDomainPreds[].canFind(rndPred)) {
	assert (proc !is null);
	_lambdaDomainPreds ~= rndPred;
	proc._esdl__addLambdaCstDom(this);
      }
    }
    else {
      if (! _unresolvedDomainPreds[].canFind(rndPred)) {
	_unresolvedDomainPreds ~= rndPred;
      }
    }
  }
  
  void purgeRndPred(CstPredicate pred) {
    // import std.stdio;
    // writeln("Removing pred: ", pred.describe());
    import std.algorithm: countUntil;
    if (pred.isLambdaPred()) {
      auto index = countUntil(_lambdaDomainPreds[], pred);
      if (index >= 0) {
	_lambdaDomainPreds[index] = _lambdaDomainPreds[$-1];
	_lambdaDomainPreds.length = _lambdaDomainPreds.length - 1;
      }
    }
    else {
      auto index = countUntil(_unresolvedDomainPreds[], pred);
      if (index >= 0) {
	_unresolvedDomainPreds[index] = _unresolvedDomainPreds[$-1];
	_unresolvedDomainPreds.length = _unresolvedDomainPreds.length - 1;
      }
    }
  }

  final override void resetLambdaPreds() {
    _lambdaDomainPreds.reset();
  }

  // CstSolverAgent _agent;

  // CstSolverAgent agent() {
  //   return _agent;
  // }

  uint annotation() {
    return _domN;
  }

  void setAnnotation(uint n) {
    // import std.stdio;
    // writeln("Domain: ", _esdl__getName(), " setAnnotation: ", n);
    _domN = n;
  }
  
  final void annotate(CstSolverAgent agent, _esdl__CstProcessor proc) {
    this._esdl__getResolvedNode(proc).annotateResolved(agent, proc);
  }

  final void annotateResolved(CstSolverAgent agent, _esdl__CstProcessor proc) {
    assert (this is this._esdl__getResolvedNode(proc));
    // import std.conv: to;
    // import std.stdio;
    // writeln("annotate: ", this._esdl__getName());
    if (_domN == uint.max) {
      if (_varN == uint.max) _varN = agent.getAnnotationIndex();
      if (this.isSolved()) setAnnotation(agent.addAnnotatedVar(this));
      else setAnnotation(agent.addAnnotatedDom(this));
    }
    // writeln("annotate: ", _varN.to!string());
    // writeln("annotate: ", _domN.to!string());
  }

  override bool _esdl__isDomainInRange() {
    assert(false, "_esdl__isDomainInRange is not defined for: " ~ _esdl__getName());
  }

  void setProcContext(_esdl__CstProcessor proc) {
    // import std.stdio;
    // writeln("setProcContext on: ", this._esdl__getName());
    assert (_state is State.INIT && (! this.isSolved()));
    proc.collateDomain(this);
    // assert (_agent is null && (! this.isSolved()));
    // _agent = agent;
    if (this._esdl__isRand()) {
      foreach (pred; _resolvedDomainPreds) {
	if (pred.isEnabled() && pred.isResolved() && ! pred.isBlocked()) {
	  pred.setProcContext(proc);
	}
      }
      if (_esdl__parentIsConstrained()) {
	CstDomSet parent = getParentDomSet();
	// writeln("setProcContext on parent: ", parent._esdl__getName());
	assert (parent !is null);
	if (parent._state is CstDomSet.State.INIT) {
	  parent.setProcContext(proc);
	}
      }
    }
  }
  
  void setSolverContext(CstSolverAgent agent, uint level) {
    assert (_state is State.COLLATED &&
	    (! this.isSolved()) && _esdl__getOrderLevel() == level - 1);
    _state = State.GROUPED;
    if (this._esdl__isRand()) {
      foreach (pred; _resolvedDomainPreds) {
  	if (pred.isEnabled() &&
	    pred.isCollated() &&
	    pred._esdl__getOrderLevel == level - 1) {
  	  pred.setSolverContext(agent, level);
  	}
      }
      if (_esdl__parentIsConstrained()) {
  	CstDomSet parent = getParentDomSet();
  	assert (parent !is null);
  	if (parent._state is CstDomSet.State.INIT ||
	    parent._state is CstDomSet.State.COLLATED) {
  	  parent.setSolverContext(agent, level);
  	}
      }
    }
  }

  // abstract void annotate(CstSolverAgent agent, _esdl__CstProcessor proc);
  abstract bool visitDomain(CstSolver solver);
  
  // init value has to be different from proxy._cycle init value
  uint _cycle = -1;
  State _state;

  uint _unresolveLap;

  override void reset() {
    _resolvedDomainPreds.reset();
    _state = State.INIT;
    _orderVar = SolveOrder.UNDECIDED;
    _orderLevel = 0;
    _depCbs.reset();
  }
  

  final void markAsUnresolved(uint lap) {
    if (_unresolveLap != lap) {
      _unresolveLap = lap;
      CstDomSet parent = getParentDomSet();
      if (parent !is null)
	parent.markAsUnresolved(lap, false);
      foreach (pred; _unresolvedDomainPreds)
	pred.markAsUnresolved(lap);
      foreach (pred; _lambdaDomainPreds)
	pred.markAsUnresolved(lap);
    }
  }

  void execCbs(_esdl__CstProcessor proc) {
    execIterCbs(proc);
    execDepCbs(proc);
  }

  void execIterCbs(_esdl__CstProcessor proc) { }
  void execDepCbs(_esdl__CstProcessor proc) {
    // import std.stdio;
    // writeln("domain: ", this._esdl__getFullName());
    foreach (cb; _depCbs) {
      // writeln(cb._esdl__getFullName());
      cb.doResolve(proc);
    }
  }

  override void registerDepPred(CstDepCallback depCb) {
    // if (! _depCbs[].canFind(depCb))
    _depCbs ~= depCb;
  }

  override void registerIdxPred(CstDepCallback idxCb) {
    // if (! _depCbs[].canFind(idxCb))
    _depCbs ~= idxCb;
  }

  abstract bool _esdl__parentIsConstrained();
  abstract string describe(bool descExpr=false);

  void _esdl__scan(_esdl__CstProcessor proc) { }
  CstDomBase getDomain() { return this; }

  final void visit(CstSolver solver, _esdl__CstProcessor proc) {
    solver.pushToEvalStack(this._esdl__getResolvedNode(proc));
  }

}

abstract class CstValue: CstTerm
{
  bool isConst() { return true; }

  bool isIterator() { return false; }


  CstValue _esdl__unroll(CstIterator iters, ulong n,
			 _esdl__CstProcessor proc) {
    return this;
  }

  abstract bool isBool();
  abstract long value();
  abstract bool getBool();
  // abstract bool signed();
  // abstract uint bitcount();
  
  void _esdl__scan(_esdl__CstProcessor proc) { }

}

abstract class CstVecValueBase: CstValue, CstVecTerm {
  final override bool isConst() { return true; }
  final override bool isIterator() { return false; }
  final override CstDomBase getDomain() { return null; }
  final override bool isDistVar() { return false; }
}


abstract class CstObjSet: CstObjArrVoid, CstObjArrIntf
{
  string _esdl__name;

  private _esdl__Proxy _root;
  
  this(string name, _esdl__Proxy root) {
    assert (root !is null);
    _esdl__name = name;
    _root = root;
  }

  _esdl__Proxy _esdl__getRootProxy() {
    assert (_root !is null);
    return _root;
  }

  string _esdl__getName() {
    return _esdl__name;
  }

  uint _esdl__domsetUnresolvedArrLen = uint.max;
  uint _esdl__domsetLeafElemsCount = 0;

  final uint _esdl__leafsCount() {
    assert (isDepResolved());
    return _esdl__domsetLeafElemsCount;
  }
  
  final bool isDepResolved() {
    return _esdl__domsetUnresolvedArrLen == 0;
  }

  abstract void markHierResolved(_esdl__CstProcessor proc);
  
}

abstract class CstDomSet: CstVecArrVoid, CstVecPrim, CstVecArrIntf
{
  State _state;
  
  string _esdl__name;

  _esdl__Proxy _root;
  
  this(string name, _esdl__Proxy root) {
    _esdl__name = name;
    _root = root;
  }

  _esdl__Proxy _esdl__getRootProxy() {
    assert (_root !is null);
    return _root;
  }

  override string _esdl__getName() {
    return _esdl__name;
  }

  // Callbacks
  Vector!(CstDepCallback, "depCbs") _depCbs;

  // Dependencies
  CstDepIntf[] _deps;
  
  CstVarNodeIntf [] _dependents;

  void orderBefore(CstVarNodeIntf a) {
    _dependents ~= a;
  }

  auto getOrdered() {
    return _dependents;
  }

  final CstVarNodeIntf [] getDependents(){
    if (getParentDomSet !is null) {
      return getOrdered() ~ getParentDomSet().getDependents();
    }
    else return getOrdered();
  }

  final bool isDependent(CstVarNodeIntf[] depArr){
    import std.algorithm.searching : canFind;
    if (getParentDomSet() is null) return depArr.canFind(this);
    else return (depArr.canFind(this) || getParentDomSet().isDependent(depArr));
  }
      
  void addDep(CstDepIntf dep) { if (! _deps.canFind(dep)) _deps ~= dep; }
  CstDepIntf[] getDeps() { return _deps; }
  
  uint _unresolveLap;

  abstract void markAsUnresolved(uint lap, bool hier);
  abstract uint elemBitcount();
  abstract bool elemSigned();

  override void _esdl__markOrderedAfter(uint level) {
    if (_orderLevel == level) return;
    assert (_orderLevel == level - 1);
    _orderLevel = level;
    CstPredicate [] preds = _resolvedDomainPreds[];
    foreach (pred; preds) {
      if (pred._esdl__getOrderLevel() < level){
	assert (pred._esdl__getOrderLevel() == level - 1, "unexpected error in ordering");
	pred._esdl__setOrderLevel(level);
	CstDomBase [] doms = pred.getUnresolvedRnds();
	foreach (dom; doms){
	  if (dom._orderVar != SolveOrder.NOW  && !dom.isSolved()) {
	    dom._esdl__markOrderedAfter(level);
	  }
	}
	CstDomSet [] domArrs = pred.getUnresolvedRndArrs();
	foreach (domArr; domArrs){
	  if (domArr._orderVar != SolveOrder.NOW ) {
	    domArr._esdl__markOrderedAfter(level);
	  }
	}
      }
    }
  }
  
  void execCbs(_esdl__CstProcessor proc) {
    execIterCbs(proc);
    execDepCbs(proc);
  }

  void execIterCbs(_esdl__CstProcessor proc) { }
  void execDepCbs(_esdl__CstProcessor proc) {
    foreach (cb; _depCbs) {
      cb.doResolve(proc);
    }
  }

  abstract CstDomSet getParentDomSet();
  abstract CstDomSet _esdl__unroll(CstIterator iter, ulong n,
				   _esdl__CstProcessor proc);
  
  override void registerDepPred(CstDepCallback depCb) {
    // if (! _depCbs[].canFind(depCb))
    _depCbs ~= depCb;
  }

  override void registerIdxPred(CstDepCallback idxCb) {
    // if (! _depCbs[].canFind(idxCb))
    _depCbs ~= idxCb;
  }

  uint _esdl__domsetUnresolvedArrLen = uint.max;
  uint _esdl__domsetUnsolvedLeafCount = uint.max;
  uint _esdl__domsetLeafElemsCount = 0;

  // override bool isSolved() {
  //   return _esdl__depsAreResolved();
  // }
  
  final uint _esdl__leafsCount() {
    assert (isDepResolved());
    return _esdl__domsetLeafElemsCount;
  }
  
  abstract bool _esdl__isRand();

  override bool isDepResolved() {
    return _esdl__domsetUnresolvedArrLen == 0;
  }

  final bool isSolved() {
    return _esdl__domsetUnsolvedLeafCount == 0;
  }

  abstract void markHierResolved(_esdl__CstProcessor proc);

  void markSolved(_esdl__CstProcessor proc) {
    if (_state == State.SOLVED) return;
    if (proc.debugSolver()) {
      import std.stdio;
      writeln("Marking ", this._esdl__getName(), " as SOLVED");
    }
    _resolvedDomainPreds.reset();
    assert (_state != State.SOLVED, this._esdl__getName() ~
	    " already marked as solved");
    _state = State.SOLVED;
    proc.addSolvedDomainArr(this);
    this.execCbs(proc);
  }
  
  bool hasChanged() {
    assert (false);
  }

  bool tryResolveDep(_esdl__CstProcessor proc) { return false; }
	
  void visit(CstSolver solver, _esdl__CstProcessor proc) {
    foreach (dom; this[]) {
      // import std.stdio;
      // writeln("Visiting: ", dom._esdl__getFullName());
      dom.visit(solver, proc);
    }
  }

  void visit(CstDistSolverBase solver, _esdl__CstProcessor proc) {
    foreach (dom; this[]) {
      // import std.stdio;
      // writeln("Visiting: ", dom._esdl__getFullName());
      // writeln("Purging: ", dom.value());
      solver.purge(dom.value());
    }
  }

  abstract void setDomainArrContext(CstPredicate pred, DomainContextEnum context);

  uint         _domSetN = uint.max;
  uint         _varSetN = uint.max;

  uint annotation() {
    return _domSetN;
  }

  void setAnnotation(uint n) {
    // import std.stdio;
    // writeln("Domain: ", _esdl__getName(), " setAnnotation: ", n);
    _domSetN = n;
  }
  
  final void annotate(CstSolverAgent agent, _esdl__CstProcessor proc) {
    assert (isDepResolved());
    CstDomSet resolved = this._esdl__getResolvedNode(proc);
    if (resolved !is this) resolved.annotate(agent, proc);
    else {
      foreach (dom; this[]) dom.annotate(agent, proc);
      // import std.conv: to;
      // import std.stdio;
      // writeln("annotate: ", this._esdl__getName());
      if (_domSetN == uint.max) {
	if (_varSetN == uint.max) _varSetN = agent.getAnnotationIndex();
	if (this.isSolved()) setAnnotation(agent.addAnnotatedVarArr(this));
	else setAnnotation(agent.addAnnotatedDomArr(this));
      }
      // writeln("annotate: ", _varSetN.to!string());
      // writeln("annotate: ", _domSetN.to!string());
    }
  }

  
  void writeExprString(_esdl__CstProcessor proc, ref _esdl__Sigbuf str) {
    assert (isDepResolved());
    foreach (dom; this[]) {
      dom.writeExprString(proc, str);
      str ~= ' ';
    }
  }

  void calcHash(ref Hash hash){
    foreach (dom; this[]) {
      dom.calcHash(hash);
      hash.modify(' ');
    }
  }

  Hash _hash;
  
  size_t hashValue(){
    return _hash.hash;
  }
  void makeHash(){
    _hash = Hash(0);
    // foreach (dom; this[]) {
    //   dom.makeHash();
    //   _hash.modify(dom.hashValue());
    //   _hash.modify(' ');
    // }
    // this[] cant be resolved rn

    _hash.modify(1733); //random number
  }
  

  abstract bool _esdl__parentIsConstrained();
  
  Vector!(CstPredicate, "resolvedDomainPreds") _resolvedDomainPreds;
  Vector!(CstPredicate, "unresolvedDomainPreds") _unresolvedDomainPreds;
  Vector!(CstPredicate, "lambdaDomainPreds") _lambdaDomainPreds;

  final void addResolvedPred(CstPredicate pred) {
    _resolvedDomainPreds ~= pred;
  }
  
  final void addUnresolvedPred(CstPredicate pred) {
    _unresolvedDomainPreds ~= pred;
  }
  
  final void addLambdaPred(CstPredicate pred) {
    _lambdaDomainPreds ~= pred;
  }
  
  override void registerRndPred(CstPredicate rndPred, _esdl__CstProcessor proc) {
    if (rndPred.isLambdaPred()) {
      if (! _lambdaDomainPreds[].canFind(rndPred)) {
	assert(proc !is null);
	_lambdaDomainPreds ~= rndPred;
	proc._esdl__addLambdaCstDom(this);
      }
    }
    else {
      if (! _unresolvedDomainPreds[].canFind(rndPred)) {
	_unresolvedDomainPreds ~= rndPred;
      }
    }
  }
  
  CstVecArrExpr sum() {
    return new CstVecArrExpr(this// , CstVectorOp.SUM
    );
  }

  public enum State: ubyte { INIT, COLLATED, GROUPED, SOLVED }

  uint _orderLevel = 0;
      
  override uint _esdl__getOrderLevel(){
    return _orderLevel;
  }

  void _esdl__setOrderLevel(uint lev){
    _orderLevel = lev;
  }

  // CstVarNodeIntf [] _solvedAfter;
  // CstVarNodeIntf [] getSolvedAfter() {
  //   return _solvedAfter;
  // }
  // void addSolvedAfter(CstVarNodeIntf dependent){
  //   _solvedAfter ~= dependent;
  // }
  // CstVarNodeIntf [] _solvedBefore;
  // CstVarNodeIntf [] getSolvedBefore() {
  //   return _solvedBefore;
  // }
  // void addSolvedBefore(CstVarNodeIntf dependent){
  //   _solvedBefore ~= dependent;
  // }

  
  SolveOrder _orderVar = SolveOrder.UNDECIDED;
  
  override void _esdl__setOrder(SolveOrder order){
    _orderVar = order;
  }
  
  override SolveOrder _esdl__getOrder() {
    return _orderVar;
  }
  override void reset() {
    _state = State.INIT;
    _esdl__domsetUnresolvedArrLen = uint.max;
    _esdl__domsetUnsolvedLeafCount = uint.max;
    _esdl__domsetLeafElemsCount = 0;
    _orderVar = SolveOrder.UNDECIDED;
    _orderLevel = 0;
    _depCbs.reset();
  }
  
  void setProcContext(_esdl__CstProcessor proc) {
    // import std.stdio;
    // writeln("setProcContext on: ", this._esdl__getName());
    assert (this.isDepResolved(), this._esdl__getName() ~ " is unresolved");
    assert (_state is State.INIT);
    foreach (pred; _resolvedDomainPreds[]) {
      if (! pred.isGuard()) {
	if (pred.isEnabled() && pred.isResolved() && ! pred.isBlocked()) {
	  pred.setProcContext(proc);
	}
      }
    }
    if (_esdl__parentIsConstrained()) {
      CstDomSet parent = getParentDomSet();
      assert (parent !is null);
      if (parent._state is State.INIT) {
	parent.setProcContext(proc);
      }
    }
    else {			// only for the top arr
      proc.collateDomArr(this);
      foreach (dom; this[]) {
	if (dom._state is CstDomBase.State.INIT && (! dom.isSolved())) {
	  dom.setProcContext(proc);
	}
      }
    }
  }
  
  void setSolverContext(CstSolverAgent agent, uint level) {
    assert (_state is State.COLLATED || _state is State.INIT);
    assert (this.isDepResolved(), this._esdl__getName() ~ " is unresolved");
    foreach (pred; _resolvedDomainPreds[]) {
      if (! pred.isGuard()) {
  	if (pred.isEnabled() &&
	    pred.isCollated() &&
	    pred._esdl__getOrderLevel() == level - 1) {
  	  pred.setSolverContext(agent, level);
  	}
      }
    }
    if (_esdl__parentIsConstrained()) {
      CstDomSet parent = getParentDomSet();
      assert (parent !is null);
      parent.setSolverContext(agent, level);
    }
    else {			// only for the top arr
      _state = State.GROUPED;
      foreach (dom; this[]) {
  	if (dom._state is CstDomBase.State.COLLATED &&
	    (! dom.isSolved()) &&
	    dom._esdl__getOrderLevel() == level - 1) {
  	  dom.setSolverContext(agent, level);
  	}
      }
    }
  }

  CstDomBase getDomain() { return null; }

  abstract CstDomSet _esdl__getResolvedNode(_esdl__CstProcessor proc);

  final override void resetLambdaPreds() {
    _lambdaDomainPreds.reset();
  }

  abstract CstVecType getVecType();
}


// The client keeps a list of agents that when resolved makes the client happy
interface CstIterCallback
{
  string _esdl__getName();
  string _esdl__getFullName();
  void doUnroll(_esdl__CstProcessor proc);
}

interface CstDepCallback
{
  string _esdl__getName();
  string _esdl__getFullName();
  void doResolve(_esdl__CstProcessor proc);
}

interface CstVecPrim
{
  string _esdl__getName();
  string _esdl__getFullName();
  void solveBefore(CstVecPrim other);
  void addPreRequisite(CstVecPrim other);
}

interface CstTerm
{
  string describe(bool descExpr=false);

  void setDomainContext(CstPredicate pred, DomainContextEnum context);
  bool isSolved();
  void visit(CstSolver solver, _esdl__CstProcessor proc);
  void visit(CstDistSolverBase dist, _esdl__CstProcessor proc);

  void annotate(CstSolverAgent agent, _esdl__CstProcessor proc);
  void writeExprString(_esdl__CstProcessor proc, ref _esdl__Sigbuf str);
  void calcHash(ref Hash hash);
  void makeHash();
  size_t hashValue();

  CstTerm _esdl__unroll(CstIterator iter, ulong n,
			_esdl__CstProcessor proc);
  
  void _esdl__scan(_esdl__CstProcessor proc); // {}		// used for CstVarVisitorExpr

  CstDomBase getDomain(); // Return the domain if the expression is a domain
  // bool isDomain();
}

// This class represents an unwound Foreach iter at vec level
abstract class CstIterator: CstVecTerm
{
  Vector!(CstIterCallback, "iterCbs") _iterCbs;

  void registerRolled(CstIterCallback cb) {
    _iterCbs ~= cb;
  }

  void unrollCbs(_esdl__CstProcessor proc) {
    foreach (cb; _iterCbs) {
      cb.doUnroll(proc);
    }
  }

  final override bool isDistVar() { return false; } 
  abstract ulong size();
  abstract string _esdl__getName();
  abstract string _esdl__getFullName();
  abstract CstIterator unrollIterator(CstIterator iter, uint n);
  abstract CstDomBase getLenVec();
  abstract ulong mapIter(size_t i);
  final bool isUnrollable() {
    return getLenVec().isSolved();
  }
  bool isConst() {
    return false;
  }
  bool isIterator() {
    return true;
  }
  long evaluate() {
    assert(false, "Can not evaluate an Iterator: " ~ this._esdl__getName());
  }
  void _esdl__scan(_esdl__CstProcessor proc) { }

  override CstDomBase getDomain() { return null; }

  override final CstVecType getVecType() {
    return CstVecType.ULONG;
  }

  final void reset() {
    _iterCbs.reset();
  }
  
}

interface CstVecTerm: CstTerm
{
  bool isConst();
  bool isIterator();
  bool isDistVar();
  
  long evaluate();
  uint bitcount();
  bool signed();

  CstVecType getVecType();

  CstVecTerm _esdl__unroll(CstIterator iter, ulong n,
			   _esdl__CstProcessor proc);

  final CstLogicTerm toBoolExpr() {
    auto zero = new CstVecValue!int(0); // CstVecValue!int.allocate(0);
    return new CstVec2LogicExpr(this, zero, CstCompareOp.NEQ);
  }

  CstVec2VecExpr opBinary(string op)(CstVecTerm other)
  {
    static if(op == "&") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.AND);
    }
    static if(op == "|") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.OR);
    }
    static if(op == "^") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.XOR);
    }
    static if(op == "+") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.ADD);
    }
    static if(op == "-") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.SUB);
    }
    static if(op == "*") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.MUL);
    }
    static if(op == "/") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.DIV);
    }
    static if(op == "%") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.REM);
    }
    static if(op == "<<") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.LSH);
    }
    static if(op == ">>") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.RSH);
    }
    static if(op == ">>>") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.LRSH);
    }
    static if(op == "~") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.RANGE);
    }
  }

  CstVec2VecExpr opBinary(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
  	auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
  	static if(op == "&") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.AND);
  	}
  	static if(op == "|") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.OR);
  	}
  	static if(op == "^") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.XOR);
  	}
  	static if(op == "+") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.ADD);
  	}
  	static if(op == "-") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.SUB);
  	}
  	static if(op == "*") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.MUL);
  	}
  	static if(op == "/") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.DIV);
  	}
  	static if(op == "%") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.REM);
  	}
  	static if(op == "<<") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.LSH);
  	}
  	static if(op == ">>") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.RSH);
  	}
  	static if(op == ">>>") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.LRSH);
  	}
  	static if(op == "~") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.RANGE);
  	}
      }

  CstVec2VecExpr opBinaryRight(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
	auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
	static if(op == "&") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.AND);
	}
	static if(op == "|") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.OR);
	}
	static if(op == "^") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.XOR);
	}
	static if(op == "+") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.ADD);
	}
	static if(op == "-") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.SUB);
	}
	static if(op == "*") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.MUL);
	}
	static if(op == "/") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.DIV);
	}
	static if(op == "%") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.REM);
	}
	static if(op == "<<") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.LSH);
	}
	static if(op == ">>") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.RSH);
	}
	static if(op == ">>>") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.LRSH);
	}
	static if(op == "~") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.RANGE);
	}
      }

  // final CstVecSliceExpr opSlice(CstVecTerm lhs, CstVecTerm rhs) {
  //   return new CstVecSliceExpr(this, lhs, rhs);
  // }

  final CstVecSliceExpr opIndex(CstRangeExpr range) {
    return new CstVecSliceExpr(this, range);
  }

  // final CstVecIndexExpr opIndex(CstVecTerm index) {
  //   return new CstVecIndexExpr(this, index);
  // }

  CstNotVecExpr opUnary(string op)() if(op == "~") {
    return new CstNotVecExpr(this);
  }

  CstNegVecExpr opUnary(string op)() if(op == "-") {
    return new CstNegVecExpr(this);
  }

  final CstLogicTerm inside(CstInsideSetElem range) {
    if (range._rhs is null) {
      return new CstVec2LogicExpr(this, range._lhs, CstCompareOp.EQU);
    }
    else {
      CstLogicTerm lhs = new CstVec2LogicExpr(this, range._lhs, CstCompareOp.GTE);
      CstLogicTerm rhs;
      if (range._inclusive) rhs = new CstVec2LogicExpr(this, range._rhs, CstCompareOp.LTE);
      else rhs = new CstVec2LogicExpr(this, range._rhs, CstCompareOp.LTH);
      return lhs & rhs;
    }
  }
}

interface CstLogicTerm: CstTerm
{
  CstDistSolverBase getDist();
  bool isCompatWithDist(CstDomBase A);

  void setDistPredContext(CstPredicate pred);

  bool eval();


  CstLogicTerm _esdl__unroll(CstIterator iter, ulong n,
			     _esdl__CstProcessor proc);

  CstLogicTerm opBinary(string op)(CstLogicTerm other)
  {
    static if(op == "&") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICAND);
    }
    static if(op == "|") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICOR);
    }
    static if(op == ">>") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICIMP);
    }
  }

  CstLogicTerm opOpAssign(string op)(CstLogicTerm other)
  {
    static if(op == ">>>") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICIMP);
    }
  }
  
  CstLogicTerm opUnary(string op)() if(op == "*")
    {
      static if(op == "*") {	// "!" in parser is translated as "*"
	CstInsideArrExpr expr = cast(CstInsideArrExpr) this;
	if (expr !is null) {
	  CstInsideArrExpr notExpr =  expr.dup();
	  notExpr.negate();
	  return notExpr;
	}
	else return new CstNotLogicExpr(this);
      }
    }

  CstLogicTerm opUnary(string op)() if(op == "~")
    {
      static if(op == "~") {	// "!" in parser is translated as "*"
	return new CstNotLogicExpr(this);
      }
    }

  final CstLogicTerm implies(CstLogicTerm other)
  {
    return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICIMP);
  }

  final CstLogicTerm logicOr(CstLogicTerm other)
  {
    return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICOR);
  }

  final CstLogicTerm logicAnd(CstLogicTerm other)
  {
    return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICAND);
  }

}

