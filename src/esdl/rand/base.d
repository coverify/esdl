module esdl.rand.base;

import std.traits: isIntegral, isBoolean;
import std.algorithm: canFind;
import std.random: Random;
import std.range: isRandomAccessRange;

import esdl.solver.base;

import esdl.rand.domain: CstVecValue;
import esdl.rand.expr: CstVecArrExpr, CstVecSliceExpr, CstRangeExpr,
  CstInsideSetElem, CstVec2LogicExpr, CstLogic2LogicExpr, CstVec2VecExpr,
  CstNotLogicExpr, CstNegVecExpr, CstInsideArrExpr;
import esdl.rand.pred: CstPredGroup, CstPredicate, Hash;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.misc: _esdl__RandGen, CstVectorOp, CstLogicOp, CstCompareOp,
  CstBinaryOp, SolveOrder;

import esdl.data.bvec: isBitVector;
import esdl.data.folder;
import esdl.data.charbuf;

interface CstVarNodeIntf {
  bool isRand();
  _esdl__Proxy getProxyRoot();
  string name();
  string fullName();
  bool inRange();
  void setOrder(SolveOrder order);
  SolveOrder getOrder();
  uint getOrderLevel();
  void markOrderedAfter(uint level);
  
  bool _esdl__isObjArray();
  CstIterator _esdl__iter();
  CstVarNodeIntf _esdl__getChild(ulong n);
  void scan();			// when an object is unrolled
}

interface CstDepIntf {
  string name();
  string fullName();

  abstract bool hasChanged();

  abstract void registerIdxPred(CstDepCallback idxCb);
  abstract void registerDepPred(CstDepCallback depCb);
  abstract bool isResolvedDep();
  abstract bool tryResolve(_esdl__Proxy proxy);

  abstract CstDomBase getDomain();
}

interface CstVecNodeIntf: CstVarNodeIntf, CstDepIntf {

  // This function is used in setDomainArrContext to register all the
  // predicates with the domain variables that this predicate
  // constrains
  abstract void registerRndPred(CstPredicate rndPred);  

  abstract void setGroupContext(CstPredGroup group);
  abstract void setProxyContext(_esdl__Proxy proxy);
  abstract void reset();
}

interface CstVectorIntf: CstVecNodeIntf {}

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

interface CstObjNodeIntf: CstVarNodeIntf {}

interface CstObjectIntf: CstObjNodeIntf {}
interface CstObjArrIntf: CstObjNodeIntf {

  _esdl__Proxy _esdl__nthLeaf(uint idx);
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


enum DomType: ubyte
{   TRUEMONO = 1,
    LAZYMONO = 2,		// like TRUEMONO with only some vals that need runtime eval
    MAYBEMONO = 3,
    INDEXEDMONO = 4,
    MULTI = 5
    }

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

  void getIterators(ref CstIterator[] iters, uint level) {
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
				"NONE" : _iter.name());
    return description;
  }
}

enum DomDistEnum: ubyte
{   NONE = 0,
    DETECT = 1,
    PROPER = 2
    }

abstract class CstDomBase: CstTerm, CstVectorIntf
{

  public enum State: ubyte
  {   INIT,
      GROUPED,
      COLLATED,
      SOLVED
      }

  uint         _domN = uint.max;
  uint         _varN = uint.max;

  _esdl__Proxy _root;
  string _name;

  string name() {
    return _name;
  }

  // Dependencies
  CstDepIntf[] _deps;

  void addDep(CstDepIntf dep) { if (! _deps.canFind(dep)) _deps ~= dep; }
  CstDepIntf[] getDeps() { return _deps; }
  
  abstract string fullName();
  // abstract void collate(ulong v, int word=0);
  abstract void setVal(ulong[] v);
  abstract void setVal(ulong v);

  abstract bool isBool();
  abstract void setBool(bool v);
  abstract bool getBool();
  
  // abstract uint domIndex();
  // abstract void domIndex(uint s);
  abstract bool isRand();
  abstract bool signed();
  abstract uint bitcount();
  abstract _esdl__Proxy getProxyRoot();
  abstract void _esdl__doRandomize(_esdl__RandGen randGen);
  abstract CstDomBase getResolved();
  abstract bool updateVal();
  abstract bool hasChanged();
  abstract bool isStatic();
  abstract bool isRolled();
  abstract void registerRndPred(CstPredicate rndPred);
  abstract CstDomSet getParentDomSet();

  override void markOrderedAfter(uint level) {
    if (_orderLevel == level) return;
    assert (_orderLevel == level - 1);
    _orderLevel = level;
    CstPredicate[] preds = getRandPreds();
    foreach (pred; preds){
      if (pred.getOrderLevel() < level) {
	assert(pred.getOrderLevel() == level - 1, "unexpected error in ordering");
	pred.setOrderLevel(level);
	CstDomBase[] doms = pred.getDomains();
	foreach (dom; doms) {
	  if (dom._orderVar != SolveOrder.NOW && !dom.isSolved()) {
	    dom.markOrderedAfter(level);
	  }
	}
	CstDomSet[] domArrs = pred.getDomArrs();
	foreach (domArr; domArrs) {
	  if (domArr._orderVar != SolveOrder.NOW ) {
	    domArr.markOrderedAfter(level);
	  }
	}
      }
    }
  }

  uint _orderLevel = 0;
      
  override uint getOrderLevel(){
    return _orderLevel;
  }

  void setOrderLevel(uint lev){
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
  
  override void setOrder(SolveOrder order){
    _orderVar = order;
  }

  override SolveOrder getOrder() {
    return _orderVar;
  }
  // abstract void registerVarPred(CstPredicate varPred);  
  // abstract void registerDepPred(CstDepCallback depCb);
  // abstract void registerIdxPred(CstDepCallback idxCb);

  // CstVecNodeIntf
  final bool _esdl__isVecArray() {return false;}
  final CstIterator _esdl__iter() {return null;}
  final CstVarNodeIntf _esdl__getChild(ulong n) {assert (false);}

  DomDistEnum _dist;
  final bool isDist() { return _dist >= DomDistEnum.DETECT; }

  final void isDist(bool b) {
    if (b) {
      if (_dist == DomDistEnum.NONE) _dist = DomDistEnum.DETECT;
    }
    else 
      _dist = DomDistEnum.NONE;
  }
  final void isDist(DomDistEnum d) {
    _dist = d;
  }
  
  abstract long value();
  
  void forceResolve(_esdl__Proxy proxy) {
    if (! tryResolve(proxy))
	assert (false, "Unable to resolve domain: " ~ name());
  }

  bool tryResolve(_esdl__Proxy proxy) {
    import std.algorithm.iteration: filter;
    if (isResolvedDep()) {
      execCbs();
      return true;
    }
    else {
      if (_rndPreds.length == 0 ||
	  _rndPreds.filter!(pred => ! pred.isGuard()).empty()) {
	randomizeWithoutConstraints(proxy);
	return true;
      }
    }
    return false;
  }
  void randomizeWithoutConstraints(_esdl__Proxy proxy){
    _esdl__doRandomize(getProxyRoot()._esdl__getRandGen());
    proxy.solvedSome();
    markSolved();
    proxy.addSolvedDomain(this);
    execCbs();
  }

  void markSolved() {
    if (_root._esdl__debugSolver) {
      import std.stdio;
      writeln("Marking ", this.name(), " as SOLVED");
    }
    _tempPreds.reset();
    assert (_state != State.SOLVED, this.name() ~
	    " already marked as solved");
    _state = State.SOLVED;
  }

  bool isMarkedSolved() {
    return _state == State.SOLVED;
  }
  
  override final bool isResolvedDep() {
    return isSolved();
  }

  final bool isSolved() {
    if (isRand()) {
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
  CstDepCallback[] _depCbs;

  CstPredicate[] _rndPreds;
  // CstPredicate[] _varPreds;

  CstPredicate [] getRandPreds(){
    return _rndPreds;
  }
  Folder!(CstPredicate, "tempPreds") _tempPreds;


  void purgeRndPred(CstPredicate pred) {
    // import std.stdio;
    // writeln("Removing pred: ", pred.describe());
    import std.algorithm: countUntil;
    auto index = countUntil(_rndPreds, pred);
    if (index >= 0) {
      _rndPreds[index] = _rndPreds[$-1];
      _rndPreds.length -= 1;
    }
  }

  // CstPredGroup _group;

  // CstPredGroup group() {
  //   return _group;
  // }

  uint annotation() {
    return _domN;
  }

  void setAnnotation(uint n) {
    // import std.stdio;
    // writeln("Domain: ", name(), " setAnnotation: ", n);
    _domN = n;
  }
  
  final void annotate(CstPredGroup group) {
    import std.conv: to;
    // import std.stdio;
    // writeln("annotate: ", this.name());
    if (_domN == uint.max) {
      if (_varN == uint.max) _varN = _root.indexVar();
      if (this.isSolved()) setAnnotation(group.addVariable(this));
      else setAnnotation(group.addDomain(this));
    }
    // writeln("annotate: ", _varN.to!string());
    // writeln("annotate: ", _domN.to!string());
  }

  override bool inRange() {
    assert(false, "inRange is not defined for: " ~ name());
  }

  void setProxyContext(_esdl__Proxy proxy){
    // import std.stdio;
    // writeln("setProxyContext on: ", this.name());
    assert (_state is State.INIT && (! this.isSolved()));
    proxy.addGroupDomain(this);
    // assert (_group is null && (! this.isSolved()));
    // _group = group;
    if (this.isRand()) {
      foreach (pred; _rndPreds) {
	if (pred.isEnabled() &&
	    pred._state is CstPredicate.State.INIT//  &&
	    // ! pred.hasUnrolled() // now taken care of in _state (UNROLLED)
	    ) {
	  pred.setProxyContext(proxy);
	}
      }
      if (_esdl__parentIsConstrained) {
	CstDomSet parent = getParentDomSet();
	assert (parent !is null);
	if (parent._state is CstDomSet.State.INIT) {
	  parent.setProxyContext(proxy);
	}
      }
    }
  }
  
  void setGroupContext(CstPredGroup group, uint level) {
    assert (_state is State.COLLATED &&
	    (! this.isSolved()) && getOrderLevel() == level - 1);
    _state = State.GROUPED;
    if (this.isRand()) {
      foreach (pred; _rndPreds) {
  	if (pred.isEnabled() &&
	    pred.isCollated() &&
	    pred.getOrderLevel == level - 1) {
  	  pred.setGroupContext(group, level);
  	}
      }
      if (_esdl__parentIsConstrained) {
  	CstDomSet parent = getParentDomSet();
  	assert (parent !is null);
  	if (parent._state is CstDomSet.State.INIT ||
	    parent._state is CstDomSet.State.COLLATED) {
  	  parent.setGroupContext(group, level);
  	}
      }
    }
  }

  // abstract void annotate(CstPredGroup group);
  abstract bool visitDomain(CstSolver solver);
  
  // init value has to be different from proxy._cycle init value
  uint _cycle = -1;
  State _state;
  uint _unresolveLap;

  override void reset() {
    _state = State.INIT;
    _orderVar = SolveOrder.UNDECIDED;
    _orderLevel = 0;
  }
  
  DomType _type = DomType.TRUEMONO;

  final void markAsUnresolved(uint lap) {
    if (_unresolveLap != lap) {
      _unresolveLap = lap;
      CstDomSet parent = getParentDomSet();
      if (parent !is null)
	parent.markAsUnresolved(lap, false);
      foreach (pred; _rndPreds)
	pred.markAsUnresolved(lap);
    }
  }

  void execCbs() {
    execIterCbs();
    execDepCbs();
  }

  void execIterCbs() { }
  void execDepCbs() {
    foreach (cb; _depCbs) {
      cb.doResolve();
    }
  }

  override void registerDepPred(CstDepCallback depCb) {
    foreach (cb; _depCbs) {
      if (cb is depCb) {
	return;
      }
    }
    _depCbs ~= depCb;
  }

  override void registerIdxPred(CstDepCallback idxCb) {
    foreach (cb; _depCbs) {
      if (cb is idxCb) {
	return;
      }
    }
    _depCbs ~= idxCb; // use same callbacks as deps for now
  }

  bool _esdl__parentIsConstrained;
  abstract string describe(bool descExpr=false);

  void scan() { }
  CstDomBase getDomain() { return this; }
}

abstract class CstValue: CstTerm
{
  bool isConst() { return true; }

  bool isIterator() { return false; }

  CstValue unroll(CstIterator iters, ulong n) {
    return this;
  }

  abstract bool isBool();
  abstract long value();
  abstract bool getBool();
  // abstract bool signed();
  // abstract uint bitcount();

  void scan() { }

}

abstract class CstVecValueBase: CstValue, CstVecTerm {
  final override bool isConst() { return true; }
  final override bool isIterator() { return false; }
  final override CstDomBase getDomain() { return null; }
}


abstract class CstObjSet: CstObjArrVoid, CstObjArrIntf
{
  string _name;

  _esdl__Proxy _root;
  
  this(string name) {
    _name = name;
  }

  _esdl__Proxy getProxyRoot() {
    assert (_root !is null);
    return _root;
  }

  string name() {
    return _name;
  }

  uint _esdl__unresolvedArrLen = uint.max;
  uint _esdl__leafElemsCount = 0;

  final uint _esdl__leafsCount() {
    assert (isSolved());
    return _esdl__leafElemsCount;
  }
  
  final bool isSolved() {
    return _esdl__unresolvedArrLen == 0;
  }

  abstract void markSolved();
  
}

abstract class CstDomSet: CstVecArrVoid, CstVecPrim, CstVecArrIntf
{
  State _state;
  
  string _name;

  _esdl__Proxy _root;
  
  // Callbacks
  CstDepCallback[] _depCbs;

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

  override void markOrderedAfter(uint level) {
    if (_orderLevel == level) return;
    assert (_orderLevel == level - 1);
    _orderLevel = level;
    CstPredicate [] preds = getRandPreds();
    foreach (pred; preds) {
      if (pred.getOrderLevel() < level){
	assert (pred.getOrderLevel() == level - 1, "unexpected error in ordering");
	pred.setOrderLevel(level);
	CstDomBase [] doms = pred.getDomains();
	foreach (dom; doms){
	  if (dom._orderVar != SolveOrder.NOW  && !dom.isSolved()) {
	    dom.markOrderedAfter(level);
	  }
	}
	CstDomSet [] domArrs = pred.getDomArrs();
	foreach (domArr; domArrs){
	  if (domArr._orderVar != SolveOrder.NOW ) {
	    domArr.markOrderedAfter(level);
	  }
	}
      }
    }
  }
  
  void execCbs() {
    execIterCbs();
    execDepCbs();
  }

  void execIterCbs() { }
  void execDepCbs() {
    foreach (cb; _depCbs) {
      cb.doResolve();
    }
  }

  abstract CstDomSet getParentDomSet();
  abstract CstDomSet unroll(CstIterator iter, ulong n);
  
  override void registerDepPred(CstDepCallback depCb) {
    foreach (cb; _depCbs) {
      if (cb is depCb) {
	return;
      }
    }
    _depCbs ~= depCb;
  }

  override void registerIdxPred(CstDepCallback idxCb) {
    foreach (cb; _depCbs) {
      if (cb is idxCb) {
	return;
      }
    }
    _depCbs ~= idxCb; // use same callbacks as deps for now
  }

  this(string name) {
    _name = name;
  }

  _esdl__Proxy getProxyRoot() {
    assert (_root !is null);
    return _root;
  }

  override string name() {
    return _name;
  }

  uint _esdl__unresolvedArrLen = uint.max;
  uint _esdl__leafElemsCount = 0;

  // override bool isSolved() {
  //   return isResolved();
  // }
  
  final uint _esdl__leafsCount() {
    assert (isResolvedDep());
    return _esdl__leafElemsCount;
  }
  
  abstract bool isRand();

  override bool isResolvedDep() {
    return _esdl__unresolvedArrLen == 0;
  }

  abstract void markSolved();
  
  bool hasChanged() {
    assert (false);
  }

  bool tryResolve(_esdl__Proxy proxy) { return false; }
	
  void visit(CstSolver solver) {
    foreach (dom; this[]) {
      // import std.stdio;
      // writeln("Visiting: ", dom.fullName());
      dom.visit(solver);
    }
  }

  void visit(CstDistSolverBase solver) {
    foreach (dom; this[]) {
      // import std.stdio;
      // writeln("Visiting: ", dom.fullName());
      // writeln("Purging: ", dom.value());
      solver.purge(dom.value());
    }
  }

  abstract void setDomainArrContext(CstPredicate pred,
				    ref CstDomBase[] rnds,
				    ref CstDomSet[] rndArrs,
				    ref CstDomBase[] vars,
				    ref CstDomSet[] varArrs,
				    ref CstDomBase[] dists,
				    ref CstValue[] vals,
				    ref CstIterator[] iters,
				    ref CstDepIntf[] idxs,
				    ref CstDomBase[] bitIdxs,
				    ref CstDepIntf[] deps);

  void writeExprString(ref Charbuf str) {
    assert (isResolvedDep());
    foreach (dom; this[]) {
      dom.writeExprString(str);
      str ~= ' ';
    }
  }

  void calcHash(ref Hash hash){
    assert (isResolvedDep());
    foreach (dom; this[]) {
      dom.calcHash(hash);
      hash.modify(' ');
    }
  }

  CstPredicate[] _rndPreds;

  CstPredicate [] getRandPreds(){
    return _rndPreds;
  }
  bool _esdl__parentIsConstrained;
  override void registerRndPred(CstPredicate rndPred) {
    foreach (pred; _rndPreds)
      if (pred is rndPred) return;
    _rndPreds ~= rndPred;
  }

  CstVecArrExpr sum() {
    return new CstVecArrExpr(this// , CstVectorOp.SUM
    );
  }

  public enum State: ubyte
  {   INIT,
      GROUPED,
      COLLATED,
      SOLVED
      }

  uint _orderLevel = 0;
      
  override uint getOrderLevel(){
    return _orderLevel;
  }

  void setOrderLevel(uint lev){
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
  
  override void setOrder(SolveOrder order){
    _orderVar = order;
  }
  
  override SolveOrder getOrder() {
    return _orderVar;
  }
  override void reset() {
    _state = State.INIT;
    _esdl__unresolvedArrLen = uint.max;
    _esdl__leafElemsCount = 0;
    _orderVar = SolveOrder.UNDECIDED;
    _orderLevel = 0;
  }
  
  void setProxyContext(_esdl__Proxy proxy){
    // import std.stdio;
    // writeln("setProxyContext on: ", this.name());
    assert (this.isResolvedDep(), this.name() ~ " is unresolved");
    assert (_state is State.INIT);
    foreach (pred; _rndPreds) {
      if (! pred.isGuard()) {
	if (pred.isEnabled() &&
	    pred._state is CstPredicate.State.INIT) {
	  pred.setProxyContext(proxy);
	}
      }
    }
    if (_esdl__parentIsConstrained) {
      CstDomSet parent = getParentDomSet();
      assert (parent !is null);
      if (parent._state is State.INIT) {
	parent.setProxyContext(proxy);
      }
    }
    else {			// only for the top arr
      proxy.addGroupDomArr(this);
      foreach (dom; this[]) {
	if (dom._state is CstDomBase.State.INIT && (! dom.isSolved())) {
	  dom.setProxyContext(proxy);
	}
      }
    }
  }
  
  void setGroupContext(CstPredGroup group, uint level) {
    assert (_state is State.COLLATED || _state is State.INIT);
    assert (this.isResolvedDep(), this.name() ~ " is unresolved");
    foreach (pred; _rndPreds) {
      if (! pred.isGuard()) {
  	if (pred.isEnabled() &&
	    pred.isCollated() &&
	    pred.getOrderLevel() == level - 1) {
  	  pred.setGroupContext(group, level);
  	}
      }
    }
    if (_esdl__parentIsConstrained) {
      CstDomSet parent = getParentDomSet();
      assert (parent !is null);
      parent.setGroupContext(group, level);
    }
    else {			// only for the top arr
      _state = State.GROUPED;
      foreach (dom; this[]) {
  	if (dom._state is CstDomBase.State.COLLATED &&
	    (! dom.isSolved()) &&
	    dom.getOrderLevel() == level - 1) {
  	  dom.setGroupContext(group, level);
  	}
      }
    }
  }

  CstDomBase getDomain() { return null; }
}


// The client keeps a list of agents that when resolved makes the client happy
interface CstIterCallback
{
  string name();
  void doUnroll();
}

interface CstDepCallback
{
  string name();
  void doResolve();
}

interface CstVecPrim
{
  string name();
  void solveBefore(CstVecPrim other);
  void addPreRequisite(CstVecPrim other);
}

interface CstTerm
{
  string describe(bool descExpr=false);

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps);

  bool isSolved();
  void visit(CstSolver solver);
  void visit(CstDistSolverBase dist);

  void writeExprString(ref Charbuf str);
  void calcHash(ref Hash hash);

  CstTerm unroll(CstIterator iter, ulong n);
  
  void scan(); // {}		// used for CstVarVisitorExpr

  CstDomBase getDomain(); // Return the domain if the expression is a domain
  // bool isDomain();
}

// This class represents an unwound Foreach iter at vec level
abstract class CstIterator: CstVecTerm
{
  CstIterCallback[] _cbs;
  void registerRolled(CstIterCallback cb) {
    _cbs ~= cb;
  }
  void unrollCbs() {
    foreach (cb; _cbs) {
      cb.doUnroll();
    }
  }
  abstract ulong size();
  abstract string name();
  abstract string fullName();
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
    assert(false, "Can not evaluate an Iterator: " ~ this.name());
  }

  void scan() { }

  override CstDomBase getDomain() { return null; }
  
}

interface CstVecTerm: CstTerm
{
  bool isConst();
  bool isIterator();

  long evaluate();
  uint bitcount();
  bool signed();

  CstVecTerm unroll(CstIterator iter, ulong n);

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

  void setPredContext(CstPredicate pred);

  bool isOrderingExpr();
  bool eval();

  CstLogicTerm unroll(CstIterator iter, ulong n);

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
      static if(op == "*") {	// "!" in cstx is translated as "*"
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
      static if(op == "~") {	// "!" in cstx is translated as "*"
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

// Each process, routine and the root process have their own random
// generator. This is done to enable random stability.
ref Random getRandGen() {
  import esdl.base.core: Procedure, Process, RootThread;
  Procedure proc;
  proc = Process.self;
  if(proc is null) {
    proc = RootThread.self;
  }
  if(proc !is null) {
    return proc.getRandGen();
  }
  else {
    assert(false, "getRandGen can be accessed only from a Process," ~
	   " or RootThread");
  }
}

T urandom(T=uint)() if (isIntegral!T || isBitVector!T) {
  static if(isBitVector!T) {
    T v;
    v.randomize(getRandGen());
    return v;
  }
  else {
    import std.random: uniform;
    auto v = uniform!T(getRandGen());
    // debug(SEED) {
    //   import std.stdio;
    //   stdout.writeln("URANDOM returns: ", v);
    // }
    return v;
  }
}

bool urandom(T=bool)() if (isBoolean!T) {
  import std.random: uniform;
  uint v = uniform!("[]", uint)(0, 1, getRandGen());
  if (v == 0) return false;
  else return true;
 }

R shuffle(R)(ref R range) {
  import std.random: randomShuffle;
  return randomShuffle(range, getRandGen());
 }

T urandom(string BOUNDARY="[)", T=uint)(T min, T max)
  if (isIntegral!T || isBitVector!T) {
    import std.random: uniform;
    return uniform!(BOUNDARY, T)(min, max, getRandGen());
  }

T urandom_range(string BOUNDARY="[)", T=uint)(T min, T max) {
  import std.random: uniform;
  return uniform!(BOUNDARY, T)(min, max, getRandGen());
}

void srandom(uint _seed) {
  getRandGen().seed(_seed);
}

