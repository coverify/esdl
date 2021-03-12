module esdl.rand.base;

import esdl.solver.base;
import esdl.rand.dist;
import esdl.rand.expr: CstValue, CstVecTerm, CstVecArrExpr;
import esdl.rand.pred: CstPredGroup, CstPredicate;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.misc: _esdl__RandGen, CstVectorOp;
import esdl.data.folder;
import esdl.data.charbuf;

interface CstVarNodeIntf {
  bool isRand();
  _esdl__Proxy getProxyRoot();
  string name();
  string fullName();

  bool _esdl__isObjArray();
  CstIterator _esdl__iter();
  CstVarNodeIntf _esdl__getChild(ulong n);
  void visit();			// when an object is unrolled
}

interface CstVecNodeIntf: CstVarNodeIntf {
  abstract bool hasChanged();

  // This function is used in setDomainArrContext to register all the
  // predicates with the domain variables that this predicate
  // constrains
  abstract void registerRndPred(CstPredicate rndPred);  

  abstract void registerDepPred(CstDepCallback depCb);
  abstract void registerIdxPred(CstDepCallback idxCb);
  abstract bool isSolved();
  abstract void randomizeIfUnconstrained(_esdl__Proxy proxy);
  abstract void setGroupContext(CstPredGroup group);
  abstract void reset();
}

interface CstVectorIntf: CstVecNodeIntf {}

interface CstVecArrIntf: CstVecNodeIntf {
  CstDomain _esdl__nthLeaf(uint idx);
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

abstract class CstDomain: CstVecTerm, CstVectorIntf
{

  public enum State: ubyte
  {   INIT,
      GROUPED,
      SOLVED
      }

  uint         _domN = uint.max;
  uint annotation() {
    return _domN;
  }
  
  uint         _varN = uint.max;

  _esdl__Proxy _root;
  string _name;

  string name() {
    return _name;
  }


  abstract string fullName();
  // abstract void collate(ulong v, int word=0);
  abstract void setVal(ulong[] v);
  abstract void setVal(ulong v);

  abstract bool isBool();
  abstract void setBool(bool v);
  abstract bool getBool();
  
  // abstract uint domIndex();
  // abstract void domIndex(uint s);
  // abstract bool signed();
  abstract bool isRand();
  // abstract uint bitcount();
  abstract _esdl__Proxy getProxyRoot();
  abstract void _esdl__doRandomize(_esdl__RandGen randGen);
  abstract CstDomain getResolved();
  abstract bool updateVal();
  abstract bool hasChanged();
  abstract bool isStatic();
  abstract bool isRolled();
  abstract void registerRndPred(CstPredicate rndPred);
  abstract CstDomSet getParentDomSet();
  // abstract void registerVarPred(CstPredicate varPred);  
  // abstract void registerDepPred(CstDepCallback depCb);
  // abstract void registerIdxPred(CstDepCallback idxCb);

  // CstVecNodeIntf
  final bool _esdl__isVecArray() {return false;}
  final CstIterator _esdl__iter() {return null;}
  final CstVarNodeIntf _esdl__getChild(ulong n) {assert (false);}

  bool _isDist;
  final bool isDist() { return _isDist; }
  final void isDist(bool b) { _isDist = b; }

  abstract long value();
  
  void randomizeIfUnconstrained(_esdl__Proxy proxy) {
    if (! isSolved()) {
      if (_rndPreds.length == 0) {
	randomizeWithoutConstraints(proxy);
      }
    }
  }
  void randomizeWithoutConstraints(_esdl__Proxy proxy){
    _esdl__doRandomize(getProxyRoot()._esdl__getRandGen());
    proxy.solvedSome();
    markSolved();
    proxy.addSolvedDomain(this);
    execCbs();
  }

  void markSolved() {
    debug(CSTDOMAINS) {
      import std.stdio;
      stderr.writeln("Marking ", this.name(), " as SOLVED");
    }
    _tempPreds.reset();
    assert (_state != State.SOLVED);
    _state = State.SOLVED;
  }

  override final bool isSolved() {
    if (isRand()) {
      if (_state == State.SOLVED) return true;
      else return false;
    }
    else return true;
  }

  // Callbacks
  CstDepCallback[] _depCbs;

  CstPredicate[] _rndPreds;
  // CstPredicate[] _varPreds;

  CstPredicate [] getRandPreds(){
    return _rndPreds;
  }
  Folder!(CstPredicate, "tempPreds") _tempPreds;

  // CstPredGroup _group;

  // CstPredGroup group() {
  //   return _group;
  // }

  void setGroupContext(CstPredGroup group) {
    assert (_state is State.INIT && (! this.isSolved()));
    _state = State.GROUPED;
    // assert (_group is null && (! this.isSolved()));
    // _group = group;
    foreach (pred; _rndPreds) {
      if (pred._state is CstPredicate.State.INIT && !pred.getmarkBefore()) {
	pred.setGroupContext(group);
      }
    }
    if (_esdl__parentIsConstrained) {
      CstDomSet parent = getParentDomSet();
      assert (parent !is null);
      if (parent._state is CstDomSet.State.INIT) {
	parent.setGroupContext(group);
      }
    }
  }

  abstract void annotate(CstPredGroup group);
  abstract bool visitDomain(CstSolver solver);
  
  // init value has to be different from proxy._cycle init value
  uint _cycle = -1;
  State _state;
  uint _unresolveLap;

  override void reset() {
    _state = State.INIT;
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
  uint _markBefore = 0;
  void orderBefore(CstDomain x, uint lap){
    if(isSolved() || x.isSolved()){
      return;
    }
    x.setmarkBefore(lap);
    CstPredicate [] a = x.getRandPreds();
    foreach(elem; a){
      if(!elem.getmarkBefore()){
	elem.setmarkBefore(true);
	CstDomain [] b = elem.getDomains();
	foreach(j, e; b){
	  if(e != this && e.getmarkBefore() != lap){
	    orderBefore(e, lap);
	  }
	}
      }
    }
  }
  void setmarkBefore(uint lap){
    _markBefore = lap;
  }
  uint getmarkBefore(){
    return _markBefore;
  }

  bool _esdl__parentIsConstrained;
  override abstract string describe();
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

  uint _unresolveLap;

  abstract void markAsUnresolved(uint lap, bool hier);
  abstract uint elemBitcount();
  abstract bool elemSigned();

  
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

  override bool isSolved() {
    return isResolved();
  }
  
  final uint _esdl__leafsCount() {
    assert (isResolved());
    return _esdl__leafElemsCount;
  }
  
  final bool isResolved() {
    return _esdl__unresolvedArrLen == 0;
  }

  abstract void markSolved();
  
  bool hasChanged() {
    assert (false);
  }

  void randomizeIfUnconstrained(_esdl__Proxy proxy) {}
	
  void visit(CstSolver solver) {
    foreach (dom; this[]) {
      // import std.stdio;
      // writeln("Visiting: ", dom.fullName());
      dom.visit(solver);
    }
  }

  abstract void setDomainArrContext(CstPredicate pred,
				    ref CstDomain[] rnds,
				    ref CstDomSet[] rndArrs,
				    ref CstDomain[] vars,
				    ref CstDomSet[] varArrs,
				    ref CstValue[] vals,
				    ref CstIterator[] iters,
				    ref CstVecNodeIntf[] idxs,
				    ref CstDomain[] bitIdxs,
				    ref CstVecNodeIntf[] deps);

  void writeExprString(ref Charbuf str) {
    assert (isResolved());
    foreach (dom; this[]) {
      dom.writeExprString(str);
      str ~= ' ';
    }
  }

  CstPredicate[] _rndPreds;
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
      SOLVED
      }

  override void reset() {
    _state = State.INIT;
  }
  
  void setGroupContext(CstPredGroup group) {
    assert (this.isResolved());
    assert (_state is State.INIT);
    foreach (pred; _rndPreds) {
      if (pred._state is CstPredicate.State.INIT) {
	pred.setGroupContext(group);
      }
    }
    if (_esdl__parentIsConstrained) {
      CstDomSet parent = getParentDomSet();
      assert (parent !is null);
      if (parent._state is State.INIT) {
	parent.setGroupContext(group);
      }
    }
    else {			// only for the top arr
      _state = State.GROUPED;
      foreach (dom; this[]) {
	if (dom._state is CstDomain.State.INIT && (! dom.isSolved())) {
	  dom.setGroupContext(group);
	}
      }
    }
  }
}


// The client keeps a list of agents that when resolved makes the client happy
interface CstIterCallback
{
  abstract void doUnroll();
}

interface CstDepCallback
{
  abstract void doResolve();
}

interface CstVecPrim
{
  abstract string name();
  abstract void solveBefore(CstVecPrim other);
  abstract void addPreRequisite(CstVecPrim other);
}

abstract class CstExpr: CstVectorVoid
{
  string describe();

  abstract void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps);

  abstract bool isSolved();
  abstract void visit(CstSolver solver);
  void visit() {}		// used for CstVarVisitorExpr
  abstract void writeExprString(ref Charbuf str);
}

abstract class CstVecExpr: CstExpr
{
  abstract bool isConst();
  abstract bool isIterator();
  
  abstract long evaluate();

  abstract CstVecExpr unroll(CstIterator iter, ulong n);

  abstract bool isOrderingExpr();

  abstract uint bitcount();
  abstract bool signed();

}

abstract class CstLogicExpr: CstExpr
{
  abstract DistRangeSetBase getDist();
  abstract CstVecExpr isNot(CstDomain A);
  abstract CstLogicExpr unroll(CstIterator iter, ulong n);
  bool isOrderingExpr(){
    return false;
  }

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
  abstract CstDomain getLenVec();
  abstract ulong mapIter(size_t i);
  final bool isUnrollable() {
    return getLenVec().isSolved();
  }
  override bool isConst() {
    return false;
  }
  override bool isIterator() {
    return true;
  }
  override long evaluate() {
    assert(false, "Can not evaluate an Iterator: " ~ this.name());
  }
  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }
}
