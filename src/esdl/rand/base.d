module esdl.rand.base;

import std.traits: isIntegral;

import esdl.solver.base;

import esdl.rand.domain: CstVecValue;
import esdl.rand.expr: CstVecArrExpr, CstVecSliceExpr, CstRangeExpr,
  CstInsideSetElem, CstVec2LogicExpr, CstLogic2LogicExpr, CstVec2VecExpr,
  CstNotLogicExpr, CstNegVecExpr;
import esdl.rand.pred: CstPredGroup, CstPredicate;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.misc: _esdl__RandGen, CstVectorOp, CstLogicOp, CstCompareOp,
  CstBinaryOp;

import esdl.data.bvec: isBitVector;
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
  void scan();			// when an object is unrolled
}

interface CstDepIntf {
  string name();
  string fullName();

  abstract bool hasChanged();

  abstract void registerIdxPred(CstDepCallback idxCb);
  abstract void registerDepPred(CstDepCallback depCb);
  abstract bool isSolved();
  abstract void tryResolve(_esdl__Proxy proxy);
}

interface CstVecNodeIntf: CstVarNodeIntf, CstDepIntf {

  // This function is used in setDomainArrContext to register all the
  // predicates with the domain variables that this predicate
  // constrains
  abstract void registerRndPred(CstPredicate rndPred);  

  abstract void setGroupContext(CstPredGroup group);
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
  // abstract void registerVarPred(CstPredicate varPred);  
  // abstract void registerDepPred(CstDepCallback depCb);
  // abstract void registerIdxPred(CstDepCallback idxCb);

  // CstVecNodeIntf
  final bool _esdl__isVecArray() {return false;}
  final CstIterator _esdl__iter() {return null;}
  final CstVarNodeIntf _esdl__getChild(ulong n) {assert (false);}

  DomDistEnum _dist;
  final bool isDist() { return _dist >= DomDistEnum.DETECT; }
  final bool isProperDist() {
    if (_dist == DomDistEnum.NONE) return false;
    if (_dist >= DomDistEnum.PROPER) return true;

    bool isProper = true;

    // now make sure that all the predicates related to this domain are
    // not related to any other domain (ignoring conditions)
    foreach (pred; getRandPreds()) {
      if (pred.getDom() is this) {
	pred.hasDistDomain(true);
      }
      else {
	isProper = false;
	break;
      }
    }

    if (isProper) {
      _dist = DomDistEnum.PROPER;
    }
    else {
      foreach (pred; getRandPreds()) {
	pred.hasDistDomain(false);
      }
    }

    return isProper;
  }

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
  
  void tryResolve(_esdl__Proxy proxy) {
    if (isSolved()) execCbs();
    else {
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
    assert (_state != State.SOLVED, this.name() ~
	    " already marked as solved");
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

  final void annotate(CstPredGroup group, bool withDist) {
    // import std.stdio;
    // writeln(this.name(), ": ", withDist);
    if (_domN == uint.max) {
      if (withDist) {
	if (this.isProperDist() && ! this.isSolved()) {
	  _domN = group.addDistDomain(this);
	}
	else {
	  if (! this.isSolved()) {
	    _domN = group.addRandom(this);
	  }
	}
      }
      else {
	if (this.isSolved()) {
	  _domN = group.addVariable(this);
	  if (_varN == uint.max) _varN = _root.indexVar();
	}
	else {
	  // if (this.isProperDist()) {
	  //   group.addDistDomain(this);
	  // }
	  _domN = group.addDomain(this);
	}
      }
    }
  }

  void setGroupContext(CstPredGroup group) {
    // import std.stdio;
    // writeln("setGroupContext on: ", this.name());
    if (isDist()) this.isProperDist();

    assert (_state is State.INIT && (! this.isSolved()));
    _state = State.GROUPED;
    // assert (_group is null && (! this.isSolved()));
    // _group = group;
    foreach (pred; _rndPreds) {
      if (! pred.isGuard()) {
	if (pred._state is CstPredicate.State.INIT && !pred.getmarkBefore()) {
	  pred.setGroupContext(group);
	}
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

  // abstract void annotate(CstPredGroup group);
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
  void orderBefore(CstDomBase x, uint lap){
    if(isSolved() || x.isSolved()){
      return;
    }
    x.setmarkBefore(lap);
    CstPredicate [] a = x.getRandPreds();
    foreach(elem; a){
      if(!elem.getmarkBefore()){
	elem.setmarkBefore(true);
	CstDomBase [] b = elem.getDomains();
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
  abstract string describe();

  void scan() { }
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
  override bool isConst() {return true;}
  override bool isIterator() {return false;}
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
  
  abstract bool isRand();

  final bool isResolved() {
    if (isRand()) {
      return _esdl__unresolvedArrLen == 0;
    }
    else {
      return true;
    }
  }

  abstract void markSolved();
  
  bool hasChanged() {
    assert (false);
  }

  void tryResolve(_esdl__Proxy proxy) {}
	
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
      solver.purge(dom.value());
    }
  }

  abstract void setDomainArrContext(CstPredicate pred,
				    ref CstDomBase[] rnds,
				    ref CstDomSet[] rndArrs,
				    ref CstDomBase[] vars,
				    ref CstDomSet[] varArrs,
				    ref CstValue[] vals,
				    ref CstIterator[] iters,
				    ref CstDepIntf[] idxs,
				    ref CstDomBase[] bitIdxs,
				    ref CstDepIntf[] deps);

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
    _esdl__unresolvedArrLen = uint.max;
    _esdl__leafElemsCount = 0;
  }
  
  void setGroupContext(CstPredGroup group) {
    // import std.stdio;
    // writeln("setGroupContext on: ", this.name());
    assert (this.isResolved(), this.name() ~ " is unresolved");
    assert (_state is State.INIT);
    foreach (pred; _rndPreds) {
      if (! pred.isGuard()) {
	if (pred._state is CstPredicate.State.INIT) {
	  pred.setGroupContext(group);
	}
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
	if (dom._state is CstDomBase.State.INIT && (! dom.isSolved())) {
	  dom.setGroupContext(group);
	}
      }
    }
  }
}


// The client keeps a list of agents that when resolved makes the client happy
interface CstIterCallback
{
  void doUnroll();
}

interface CstDepCallback
{
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
  string describe();

  void setDomainContext(CstPredicate pred,
  			 ref CstDomBase[] rnds,
  			 ref CstDomSet[] rndArrs,
  			 ref CstDomBase[] vars,
  			 ref CstDomSet[] varArrs,
  			 ref CstValue[] vals,
  			 ref CstIterator[] iters,
  			 ref CstDepIntf[] idxs,
  			 ref CstDomBase[] bitIdxs,
  			 ref CstDepIntf[] deps);

  bool isSolved();
  void visit(CstSolver solver);
  void visit(CstDistSolverBase dist);

  void writeExprString(ref Charbuf str);

  CstTerm unroll(CstIterator iter, ulong n);
  
  void scan(); // {}		// used for CstVarVisitorExpr
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
	return new CstNotLogicExpr(this);
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
