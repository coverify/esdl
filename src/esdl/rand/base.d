module esdl.rand.base;

import esdl.solver.base;
import esdl.solver.buddy: CstBuddySolver;
import esdl.solver.z3: CstZ3Solver;
import esdl.solver.mono: CstMonoSolver;
import esdl.rand.dist;
import esdl.rand.expr: CstValue, CstVecTerm, CstVecArrExpr;
import esdl.rand.proxy: _esdl__ConstraintBase, _esdl__Proxy;
import esdl.rand.misc: _esdl__RandGen, isVecSigned, writeHexString, CstVectorOp;
import esdl.data.bvec: isBitVector;
import esdl.data.folder;
import esdl.data.charbuf;
import std.algorithm;
import std.array;
import std.container.array;
import std.traits: isIntegral, isBoolean;

interface CstVarNodeIntf {
  bool isRand();
  _esdl__Proxy getProxyRoot();
  string name();
  string fullName();

  bool _esdl__isObjArray();
  CstIterator _esdl__iter();
  CstVarNodeIntf _esdl__getChild(uint n);
  void visit();			// when an object is unrolled
}

interface CstVecNodeIntf: CstVarNodeIntf {
  abstract bool hasChanged();
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
  final CstVarNodeIntf _esdl__getChild(uint n) {assert (false);}

  bool _isDist;
  final bool isDist() { return _isDist; }
  final void isDist(bool b) { _isDist = b; }

  abstract long value();
  
  void randomizeIfUnconstrained(_esdl__Proxy proxy) {
    if (! isSolved()) {
      if (_rndPreds.length == 0) {
	_esdl__doRandomize(getProxyRoot()._esdl__getRandGen());
	proxy.solvedSome();
	markSolved();
	proxy.addSolvedDomain(this);
	execCbs();
      }
    }
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
      if (pred._state is CstPredicate.State.INIT) {
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


  bool _esdl__parentIsConstrained;
  override abstract string describe();
}

abstract class CstObjSet: CstObjArrIntf
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

abstract class CstDomSet: CstVecPrim, CstVecArrIntf
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
  abstract CstDomSet unroll(CstIterator iter, uint n);
  
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

abstract class CstExpr
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

  abstract CstVecExpr unroll(CstIterator iter, uint n);

  abstract bool isOrderingExpr();

  abstract uint bitcount();
  abstract bool signed();

}

abstract class CstLogicExpr: CstExpr
{
  abstract DistRangeSetBase getDist();
  abstract CstVecExpr isNot(CstDomain A);
  abstract CstLogicExpr unroll(CstIterator iter, uint n);

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
  abstract uint size();
  abstract string name();
  abstract string fullName();
  abstract CstIterator unrollIterator(CstIterator iter, uint n);
  abstract CstDomain getLenVec();
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

  Folder!(CstPredicate, "predList") _predList;
  Folder!(CstPredicate, "dynPredList") _dynPredList;
  
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
	_predList.length != _preds.length ||
	_dynPredList.length != _dynPreds.length) {
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
      foreach (pred; _dynPreds) pred._group = null;
      _dynPreds.reset();
      foreach (pred; sort!((x, y) => x.name() < y.name())(_dynPredList[])) {
	pred._group = this;
	if (pred._soft != 0) _hasSoftConstraints = true;
	if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
	if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
	_dynPreds ~= pred;
      }
    }
    // for the next cycle
    _predList.reset();
    _dynPredList.reset();
  }

  void annotate() {
    foreach (pred; _preds) {
      foreach (rnd; pred._rnds) {
	rnd.annotate(this);
      }
      foreach (rndArr; pred._rndArrs) {
	addDomainArr(rndArr);
	foreach (rnd; rndArr[]) {
	  rnd.annotate(this);
	}
      }
      foreach (var; pred._vars) {
	var.annotate(this);
      }
      foreach (varArr; pred._varArrs) {
	addVariableArr(varArr);
	foreach (var; varArr[]) {
	  var.annotate(this);
	}
      }
    }
  }

  Charbuf _sig;
  
  string signature() {
    _sig.reset();
    _sig ~= "GROUP:\n";
    foreach (pred; _preds) {
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
    // writeln(this.describe());
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
	    foreach (dom; _doms) totalBits += dom.bitcount();
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
      _solver.solve(this);
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
    _expr.visit(solver);
  }
  // alias _expr this;

  enum State: byte {
    INIT = 0,
    GROUPED = 1,
    SOLVED = 2,
  }

  _esdl__ConstraintBase _constraint;
  uint _statement;
  _esdl__Proxy _proxy;
  CstScope _scope;
  CstLogicExpr _expr;
  CstPredicate _parent;
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

  this(_esdl__ConstraintBase cst, uint stmt, _esdl__Proxy proxy,
       uint soft, CstLogicExpr expr, CstPredicate parent=null,
       CstIterator unrollIter=null, uint unrollIterVal=0// ,
       // CstIterator[] iters ...
       ) {
    synchronized(typeid(CstPredicate)) {
      _id = _count++;
    }
    assert(proxy !is null);
    _constraint = cst;
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
      
    this.setDomainContext();

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
    if (iter.getLenVec().isSolved()) {
      this.unroll(iter);
      _unrollCycle = _proxy._cycle;
    }
  }
  
  void unroll(CstIterator iter) {
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
	_uwPreds ~= new CstPredicate(_constraint, _statement, _proxy, _soft,
				     _expr.unroll(iter, i), this, iter, i// ,
				     // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
				     );
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

  final void setDomainContext() {
    CstIterator[] varIters;
    
    _expr.setDomainContext(this, _rnds, _rndArrs, _vars, _varArrs, _vals,
			   varIters, _idxs, _bitIdxs, _deps);

    // foreach (varIter; varIters) {
    //   import std.stdio;
    //   stderr.writeln("Found Iterator: ", varIter.name());
    // }
    // if (_iters.length > 0) {
    //   _len = _iters[0].getLenVec();
    // }
    foreach (rnd; _rnds) {
      rnd.registerRndPred(this);
      if (! rnd.isStatic()) {
	_dynRnds ~= rnd;
      }
    }
    foreach (rnd; _rndArrs) {
      rnd.registerRndPred(this);
    }

    // foreach (var; _vars) var.registerVarPred(this);

    if ((! this.isVisitor()) && _rndArrs.length == 0) {
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
      _iters = varIters;
    }
    else {
      _iters = _parsedIters.filter!(itr =>
				    canFind!((CstIterator a, CstIterator b) => a == b)
				    (varIters, itr)).array;
    }
    
    if (_iters.length != 0) _iters[0].registerRolled(this);
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
      assert(_group is null, "A predicate may be added to a group, but group should not change");
      group.needSync();
    }
    if (_rndArrs.length != 0) group.needSync();
    if (_bitIdxs.length != 0) group.needSync();
    if (this.isDynamic()) group.addDynPredicate(this);
    else group.addPredicate(this);
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

  void writeSignature(ref Charbuf str) {
    import std.conv: to;
    if (_soft != 0) {
      str ~= '!';
      str ~= _soft.to!string();
      str ~= ':';
    }
    _expr.writeExprString(str);
  }

  bool _isDist;
  bool isDist() { return _isDist; }
  void isDist(bool b) { _isDist = b; }

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
  this(_esdl__ConstraintBase cst, uint stmt, _esdl__Proxy proxy,
       uint soft, CstLogicExpr expr, CstPredicate parent=null,
       CstIterator unrollIter=null, uint unrollIterVal=0// ,
       // CstIterator[] iters ...
       ) {
    // import std.stdio;
    // writeln("Creating a visitor predicate: ", cst.name());
    super(cst, stmt, proxy, soft, expr, parent, unrollIter, unrollIterVal);
  }

  override bool isVisitor() {
    return true;
  }

  override void unroll(CstIterator iter) {
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
	_uwPreds ~= new CstVisitorPredicate(_constraint, _statement, _proxy, _soft,
					    _expr.unroll(iter, i), this, iter, i// ,
					    // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
					    );
      }
    }

    // Do not use foreach here since we may have more elements in the
    // array than the current value of currLen
    for (size_t i=0; i!=currLen; ++i) {
      if (_uwPreds[i]._iters.length == 0) { // completely unrolled
	_uwPreds[i]._expr.visit();
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

class CstBlock
{
  CstPredicate[] _preds;
  bool[] _booleans;

  string describe() {
    string name_ = "";
    foreach(pred; _preds) {
      name_ ~= " & " ~ pred._expr.describe() ~ "\n";
    }
    return name_;
  }

  void clear() {
    _preds.length = 0;
  }

  bool isEmpty() {
    return _preds.length == 0;
  }
  
  void opOpAssign(string op)(bool other)
    if(op == "~") {
      _booleans ~= other;
    }

  void opOpAssign(string op)(CstPredicate other)
    if(op == "~") {
      _preds ~= other;
    }

  void opOpAssign(string op)(CstBlock other)
    if(op == "~") {
      if(other is null) return;
      foreach(pred; other._preds) {
	_preds ~= pred;
      }
      foreach(boolean; other._booleans) {
	_booleans ~= boolean;
      }
    }

}
