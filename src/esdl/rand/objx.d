module esdl.rand.objx;

import esdl.data.bvec;
import esdl.data.bstr;
import esdl.data.queue;
import std.traits: isIntegral, isBoolean, isArray, KeyType,
  isStaticArray, isDynamicArray, isAssociativeArray;

import esdl.rand.misc;
import esdl.rand.base: CstVecTerm, CstIterator,
  CstDomBase, CstDomSet, CstVarNodeIntf, CstVecNodeIntf,
  CstObjArrIntf, CstVarGlobIntf, CstObjectVoid, CstObjArrVoid,
  CstDepIntf, CstObjectIntf, CstObjSetIntf, CstObjSet, CstObjStub;
import esdl.rand.pred: CstPredicate;
import esdl.rand.proxy: _esdl__Proxy, _esdl__CstProcessor;
import esdl.rand.expr: CstRangeExpr;
import esdl.rand.domain: CstArrIterator, CstArrLength, CstArrHierLength;
import esdl.rand.meta: _esdl__ProxyResolve, _esdl__LambdaProxyResolve;
import esdl.rand.misc: _esdl__staticCast;

import std.algorithm.searching: canFind;
import esdl.base.rand: _esdl__RandGen, getRandGen;
// import esdl.base.alloc: make;

interface CstObjIndexed { }

// V represents the type of the declared array/non-array member
// N represents the level of the array-elements we have to traverse
// for the elements this CstObject represents

class CstObjectGlob(V, rand RAND_ATTR, alias SYM)
  : CstObject!(V, RAND_ATTR, 0), CstVarGlobIntf
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  this(_esdl__Proxy parent) {
    super(parent);
  }

  final override void* _esdl__refPtr() {
    return cast(void*) _esdl__ref();
  }

  static if (is (V == struct)) {
    final override V* _esdl__ref() {
      return & SYM;
    }
  }
  else {
    final override V _esdl__ref() {
      return SYM;
    }
  }

  final override string _esdl__name() {
    return SYM.stringof;
  }

  final override bool _esdl__isDomainInRange() { return true; }
  final override bool _esdl__isRand() { return false; }
  final override bool _esdl__isStatic() { return true; }
  final override bool _esdl__isRolled(_esdl__CstProcessor proc) { return false; }
  final override bool _esdl__depsAreResolved() { return true; }
  final override typeof(this) _esdl__getResolvedNode(_esdl__CstProcessor proc) { return this; }
  final override typeof(this) _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) { return this; }

}

class CstObjectGlobEnum(V, rand RAND_ATTR)
  : CstObject!(V, RAND_ATTR, 0), CstVarGlobIntf
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static assert (_esdl__ISRAND == false);

  V _var;

  this(_esdl__Proxy parent, V var) {
    _var = var;
    super(parent);
  }

  final override string _esdl__name() {
    import std.conv: to;
    return _var.to!string();
  }

  static assert (is (V == struct));
  final override V* _esdl__ref() {
    return &_var;
  }

  final override void* _esdl__refPtr() {
    return cast(void*) _esdl__ref();
  }

  final override bool _esdl__isDomainInRange() { return true; }
  final override bool _esdl__isRand() { return false; }
  final override bool _esdl__isStatic() { return true; }
  final override bool _esdl__isRolled(_esdl__CstProcessor proc) { return false; }
  final override bool _esdl__depsAreResolved() { return true; }
  final override typeof(this) _esdl__getResolvedNode(_esdl__CstProcessor proc) { return this; }
  // no unrolling is possible without adding rand proxy
  final override typeof(this) _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
    return this;
  }

}

class CstObjectIdx(V, rand RAND_ATTR, VV, int IDX,
		   P, int PIDX): CstObject!(V, RAND_ATTR, 0)
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  enum int _esdl__PROXYINDEX = PIDX;

  this(_esdl__Proxy parent) {
    assert(parent !is null);
    super(parent);
  }

  final override string _esdl__name() {
    alias TT = P._esdl__Type;
    return TT.tupleof[IDX].stringof;
  }

  final override void* _esdl__refPtr() {
    return cast(void*) _esdl__ref();
  }

  static if (is (V == struct)) {
    final override V* _esdl__ref() {
      assert (_parent !is null);
      _esdl__PROXYT proxy = _esdl__staticCast!_esdl__PROXYT(_parent);
      assert (proxy._esdl__ref() !is null);
      return &(proxy._esdl__ref().tupleof[IDX]);
    }
  }
  else {
    final override V _esdl__ref() {
      assert (_parent !is null);
      _esdl__PROXYT proxy = _esdl__staticCast!_esdl__PROXYT(_parent);
      assert (proxy._esdl__ref() !is null);
      return proxy._esdl__ref().tupleof[IDX];
    }
  }
  
  final override bool _esdl__isDomainInRange() { return _parent._esdl__isDomainInRange(); }
  final override bool _esdl__isRand() {
    return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
  }
  final override bool _esdl__isStatic() { return _parent._esdl__isStatic; }
  final override bool _esdl__isRolled(_esdl__CstProcessor proc) { return _parent._esdl__isRolled(proc); }
  final override bool _esdl__depsAreResolved() { return _parentsDepsAreResolved; }

  final override typeof(this) _esdl__getResolvedNode(_esdl__CstProcessor proc) {
    if (_parentsDepsAreResolved) return this;
    else {
      P uparent = _esdl__staticCast!(P)(_parent._esdl__getResolvedNode(proc));
      assert (uparent !is null);
      return uparent.tupleof[PIDX];
    }
  }

  final override typeof(this) _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
    if (_parent._esdl__isRoot()) {
      return this;
    }
    else {
      P uparent = _esdl__staticCast!(P)(_parent._esdl__unroll(iter, n, proc));
      assert (uparent !is null);
      return uparent.tupleof[PIDX];
    }
  }

  final override bool rand_mode() {
    static if (_esdl__PROXYT._esdl__HAS_RAND_INFO == false) return true;
    else {
      assert (_parent !is null);
      _esdl__PROXYT proxy = _esdl__staticCast!_esdl__PROXYT(_parent);
      assert (proxy._esdl__ref() !is null);
      return proxy._esdl__ref().rand_mode!(PIDX)();
    }
  }


}

class CstRootLambdaProxy(V) if (is (V == class) || is (V == struct) ||
				(is (V == S*, S) && is (S == struct))):
  CstRootProxy!(V)
    {
      static if (is (V == class) || (is (V == S*, S) && is (S == struct))) {
	this(V v) {super(v);}
      }
      else {
	this(V* v) {super(v);}
      }

      _esdl__Proxy _esdl__getLambdaProxy(uint cstID) {
	_cstID = cstID;
	return _esdl__getProxy();
      }

      alias PROXYT = _esdl__LambdaProxyResolve!(LEAF);

      // can not store _proxy as PROXYT since that results in
      // cyclic type dependency
      _esdl__Proxy[] _proxys;

      _esdl__Proxy _esdl__getLambda()(uint _cstID) {
	if (_proxys.length <= _cstID) _proxys.length = _cstID + 1;
	_esdl__Proxy proxy = _proxys[_cstID];
	if (proxy is null) {
	  // version (CACHEDPROXIES) {
	  //   proxy = PROXYT._esdl__make(this);
	  // }
	  // else {
	  proxy = new PROXYT(this);
	  // }
	  _proxys[_cstID] = proxy;
	}
	return proxy;
      }

      uint _cstID;		// currently active cstID

      override _esdl__Proxy _esdl__getProxy() {
	return _esdl__getLambda(_cstID);
      }


    }


class CstRootProxy(V) if (is (V == class) || is (V == struct) ||
			  (is (V == S*, S) && is (S == struct))):
  CstObject!(V, rand.init, 0)
    {
      enum _esdl__ISRAND = true;
      enum _esdl__HASPROXY = true;

      static if (is (V == class) || (is (V == S*, S) && is (S == struct))) {
	this(V v) {
	  import esdl.base.core: Procedure;
	  super(null);
	  _esdl__randObj = v;
	  _esdl__proc = new _esdl__CstProcessor(this);
	  auto proc = Procedure.self;
	  if (proc !is null) {
	    _esdl__proc._seed = 0; // uniform!(uint)(procRgen);
	  }
	  else {
	    // no active simulation -- use global rand generator
	    _esdl__proc._seed = 0; // uniform!(uint)();
	  }
	}
	void updateRandObj(V v) {
	  _esdl__randObj = v;
	}
      }
      else {
	this(V* v) {
	  import esdl.base.core: Procedure;
	  super(null);
	  _esdl__randObj = v;
	  _esdl__proc = new _esdl__CstProcessor(this);
	  auto proc = Procedure.self;
	  if (proc !is null) {
	    _esdl__proc._seed = 0; // uniform!(uint)(procRgen);
	  }
	  else {
	    // no active simulation -- use global rand generator
	    _esdl__proc._seed = 0; // uniform!(uint)();
	  }
	}
	void updateRandObj(V* v) {
	  _esdl__randObj = v;
	}
      }

      final override void* _esdl__refPtr() {
	return cast(void*) _esdl__ref();
      }

      static if (is (V == struct)) {
	V* _esdl__randObj;
	final override V* _esdl__ref() {
	  return _esdl__randObj;
	}
      }
      else {
	V _esdl__randObj;
	final override V _esdl__ref() {
	  return _esdl__randObj;
	}
      }

      final override string _esdl__name() {
	return "$root";
      }
      
      final override bool _esdl__isRoot() { return true; }
      
      final override bool _esdl__isDomainInRange() { return true; }
      final override bool _esdl__isRand() { return true; }
      final override bool _esdl__isStatic() { return true; }
      final override bool _esdl__isRolled(_esdl__CstProcessor proc) { return false; }
      final override bool _esdl__depsAreResolved() { return true; }
      final override typeof(this) _esdl__getResolvedNode(_esdl__CstProcessor proc) { return this; }
      final override typeof(this) _esdl__unroll(CstIterator iter, ulong n,
						_esdl__CstProcessor proc) {
	return this;
      }

      final override bool rand_mode() {
	return true;
      }

      _esdl__CstProcessor _esdl__proc;

      final override _esdl__CstProcessor _esdl__getProc() {
	return _esdl__proc;
      }

      debug (CSTSOLVER) {
	enum bool _esdl__DEBUGSOVER = true;
      }
      else {
	enum bool _esdl__DEBUGSOVER = false;
      }

      final override bool _esdl__debugSolver() {
	return _esdl__DEBUGSOVER;
      }

    }

abstract class _esdl__TypedStub(LEAF): CstObjStub
{
  static if (is (LEAF == struct))
    abstract LEAF* _esdl__ref();
  else
    abstract LEAF _esdl__ref();
}
			       

abstract class _esdl__ObjStub(V, rand RAND_ATTR, int N):
  _esdl__TypedStub!(LeafElementType!V), rand.disable, rand.barrier
{
  // import esdl.rand.meta: _esdl__ProxyResolve;

  alias LEAF = LeafElementType!V;

  alias PROXYT = _esdl__ProxyResolve!(LEAF);

  // can not store _proxy as PROXYT since that results in
  // cyclic type dependency
  _esdl__Proxy _proxy;
  _esdl__Proxy _parent;

  final override _esdl__Proxy _esdl__parent() {
    // assert (_parent !is null);
    return _parent;
  }

  final void _esdl__setStub() {
    // In case the Stub does not have a proxy yet
    if (_proxy !is null) _proxy._esdl__setStub(this);
  }

  this(_esdl__Proxy parent) {
    _parent = parent;
    assert (_proxy is null);
  }
  
  PROXYT _esdl__get()() {
    if (_proxy is null) {
      // assert (_parent !is null);
      version (CACHEDPROXIES) {
	_proxy = PROXYT._esdl__make(this);
      }
      else {
	_proxy = new PROXYT(this);
      }
    }
    return _esdl__staticCast!PROXYT(_proxy);
  }

  _esdl__Proxy _esdl__getProxy() {
    return _esdl__get();
  }

  auto opDispatch(string WHAT)() {
    return __traits(getMember, _esdl__get(), WHAT);
  }


  // These functions can not be handled with opDispatch because these are
  // actually virtual functions in the proxy class??

  void _esdl__doConstrain(_esdl__CstProcessor proc, bool callPreRandomize) {
    this._esdl__get()._esdl__doConstrain(proc, callPreRandomize);
  }
  
  void _esdl__doRandomize(_esdl__RandGen randGen) {
    this._esdl__get()._esdl__doRandomize(randGen);
  }

  final CstIterator _esdl__iter() {
    return null;
  }

  abstract typeof(this) _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc);

}

abstract class CstObjectBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) == 0):
    _esdl__ObjStub!(V, RAND_ATTR, N), rand.disable, rand.barrier
      {
	enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
	alias LEAF = LeafElementType!V;
	alias RAND = RAND_ATTR;

	this(_esdl__Proxy parent) {
	  super(parent);
	}

	override string _esdl__getName() {
	  return _esdl__name();
	}

	S to(S)() if (is (S == string)) {
	  static if (HAS_RAND_ATTRIB) {
	    if (_esdl__isRand) {
	      return "RAND#" ~ _esdl__name();
	    }
	    else {
	      return "VAL#" ~ _esdl__name();
	    }
	  }
	  else {
	    return "VAR#" ~ _esdl__name();
	  }
	}

	override string toString() {
	  import std.conv: to;
	  return this.to!string();
	}

	bool rand_mode() { return true; }
	// overridden in derived classes
	override bool _esdl__isRand() { assert (false); }
      }

abstract class CstObject(V, rand RAND_ATTR, int N) if (N == 0):
  CstObjectBase!(V, RAND_ATTR, N)
    {
      alias RV = typeof(this);

      _esdl__Proxy _parent;
      bool _parentsDepsAreResolved;
      
      _esdl__Proxy _esdl__getParentProxy() {
	return _parent;
      }

      // Call super only after the _parent has been set
      this(_esdl__Proxy parent) {
	_parent = parent;
	if (_parent is null) _parentsDepsAreResolved = true; // root
	else _parentsDepsAreResolved = _parent._esdl__depsAreResolved();
	super(parent);
      }

      override bool _esdl__isRand() {
	if (_parent is null) return true;
	return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
      }

      override bool _esdl__isDomainInRange() {
	if (_parent is null) return true;
	return _parent._esdl__isDomainInRange();
      }

      final override string _esdl__getFullName() {
	if (_parent is null) return "$root";
	if (_parent._esdl__isRoot()) return _esdl__name();
	else  
	  return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      bool _esdl__isStatic() {
	if (_parent is null) return true;
	return _parent._esdl__isStatic();
      }

      bool _esdl__isReal() {
	if (_parent is null) return true;
	return _parent._esdl__isReal();
      }

      bool _esdl__isRolled(_esdl__CstProcessor proc) {
	if (_parent is null) return false;
	return _parent._esdl__isRolled(proc);		// N == 0
      }

      bool _esdl__depsAreResolved() { // this level is resolved
	return _parentsDepsAreResolved;
      }

      RV _esdl__getResolvedNode(_esdl__CstProcessor proc) {
	return this;
      }

      // RV
      override typeof(this) _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
	return this;
      }

      static if (is (LEAF == struct)) {
	LEAF* getRef() {
	  return _esdl__ref();
	}
      }
      else {
	LEAF getRef() {	// 
	  return _esdl__ref();
	}
      }

      override void _esdl__scan(_esdl__CstProcessor proc) {
	// import std.stdio;
	// writeln("Visiting: ", this._esdl__getFullName());
	assert (false);
	// assert (this.getRef() !is null);
	// _esdl__doConstrain(_esdl__getRootProxy());
      }

      void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	// no parent
      }

}

// Array Element
class CstObject(V, rand RAND_ATTR, int N) if (N != 0):
  CstObjectBase!(V, RAND_ATTR, N), CstObjIndexed
    {
      alias RV = typeof(this);
      alias P = CstObjArr!(V, RAND_ATTR, N-1);
      P _parent;

      _esdl__Proxy _esdl__getParentProxy() {
	assert (_parent !is null);
	return _parent._esdl__getParentProxy();
      }

      bool _parentsDepsAreResolved;

      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;
      immutable bool _nodeIsMapped = false;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      // Call super only after the _parent has been set
      this(P parent, CstVecTerm indexExpr, bool isMapped) {
	assert (parent !is null);
	_parent = parent;
	_nodeIsMapped = isMapped;
	super(_esdl__getParentProxy());
	_indexExpr = indexExpr;
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
      }

      // Call super only after the _parent has been set
      this(P parent, ulong index, bool isMapped) {
	assert (parent !is null);
	_parent = parent;
	_nodeIsMapped = isMapped;
	super(_esdl__getParentProxy());
	_pindex = index;
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
      }

      final override string _esdl__name() {
	import std.conv: to;
	if (_indexExpr is null)
	  return (_nodeIsMapped ? "[#" : "[%") ~ _pindex.to!string() ~ "]";
	else
	  return (_nodeIsMapped ? "[#" : "[%") ~ _indexExpr.describe() ~ "]";
      }
      
      final override bool _esdl__isRand() { // no rand_mode since this is an array element
	return HAS_RAND_ATTRIB && _parent._esdl__isRand();
      }

      final override bool _esdl__isDomainInRange() {
	if (_indexExpr !is null) assert (false, "Unresolved Index");
	else return _parent._esdl__isDomainInRange() && _parent.inRangeIndex(_pindex);
      }

      // override bool opEquals(Object other) {
      // 	auto rhs = cast (RV) other;
      // 	if (rhs is null) return false;
      // 	else return (_parent == rhs._parent && _indexExpr == _indexExpr);
      // }
      
      final bool _esdl__isStatic() {
	return (_indexExpr is null ||
		_indexExpr.isIterator ||
		_indexExpr.isConst) &&
	  _parent._esdl__isStatic();
      }

      final bool _esdl__isReal() {
	return _indexExpr is null &&
	  _parent._esdl__isReal();
      }

      final bool _esdl__isRolled(_esdl__CstProcessor proc) {
	return (_indexExpr !is null &&
		_indexExpr.isIterator) ||
	  _parent._esdl__isRolled(proc);
      }

      final override string _esdl__getFullName() {
	return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      final override bool _esdl__depsAreResolved() {
	return _parentsDepsAreResolved && _nodeIsMapped;
      }

      final override RV _esdl__getResolvedNode(_esdl__CstProcessor proc) {
	if (_resolvedCycle != proc._cycle) {
	  auto parent = _parent._esdl__getResolvedNode(proc);
	  if (_indexExpr) {
	    _resolvedObj = parent[cast(size_t) _indexExpr.evaluate()];
	  }
	  else {
	    static if (isAssociativeArray!V) {
	      _resolvedObj = _nodeIsMapped ? parent[_pindex] :
		parent.getElem(_parent.mapIndex(_pindex));
	    }
	    else {
	      _resolvedObj = parent[_pindex];
	    }
	  }
	  _resolvedCycle = proc._cycle;
	}
	return _resolvedObj;
      }

      // RV
      final override RV _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
	if (_indexExpr) {
	  return _parent._esdl__unroll(iter, n, proc)[_indexExpr._esdl__unroll(iter, n, proc)];
	}
	else {
	  return _parent._esdl__unroll(iter, n, proc)[_pindex];
	}
      }
      
      final override void* _esdl__refPtr() {
	if (_indexExpr is null // || _indexExpr.isConst()
	    )
	  return cast(void*) _esdl__ref();
	else return null;
      }

      static if (is (LEAF == struct)) {
	LEAF* getRef() {
	  if (_indexExpr) {
	    return getRefTmpl(_parent, cast(size_t) _indexExpr.evaluate());
	  }
	  else {
	    return getRefTmpl(_parent, this._pindex);
	  }
	}
	final override LEAF* _esdl__ref() {
	  return getRef();
	}
      }
      else {
	LEAF getRef() {
	  if (_indexExpr) {
	    return getRefTmpl(_parent, cast(size_t) _indexExpr.evaluate());
	  }
	  else {
	    return getRefTmpl(_parent, this._pindex);
	  }
	}
	final override LEAF _esdl__ref() {
	  return getRef();
	}
      }

      final override void _esdl__scan(_esdl__CstProcessor proc) {
	// import std.stdio;
	// writeln("Visiting: ", this._esdl__getFullName());
	assert (this.getRef() !is null);
	if (this._esdl__isRand()) {
	  _esdl__doConstrain(proc, true);
	}
      }

      final void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	if (_parent._esdl__isStatic()) {
	  import std.algorithm.searching: canFind;
	  auto len = _parent.arrLen();
	  if (! pred._unrolledIters[].canFind(len.iterVar()))
	    pred.addDep(len, context);
	}

	_parent.setDomainContext(pred, context);

	if (_indexExpr !is null) {
	  // Here we need to put the parent as a dep for the pred
	  // and since this prim needs resolution, the constituents of
	  // the indexExpr need to trigger a function that finds out
	  // whether the _indexExpr has been fully resolved or
	  // not. When the indexExpr gets resolved, it should inform
	  // the parent about resolution which in turn should inform
	  // the pred that it can go ahead
	  _indexExpr.setDomainContext(pred, DomainContextEnum.INDEX);
	}
      }
    }


class CstObjArrGlob(V, rand RAND_ATTR, int N, alias SYM)
  : CstObjArr!(V, RAND_ATTR, N), CstVarGlobIntf
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  this(_esdl__Proxy parent) {
    super(parent);
  }

  // no unrolling is possible without adding rand proxy
  final override RV _esdl__unroll(CstIterator iter, ulong n,
				  _esdl__CstProcessor proc) {
    return this;
  }

  final override V* _esdl__ref() {
    return & SYM;
  }

  final override string _esdl__name() {
    return SYM.stringof;
  }
}

class CstObjArrGlobEnum(V, rand RAND_ATTR, int N)
  : CstObjArr!(V, RAND_ATTR, N), CstVarGlobIntf
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static assert (_esdl__ISRAND == false);

  V _var;
  
  this(_esdl__Proxy parent, V var) {
    _var = var;
    super(parent);
  }

  final override string _esdl__name() {
    import std.conv: to;
    return _val.to!string();
  }

  final override V* _esdl__ref() {
    return &_var;
  }

  final override bool _esdl__isDomainInRange() { return true; }
  final override bool _esdl__isRand() { return false; }
  final override bool _esdl__isStatic() { return true; }
  final override bool _esdl__isRolled(_esdl__CstProcessor proc) { return false; }
  final override bool _esdl__depsAreResolved() { return true; }
  final override typeof(this) _esdl__getResolvedNode(_esdl__CstProcessor proc) { return this; }
  // no unrolling is possible without adding rand proxy
  final override typeof(this) _esdl__unroll(CstIterator iter, ulong n,
					    _esdl__CstProcessor proc) {
    return this;
  }

}


// Arrays (Multidimensional arrays as well)
class CstObjArrIdx(V, rand RAND_ATTR, VV, int IDX,
		   P, int PIDX): CstObjArr!(V, RAND_ATTR, 0)
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  enum int _esdl__PROXYINDEX = PIDX;

  this(_esdl__Proxy parent) {
    super(parent);
  }

  final override string _esdl__name() {
    alias TT = P._esdl__Type;
    return TT.tupleof[IDX].stringof;
  }

  final override V* _esdl__ref() {
    assert (_parent !is null);
    _esdl__PROXYT proxy = _esdl__staticCast!_esdl__PROXYT(_parent);
    assert (proxy._esdl__ref() !is null);
    return &(proxy._esdl__ref().tupleof[IDX]);
  }

  final override bool _esdl__isDomainInRange() { return _parent._esdl__isDomainInRange(); }
  final override bool _esdl__isRand() {
    return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
  }
  final override bool _esdl__isStatic() { return _parent._esdl__isStatic(); }
  final override bool _esdl__isRolled(_esdl__CstProcessor proc) { return _parent._esdl__isRolled(proc); }
  final override bool _esdl__depsAreResolved() { return _parentsDepsAreResolved; }

  final override typeof(this) _esdl__getResolvedNode(_esdl__CstProcessor proc) {
    if (_parentsDepsAreResolved) return this;
    else {
      P uparent = _esdl__staticCast!(P)(_parent._esdl__getResolvedNode(proc));
      assert (uparent !is null);
      return uparent.tupleof[PIDX];
    }
  }

  final override typeof(this) _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
    if (_parent._esdl__isRoot()) {
      return this;
    }
    else {
      P uparent = _esdl__staticCast!(P)(_parent._esdl__unroll(iter, n, proc));
      assert (uparent !is null);
      return uparent.tupleof[PIDX];
    }
  }

  final override bool rand_mode() {
    static if (_esdl__PROXYT._esdl__HAS_RAND_INFO == false) return true;
    else {
      assert (_parent !is null);
      _esdl__PROXYT proxy = _esdl__staticCast!_esdl__PROXYT(_parent);
      assert (proxy._esdl__ref() !is null);
      return proxy._esdl__ref().rand_mode!(PIDX)();
    }
  }

}

abstract class CstObjArrStub(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) != 0) : CstObjArrVoid, CstObjArrIntf // CstObjSetIntf
{

  alias RV = CstObjArr!(V, RAND_ATTR, N);

  enum ARR_ORDER = _esdl__ArrOrder!(V, N);
  enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
  alias LEAF = LeafElementType!V;
  alias RAND = RAND_ATTR;

  alias L = ElementTypeN!(V, N);
  alias E = ElementTypeN!(V, N+1);

  static if (_esdl__ArrOrder!(V, N+1) == 0) {
    alias EV = CstObject!(V, RAND_ATTR, N+1);
  }
  else {
    alias EV = CstObjArr!(V, RAND_ATTR, N+1);
  }

  static if (isAssociativeArray!L) {
    static assert(N == 0,
		  "Only top level Associative Arrays are supported for now");
  }

  CstObjArrProxy!(V, RAND_ATTR, N) _proxy;

  final void _esdl__setStub() {
    assert (_proxy !is null);
    _proxy._esdl__setStub(this);
  }
  
  this() {
    _proxy = new CstObjArrProxy!(V, RAND_ATTR, N)(this);
  }

  abstract string _esdl__name();
    
  abstract EV createElem(uint i, bool isMapped);
  abstract EV createElem(CstVecTerm indexExpr, bool isMapped);
    
  // overridden in derived classes
  bool rand_mode() { return true; }
  // overridden in derived classes
  bool _esdl__isRand() { assert (false); }

  bool inRangeIndex(ulong index) { return index < getLen(); }
  
  abstract size_t getLen();
  abstract void setLen(size_t len);
    
  void buildElements(size_t v) { _proxy.buildElements(v); }

  abstract ulong mapIter(size_t iter);
  abstract size_t mapIndex(ulong index);

  string _esdl__getName() { return _proxy._esdl__getName(); }
  EV opIndex(CstVecTerm indexExpr) { return _proxy.opIndex(indexExpr); }

  EV opIndex(CstRangeExpr index) { return _proxy.opIndex(index); }

  EV opIndex(ulong index) { return _proxy.opIndex(index); }

  EV getElem(ulong index) { return _proxy.getElem(index);  }

  void _esdl__doRandomize(_esdl__RandGen randGen) { _proxy._esdl__doRandomize(randGen); }

  uint maxArrLen() { return _proxy.maxArrLen(); }

  CstArrLength!RV length() { return _proxy.length(); }

  CstArrLength!RV arrLen() { return _proxy.arrLen(); }

  CstArrHierLength!RV arrHierLen() { return _proxy.arrHierLen(); }

  void markArrLen(size_t length, _esdl__CstProcessor proc) { _proxy.markArrLen(length, proc); }

  EV _esdl__elems() { return _proxy._esdl__elems(); }

  
  final CstIterator _esdl__iter() { return  _proxy._esdl__iter(); }

  final CstVarNodeIntf _esdl__getChild(ulong n) { return _proxy._esdl__getChild(n); }


  final CstObjectIntf _esdl__nthLeaf(uint idx) { return _proxy._esdl__nthLeaf(idx); }    

  final void _esdl__scan(_esdl__CstProcessor proc) { }

  static if (N != 0) {
    abstract bool indexIsConst();
    abstract CstObjArrProxy!(V, RAND_ATTR, N-1) getParentArrProxy();
  }
  
}

class CstObjArrProxy(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) != 0): CstObjSet
{

  alias RV = CstObjArr!(V, RAND_ATTR, N);

  enum ARR_ORDER = _esdl__ArrOrder!(V, N);
  enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
  alias LEAF = LeafElementType!V;
  alias RAND = RAND_ATTR;

  alias L = ElementTypeN!(V, N);
  alias E = ElementTypeN!(V, N+1);

  static if (_esdl__ArrOrder!(V, N+1) == 0) {
    alias EV = CstObject!(V, RAND_ATTR, N+1);
  }
  else {
    alias EV = CstObjArr!(V, RAND_ATTR, N+1);
  }

  static if (isAssociativeArray!L) {
    static assert(N == 0,
		  "Only top level Associative Arrays are supported for now");
  }

  CstObjArrStub!(V, RAND_ATTR, N) _stub;

  final void _esdl__setStub(CstObjArrStub!(V, RAND_ATTR, N) stub) {
    _stub = stub;
  }
  
  this(CstObjArrStub!(V, RAND_ATTR, N) stub) {
    _stub = stub;
    _arrLen = new CstArrLength!RV(_esdl__staticCast!RV(_stub));
    _arrHierLen = new CstArrHierLength!RV(_esdl__staticCast!RV(_stub));
    super();
  }

  final override string _esdl__name() {
    return _stub._esdl__name();
  }
    
  CstArrLength!RV _arrLen;
  CstArrHierLength!RV _arrHierLen;

  EV[] _elems;
  EV   _negIndexElem;

  // abstract
  final EV createElem(uint i, bool isMapped) { return _stub.createElem(i, isMapped); }
  // abstract
  final EV createElem(CstVecTerm indexExpr, bool isMapped) { return _stub.createElem(indexExpr, isMapped); }
    
  final bool rand_mode() { return _stub.rand_mode(); }
  // overridden in derived classes
  final bool _esdl__isRand() { return _stub._esdl__isRand(); }

  final bool inRangeIndex(ulong index) { return _stub.inRangeIndex(index); }
  
  // abstract
  final size_t getLen() { return _stub.getLen(); }
  // abstract
  final void setLen(size_t len) { _stub.setLen(len); }
    
  override void markHierResolved(_esdl__CstProcessor proc) {
    _arrHierLen.setVal(_esdl__domsetLeafElemsCount, proc);
    static if (N != 0) {
      if (_stub.indexIsConst()) {
	_stub.getParentArrProxy().markChildResolved(_esdl__domsetLeafElemsCount, proc);
      }
    }
  }

  void markChildResolved(uint n, _esdl__CstProcessor proc) {
    assert (_esdl__domsetUnresolvedArrLen != 0 &&
	    _esdl__domsetUnresolvedArrLen != uint.max);
    _esdl__domsetUnresolvedArrLen -= 1;
    _esdl__domsetLeafElemsCount += n;
    if (_esdl__domsetUnresolvedArrLen == 0) {
      markHierResolved(proc);
    }
  }

  size_t _forcedLength;

  final void buildElements(size_t v) {
    if (! _arrLen.isSolved()) {
      if (v > _forcedLength) {
	_forcedLength = v;
      }
    }
    else if (v < _forcedLength) {
      return;
      // import std.string: format;
      // assert(false,
      // 	     format("Trying to set length %d, while it should be a minimum %d",
      // 		    v, _forcedLength));
    }
    uint currLen = cast(uint) _elems.length;
    if (currLen < v) {
      _elems.length = v;
      for (uint i=currLen; i!=v; ++i) {
	_elems[i] = createElem(i, true);
      }
    }
  }

  // abstract
  final ulong mapIter(size_t iter) { return _stub.mapIter(iter); }
  // abstract
  final size_t mapIndex(ulong index) { return _stub.mapIndex(index); }

  // virtual elements
  EV[CstVecTerm] _exprElems;

  // assoc array elements
  static if (isAssociativeArray!V) {
    EV[ulong] _assocElems;
  }

  final EV opIndex(CstVecTerm indexExpr) {
    if (indexExpr.isConst()) {
      ulong index = indexExpr.evaluate();
      return this[index];
    }
    else {
      EV* eptr = indexExpr in _exprElems;
      if (eptr is null) {
	EV elem = createElem(indexExpr, false);
	_exprElems[indexExpr] = elem;
	return elem;
      }
      else return *eptr;
    }
  }

  final EV opIndex(CstRangeExpr index) {
    assert (index._rhs is null);
    return this.opIndex(index._lhs);
  }

  final EV opIndex(ulong index) {
    // import std.stdio;
    // writeln(this._esdl__getFullName());
    static if (isAssociativeArray!V) {
      EV* eptr = index in _assocElems;
      if (eptr is null) {
	EV elem = createElem(cast (uint) index, false);
	_assocElems[index] = elem;
	return elem;
      }
      else return *eptr;
    }
    else {
      if (index > uint.max/2) { // negative index
	if (_negIndexElem is null) _negIndexElem = createElem(uint.max, false);
	return _negIndexElem;
      }
      else {
	if (index >= _elems.length) buildElements(index+1);
	return _elems[index];
      }
    }
  }

  final EV getElem(ulong index) {
    // import std.stdio;
    // writeln(this._esdl__getFullName());
    if (index > uint.max/2) { // negative index
      if (_negIndexElem is null) _negIndexElem = createElem(uint.max, false);
      return _negIndexElem;
    }
    else {
      if (index >= _elems.length) buildElements(index+1);
      return _elems[index];
    }
  }

  final void _esdl__doRandomize(_esdl__RandGen randGen) {
    static if (HAS_RAND_ATTRIB) {
      assert (_arrLen !is null);
      // if there is no constraint on the length of the array,
      // do not try to randomize it, since it will probably create a
      // big array which might lead to memory allocation issues
      buildElements(getLen());
      for (size_t i=0; i != _arrLen.evaluate(); ++i) {
	_elems[i]._esdl__doRandomize(randGen);
      }
    }
    else {
      assert (false);
    }
  }

  final uint maxArrLen() {
    static if (HAS_RAND_ATTRIB) {
      static if (isStaticArray!L) {
	return L.length;
      }
      else {
	return RAND_ATTR[N];
      }
    }
    else {
      return uint.max;
    }
  }

  final CstArrLength!RV length() {
    return _arrLen;
  }

  final CstArrLength!RV arrLen() {
    return _arrLen;
  }

  final CstArrHierLength!RV arrHierLen() {
    return _arrHierLen;
  }

  final void markArrLen(size_t length, _esdl__CstProcessor proc) {
    buildElements(length);
    // import std.stdio;
    // writeln("buildElements: ", length);
    static if (is (EV: CstObjectIntf)) {
      _esdl__domsetUnresolvedArrLen = 0;
      _esdl__domsetLeafElemsCount = cast(uint) length;
      markHierResolved(proc);
    }
    else {
      _esdl__domsetUnresolvedArrLen = cast(uint) length;
      _esdl__domsetLeafElemsCount = 0;
    }
  }

  final EV _esdl__elems() {
    return this[_esdl__iter()];
  }

  
  final CstIterator _esdl__iter() {
    CstArrIterator!RV iter = arrLen.makeIterVar();
    return iter;
  }

  final CstVarNodeIntf _esdl__getChild(ulong n) {
    return this[cast(size_t) n];
  }


  final CstObjectIntf _esdl__nthLeaf(uint idx) {
    static if (is (EV: CstObjectIntf)) {
      return _elems[idx];
    }
    else {
      uint iter;
      for (iter = 0; iter != _elems.length; ++iter) {
	assert (_elems[iter] !is null);
	if (idx >= _elems[iter]._proxy._esdl__domsetLeafElemsCount) {
	  idx -= _elems[iter]._proxy._esdl__domsetLeafElemsCount;
	}
	else {
	  break;
	}
      }
      return _elems[iter]._esdl__nthLeaf(idx);
    }
  }    

  final void _esdl__scan(_esdl__CstProcessor proc) {
    // import std.stdio;
    // writeln("Visiting: ", this._esdl__getFullName());
  }

}

abstract class CstObjArrBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) != 0): CstObjSet
{

  alias RV = CstObjArr!(V, RAND_ATTR, N);

  enum ARR_ORDER = _esdl__ArrOrder!(V, N);
  enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
  alias LEAF = LeafElementType!V;
  alias RAND = RAND_ATTR;

  alias L = ElementTypeN!(V, N);
  alias E = ElementTypeN!(V, N+1);

  static if (_esdl__ArrOrder!(V, N+1) == 0) {
    alias EV = CstObject!(V, RAND_ATTR, N+1);
  }
  else {
    alias EV = CstObjArr!(V, RAND_ATTR, N+1);
  }

  static if (isAssociativeArray!L) {
    static assert(N == 0,
		  "Only top level Associative Arrays are supported for now");
  }

  this() { super(); }
    
  CstArrLength!RV _arrLen;
  CstArrHierLength!RV _arrHierLen;

  EV[] _elems;
  EV   _negIndexElem;

  abstract EV createElem(uint i, bool isMapped);
  abstract EV createElem(CstVecTerm indexExpr, bool isMapped);
    
  bool rand_mode() { return true; }
  // overridden in derived classes
  bool _esdl__isRand() { assert (false); }

  bool inRangeIndex(ulong index) {
    return index < getLen();
  }
  
  abstract size_t getLen();
  abstract void setLen(size_t len);
    
  size_t _forcedLength;

  void buildElements(size_t v) {
    if (! _arrLen.isSolved()) {
      if (v > _forcedLength) {
	_forcedLength = v;
      }
    }
    else if (v < _forcedLength) {
      return;
      // import std.string: format;
      // assert(false,
      // 	     format("Trying to set length %d, while it should be a minimum %d",
      // 		    v, _forcedLength));
    }
    uint currLen = cast(uint) _elems.length;
    if (currLen < v) {
      _elems.length = v;
      for (uint i=currLen; i!=v; ++i) {
	_elems[i] = createElem(i, true);
      }
    }
  }

  abstract ulong mapIter(size_t iter);
  abstract size_t mapIndex(ulong index);

  EV opIndex(CstVecTerm indexExpr) {
    if (indexExpr.isConst()) {
      ulong index = indexExpr.evaluate();
      return this[index];
    }
    else {
      return createElem(indexExpr, false);
    }
  }

  EV opIndex(CstRangeExpr index) {
    assert (index._rhs is null);
    return this.opIndex(index._lhs);
  }

  EV opIndex(ulong index) {
    // import std.stdio;
    // writeln(this._esdl__getFullName());
    static if (isAssociativeArray!V) {
      return createElem(cast(int) index, false);
    }
    else {
      if (index > uint.max/2) { // negative index
	if (_negIndexElem is null) _negIndexElem = createElem(uint.max, false);
	return _negIndexElem;
      }
      else {
	if (index >= _elems.length) buildElements(index+1);
	return _elems[index];
      }
    }
  }

  EV getElem(ulong index) {
    // import std.stdio;
    // writeln(this._esdl__getFullName());
    if (index > uint.max/2) { // negative index
      if (_negIndexElem is null) _negIndexElem = createElem(uint.max, false);
      return _negIndexElem;
    }
    else {
      if (index >= _elems.length) buildElements(index+1);
      return _elems[index];
    }
  }

  void _esdl__doRandomize(_esdl__RandGen randGen) {
    static if (HAS_RAND_ATTRIB) {
      assert (_arrLen !is null);
      // if there is no constraint on the length of the array,
      // do not try to randomize it, since it will probably create a
      // big array which might lead to memory allocation issues
      buildElements(getLen());
      for (size_t i=0; i != _arrLen.evaluate(); ++i) {
	_elems[i]._esdl__doRandomize(randGen);
      }
    }
    else {
      assert (false);
    }
  }

  uint maxArrLen() {
    static if (HAS_RAND_ATTRIB) {
      static if (isStaticArray!L) {
	return L.length;
      }
      else {
	return RAND_ATTR[N];
      }
    }
    else {
      return uint.max;
    }
  }

  CstArrLength!RV length() {
    return _arrLen;
  }

  CstArrLength!RV arrLen() {
    return _arrLen;
  }

  CstArrHierLength!RV arrHierLen() {
    return _arrHierLen;
  }

  void markArrLen(size_t length, _esdl__CstProcessor proc) {
    buildElements(length);
    // import std.stdio;
    // writeln("buildElements: ", length);
    static if (is (EV: CstObjectIntf)) {
      _esdl__domsetUnresolvedArrLen = 0;
      _esdl__domsetLeafElemsCount = cast(uint) length;
      markHierResolved(proc);
    }
    else {
      _esdl__domsetUnresolvedArrLen = cast(uint) length;
      _esdl__domsetLeafElemsCount = 0;
    }
  }

  EV _esdl__elems() {
    return this[_esdl__iter()];
  }

  
  final CstIterator _esdl__iter() {
    CstArrIterator!RV iter = arrLen.makeIterVar();
    return iter;
  }

  final CstVarNodeIntf _esdl__getChild(ulong n) {
    return this[cast(size_t) n];
  }


  final CstObjectIntf _esdl__nthLeaf(uint idx) {
    static if (is (EV: CstObjectIntf)) {
      return _elems[idx];
    }
    else {
      uint iter;
      for (iter = 0; iter != _elems.length; ++iter) {
	assert (_elems[iter] !is null);
	if (idx >= _elems[iter]._esdl__domsetLeafElemsCount) {
	  idx -= _elems[iter]._esdl__domsetLeafElemsCount;
	}
	else {
	  break;
	}
      }
      return _elems[iter]._esdl__nthLeaf(idx);
    }
  }    

  final void _esdl__scan(_esdl__CstProcessor proc) {
    // import std.stdio;
    // writeln("Visiting: ", this._esdl__getFullName());
  }

}

abstract class CstObjArr(V, rand RAND_ATTR, int N) if (N == 0):
  CstObjArrStub!(V, RAND_ATTR, N)
    {
      _esdl__Proxy _parent;
      bool _parentsDepsAreResolved;
    
      _esdl__Proxy _esdl__getParentProxy() {
	return _parent;
      }

      abstract V* _esdl__ref();

      // Call super only after the _parent has been set
      this(_esdl__Proxy parent) {
	super();
	_parent = parent;
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
      }

      override bool _esdl__isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
      }

      override bool _esdl__isDomainInRange() {
	return _parent._esdl__isDomainInRange();
      }

      bool _esdl__isRolled(_esdl__CstProcessor proc) {
	return _parent._esdl__isRolled(proc);
      }

      bool _esdl__isStatic() {
	return _parent._esdl__isStatic();
      }

      bool _esdl__isReal() {
	return _parent._esdl__isReal();
      }

      final string _esdl__getFullName() {
	if (_parent._esdl__isRoot()) return _esdl__getName();
	else  
	  return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      bool _esdl__depsAreResolved() {
	return _parentsDepsAreResolved;
      }

      RV _esdl__getResolvedNode(_esdl__CstProcessor proc) {
	return this;
      }

      RV _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
	return this;
      }

      override void setLen(size_t len) {
	setLenTmpl(this, len);
      }
      
      override size_t getLen() {
	return getLenTmpl(this);
      }

      void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	// arrlen should not be handled here. It is handled as part
	// of the indexExpr in the elements when required (that is
	// when indexExpr is not contant, but an expression)
	  
	// auto iter = arrLen.makeIterVar();
	// iters ~= iter;

	// no parent
      }

      override ulong mapIter(size_t iter) {
	static if (isAssociativeArray!V) {
	  auto keys = (*(_esdl__ref())).keys;
	  if (keys.length <= iter) assert (false);
	  else return keys[iter];
	}
	else {
	  return iter;
	}
      }
	
      override size_t mapIndex(ulong index) {
	import std.string: format;
	static if (isAssociativeArray!V) {
	  foreach (i, key; (*(_esdl__ref())).keys) {
	    if (key == index) return i;
	  }
	  assert (false, format("Can not find key %s in Associative Array",
				cast(KeyType!V) index));
	}
	else {
	  return cast(size_t) index;
	}
      }

      override EV createElem(CstVecTerm indexExpr, bool isMapped) {
	return new EV(this, indexExpr, isMapped);
      }
  
      override EV createElem(uint i, bool isMapped) {
	return new EV(this, cast(uint) i, isMapped);
      }
  
    }

class CstObjArr(V, rand RAND_ATTR, int N) if (N != 0):
  CstObjArrStub!(V, RAND_ATTR, N), CstObjIndexed
    {
      alias P = CstObjArr!(V, RAND_ATTR, N-1);
      P _parent;

      _esdl__Proxy _esdl__getParentProxy() {
	return _parent._esdl__getParentProxy();
      }

      bool _parentsDepsAreResolved;
      
      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;
      immutable bool _nodeIsMapped = false;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      // Call super only after the _parent has been set
      this(P parent, CstVecTerm indexExpr, bool isMapped) {
	assert (parent !is null);
	super();
	_nodeIsMapped = isMapped;
	_parent = parent;
	_indexExpr = indexExpr;
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
      }

      // Call super only after the _parent has been set
      this(P parent, ulong index, bool isMapped) {
	assert (parent !is null);
	super();
	_nodeIsMapped = isMapped;
	_parent = parent;
	_pindex = index;
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
      }

      final override string _esdl__name() {
	import std.conv: to;
	if (_indexExpr is null)
	  return (_nodeIsMapped ? "[#" : "[%") ~ _pindex.to!string() ~ "]";
	else
	  return (_nodeIsMapped ? "[#" : "[%") ~ _indexExpr.describe() ~ "]";
      }
      
      final override bool _esdl__isRand() { // no rand_mode since this is an array element
	return HAS_RAND_ATTRIB && _parent._esdl__isRand();
      }

      final override bool _esdl__isDomainInRange() {
	if (_indexExpr !is null) assert (false, "Unresolved Index");
	else return _parent._esdl__isDomainInRange() && _parent.inRangeIndex(_pindex);
      }

      // final override bool opEquals(Object other) {
      // 	auto rhs = cast (RV) other;
      // 	if (rhs is null) return false;
      // 	else return (_parent == rhs._parent && _indexExpr == _indexExpr);
      // }
      
      final bool _esdl__isRolled(_esdl__CstProcessor proc) {
	return (_indexExpr !is null &&
		_indexExpr.isIterator) ||
	  _parent._esdl__isRolled(proc);
      }

      final bool _esdl__isStatic() {
	return (_indexExpr is null  ||
		_indexExpr.isIterator ||
		_indexExpr.isConst) &&
	  _parent._esdl__isStatic();
      }

      final bool _esdl__isReal() {
	return _indexExpr is null &&
	  _parent._esdl__isReal();
      }

      final string _esdl__getFullName() {
	return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      final override bool _esdl__depsAreResolved() {
	return _parentsDepsAreResolved && _nodeIsMapped;
      }

      final RV _esdl__getResolvedNode(_esdl__CstProcessor proc) {
	if (_resolvedCycle != proc._cycle) {
	  auto parent = _parent._esdl__getResolvedNode(proc);
	  if (_indexExpr) {
		_resolvedObj = parent[_indexExpr.evaluate()];
	  }
	  else {
	    static if (isAssociativeArray!V) {
	      _resolvedObj = _nodeIsMapped ? parent[_pindex] :
		parent.getElem(_parent.mapIndex(_pindex));
	    }
	    else {
	      _resolvedObj = parent[_pindex];
	    }
	  }
	  _resolvedCycle = proc._cycle;
	}
	return _resolvedObj;
      }

      final RV _esdl__unroll(CstIterator iter, ulong n, _esdl__CstProcessor proc) {
	if (_indexExpr) {
	  return _parent._esdl__unroll(iter, n, proc)[_indexExpr._esdl__unroll(iter, n, proc)];
	}
	else {
	  return _parent._esdl__unroll(iter, n, proc)[_pindex];
	}
      }

      final override void setLen(size_t len) {
	setLenTmpl(this, len);
      }
      

      final override size_t getLen() {
	return getLenTmpl(this);
      }

      void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	// arrlen should not be handled here. It is handled as part
	// of the indexExpr in the elements when required (that is
	// when indexExpr is not contant, but an expression)
	  
	// auto iter = arrLen.makeIterVar();
	// iters ~= iter;
	if (_parent._esdl__isStatic()) {
	  import std.algorithm.searching: canFind;
	  auto len = _parent.arrLen();
	  if (! pred._unrolledIters[].canFind(len.iterVar()))
	    pred.addDep(len, context);
	}

	_parent.setDomainContext(pred, context);
	if (_indexExpr !is null) {
	  _indexExpr.setDomainContext(pred, DomainContextEnum.INDEX);
	}
      }

      final override ulong mapIter(size_t iter) {
	static if (isAssociativeArray!L) {
	  static assert (false, "Associative Arrays are supported only at top array hierarchy");
	}
	else return iter;
      }
      
      final override size_t mapIndex(ulong index) {
	static if (isAssociativeArray!L) {
	  static assert (false, "Associative Arrays are supported only at top array hierarchy");
	}
	else return cast(size_t) index;
      }

      final override EV createElem(CstVecTerm indexExpr, bool isMapped) {
	return new EV(this, indexExpr, isMapped);
      }
  
      final override EV createElem(uint i, bool isMapped) {
	return new EV(this, cast(uint) i, isMapped);
      }
  
      final override bool indexIsConst() { return (_indexExpr is null); }
	
      final override CstObjArrProxy!(V, RAND_ATTR, N-1) getParentArrProxy() {
	return _parent._proxy;
      }

    }


private auto getArrElemTmpl(A, N...)(ref A arr, N indx)
  if ((isArray!A || isQueue!A || isAssociativeArray!A) &&
      N.length > 0 && isIntegral!(N[0])) {
    alias LEAF = LeafElementType!A;
    static if (isAssociativeArray!A) auto key = arr.keys[cast(size_t) (indx[0])];
    else                             size_t key = cast(size_t) (indx[0]);
    static if (N.length == 1) {
      static if (is (LEAF == struct)) {
	return &(arr[key]);
      }
      else {
	return (arr[key]);
      }
    }
    else {
      return getArrElemTmpl(arr[key], indx[1..$]);
    }
  }

private auto getRefTmpl(RV, J...)(RV rv, J indx)
     // if (is (RV: CstObjSet) && isIntegral!(J[0]))
       {
    static if (is (RV: CstObjIndexed)) {
      if (rv._indexExpr) {
	  assert (rv._indexExpr.isConst());
	  return getRefTmpl(rv._parent, cast (size_t) rv._indexExpr.evaluate(), indx);
	}
	else {
	  return getRefTmpl(rv._parent, rv._pindex, indx);
	}
      }
    else {
      return getArrElemTmpl(*(rv._esdl__ref()), indx);
    }
 }


private size_t getArrLenTmpl(A, N...)(ref A arr, N indx)
  if (isArray!A || isQueue!A || isAssociativeArray!A) {
    static if (N.length == 0) return arr.length;
    else {
      if (arr.length == 0) return 0;
      else {
	static if (isAssociativeArray!A) auto key = arr.keys[cast(size_t) (indx[0])];
	else                             size_t key = cast(size_t) (indx[0]);
	return getArrLenTmpl(arr[key], indx[1..$]);
      }
    }
  }

private size_t getLenTmpl(RV, N...)(RV rv, N indx) {
  static if (is (RV: CstObjIndexed)) {
    return getLenTmpl(rv._parent, rv._pindex, indx);
  }
  else {
    return getArrLenTmpl(*(rv._esdl__ref()), indx);
  }
}

private void setArrLen(A, N...)(ref A arr, size_t v, N indx)
  if (isArray!A || isQueue!A || isAssociativeArray!A) {
    static if(N.length == 0) {
      static if (isDynamicArray!A || isQueue!A) arr.length = v;
      else static if (isStaticArray!A)
	assert (false, "Can not set length of a fixed length array");
      else static if (isAssociativeArray!A)
	assert (false, "Can not set length of an associative array");
      else static assert (false, "Unhandled Exception");
    }
    else {
      static if (isAssociativeArray!A) auto key = arr.keys[cast(size_t) (indx[0])];
      else                             size_t key = cast(size_t) (indx[0]);
      setArrLen(arr[key], v, indx[1..$]);
    }
  }

private void setLenTmpl(RV, N...)(RV rv, size_t v, N indx) {
  static if (is (RV: CstObjIndexed)) {
    setLenTmpl(rv._parent, v, rv._pindex, indx);
  }
  else {
    setArrLen(*(rv._esdl__ref()), v, indx);
	  
  }
}
