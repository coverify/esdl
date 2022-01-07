module esdl.rand.objx;

import esdl.data.bvec;
import esdl.data.bstr;
import esdl.data.queue;
import std.traits: isIntegral, isBoolean, isArray, KeyType,
  isStaticArray, isDynamicArray, isAssociativeArray;

import esdl.rand.misc;
import esdl.rand.base: CstValue, CstVecTerm, CstIterator,
  CstDomBase, CstDomSet, CstObjSet, CstVarNodeIntf, CstVecNodeIntf,
  CstObjArrIntf, CstVarGlobIntf, CstObjectVoid, CstObjArrVoid,
  CstDepIntf, CstObjectIntf;
import esdl.rand.pred: CstPredicate;
import esdl.rand.proxy: _esdl__Proxy, _esdl__CstProcessor;
import esdl.rand.expr: CstRangeExpr;
import esdl.rand.domain: CstArrIterator, CstArrLength, CstArrHierLength;
import esdl.rand.meta: _esdl__ProxyResolve, _esdl__staticCast, _esdl__ARG;

import std.algorithm.searching: canFind;
import esdl.base.rand: _esdl__RandGen, getRandGen;

interface CstObjIndexed { }

// V represents the type of the declared array/non-array member
// N represents the level of the array-elements we have to traverse
// for the elements this CstObject represents

class CstObjectGlob(V, rand RAND_ATTR, int N, alias SYM)
  : CstObject!(V, RAND_ATTR, N), CstVarGlobIntf
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static if (is (LEAF == struct)) {
    this(string name, _esdl__Proxy parent, V* var) {
      super(name, parent, var);
    }
  }
  else {
    this(string name, _esdl__Proxy parent, V var) {
      super(name, parent, var);
    }
  }

  override void _esdl__fixRef() {
    static if (is (V == struct)) {
      _esdl__setValRef(& SYM);
    }
    else
      _esdl__setValRef(SYM);
  }
  
  // no unrolling is possible without adding rand proxy
  override typeof(this) _esdl__unroll(CstIterator iter, ulong n) {
    return this;
  }
}

class CstObjectGlobEnum(V, rand RAND_ATTR, int N)
  : CstObject!(V, RAND_ATTR, N), CstVarGlobIntf
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static assert (_esdl__ISRAND == false);

  V _var;

  this(string name, _esdl__Proxy parent, V var) {
    _var = var;
    super(name, parent, & _var);
  }

  override void _esdl__fixRef() {
    _esdl__setValRef(& _var);
  }
  
  // no unrolling is possible without adding rand proxy
  override typeof(this) _esdl__unroll(CstIterator iter, ulong n) {
    return this;
  }
}

class CstObjectIdx(V, rand RAND_ATTR, int N, VT, int IDX,
		   P, int PIDX): CstObject!(V, RAND_ATTR, N)
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;

  static if (is (LEAF == struct)) {
    this(string name, _esdl__Proxy parent, V* var) {
      assert(parent !is null);
      super(name, parent, var);
    }
  }
  else {
    this(string name, _esdl__Proxy parent, V var) {
      assert(parent !is null);
      super(name, parent, var);
    }
  }    

  static if (is (P: _esdl__ARG)) {
    override RV _esdl__unroll(CstIterator iter, ulong n) {
      return this;
    }
  }
  else {
    override RV _esdl__unroll(CstIterator iter, ulong n) {
      if (_parent !is _root) {
	P uparent = cast(P)(_parent._esdl__unroll(iter, n));
	assert (uparent !is null);
	return uparent.tupleof[PIDX];
      }
      else {
	return this;
      }
    }
    override RV _esdl__getResolvedNode() {
      if (_parentsDepsAreResolved) return this;
      else {
	P uparent = cast(P)(_parent._esdl__getResolvedNode());
	assert (uparent !is null);
	return uparent.tupleof[PIDX];
      }
    }
  }
  override bool rand_mode() {
    static if (_esdl__PROXYT._esdl__HAS_RAND_INFO == false) return true;
    else {
      assert (_parent !is null);
      _esdl__PROXYT proxy = _esdl__staticCast!_esdl__PROXYT(_parent);
      assert (proxy._esdl__outer !is null);
      return proxy._esdl__outer.rand_mode!(IDX)();
    }
  }
}

abstract class _esdl__ProxyStub(T): CstObjectIntf, rand.disable, rand.barrier
{
  // import esdl.rand.meta: _esdl__ProxyResolve;

  enum _esdl__TypeHasRandBarrier=true;
  
  alias PROXYT = _esdl__ProxyResolve!T;

  _esdl__Proxy _proxy;
  _esdl__Proxy _parent;

  static if (is (T == struct)) {
    T* _outer;
    T* _esdl__getRef()() {return _outer;}
    void _esdl__setValRef()(T* outer) {
      _outer = outer;
      this._esdl__get()._esdl__setValRef(outer);
    }
    this(_esdl__Proxy parent, void* outer) {
      _parent = parent;
      _outer = cast(T*) outer;
    }
  }
  else {
    T _outer;
    T _esdl__getRef()() {return _outer;}
    void _esdl__setValRef()(T outer) {
      _outer = outer;
      this._esdl__get()._esdl__setValRef(outer);
    }
    this(_esdl__Proxy parent, T outer) {
      _parent = parent;
      _outer = outer;
    }
  }
  
  PROXYT _esdl__get()() {
    if (_proxy is null) {
      assert(_parent !is null);
      _proxy = new PROXYT(_parent, this, _outer);
    }
    return _esdl__staticCast!PROXYT(_proxy);
  }

  _esdl__Proxy _esdl__getProxy() {
    return _esdl__get();
  }

  auto opDispatch(string WHAT)() {
    return __traits(getMember, _esdl__get(), WHAT);
  }

  void _esdl__doConstrain(_esdl__Proxy proxy, bool callPreRandomize) {
    this._esdl__get()._esdl__doConstrain(proxy, callPreRandomize);
  }
  
  void _esdl__doRandomize(_esdl__RandGen randGen) {
    this._esdl__get()._esdl__doRandomize(randGen);
  }

  final CstIterator _esdl__iter() {
    return null;
  }

  abstract typeof(this) _esdl__unroll(CstIterator iter, ulong n);
}

abstract class CstObjectBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) == 0):
    _esdl__ProxyStub!(LeafElementType!V), rand.disable, rand.barrier
      {
	enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
	alias LEAF = LeafElementType!V;
	alias RAND = RAND_ATTR;

	static if (is (LEAF == struct)) {
	  this(string name, _esdl__Proxy parent, LEAF* var) {
	    _esdl__name = name;
	    super(parent, var);
	  }
	}
	else {
	  this(string name, _esdl__Proxy parent, LEAF var) {
	    _esdl__name = name;
	    super(parent, var);
	  }
	}

	string _esdl__name;
	_esdl__Proxy _root;
	_esdl__CstProcessor _proc;

	override string _esdl__getName() {
	  return _esdl__name;
	}

	S to(S)() if (is (S == string)) {
	  static if (HAS_RAND_ATTRIB) {
	    if (_esdl__isRand) {
	      return "RAND#" ~ _esdl__name;
	    }
	    else {
	      return "VAL#" ~ _esdl__name;
	    }
	  }
	  else {
	    return "VAR#" ~ _esdl__name;
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

class CstObject(V, rand RAND_ATTR, int N) if (N == 0):
  CstObjectBase!(V, RAND_ATTR, N)
    {
      alias RV = typeof(this);

      _esdl__Proxy _parent;
      bool _parentsDepsAreResolved;
      
      // Call super only after the _parent has been set
      static if (is (LEAF == struct)) {
	this(string name, _esdl__Proxy parent, V* var) {
	  _parent = parent;
	  _root = _parent._esdl__getRootProxy();
	  _proc = _root._esdl__getProcessor();
	  _parentsDepsAreResolved = _parent._esdl__depsAreResolved();
	  super(name, parent, var);
	}
      }
      else {
	this(string name, _esdl__Proxy parent, V var) {
	  _parent = parent;
	  _root = _parent._esdl__getRootProxy();
	  _proc = _root._esdl__getProcessor();
	  _parentsDepsAreResolved = _parent._esdl__depsAreResolved();
	  super(name, parent, var);
	}
      }

      final override bool _esdl__isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
      }

      final override bool _esdl__isDomainInRange() { return _parent._esdl__isDomainInRange(); }

      final override string _esdl__getFullName() {
	if (_parent is _root) return _esdl__name;
	else  
	  return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      _esdl__Proxy _esdl__getRootProxy()() {
	assert (_root !is null);
	return _root;
      }

      _esdl__CstProcessor _esdl__getProcessor()() {
	assert (_proc !is null);
	return _proc;
      }

      final bool _esdl__isStatic() {
	return _parent._esdl__isStatic();
      }

      final bool _esdl__isReal() {
	return _parent._esdl__isReal();
      }

      final bool _esdl__isRolled() {
	return _parent._esdl__isRolled();		// N == 0
      }

      override bool _esdl__depsAreResolved() { // this level is resolved
	return _parentsDepsAreResolved;
      }

      override RV _esdl__getResolvedNode() {
	return this;
      }

      // RV
      override typeof(this) _esdl__unroll(CstIterator iter, ulong n) {
	return this;
      }

      static if (is (LEAF == struct)) {
	LEAF* getRef() {
	  return _esdl__getRef();
	}
      }
      else {
	LEAF getRef() {	// 
	  return _esdl__getRef();
	}
      }

      override void _esdl__scan() {
	// import std.stdio;
	// writeln("Visiting: ", this._esdl__getFullName());
	assert (false);
	// assert (this.getRef() !is null);
	// _esdl__setValRef(this.getRef());
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

      bool _parentsDepsAreResolved;

      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;
      immutable bool _nodeIsMapped = false;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      // Call super only after the _parent has been set
      this(string name, P parent, CstVecTerm indexExpr, bool isMapped) {
	// if (indexExpr.isConst()) {
	//   ulong index = indexExpr.evaluate();
	//   this(name, parent, index);
	// }
	// else {
	assert (parent !is null);
	_nodeIsMapped = isMapped;
	_esdl__name = name ~ (isMapped ? "[#" : "[%") ~ indexExpr.describe() ~ "]";
	super(_esdl__name, parent._esdl__getRootProxy(), null);
	_parent = parent;
	_root = _parent._esdl__getRootProxy();
	_proc = _root._esdl__getProcessor();
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
	_indexExpr = indexExpr;
	// }
      }

      // Call super only after the _parent has been set
      this(string name, P parent, ulong index, bool isMapped) {
	import std.conv: to;
	assert (parent !is null);
	_nodeIsMapped = isMapped;
	_esdl__name = name ~ (isMapped ? "[#" : "[%") ~ index.to!string() ~ "]";
	super(_esdl__name, parent._esdl__getRootProxy(), null);
	_parent = parent;
	_pindex = index;
	_root = _parent._esdl__getRootProxy();
	_proc = _root._esdl__getProcessor();
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
      }

      final override bool _esdl__isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
      }

      final override bool _esdl__isDomainInRange() {
	if (_indexExpr !is null) assert (false, "Unresolved Index");
	else return _parent._esdl__isDomainInRange() && _parent.inRangeIndex(_pindex);
      }

      override bool opEquals(Object other) {
	auto rhs = cast (RV) other;
	if (rhs is null) return false;
	else return (_parent == rhs._parent && _indexExpr == _indexExpr);
      }
      
      final bool _esdl__isStatic() {
	return ((_indexExpr is null ||
		 _indexExpr.isIterator ||
		 _indexExpr.isConst) &&
		_parent._esdl__isStatic());
      }

      final bool _esdl__isReal() {
	return (_indexExpr is null &&
		_parent._esdl__isReal());
      }

      final bool _esdl__isRolled() {
	return ((_indexExpr !is null &&
		 _indexExpr.isIterator) ||
		_parent._esdl__isRolled());
      }

      final override string _esdl__getFullName() {
	return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      _esdl__Proxy _esdl__getRootProxy()() {
	assert (_root !is null);
	return _root;
      }

      _esdl__CstProcessor _esdl__getProcessor()() {
	assert (_proc !is null);
	return _proc;
      }

      override bool _esdl__depsAreResolved() {
	return _parentsDepsAreResolved && _nodeIsMapped;
      }

      override RV _esdl__getResolvedNode() {
	if (_resolvedCycle != _esdl__getProcessor()._cycle) {
	  auto parent = _parent._esdl__getResolvedNode();
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
	  _resolvedCycle = _esdl__getProcessor()._cycle;
	}
	return _resolvedObj;
      }

      // RV
      override RV _esdl__unroll(CstIterator iter, ulong n) {
	if (_indexExpr) {
	  return _parent._esdl__unroll(iter,n)[_indexExpr._esdl__unroll(iter,n)];
	}
	else {
	  return _parent._esdl__unroll(iter,n)[_pindex];
	}
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
      }

      override void _esdl__scan() {
	// import std.stdio;
	// writeln("Visiting: ", this._esdl__getFullName());
	assert (this.getRef() !is null);
	_esdl__setValRef(this.getRef());
	if (this._esdl__isRand()) {
	  _esdl__doConstrain(_esdl__getRootProxy(), true);
	}
      }

      void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	if (_parent._esdl__isStatic()) {
	  import std.algorithm.searching: canFind;
	  auto len = _parent._arrLen;
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

  this(string name, _esdl__Proxy parent, V* var) {
    super(name, parent, var);
  }

  override void _esdl__fixRef() {
    _esdl__setValRef (& SYM);
  }
  
  // no unrolling is possible without adding rand proxy
  override RV _esdl__unroll(CstIterator iter, ulong n) {
    return this;
  }
}

class CstObjArrGlobEnum(V, rand RAND_ATTR, int N)
  : CstObjArr!(V, RAND_ATTR, N), CstVarGlobIntf
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static assert (_esdl__ISRAND == false);

  V _var;
  
  this(string name, _esdl__Proxy parent, V var) {
    _var = var;
    super(name, parent, & _var);
  }

  override void _esdl__fixRef() {
    _esdl__setValRef (& _var);
  }
  
  // no unrolling is possible without adding rand proxy
  override RV _esdl__unroll(CstIterator iter, ulong n) {
    return this;
  }
}


// Arrays (Multidimensional arrays as well)
class CstObjArrIdx(V, rand RAND_ATTR, int N, VT, int IDX,
		   P, int PIDX): CstObjArr!(V, RAND_ATTR, N)
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  this(string name, _esdl__Proxy parent, V* var) {
    super(name, parent, var);
  }
  static if (is (P: _esdl__ARG)) {
    override RV _esdl__unroll(CstIterator iter, ulong n) {
      return this;
    }
  }
  else {
    override RV _esdl__unroll(CstIterator iter, ulong n) {
      if (_parent !is _esdl__getRootProxy()) {
	P uparent = cast(P)(_parent._esdl__unroll(iter, n));
	assert (uparent !is null);
	return uparent.tupleof[PIDX];
      }
      else {
	return this;
      }
    }
    override RV _esdl__getResolvedNode() {
      if (_parentsDepsAreResolved) return this;
      else {
	P uparent = cast(P)(_parent._esdl__getResolvedNode());
	assert (uparent !is null);
	return uparent.tupleof[PIDX];
      }
    }
  }
  override bool rand_mode() {
    static if (_esdl__PROXYT._esdl__HAS_RAND_INFO == false) return true;
    else {
      assert (_parent !is null);
      _esdl__PROXYT proxy = _esdl__staticCast!_esdl__PROXYT(_parent);
      assert (proxy._esdl__outer !is null);
      return proxy._esdl__outer.rand_mode!(IDX)();
    }
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

  this(string name, _esdl__Proxy root) {
    super(name, root);
  }
    
  CstArrLength!RV _arrLen;
  CstArrHierLength!RV _arrHierLen;

  EV[] _elems;
  EV   _negIndexElem;

  abstract EV createElem(CstVecTerm indexExpr, bool isMapped);
  abstract EV createElem(uint i, bool isMapped);
    
  bool rand_mode() { return true; }
  // overridded in derived classes
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

  void markArrLen(size_t length) {
    buildElements(length);
    // import std.stdio;
    // writeln("buildElements: ", length);
    static if (is (EV: CstObjectIntf)) {
      _esdl__domsetUnresolvedArrLen = 0;
      _esdl__domsetLeafElemsCount = cast(uint) length;
      markHierResolved();
    }
    else {
      _esdl__domsetUnresolvedArrLen = cast(uint) length;
      _esdl__domsetLeafElemsCount = 0;
    }
  }

  EV _esdl__elems() {
    return this[_esdl__iter()];
  }

  
  final bool _esdl__isObjArray() {return true;}

  final CstIterator _esdl__iter() {
    CstArrIterator!RV iter = arrLen.makeIterVar();
    return iter;
  }

  final CstVarNodeIntf _esdl__getChild(ulong n) {
    return this[n];
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

  final void _esdl__scan() {
    // import std.stdio;
    // writeln("Visiting: ", this._esdl__getFullName());
  }

}

class CstObjArr(V, rand RAND_ATTR, int N) if (N == 0):
  CstObjArrBase!(V, RAND_ATTR, N)
    {
      V* _var;
      _esdl__Proxy _parent;
      bool _parentsDepsAreResolved;
    
      void _esdl__setValRef(V* var) {
	_var = var;
      }
      
      // Call super only after the _parent has been set
      this(string name, _esdl__Proxy parent, V* var) {
	super(name, parent._esdl__getRootProxy());
	_var = var;
	_parent = parent;
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
	_arrLen = new CstArrLength!RV(name ~ "->length", this);
	_arrHierLen = new CstArrHierLength!RV (name ~ "->hierLength", this);
      }

      final override bool _esdl__isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
      }

      final override bool _esdl__isDomainInRange() {
	return _parent._esdl__isDomainInRange();
      }

      final bool _esdl__isRolled() {
	return _parent._esdl__isRolled();
      }

      final bool _esdl__isStatic() {
	return _parent._esdl__isStatic();
      }

      final bool _esdl__isReal() {
	return _parent._esdl__isReal();
      }

      final string _esdl__getFullName() {
	if (_parent is _esdl__getRootProxy()) return _esdl__name;
	else  
	  return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      override bool _esdl__depsAreResolved() {
	return _parentsDepsAreResolved;
      }

      override RV _esdl__getResolvedNode() {
	return this;
      }

      RV _esdl__unroll(CstIterator iter, ulong n) {
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
	  auto keys = (*_var).keys;
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
	  foreach (i, key; (*_var).keys) {
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
	return new EV(_esdl__name, this, indexExpr, isMapped);
      }
  
      override EV createElem(uint i, bool isMapped) {
	return new EV(_esdl__name, this, cast(uint) i, isMapped);
      }
  
      override void markHierResolved() {
	_arrHierLen.setVal(_esdl__domsetLeafElemsCount);
	// top level array -- no need to do anything
	// import std.stdio;
	// stdout.writeln("Array elements count: ", _esdl__domsetLeafElemsCount);
	// foreach (elem; this[]) {
	//   stdout.writeln(elem._esdl__getName());
	// }
      }

      void markChildResolved(uint n) {
	assert (_esdl__domsetUnresolvedArrLen != 0 &&
		_esdl__domsetUnresolvedArrLen != uint.max);
	_esdl__domsetUnresolvedArrLen -= 1;
	_esdl__domsetLeafElemsCount += n;
	if (_esdl__domsetUnresolvedArrLen == 0) {
	  markHierResolved();
	}
      }
    }

class CstObjArr(V, rand RAND_ATTR, int N) if (N != 0):
  CstObjArrBase!(V, RAND_ATTR, N), CstObjIndexed
    {
      alias P = CstObjArr!(V, RAND_ATTR, N-1);
      P _parent;

      bool _parentsDepsAreResolved;
      
      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;
      immutable bool _nodeIsMapped = false;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      // Call super only after the _parent has been set
      this(string name, P parent, CstVecTerm indexExpr, bool isMapped) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	string iname = name ~ (isMapped ? "[#" : "[%") ~ indexExpr.describe() ~ "]";
	super(iname, parent._esdl__getRootProxy());
	_nodeIsMapped = isMapped;
	_parent = parent;
	_indexExpr = indexExpr;
	// _root = _parent._esdl__getRootProxy();
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
	_arrLen = new CstArrLength!RV(iname ~ "->length", this);
	_arrHierLen = new CstArrHierLength!RV (name ~ "->hierLength", this);
      }

      // Call super only after the _parent has been set
      this(string name, P parent, ulong index, bool isMapped) {
	import std.conv: to;
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	string iname = name ~ (isMapped ? "[#" : "[%") ~ index.to!string() ~ "]";
	super(iname, parent._esdl__getRootProxy());
	_nodeIsMapped = isMapped;
	_parent = parent;
	// _indexExpr = _esdl__cstVal(index);
	_pindex = index;
	// _root = _parent._esdl__getRootProxy();
	_parentsDepsAreResolved = _parent._esdl__depsAreResolved();
	_arrLen = new CstArrLength!RV(iname ~ "->length", this);
	_arrHierLen = new CstArrHierLength!RV (name ~ "->hierLength", this);
      }

      final override bool _esdl__isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent._esdl__isRand();
      }

      final override bool _esdl__isDomainInRange() {
	if (_indexExpr !is null) assert (false, "Unresolved Index");
	else return _parent._esdl__isDomainInRange() && _parent.inRangeIndex(_pindex);
      }

      override bool opEquals(Object other) {
	auto rhs = cast (RV) other;
	if (rhs is null) return false;
	else return (_parent == rhs._parent && _indexExpr == _indexExpr);
      }
      
      final bool _esdl__isRolled() {
	return (_indexExpr !is null &&
		_indexExpr.isIterator) ||
	  _parent._esdl__isRolled();
      }

      final bool _esdl__isStatic() {
	return ((_indexExpr is null  ||
		 _indexExpr.isIterator ||
		 _indexExpr.isConst) &&
		_parent._esdl__isStatic());
      }

      final bool _esdl__isReal() {
	return (_indexExpr is null &&
		_parent._esdl__isReal());
      }

      final string _esdl__getFullName() {
	return _parent._esdl__getFullName() ~ "." ~ _esdl__getName();
      }
      
      override bool _esdl__depsAreResolved() {
	return _parentsDepsAreResolved && _nodeIsMapped;
      }

      override RV _esdl__getResolvedNode() {
	if (_resolvedCycle != _esdl__getCstProcessor()._cycle) {
	  auto parent = _parent._esdl__getResolvedNode();
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
	  _resolvedCycle = _esdl__getCstProcessor()._cycle;
	}
	return _resolvedObj;
      }

      RV _esdl__unroll(CstIterator iter, ulong n) {
	if (_indexExpr) {
	  return _parent._esdl__unroll(iter,n)[_indexExpr._esdl__unroll(iter,n)];
	}
	else {
	  return _parent._esdl__unroll(iter,n)[_pindex];
	}
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
	if (_parent._esdl__isStatic()) {
	  import std.algorithm.searching: canFind;
	  auto len = _parent._arrLen;
	  if (! pred._unrolledIters[].canFind(len.iterVar()))
	    pred.addDep(len, context);
	}

	_parent.setDomainContext(pred, context);
	if (_indexExpr !is null) {
	  _indexExpr.setDomainContext(pred, DomainContextEnum.INDEX);
	}
      }

      override ulong mapIter(size_t iter) {
	static if (isAssociativeArray!L) {
	  static assert (false, "Associative Arrays are supported only at top array hierarchy");
	}
	else return iter;
      }
      
      override size_t mapIndex(ulong index) {
	static if (isAssociativeArray!L) {
	  static assert (false, "Associative Arrays are supported only at top array hierarchy");
	}
	else return cast(size_t) index;
      }

      override EV createElem(CstVecTerm indexExpr, bool isMapped) {
	return new EV(_esdl__name, this, indexExpr, isMapped);
      }
  
      override EV createElem(uint i, bool isMapped) {
	return new EV(_esdl__name, this, cast(uint) i, isMapped);
      }
  
      override void markHierResolved() {
	_arrHierLen.setVal(_esdl__domsetLeafElemsCount);
	if (_indexExpr is null) {
	  _parent.markChildResolved(_esdl__domsetLeafElemsCount);
	}
      }

      void markChildResolved(uint n) {
	assert (_esdl__domsetUnresolvedArrLen != 0 &&
		_esdl__domsetUnresolvedArrLen != uint.max);
	_esdl__domsetUnresolvedArrLen -= 1;
	_esdl__domsetLeafElemsCount += n;
	if (_esdl__domsetUnresolvedArrLen == 0) {
	  markHierResolved();
	}
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
  if (is (RV: CstObjSet) && isIntegral!(J[0])) {
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
      return getArrElemTmpl(*(rv._var), indx);
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
    return getArrLenTmpl(*(rv._var), indx);
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
    setArrLen(*(rv._var), v, indx);
	  
  }
}
