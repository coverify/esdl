module esdl.rand.objx;

import esdl.data.bvec;
import esdl.data.bstr;
import esdl.data.queue;
import std.traits: isIntegral, isBoolean, isArray, KeyType,
  isStaticArray, isDynamicArray, isAssociativeArray;

import esdl.rand.misc;
import esdl.rand.base: CstValue, CstVecTerm, CstIterator, DomType,
  CstDomBase, CstDomSet, CstObjectStubBase, CstObjArrStubBase, CstObjSet,
  CstVarNodeIntf, CstVecNodeIntf, CstObjArrIntf, CstVarGlobIntf,
  CstObjectVoid, CstObjArrVoid, CstDepIntf;
import esdl.rand.pred: CstPredicate;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.expr: CstRangeExpr;
import esdl.rand.domain: CstArrIterator, CstArrLength;

import esdl.rand.meta: _esdl__ProxyResolve, _esdl__staticCast;

import std.algorithm.searching: canFind;

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
  override _esdl__Proxy unroll(CstIterator iter, ulong n) {
    return this;
  }
}

class CstObjectStub(V, rand RAND_ATTR, int N, int IDX,
		    P, int PIDX): CstObjectStubBase
{
  enum int _esdl__INDEX = IDX;
  alias _esdl__PROXYT = P;
  
  CstObjectVoid _obj;
  
  string _name;
  _esdl__Proxy _parent;
  
  static if (is (V == struct)) {
    V* _var;
    this(string name, _esdl__Proxy parent, V* var) {
      assert(parent !is null);
      _name = name;
      _parent = parent;
      _var = var;
    }
  }
  else {
    V _var;
    this(string name, _esdl__Proxy parent, V var) {
      assert(parent !is null);
      _name = name;
      _parent = parent;
      _var = var;
    }
  }

  CstObjectVoid _esdl__obj() {
    return _obj;
  }

  auto _esdl__get()() {
    alias TYPE = CstObjectIdx!(V, RAND_ATTR, N, IDX, P, PIDX);
    if (_obj is null) {
      assert(_parent !is null);
      _obj = new TYPE(_name, _parent, _var);
    }
    return _esdl__staticCast!TYPE(_obj);
  }

  auto opDispatch(string WHAT)() {
    auto obj = this._esdl__get();
    return __traits(getMember, obj, WHAT);
  }
}

class CstObjectIdx(V, rand RAND_ATTR, int N, int IDX,
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

  static if (PIDX >= 0) {	// exclude randomize_with
    override _esdl__Proxy unroll(CstIterator iter, ulong n) {
      if (_parent !is _root) {
	P uparent = cast(P)(_parent.unroll(iter, n));
	assert (uparent !is null);
	static if (is (typeof(uparent.tupleof[PIDX]): CstObjectStubBase)) {
	  return uparent.tupleof[PIDX]._esdl__get();
	}
	else {
	  return uparent.tupleof[PIDX];
	}
      }
      else {
	return this;
      }
    }
  }
}

class CstObjectBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) == 0):
    _esdl__ProxyResolve!(LeafElementType!V)
      {
	enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
	alias LEAF = LeafElementType!V;

	static if (is (LEAF == struct)) {
	  this(string name, _esdl__Proxy parent, LEAF* var) {
	    _name = name;
	    super(parent, var);
	  }
	}
	else {
	  this(string name, _esdl__Proxy parent, LEAF var) {
	    _name = name;
	    super(parent, var);
	  }
	}

	string _name;

	override string name() {
	  return _name;
	}

	S to(S)() if (is (S == string)) {
	  static if (HAS_RAND_ATTRIB) {
	    if (isRand) {
	      return "RAND#" ~ _name;
	    }
	    else {
	      return "VAL#" ~ _name;
	    }
	  }
	  else {
	    return "VAR#" ~ _name;
	  }
	}

	override string toString() {
	  return this.to!string();
	}

	bool _isRand = true;
	void rand_mode(bool mode) {
	  if (mode != _isRand) {
	    _isRand = mode;
	    _root.setNeedSync();
	  }
	}
	bool rand_mode() { return _isRand; }
	// overridded in derived classes
	override bool isRand() { assert (false); }
      }

class CstObject(V, rand RAND_ATTR, int N) if (N == 0):
  CstObjectBase!(V, RAND_ATTR, N)
    {
      alias RV = typeof(this);

      _esdl__Proxy _root;
      _esdl__Proxy _parent;
      
      // Call super only after the _parent has been set
      static if (is (LEAF == struct)) {
	this(string name, _esdl__Proxy parent, V* var) {
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	  super(name, parent, var);
	}
      }
      else {
	this(string name, _esdl__Proxy parent, V var) {
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	  super(name, parent, var);
	}
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && _isRand && _parent.isRand();
      }

      final override string fullName() {
	if (_parent is _root) return _name;
	else  
	  return _parent.fullName() ~ "." ~ name();
      }
      
      _esdl__Proxy getProxyRoot()() {
	assert (_root !is null);
	return _root;
      }

      final override bool isStatic() {
	return _parent.isStatic();
      }

      final override bool isRolled() {
	return _parent.isRolled();		// N == 0
      }

      // RV
      override _esdl__Proxy unroll(CstIterator iter, ulong n) {
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

      override void scan() {
	// import std.stdio;
	// writeln("Visiting: ", this.fullName());
	assert (false);
	// assert (this.getRef() !is null);
	// _esdl__setValRef(this.getRef());
	// _esdl__doConstrain(getProxyRoot());
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomBase[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomBase[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstDepIntf[] idxs,
			    ref CstDomBase[] bitIdxs,
			    ref CstDepIntf[] deps) {
	// no parent
      }

    }

// Array Element
class CstObject(V, rand RAND_ATTR, int N) if (N != 0):
  // _esdl__ProxyResolve!(LeafElementType!V)
  CstObjectBase!(V, RAND_ATTR, N), CstObjIndexed
    {
      alias RV = typeof(this);
      alias P = CstObjArr!(V, RAND_ATTR, N-1);
      P _parent;

      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      _esdl__Proxy _root;

      // Call super only after the _parent has been set
      this(string name, P parent, CstVecTerm indexExpr) {
	if (indexExpr.isConst()) {
	  ulong index = indexExpr.evaluate();
	  this(name, parent, index);
	}
	else {
	  assert (parent !is null);
	  _name = name;
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	  _indexExpr = indexExpr;
	  super(name, parent.getProxyRoot(), null);
	}
      }

      // Call super only after the _parent has been set
      this(string name, P parent, ulong index) {
	assert (parent !is null);
	_name = name;
	_parent = parent;
	_pindex = index;
	_root = _parent.getProxyRoot();
	super(name, parent.getProxyRoot(), null);
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && _isRand && _parent.isRand();
      }

      override bool opEquals(Object other) {
	auto rhs = cast (RV) other;
	if (rhs is null) return false;
	else return (_parent == rhs._parent && _indexExpr == _indexExpr);
      }
      
      final override bool isStatic() {
	return ((_indexExpr is null ||
		 _indexExpr.isIterator ||
		 _indexExpr.isConst) &&
		_parent.isStatic());
      }

      final override bool isRolled() {
	return ((_indexExpr !is null &&
		 _indexExpr.isIterator) ||
		_parent.isRolled());
      }

      final override string fullName() {
	return _parent.fullName() ~ "." ~ name();
      }
      
      _esdl__Proxy getProxyRoot()() {
	assert (_root !is null);
	return _root;
      }

      RV getResolved() {
	if (_resolvedCycle != getProxyRoot()._cycle) {
	  auto parent = _parent.getResolved();
	  if (_indexExpr) {
	    _resolvedObj = parent[cast(size_t) _indexExpr.evaluate()];
	  }
	  else {
	    _resolvedObj = parent[_pindex];
	  }
	  _resolvedCycle = getProxyRoot()._cycle;
	}
	return _resolvedObj;
      }

      // RV
      override _esdl__Proxy unroll(CstIterator iter, ulong n) {
	if (_indexExpr) {
	  return _parent.unroll(iter,n)[_indexExpr.unroll(iter,n)];
	}
	else {
	  return _parent.unroll(iter,n)[_pindex];
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

      override void scan() {
	// import std.stdio;
	// writeln("Visiting: ", this.fullName());
	assert (this.getRef() !is null);
	_esdl__setValRef(this.getRef());
	if (this.isRand())
	  _esdl__doConstrain(getProxyRoot());
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomBase[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomBase[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstDepIntf[] idxs,
			    ref CstDomBase[] bitIdxs,
			    ref CstDepIntf[] deps) {
	static if (RAND_ATTR.isRand()) {
	  // 	if (! canFind(rnds, this)) rnds ~= this;
	  // }
	  // else {
	  // 	if (! canFind(vars, this)) vars ~= this;
	}
	if (_parent.isStatic()) {
	  deps ~= _parent._arrLen;
	}
	_parent.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);

	if (_indexExpr !is null) {
	  // Here we need to put the parent as a dep for the pred
	  // and since this prim needs resolution, the constituents of
	  // the indexExpr need to trigger a function that finds out
	  // whether the _indexExpr has been fully resolved or
	  // not. When the indexExpr gets resolved, it should inform
	  // the parent about resolution which in turn should inform
	  // the pred that it can go ahead
	  CstDomBase[] indexes;
	  _indexExpr.setDomainContext(pred, indexes, rndArrs, indexes, varArrs, vals, iters, idxs, bitIdxs, deps);
	  foreach (index; indexes) idxs ~= index;
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
  override RV unroll(CstIterator iter, ulong n) {
    return this;
  }
}


class CstObjArrStub(V, rand RAND_ATTR, int N, int IDX,
		    P, int PIDX): CstObjArrStubBase
{
  enum int _esdl__INDEX = IDX;
  alias _esdl__PROXYT = P;
  
  CstObjArrVoid _obj;

  string _name;
  _esdl__Proxy _parent;
  V* _var;

  this(string name, _esdl__Proxy parent, V* var) {
    _name = name;
    _parent = parent;
    _var = var;
  }

  CstObjArrVoid _esdl__obj() {
    return _obj;
  }

  auto _esdl__get()() {
    alias TYPE = CstObjArrIdx!(V, RAND_ATTR, N, IDX, P, PIDX);
    if (_obj is null) {
      assert(_parent !is null);
      _obj = new TYPE(_name, _parent, _var);
    }
    return _esdl__staticCast!TYPE(_obj);
  }

  auto opDispatch(string WHAT)() {
    auto obj = this._esdl__get();
    return __traits(getMember, obj, WHAT);
  }
}

// Arrays (Multidimensional arrays as well)
class CstObjArrIdx(V, rand RAND_ATTR, int N, int IDX,
		   P, int PIDX): CstObjArr!(V, RAND_ATTR, N)
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  this(string name, _esdl__Proxy parent, V* var) {
    super(name, parent, var);
  }
  override RV unroll(CstIterator iter, ulong n) {
    if (_parent !is _root) {
      P uparent = cast(P)(_parent.unroll(iter, n));
      assert (uparent !is null);
      static if (is (typeof(uparent.tupleof[PIDX]): CstObjArrStubBase)) {
	return uparent.tupleof[PIDX]._esdl__get();
      }
      else {
	return uparent.tupleof[PIDX];
      }
    }
    else {
      return this;
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

  this(string name) {
    super(name);
  }
    
  CstArrLength!RV _arrLen;

  EV[] _elems;

  abstract EV createElem(CstVecTerm indexExpr);
  abstract EV createElem(uint i);
    
  bool _isRand = true;
  void rand_mode(bool mode) {
    if (mode != _isRand) {
      _isRand = mode;
      _root.setNeedSync();
    }
  }
  bool rand_mode() { return _isRand; }
  // overridded in derived classes
  bool isRand() { assert (false); }

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
	_elems[i] = createElem(i);
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
      return createElem(indexExpr);
    }
  }

  EV opIndex(CstRangeExpr index) {
    assert (index._rhs is null);
    return this.opIndex(index._lhs);
  }

  EV opIndex(ulong index) {
    size_t key = mapIndex(index);
    if (_arrLen.isSolved()) {
      auto len = _arrLen.evaluate();
      if (len <= key) {
	assert (false, "Index Out of Range");
      }
      buildElements(len);
    }
    else {
      buildElements(key+1);
    }
    return _elems[key];
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

  void markArrLen(size_t length) {
    buildElements(length);
    // import std.stdio;
    // writeln("buildElements: ", length);
    static if (is (EV: _esdl__Proxy)) {
      _esdl__unresolvedArrLen = 0;
      _esdl__leafElemsCount = cast(uint) length;
      markSolved();
    }
    else {
      _esdl__unresolvedArrLen = cast(uint) length;
      _esdl__leafElemsCount = 0;
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


  final _esdl__Proxy _esdl__nthLeaf(uint idx) {
    static if (is (EV: _esdl__Proxy)) {
      return _elems[idx];
    }
    else {
      uint iter;
      for (iter = 0; iter != _elems.length; ++iter) {
	assert (_elems[iter] !is null);
	if (idx >= _elems[iter]._esdl__leafElemsCount) {
	  idx -= _elems[iter]._esdl__leafElemsCount;
	}
	else {
	  break;
	}
      }
      return _elems[iter]._esdl__nthLeaf(idx);
    }
  }    

  final void scan() {
    // import std.stdio;
    // writeln("Visiting: ", this.fullName());
  }

}

class CstObjArr(V, rand RAND_ATTR, int N) if (N == 0):
  CstObjArrBase!(V, RAND_ATTR, N)
    {
      alias RAND=RAND_ATTR;

      V* _var;
      _esdl__Proxy _parent;
    
      void _esdl__setValRef(V* var) {
	_var = var;
      }
      
      // Call super only after the _parent has been set
      this(string name, _esdl__Proxy parent, V* var) {
	_var = var;
	_parent = parent;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!RV(name ~ "->length", this);
	super(name);
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && _isRand && _parent.isRand();
      }

      final bool isRolled() {
	return _parent.isRolled();
      }

      final bool isStatic() {
	return _parent.isStatic();
      }

      final string fullName() {
	if (_parent is _root) return _name;
	else  
	  return _parent.fullName() ~ "." ~ name();
      }
      
      RV getResolved() {
	return this;
      }

      RV unroll(CstIterator iter, ulong n) {
	return this;
      }

      override void setLen(size_t len) {
	setLenTmpl(this, len);
      }
      
      override size_t getLen() {
	return getLenTmpl(this);
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomBase[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomBase[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstDepIntf[] idxs,
			    ref CstDomBase[] bitIdxs,
			    ref CstDepIntf[] deps) {
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

      override EV createElem(CstVecTerm indexExpr) {
	return new EV(name ~ "[" ~ indexExpr.describe() ~ "]", this, indexExpr);
      }
  
      override EV createElem(uint i) {
	import std.conv: to;
	return new EV(_name ~ "[#" ~ i.to!string() ~ "]",
		      this, cast(uint) i);
      }
  
      override void markSolved() {
	// top level array -- no need to do anything
	// import std.stdio;
	// stderr.writeln("Array elements count: ", _esdl__leafElemsCount);
	// foreach (elem; this[]) {
	//   stderr.writeln(elem.name());
	// }
      }

      void markChildSolved(uint n) {
	assert (_esdl__unresolvedArrLen != 0 &&
		_esdl__unresolvedArrLen != uint.max);
	_esdl__unresolvedArrLen -= 1;
	_esdl__leafElemsCount += n;
	if (_esdl__unresolvedArrLen == 0) {
	  markSolved();
	}
      }
    }

class CstObjArr(V, rand RAND_ATTR, int N) if (N != 0):
  CstObjArrBase!(V, RAND_ATTR, N), CstObjIndexed
    {
      alias P = CstObjArr!(V, RAND_ATTR, N-1);
      P _parent;
      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;

      alias RAND=RAND_ATTR;
      
      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      // Call super only after the _parent has been set
      this(string name, P parent, CstVecTerm indexExpr) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	_parent = parent;
	_indexExpr = indexExpr;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!RV(name ~ "->length", this);
	super(name);
      }

      // Call super only after the _parent has been set
      this(string name, P parent, ulong index) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	_parent = parent;
	// _indexExpr = _esdl__cstVal(index);
	_pindex = index;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!RV(name ~ "->length", this);
	super(name);
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && _isRand && _parent.isRand();
      }

      override bool opEquals(Object other) {
	auto rhs = cast (RV) other;
	if (rhs is null) return false;
	else return (_parent == rhs._parent && _indexExpr == _indexExpr);
      }
      
      final bool isRolled() {
	return (_indexExpr !is null &&
		_indexExpr.isIterator) ||
	  _parent.isRolled();
      }

      final bool isStatic() {
	return ((_indexExpr is null  ||
		 _indexExpr.isIterator ||
		 _indexExpr.isConst) &&
		_parent.isStatic());
      }

      final string fullName() {
	return _parent.fullName() ~ "." ~ name();
      }
      
      RV getResolved() {
	if (_resolvedCycle != getProxyRoot()._cycle) {
	  auto parent = _parent.getResolved();
	  if (_indexExpr) {
		_resolvedObj = parent[_indexExpr.evaluate()];
	  }
	  else {
		_resolvedObj = parent[_pindex];
	  }
	  _resolvedCycle = getProxyRoot()._cycle;
	}
	return _resolvedObj;
      }

      RV unroll(CstIterator iter, ulong n) {
	if (_indexExpr) {
	  return _parent.unroll(iter,n)[_indexExpr.unroll(iter,n)];
	}
	else {
	  return _parent.unroll(iter,n)[_pindex];
	}
      }

      override void setLen(size_t len) {
	setLenTmpl(this, len);
      }
      

      override size_t getLen() {
	return getLenTmpl(this);
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomBase[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomBase[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstDepIntf[] idxs,
			    ref CstDomBase[] bitIdxs,
			    ref CstDepIntf[] deps) {
	// arrlen should not be handled here. It is handled as part
	// of the indexExpr in the elements when required (that is
	// when indexExpr is not contant, but an expression)
	  
	// auto iter = arrLen.makeIterVar();
	// iters ~= iter;
	if (_parent.isStatic()) {
	  deps ~= _parent._arrLen;
	}
	_parent.setDomainContext(pred, rnds, rndArrs, vars, varArrs,
				 vals, iters, idxs, bitIdxs, deps);
	if (_indexExpr !is null) {
	  CstDomBase[] indexes;
	  _indexExpr.setDomainContext(pred, indexes, rndArrs, indexes, varArrs,
				      vals, iters, idxs, bitIdxs, deps);
	  foreach (index; indexes) idxs ~= index;
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

      override EV createElem(CstVecTerm indexExpr) {
	return new EV(name ~ "[" ~ indexExpr.describe() ~ "]", this, indexExpr);
      }
  
      override EV createElem(uint i) {
	import std.conv: to;
	return new EV(_name ~ "[#" ~ i.to!string() ~ "]",
		      this, cast(uint) i);
      }
  
      override void markSolved() {
	if (_indexExpr is null) {
	  _parent.markChildSolved(_esdl__leafElemsCount);
	}
      }

      void markChildSolved(uint n) {
	assert (_esdl__unresolvedArrLen != 0 &&
		_esdl__unresolvedArrLen != uint.max);
	_esdl__unresolvedArrLen -= 1;
	_esdl__leafElemsCount += n;
	if (_esdl__unresolvedArrLen == 0) {
	  markSolved();
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
