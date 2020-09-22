module esdl.rand.vecx;

import esdl.data.bvec;
import esdl.data.bstr;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray, isDynamicArray;

import esdl.solver.base: CstSolver;

import esdl.rand.misc;
import esdl.rand.intr;
import esdl.rand.base: CstVecPrim, CstVecExpr, CstIterator, DomType,
  CstDomain, CstPredicate, CstVecIntf, CstVectorIntf, CstVecArrIntf;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.expr: CstArrLength, CstVecDomain, _esdl__cstVal,
  CstVecTerm, CstArrIterator, CstValue, CstRangeExpr;

import esdl.rand.intr: IntRangeSet;
import esdl.rand.meta: _esdl__ProxyResolve, _esdl__staticCast;

import std.algorithm.searching: canFind;
import std.typetuple: staticIndexOf, TypeTuple;
import std.traits: BaseClassesTuple; // required for staticIndexOf

// T represents the type of the declared array/non-array member
// N represents the level of the array-elements we have to traverse
// for the elements this CstVector represents

class CstVecIdx(V, rand RAND_ATTR, int N, int IDX,
		P, int PIDX): CstVector!(V, RAND_ATTR, N)
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  this(string name, ref V var, _esdl__Proxy parent) {
    super(name, var, parent);
  }

  static if (PIDX >= 0) {	// exclude randomize_with
    override CstVecExpr unroll(CstIterator iter, uint n) {
      if (_parent !is _root) {
	P uparent = cast(P)(_parent.unroll(iter, n));
	assert (uparent !is null);
	return uparent.tupleof[PIDX];
      }
      else {
	return this;
      }
    }
  }

}

class CstVectorBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) == 0):
    CstVecDomain!(LeafElementType!V, RAND_ATTR), CstVecPrim
      {
	enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
	alias LEAF = LeafElementType!V;

	static if (HAS_RAND_ATTRIB) {
	  CstVecPrim[] _preReqs;
	}

	this(string name, _esdl__Proxy root) {
	  // import std.stdio;
	  // writeln("New vec ", name);
	  super(name, root);
	}

	override string name() {
	  return _name;
	}

	override bool isRand() {
	  static if (HAS_RAND_ATTRIB) {
	    return true;
	  }
	  else {
	    return false;
	  }
	}

	void solveBefore(CstVecPrim other) {
	  static if (HAS_RAND_ATTRIB) {
	    other.addPreRequisite(this);
	  }
	  else {
	    assert (false);
	  }
	}

	void addPreRequisite(CstVecPrim domain) {
	  static if (HAS_RAND_ATTRIB) {
	    _preReqs ~= domain;
	  }
	  else {
	    assert (false);
	  }
	}
      }

// Primary Vector -- not an element of any array
class CstVector(V, rand RAND_ATTR, int N) if (N == 0):
  CstVectorBase!(V, RAND_ATTR, N)
    {
      alias RV = typeof(this);

      V* _var;
      _esdl__Proxy _parent;
      
      this(string name, ref V var, _esdl__Proxy parent) {
	// import std.stdio;
	// writeln("New vec ", name);
	super(name, parent.getProxyRoot());
	_var = &var;
	_parent = parent;
	_root = _parent.getProxyRoot();
      }

      final override string fullName() {
	if (_parent is _root) return _name;
	else  
	  return _parent.fullName() ~ "." ~ name();
      }
      
      final override bool isStatic() {
	return true;		// N == 0
      }

      void _esdl__setValRef(ref V var) {
	_var = &var;
      }
      
      override _esdl__Proxy getProxyRoot() {
	assert (_root !is null);
	return _root;
      }

      override RV getResolved() {
	return this;
      }

      // RV
      override CstVecExpr unroll(CstIterator iter, uint n) {
	return this;
      }

      override LEAF* getRef() {
	return _var;
      }

      override long value() {
	return cast (long) (*_var);
      }

      override bool isConst() {
	return false;
      }

      override bool isIterator() {
	return false;
      }

      override bool isOrderingExpr() {
	return false;		// only CstVecOrderingExpr return true
      }

      override void setDomainContext(CstPredicate pred,
				     ref CstDomain[] rnds,
				     ref CstDomain[] vars,
				     ref CstValue[] vals,
				     ref CstIterator[] iters,
				     ref CstDomain[] idxs,
				     ref CstDomain[] bitIdxs,
				     ref CstDomain[] deps) {
	static if (RAND_ATTR.isRand()) {
	  if (! canFind(rnds, this)) rnds ~= this;
	}
	else {
	  if (! canFind(vars, this)) vars ~= this;
	}
      }

      final override void markAsUnresolved(uint lap) {
	if (_unresolveLap != lap) {
	  _unresolveLap = lap;
	  foreach (pred; _rndPreds) {
	    pred.markAsUnresolved(lap);
	  }
	}
      }
      
      auto _esdl__sym(S ...)(CstRangeExpr[] indx=[])
      {
	static if (S.length == 0) {
	  assert (indx.length == 0);
	  return this;
	}
	else static if (S[0] == "") {
	  assert (indx.length == 1);
	  return this.opIndex(indx[0]);
	}
	else {
	  static assert (S.length == 1);
	  return __traits(getMember, this, S[0]);
	}
      }
    }

// Array Element
class CstVector(V, rand RAND_ATTR, int N) if (N != 0):
  CstVectorBase!(V, RAND_ATTR, N)
    {
      alias RV = typeof(this);
      alias P = CstVecArr!(V, RAND_ATTR, N-1);
      P _parent;

      CstVecExpr _indexExpr = null;
      int _pindex = 0;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedVec;

      this(string name, P parent, CstVecExpr indexExpr) {
	// import std.stdio;
	// writeln("New ", name);
	if (indexExpr.isConst()) {
	  uint index = cast(uint) indexExpr.evaluate();
	  this(name, parent, index);
	}
	else {
	  assert (parent !is null);
	  super(name, parent.getProxyRoot());
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	  _indexExpr = indexExpr;
	  // only concrete elements need be added
	  // getProxyRoot().addRndDomain(this);
	}
      }

      this(string name, P parent, uint index) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	super(name, parent.getProxyRoot());
	_parent = parent;
	// _indexExpr = _esdl__cstVal(index);
	_pindex = index;
	_root = _parent.getProxyRoot();
	
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

      final override string fullName() {
	return _parent.fullName() ~ "." ~ name();
      }
      
      override _esdl__Proxy getProxyRoot() {
	assert (_root !is null);
	return _root;
      }

      override RV getResolved() {
	// domains do not resolve by themselves -- we only check if a
	// domain has dependencies. If not, we make a call to getResolved()
	if (_resolvedCycle != getProxyRoot()._cycle) {
	  auto parent = _parent.getResolved();
	  if (_indexExpr) {
	    _resolvedVec = parent[cast(size_t) _indexExpr.evaluate()];
	  }
	  else {
	    _resolvedVec = parent[_pindex];
	  }
	  _resolvedCycle = getProxyRoot()._cycle;
	}
	return _resolvedVec;
      }

      // RV
      override CstVecExpr unroll(CstIterator iter, uint n) {
	if (_indexExpr) {
	  return _parent.unroll(iter,n)[_indexExpr.unroll(iter,n)];
	}
	else {
	  return _parent.unroll(iter,n)[_pindex];
	}
      }
      
      override LEAF* getRef() {
	if (_indexExpr) {
	  return _parent.getRef(cast(size_t) _indexExpr.evaluate());
	}
	else {
	  return _parent.getRef(this._pindex);
	}
      }

      override long value() {
      	if (_indexExpr) {
      	  return *(_parent.getRef(_indexExpr.evaluate()));
      	}
      	else {
      	  return *(_parent.getRef(this._pindex));
      	}
      }

      override bool isConst() {
	return false;
      }

      override bool isIterator() {
	return false;
      }

      override bool isOrderingExpr() {
	return false;		// only CstVecOrderingExpr return true
      }

      override void setDomainContext(CstPredicate pred,
				     ref CstDomain[] rnds,
				     ref CstDomain[] vars,
				     ref CstValue[] vals,
				     ref CstIterator[] iters,
				     ref CstDomain[] idxs,
				     ref CstDomain[] bitIdxs,
				     ref CstDomain[] deps) {
	static if (RAND_ATTR.isRand()) {
	  if (! this.isStatic()) {
	    if (_type <= DomType.LAZYMONO) _type = DomType.MAYBEMONO;
	  }
	  if (! canFind(rnds, this)) rnds ~= this;
	}
	else {
	  if (! canFind(vars, this)) vars ~= this;
	}
	_parent.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);

	if (_indexExpr !is null) {
	  // Here we need to put the parent as a dep for the pred
	  // and since this prim needs resolution, the constituents of
	  // the indexExpr need to trigger a function that finds out
	  // whether the _indexExpr has been fully resolved or
	  // not. When the indexExpr gets resolved, it should inform
	  // the parent about resolution which in turn should inform
	  // the pred that it can go ahead
	  _indexExpr.setDomainContext(pred, idxs, idxs, vals, iters, idxs, bitIdxs, deps);
	}
      }

      override void markAsUnresolved(uint lap) {
	if (isStatic()) {
	  if (_unresolveLap != lap) {
	    _unresolveLap = lap;
	    foreach (pred; _rndPreds) {
	      pred.markAsUnresolved(lap);
	    }
	  }
	}
	else {
	  _parent.markAsUnresolved(lap);
	}
      }

      auto _esdl__sym(S ...)(CstRangeExpr[] indx=[])
      {
	static if (S.length == 0) {
	  assert (indx.length == 0);
	  return this;
	}
	else static if (S[0] == "") {
	  assert (indx.length == 1);
	  return this.opIndex(indx[0]);
	}
	else {
	  static assert (S.length == 1);
	  return __traits(getMember, this, S[0]);
	}
      }
    }

// Arrays (Multidimensional arrays as well)

class CstVecArrIdx(V, rand RAND_ATTR, int N, int IDX,
		   P, int PIDX): CstVecArr!(V, RAND_ATTR, N)
{
  // static assert (is (typeof(this) == P.tupleof[PIDX]));
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  enum int _esdl__PINDEX = PIDX;
  this(string name, ref V var, _esdl__Proxy parent) {
    super(name, var, parent);
  }

  override RV unroll(CstIterator iter, uint n) {
    // import std.stdio;
    P parent = cast(P)(_parent);
    assert (parent !is null);
    assert (this is parent.tupleof[PIDX]);
    // writeln("Unrolling: ", parent.tupleof[PIDX].stringof);
    return this;
  }
}

abstract class CstVecArrBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) != 0): CstVecPrim, CstVecArrIntf
{
  enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
  alias LEAF = LeafElementType!V;
  alias RAND = RAND_ATTR;

  alias L = ElementTypeN!(V, N);
  alias E = ElementTypeN!(V, N+1);

  static if (_esdl__ArrOrder!(V, N+1) == 0) {
    alias EV = CstVector!(V, RAND_ATTR, N+1);
  }
  else {
    alias EV = CstVecArr!(V, RAND_ATTR, N+1);
  }

  alias RV = CstVecArr!(V, RAND_ATTR, N);
  
  EV[] _elems;

  abstract EV createElem(uint i);
  abstract EV createElem(CstVecExpr index);

  abstract size_t getLen();
  
  // new EV(_name ~ "[#" ~ i.to!string() ~ "]",
  // 	 this, cast(uint) i);
  
  string _name;

  _esdl__Proxy _root;
  
  CstArrLength!(RV) _arrLen;

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

  static if (HAS_RAND_ATTRIB) {
    CstVecPrim[] _preReqs;
  }

  bool isRand() {
    static if (HAS_RAND_ATTRIB) {
      return true;
    }
    else {
      return false;
    }
  }

  void solveBefore(CstVecPrim other) {
    static if (HAS_RAND_ATTRIB) {
      other.addPreRequisite(this);
    }
    else {
      assert(false);
    }
  }

  void addPreRequisite(CstVecPrim prim) {
    static if (HAS_RAND_ATTRIB) {
      _preReqs ~= prim;
    }
    else {
      assert(false);
    }
  }

  uint maxArrLen() {
    static if (HAS_RAND_ATTRIB) {
      static if(isStaticArray!L) {
	return cast(uint) L.length;
      }
      else {
	return RAND_ATTR[N];
      }
    }
    else {
      return uint.max;
    }
  }

  static if (HAS_RAND_ATTRIB) {
    static private void _setLen(A, N...)(ref A arr, size_t v, N indx)
      if(isArray!A) {
	static if(N.length == 0) {
	  static if(isDynamicArray!A) {
	    arr.length = v;
	    // import std.stdio;
	    // writeln(arr, " indx: ", N.length);
	  }
	  else {
	    assert(false, "Can not set length of a fixed length array");
	  }
	}
	else {
	  // import std.stdio;
	  // writeln(arr, " indx: ", N.length);
	  _setLen(arr[indx[0]], v, indx[1..$]);
	}
      }

  }
  
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
	import std.conv: to;
	_elems[i] = createElem(i);
      }
    }
  }

  CstArrLength!(RV) length() {
    return _arrLen;
  }

  CstArrLength!(RV) arrLen() {
    return _arrLen;
  }

  EV opIndex(CstVecExpr indexExpr) {
    if (indexExpr.isConst()) {
      size_t index = cast(size_t) indexExpr.evaluate();
      if (_arrLen.isSolved()) {
	if (_arrLen.evaluate() <= index) {
	  assert (false, "Index Out of Range");
	}
      }
      buildElements(index+1);
      return _elems[index];
    }
    else {
      return createElem(indexExpr);
    }
  }

  EV opIndex(size_t index) {
    if (_arrLen.isSolved()) {
      uint len = cast(uint) _arrLen.evaluate();
      if (len <= index) {
	assert (false, "Index Out of Range");
      }
      buildElements(len);
    }
    else {
      buildElements(index+1);
    }
    // assert (_elems[index]._indexExpr is null);
    return _elems[index];
  }

  void _esdl__doRandomize(_esdl__RandGen randGen) {
    static if (HAS_RAND_ATTRIB) {
      assert (_arrLen !is null);
      // if there is no constraint on the length of the array,
      // do not try to randomize it, since it will probably create a
      // big array which might lead to memory allocation issues
      buildElements(getLen());
      for (size_t i=0; i != arrLen.evaluate(); ++i) {
	this[i]._esdl__doRandomize(randGen);
      }
    }
    else {
      assert (false);
    }
  }

  EV _esdl__elems() {
    return this[_esdl__iter()];
  }

  final bool _esdl__isVecArray() {return true;}
  final CstIterator _esdl__iter() {
    CstArrIterator!(RV) iter = arrLen.makeIterVar();
    return iter;
  }
  final CstVecIntf _esdl__getChild(uint n) {
    return this[n];
  }

}

// Primary Array
class CstVecArr(V, rand RAND_ATTR, int N) if (N == 0):
  CstVecArrBase!(V, RAND_ATTR, N)
    {
      alias RV = typeof(this);

      alias RAND=RAND_ATTR;


      V* _var;
      _esdl__Proxy _parent;
    
      void _esdl__setValRef(ref V var) {
	_var = &var;
      }
      
      this(string name, ref V var, _esdl__Proxy parent) {
	super(name);
	_var = &var;
	_parent = parent;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!(RV) (name ~ "->length", this);
      }

      final bool isStatic() {
	return true; 		// N == 0
      }

      final string fullName() {
	if (_parent is _root) return _name;
	else  
	  return _parent.fullName() ~ "." ~ name();
      }
      
      RV getResolved() {
	return this;
      }

      RV unroll(CstIterator iter, uint n) {
	return this;
      }

      static private auto getRef(A, N...)(ref A arr, N indx)
	if (isArray!A && N.length > 0 && isIntegral!(N[0])) {
	  static if (N.length == 1) return &(arr[indx[0]]);
	  else {
	    return getRef(arr[indx[0]], indx[1..$]);
	  }
	}

      auto getRef(J...)(J indx) if(isIntegral!(J[0])) {
	return getRef(*_var, cast(size_t) indx);
      }

      void setLen(N...)(size_t v, N indx) {
	static if (HAS_RAND_ATTRIB) {
	  _setLen(*_var, v, indx);
	}
	else {
	  assert (false);
	}
      }

      static private size_t _getLen(A, N...)(ref A arr, N indx) if(isArray!A) {
	static if (N.length == 0) return arr.length;
	else {
	  if (arr.length == 0) return 0;
	  else return _getLen(arr[indx[0]], indx[1..$]);
	}
      }

      size_t _getLen(N...)(N indx) {
	return _getLen(*_var, indx);
      }

      override size_t getLen() {
	return _getLen();
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomain[] rnds,
			    ref CstDomain[] vars,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstDomain[] idxs,
			    ref CstDomain[] bitIdxs,
			    ref CstDomain[] deps) {
	// arrlen should not be handled here. It is handled as part
	// of the indexExpr in the elements when required (that is
	// when indexExpr is not contant, but an expression)
	  
	// auto iter = arrLen.makeIterVar();
	// iters ~= iter;

	// no parent
      }

      void markAsUnresolved(uint lap) {
	foreach (elem; _elems) {
	  elem.markAsUnresolved(lap);
	}
      }

      auto _esdl__sym(S ...)(CstRangeExpr[] indx=[])
      {
	static if (S.length == 0) return this;
	else static if (S[0] == "") {
	  return this.opIndex(indx[0])._esdl__sym!(S[1..$])(indx[1..$]);
	}
	else {
	  static assert (S.length == 1);
	  return __traits(getMember, this, S[0]);
	}
      }

      override EV createElem(uint i) {
	import std.conv: to;
	return new EV(name() ~ "[#" ~ i.to!string() ~ "]",
		      this, i);
      }

      override EV createElem(CstVecExpr index) {
	return new EV(name() ~ "[#" ~ index.describe() ~ "]",
		      this, index);
      }

      
    }

// Array that is elelment of another array
class CstVecArr(V, rand RAND_ATTR, int N) if (N != 0):
  CstVecArrBase!(V, RAND_ATTR, N)
    {
      alias P = CstVecArr!(V, RAND_ATTR, N-1);
      P _parent;
      CstVecExpr _indexExpr = null;
      int _pindex = 0;

      alias RV = typeof(this);

      alias RAND=RAND_ATTR;
      
      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedVec;

      this(string name, P parent, CstVecExpr indexExpr) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	super(name);
	_parent = parent;
	_indexExpr = indexExpr;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!(RV) (name ~ "->length", this);
      }

      this(string name, P parent, uint index) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	super(name);
	_parent = parent;
	// _indexExpr = _esdl__cstVal(index);
	_pindex = index;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!(RV) (name ~ "->length", this);
      }

      override bool opEquals(Object other) {
	auto rhs = cast (RV) other;
	if (rhs is null) return false;
	else return (_parent == rhs._parent && _indexExpr == _indexExpr);
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
	    _resolvedVec = parent[_indexExpr.evaluate()];
	  }
	  else {
	    _resolvedVec = parent[_pindex];
	  }
	  _resolvedCycle = getProxyRoot()._cycle;
	}
	return _resolvedVec;
      }

      RV unroll(CstIterator iter, uint n) {
	if (_indexExpr) {
	  return _parent.unroll(iter,n)[_indexExpr.unroll(iter,n)];
	}
	else {
	  return _parent.unroll(iter,n)[_pindex];
	}
      }

      void setLen(N...)(size_t v, N indx) {
	static if (HAS_RAND_ATTRIB) {
	  _parent.setLen(v, _pindex, indx);
	}
      }

      static private size_t _getLen(A, N...)(ref A arr, N indx) if(isArray!A) {
	static if (N.length == 0) return arr.length;
	else {
	  return _getLen(arr[indx[0]], indx[1..$]);
	}
      }

      size_t _getLen(N...)(N indx) {
	return _parent._getLen(_pindex, indx);
      }

      override size_t getLen() {
	return _getLen();
      }

      static private auto getRef(A, N...)(ref A arr, N indx)
	if (isArray!A && N.length > 0 && isIntegral!(N[0])) {
	  static if (N.length == 1) return &(arr[indx[0]]);
	  else {
	    return getRef(arr[indx[0]], indx[1..$]);
	  }
	}

      auto getRef(N...)(N indx) if (isIntegral!(N[0])) {
	if (_indexExpr) {
	  assert (_indexExpr.isConst());
	  return _parent.getRef(cast (size_t) _indexExpr.evaluate(), indx);
	}
	else {
	  return _parent.getRef(this._pindex, indx);
	}
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomain[] rnds,
			    ref CstDomain[] vars,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstDomain[] idxs,
			    ref CstDomain[] bitIdxs,
			    ref CstDomain[] deps) {
	// arrlen should not be handled here. It is handled as part
	// of the indexExpr in the elements when required (that is
	// when indexExpr is not contant, but an expression)
	  
	// auto iter = arrLen.makeIterVar();
	// iters ~= iter;
	_parent.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
	if (_indexExpr !is null) {
	  _indexExpr.setDomainContext(pred, idxs, idxs, vals, iters, idxs, bitIdxs, deps);
	}
      }

      void markAsUnresolved(uint lap) {
	if (isStatic()) {
	  foreach (elem; _elems) {
	    elem.markAsUnresolved(lap);
	  }
	}
	else {
	  _parent.markAsUnresolved(lap);
	}
      }

      auto _esdl__sym(S ...)(CstRangeExpr[] indx=[])
      {
	static if (S.length == 0) return this;
	else static if (S[0] == "") {
	  return this.opIndex(indx[0])._esdl__sym!(S[1..$])(indx[1..$]);
	}
	else {
	  static assert (S.length == 1);
	  return __traits(getMember, this, S[0]);
	}
      }

      override EV createElem(uint i) {
	import std.conv: to;
	return new EV(name() ~ "[#" ~ i.to!string() ~ "]",
		      this, i);
      }

      override EV createElem(CstVecExpr index) {
	return new EV(name() ~ "[#" ~ index.describe() ~ "]",
		      this, index);
      }
    }

