module esdl.rand.objx;

import esdl.data.bvec;
import esdl.data.bstr;
import esdl.data.queue;
import std.traits: isIntegral, isBoolean, isArray,
  isStaticArray, isDynamicArray;

import esdl.rand.misc;
import esdl.rand.base: CstVecExpr, CstIterator, DomType, CstDomain, CstDomSet,
  CstObjSet, CstPredicate, CstVarNodeIntf, CstVecNodeIntf, CstObjArrIntf;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.expr: CstArrLength, _esdl__cstVal,
  CstArrIterator, CstValue, CstRangeExpr;

import esdl.rand.meta: _esdl__ProxyResolve, _esdl__staticCast;

import std.algorithm.searching: canFind;

interface CstObjIndexed { }

// V represents the type of the declared array/non-array member
// N represents the level of the array-elements we have to traverse
// for the elements this CstObject represents

class CstObjIdx(V, rand RAND_ATTR, int N, int IDX,
		P, int PIDX): CstObject!(V, RAND_ATTR, N)
{
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;

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

  static if (PIDX >= 0) {	// exclude randomize_with
    override _esdl__Proxy unroll(CstIterator iter, uint n) {
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

	override bool isRand() {
	  static if (HAS_RAND_ATTRIB) {
	    return true;
	  }
	  else {
	    return false;
	  }
	}

      }

class CstObject(V, rand RAND_ATTR, int N) if (N == 0):
  CstObjectBase!(V, RAND_ATTR, N)
    {
      alias RV = typeof(this);

      _esdl__Proxy _root;
      _esdl__Proxy _parent;
      
      static if (is (LEAF == struct)) {
	this(string name, _esdl__Proxy parent, V* var) {
	  super(name, parent, var);
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	}
      }
      else {
	this(string name, _esdl__Proxy parent, V var) {
	  super(name, parent, var);
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	}
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
      override _esdl__Proxy unroll(CstIterator iter, uint n) {
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

      override void visit() {
	// import std.stdio;
	// writeln("Visiting: ", this.fullName());
	assert (this.getRef() !is null);
	_esdl__setValRef(this.getRef());
	_esdl__doConstrain(getProxyRoot());
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomain[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomain[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstVecNodeIntf[] idxs,
			    ref CstDomain[] bitIdxs,
			    ref CstVecNodeIntf[] deps) {
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

      CstVecExpr _indexExpr = null;
      int _pindex = 0;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      _esdl__Proxy _root;

      this(string name, P parent, CstVecExpr indexExpr) {
	if (indexExpr.isConst()) {
	  uint index = cast(uint) indexExpr.evaluate();
	  this(name, parent, index);
	}
	else {
	  assert (parent !is null);
	  super(name, parent.getProxyRoot(), null);
	  _name = name;
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	  _indexExpr = indexExpr;
	}
      }

      this(string name, P parent, uint index) {
	assert (parent !is null);
	super(name, parent.getProxyRoot(), null);
	// super(parent.getProxyRoot());
	_name = name;
	_parent = parent;
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
      override _esdl__Proxy unroll(CstIterator iter, uint n) {
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

      override void visit() {
	// import std.stdio;
	// writeln("Visiting: ", this.fullName());
	assert (this.getRef() !is null);
	_esdl__setValRef(this.getRef());
	_esdl__doConstrain(getProxyRoot());
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomain[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomain[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstVecNodeIntf[] idxs,
			    ref CstDomain[] bitIdxs,
			    ref CstVecNodeIntf[] deps) {
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
	  CstDomain[] indexes;
	  _indexExpr.setDomainContext(pred, indexes, rndArrs, indexes, varArrs, vals, iters, idxs, bitIdxs, deps);
	  foreach (index; indexes) idxs ~= index;
	}
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
  override RV unroll(CstIterator iter, uint n) {
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

  this(string name) {
    super(name);
  }
    
  CstArrLength!RV _arrLen;

  EV[] _elems;

  abstract EV createElem(CstVecExpr indexExpr);
  abstract EV createElem(uint i);
    
  bool isRand() {
    static if (HAS_RAND_ATTRIB) {
      return true;
    }
    else {
      return false;
    }
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
	_elems[i] = createElem(i);
      }
    }
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

  EV opIndex(CstRangeExpr index) {
    assert (index._rhs is null);
    return this.opIndex(index._lhs);
  }

  EV opIndex(size_t index) {
    if (_arrLen.isSolved()) {
      auto len = _arrLen.evaluate();
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
      for (size_t i=0; i != _arrLen.evaluate(); ++i) {
	this[i]._esdl__doRandomize(randGen);
      }
    }
    else {
      assert (false);
    }
  }

  uint maxArrLen() {
    static if (HAS_RAND_ATTRIB) {
      static if(isStaticArray!L) {
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

  final CstVarNodeIntf _esdl__getChild(uint n) {
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

  final void visit() {
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
      
      this(string name, _esdl__Proxy parent, V* var) {
	super(name);
	_var = var;
	_parent = parent;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!RV(name ~ "->length", this);
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

      RV unroll(CstIterator iter, uint n) {
	return this;
      }

      override void setLen(size_t len) {
	setLenTmpl(this, len);
      }
      
      override size_t getLen() {
	return getLenTmpl(this);
      }

      void setDomainContext(CstPredicate pred,
			    ref CstDomain[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomain[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstVecNodeIntf[] idxs,
			    ref CstDomain[] bitIdxs,
			    ref CstVecNodeIntf[] deps) {
	// arrlen should not be handled here. It is handled as part
	// of the indexExpr in the elements when required (that is
	// when indexExpr is not contant, but an expression)
	  
	// auto iter = arrLen.makeIterVar();
	// iters ~= iter;

	// no parent
      }

      override EV createElem(CstVecExpr indexExpr) {
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
      CstVecExpr _indexExpr = null;
      int _pindex = 0;

      alias RAND=RAND_ATTR;
      
      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      this(string name, P parent, CstVecExpr indexExpr) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	super(name);
	_parent = parent;
	_indexExpr = indexExpr;
	_root = _parent.getProxyRoot();
	_arrLen = new CstArrLength!RV(name ~ "->length", this);
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
	_arrLen = new CstArrLength!RV(name ~ "->length", this);
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

      RV unroll(CstIterator iter, uint n) {
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
			    ref CstDomain[] rnds,
			    ref CstDomSet[] rndArrs,
			    ref CstDomain[] vars,
			    ref CstDomSet[] varArrs,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstVecNodeIntf[] idxs,
			    ref CstDomain[] bitIdxs,
			    ref CstVecNodeIntf[] deps) {
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
	  CstDomain[] indexes;
	  _indexExpr.setDomainContext(pred, indexes, rndArrs, indexes, varArrs,
				      vals, iters, idxs, bitIdxs, deps);
	  foreach (index; indexes) idxs ~= index;
	}
      }

      override EV createElem(CstVecExpr indexExpr) {
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
  if ((isArray!A || isQueue!A) && N.length > 0 && isIntegral!(N[0])) {
    alias LEAF = LeafElementType!A;
    static if (N.length == 1) {
      static if (is (LEAF == struct)) {
	return &(arr[cast(size_t) (indx[0])]);
      }
      else {
	return (arr[cast(size_t) (indx[0])]);
      }
    }
    else {
      return getArrElemTmpl(arr[cast(size_t) (indx[0])], indx[1..$]);
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
  if (isArray!A || isQueue!A) {
    static if (N.length == 0) return arr.length;
    else {
      if (arr.length == 0) return 0;
      else return getArrLenTmpl(arr[indx[0]], indx[1..$]);
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
  if (isArray!A || isQueue!A) {
    static if(N.length == 0) {
      static if(isDynamicArray!A || isQueue!A) {
	arr.length = v;
      }
      else {
	assert(false, "Can not set length of a fixed length array");
      }
    }
    else {
      setArrLen(arr[indx[0]], v, indx[1..$]);
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

