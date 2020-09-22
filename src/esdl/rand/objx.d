module esdl.rand.objx;

import esdl.data.bvec;
import esdl.data.bstr;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray,
  isDynamicArray;

import esdl.rand.misc;
import esdl.rand.intr;
import esdl.rand.base: CstVecExpr, CstIterator, DomType, CstDomain,
  CstLogicExpr, CstPredicate, CstObjIntf, CstObjectIntf, CstObjArrIntf;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.expr: CstArrLength, _esdl__cstVal,
  CstArrIterator, CstValue, CstRangeExpr;

import esdl.rand.intr: IntRangeSet;
import esdl.rand.meta: _esdl__ProxyResolve;

import std.algorithm.searching: canFind;


// T represents the type of the declared array/non-array member
// N represents the level of the array-elements we have to traverse
// for the elements this CstObject represents

class CstObjIdx(V, rand R, int N, int IDX,
		P, int PIDX): CstObject!(V, R, N)
{
  enum _esdl__ISRAND = R.isRand();
  enum _esdl__HASPROXY = R.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  this(string name, ref V var, _esdl__Proxy parent) {
    super(name, var, parent);
  }

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

class CstObjectBase(V, rand R, int N) if (_esdl__ArrOrder!(V, N) == 0):
  _esdl__ProxyResolve!(LeafElementType!V)
    {
      enum HAS_RAND_ATTRIB = R.isRand();
      alias LEAF = LeafElementType!V;

      this(ref LEAF var, _esdl__Proxy parent) {
	super(var, parent);
      }

      this(LEAF var, _esdl__Proxy parent) {
	super(var, parent);
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

class CstObject(V, rand R, int N) if (N == 0):
  CstObjectBase!(V, R, N)
    {
      alias RV = typeof(this);

      _esdl__Proxy _root;
      _esdl__Proxy _parent;
      
      static if (is (V == struct)) {
	this(string name, ref V var, _esdl__Proxy parent) {
	  // import std.stdio;
	  // writeln("New obj ", name);
	  super(var, parent);
	  _name = name;
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	  // _var = &var;
	}
      }
      else {
	this(string name, V var, _esdl__Proxy parent) {
	  // import std.stdio;
	  // writeln("New obj ", name);
	  super(var, parent);
	  _name = name;
	  _parent = parent;
	  _root = _parent.getProxyRoot();
	  // _var = &var;
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

      // void _esdl__setValRef(ref V var) {
      // 	_var = &var;
      // }
      
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

    }

class CstObject(V, rand R, int N) if (N != 0):
  // _esdl__ProxyResolve!(LeafElementType!V)
  CstObjectBase!(V, R, N)
    {

      alias RV = typeof(this);
      alias P = CstObjArr!(V, R, N-1);

      P _parent;
      _esdl__Proxy _root;

      CstVecExpr _indexExpr = null;
      int _pindex = 0;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedObj;

      this(string name, P parent, CstVecExpr indexExpr) {
	super(null, parent.getProxyRoot());
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	_name = name;
	_parent = parent;
	_indexExpr = indexExpr;
	_root = _parent.getProxyRoot();
	// only concrete elements need be added
	// getProxyRoot().addRndDomain(this);
      }

      this(string name, P parent, uint index) {
	super(null, parent.getProxyRoot());
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	// super(parent.getProxyRoot());
	_name = name;
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
      
      _esdl__Proxy getProxyRoot()() {
	assert (_root !is null);
	return _root;
      }

      RV getResolved() {
	// if (_resolvedCycle != getProxyRoot()._cycle) {
	// 	auto parent = _parent.getResolved();
	// 	if (_indexExpr) {
	// 	  _resolvedObj = parent[cast(size_t) _indexExpr.evaluate()];
	// 	}
	// 	else {
	// 	  _resolvedObj = parent[_pindex];
	// 	}
	// 	_resolvedCycle = getProxyRoot()._cycle;
	// }
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
	    return _parent.getRef(cast(size_t) _indexExpr.evaluate());
	  }
	  else {
	    return _parent.getRef(this._pindex);
	  }
	}
      }
      else {
	LEAF getRef() {
	  if (_indexExpr) {
	    return _parent.getRef(cast(size_t) _indexExpr.evaluate());
	  }
	  else {
	    return _parent.getRef(this._pindex);
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
			    ref CstDomain[] vars,
			    ref CstValue[] vals,
			    ref CstIterator[] iters,
			    ref CstDomain[] idxs,
			    ref CstDomain[] bitIdxs,
			    ref CstDomain[] deps) {
	static if (R.isRand()) {
	  // 	if (! canFind(rnds, this)) rnds ~= this;
	  // }
	  // else {
	  // 	if (! canFind(vars, this)) vars ~= this;
	}
	if (_parent.isStatic()) {
	  deps ~= _parent._arrLen;
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
    }


// template CstObjArr(T, int I, int N=0)
//   if(_esdl__ArrOrder!(T, I, N) != 0) {
//   alias CstObjArr = CstObjArr!(typeof(T.tupleof[I]), LeafElementType!(T.tupleof[I]),
// 			       getRandAttr!(T, I), N);
// }

// Arrays (Multidimensional arrays as well)
class CstObjArrIdx(V, rand R, int N, int IDX,
		   P, int PIDX): CstObjArr!(V, R, N)
{
  enum _esdl__ISRAND = R.isRand();
  enum _esdl__HASPROXY = R.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;
  this(string name, ref V var, _esdl__Proxy parent) {
    super(name, var, parent);
  }
  override CstObjArr!(V, R, N) unroll(CstIterator iter, uint n) {
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


abstract class CstObjArrBase(V, rand R, int N) if (_esdl__ArrOrder!(V, N) != 0):
  CstObjArrIntf
  {

    alias RV = CstObjArr!(V, R, N);

    enum HAS_RAND_ATTRIB = R.isRand();
    alias LEAF = LeafElementType!V;

    alias L = ElementTypeN!(V, N);
    alias E = ElementTypeN!(V, N+1);

    static if (_esdl__ArrOrder!(V, N+1) == 0) {
      alias EV = CstObject!(V, R, N+1);
    }
    else {
      alias EV = CstObjArr!(V, R, N+1);
    }

    CstArrLength!RV _arrLen;

    EV[] _elems;

    string _name;

    _esdl__Proxy _root;

    string name() {
      return _name;
    }

    bool isRand() {
      static if (HAS_RAND_ATTRIB) {
	return true;
      }
      else {
	return false;
      }
    }

    abstract EV createElem(CstVecExpr indexExpr);
    abstract EV createElem(uint i);
    
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
	  // import std.conv: to;
	  _elems[i] = createElem(i);
	}
      }
      // static if (is (EV: CstObjectIntf)) {
      //   if (_parent.isStatic()) {
      // 	import std.stdio;
      // 	writeln("Need to call setOuter in these CstObject's:");
      // 	foreach (elem; _elems) {
      // 	  writeln("    ", elem.fullName());
      // 	}
      //   }
      // }
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

    abstract size_t getLen();
    
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

    EV _esdl__elems() {
      return this[_esdl__iter()];
    }

    CstArrLength!RV length() {
      return _arrLen;
    }

    CstArrLength!RV arrLen() {
      return _arrLen;
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
    final bool _esdl__isObjArray() {return true;}

    final CstIterator _esdl__iter() {
      CstArrIterator!RV iter = arrLen.makeIterVar();
      return iter;
    }

    final CstObjIntf _esdl__getChild(uint n) {
      return this[n];
    }

    final void visit() {
      // import std.stdio;
      // writeln("Visiting: ", this.fullName());
    }

    _esdl__Proxy getProxyRoot()() {
      assert (_root !is null);
      return _root;
    }
  

    uint maxArrLen() {
      static if (HAS_RAND_ATTRIB) {
	static if(isStaticArray!L) {
	  return L.length;
	}
	else {
	  return R[N];
	}
      }
      else {
	return uint.max;
      }
    }

}

class CstObjArr(V, rand R, int N) if (N == 0 && _esdl__ArrOrder!(V, N) != 0):
  CstObjArrBase!(V, R, N)
{
  alias RAND=R;

  V* _var;
  _esdl__Proxy _parent;
    
  void _esdl__setValRef(ref V var) {
    _var = &var;
  }
      
  this(string name, ref V var, _esdl__Proxy parent) {
    _name = name;
    _var = &var;
    _parent = parent;
    _root = _parent.getProxyRoot();
    _arrLen = new CstArrLength!RV(name ~ "->length", this);
  }

  _esdl__Proxy getProxyRoot() {
    assert (_root !is null);
    return _root;
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

  static private auto getRef(A, N...)(ref A arr, N indx)
    if (isArray!A && N.length > 0 && isIntegral!(N[0])) {
      static if (N.length == 1) {
	static if (is (LEAF == struct)) {
	  return &(arr[cast(size_t) (indx[0])]);
	}
	else {
	  return (arr[cast(size_t) (indx[0])]);
	}
      }
      else {
	return getRef(arr[cast(size_t) (indx[0])], indx[1..$]);
      }
    }

  auto getRef(J...)(J indx) if(isIntegral!(J[0])) {
    return getRef(*_var, indx);
  }

  void setLen(N...)(size_t v, N indx) {
    static if (HAS_RAND_ATTRIB) {
      _setLen(*_var, v, indx);
    }
  }

  override size_t getLen() {
    return _getLen();
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

  override EV createElem(CstVecExpr indexExpr) {
    return new EV(name ~ "[" ~ indexExpr.describe() ~ "]", this, indexExpr);
  }
  
  override EV createElem(uint i) {
    import std.conv: to;
    return new EV(_name ~ "[#" ~ i.to!string() ~ "]",
		  this, cast(uint) i);
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
}

class CstObjArr(V, rand R, int N) if(N != 0 && _esdl__ArrOrder!(V, N) != 0):
  CstObjArrBase!(V, R, N)
{
  alias P = CstObjArr!(V, R, N-1);

  P _parent;
  CstVecExpr _indexExpr = null;
  int _pindex = 0;

  alias RAND=R;
      
  uint _resolvedCycle;	// cycle for which indexExpr has been resolved
  RV _resolvedObj;

  this(string name, P parent, CstVecExpr indexExpr) {
    // import std.stdio;
    // writeln("New ", name);
    assert (parent !is null);
    _name = name;
    _parent = parent;
    _indexExpr = indexExpr;
    _root = _parent.getProxyRoot();
    _arrLen = new CstArrLength!RV(name ~ "->length", this);
  }

  this(string name, P parent, uint index) {
    // import std.stdio;
    // writeln("New ", name);
    assert (parent !is null);
    _name = name;
    _parent = parent;
    // _indexExpr = _esdl__cstVal(index);
    _pindex = index;
    _root = _parent.getProxyRoot();
    _arrLen = new CstArrLength!RV(name ~ "->length", this);
  }

  _esdl__Proxy getProxyRoot() {
    assert (_root !is null);
    return _root;
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
    // if (_resolvedCycle != getProxyRoot()._cycle) {
    //   auto parent = _parent.getResolved();
    //   if (_indexExpr) {
    // 	_resolvedObj = parent[_indexExpr.evaluate()];
    //   }
    //   else {
    // 	_resolvedObj = parent[_pindex];
    //   }
    //   _resolvedCycle = getProxyRoot()._cycle;
    // }
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

  void setLen(N...)(size_t v, N indx) {
    static if (HAS_RAND_ATTRIB) {
      _parent.setLen(v, _pindex, indx);
    }
  }

  override size_t getLen() {
    return _getLen();
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

  static private auto getRef(A, N...)(ref A arr, N indx)
    if (isArray!A && N.length > 0 && isIntegral!(N[0])) {
      static if (N.length == 1) {
	static if (is (LEAF == struct)) {
	  return &(arr[indx[0]]);
	}
	else {
	  return (arr[indx[0]]);
	}
      }
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

  override EV createElem(CstVecExpr indexExpr) {
    return new EV(name ~ "[" ~ indexExpr.describe() ~ "]", this, indexExpr);
  }
  
  override EV createElem(uint i) {
    import std.conv: to;
    return new EV(_name ~ "[#" ~ i.to!string() ~ "]",
		  this, cast(uint) i);
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
    if (_parent.isStatic()) {
      deps ~= _parent._arrLen;
    }
    _parent.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
    if (_indexExpr !is null) {
      _indexExpr.setDomainContext(pred, idxs, idxs, vals, iters, idxs, bitIdxs, deps);
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

}
