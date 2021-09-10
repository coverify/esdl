module esdl.rand.vecx;

import esdl.data.bvec;
import esdl.data.bstr;
import esdl.data.queue;
import std.traits: isIntegral, isBoolean, isArray, KeyType,
  isStaticArray, isDynamicArray, isSigned, isAssociativeArray;

import esdl.rand.misc;
import esdl.rand.base: CstVecPrim, CstVecTerm, CstIterator, DomType, CstDomBase,
  CstDomSet, CstVarNodeIntf, CstVecNodeIntf, CstVarGlobIntf, CstValue,
  CstLogicTerm, CstDepIntf;
import esdl.rand.pred: CstPredicate;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.expr: CstRangeExpr, CstVec2LogicExpr;
import esdl.rand.domain: CstVecValue, CstArrIterator, CstArrLength, CstDomain;
import esdl.rand.meta: _esdl__ProxyResolve, _esdl__staticCast, _esdl__ARG;

import esdl.base.rand: _esdl__RandGen;

import std.algorithm.searching: canFind;

interface CstVecIndexed { }

// V represents the type of the declared array/non-array member
// N represents the level of the array-elements we have to traverse
// for the elements this CstVector represents

class CstVectorGlob(V, rand RAND_ATTR, int N, alias SYM)
  : CstVector!(V, RAND_ATTR, N), CstVarGlobIntf
{
  alias RV = typeof(this);
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static assert (_esdl__ISRAND == false);

  this(string name, _esdl__Proxy parent, V* var) {
    super(name, parent, var);
  }

  override void _esdl__fixRef() {
    _esdl__setValRef(& SYM);
  }
  
  // no unrolling is possible without adding rand proxy
  override RV unroll(CstIterator iter, ulong n) {
    return this;
  }
}

class CstVectorGlobEnum(V, rand RAND_ATTR, int N)
  : CstVector!(V, RAND_ATTR, N), CstVarGlobIntf
{
  alias RV = typeof(this);
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static assert (_esdl__ISRAND == false);
  
  V _var;

  this(string name, _esdl__Proxy parent, V var) {
    _var = var;
    super(name, parent, &_var);
  }

  override void _esdl__fixRef() {
    _esdl__setValRef(& _var);
  }
  
  // no unrolling is possible without adding rand proxy
  override RV unroll(CstIterator iter, ulong n) {
    return this;
  }

}

class CstVectorIdx(V, rand RAND_ATTR, int N, int IDX,
		   P, int PIDX): CstVector!(V, RAND_ATTR, N)
{
  alias RV = typeof(this);
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();
  alias _esdl__PROXYT = P;
  enum int _esdl__INDEX = IDX;

  this(string name, _esdl__Proxy parent, V* var) {
    super(name, parent, var);
  }

  static if (is (P: _esdl__ARG)) {
    override RV unroll(CstIterator iter, ulong n) {
      return this;
    }
  }
  else {
    override RV unroll(CstIterator iter, ulong n) {
      if (_parent !is _root) {
	P uparent = cast(P)(_parent.unroll(iter, n));
	assert (uparent !is null);
	return uparent.tupleof[PIDX];
      }
      else {
	return this;
      }
    }
    override RV getResolvedNode() {
      if (_parentsDepsAreResolved) return this;
      else {
	P uparent = cast(P)(_parent.getResolvedNode());
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
      return true;
      assert (proxy._esdl__outer !is null);
      return proxy._esdl__outer.rand_mode!(IDX)();
    }
  }

}


class CstVectorBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) == 0):
    CstDomain!(LeafElementType!V, RAND_ATTR), CstVecPrim
      {
	enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();
	alias LEAF = LeafElementType!V;
	alias RAND = RAND_ATTR;

	static if (HAS_RAND_ATTRIB) {
	  CstVecPrim[] _preReqs;
	}

	this(string name, _esdl__Proxy root) {
	  super(name, root);
	}

	override string name() {
	  return _name;
	}

	bool rand_mode() { return true; }
	// overridded in derived classes
	override bool isRand() { assert (false); }

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
      bool _parentsDepsAreResolved;
      
      this(string name, _esdl__Proxy parent, V* var) {
	super(name, parent.getProxyRoot());
	_var = var;
	_parent = parent;
	_root = _parent.getProxyRoot();
	_parentsDepsAreResolved = _parent.depsAreResolved();
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent.isRand();
      }

      final override bool inRange() { return _parent.inRange(); }

      final override string fullName() {
	if (_parent is _root) return _name;
	else  
	  return _parent.fullName() ~ "." ~ name();
      }
      
      void _esdl__setValRef(V* var) {
	_var = var;
      }
      
      override _esdl__Proxy getProxyRoot() {
	assert (_root !is null);
	return _root;
      }

      final override bool isStatic() {
	return _parent.isStatic();		// N == 0
      }

      final override bool isRolled() {
	return _parent.isRolled();		// N == 0
      }

      override bool depsAreResolved() {
	return _parentsDepsAreResolved;
      }

      override RV getResolvedNode() {
	return this;
      }

      // RV
      RV unroll(CstIterator iter, ulong n) {
	return this;
      }

      override LEAF* getRef() {
	return _var;
      }

      bool isConst() {
	return false;
      }

      bool isIterator() {
	return false;
      }

      void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	// setDomainContext is executed right in the start
	// dynamic rand_mode information is handled later
	// do not use isRand here
	static if (HAS_RAND_ATTRIB) {
	  if (this.isDist()) {
	    pred.addDist(this, context);
	  }
	  else {
	    pred.addUnresolvedRnd(this, context);
	  }
	}
	else {
	  pred.addVar(this, context);
	}
      }

      override CstDomSet getParentDomSet() {
	return null;
      }
      
    }

// Array Element
class CstVector(V, rand RAND_ATTR, int N) if (N != 0):
  CstVectorBase!(V, RAND_ATTR, N), CstVecIndexed
    {
      alias RV = typeof(this);
      alias P = CstVecArr!(V, RAND_ATTR, N-1);
      P _parent;

      bool _parentsDepsAreResolved;

      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;
      immutable bool _nodeIsMapped = false;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedVec;

      this(string name, P parent, CstVecTerm indexExpr, bool isMapped) {
	// if (indexExpr.isConst()) {
	//   ulong index = indexExpr.evaluate();
	//   this(name, parent, index);
	// }
	// else {
	assert (parent !is null);
	super(name ~ "[#" ~ indexExpr.describe() ~ "]", parent.getProxyRoot());
	_nodeIsMapped = isMapped;
	_parent = parent;
	_root = _parent.getProxyRoot();
	_parentsDepsAreResolved = _parent.depsAreResolved();
	_indexExpr = indexExpr;
	if (_parent._unresolvedDomainPreds.length > 0 ||
	    _parent._esdl__parentIsConstrained) {
	  _type = DomType.MULTI;
	  _esdl__parentIsConstrained = true;
	}
	// }
      }

      this(string name, P parent, ulong index, bool isMapped) {
	import std.conv: to;
	assert (parent !is null);
	super(name  ~ "[#" ~ index.to!string() ~ "]", parent.getProxyRoot());
	_nodeIsMapped = isMapped;
	_parent = parent;
	_pindex = index;
	_root = _parent.getProxyRoot();
	_parentsDepsAreResolved = _parent.depsAreResolved();
	if (_parent._unresolvedDomainPreds.length > 0 ||
	    _parent._esdl__parentIsConstrained) {
	  _type = DomType.MULTI;
	  _esdl__parentIsConstrained = true;
	}
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent.isRand();
      }

      final override bool inRange() {
	if (_indexExpr !is null) assert (false, "Unresolved Index");
	else {
	  // import std.stdio;
	  // writeln("inRange: ", name(), " - ", _pindex);
	  return _parent.inRange() && _parent.inRangeIndex(_pindex);
	}
      }

      override bool opEquals(Object other) {
	auto rhs = cast (RV) other;
	if (rhs is null) return false;
	else {
	  if (_indexExpr is null) {
	    if (rhs._indexExpr !is null) return false;
	    else return (_parent == rhs._parent && _pindex == rhs._pindex);
	  }
	  else {
	    if (rhs._indexExpr is null) return false;
	    else return (_parent == rhs._parent && _indexExpr == rhs._indexExpr);
	  }
	}
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
      
      override _esdl__Proxy getProxyRoot() {
	assert (_root !is null);
	return _root;
      }

      override bool depsAreResolved() {
	return _parentsDepsAreResolved && _nodeIsMapped;
      }

      override RV getResolvedNode() {
	// domains do not resolve by themselves -- we only check if a
	// domain has dependencies. If not, we make a call to getResolvedNode()
	if (_resolvedCycle != getProxyRoot()._cycle) {
	  auto parent = _parent.getResolvedNode();
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
      override RV unroll(CstIterator iter, ulong n) {
	if (_indexExpr) {
	  return _parent.unroll(iter,n)[_indexExpr.unroll(iter,n)];
	}
	else {
	  return _parent.unroll(iter,n)[_pindex];
	}
      }
      
      override LEAF* getRef() {
	// import std.stdio;
	// writeln("getRef: ", name());
	if (_indexExpr) {
	  return getRefTmpl(_parent, cast(size_t) _indexExpr.evaluate());
	}
	else {
	  return getRefTmpl(_parent, this._pindex);
	}
      }

      bool isConst() {
	return false;
      }

      bool isIterator() {
	return false;
      }

      void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	// setDomainContext is executed right in the start
	// dynamic rand_mode information is handled later
	// do not use isRand here
	static if (HAS_RAND_ATTRIB) {
	  if (! this.isStatic()) {
	    if (_type <= DomType.LAZYMONO) _type = DomType.MAYBEMONO;
	  }
	  if (this.isDist()) {
	    pred.addDist(this, context);
	  }
	  else {
	    pred.addUnresolvedRnd(this, context);
	  }
	}
	else {
	  pred.addVar(this, context);
	}

	if (_parent.isStatic()) {
	  auto len = _parent._arrLen;
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

      override CstDomSet getParentDomSet() {
	return _parent;
      }
      
    }

class CstVecArrGlob(V, rand RAND_ATTR, int N, alias SYM)
  : CstVecArr!(V, RAND_ATTR, N), CstVarGlobIntf
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

// Arrays (Multidimensional arrays as well)
class CstVecArrGlobEnum(V, rand RAND_ATTR, int N)
  : CstVecArr!(V, RAND_ATTR, N), CstVarGlobIntf
{
  // static assert (is (typeof(this) == P.tupleof[PIDX]));
  enum _esdl__ISRAND = RAND_ATTR.isRand();
  enum _esdl__HASPROXY = RAND_ATTR.hasProxy();

  static assert (_esdl__ISRAND == false);

  V _var;

  this(string name, _esdl__Proxy parent, V var) {
    _var = var;
    super(name, parent, &_var);
  }

  override void _esdl__fixRef() {
    _esdl__setValRef (& _var);
  }
  
  // no unrolling is possible without adding rand proxy
  override RV unroll(CstIterator iter, ulong n) {
    return this;
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
  this(string name, _esdl__Proxy parent, V* var) {
    super(name, parent, var);
  }

  static if (is (P: _esdl__ARG)) {
    override RV unroll(CstIterator iter, ulong n) {
      return this;
    }
  }
  else {
    override RV unroll(CstIterator iter, ulong n) {
      P uparent = cast(P)(_parent.unroll(iter, n));
      assert (uparent !is null);
      assert (this is uparent.tupleof[PIDX]);
      return this;
    }
    override RV getResolvedNode() {
      if (_parentsDepsAreResolved) return this;
      else {
	P uparent = cast(P)(_parent.getResolvedNode());
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
      return true;
      assert (proxy._esdl__outer !is null);
      return proxy._esdl__outer.rand_mode!(IDX)();
    }
  }
}


abstract class CstVecArrBase(V, rand RAND_ATTR, int N)
  if (_esdl__ArrOrder!(V, N) != 0): CstDomSet
{

  alias RV = CstVecArr!(V, RAND_ATTR, N);

  enum ARR_ORDER = _esdl__ArrOrder!(V, N);
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
  
  static if (isAssociativeArray!L) {
    static assert(N == 0,
		  "Only top level Associative Arrays are supported for now");
  }

  this(string name) {
    super(name);
  }

  CstArrLength!(RV) _arrLen;

  EV[] _elems;
  EV   _negIndexElem;

  abstract EV createElem(uint i, bool isMapped);
  abstract EV createElem(CstVecTerm index, bool isMapped);

  bool rand_mode() { return true; }
  // overridded in derived classes
  override bool isRand() { assert (false); }

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
    // writeln(this.fullName());
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

  void _esdl__doRandomize(_esdl__RandGen randGen) {
    if (isRand()) {
      assert (_arrLen !is null);
      // if there is no constraint on the length of the array,
      // do not try to randomize it, since it will probably create a
      // big array which might lead to memory allocation issues
      // buildElements(getLen());
      for (size_t i=0; i != arrLen.evaluate(); ++i) {
	_elems[i]._esdl__doRandomize(randGen);
      }
    }
    else {
      assert (false);
    }
  }

  // new EV(_name ~ "[#" ~ i.to!string() ~ "]",
  // 	 this, cast(uint) i);

  uint maxArrLen() {
    if (isRand()) {
      static if (isStaticArray!L) {
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

  CstArrLength!(RV) length() {
    return _arrLen;
  }

  CstArrLength!(RV) arrLen() {
    return _arrLen;
  }

  void markArrLen(size_t length) {
    buildElements(length);
    // import std.stdio;
    // writeln("buildElements: ", length);
    static if (is (EV: CstDomBase)) {
      _esdl__domsetUnresolvedArrLen = 0;
      _esdl__domsetLeafElemsCount = cast(uint) length;
      markResolved();
      execCbs();
    }
    else {
      _esdl__domsetUnresolvedArrLen = cast(uint) length;
      _esdl__domsetLeafElemsCount = 0;
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

  final CstVarNodeIntf _esdl__getChild(ulong n) {
    return this[cast(size_t) n];
  }

  final CstDomBase _esdl__nthLeaf(uint idx) {
    static if (is (EV: CstDomBase)) {
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

  override void setDomainArrContext(CstPredicate pred, DomainContextEnum context) {
    // assert (context == DomainContextEnum.DEFAULT);
    static if (RAND_ATTR.isRand()) {
      pred.addUnresolvedRndArr(this, context);
    }
    else {
      pred.addVarArr(this, context);
    }

    // Unless the array gets resolved, we can not solve the elements
    pred.addDep(this, context);
    pred.addDep(_arrLen, context);
  }

  final override void markAsUnresolved(uint lap, bool hier) {
    if (_unresolveLap != lap) {
      _unresolveLap = lap;
      CstDomSet parent = getParentDomSet();
      if (parent !is null)
	parent.markAsUnresolved(lap, false);
      foreach (pred; _unresolvedDomainPreds)
	pred.markAsUnresolved(lap);
      if (hier is true) {
	foreach (elem; _elems) {
	  static if (is (EV: CstDomSet))
	    elem.markAsUnresolved(lap, hier);
	  else 
	    elem.markAsUnresolved(lap);
	}
      }
    }
  }

  static if (HAS_RAND_ATTRIB) {
    CstVecPrim[] _preReqs;
  }

  override uint elemBitcount() {
    static if (isIntegral!LEAF) {
      return LEAF.sizeof * 8;
    }
    else static if(isBitVector!LEAF) {
      return cast(uint) LEAF.SIZE;
    }
    else static if(isBoolean!LEAF) {
      return 1;
    }
  }

  override bool elemSigned() {
    static if (isIntegral!LEAF) {
      return isSigned!LEAF;
    }
    else static if(isBitVector!LEAF) {
      return LEAF.ISSIGNED;
    }
    else static if(isBoolean!LEAF) {
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

  
}

// Primary Array
class CstVecArr(V, rand RAND_ATTR, int N) if (N == 0):
  CstVecArrBase!(V, RAND_ATTR, N)
    {
      V* _var;
      _esdl__Proxy _parent;
      bool _parentsDepsAreResolved;
    
      void _esdl__setValRef(V* var) {
	_var = var;
      }
      
      this(string name, _esdl__Proxy parent, V* var) {
	super(name);
	_var = var;
	_parent = parent;
	_root = _parent.getProxyRoot();
	_parentsDepsAreResolved = _parent.depsAreResolved();
	_arrLen = new CstArrLength!(RV) (name ~ "->length", this);
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent.isRand();
      }

      final override bool inRange() {
	return _parent.inRange();
      }

      final bool isRolled() {
	return _parent.isRolled();
      }

      final bool isStatic() {
	return _parent.isStatic(); 		// N == 0
      }

      final string fullName() {
	if (_parent is _root) return _name;
	else  
	  return _parent.fullName() ~ "." ~ name();
      }
      
      override bool depsAreResolved() {
	return _parentsDepsAreResolved;
      }

      override RV getResolvedNode() {
	return this;
      }

      override RV unroll(CstIterator iter, ulong n) {
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

      override EV createElem(uint i, bool isMapped) {
	return new EV(name(), this, i, isMapped);
      }

      override EV createElem(CstVecTerm index, bool isMapped) {
	return new EV(name(), this, index, isMapped);
      }

      override void markResolved() {
	// top level array -- no need to do anything
	// import std.stdio;
	// stdout.writeln("Array elements count: ", _esdl__domsetLeafElemsCount);
	// foreach (elem; this[]) {
	//   stdout.writeln(elem.name());
	// }
      }

      void markChildResolved(uint n) {
	assert (_esdl__domsetUnresolvedArrLen != 0 &&
		_esdl__domsetUnresolvedArrLen != uint.max);
	_esdl__domsetUnresolvedArrLen -= 1;
	_esdl__domsetLeafElemsCount += n;
	if (_esdl__domsetUnresolvedArrLen == 0) {
	  markResolved();
	  execCbs();
	}
      }

      override CstDomSet getParentDomSet() {
	return null;
      }
      
      override void markOrderedAfter(uint level) {
	super.markOrderedAfter(level);
	for (size_t i=0; i != getLen(); ++i) {
	  if (_elems[i].getOrder() != SolveOrder.NOW) {
	    _elems[i].markOrderedAfter(level);
	  }
	}
      }
    }

// Array that is elelment of another array
class CstVecArr(V, rand RAND_ATTR, int N) if (N != 0):
  CstVecArrBase!(V, RAND_ATTR, N), CstVecIndexed
    {
      alias P = CstVecArr!(V, RAND_ATTR, N-1);
      P _parent;

      bool _parentsDepsAreResolved;

      CstVecTerm _indexExpr = null;
      ulong _pindex = 0;
      immutable bool _nodeIsMapped = false;

      uint _resolvedCycle;	// cycle for which indexExpr has been resolved
      RV _resolvedVec;

      this(string name, P parent, CstVecTerm indexExpr, bool isMapped) {
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	super(name ~ "[#" ~ indexExpr.describe() ~ "]");
	_nodeIsMapped = isMapped;
	_parent = parent;
	_indexExpr = indexExpr;
	_root = _parent.getProxyRoot();
	_parentsDepsAreResolved = _parent.depsAreResolved();
	_arrLen = new CstArrLength!(RV) (name ~ "->length", this);
	if (_parent._unresolvedDomainPreds.length > 0 ||
	    _parent._esdl__parentIsConstrained) {
	  _esdl__parentIsConstrained = true;
	}
      }

      this(string name, P parent, ulong index, bool isMapped) {
	import std.conv: to;
	// import std.stdio;
	// writeln("New ", name);
	assert (parent !is null);
	super(name  ~ "[#" ~ index.to!string() ~ "]");
	_nodeIsMapped = isMapped;
	_parent = parent;
	_pindex = index;
	_root = _parent.getProxyRoot();
	_parentsDepsAreResolved = _parent.depsAreResolved();
	_arrLen = new CstArrLength!(RV) (name ~ "->length", this);
	if (_parent._unresolvedDomainPreds.length > 0 ||
	    _parent._esdl__parentIsConstrained) {
	  _esdl__parentIsConstrained = true;
	}
      }

      final override bool isRand() {
	return HAS_RAND_ATTRIB && rand_mode() && _parent.isRand();
      }

      final override bool inRange() {
	if (_indexExpr !is null) assert (false, "Unresolved Index");
	else {
	  // import std.stdio;
	  // writeln("inRange: ", name(), " - ", _pindex);
	  return _parent.inRange() && _parent.inRangeIndex(_pindex);
	}
      }

      override bool opEquals(Object other) {
	auto rhs = cast (RV) other;
	if (rhs is null) return false;
	else {
	  if (_indexExpr is null) {
	    if (rhs._indexExpr !is null) return false;
	    else return (_parent == rhs._parent && _pindex == rhs._pindex);
	  }
	  else {
	    if (rhs._indexExpr is null) return false;
	    else return (_parent == rhs._parent && _indexExpr == rhs._indexExpr);
	  }
	}
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
      
      override bool depsAreResolved() {
	return _parentsDepsAreResolved && _nodeIsMapped;
      }

      override RV getResolvedNode() {
	if (_resolvedCycle != getProxyRoot()._cycle) {
	  auto parent = _parent.getResolvedNode();
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

      override RV unroll(CstIterator iter, ulong n) {
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

      void setDomainContext(CstPredicate pred, DomainContextEnum context) {
	// arrlen should not be handled here. It is handled as part
	// of the indexExpr in the elements when required (that is
	// when indexExpr is not contant, but an expression)
	  
	// auto iter = arrLen.makeIterVar();
	// iters ~= iter;

	if (_parent.isStatic()) {
	  auto len = _parent._arrLen;
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

      override EV createElem(uint i, bool isMapped) {
	return new EV(name(), this, i, isMapped);
      }

      override EV createElem(CstVecTerm index, bool isMapped) {
	return new EV(name(), this, index, isMapped);
      }

      override void markResolved() {
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
	  markResolved();
	  execCbs();
	}
      }

      override CstDomSet getParentDomSet() {
	return _parent;
      }
      
      override void markOrderedAfter(uint level) {
	super.markOrderedAfter(level);
	for (size_t i=0; i != getLen(); ++i) {
	  if (_elems[i].getOrder() != SolveOrder.NOW) {
	    _elems[i].markOrderedAfter(level);
	  }
	}
      }
    }

private auto getArrElemTmpl(A, N...)(ref A arr, N indx)
  if ((isArray!A || isQueue!A || isAssociativeArray!A) &&
      N.length > 0 && isIntegral!(N[0])) {
    static if (isAssociativeArray!A) {
      if (indx[0] < arr.keys.length) {
	auto key = arr.keys[cast(size_t) (indx[0])];
	static if (N.length == 1) {
	  return &(arr[key]);
	}
	else {
	  return getArrElemTmpl(arr[key], indx[1..$]);
	}
      }
      else {
	assert (false, "Range violation");
      }
      
    }
    else {
      size_t key = cast(size_t) (indx[0]);
      if (key < arr.length) {
	static if (N.length == 1) {
	  return &(arr[key]);
	}
	else {
	  return getArrElemTmpl(arr[key], indx[1..$]);
	}
      }
      else {
	import std.stdio;
	writeln ("length: ", arr.length, " index: ", key);
	assert (false, "Range violation");
      }
    }
  }

private auto getRefTmpl(RV, J...)(RV rv, J indx)
  if (is (RV: CstDomSet) && isIntegral!(J[0])) {
    static if (is (RV: CstVecIndexed)) {
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

size_t getLenTmpl(RV, N...)(RV rv, N indx) {
  static if (is (RV: CstVecIndexed)) {
    return getLenTmpl(rv._parent, rv._pindex, indx);
  }
  else {
    return getArrLenTmpl(*(rv._var), indx);
  }
}

private void setArrLen(A, N...)(ref A arr, size_t v, N indx)
  if (isArray!A || isQueue!A || isAssociativeArray!A) {
    static if (N.length == 0) {
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
  static if (is (RV: CstVecIndexed)) {
    setLenTmpl(rv._parent, v, rv._pindex, indx);
  }
  else {
    assert (rv._var !is null);
    setArrLen(*(rv._var), v, indx);
  }
}
