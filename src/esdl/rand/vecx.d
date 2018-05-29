module esdl.rand.vecx;

import esdl.data.bvec;
import esdl.data.bstr;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray, isDynamicArray;

import esdl.rand.obdd;
import esdl.rand.base;
import esdl.rand.expr: CstVarPrim, CstVarExpr, CstVarIterBase,
  CstStage, // CstValAllocator,
  CstVarLen, CstDomain, CstVecDomain, _esdl__cstVal;

// Consolidated Proxy Class
// template CstVecBase(T, int I, int N=0) {
//   alias CstVecBase = CstVecBase!(typeof(T.tupleof[I]),
// 				     getRandAttr!(T, I), N);
// }

abstract class CstVecBase(V, alias R, int N)
  if(_esdl__ArrOrder!(V, N) == 0): CstVecDomain!R, CstVarPrim
{
  enum HAS_RAND_ATTRIB = (! __traits(isSame, R, _esdl__norand));

  alias E = ElementTypeN!(V, N);
  alias RV = typeof(this);

  string _name;

  Unconst!E _refreshedVal;

  static if (HAS_RAND_ATTRIB) {
    CstVarPrim[] _preReqs;
  }

  this(string name) {
    _name = name;
  }

  static if(HAS_RAND_ATTRIB && is(E == enum)) {
    BDD _primBdd;
    BDD getPrimBdd(Buddy buddy) {
      import std.traits;
      if(_primBdd.isZero()) {
	foreach(e; EnumMembers!E) {
	  _primBdd = _primBdd | this.bddvec.equ(buddy.buildVec(e));
	}
      }
      return _primBdd;
    }
    void resetPrimeBdd() {
      _primBdd.reset();
    }
  }
  else {
    BDD getPrimBdd(Buddy buddy) {
      return buddy.one();
    }
    void resetPrimeBdd() { }
  }

  ~this() {
    resetPrimeBdd();
  }

  override string name() {
    return _name;
  }

  void _esdl__reset() {
    static if (HAS_RAND_ATTRIB) {
      _stage = null;
      _resolveLap = 0;
    }
  }

  bool isVarArr() {
    return false;
  }

  abstract ulong value();
  
  override long evaluate() {
    static if (HAS_RAND_ATTRIB) {
      if(! this.isRand || stage().solved()) {
	return value();
      }
      else {
	import std.conv;
	assert(false, "Rand variable " ~ _name ~
	       " evaluation in wrong stage: " ~ stage()._id.to!string);
      }
    }
    else {
      return value();
    }
  }

  uint bitcount() {
    static if(isBoolean!E)         return 1;
    else static if(isIntegral!E)   return E.sizeof * 8;
    else static if(isBitVector!E)  return E.SIZE;
    else static assert(false, "bitcount can not operate on: " ~ E.stringof);
  }

  bool signed() {
    static if(isVecSigned!E) {
      return true;
    }
    else  {
      return false;
    }
  }

  S to(S)()
    if (is(S == string)) {
      import std.conv;
      static if (HAS_RAND_ATTRIB) {
	if (isRand) {
	  return "RAND#" ~ _name ~ ":" ~ value().to!string();
	}
	else {
	  return "VAL#" ~ _name ~ ":" ~ value().to!string();
	}
      }
      else {
	return "VAR#" ~ _name ~ ":" ~ value().to!string();
      }
    }

  override string toString() {
    return this.to!string();
  }

  void solveBefore(CstVarPrim other) {
    static if (HAS_RAND_ATTRIB) {
      other.addPreRequisite(this);
    }
    else {
      assert(false);
    }
  }

  void addPreRequisite(CstVarPrim domain) {
    static if (HAS_RAND_ATTRIB) {
      _preReqs ~= domain;
    }
    else {
      assert(false);
    }
  }

  void build() {}

  abstract E* getRef();
  
  override bool isRand() {
    static if (HAS_RAND_ATTRIB) {
      return true;
    }
    else {
      return false;
    }
  }
}

// T represents the type of the declared array/non-array member
// N represents the level of the array-elements we have to traverse
// for the elements this CstVec represents
template CstVec(T, int I, int N=0)
  if(_esdl__ArrOrder!(T, I, N) == 0) {
  alias CstVec = CstVec!(typeof(T.tupleof[I]),
			 getRandAttr!(T, I), N);
}

class CstVec(V, alias R, int N) if(N == 0 && _esdl__ArrOrder!(V, N) == 0):
  CstVecBase!(V, R, N)
    {
      import std.traits;
      import std.range;
      import esdl.data.bvec;

      V* _var;

    
      this(string name, ref V var) {
	// import std.stdio;
	// writeln("New ", name);
	super(_name);
	_var = &var;
      }

      void _esdl__setValRef(ref V var) {
	_var = &var;
      }
      
      override CstVarPrim[] preReqs() {
	static if (HAS_RAND_ATTRIB) {
	  return _preReqs;
	}
	else {
	  return [];
	}
      }

      override CstVarIterBase[] itrVars() {
	return [];
      }

      override bool hasUnresolvedIdx() {
	return false;
      }
      
      override CstDomain[] getRndDomains() {
	static if (HAS_RAND_ATTRIB) {
	  if(isRand) return [this];
	  else return [];
	}
	else {
	  return [];
	}
      }

      CstDomain[] getDomainLens() {
	assert(false);
      }

      override RV unwind(CstVarIterBase itr, uint n) {
	// itrVars is always empty
	return this;
      }

      void _esdl__doRandomize(_esdl__RandGen randGen) {
	static if (HAS_RAND_ATTRIB) {
	  if(stage is null) {
	    randGen.gen(*_var);
	  }
	}
	else {
	  assert(false);
	}
      }

      override E* getRef() {
	return _var;
      }

      override ulong value() {
	return cast(long) (*_var);
      }

      override bool refresh(CstStage s, Buddy buddy) {
	static if (HAS_RAND_ATTRIB) {
	  assert (stage(), "Stage not set for " ~ this.name());
	  if (this.isRand && s is stage()) {
	    return false;
	  }
	  else if ((! this.isRand) ||
		   this.isRand && stage().solved()) { // work with the value
	    return refreshVal(buddy);
	  }
	  else {
	    assert(false, "Constraint evaluation in wrong stage");
	  }
	}
	else {
	  return refreshVal(buddy);
	}
      }
  
      private bool refreshVal(Buddy buddy) {
	auto val = *(getRef());
	if (_valvec.isNull ||
	    val != _refreshedVal) {
	  _valvec.buildVec(buddy, val);
	  _refreshedVal = val;
	  return true;
	}
	else {
	  return false;
	}
      }
  
      override BddVec getBDD(CstStage s, Buddy buddy) {
	static if (HAS_RAND_ATTRIB) {
	  assert(stage(), "Stage not set for " ~ this.name());
	  if(this.isRand && s is stage()) {
	    return _domvec;
	  }
	  else if((! this.isRand) ||
		  this.isRand && stage().solved()) { // work with the value
	    return _valvec;
	  }
	  else {
	    assert(false, "Constraint evaluation in wrong stage");
	  }
	}
	else {
	  return _valvec;
	}
      }

      void collate(ulong v, int word = 0) {
	static if (HAS_RAND_ATTRIB) {
	  static if(isIntegral!V || isBoolean!V) {
	    if(word == 0) {
	      *_var = cast(V) v; // = cast(V) toBitVec(v      }
	    }
	    else {
	      static if(size_t.sizeof == 4 && (is(V == long) || is(V == ulong))) {
		assert(word == 1);	// 32 bit machine with long integral
		V val = v;
		val = val << (8 * size_t.sizeof);
		*_var += val;
	      }
	      else {
		assert(false, "word has to be 0 for integrals");
	      }
	    }
	  }
	  else {
	    _var._setNthWord(v, word); // = cast(V) toBitVec(v);
	  }
	}
	else {
	  assert(false);
	}
      }

      override bool isConst() {
	return false;
      }

      override bool isOrderingExpr() {
	return false;		// only CstVecOrderingExpr return true
      }
    }

class CstVec(V, alias R, int N=0) if(N != 0 && _esdl__ArrOrder!(V, N) == 0):
  CstVecBase!(V, R, N)
    {
      import std.traits;
      import std.range;
      import esdl.data.bvec;

      alias RV = typeof(this);
      alias P = CstVecArr!(V, R, N-1);
      P _parent;

      CstVarExpr _indexExpr = null;
      int _pindex = 0;

      this(string name, P parent, CstVarExpr indexExpr) {
	assert(parent !is null);
	super(name);
	_parent = parent;
	_indexExpr = indexExpr;
      }

      this(string name, P parent, uint index) {
	assert(parent !is null);
	super(name);
	_parent = parent;
	// _indexExpr = _esdl__cstVal(index);
	_pindex = index;
      }

      override CstVarPrim[] preReqs() {
	if(_indexExpr) {
	  static if (HAS_RAND_ATTRIB) {
	    return _preReqs ~ _parent.arrLen() ~
	      _parent.preReqs() ~ _indexExpr.preReqs();
	  }
	  else {
	    return _parent.preReqs() ~ _indexExpr.preReqs();
	  }
	}
	else {
	  static if (HAS_RAND_ATTRIB) {
	    return _preReqs ~ _parent.arrLen() ~ _parent.preReqs();
	  }
	  else {
	    return _parent.preReqs();
	  }
	}
      }

      override CstVarIterBase[] itrVars() {
	if(_indexExpr) {
	  return _parent.itrVars() ~ _indexExpr.itrVars();
	}
	else {
	  return _parent.itrVars();
	}
      }

      override bool hasUnresolvedIdx() {
	return _parent.hasUnresolvedIdx(); // no _relatedIdxs for this instance
      }
      
      CstDomain[] getDomainLens() {
	assert(false);
      }

      // What is required here
      // we could be dealing with an _pindex or an _indexExpr. Further
      // the indexExpr could be either a solvable constraint expression
      // or an array length iterator that iterates over the length of
      // the given array. To add to the complexity here, we could have a
      // case where the given element has a parent that too a
      // non-elementary one (involving non-integer indexes). In such
      // cases we need to list all the elements of the array that could
      // finally represent the given element that we are currently
      // dealing with.
      override CstDomain[] getRndDomains() {
	CstDomain[] domains;
	static if (HAS_RAND_ATTRIB) {
	  if (_indexExpr) {
	    if (_indexExpr.isConst()) {
	      // domains = cast (CstDomain[]) _parent.getDomainElems(_indexExpr.evaluate());
	      foreach(pp; _parent.getDomainElems(_indexExpr.evaluate())) {
		domains ~= pp;
	      }
	    }
	    else {
	      // FIXME -- if the expression has been solved
	      // return _parent.getRndDomains(_indexExpr.evaluate()) ;
	      domains = _indexExpr.getRndDomains();
	      foreach(pp; _parent.getDomainElems(-1)) {
		domains ~= pp;
	      }
	      // domains ~= _parent.getDomainElems(-1);
	    }
	  }
	  else {
	    foreach(pp; _parent.getDomainElems(_pindex)) {
	      domains ~= pp;
	    }
	    // domains =  cast (CstDomain[]) _parent.getDomainElems(_pindex);
	  }
	  return domains;
	}
	else {
	  if(_indexExpr) {
	    // FIXME -- if the expression has been solved
	    // return _parent.getDomainElems(_indexExpr.evaluate()) ;
	    domains = _indexExpr.getRndDomains() ~ _parent.getRndDomains();
	  }
	  else {
	    // foreach(pp; _parent.getDomainElems(_pindex)) {
	    //   domains ~= pp;
	    // }
	    domains = _parent.getRndDomains();
	  }
	  return domains;
	}
      }

      override RV unwind(CstVarIterBase itr, uint n) {
	bool found = false;
	foreach(var; itrVars()) {
	  if(itr is var) {
	    found = true;
	    break;
	  }
	}
	if(! found) {		// itr is unrelated
	  return this;
	}
	else if(_indexExpr) {
	  return _parent.unwind(itr,n)[_indexExpr.unwind(itr,n)];
	}
	else {
	  return _parent.unwind(itr,n)[_pindex];
	}
      }

      void _esdl__doRandomize(_esdl__RandGen randGen) {
	static if (HAS_RAND_ATTRIB) {
	  if(stage is null) {
	    E val;
	    randGen.gen(val);
	    collate(val);
	  }
	}
	else {
	  assert(false, name());
	}
      }

      override E* getRef() {
	if(_indexExpr) {
	  return _parent.getRef(cast(size_t) _indexExpr.evaluate());
	}
	else {
	  return _parent.getRef(this._pindex);
	}
      }

      override ulong value() {
	if(_indexExpr) {
	  return *(_parent.getRef(_indexExpr.evaluate()));
	}
	else {
	  return *(_parent.getRef(this._pindex));
	}
      }

      RV flatten() {
	if (_indexExpr !is null) {
	  return _parent.flatten()[_indexExpr.evaluate()];
	}
	else {
	  return this;
	}
      }

      override bool refresh(CstStage s, Buddy buddy) {
	static if (HAS_RAND_ATTRIB) {
	  if (_indexExpr !is null) {
	    return flatten().refresh(s, buddy);
	  }
	  else {
	    assert(stage(), "Stage not set for " ~ this.name());
	    if(this.isRand && s is stage()) {
	      return false;
	    }
	    else if((! this.isRand) ||
		    this.isRand && stage().solved()) { // work with the value
	      return refreshVal(buddy);
	    }
	    else {
	      assert(false, "Constraint evaluation in wrong stage");
	    }
	  }
	}
	else {
	  return refreshVal(buddy);
	}
      }
  
      private bool refreshVal(Buddy buddy) {
	auto val = *(getRef());
	if (_valvec.isNull ||
	    val != _refreshedVal) {
	  _valvec.buildVec(buddy, val);
	  _refreshedVal = val;
	  return true;
	}
	else {
	  return false;
	}
      }
  
      override BddVec getBDD(CstStage s, Buddy buddy) {
	static if (HAS_RAND_ATTRIB) {
	  if (_indexExpr !is null) {
	    auto dvec = _parent[_indexExpr.evaluate()];
	    return dvec.getBDD(s, buddy);
	  }
	  else {
	    assert(stage(), "Stage not set for " ~ this.name());
	    if(this.isRand && s is stage()) {
	      return _domvec;
	    }
	    else if((! this.isRand) ||
		    this.isRand && stage().solved()) { // work with the value
	      return _valvec;
	    }
	    else {
	      assert(false, "Constraint evaluation in wrong stage");
	    }
	  }
	}
	else {
	  return _valvec;
	}
      }

      void collate(ulong v, int word = 0) {
	static if (HAS_RAND_ATTRIB) {
	  E* var = getRef();
	  static if(isIntegral!E) {
	    if(word == 0) {
	      *var = cast(E) v;
	    }
	    else {
	      assert(false, "word has to be 0 for integrals");
	    }
	  }
	  else {
	    (*var)._setNthWord(v, word);
	  }
	}
	else {
	  assert(false);
	}
      }

      override bool isConst() {
	return false;
      }

      override bool isOrderingExpr() {
	return false;		// only CstVecOrderingExpr return true
      }
    }

// Arrays (Multidimensional arrays as well)
// template CstVecArrBase(T, int I, int N=0)
//   if(_esdl__ArrOrder!(T, I, N) != 0) {
//   alias CstVecArrBase = CstVecArrBase!(typeof(T.tupleof[I]),
// 					   getRandAttr!(T, I), N);
// }

abstract class CstVecArrBase(V, alias R, int N=0)
  if(_esdl__ArrOrder!(V, N) != 0): CstVarPrim
{
  enum HAS_RAND_ATTRIB = (! __traits(isSame, R, _esdl__norand));

  alias L = ElementTypeN!(V, N);
  alias E = ElementTypeN!(V, N+1);

  static if (_esdl__ArrOrder!(V, N+1) == 0) {
    alias EV = CstVec!(V, R, N+1);
  }
  else {
    alias EV = CstVecArr!(V, R, N+1);
  }

  EV[] _elems;

  string _name;
  override string name() {
    return _name;
  }

  size_t maxArrLen() {
    static if (HAS_RAND_ATTRIB) {
      static if(isStaticArray!L) {
	return L.length;
      }
      else {
	return getRandAttrN!(R, N);
      }
    }
    else {
      return L.length;
    }
  }

  static if (HAS_RAND_ATTRIB) {
    CstVarPrim[] _preReqs;
  }

  bool isVarArr() {
    return true;
  }

  BDD getPrimBdd(Buddy buddy) {
    return buddy.one();
  }

  void resetPrimeBdd() { }

  // override CstVec2VecExpr opIndex(CstVarExpr idx) {
  //   return new CstVec2VecExpr(this, idx, CstBinVecOp.IDXINDEX);
  // }

  bool isRand() {
    assert(false, "isRand not implemented for CstVecArrBase");
  }

  ulong value() {
    assert(false, "value not implemented for CstVecArrBase");
  }

  void collate(ulong v, int word = 0) {
    assert(false, "value not implemented for CstVecArrBase");
  }

  void stage(CstStage s) {
    assert(false, "stage not implemented for CstVecArrBase");
  }

  uint domIndex() {
    assert(false, "domIndex not implemented for CstVecArrBase");
  }

  void domIndex(uint s) {
    assert(false, "domIndex not implemented for CstVecArrBase");
  }

  uint bitcount() {
    assert(false, "bitcount not implemented for CstVecArrBase");
  }

  bool signed() {
    assert(false, "signed not implemented for CstVecArrBase");
  }

  ref BddVec bddvec() {
    assert(false, "bddvec not implemented for CstVecArrBase");
  }

  void bddvec(BddVec b) {
    assert(false, "bddvec not implemented for CstVecArrBase");
  }

  void solveBefore(CstVarPrim other) {
    static if (HAS_RAND_ATTRIB) {
      other.addPreRequisite(this);
    }
    else {
      assert(false);
    }
  }

  void addPreRequisite(CstVarPrim prim) {
    static if (HAS_RAND_ATTRIB) {
      _preReqs ~= prim;
    }
    else {
      assert(false);
    }
  }

}

template CstVecArr(T, int I, int N=0)
  if(_esdl__ArrOrder!(T, I, N) != 0) {
  alias CstVecArr = CstVecArr!(typeof(T.tupleof[I]),
			       getRandAttr!(T, I), N);
}

// Arrays (Multidimensional arrays as well)
class CstVecArr(V, alias R, int N=0)
  if(N == 0 && _esdl__ArrOrder!(V, N) != 0):
    CstVecArrBase!(V, R, N)
      {
	alias RV = typeof(this);
	CstVarLen!RV _arrLen;

	alias RAND=R;

	V* _var;

	void _esdl__setValRef(ref V var) {
	  _var = &var;
	}
      
	static if (HAS_RAND_ATTRIB) {
	  static if(isStaticArray!V) {
	    static assert(__traits(isSame, R, rand));
	    enum int maxLen = V.length;
	    this(string name, ref V var) {
	      _name = name;
	      _var = &var;
	      _arrLen = new CstVarLen!RV(name ~ ".len", this);
	      _relatedIdxs ~= _arrLen;
	    }
	  }

	  static if(isDynamicArray!V) {
	    enum int maxLen = getRandAttrN!(R, N);
	    this(string name, ref V var) {
	      _name = name;
	      _var = &var;
	      _arrLen = new CstVarLen!RV(name ~ ".len", this);
	      _relatedIdxs ~= _arrLen;
	    }
	  }
	}
	else {
	  this(string name, ref V var) {
	    _name = name;
	    _var = &var;
	    _arrLen = new CstVarLen!RV(name ~ ".len", this);
	    _relatedIdxs ~= _arrLen;
	  }
	}

	CstVarPrim[] preReqs() {
	  static if (HAS_RAND_ATTRIB) {
	    return _preReqs;		// N = 0 -- no _parent
	  }
	  else {
	    return [];
	  }
	}

	CstVarIterBase[] itrVars() {
	  return [];		// N = 0 -- no _parent
	}

	static if (HAS_RAND_ATTRIB) {
	  EV[] getDomainElems(long idx) {
	    build();
	    if(idx < 0) return _elems;
	    else return [_elems[idx]];
	  }
	}

	// CstDomain[] getRndDomains() {
	//   static if (false) {	// This function can only be there for leaf nodes
	//     static if (HAS_RAND_ATTRIB) {
	//       CstDomain[] domains;
	//       foreach(elem; _elems) {
	// 	domains ~= elem;
	//       }
	//       return domains;
	//     }
	//     else {
	//       return [];
	//     }
	//   }
	//   else {
	//     assert(false);
	//   }
	// }

	CstDomain[] getDomainLens() {
	  static if (HAS_RAND_ATTRIB) {
	    CstDomain[] domains;
	    if(_arrLen.isRand) domains ~= _arrLen;
	    return domains;
	  }
	  else {
	    return [];
	  }
	}
    
	RV unwind(CstVarIterBase itr, uint n) {
	  return this;
	}

	RV flatten() {
	  return this;
	}

	bool parentLenIsUnresolved() {
	  return false;		// no parent
	}

	bool hasUnresolvedIdx() {
	  foreach (domain; _relatedIdxs) {
	    if (! domain.solved()) {
	      return true;
	    }
	  }
	  return false;		// N=0 -- no _parent
	}
      
	static private auto getRef(A, N...)(ref A arr, N idx)
	  if(isArray!A && N.length > 0 && isIntegral!(N[0])) {
	    static if(N.length == 1) return &(arr[idx[0]]);
	    else {
	      return getRef(arr[idx[0]], idx[1..$]);
	    }
	  }

	auto getRef(J...)(J idx) if(isIntegral!(J[0])) {
	  return getRef(*_var, cast(size_t) idx);
	}

	static if (HAS_RAND_ATTRIB) {

	  static private void setLen(A, N...)(ref A arr, size_t v, N idx)
	    if(isArray!A) {
	      static if(N.length == 0) {
		static if(isDynamicArray!A) {
		  arr.length = v;
		  // import std.stdio;
		  // writeln(arr, " idx: ", N.length);
		}
		else {
		  assert(false, "Can not set length of a fixed length array");
		}
	      }
	      else {
		// import std.stdio;
		// writeln(arr, " idx: ", N.length);
		setLen(arr[idx[0]], v, idx[1..$]);
	      }
	    }
	}
	else {
	  void setLen(N...)(size_t v, N idx) {
	    // setLen(*_var, v, idx);
	    assert(false, "Can not set value for VarVecArr");
	  }
	}

	static private size_t getLen(A, N...)(ref A arr, N idx) if(isArray!A) {
	  static if(N.length == 0) return arr.length;
	  else {
	    return getLen(arr[idx[0]], idx[1..$]);
	  }
	}

	size_t getLen(N...)(N idx) {
	  return getLen(*_var, idx);
	}

	void setLen(N...)(size_t v, N idx) {
	  static if (HAS_RAND_ATTRIB) {
	    setLen(*_var, v, idx);
	  }
	  else {
	    assert(false);
	  }
	}

	bool isUnwindable() {
	  foreach (var; _relatedIdxs) {
	    if (! var.solved()) return false;
	  }
	  return true;
	}

	CstDomain[] _relatedIdxs;
	void addRelatedIdx(CstDomain domain) {
	  foreach (var; _relatedIdxs) {
	    if (domain is var) {
	      return;
	    }
	  }
	  _relatedIdxs ~= domain;
	}
      
	EV opIndex(CstVarExpr idx) {
	  foreach (domain; idx.getRndDomains()) {
	    addRelatedIdx(domain);
	  }
	  if(idx.isConst() && _arrLen.solved()) {
	    // resolve only if the length has been resolved yet
	    // And when the length is reolved, we must make sure that
	    // unwinding of iterator takes care of such elements as
	    // well which are not explicitly onvoking iterators
	    assert(_elems.length > 0, "_elems for expr " ~ this.name() ~
		   " have not been built");
	    return _elems[cast(size_t) idx.evaluate()];
	  }
	  else {
	    // static if(isStaticArray!E) {
	    //   // static array
	    return new EV(name ~ "[" ~ idx.name() ~ "]", this, idx);
	    // }
	    // else static if(isDynamicArray!E) {
	    //   // dynamic array
	    //   return new EV(name ~ "[" ~ idx.name() ~ "]", this, idx);
	    // }
	    // else {
	    //   return new EV(name ~ "[" ~ idx.name() ~ "]", this, idx);
	    // }
	  }
	}

	EV opIndex(size_t idx) {
	  build();
	  assert(_elems[idx]._indexExpr is null);
	  return _elems[idx];
	}

	void _esdl__doRandomize(_esdl__RandGen randGen) {
	  static if (HAS_RAND_ATTRIB) {
	    if(_elems.length == 0) this.build();
	    assert(arrLen !is null);
	    for(size_t i=0; i != arrLen.evaluate(); ++i) {
	      this[i]._esdl__doRandomize(randGen);
	    }
	  }
	  else {
	    assert(false);
	  }
	}

	auto elements() {
	  this.build();
	  auto itr = arrLen.makeItrVar();
	  return this[itr];
	}

	bool built() {
	  return (_elems.length == maxArrLen() &&
		  _elems[0] !is null);
	}
    
	void build() {
	  if(built()) return;
	  _elems.length = maxArrLen();
	  // static if(isIntegral!E || isBitVector!E) {
	  // if(! built()) {
	  for (uint i=0; i!=maxArrLen; ++i) {
	    if(_elems[i] is null) {
	      import std.conv: to;
	      _elems[i] = new EV(_name ~ "[#" ~ i.to!string() ~ "]", this, i);
	      if(_elems[i].isVarArr()) {
		_elems[i].build();
	      }
	    }
	  }
	}
	
	auto iterator() {
	  this.build();
	  auto itr = arrLen.makeItrVar();
	  return itr;
	}

	CstVarLen!RV length() {
	  return _arrLen;
	}

	CstVarLen!RV arrLen() {
	  return _arrLen;
	}

	void _esdl__reset() {
	  _arrLen._esdl__reset();
	  foreach(elem; _elems) {
	    if(elem !is null) {
	      elem._esdl__reset();
	    }
	  }
	}

	CstStage stage() {
	  assert(false);
	}

      }

class CstVecArr(V, alias R, int N=0)
  if(N != 0 && _esdl__ArrOrder!(V, N) != 0):
    CstVecArrBase!(V, R, N)
      {
	import std.traits;
	import std.range;
	import esdl.data.bvec;
	alias P = CstVecArr!(V, R, N-1);
	P _parent;
	CstVarExpr _indexExpr = null;
	int _pindex = 0;

	alias RV = typeof(this);
	CstVarLen!RV _arrLen;

	alias RAND=R;
      
	this(string name, P parent, CstVarExpr indexExpr) {
	  assert(parent !is null);
	  _name = name;
	  _parent = parent;
	  _indexExpr = indexExpr;
	  _arrLen = new CstVarLen!RV(name ~ ".len", this);
	  _relatedIdxs ~= _arrLen;
	}

	this(string name, P parent, uint index) {
	  assert(parent !is null);
	  _name = name;
	  _parent = parent;
	  // _indexExpr = _esdl__cstVal(index);
	  _pindex = index;
	  _arrLen = new CstVarLen!RV(name ~ ".len", this);
	  _relatedIdxs ~= _arrLen;
	}

	CstVarPrim[] preReqs() {
	  CstVarPrim[] req;
	  static if (HAS_RAND_ATTRIB) {
	    req = _preReqs ~ _parent.arrLen();
	  }
	  if(_indexExpr) {
	    return req ~ _indexExpr.preReqs() ~ _parent.preReqs();
	  }
	  else {
	    return req ~ _parent.preReqs();
	  }
	}

	CstVarIterBase[] itrVars() {
	  if(_indexExpr) {
	    return _parent.itrVars() ~ _indexExpr.itrVars(); // ~ _arrLen.makeItrVar();
	  }
	  else {
	    return _parent.itrVars();
	  }
	}

	bool parentLenIsUnresolved() {
	  return (! _parent._arrLen.solved());
	}

	bool hasUnresolvedIdx() {
	  foreach (domain; _relatedIdxs) {
	    if (! domain.solved()) {
	      return true;
	    }
	  }
	  return _parent.hasUnresolvedIdx();
	}

	EV[] getDomainElems(long idx) {
	  EV[] elems;
	  static if (HAS_RAND_ATTRIB) {
	    if(_indexExpr) {
	      foreach(pp; _parent.getDomainElems(-1)) {
		if(idx < 0) elems ~= pp._elems;
		else elems ~= pp._elems[idx];
	      }
	    }
	    else {
	      foreach(pp; _parent.getDomainElems(_pindex)) {
		if(idx < 0) elems ~= pp._elems;
		else elems ~= pp._elems[idx];
	      }
	    }
	  }
	  return elems;
	}
    
	// This is slightly tricky in case we are pointing directly to
	// just one element of the array, this function should return just
	// that element. But it could be that the index or an upper
	// hierarchy index is not a constant, but an iterator or a
	// randomized epression. In that case, we shall have to return
	// more primary elements
	// CstDomain[] getRndDomains() {
	// 	CstDomain[] domains;
	// 	static if (HAS_RAND_ATTRIB) {
	// 	  if(_indexExpr) {
	// 	    domains = _indexExpr.getRndDomains();
	// 	    foreach(pp; _parent.getDomainElems(-1)) {
	// 	      domains ~= pp;
	// 	    }
	// 	  }
	// 	  else {
	// 	    foreach(pp; _parent.getDomainElems(_pindex)) {
	// 	      domains ~= pp;
	// 	    }
	// 	  }
	// 	}
	// 	else {
	// 	  domains ~= _parent.getDomainLens();
	// 	  if(_indexExpr) {
	// 	    domains ~= _indexExpr.getRndDomains() ~ _parent.getDomainLens();
	// 	  }
	// 	}
	// 	return domains;
	// }

	CstDomain[] getDomainLens() {
	  // if(_pindex.itrVars.length is 0)
	  if(_indexExpr is null) {
	    return [_parent[_pindex].arrLen()];
	    // return domains ~ _parent[_pindex].getDomainLens();
	  }
	  if(_indexExpr.isConst()) {
	    CstDomain[] domains;
	    domains ~= _parent[cast(size_t) _indexExpr.evaluate()].getDomainLens();
	    return domains;
	  }
	  else {
	    CstDomain[] domains;
	    // import std.stdio;
	    // writeln(_parent.name(), " ", p.name());
	    domains = _indexExpr.getRndDomains();
	    foreach(pp; _parent.getDomainElems(-1)) {
	      domains ~= pp.getDomainLens();
	    }
	    return domains;
	  }
	}

	RV flatten() {
	  if (_indexExpr !is null) {
	    return _parent.flatten()[_indexExpr.evaluate()];
	  }
	  else {
	    return this;
	  }
	}

	RV unwind(CstVarIterBase itr, uint n) {
	  bool found = false;
	  foreach(var; itrVars()) {
	    if(itr is var) {
	      found = true;
	      break;
	    }
	  }
	  if(! found) {
	    return this;
	  }
	  else if(_indexExpr) {
	    return _parent.unwind(itr,n)[_indexExpr.unwind(itr,n)];
	  }
	  else {
	    return _parent.unwind(itr,n)[_pindex];
	  }
	}

	static private size_t getLen(A, N...)(ref A arr, N idx) if(isArray!A) {
	  static if(N.length == 0) return arr.length;
	  else {
	    return getLen(arr[idx[0]], idx[1..$]);
	  }
	}

	static if (HAS_RAND_ATTRIB) {
	  static private void setLen(A, N...)(ref A arr, size_t v, N idx)
	    if(isArray!A) {
	      static if(N.length == 0) {
		static if(isDynamicArray!A) {
		  arr.length = v;
		  // import std.stdio;
		  // writeln(arr, " idx: ", N.length);
		}
		else {
		  assert(false, "Can not set length of a fixed length array");
		}
	      }
	      else {
		// import std.stdio;
		// writeln(arr, " idx: ", N.length);
		setLen(arr[idx[0]], v, idx[1..$]);
	      }
	    }

	  void setLen(N...)(size_t v, N idx) {
	    _parent.setLen(v, _pindex, idx);
	  }
	}

	size_t getLen(N...)(N idx) {
	  return _parent.getLen(_pindex, idx);
	}

	static private auto getRef(A, N...)(ref A arr, N idx)
	  if(isArray!A && N.length > 0 && isIntegral!(N[0])) {
	    static if(N.length == 1) return &(arr[idx[0]]);
	    else {
	      return getRef(arr[idx[0]], idx[1..$]);
	    }
	  }

	auto getRef(N...)(N idx) if(isIntegral!(N[0])) {
	  if(_indexExpr) {
	    assert(_indexExpr.isConst());
	    return _parent.getRef(cast(size_t) _indexExpr.evaluate(), idx);
	  }
	  else {
	    return _parent.getRef(this._pindex, idx);
	  }
	}

	bool isUnwindable() {
	  foreach (var; _relatedIdxs) {
	    if (! var.solved()) return false;
	  }
	  return true;
	}

	CstDomain[] _relatedIdxs;
	void addRelatedIdx(CstDomain domain) {
	  foreach (var; _relatedIdxs) {
	    if (domain is var) {
	      return;
	    }
	  }
	  _relatedIdxs ~= domain;
	}
      
	EV opIndex(CstVarExpr idx) {
	  foreach (domain; idx.getRndDomains()) {
	    addRelatedIdx(domain);
	  }
	  if(idx.isConst()) {
	    assert(_elems.length > 0, "_elems for expr " ~ this.name() ~
		   " have not been built");
	    // if(idx.evaluate() >= _elems.length || idx.evaluate() < 0 || _elems is null) {
	    // 	import std.stdio;
	    // 	writeln(this.name(), ":", idx.evaluate());
	    // }
	    // import std.stdio;
	    // writeln(idx.evaluate());
	    return _elems[cast(size_t) idx.evaluate()];
	  }
	  else {
	    // static if(isStaticArray!E) {
	    //   // static array
	    return new EV(name ~ "[" ~ idx.name() ~ "]", this, idx);
	    // }
	    // else static if(isDynamicArray!E) {
	    //   // dynamic array
	    //   return new EV(name ~ "[" ~ idx.name() ~ "]", this, idx);
	    // }
	    // else {
	    //   return new EV(name ~ "[" ~ idx.name() ~ "]", this, idx);
	    // }
	  }
	}

	EV opIndex(size_t idx) {
	  build();
	  assert(_elems[idx]._indexExpr is null);
	  return _elems[idx];
	}

	void _esdl__doRandomize(_esdl__RandGen randGen) {
	  static if (HAS_RAND_ATTRIB) {
	    if(_elems.length == 0) this.build();
	    assert(arrLen !is null);
	    for(size_t i=0; i != arrLen.evaluate(); ++i) {
	      this[i]._esdl__doRandomize(randGen);
	    }
	  }
	  else {
	    assert(false);
	  }
	}

	auto elements() {
	  this.build();
	  auto idx = arrLen.makeItrVar();
	  return this[idx];
	}

	bool built() {
	  return (_elems.length == maxArrLen() &&
		  _elems[0] !is null);
	}
    
	void build() {
	  if(built()) return;
	  _elems.length = maxArrLen();
	  // static if(isIntegral!E || isBitVector!E) {
	  // if(! built()) {
	  for (uint i=0; i!=maxArrLen; ++i) {
	    if(_elems[i] is null) {
	      import std.conv: to;
	      _elems[i] = new EV(_name ~ "[#" ~ i.to!string() ~ "]", this, i);
	      if(_elems[i].isVarArr()) {
		_elems[i].build();
	      }
	    }
	  }
	}
	
	auto iterator() {
	  this.build();
	  auto itr = arrLen.makeItrVar();
	  return itr;
	}

	CstVarLen!RV length() {
	  return _arrLen;
	}

	CstVarLen!RV arrLen() {
	  return _arrLen;
	}

	void _esdl__reset() {
	  _arrLen._esdl__reset();
	  foreach(elem; _elems) {
	    if(elem !is null) {
	      elem._esdl__reset();
	    }
	  }
	}

	CstStage stage() {
	  assert(false);
	}

      }
