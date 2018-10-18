module esdl.rand.expr;

import esdl.rand.intr;
import esdl.rand.obdd;
import esdl.rand.misc: _esdl__RandGen, _esdl__norand, isVecSigned, Unconst;
import esdl.rand.misc: CstBinVecOp, CstBinBddOp, CstBddOp;

import esdl.rand.base;
import esdl.data.bvec: isBitVector;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray, isDynamicArray;

interface CstVecTerm: CstVecExpr
{

  final CstBddTerm toBdd() {
    auto zero = new CstVal!int(0); // CstVal!int.allocate(0);
    return new CstVec2BddExpr(this, zero, CstBinBddOp.NEQ);
  }

  abstract CstVecExpr unroll(CstIteratorBase iter, uint n);

  CstVec2VecExpr opBinary(string op)(CstVecTerm other)
  {
    static if(op == "&") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.AND);
    }
    static if(op == "|") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.OR);
    }
    static if(op == "^") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.XOR);
    }
    static if(op == "+") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.ADD);
    }
    static if(op == "-") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.SUB);
    }
    static if(op == "*") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.MUL);
    }
    static if(op == "/") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.DIV);
    }
    static if(op == "%") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.REM);
    }
    static if(op == "<<") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.LSH);
    }
    static if(op == ">>") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.RSH);
    }
  }

  CstVec2VecExpr opBinary(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
  	auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
  	static if(op == "&") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.AND);
  	}
  	static if(op == "|") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.OR);
  	}
  	static if(op == "^") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.XOR);
  	}
  	static if(op == "+") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.ADD);
  	}
  	static if(op == "-") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.SUB);
  	}
  	static if(op == "*") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.MUL);
  	}
  	static if(op == "/") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.DIV);
  	}
  	static if(op == "%") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.REM);
  	}
  	static if(op == "<<") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.LSH);
  	}
  	static if(op == ">>") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.RSH);
  	}
      }

  CstVec2VecExpr opBinaryRight(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
	auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
	static if(op == "&") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.AND);
	}
	static if(op == "|") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.OR);
	}
	static if(op == "^") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.XOR);
	}
	static if(op == "+") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.ADD);
	}
	static if(op == "-") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.SUB);
	}
	static if(op == "*") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.MUL);
	}
	static if(op == "/") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.DIV);
	}
	static if(op == "%") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.REM);
	}
	static if(op == "<<") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.LSH);
	}
	static if(op == ">>") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.RSH);
	}
      }

  final CstVecTerm opIndex(CstVecExpr index) {
    // assert(false, "Index operation defined only for Arrays");
    return new CstVecSliceExpr(this, index);
  }

  CstVecTerm opSlice(P)(P p)
    if(isIntegral!P || isBitVector!P) {
      return new CstVecSliceExpr(this, new CstVal!P(p)); // CstVal!P.allocate(p));
    }

  final CstVecTerm opSlice(CstVecExpr lhs, CstVecExpr rhs) {
    return new CstVecSliceExpr(this, lhs, rhs);
  }

  CstVecTerm opSlice(P, Q)(P p, Q q)
    if((isIntegral!P || isBitVector!P) && (isIntegral!Q || isBitVector!Q)) {
      return new CstVecSliceExpr(this, new CstVal!P(p), // CstVal!P.allocate(p),
				 new CstVal!Q(q)); // CstVal!Q.allocate(q));
    }
  CstNotBddExpr opUnary(string op)() if(op == "*") {
    // static if(op == "*") {	// "!" in cstx is translated as "*"
    return new CstNotBddExpr(this.toBdd());
    // }
    // else {
    //   static assert(false);
    // }
  }
  CstNotVecExpr opUnary(string op)() if(op == "~") {
    // static if(op == "*") {	// "!" in cstx is translated as "*"
    return new CstNotVecExpr(this);
    // }
    // else {
    //   static assert(false);
    // }
  }
  CstNegVecExpr opUnary(string op)() if(op == "-") {
    // static if(op == "*") {	// "!" in cstx is translated as "*"
    return new CstNegVecExpr(this);
    // }
    // else {
    //   static assert(false);
    // }
  }
}

abstract class CstVecDomain(T, alias R): CstDomain, CstVecTerm
{
  enum HAS_RAND_ATTRIB = (! __traits(isSame, R, _esdl__norand));

  BddVec _valvec;
  _esdl__Solver _root;

  alias RANGET = IntRangeType!T;

  Unconst!T _refreshedVal;

  static if (HAS_RAND_ATTRIB) {
    // BddVec       _domvec;
    uint         _domIndex = uint.max;
    CstStage     _stage = null;
    uint         _resolveLap = 0;
  }

  Unconst!T _value;

  this() {
    fixRangeSet();
  }

  ~this() {
    // static if (HAS_RAND_ATTRIB) {
    //   _domvec.reset();
    // }
    _valvec.reset();
  }    

  void fixRangeSet() {
    static if (isIntegral!T) {
      IntR rn = IntR(cast(int) T.min, cast(int) T.max);
      _rangeSet &= rn;
    }
    static if (isBitVector!T && T.SIZE <= 32) {
      IntR rn = IntR(cast(int) T.min, cast(int) T.max);
      _rangeSet &= rn;
    }
  }

  override ref BddVec bddvec(Buddy buddy) {
    static if (HAS_RAND_ATTRIB) {
      assert(_domIndex != uint.max,
	     "BDD Domain not yet created for: " ~ name());
      return buddy.getVec(_domIndex);
      // return _domvec;
    }
    else {
      return _valvec;
    }
  }

  // void bddvec(BddVec b) {
  //   static if (HAS_RAND_ATTRIB) {
  //     _domvec = b;
  //   }
  //   else {
  //     assert(false);
  //   }
  // }

  override uint domIndex() {
    static if (HAS_RAND_ATTRIB) {
      return _domIndex;
    }
    else {
      assert(false);
    }
  }

  override void domIndex(uint s) {
    static if (HAS_RAND_ATTRIB) {
      _domIndex = s;
    }
    else {
      assert(false);
    }
  }

  override void reset() {
    static if (HAS_RAND_ATTRIB) {
      _domIndex = uint.max;
    }
  }
  
  override CstStage stage() {
    static if (HAS_RAND_ATTRIB) {
      return _stage;
    }
    else {
      assert(false);
    }
  }

  override void stage(CstStage s) {
    static if (HAS_RAND_ATTRIB) {
      _stage = s;
    }
    else {
      assert(false);
    }
  }

  uint resolveLap() {
    static if (HAS_RAND_ATTRIB) {
      if (_stage !is null && _stage.solved()) {
	return 0;
      }
      else {
	static if (HAS_RAND_ATTRIB) {
	  return _resolveLap;
	}
	else {
	  return 0;
	}
      }
    }
    else return 0;
  }

  void resolveLap(uint lap) {
    static if (HAS_RAND_ATTRIB) {
      if (_stage !is null && _stage.solved()) {
	_resolveLap = 0;
      }
      else {
	static if (HAS_RAND_ATTRIB) {
	  _resolveLap = lap;
	}
      }
    }
  }

  abstract T* getRef();
  
  // override void collate(ulong v, int word = 0) {
  //   static if (HAS_RAND_ATTRIB) {
  //     T* var = getRef();
  //     static if(isIntegral!T) {
  // 	if(word == 0) {
  // 	  *var = cast(T) v;
  // 	}
  // 	else {
  // 	  assert(false, "word has to be 0 for integrals");
  // 	}
  //     }
  //     else {
  // 	(*var)._setNthWord(v, word);
  //     }
  //     markSolved();
  //   }
  //   else {
  //     assert(false);
  //   }
  // }

  override void setVal(ulong[] value) {
    static if (HAS_RAND_ATTRIB) {
      Unconst!T newVal;
      foreach (i, v; value) {
	static if(isIntegral!T) {
	  if (i == 0) {
	    newVal = cast(T) v;
	  }
	  else {
	    assert(false, "word has to be 0 for integrals");
	  }
	}
	else {
	  newVal._setNthWord(v, i);
	}
      }
      if (newVal != *(getRef())) {
	_valueChanged = true;
      }
      *(getRef()) = newVal;
      markSolved();
      execCbs();
    }
    else {
      assert(false);
    }
  }

  override void setVal(ulong value) {
    static if (isBitVector!T) {
      assert (T.SIZE <= 64);
    }
    static if (HAS_RAND_ATTRIB) {
      Unconst!T newVal;
      static if(isIntegral!T) {
	newVal = cast(T) value;
      }
      else {
	newVal._setNthWord(value, 0);
      }

      if (newVal != *(getRef())) {
	_valueChanged = true;
      }
      *(getRef()) = newVal;
      markSolved();
      execCbs();
    }
    else {
      assert(false);
    }
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    static if (HAS_RAND_ATTRIB) {
      if (! solved()) {
	Unconst!T newVal;
	randGen.gen(newVal);
	if (newVal != *(getRef())) {
	  _valueChanged = true;
	  *(getRef()) = newVal;
	}
	markSolved();
	execCbs();
      }
    }
    else {
      assert(false);
    }
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen, CstStage s) {
    static if (HAS_RAND_ATTRIB) {
      assert(stage is s);
      _esdl__doRandomize(randGen);
    }
    else {
      assert(false);
    }
  }

  override bool isRand() {
    static if (HAS_RAND_ATTRIB) {
      return true;
    }
    else {
      return false;
    }
  }

  bool _valueChanged = true;

  override bool hasChanged() {
    return _valueChanged;
  }
  
  override void updateVal() {
    assert(isRand() !is true);
    Unconst!T newVal;
    if (_solvedCycle != _root._cycle) {
      newVal = *(getRef());
      _solvedCycle = _root._cycle;
      if (_valvec.isNull ||
	  newVal != _value) {
	_value = newVal;
	_valueChanged = true;
	_valvec.buildVec(_root._esdl__buddy, _value);
      }
    }
  }
}

interface CstBddTerm: CstBddExpr
{
  abstract override CstBddTerm unroll(CstIteratorBase iter, uint n);

  CstBddTerm opBinary(string op)(CstBddTerm other)
  {
    static if(op == "&") {
      return new CstBdd2BddExpr(this, other, CstBddOp.LOGICAND);
    }
    static if(op == "|") {
      return new CstBdd2BddExpr(this, other, CstBddOp.LOGICOR);
    }
    static if(op == ">>") {
      return new CstBdd2BddExpr(this, other, CstBddOp.LOGICIMP);
    }
  }

  CstBddTerm opUnary(string op)()
  {
    static if(op == "*") {	// "!" in cstx is translated as "*"
      return new CstNotBddExpr(this);
    }
  }

  final CstBddTerm implies(CstBddTerm other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICIMP);
  }

  final CstBddTerm implies(CstVecTerm other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICIMP);
  }

  final CstBddTerm logicOr(CstBddTerm other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICOR);
  }

  final CstBddTerm logicOr(CstVecTerm other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICOR);
  }

  final CstBddTerm logicAnd(CstBddTerm other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICAND);
  }

  final CstBddTerm logicAnd(CstVecTerm other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICAND);
  }

}

class CstIterator(RV): CstIteratorBase, CstVecTerm
{
  RV _arrVar;

  RV arrVar() {
    return _arrVar;
  }

  string _name;

  this(RV arrVar) {
    _name = "iterVar";
    _arrVar = arrVar;
    // _arrVar._arrLen.iterVar(this);
  }

  final override CstDomain getLenVec() {
    return _arrVar.arrLen();
  }
  
  override CstIteratorBase[] iterVars() {
    return _arrVar.iterVars() ~ this;
  }

  override CstIteratorBase getIterator() {
    CstIteratorBase piter = _arrVar.getIterator();
    if (piter !is null) return piter;
    else return this;
  }

  override bool hasUnresolvedIndx() {
    return true;
  }
      
  override CstDomain[] unresolvedIndxs() {
    return [_arrVar.arrLen()];
  }
  
  override uint maxVal() {
    if(! this.isUnrollable()) {
      assert(false, "Can not find maxVal since the " ~
	     "Iter Variable is unrollable");
    }
    // import std.stdio;
    // writeln("maxVal for arrVar: ", _arrVar.name(), " is ",
    // 	    _arrVar.arrLen.value);
    return cast(uint) _arrVar.arrLen.value;
  }

  override bool isUnrollable() {
    return getLenVec().solved();
    // return _arrVar.isUnrollable();
  }

  // get all the primary bdd vectors that constitute a given bdd expression
  override CstDomain[] getRndDomains(bool resolved) {
    return [_arrVar._arrLen]; // _arrVar.arrLen.getRndDomains(resolved);
  }

  override string name() {
    string n = _arrVar.arrLen.name();
    return n[0..$-3] ~ "iter";
  }

  // while an iterator is a singleton wrt to an array, the array
  // itself could have multiple object instances in case it is not
  // concrete -- eg foo[foo.iter].iter
  override bool opEquals(Object other) {
    auto rhs = cast(typeof(this)) other;
    if (rhs is null) return false;
    else return (_arrVar == rhs._arrVar);
  }

  override CstVecExpr unroll(CstIteratorBase iter, uint n) {
    if(this !is iter) {
      return _arrVar.unroll(iter,n).arrLen().makeIterVar();
    }
    else {
      return new CstVal!size_t(n); // CstVal!size_t.allocate(n);
    }
  }

  override CstIteratorBase unrollIter(CstIteratorBase iter, uint n) {
    assert(this !is iter);
    return _arrVar.unroll(iter,n).arrLen().makeIterVar();
  }

  override uint resolveLap() {
    assert (false, "resolveLap should never be called on CstIterator");
  }

  override void resolveLap(uint lap) {}

  override bool isConst() {
    return false;
  }

  override bool isIterator() {
    return true;
  }

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  // this will not return the arrVar since the length variable is
  // not getting constrained here
  override CstVecPrim[] preReqs() {
    return [];
  }

  // get the list of stages this expression should be avaluated in
  // override CstStage[] getStages() {
  //   return arrVar.arrLen.getStages();
  // }

  override bool refresh(CstStage s, Buddy buddy) {
    assert(false, "Can not refresh for a Iter Variable without unrolling");
  }
  
  override BddVec getBDD(CstStage stage, Buddy buddy) {
    assert(false, "Can not getBDD for a Iter Variable without unrolling");
  }

  override bool getVal(ref long val) {
    return false;
  }

  override long evaluate() {
    assert(false, "Can not evaluate an Iterator: " ~ this.name());
  }

  override void setBddContext(CstPredicate pred,
			      ref CstDomain[] vars,
			      ref CstDomain[] vals,
			      ref CstIteratorBase[] iters,
			      ref CstDomain[] idxs,
			      ref CstDomain[] deps) {
    iters ~= this;
  }

  override bool getIntRange(ref IntR rng) {
    return false;
  }

  override bool solved() {
    return _arrVar._arrLen.solved();
  }
}

class CstVecLen(RV): CstVecDomain!(uint, RV.RAND), CstVecPrim
{

  enum HAS_RAND_ATTRIB = (! __traits(isSame, RV.RAND, _esdl__norand));

  // This bdd has the constraint on the max length of the array
  BDD _primBdd;
  
  CstIterator!RV _iterVar;

  RV _parent;

  string _name;

  CstVecPrim[] _preReqs;

  override string name() {
    return _name;
  }

  this(string name, RV parent) {
    assert(parent !is null);
    _name = name;
    _parent = parent;
    _iterVar = new CstIterator!RV(_parent);
    if (_parent.isActualDomain()) {
      _parent.getSolverRoot().addDomain(this, HAS_RAND_ATTRIB);
    }
  }

  ~this() {
    // _domvec.reset();
    _valvec.reset();
    _primBdd.reset();
  }

  CstVecPrim[] preReqs() {
    return _preReqs ~ _parent.preReqs();
  }

  CstIteratorBase[] iterVars() {
    return _parent.iterVars();
  }

  override _esdl__Solver getSolverRoot() {
    return _parent.getSolverRoot();
  }

  CstIteratorBase getIterator() {
    return _parent.getIterator();
  }

  CstDomain[] unresolvedIndxs() {
    return _parent.parentUnresolvedIndxs();
  }

  bool hasUnresolvedIndx() {
    // just must make sure that the
    // array -- if it has a parent array -- is not an abstract element of the parent array
    return _parent.parentLenIsUnresolved();
  }
      
  override bool resolve() {	// no dependency
    return true;
  }

  override CstVecLen!RV getResolved() { // always self
    return this;
  }

  CstDomain[] getRndDomains(bool resolved) {
    return _parent.getDomainLens(resolved);
  }

  CstDomain[] getDomainLens(bool resolved) {
    return [this];
  }
  
  private bool refreshNoRand(Buddy buddy) {
    auto val = _parent.getLen();
    if (! _valvec.isNull()) {
      return false;
    }
    else {
      _valvec.buildVec(buddy, val);
      return true;
    }
  }

  // override CstStage[] getStages() {
  //   CstStage[] stages;
  //   if(isRand) stages = [this.stage()];
  //   return stages;
  // }
  bool refresh(CstStage s, Buddy buddy) {
    static if (HAS_RAND_ATTRIB) {
      auto fparent = _parent.flatten();
      if (fparent !is _parent) {
	return _parent.flatten().arrLen.refresh(s, buddy);
      }
      else {
	assert(stage() !is null, "stage null for: " ~ name());
	if(this.isRand && stage() is s) {
	  return false;
	}
	else if((! this.isRand) ||
		this.isRand && stage().solved()) { // work with the value
	  return refreshNoRand(buddy);
	}
	else {
	  assert(false, "Constraint evaluation in wrong stage");
	}
      }
    }
    else {
      return refreshNoRand(buddy);
    }
  }

  BddVec getBDD(CstStage s, Buddy buddy) {
    static if (HAS_RAND_ATTRIB) {
      auto fparent = _parent.flatten();
      if (fparent !is _parent) {
	return _parent.flatten().arrLen.getBDD(s, buddy);
      }
      else {
	assert(stage() !is null, "stage null for: " ~ name());
	if(this.isRand && stage() is s) {
	  return bddvec(buddy);
	  // return _domvec;
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

  bool getVal(ref long val) {
    static if (HAS_RAND_ATTRIB) {
      assert(stage() !is null);
      if(! this.isRand || stage().solved()) {
	val = value();
	return true;
      }
      else {
	return false;
      }
    }
    else {
      val = value();
      return true;
    }
  }

  long evaluate() {
    static if (HAS_RAND_ATTRIB) {
      // assert(stage() !is null);
      if(! this.isRand || this.solved()) {
    	return value();
      }
      else {
    	import std.conv;
    	assert(false, "Error evaluating " ~ _name);
      }
    }
    else {
      return value();
    }
  }

  // bool isResolved() {
  //   return stage().solved();
  // }
  
  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    // this function will only be called when array lenght is
    // unconstrainted
    markSolved();
    _parent.buildElements();
    execCbs();
  }
  
  override void _esdl__doRandomize(_esdl__RandGen randGen, CstStage s) {
    assert(s is stage);
    _esdl__doRandomize(randGen);
  }
  
  override bool isRand() {
    static if (HAS_RAND_ATTRIB) {
      import std.traits;
      if (isStaticArray!(RV.L)) return false;
      else return true;
    }
    else {
      return false;
    }
  }

  T to(T)()
    if(is(T == string)) {
      import std.conv;
      if(isRand) {
	return "RAND-" ~ "#" ~ _name ~ ":" ~ value().to!string();
      }
      else {
	return "VAL#" ~ _name ~ ":" ~ value().to!string();
      }
    }

  override string toString() {
    return this.to!string();
  }

  override BDD getPrimBdd(Buddy buddy) {
    if(_primBdd.isZero()) {
      _primBdd = this.bddvec(buddy).lte(buddy.buildVec(_parent.maxArrLen));
    }
    return _primBdd;
  }
  
  void resetPrimeBdd() {
    _primBdd.reset();
  }

  void iterVar(CstIterator!RV var) {
    _iterVar = var;
  }

  CstIterator!RV iterVar() {
    return _iterVar;
  }

  CstIterator!RV makeIterVar() {
    if(_iterVar is null) {
      _iterVar = new CstIterator!RV(_parent);
    }
    return _iterVar;
  }

  override uint bitcount() {
    if (_parent.maxArrLen == -1) {
      return 32;
    }
    uint i = 1;
    for (size_t c=1; c < _parent.maxArrLen; c *= 2) {
      i++;
    }
    return i;
  }

  override bool signed() {
    return false;
  }

  long value() {
    return _parent.getLen();
  }

  override void setVal(ulong value) {
    markSolved();
    _parent.setLen(cast(size_t) value);
    execCbs();
  }

  override void setVal(ulong[] v) {
    assert(v.length == 1);
    markSolved();
    _parent.setLen(cast(size_t) v[0]);
    execCbs();
  }

  // override void collate(ulong v, int word = 0) {
  //   assert(word == 0);
  //   _parent.setLen(cast(size_t) v);
  // }

  CstVecExpr unroll(CstIteratorBase iter, uint n) {
    return _parent.unroll(iter,n).arrLen();
  }

  void _esdl__reset() {
    _stage = null;
    _resolveLap = 0;
  }

  bool isVarArr() {
    return false;
  }

  void solveBefore(CstVecPrim other) {
    other.addPreRequisite(this);
  }

  void addPreRequisite(CstVecPrim domain) {
    _preReqs ~= domain;
  }

  bool isConst() {
    return false;
  }
  
  bool isIterator() {
    return false;
  }
  
  bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    bool listed;
    foreach (var; vars) {
      if (var is this) {
	listed = true;
	break;
      }
    }
    if (listed is false) {
      vars ~= this;
    }
    markAbstractDomains(true);
    _parent.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  bool getIntRange(ref IntR rng) {
    return true;
  }

  override void execIterCbs() {
    assert(_iterVar !is null);
    _iterVar.unrollCbs();
  }

  override uint* getRef() {
    assert(false);
  }

  final override bool isActualDomain() {
    return _parent.isActualDomain();
  }

  override bool hasAbstractDomains() {
    return _parent.hasAbstractDomains();
  }

  override void markAbstractDomains(bool len) {
    _parent.markAbstractDomains(len);
  }

  void labelAbstractDomains(bool len) {
    assert(len is true);
    if (this._type !is DomType.MULTI) {
      this._type = DomType.MAYBEMONO;
    }
  }
}

abstract class CstValBase: CstVecTerm
{
  CstBddExpr _cstExpr;
  
  CstVecPrim[] preReqs() {
    return [];
  }

  CstIteratorBase[] iterVars() {
    return [];
  }

  CstIteratorBase getIterator() {
    return null;
  }

  CstDomain[] unresolvedIndxs() {
    return [];
  }
      
  bool hasUnresolvedIndx() {
    return false;
  }
      
  bool isConst() {
    return true;
  }

  bool isIterator() {
    return false;
  }

  CstDomain[] getRndDomains(bool resolved) {
    return [];
  }

  override CstVecExpr unroll(CstIteratorBase l, uint n) {
    return this;
  }

}

auto _esdl__cstVal(T)(T val) {
  return new CstVal!(T)(val); // CstVal!(T).allocate(val);
}

class CstVal(T = int): CstValBase
{
  // static class Allocator: CstValAllocator {
  //   CstVal!T[] container;
  //   uint _index = 0;

  //   uint _mark;

  //   override void markIndex() {
  //     _mark = _index;
  //   }

  //   override void resetIndex() {
  //     for (uint i = _mark; i != _index; ++i) {
  // 	container[i]._valvec.reset();
  //     }
  //     _index = _mark;
      
  //   }


  //   CstVal!T allocate(T val) {
  //     // return new CstVal!T(val);
  //     if (_index >= container.length) {
  //   	container.length += 1;
  //   	container[$-1] = new CstVal!T(val);
  //     }
      
  //     auto cstVal = container[_index];
  //     cstVal._val = val;
  //     _index++;
  //     return cstVal;
  //   }
  // }

  import std.conv;

  // static Allocator _allocator;

  // static this() {
  //   CstVal!T._allocator = new Allocator;
  //   CstValAllocator.allocators ~= CstVal!T._allocator;
  // }

  T _val;			// the value of the constant
  BddVec _valvec;

  string name() {
    return _val.to!string();
  }

  // static CstVal!T allocate(T value) {
  //   Allocator allocator = _allocator;
  //   if (allocator is null) {
  //     allocator = new Allocator;
  //     _allocator = allocator;
  //     CstValAllocator.allocators ~= allocator;
  //   }

  //   // return new CstVal!T(value);
  //   return allocator.allocate(value);
  // }

  this(T value) {
    _val = value;
  }

  ~this() {
    _valvec.reset();
  }

  bool refresh(CstStage stage, Buddy buddy) {
    if (_valvec.isNull()) {
      _valvec.buildVec(buddy, _val);
      return true;
    }
    else {
      return false;
    }
  }
  
  BddVec getBDD(CstStage stage, Buddy buddy) {
    return _valvec;
  }

  const(T)* getRef() {
    return &_val;
  }

  bool getVal(ref long val) {
    val = _val;
    return true;
  }

  long evaluate() {
    return _val;
  }

  override CstDomain[] unresolvedIndxs() {
    return [];
  }

  override bool hasUnresolvedIndx() {
    return false;
  }

  uint resolveLap() {
    return 0;			// const
  }

  void resolveLap(uint lap) {}

  bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  bool solved() {
    return true;
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    if (_valvec.isNull()) {
      _valvec.buildVec(pred.getSolver().getBuddy(), _val);
    }
  }

   bool getIntRange(ref IntR rng) {
     assert(false, "getIntRange should never be called for a CstVal");
  }

}


// This class would hold two(bin) vector nodes and produces a vector
// only after processing those two nodes
class CstVec2VecExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;
  CstBinVecOp _op;

  // CstDomain[] _preReqs;
  CstVecPrim[] preReqs() {
    return _lhs.preReqs() ~ _rhs.preReqs();
  }

  CstIteratorBase[] _iterVars;
  CstIteratorBase[] iterVars() {
    return _iterVars;
  }

  CstIteratorBase getIterator() {
    auto liter = _lhs.getIterator();
    auto riter = _rhs.getIterator();
    if (liter !is null) {
      assert (riter is null || riter is liter);
      return liter;
    }
    else {
      return riter;
    }
  }

  CstDomain[] _unresolvedIndxs;
  
  CstDomain[] unresolvedIndxs() {
    return _unresolvedIndxs;
  }
  
  bool hasUnresolvedIndx() {
    return _lhs.hasUnresolvedIndx() || _rhs.hasUnresolvedIndx();
  }
      
  string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string() ~ " " ~ _rhs.name ~ " )";
  }

  CstDomain[] getRndDomains(bool resolved) {
    return _lhs.getRndDomains(resolved) ~ _rhs.getRndDomains(resolved);
  }

  bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.iterVars.length !is 0) {
      assert(false,
	     "CstVec2VecExpr: Need to unroll the iterVars" ~
	     " before attempting to solve BDD");
    }

    // auto lvec = _lhs.getBDD(stage, buddy);
    // auto rvec = _rhs.getBDD(stage, buddy);

    final switch(_op) {
    case CstBinVecOp.AND: return _lhs.getBDD(stage, buddy) &
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.OR:  return _lhs.getBDD(stage, buddy) |
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.XOR: return _lhs.getBDD(stage, buddy) ^
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.ADD: return _lhs.getBDD(stage, buddy) +
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.SUB: return _lhs.getBDD(stage, buddy) -
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.MUL:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) *
			   _rhs.evaluate();
      if(_lhs.isConst()) return _lhs.evaluate() *
			   _rhs.getBDD(stage, buddy);
      return _lhs.getBDD(stage, buddy) * _rhs.getBDD(stage, buddy);
    case CstBinVecOp.DIV:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) /
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) / _rhs.getBDD(stage, buddy);
    case CstBinVecOp.REM:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) %
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) % _rhs.getBDD(stage, buddy);
    case CstBinVecOp.LSH:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) <<
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) << _rhs.getBDD(stage, buddy);
    case CstBinVecOp.RSH:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) >>
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) >> _rhs.getBDD(stage, buddy);
    case CstBinVecOp.BITINDEX:
      assert(false, "BITINDEX is not implemented yet!");
    }
  }

  bool getVal(ref long val) {

    long lval;
    long rval;
    if (! _lhs.getVal(lval)) {
      return false;
    }
    if (! _rhs.getVal(rval)) {
      return false;
    }

    final switch(_op) {
    case CstBinVecOp.AND: val = lval &  rval; return true;
    case CstBinVecOp.OR:  val = lval |  rval; return true;
    case CstBinVecOp.XOR: val = lval ^  rval; return true;
    case CstBinVecOp.ADD: val = lval +  rval; return true;
    case CstBinVecOp.SUB: val = lval -  rval; return true;
    case CstBinVecOp.MUL: val = lval *  rval; return true;
    case CstBinVecOp.DIV: val = lval /  rval; return true;
    case CstBinVecOp.REM: val = lval %  rval; return true;
    case CstBinVecOp.LSH: val = lval << rval; return true;
    case CstBinVecOp.RSH: val = lval >> rval; return true;
    case CstBinVecOp.BITINDEX:
      assert(false, "BITINDEX is not implemented yet!");
    }
  }

  long evaluate() {
    auto lvec = _lhs.evaluate();
    auto rvec = _rhs.evaluate();

    final switch(_op) {
    case CstBinVecOp.AND: return lvec &  rvec;
    case CstBinVecOp.OR:  return lvec |  rvec;
    case CstBinVecOp.XOR: return lvec ^  rvec;
    case CstBinVecOp.ADD: return lvec +  rvec;
    case CstBinVecOp.SUB: return lvec -  rvec;
    case CstBinVecOp.MUL: return lvec *  rvec;
    case CstBinVecOp.DIV: return lvec /  rvec;
    case CstBinVecOp.REM: return lvec %  rvec;
    case CstBinVecOp.LSH: return lvec << rvec;
    case CstBinVecOp.RSH: return lvec >> rvec;
    case CstBinVecOp.BITINDEX:
      assert(false, "BITINDEX is not implemented yet!");
    }
  }

  override CstVec2VecExpr unroll(CstIteratorBase iter, uint n) {
    bool found = false;
    foreach(var; iterVars()) {
      if(iter is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstVec2VecExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
    }
  }

  this(CstVecExpr lhs, CstVecExpr rhs, CstBinVecOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
    foreach (var; lhs.iterVars ~ rhs.iterVars) {
      bool add = true;
      foreach (l; _iterVars) {
    	if (l is var) add = false;
    	break;
      }
      if (add) _iterVars ~= var;
    }

    foreach (var; lhs.unresolvedIndxs ~ rhs.unresolvedIndxs) {
      bool add = true;
      foreach (l; _unresolvedIndxs) {
    	if (l is var) add = false;
    	break;
      }
      if (add) _unresolvedIndxs ~= var;
    }
  }

  uint resolveLap() {
    auto lhs = _lhs.resolveLap();
    auto rhs = _rhs.resolveLap();
    if (rhs > lhs) return rhs;
    else return lhs;
  }

  void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }
  
  bool isConst() {
    return false;
  }

  bool isIterator() {
    return false;
  }

  bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    _lhs.setBddContext(pred, vars, vals, iters, idxs, deps);
    _rhs.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  bool getIntRange(ref IntR rng) {
    if (_rhs.solved()) {
      assert(! _lhs.solved());
      auto rhs = cast(int) _rhs.evaluate();
      switch(_op) {
      case CstBinVecOp.ADD:
	IntRangeMod!int(IntRangeModOp.ADD, rhs).apply(rng);
	return _lhs.getIntRange(rng);
	break;
      case CstBinVecOp.SUB: 
	IntRangeMod!int(IntRangeModOp.SUB, rhs).apply(rng);
	return _lhs.getIntRange(rng);
	break;
      default:
	return false;
      }
    }
    else if (_lhs.solved()) {
      assert(! _rhs.solved());
      auto lhs = cast(int) _lhs.evaluate();
      switch(_op) {
      case CstBinVecOp.ADD:
	IntRangeMod!int(IntRangeModOp.ADD, lhs).apply(rng);
	return _rhs.getIntRange(rng);
	break;
      case CstBinVecOp.SUB: 
	IntRangeMod!int(IntRangeModOp.SUBD, lhs).apply(rng);
	return _rhs.getIntRange(rng);
	break;
      default:
	return false;
      }
    }
    else {
      return false;
    }
  }

  override bool solved() {
    return _lhs.solved() && _rhs.solved();
  }

}

class CstVecSliceExpr: CstVecTerm
{
  CstVecExpr _vec;
  CstVecExpr _lhs;
  CstVecExpr _rhs;

  // CstDomain[] _preReqs;
  CstVecPrim[] preReqs() {
    // CstVecPrim[] reqs;
    if(_rhs is null) {
      return _vec.preReqs() ~ _lhs.preReqs();
      // foreach(req; _vec.preReqs() ~ _lhs.preReqs()) {
      // 	if(! req.solved()) {
      // 	  reqs ~= req;
      // 	}
      // }
    }
    else {
      return _vec.preReqs() ~ _lhs.preReqs() ~ _rhs.preReqs();
      // foreach(req; _vec.preReqs() ~ _lhs.preReqs() ~ _rhs.preReqs()) {
      // 	if(! req.solved()) {
      // 	  reqs ~= req;
      // 	}
      // }
    }
    // return reqs;
  }
  
  CstIteratorBase[] _iterVars;
  CstIteratorBase[] iterVars() {
    return _iterVars;
  }

  CstIteratorBase getIterator() {
    auto liter = _lhs.getIterator();
    auto riter = _rhs.getIterator();
    if (liter !is null) {
      assert (riter is null || riter is liter);
      return liter;
    }
    else {
      return riter;
    }
  }

  CstDomain[] _unresolvedIndxs;
  CstDomain[] unresolvedIndxs() {
    return _unresolvedIndxs;
  }

  bool hasUnresolvedIndx() {
    return
      _lhs.hasUnresolvedIndx() ||
      _rhs.hasUnresolvedIndx() ||
      _vec.hasUnresolvedIndx();
  }

  string name() {
    return _vec.name() ~ "[ " ~ _lhs.name() ~ " .. " ~ _rhs.name() ~ " ]";
  }

  CstDomain[] getRndDomains(bool resolved) {
    if(_rhs is null) {
      return _vec.getRndDomains(resolved) ~ _lhs.getRndDomains(resolved);
    }
    else {
      return _vec.getRndDomains(resolved) ~ _lhs.getRndDomains(resolved) ~ _rhs.getRndDomains(resolved);
    }
  }

  bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.iterVars.length !is 0) {
      assert(false,
	     "CstVecSliceExpr: Need to unroll the iterVars" ~
	     " before attempting to solve BDD");
    }

    auto vec  = _vec.getBDD(stage, buddy);
    size_t lvec = cast(size_t) _lhs.evaluate();
    size_t rvec = lvec;
    if(_rhs is null) {
      rvec = lvec + 1;
    }
    else {
      rvec = cast(size_t) _rhs.evaluate();
    }
    return vec[lvec..rvec];
  }

  bool getVal(ref long val) {
    return false;
  }

  long evaluate() {
    // auto vec  = _vec.evaluate();
    // auto lvec = _lhs.evaluate();
    // auto rvec = _rhs.evaluate();

    assert(false, "Can not evaluate a CstVecSliceExpr!");
  }

  override CstVecSliceExpr unroll(CstIteratorBase iter, uint n) {
    bool found = false;
    foreach(var; iterVars()) {
      if(iter is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      if(_rhs is null) {
	return new CstVecSliceExpr(_vec.unroll(iter, n), _lhs.unroll(iter, n));
      }
      else {
	return new CstVecSliceExpr(_vec.unroll(iter, n),
				   _lhs.unroll(iter, n), _rhs.unroll(iter, n));
      }
    }
  }

  this(CstVecExpr vec, CstVecExpr lhs, CstVecExpr rhs=null) {
    _vec = vec;
    _lhs = lhs;
    _rhs = rhs;
    auto iterVars = vec.iterVars ~ lhs.iterVars;
    if(rhs !is null) {
      iterVars ~= rhs.iterVars;
    }
    foreach(var; iterVars) {
      bool add = true;
      foreach(l; _iterVars) {
	if(l is var) add = false;
	break;
      }
      if(add) _iterVars ~= var;
    }

    auto unresolvedIndxs = vec.unresolvedIndxs() ~ lhs.unresolvedIndxs();
    if(rhs !is null) {
      unresolvedIndxs ~= rhs.unresolvedIndxs();
    }

    foreach(indx; unresolvedIndxs) {
      bool add = true;
      foreach(l; _unresolvedIndxs) {
	if(l is indx) add = false;
	break;
      }
      if(add) _unresolvedIndxs ~= indx;
    }

  }

  uint resolveLap() {
    return _vec.resolveLap();
  }

  void resolveLap(uint lap) {
    _vec.resolveLap(lap);
  }

  bool isConst() {
    return false;
  }

  bool isIterator() {
    return false;
  }

  bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    _vec.setBddContext(pred, vars, vals, iters, idxs, deps);
    _lhs.setBddContext(pred, deps, vals, iters, idxs, deps);
    if (_rhs !is null) {
      _rhs.setBddContext(pred, deps, vals, iters, idxs, deps);
    }
  }

  bool getIntRange(ref IntR rng) {
     return false;
  }

  override bool solved() {
    if (_rhs is null) {
      return _lhs.solved() && _vec.solved();
    }
    else {
      return _lhs.solved() && _rhs.solved() && _vec.solved();
    }
  }
  
}

class CstNotVecExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _expr;

  // CstDomain[] _preReqs;
  CstVecPrim[] preReqs() {
    return _expr.preReqs();
  }

  CstIteratorBase[] _iterVars;
  CstIteratorBase[] iterVars() {
    return _iterVars;
  }

  CstIteratorBase getIterator() {
    return _expr.getIterator();
  }

  CstDomain[] unresolvedIndxs() {
    return _expr.unresolvedIndxs();
  }

  bool hasUnresolvedIndx() {
    return _expr.hasUnresolvedIndx();
  }
      
  string name() {
    return "( ~ " ~ _expr.name ~ " )";
  }

  CstDomain[] getRndDomains(bool resolved) {
    return _expr.getRndDomains(resolved);
  }

  bool refresh(CstStage stage, Buddy buddy) {
    return _expr.refresh(stage, buddy);
  }
  
  BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.iterVars.length !is 0) {
      assert(false,
	     "CstNotVecExpr: Need to unroll the iterVars" ~
	     " before attempting to solve BDD");
    }

    return ~(_expr.getBDD(stage, buddy));
  }

  bool getVal(ref long val) {
    auto retval = _expr.getVal(val);
    val = ~val;
    return retval;
  }

  long evaluate() {
    return ~(_expr.evaluate());
  }

  override CstNotVecExpr unroll(CstIteratorBase iter, uint n) {
    bool found = false;
    foreach(var; iterVars()) {
      if(iter is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstNotVecExpr(_expr.unroll(iter, n));
    }
  }

  this(CstVecExpr expr) {
    _expr = expr;
    _iterVars = _expr.iterVars;
  }

  uint resolveLap() {
    return _expr.resolveLap();
  }

  void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }
  
  bool isConst() {
    return false;
  }

  bool isIterator() {
    return false;
  }

  bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    _expr.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  bool getIntRange(ref IntR rng) {
     return false;
  }

  override bool solved() {
    return _expr.solved();
  }
}

class CstNegVecExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _expr;

  // CstDomain[] _preReqs;
  CstVecPrim[] preReqs() {
    return _expr.preReqs();
  }

  CstIteratorBase[] _iterVars;
  CstIteratorBase[] iterVars() {
    return _iterVars;
  }

  CstIteratorBase getIterator() {
    return _expr.getIterator();
  }

  CstDomain[] unresolvedIndxs() {
    return _expr.unresolvedIndxs();
  }

  bool hasUnresolvedIndx() {
    return _expr.hasUnresolvedIndx();
  }
      
  string name() {
    return "( - " ~ _expr.name ~ " )";
  }

  CstDomain[] getRndDomains(bool resolved) {
    return _expr.getRndDomains(resolved);
  }

  bool refresh(CstStage stage, Buddy buddy) {
    return _expr.refresh(stage, buddy);
  }
  
  BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.iterVars.length !is 0) {
      assert(false,
	     "CstNegVecExpr: Need to unroll the iterVars" ~
	     " before attempting to solve BDD");
    }

    return -(_expr.getBDD(stage, buddy));
  }

  bool getVal(ref long val) {
    auto retval = _expr.getVal(val);
    val = -val;
    return retval;
  }

  long evaluate() {
    return -(_expr.evaluate());
  }

  override CstNegVecExpr unroll(CstIteratorBase iter, uint n) {
    bool found = false;
    foreach(var; iterVars()) {
      if(iter is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstNegVecExpr(_expr.unroll(iter, n));
    }
  }

  this(CstVecExpr expr) {
    _expr = expr;
    _iterVars = _expr.iterVars;
  }

  uint resolveLap() {
    return _expr.resolveLap();
  }

  void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }
  
  bool isConst() {
    return false;
  }

  bool isIterator() {
    return false;
  }

  bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    _expr.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  bool getIntRange(ref IntR rng) {
     return false;
  }

  override bool solved() {
    return _expr.solved();
  }
}


class CstBdd2BddExpr: CstBddTerm
{
  import std.conv;

  CstBddExpr _lhs;
  CstBddExpr _rhs;
  CstBddOp _op;

  CstIteratorBase[] _iterVars;

  CstDomain[] _unresolvedIndxs;
  
  CstIteratorBase[] iterVars() {
       return _iterVars;
  }

  CstIteratorBase getIterator() {
    auto liter = _lhs.getIterator();
    auto riter = _rhs.getIterator();
    if (liter !is null) {
      assert (riter is null || riter is liter);
      return liter;
    }
    else {
      return riter;
    }
  }

  this(CstBddExpr lhs, CstBddExpr rhs, CstBddOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;

    foreach (var; lhs.iterVars ~ rhs.iterVars) {
      bool add = true;
      foreach (l; _iterVars) {
	if (l is var) add = false;
	break;
      }
      if (add) _iterVars ~= var;
    }

    foreach (var; lhs.unresolvedIndxs ~ rhs.unresolvedIndxs) {
      bool add = true;
      foreach (l; _unresolvedIndxs) {
	if (l is var) add = false;
	break;
      }
      if (add) _unresolvedIndxs ~= var;
    }
  }

  bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  CstDomain[] unresolvedIndxs() {
    return _unresolvedIndxs;
  }

  bool hasUnresolvedIndx() {
    return _lhs.hasUnresolvedIndx() || _rhs.hasUnresolvedIndx();
  }

  string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string ~ " " ~ _rhs.name ~ " )";
  }

  CstVecPrim[] preReqs() {
    return _lhs.preReqs() ~ _rhs.preReqs();
    // CstVecPrim[] reqs;
    // foreach(req; _lhs.preReqs() ~ _rhs.preReqs()) {
    //   if(! req.solved()) {
    // 	reqs ~= req;
    //   }
    // }
    // return reqs;
  }

  CstDomain[] getRndDomains(bool resolved) {
    return _lhs.getRndDomains(resolved) ~ _rhs.getRndDomains(resolved);
  }


  BDD getBDD(CstStage stage, Buddy buddy) {
    if(this.iterVars.length !is 0) {
      assert(false,
	     "CstBdd2BddExpr: Need to unroll the iterVars" ~
	     " before attempting to solve BDD");
    }
    auto lvec = _lhs.getBDD(stage, buddy);
    auto rvec = _rhs.getBDD(stage, buddy);

    BDD retval;
    final switch(_op) {
    case CstBddOp.LOGICAND: retval = lvec &  rvec; break;
    case CstBddOp.LOGICOR:  retval = lvec |  rvec; break;
    case CstBddOp.LOGICIMP: retval = lvec >> rvec; break;
    }
    return retval;
  }

  override CstBdd2BddExpr unroll(CstIteratorBase iter, uint n) {
    bool found = false;
    foreach(var; iterVars()) {
      if(iter is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstBdd2BddExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
    }
  }

  uint resolveLap() {
    uint lhs = _lhs.resolveLap();
    uint rhs = _rhs.resolveLap();
    if (lhs > rhs) return lhs;
    else return rhs;
  }
  void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    _lhs.setBddContext(pred, vars, vals, iters, idxs, deps);
    _rhs.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  override bool getIntRangeSet(ref IntRS rs) {
    assert(! _lhs.solved());
    assert(! _rhs.solved());

    IntRS lhs;
    IntRS rhs;

    if (_lhs.getIntRangeSet(lhs) is false) return false;
    if (_rhs.getIntRangeSet(rhs) is false) return false;

    final switch(_op) {
    case CstBddOp.LOGICAND: lhs &= rhs; break;
    case CstBddOp.LOGICOR:  lhs |= rhs; break;
    case CstBddOp.LOGICIMP: return false;
    }

    return true;
  }

  bool cstExprIsNop() {
    return false;
  }

  override bool solved() {
    return _lhs.solved && _rhs.solved();
  }
}

// TBD
class CstIteBddExpr: CstBddTerm
{
  CstIteratorBase[] _iterVars;

  CstIteratorBase[] iterVars() {
    assert(false, "TBD");
  }

  CstIteratorBase getIterator() {
    assert(false, "TBD");
  }

  CstDomain[] unresolvedIndxs() {
    assert(false, "TBD");
  }

  bool hasUnresolvedIndx() {
    assert(false, "TBD");
  }

  string name() {
    return "CstIteBddExpr";
  }

  bool refresh(CstStage stage, Buddy buddy) {
    assert(false);
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    assert(false, "TBD");
  }

  override bool getIntRangeSet(ref IntRS rng) {
     return false;
  }

  bool cstExprIsNop() {
    return false;
  }

  CstVecPrim[] preReqs() {
    assert(false, "TBD");
  }    

  uint resolveLap() {
    assert(false, "TBD");
  }    

  void resolveLap(uint lap) {
    assert(false, "TBD");
  }    

  CstBddTerm unroll(CstIteratorBase iter, uint n) {
    assert(false, "TBD");
  }

  CstDomain[] getRndDomains(bool resolved) {
    assert(false, "TBD");
  }

  // abstract CstStage[] getStages();

  abstract BDD getBDD(CstStage stage, Buddy buddy) {
    assert(false, "TBD");
  }

  override bool solved() {
    assert(false, "TBD");
  }
}

class CstVec2BddExpr: CstBddTerm
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;
  CstBinBddOp _op;

  CstIteratorBase[] _iterVars;
  CstDomain[] _unresolvedIndxs;

  CstIteratorBase[] iterVars() {
       return _iterVars;
  }

  CstIteratorBase getIterator() {
    auto liter = _lhs.getIterator();
    auto riter = _rhs.getIterator();
    if (liter !is null) {
      assert (riter is null || riter is liter);
      return liter;
    }
    else {
      return riter;
    }
  }

  CstDomain[] unresolvedIndxs() {
       return _unresolvedIndxs;
  }

  this(CstVecExpr lhs, CstVecExpr rhs, CstBinBddOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;

    foreach (var; lhs.iterVars ~ rhs.iterVars) {
      bool add = true;
      foreach (l; _iterVars) {
	if (l is var) add = false;
	break;
      }
      if (add) _iterVars ~= var;
    }

    foreach (var; lhs.unresolvedIndxs ~ rhs.unresolvedIndxs) {
      bool add = true;
      foreach (l; _unresolvedIndxs) {
	if (l is var) add = false;
	break;
      }
      if (add) _unresolvedIndxs ~= var;
    }
  }

  string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string ~ " " ~ _rhs.name ~ " )";
  }

  bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  CstVecPrim[] preReqs() {
    return _lhs.preReqs() ~ _rhs.preReqs();
    // CstVecPrim[] reqs;
    // foreach(req; _lhs.preReqs() ~ _rhs.preReqs()) {
    //   if(! req.solved()) {
    // 	reqs ~= req;
    //   }
    // }
    // return reqs;
  }
    
  CstDomain[] getRndDomains(bool resolved) {
    return _lhs.getRndDomains(resolved) ~ _rhs.getRndDomains(resolved);
  }

  BDD getBDD(CstStage stage, Buddy buddy) {
    if (this.iterVars.length !is 0) {
      // foreach (iter; iterVars) {
      // 	import std.stdio;
      // 	writeln(name(), " : ", iter.name());
      // }
      assert(false,
	     "CstVec2BddExpr: Need to unroll the iterVars" ~
	     " before attempting to solve BDD");
    }
    auto lvec = _lhs.getBDD(stage, buddy);
    auto rvec = _rhs.getBDD(stage, buddy);

    BDD retval;
    final switch(_op) {
    case CstBinBddOp.LTH: retval = lvec.lth(rvec); break;
    case CstBinBddOp.LTE: retval = lvec.lte(rvec); break;
    case CstBinBddOp.GTH: retval = lvec.gth(rvec); break;
    case CstBinBddOp.GTE: retval = lvec.gte(rvec); break;
    case CstBinBddOp.EQU: retval = lvec.equ(rvec); break;
    case CstBinBddOp.NEQ: retval = lvec.neq(rvec); break;
    }
    return retval;
  }

  override CstVec2BddExpr unroll(CstIteratorBase iter, uint n) {
    // import std.stdio;
    // writeln(_lhs.name() ~ " " ~ _op.to!string ~ " " ~ _rhs.name() ~ " Getting unwound!");
    bool found = false;
    foreach(var; iterVars()) {
      if(iter is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      // writeln("RHS: ", _rhs.unroll(iter, n).name());
      // writeln("LHS: ", _lhs.unroll(iter, n).name());
      return new CstVec2BddExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
    }
  }

  bool hasUnresolvedIndx() {
    return _lhs.hasUnresolvedIndx() || _rhs.hasUnresolvedIndx();
  }

  uint resolveLap() {
    uint lhs = _lhs.resolveLap();
    uint rhs = _rhs.resolveLap();
    if (lhs > rhs) return lhs;
    else return rhs;
  }
  
  void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }


  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    _lhs.setBddContext(pred, vars, vals, iters, idxs, deps);
    _rhs.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  override bool getIntRangeSet(ref IntRS rs) {
    if (_rhs.solved()) {
      assert(! _lhs.solved(), "Expression: " ~ _lhs.name());
      auto rhs = cast(int) _rhs.evaluate();
      IntR rn = IntR(_op, rhs);
      bool valid = _lhs.getIntRange(rn);
      rs ~= rn;
      return valid;
    }
    else if (_lhs.solved()) {
      assert(! _rhs.solved(), "Expression: " ~ _rhs.name());
      auto lhs = cast(int) _lhs.evaluate();
      IntR rn = IntR(_op, lhs, true);
      bool valid = _rhs.getIntRange(rn);
      rs ~= rn;
      return valid;
    }
    else {
      return false;
    }
  }

  override bool solved() {
    return _lhs.solved && _rhs.solved();
  }
}

class CstBddConst: CstBddTerm
{
  immutable bool _expr;

  CstIteratorBase[] iterVars() {
       return [];
  }

  CstIteratorBase getIterator() {
    return null;
  }
  
  this(bool expr) {
    _expr = expr;
  }

  bool refresh(CstStage stage, Buddy buddy) {
    return false;
  }
  
  BDD getBDD(CstStage stage, Buddy buddy) {
    if(_expr) return buddy.one();
    else return buddy.zero();
  }

  string name() {
    if(_expr) return "TRUE";
    else return "FALSE";
  }

  CstDomain[] getRndDomains(bool resolved) {
    return [];
  }

  CstVecPrim[] preReqs() {
    return [];
  }

  override CstBddConst unroll(CstIteratorBase iter, uint n) {
    return this;
  }

  CstDomain[] unresolvedIndxs() {
    return [];
  }

  bool hasUnresolvedIndx() {
    return false;
  }

  uint resolveLap() {
    return 0;
  }
  void resolveLap(uint lap) {}

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    // nothing for CstBddConst
  }

  override bool getIntRangeSet(ref IntRS rng) {
     return false;
  }

  override bool solved() {
    return true;
  }
}

class CstNotBddExpr: CstBddTerm
{
  CstBddExpr _expr;

  this(CstBddExpr expr) {
    _expr = expr;
  }

  CstIteratorBase[] iterVars() {
    return _expr.iterVars();
  }

  CstIteratorBase getIterator() {
    return _expr.getIterator();
  }

  string name() {
    return "( " ~ "!" ~ " " ~ _expr.name ~ " )";
  }

  bool refresh(CstStage stage, Buddy buddy) {
    return _expr.refresh(stage, buddy);
  }
  
  CstVecPrim[] preReqs() {
    return _expr.preReqs();
  }

  CstDomain[] getRndDomains(bool resolved) {
    return _expr.getRndDomains(resolved);
  }

  BDD getBDD(CstStage stage, Buddy buddy) {
    if(this.iterVars.length !is 0) {
      assert(false,
	     "CstBdd2BddExpr: Need to unroll the iterVars" ~
	     " before attempting to solve BDD");
    }
    auto bdd = _expr.getBDD(stage, buddy);
    return (~ bdd);
  }

  override CstNotBddExpr unroll(CstIteratorBase iter, uint n) {
    bool shouldUnroll = false;
    foreach(var; iterVars()) {
      if(iter is var) {
	shouldUnroll = true;
	break;
      }
    }
    if(! shouldUnroll) return this;
    else {
      return new CstNotBddExpr(_expr.unroll(iter, n));
    }
  }

  CstDomain[] unresolvedIndxs() {
    return _expr.unresolvedIndxs();
  }

  bool hasUnresolvedIndx() {
    return _expr.hasUnresolvedIndx();
  }

  uint resolveLap() {
    return _expr.resolveLap();
  }
  void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    _expr.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  override bool getIntRangeSet(ref IntRS rng) {
     return false;
  }

  override bool solved() {
    return _expr.solved();
  }
}

// CstBdd2BddExpr logicOr(CstVecExpr other)
// {
//   return new CstBdd2BddExpr(toBdd(this), toBdd(other), CstBddOp.LOGICOR);
// }

auto _esdl__logicOr(P, Q)(P p, Q q) {
  CstBddTerm _p;
  CstBddTerm _q;
  static if (is (P == bool)) {
    _p = new CstBddConst(p);
  }
  else static if (is (P: CstVecExpr)) {
    _p = toBdd(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstBddConst(q);
  }
  else static if (is (Q: CstVecExpr)) {
    _q = toBdd(q);
  }
  else {
    _q = q;
  }
  return _p.logicOr(_q);
}

auto _esdl__logicAnd(P, Q)(P p, Q q) {
  CstBddTerm _p;
  CstBddTerm _q;
  static if(is(P == bool)) {
    _p = new CstBddConst(p);
  }
  else static if (is (P: CstVecExpr)) {
    _p = toBdd(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstBddConst(q);
  }
  else static if (is (Q: CstVecExpr)) {
    _q = toBdd(q);
  }
  else {
    _q = q;
  }
  return _p.logicAnd(_q);
}


CstVec2BddExpr _esdl__lth(Q)(CstVecExpr left, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__lth(left, qq);
  }

CstVec2BddExpr _esdl__lth(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.LTH);
}

auto _esdl__lth(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__lth(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__gte(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p < q);
  }
}

CstVec2BddExpr _esdl__lte(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__lte(p, qq);
  }

CstVec2BddExpr _esdl__lte(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.LTE);
}

auto _esdl__lte(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__lte(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__gth(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p <= q);
  }
}

CstVec2BddExpr _esdl__gth(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__gth(p, qq);
  }

CstVec2BddExpr _esdl__gth(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.GTH);
}

auto _esdl__gth(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__gth(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__lte(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p > q);
  }
}

CstVec2BddExpr _esdl__gte(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__gte(p, qq);
  }

CstVec2BddExpr _esdl__gte(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.GTE);
}

auto _esdl__gte(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__gte(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__lth(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p >= q);
  }
}

CstVec2BddExpr _esdl__equ(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__equ(p, qq);
  }

CstVec2BddExpr _esdl__equ(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.EQU);
}

auto _esdl__equ(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__equ(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__equ(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p == q);
  }
}

CstVec2BddExpr _esdl__neq(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__neq(p, qq);
  }

CstVec2BddExpr _esdl__neq(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.NEQ);
}

auto _esdl__neq(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__neq(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__neq(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p != q);
  }
}
