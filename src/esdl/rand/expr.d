module esdl.rand.expr;

import esdl.rand.intr;
import esdl.rand.obdd;
import esdl.rand.misc: _esdl__RandGen, _esdl__norand, isVecSigned, Unconst;
import esdl.rand.misc: CstBinVecOp, CstBinBddOp, CstBddOp;

import esdl.rand.base;
import esdl.data.bvec: isBitVector;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray, isDynamicArray;

interface CstVecElem: CstVecExpr
{

  final CstBddElem toBdd() {
    auto zero = new CstVal!int(0); // CstVal!int.allocate(0);
    return new CstVec2BddExpr(this, zero, CstBinBddOp.NEQ);
  }

  // abstract CstVecExpr unroll(CstIteratorBase iter, uint n);

  CstVec2VecExpr opBinary(string op)(CstVecElem other)
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
    static if(op == "~") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.RANGE);
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
  	static if(op == "~") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.RANGE);
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
	static if(op == "~") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.RANGE);
	}
      }

  final CstVecSliceExpr opIndex(CstVecElem index) {
    // assert(false, "Index operation defined only for Arrays");
    CstVec2VecExpr range = cast(CstVec2VecExpr) index;
    if (range is null || range._op !is CstBinVecOp.RANGE) {
      range = index ~ (index + new CstVal!(int)(1));
    }
    return new CstVecSliceExpr(this, range);
  }

  // CstVecElem opSlice(P)(P p)
  //   if(isIntegral!P || isBitVector!P) {
  //     return new CstVecSliceExpr(this, new CstVal!P(p)); // CstVal!P.allocate(p));
  //   }

  // final CstVecElem opSlice(CstVecExpr lhs, CstVecExpr rhs) {
  //   return new CstVecSliceExpr(this, lhs, rhs);
  // }

  // CstVecElem opSlice(P, Q)(P p, Q q)
  //   if((isIntegral!P || isBitVector!P) && (isIntegral!Q || isBitVector!Q)) {
  //     return new CstVecSliceExpr(this, new CstVal!P(p), // CstVal!P.allocate(p),
  // 				 new CstVal!Q(q)); // CstVal!Q.allocate(q));
  //   }

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

class CstVecDomain(T, alias R): CstDomain, CstVecElem
{
  enum HAS_RAND_ATTRIB = (! __traits(isSame, R, _esdl__norand));

  BddVec _valvec;
  _esdl__Solver _root;

  Unconst!T _refreshedVal;

  string _name;

  override string name() {
    return _name;
  }

  static if (HAS_RAND_ATTRIB) {
    // BddVec       _domvec;
    uint         _domIndex = uint.max;
    CstStage     _stage = null;
    uint         _resolveLap = 0;
  }

  Unconst!T _shadowValue;

  this(_esdl__Solver root) {
    _root = root;
    fixRangeSet();
  }

  ~this() {
    static if (HAS_RAND_ATTRIB && is(T == enum)) {
      _primBdd.reset();
    }
    _valvec.reset();
  }    

  abstract long value();
  
  long evaluate() {
    static if (HAS_RAND_ATTRIB) {
      if (! this.isRand || this.solved()) {
	return value();
      }
      else {
	assert (false, "Error evaluating " ~ _name);
      }
    }
    else {
      return value();
    }
  }

  S to(S)()
    if (is (S == string)) {
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

  // implementation of CstVecDomain API
  static if (HAS_RAND_ATTRIB && is(T == enum)) {
    BDD _primBdd;
    override BDD getPrimBdd(Buddy buddy) {
      import std.traits;
      if (_primBdd.isZero()) {
	foreach(e; EnumMembers!T) {
	  _primBdd = _primBdd | this.bddvec(buddy).equ(buddy.buildVec(e));
	}
      }
      return _primBdd;
    }
  }
  else {
    override BDD getPrimBdd(Buddy buddy) {
      return buddy.one();
    }
  }

  override uint bitcount() {
    static if (isBoolean!T)         return 1;
    else static if (isIntegral!T)   return T.sizeof * 8;
    else static if (isBitVector!T)  return T.SIZE;
    else static assert(false, "bitcount can not operate on: " ~ T.stringof);
  }

  override bool signed() {
    static if (isVecSigned!T) {
      return true;
    }
    else  {
      return false;
    }
  }

  bool getIntRange(ref IntR rng) {
    return true;
  }

  bool getUniRange(ref UniRange rng) {
    INTTYPE iType;
    if (this.getIntType(iType)) {
      rng.map(iType);
      return true;
    }
    else {
      return false;
    }
  }

  bool getIntType(ref INTTYPE iType) {
    static if (isIntegral!T) {
      import std.traits;
      enum bool signed = isSigned!T;
      enum uint bits = T.sizeof * 8;
    }
    else static if (isBitVector!T) {
      enum bool signed = T.ISSIGNED;
      enum uint bits = T.SIZE;
    }
    else {			// bool
      enum signed = false;
      enum bits = 1;
    }
    static if (bits <= 64) {
      final switch (iType) {
      case INTTYPE.UINT: iType = bits <= 32 ?
	  (signed ? INTTYPE.INT : INTTYPE.UINT) :
	(signed ? INTTYPE.LONG : INTTYPE.ULONG);
	break;
      case INTTYPE.INT: iType = bits <= 32 ?
	  INTTYPE.INT : INTTYPE.LONG;
	break;
      case INTTYPE.ULONG: iType = signed ?
	  INTTYPE.LONG : INTTYPE.ULONG;
	break;
      case INTTYPE.LONG: break;
      }
      return true;
    }
    else {
      return false;
    }
  }


  
  void fixRangeSet() {
    static if (isIntegral!T) {
      static if (RangeT.sizeof == T.sizeof) {
	IntRange!RangeT fixR = IntRange!RangeT(true);
      }
      else {
	IntRange!RangeT fixR =
	  IntRange!RangeT(cast(int) T.min, cast(int) T.max + 1);
      }
      _rs &= fixR;
    }
    static if (isBitVector!T && T.SIZE <= 32) {
      static if (int.sizeof*8 == T.SIZE) {
	IntRange!RangeT fixR = IntRange!RangeT(true);
      }
      else {
	IntRange!RangeT fixR =
	  IntRange!RangeT(cast(int) T.min, cast(int) T.max + 1);
      }
      _rs &= fixR;
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
	static if(isIntegral!T || isBoolean!T) {
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
      else {
	_valueChanged = false;
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
      static if(isIntegral!T || isBoolean!T) {
	newVal = cast(T) value;
      }
      else {
	newVal._setNthWord(value, 0);
      }

      if (newVal != *(getRef())) {
	_valueChanged = true;
      }
      else {
	_valueChanged = false;
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
	else {
	  _valueChanged = false;
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
    assert (_root !is null);
    if (_solvedCycle != _root._cycle) {
      newVal = *(getRef());
      _solvedCycle = _root._cycle;
      if (_valvec.isNull ||
	  newVal != _shadowValue) {
	_shadowValue = newVal;
	_valueChanged = true;
	_valvec.buildVec(_root._esdl__buddy, _shadowValue);
      }
      else {
	_valueChanged = false;
      }
    }
  }

  static if (isIntegral!T) {
    import std.traits;
    static if (isSigned!T) {
      enum bool tSigned = true;
    }
    else {
      enum bool tSigned = false;
    }
    enum size_t tSize = T.sizeof * 8;
    enum bool IS_RANGE = true;
  }
  else static if (isBoolean!T) {
    import std.traits;
    enum bool tSigned = false;
    enum size_t tSize = 1;
    enum bool IS_RANGE = true;
  }
  else static if (isBitVector!T) {
    static if (T.ISSIGNED) {
      enum bool tSigned = true;
    }
    else {
      enum bool tSigned = false;
    }
    static if (T.SIZE <= 64) {
      enum size_t tSize = T.SIZE;
      enum bool IS_RANGE = true;
    }
    else {
      enum bool IS_RANGE = false;
    }
  }
  else {			// boolean
    enum bool IS_RANGE = false;
  }

  static if (IS_RANGE) {
    static if (tSigned) {
      static if (tSize <= 32) {
	alias RangeT = int;
      }
      else static if (tSize <= 64) {
	alias RangeT = long;
      }
    }
    else {
      static if (tSize <= 32) {
	alias RangeT = uint;
      }
      else {
	alias RangeT = ulong;
      }
    }
    IntRangeSet!RangeT _rs;
    // pragma(msg, typeof(_rs).stringof);
  }

  override bool solveRange(_esdl__RandGen randGen) {
    final switch(this._type) {
    case DomType.MONO:
      if (this._rs.isEmpty()) {
	assert(false, "Constraints on domain " ~ this.name() ~
	       " do not converge");
      }
      this.setVal(this._rs.uniform(randGen));
      break;
    case DomType.LAZYMONO:
      auto rns = this._rs.dup();
      foreach (vp; this._varPreds) {
	if (vp._vals.length > 0) {
	  IntRangeSet!RangeT tmprns;
	  if (! vp.getExpr().getUniRangeSet(tmprns)) {
	    return false;
	  }
	  rns &= tmprns;
	}
      }
      if (rns.isEmpty()) {
	assert(false, "Constraints on domain " ~ this.name() ~
	       " do not converge");
      }
      this.setVal(rns.uniform(randGen));
      break;
    case DomType.MAYBEMONO:
      auto rns = this._rs.dup();
      foreach (vp; this._varPreds) {
	if (vp._vals.length > 0) {
	  IntRangeSet!RangeT tmprns;
	  if (! vp.getExpr().getUniRangeSet(tmprns)) {
	    return false;
	  }
	  rns &= tmprns;
	}
      }
      foreach (vp; this._tempPreds) {
	IntRangeSet!RangeT tmprns;
	if (! vp.getExpr().getUniRangeSet(tmprns)) {
	  return false;
	}
	rns &= tmprns;
      }
      if (rns.isEmpty()) {
	assert(false, "Constraints on domain " ~ this.name() ~
	       " do not converge");
      }
      this.setVal(rns.uniform(randGen));
      break;
    case DomType.INDEXEDMONO:
      assert(false);
    case DomType.MULTI:
      return false;
    // default:
    //   assert(false);
    //   break;
    }
    return true;
  }

  override void registerVarPred(CstPredicate varPred) {
    static if(IS_RANGE) {
      foreach (pred; _varPreds) {
	if (pred is varPred) {
	  return;
	}
      }
      if (_type !is DomType.MULTI) {

	IntRangeSet!RangeT rs;
	if (varPred._vals.length == 0) {
	  if (varPred.getExpr().getUniRangeSet(rs)) {
	    _rs &= rs;
	  }
	  else {
	    _type = DomType.MULTI;
	  }
	  // import std.stdio;
	  // writeln(this.name());
	  // writeln(_rs);
	}

      }
      _varPreds ~= varPred;
    }
  }
  
  override void registerValPred(CstPredicate valPred) {
    foreach (pred; _valPreds) {
      if (pred is valPred) {
	return;
      }
    }
    _valPreds ~= valPred;
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


  final override string describe() {
    import std.conv: to;
    string desc = "CstDomain: " ~ name();
    desc ~= "\n	DomType: " ~ _type.to!string();
    if (_type !is DomType.MULTI) {
      desc ~= "\nIntRS: " ~ _rs.toString();
    }
    if (_varPreds.length > 0) {
      desc ~= "\n	Preds:";
      foreach (pred; _varPreds) {
	desc ~= "\n		" ~ pred.name();
      }
      desc ~= "\n";
    }
    if (_tempPreds.length > 0) {
      desc ~= "\n	Temporary Preds:";
      foreach (pred; _tempPreds) {
	desc ~= "\n		" ~ pred.name();
      }
      desc ~= "\n";
    }
    return desc;
  }
}

interface CstBddElem: CstBddExpr
{
  abstract override CstBddElem unroll(CstIteratorBase iter, uint n);

  CstBddElem opBinary(string op)(CstBddElem other)
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

  CstBddElem opUnary(string op)()
  {
    static if(op == "*") {	// "!" in cstx is translated as "*"
      return new CstNotBddExpr(this);
    }
  }

  final CstBddElem implies(CstBddElem other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICIMP);
  }

  final CstBddElem implies(CstVecElem other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICIMP);
  }

  final CstBddElem logicOr(CstBddElem other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICOR);
  }

  final CstBddElem logicOr(CstVecElem other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICOR);
  }

  final CstBddElem logicAnd(CstBddElem other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICAND);
  }

  final CstBddElem logicAnd(CstVecElem other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICAND);
  }

}

class CstIterator(RV): CstIteratorBase, CstVecElem
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
  
  override uint maxVal() {
    if(! getLenVec().solved()) {
      assert(false, "Can not find maxVal since the " ~
	     "Iter Variable is unrollable");
    }
    // import std.stdio;
    // writeln("maxVal for arrVar: ", _arrVar.name(), " is ",
    // 	    _arrVar.arrLen.value);
    return cast(uint) _arrVar.arrLen.value;
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

  override CstIteratorBase unrollIterator(CstIteratorBase iter, uint n) {
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

  // get the list of stages this expression should be avaluated in
  // override CstStage[] getStages() {
  //   return arrVar.arrLen.getStages();
  // }

  override BddVec getBDD(CstStage stage, Buddy buddy) {
    assert (false, "Can not getBDD for a Iter Variable without unrolling");
  }

  // override bool getVal(ref long val) {
  //   return false;
  // }

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

  override bool getUniRange(ref UniRange rng) {
    return false;
  }

  override bool getIntType(ref INTTYPE iType) {
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
    assert (parent !is null);
    super(parent.getSolverRoot());
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

  override _esdl__Solver getSolverRoot() {
    return _parent.getSolverRoot();
  }

  override CstVecLen!RV getResolved() { // always self
    return this;
  }

  BddVec getBDD(CstStage s, Buddy buddy) {
    static if (HAS_RAND_ATTRIB) {
      // auto fparent = _parent.flatten();
      // if (fparent !is _parent) {
      // 	return _parent.flatten().arrLen.getBDD(s, buddy);
      // }
      // else {
      assert (stage() !is null, "stage null for: " ~ name());
      if (this.isRand && stage() is s) {
	return bddvec(buddy);
	// return _domvec;
      }
      else if ((! this.isRand) ||
	      this.isRand && stage().solved()) { // work with the value
	return _valvec;
      }
      else {
	assert (false, "Constraint evaluation in wrong stage");
      }
      // }
    }
    else {
      return _valvec;
    }
  }

  // bool getVal(ref long val) {
  //   static if (HAS_RAND_ATTRIB) {
  //     assert(stage() !is null);
  //     if(! this.isRand || stage().solved()) {
  // 	val = value();
  // 	return true;
  //     }
  //     else {
  // 	return false;
  //     }
  //   }
  //   else {
  //     val = value();
  //     return true;
  //   }
  // }

  // bool isResolved() {
  //   return stage().solved();
  // }
  
  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    // this function will only be called when array lenght is
    // unconstrainted
    markSolved();
    _parent.buildElements(_parent.getLen());
    execCbs();
  }
  
  override void _esdl__doRandomize(_esdl__RandGen randGen, CstStage s) {
    assert (s is stage);
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

  override long value() {
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
    static if (HAS_RAND_ATTRIB) {
      _stage = null;
      _resolveLap = 0;
    }
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
    markAbstractVecDomains(true);
    _parent.setBddContext(pred, vars, vals, iters, idxs, deps);
  }

  override bool getIntType(ref INTTYPE iType) {
    // INTTYPE defaults to UINT
    return true;
  }

  override void execIterCbs() {
    assert(_iterVar !is null);
    _iterVar.unrollCbs();
  }

  override uint* getRef() {
    assert(false);
  }

  override void updateVal() {
    assert(isRand() !is true);
    uint newVal;
    assert(_root !is null);
    if (_solvedCycle != _root._cycle) {
      newVal = cast(uint)_parent.getLen();
      _solvedCycle = _root._cycle;
      if (_valvec.isNull ||
	  newVal != _shadowValue) {
	_shadowValue = cast(uint) newVal;
	_valueChanged = true;
	_valvec.buildVec(_root._esdl__buddy, _shadowValue);
      }
      else {
	_valueChanged = false;
      }
    }
  }
  
  final override bool isActualDomain() {
    return _parent.isActualDomain();
  }

  bool hasAbstractVecDomains() {
    return _parent.hasAbstractVecDomains();
  }

  void markAbstractVecDomains(bool len) {
    _parent.markAbstractVecDomains(len);
  }

  void labelAbstractVecDomains(bool len) {
    assert(len is true);
    if (this._type !is DomType.MULTI) {
      this._type = DomType.MAYBEMONO;
    }
  }
}

abstract class CstValBase: CstVecElem
{
  CstBddExpr _cstExpr;
  
  bool isConst() {
    return true;
  }

  bool isIterator() {
    return false;
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

  BddVec getBDD(CstStage stage, Buddy buddy) {
    return _valvec;
  }

  const(T)* getRef() {
    return &_val;
  }

  // bool getVal(ref long val) {
  //   val = _val;
  //   return true;
  // }

  long evaluate() {
    return _val;
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

   bool getUniRange(ref UniRange rng) {
     assert(false, "UniRange should never be called for a CstVal");
  }

  bool getIntType(ref INTTYPE iType) {
    static if (isIntegral!T) {
      import std.traits;
      enum bool signed = isSigned!T;
      enum uint bits = T.sizeof * 8;
    }
    else static if (isBitVector!T) {
      enum bool signed = T.ISSIGNED;
      enum uint bits = T.SIZE;
    }
    static if (bits <= 64) {
      final switch (iType) {
      case INTTYPE.UINT: iType = bits <= 32 ?
	  (signed ? INTTYPE.INT : INTTYPE.UINT) :
	(signed ? INTTYPE.LONG : INTTYPE.ULONG);
	break;
      case INTTYPE.INT: iType = bits <= 32 ?
	  INTTYPE.INT : INTTYPE.LONG;
	break;
      case INTTYPE.ULONG: iType = signed ?
	  INTTYPE.LONG : INTTYPE.ULONG;
	break;
      case INTTYPE.LONG: break;
      }
      return true;
    }
    else {
      return false;
    }
  }
}


// This class would hold two(bin) vector nodes and produces a vector
// only after processing those two nodes
class CstVec2VecExpr: CstVecElem
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;
  CstBinVecOp _op;

  string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string() ~ " " ~ _rhs.name ~ " )";
  }

  BddVec getBDD(CstStage stage, Buddy buddy) {
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
    case CstBinVecOp.RANGE:
      assert(false, "RANGE is used only in conjunction with Slice expressions!");
    }
  }

  // bool getVal(ref long val) {

  //   long lval;
  //   long rval;
  //   if (! _lhs.getVal(lval)) {
  //     return false;
  //   }
  //   if (! _rhs.getVal(rval)) {
  //     return false;
  //   }

  //   final switch(_op) {
  //   case CstBinVecOp.AND: val = lval &  rval; return true;
  //   case CstBinVecOp.OR:  val = lval |  rval; return true;
  //   case CstBinVecOp.XOR: val = lval ^  rval; return true;
  //   case CstBinVecOp.ADD: val = lval +  rval; return true;
  //   case CstBinVecOp.SUB: val = lval -  rval; return true;
  //   case CstBinVecOp.MUL: val = lval *  rval; return true;
  //   case CstBinVecOp.DIV: val = lval /  rval; return true;
  //   case CstBinVecOp.REM: val = lval %  rval; return true;
  //   case CstBinVecOp.LSH: val = lval << rval; return true;
  //   case CstBinVecOp.RSH: val = lval >> rval; return true;
  //   case CstBinVecOp.BITINDEX:
  //     assert(false, "BITINDEX is not implemented yet!");
  //   }
  // }

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
      assert (false, "BITINDEX is not implemented yet!");
    case CstBinVecOp.RANGE:
      assert (false, "RANGE is used only in conjunction with Slice expressions!");
    }
  }

  override CstVec2VecExpr unroll(CstIteratorBase iter, uint n) {
    return new CstVec2VecExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
  }

  this(CstVecExpr lhs, CstVecExpr rhs, CstBinVecOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
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

  bool getUniRange(ref UniRange rng) {
    INTTYPE iType;
    if (this.getIntType(iType)) {
      rng.map(iType);
      if (_rhs.solved()) {
	assert(! _lhs.solved());
	long rhs = _rhs.evaluate();
	switch(_op) {
	case CstBinVecOp.ADD:
	  UniRangeMod(IntRangeModOp.ADD, rhs).apply(rng);
	  return _lhs.getUniRange(rng);
	case CstBinVecOp.SUB: 
	  UniRangeMod(IntRangeModOp.SUB, rhs).apply(rng);
	  return _lhs.getUniRange(rng);
	default:
	  return false;
	}
      }
      else if (_lhs.solved()) {
	assert(! _rhs.solved());
	long lhs = _lhs.evaluate();
	switch(_op) {
	case CstBinVecOp.ADD:
	  UniRangeMod(IntRangeModOp.ADD, lhs).apply(rng);
	  return _rhs.getUniRange(rng);
	case CstBinVecOp.SUB: 
	  UniRangeMod(IntRangeModOp.SUBD, lhs).apply(rng);
	  return _rhs.getUniRange(rng);
	default:
	  return false;
	}
      }
      else {
	return false;
      }
    }
    else {
      return false;
    }
  }

  bool getIntRange(ref IntR rng) {
    if (_rhs.solved()) {
      assert(! _lhs.solved());
      auto rhs = cast(int) _rhs.evaluate();
      switch(_op) {
      case CstBinVecOp.ADD:
	IntRangeMod!int(IntRangeModOp.ADD, rhs).apply(rng);
	return _lhs.getIntRange(rng);
      case CstBinVecOp.SUB: 
	IntRangeMod!int(IntRangeModOp.SUB, rhs).apply(rng);
	return _lhs.getIntRange(rng);
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
      case CstBinVecOp.SUB: 
	IntRangeMod!int(IntRangeModOp.SUBD, lhs).apply(rng);
	return _rhs.getIntRange(rng);
      default:
	return false;
      }
    }
    else {
      return false;
    }
  }

  bool getIntType(ref INTTYPE iType) {
    bool lvalid, rvalid;
    INTTYPE lType, rType;
    
    lvalid = _lhs.getIntType(lType);
    rvalid = _rhs.getIntType(rType);

    if (lvalid && rvalid) {
      if (lType == INTTYPE.LONG ||
	  rType == INTTYPE.LONG ||
	  iType == INTTYPE.LONG) {
	iType = INTTYPE.LONG;
      }
      else if ((lType == INTTYPE.ULONG ||
		rType == INTTYPE.ULONG ||
		iType == INTTYPE.ULONG) &&
	       (lType == INTTYPE.INT ||
		rType == INTTYPE.INT ||
		iType == INTTYPE.INT))	       {
	iType = INTTYPE.LONG;
      }
      else if (lType == INTTYPE.ULONG ||
	       rType == INTTYPE.ULONG ||
	       iType == INTTYPE.ULONG) {
	iType = INTTYPE.ULONG;
      }
      else if (lType == INTTYPE.INT ||
	       rType == INTTYPE.INT ||
	       iType == INTTYPE.INT) {
	iType = INTTYPE.INT;
      }
      else {
	iType = INTTYPE.UINT;
      }
      return true;
    }
    else {
      return false;
    }
  }

  override bool solved() {
    return _lhs.solved() && _rhs.solved();
  }

}

class CstVecSliceExpr: CstVecElem
{
  CstVecExpr _vec;
  CstVec2VecExpr _range;

  string name() {
    return _vec.name() ~ "[ " ~ _range.name() ~ " ]";
  }

  BddVec getBDD(CstStage stage, Buddy buddy) {
    auto vec  = _vec.getBDD(stage, buddy);
    size_t lvec = cast(size_t) _range._lhs.evaluate();
    size_t rvec = lvec;
    if(_range._rhs is null) {
      rvec = lvec + 1;
    }
    else {
      rvec = cast(size_t) _range._rhs.evaluate();
    }
    return vec[lvec..rvec];
  }

  // bool getVal(ref long val) {
  //   return false;
  // }

  long evaluate() {
    // auto vec  = _vec.evaluate();
    // auto lvec = _lhs.evaluate();
    // auto rvec = _range._rhs.evaluate();

    assert(false, "Can not evaluate a CstVecSliceExpr!");
  }

  override CstVecSliceExpr unroll(CstIteratorBase iter, uint n) {
    if (_range._rhs is null) {
      return new CstVecSliceExpr(_vec.unroll(iter, n), _range._lhs.unroll(iter, n));
    }
    else {
      return new CstVecSliceExpr(_vec.unroll(iter, n),
				 _range._lhs.unroll(iter, n), _range._rhs.unroll(iter, n));
    }
  }

  this(CstVecExpr vec, CstVecExpr lhs, CstVecExpr rhs=null) {
    _vec = vec;
    _range = new CstVec2VecExpr(lhs, rhs, CstBinVecOp.RANGE);
  }

  this(CstVecExpr vec, CstVec2VecExpr range) {
    assert (range._op is CstBinVecOp.RANGE);
    _vec = vec;
    _range = range;
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
    _range.setBddContext(pred, deps, vals, iters, idxs, deps);
  }

  bool getIntRange(ref IntR rng) {
     return false;
  }

  bool getUniRange(ref UniRange rng) {
     return false;
  }

  bool getIntType(ref INTTYPE iType) {
    return false;
  }
  
  override bool solved() {
    return _range.solved() && _vec.solved();
  }
  
}

class CstNotVecExpr: CstVecElem
{
  import std.conv;

  CstVecExpr _expr;

  string name() {
    return "( ~ " ~ _expr.name ~ " )";
  }

  BddVec getBDD(CstStage stage, Buddy buddy) {
    return ~(_expr.getBDD(stage, buddy));
  }

  // bool getVal(ref long val) {
  //   auto retval = _expr.getVal(val);
  //   val = ~val;
  //   return retval;
  // }

  long evaluate() {
    return ~(_expr.evaluate());
  }

  override CstNotVecExpr unroll(CstIteratorBase iter, uint n) {
    return new CstNotVecExpr(_expr.unroll(iter, n));
  }

  this(CstVecExpr expr) {
    _expr = expr;
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

  bool getUniRange(ref UniRange rng) {
     return false;
  }

  bool getIntType(ref INTTYPE iType) {
    return false;
  }

  override bool solved() {
    return _expr.solved();
  }
}

class CstNegVecExpr: CstVecElem
{
  import std.conv;

  CstVecExpr _expr;

  string name() {
    return "( - " ~ _expr.name ~ " )";
  }

  BddVec getBDD(CstStage stage, Buddy buddy) {
    return -(_expr.getBDD(stage, buddy));
  }

  // bool getVal(ref long val) {
  //   auto retval = _expr.getVal(val);
  //   val = -val;
  //   return retval;
  // }

  long evaluate() {
    return -(_expr.evaluate());
  }

  override CstNegVecExpr unroll(CstIteratorBase iter, uint n) {
    return new CstNegVecExpr(_expr.unroll(iter, n));
  }

  this(CstVecExpr expr) {
    _expr = expr;
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

  bool getUniRange(ref UniRange rng) {
     return false;
  }

  bool getIntType(ref INTTYPE iType) {
    return false;
  }

override bool solved() {
    return _expr.solved();
  }
}


class CstBdd2BddExpr: CstBddElem
{
  import std.conv;

  CstBddExpr _lhs;
  CstBddExpr _rhs;
  CstBddOp _op;

  this(CstBddExpr lhs, CstBddExpr rhs, CstBddOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string ~ " " ~ _rhs.name ~ " )";
  }

  BDD getBDD(CstStage stage, Buddy buddy) {
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
    return new CstBdd2BddExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
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

  override bool getUniRangeSet(ref IntRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  override bool getUniRangeSet(ref UIntRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  override bool getUniRangeSet(ref LongRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  override bool getUniRangeSet(ref ULongRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  bool getUniRangeSetImpl(T)(ref T rs) {
    assert(! _lhs.solved());
    assert(! _rhs.solved());

    T lhs;
    T rhs;

    if (_lhs.getUniRangeSet(lhs) is false) return false;
    if (_rhs.getUniRangeSet(rhs) is false) return false;

    final switch(_op) {
    case CstBddOp.LOGICAND: lhs &= rhs; break;
    case CstBddOp.LOGICOR:  lhs |= rhs; break;
    case CstBddOp.LOGICIMP: return false;
    }

    rs = lhs;
    return true;
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

    rs = lhs;
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
class CstIteBddExpr: CstBddElem
{
  string name() {
    return "CstIteBddExpr";
  }

  void setBddContext(CstPredicate pred,
		     ref CstDomain[] vars,
		     ref CstDomain[] vals,
		     ref CstIteratorBase[] iters,
		     ref CstDomain[] idxs,
		     ref CstDomain[] deps) {
    assert(false, "TBD");
  }

  override bool getUniRangeSet(ref IntRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref UIntRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref LongRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref ULongRS rs) {
     return false;
  }

  override bool getIntRangeSet(ref IntRS rs) {
     return false;
  }

  bool cstExprIsNop() {
    return false;
  }

  uint resolveLap() {
    assert(false, "TBD");
  }    

  void resolveLap(uint lap) {
    assert(false, "TBD");
  }    

  CstBddElem unroll(CstIteratorBase iter, uint n) {
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

class CstVec2BddExpr: CstBddElem
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;
  CstBinBddOp _op;

  this(CstVecExpr lhs, CstVecExpr rhs, CstBinBddOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string ~ " " ~ _rhs.name ~ " )";
  }

  BDD getBDD(CstStage stage, Buddy buddy) {
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
    // writeln("RHS: ", _rhs.unroll(iter, n).name());
    // writeln("LHS: ", _lhs.unroll(iter, n).name());
    return new CstVec2BddExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
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

  bool getIntType(ref INTTYPE iType) {
    bool lvalid, rvalid;
    INTTYPE lType, rType;

    assert(iType == INTTYPE.UINT);

    lvalid = _lhs.getIntType(lType);
    rvalid = _rhs.getIntType(rType);

    if (lvalid && rvalid) {
      if (lType == INTTYPE.ULONG ||
	  rType == INTTYPE.ULONG) {
	iType = INTTYPE.ULONG;
      }
      else if ((lType == INTTYPE.LONG ||
		rType == INTTYPE.LONG) &&
	       (lType == INTTYPE.UINT ||
		rType == INTTYPE.UINT))	       {
	iType = INTTYPE.ULONG;
      }
      else if (lType == INTTYPE.LONG ||
	       rType == INTTYPE.LONG) {
	iType = INTTYPE.LONG;
      }
      else if (lType == INTTYPE.UINT ||
	       rType == INTTYPE.UINT) {
	iType = INTTYPE.UINT;
      }
      else {
	iType = INTTYPE.INT;
      }
      return true;
    }
    else {
      return false;
    }
  }
  
  override bool getUniRangeSet(ref IntRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  override bool getUniRangeSet(ref UIntRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  override bool getUniRangeSet(ref LongRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  override bool getUniRangeSet(ref ULongRS rs) {
    return getUniRangeSetImpl(rs);
  }
    
  bool getUniRangeSetImpl(RS)(ref RS rs) {
    static if (is (RS == IntRangeSet!T, T)) {
      if (_rhs.solved()) {
	INTTYPE iType;
	assert(! _lhs.solved(), "Expression: " ~ _lhs.name());
	bool valid = this.getIntType(iType);
	if (valid) {
	  ulong rhs = cast(int) _rhs.evaluate();
	  UniRange rn = UniRange(_op, iType, rhs);
	  valid = _lhs.getUniRange(rn);
	  auto irn = IntRange!T(rn);
	  rs ~= irn;
	}
	return valid;
      }
      else if (_lhs.solved()) {
	INTTYPE iType;
	assert(! _rhs.solved(), "Expression: " ~ _rhs.name());
	bool valid = this.getIntType(iType);
	if (valid) {
	  ulong lhs = cast(int) _lhs.evaluate();
	  UniRange rn = UniRange(_op, iType, lhs);
	  valid = _rhs.getUniRange(rn);
	  auto irn = IntRange!T(rn);
	  rs ~= irn;
	}
	return valid;
      }
      else {
	return false;
      }
    }
    else {
      static assert(false);
    }
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

class CstBddConst: CstBddElem
{
  immutable bool _expr;

  this(bool expr) {
    _expr = expr;
  }

  BDD getBDD(CstStage stage, Buddy buddy) {
    if(_expr) return buddy.one();
    else return buddy.zero();
  }

  string name() {
    if(_expr) return "TRUE";
    else return "FALSE";
  }

  override CstBddConst unroll(CstIteratorBase iter, uint n) {
    return this;
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

  override bool getUniRangeSet(ref IntRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref UIntRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref LongRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref ULongRS rs) {
     return false;
  }

  override bool getIntRangeSet(ref IntRS rng) {
     return false;
  }

  override bool solved() {
    return true;
  }
}

class CstNotBddExpr: CstBddElem
{
  CstBddExpr _expr;

  this(CstBddExpr expr) {
    _expr = expr;
  }

  string name() {
    return "( " ~ "!" ~ " " ~ _expr.name ~ " )";
  }

  BDD getBDD(CstStage stage, Buddy buddy) {
    auto bdd = _expr.getBDD(stage, buddy);
    return (~ bdd);
  }

  override CstNotBddExpr unroll(CstIteratorBase iter, uint n) {
    return new CstNotBddExpr(_expr.unroll(iter, n));
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

  override bool getUniRangeSet(ref IntRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref UIntRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref LongRS rs) {
     return false;
  }

  override bool getUniRangeSet(ref ULongRS rs) {
     return false;
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
  CstBddElem _p;
  CstBddElem _q;
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
  CstBddElem _p;
  CstBddElem _q;
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


auto _esdl__lth(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__lth_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__gte_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p < q);
  }
}

CstVec2BddExpr _esdl__lth_impl(Q)(CstVecExpr left, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__lth_impl(left, qq);
  }

CstVec2BddExpr _esdl__lth_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.LTH);
}

auto _esdl__lte(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__lte_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__gth_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p <= q);
  }
}

CstVec2BddExpr _esdl__lte_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__lte_impl(p, qq);
  }

CstVec2BddExpr _esdl__lte_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.LTE);
}

auto _esdl__gth(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__gth_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__lte_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p > q);
  }
}

CstVec2BddExpr _esdl__gth_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__gth_impl(p, qq);
  }

CstVec2BddExpr _esdl__gth_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.GTH);
}

auto _esdl__gte(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__gte_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__lth_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p >= q);
  }
}

CstVec2BddExpr _esdl__gte_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__gte_impl(p, qq);
  }

CstVec2BddExpr _esdl__gte_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.GTE);
}

auto _esdl__equ(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__equ_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__equ_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p == q);
  }
}

CstVec2BddExpr _esdl__equ_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__equ_impl(p, qq);
  }

CstVec2BddExpr _esdl__equ_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.EQU);
}

auto _esdl__neq(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__neq_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__neq_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p != q);
  }
}
CstVec2BddExpr _esdl__neq_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__neq(p, qq);
  }

CstVec2BddExpr _esdl__neq_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.NEQ);
}

