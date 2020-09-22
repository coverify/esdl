module esdl.rand.expr;

import esdl.rand.intr;
import esdl.rand.dist;

import esdl.solver.base: CstSolver;

import esdl.rand.misc: rand, _esdl__RandGen, isVecSigned, Unconst;
import esdl.rand.misc: CstBinaryOp, CstCompareOp, CstLogicOp,
  CstUnaryOp, CstSliceOp, writeHexString;

import esdl.rand.base;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.data.bvec: isBitVector, toBitVec;
import esdl.data.charbuf;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray,
  isDynamicArray, isSomeChar, EnumMembers, isSigned, OriginalType;

abstract class CstVecTerm: CstVecExpr
{

  final CstLogicTerm toBoolExpr() {
    auto zero = new CstVecValue!int(0); // CstVecValue!int.allocate(0);
    return new CstVec2LogicExpr(this, zero, CstCompareOp.NEQ);
  }

  // abstract CstVecExpr unroll(CstIterator iter, uint n);

  CstVec2VecExpr opBinary(string op)(CstVecTerm other)
  {
    static if(op == "&") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.AND);
    }
    static if(op == "|") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.OR);
    }
    static if(op == "^") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.XOR);
    }
    static if(op == "+") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.ADD);
    }
    static if(op == "-") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.SUB);
    }
    static if(op == "*") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.MUL);
    }
    static if(op == "/") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.DIV);
    }
    static if(op == "%") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.REM);
    }
    static if(op == "<<") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.LSH);
    }
    static if(op == ">>") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.RSH);
    }
    static if(op == ">>>") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.LRSH);
    }
    static if(op == "~") {
      return new CstVec2VecExpr(this, other, CstBinaryOp.RANGE);
    }
  }

  CstVec2VecExpr opBinary(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
  	auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
  	static if(op == "&") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.AND);
  	}
  	static if(op == "|") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.OR);
  	}
  	static if(op == "^") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.XOR);
  	}
  	static if(op == "+") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.ADD);
  	}
  	static if(op == "-") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.SUB);
  	}
  	static if(op == "*") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.MUL);
  	}
  	static if(op == "/") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.DIV);
  	}
  	static if(op == "%") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.REM);
  	}
  	static if(op == "<<") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.LSH);
  	}
  	static if(op == ">>") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.RSH);
  	}
  	static if(op == ">>>") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.LRSH);
  	}
  	static if(op == "~") {
  	  return new CstVec2VecExpr(this, qq, CstBinaryOp.RANGE);
  	}
      }

  CstVec2VecExpr opBinaryRight(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
	auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
	static if(op == "&") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.AND);
	}
	static if(op == "|") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.OR);
	}
	static if(op == "^") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.XOR);
	}
	static if(op == "+") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.ADD);
	}
	static if(op == "-") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.SUB);
	}
	static if(op == "*") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.MUL);
	}
	static if(op == "/") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.DIV);
	}
	static if(op == "%") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.REM);
	}
	static if(op == "<<") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.LSH);
	}
	static if(op == ">>") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.RSH);
	}
	static if(op == ">>>") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.LRSH);
	}
	static if(op == "~") {
	  return new CstVec2VecExpr(qq, this, CstBinaryOp.RANGE);
	}
      }

  // final CstVecSliceExpr opSlice(CstVecTerm lhs, CstVecTerm rhs) {
  //   return new CstVecSliceExpr(this, lhs, rhs);
  // }

  final CstVecSliceExpr opIndex(CstRangeExpr range) {
    return new CstVecSliceExpr(this, range);
  }

  // final CstVecIndexExpr opIndex(CstVecTerm index) {
  //   return new CstVecIndexExpr(this, index);
  // }

  CstNotLogicExpr opUnary(string op)() if(op == "*") {
    return new CstNotLogicExpr(this.toBoolExpr());
  }
  CstNotVecExpr opUnary(string op)() if(op == "~") {
    return new CstNotVecExpr(this);
  }
  CstNegVecExpr opUnary(string op)() if(op == "-") {
    return new CstNegVecExpr(this);
  }

  final CstLogicTerm inside(CstRangeExpr range) {
    if (range._rhs is null) {
      return new CstVec2LogicExpr(this, range._lhs, CstCompareOp.EQU);
    }
    else {
      CstLogicTerm lhs = new CstVec2LogicExpr(this, range._lhs, CstCompareOp.GTE);
      CstLogicTerm rhs;
      if (range._inclusive) rhs = new CstVec2LogicExpr(this, range._rhs, CstCompareOp.LTE);
      else rhs = new CstVec2LogicExpr(this, range._rhs, CstCompareOp.LTH);
      return lhs & rhs;
    }
  }
}

class CstVecDomain(T, rand RAND_ATTR): CstDomain
{
  enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();

  _esdl__Proxy _root;

  Unconst!T _shadowValue;

  string _name;

  override string name() {
    return _name;
  }

  uint         _domIndex = uint.max;
  uint         _resolveLap = 0;
  
  override void annotate(CstPredGroup group) {
    if (_domN == uint.max) {
      if (this.isSolved()) {
	_domN = group.addVariable(this);
	if (_varN == uint.max) _varN = _root.indexVar();
      }
      else {
	_domN = group.addDomain(this);
      }
    }
  }

  static if (is (T == enum)) {
    alias OT = OriginalType!T;

    T[] _enumSortedVals;

    void _enumSortedValsPopulate() {
      import std.algorithm.sorting: sort;
      _enumSortedVals = cast(T[]) [EnumMembers!T];
      _enumSortedVals.sort();
    }


    static if (isIntegral!OT) {
      private void _addRangeConstraint(CstSolver solver, OT min, OT max) {
	if (min == max) {
	  solver.pushToEvalStack(this);
	  solver.pushToEvalStack(min, OT.sizeof*8, isSigned!OT);
	  solver.processEvalStack(CstCompareOp.EQU);
	}
	else {
	  solver.pushToEvalStack(this);
	  solver.pushToEvalStack(min, OT.sizeof*8, isSigned!OT);
	  solver.processEvalStack(CstCompareOp.GTE);
	  solver.pushToEvalStack(this);
	  solver.pushToEvalStack(max, OT.sizeof*8, isSigned!OT);
	  solver.processEvalStack(CstCompareOp.LTE);
	  solver.processEvalStack(CstLogicOp.LOGICAND);
	}
      }
    }
    else static if (isBitVector!OT && OT.SIZE <= 64) {
      private void _addRangeConstraint(CstSolver solver, OT min, OT max) {
	if (min == max) {
	  solver.pushToEvalStack(this);
	  solver.pushToEvalStack(cast(ulong) min, OT.SIZE, OT.ISSIGNED);
	  solver.processEvalStack(CstCompareOp.EQU);
	}
	else {
	  solver.pushToEvalStack(this);
	  solver.pushToEvalStack(cast(ulong) min, OT.SIZE, OT.ISSIGNED);
	  solver.processEvalStack(CstCompareOp.GTE);
	  solver.pushToEvalStack(this);
	  solver.pushToEvalStack(cast(ulong) max, OT.SIZE, OT.ISSIGNED);
	  solver.processEvalStack(CstCompareOp.LTE);
	  solver.processEvalStack(CstLogicOp.LOGICAND);
	}
      }
    }
    else {
      private void _addRangeConstraint(CstSolver solver, OT min, OT max) {
	assert (false);
      }
    }
  }


   override bool visitDomain(CstSolver solver) {
    static if (is (T == enum)) {
      uint count;
      if (_enumSortedVals.length == 0) {
	_enumSortedValsPopulate();
      }
      T min;
      T max;
      foreach (i, val; _enumSortedVals) {
	if (i == 0) {
	  min = val;
	  max = val;
	}
	else {
	  if (val - max == 1) {
	    max = val;
	  }
	  else {
	    _addRangeConstraint(solver, min, max);
	    count += 1;
	    min = val;
	    max = val;
	  }
	}
      }
      _addRangeConstraint(solver, min, max);
      for (uint i=0; i!=count; ++i) {
	solver.processEvalStack(CstLogicOp.LOGICOR);
      }
      return true;
    }
    else {
      return false;
    }
  }

  override void visit(CstSolver solver) {
    // assert (solver !is null);
    solver.pushToEvalStack(this);
  }

  override void writeExprString(ref Charbuf str) {
    if (this.isSolved()) {
      str ~= 'V';
      if (_domN < 256) (cast(ubyte) _domN).writeHexString(str);
      else (cast(ushort) _domN).writeHexString(str);
      str ~= '#';
      if (_varN < 256) (cast(ubyte) _varN).writeHexString(str);
      else (cast(ushort) _varN).writeHexString(str);
    }
    else {
      str ~= 'R';
      if (_domN < 256) (cast(ubyte) _domN).writeHexString(str);
      else (cast(ushort) _domN).writeHexString(str);
      str ~= T.stringof;
      // static if (isBitVector!T) {
      // 	static if (T.ISSIGNED) {
      // 	  str ~= 'S';
      // 	}
      // 	else {
      // 	  str ~= 'U';
      // 	}
      // 	if (T.SIZE < 256) (cast(ubyte) T.SIZE).writeHexString(str);
      // 	else (cast(ushort) T.SIZE).writeHexString(str);
      // }
      // else static if (is (T == enum)) {
      // 	str ~= T.stringof;
      // }
      // else static if (isIntegral!T) {
      // 	static if (isSigned!T) {
      // 	  str ~= 'S';
      // 	}
      // 	else {
      // 	  str ~= 'U';
      // 	}
      // 	(cast(ubyte) (T.sizeof * 8)).writeHexString(str);
      // }
      // else static if (isBoolean!T) {
      // 	str ~= 'U';
      // 	(cast(ubyte) 1).writeHexString(str);
      // }
    }
  }

  this(string name, _esdl__Proxy root) {
    _name = name;
    _root = root;
    fixRangeSet();
  }

  ~this() {
  }    

  override long evaluate() {
    static if (HAS_RAND_ATTRIB) {
      if (! this.isRand || this.isSolved()) {
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

  // S to(S)()
  //   if (is (S == string)) {
  //     import std.conv;
  //     static if (HAS_RAND_ATTRIB) {
  // 	if (isRand) {
  // 	  return "RAND#" ~ _name ~ ":" ~ value().to!string();
  // 	}
  // 	else {
  // 	  return "VAL#" ~ _name ~ ":" ~ value().to!string();
  // 	}
  //     }
  //     else {
  // 	return "VAR#" ~ _name ~ ":" ~ value().to!string();
  //     }
  //   }

  // override string toString() {
  //   return this.to!string();
  // }

  override uint bitcount() {
    static if (isBoolean!T)         return 1;
    else static if (isIntegral!T || isSomeChar!T)   return T.sizeof * 8;
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

  override bool getIntRange(ref IntR rng) {
    return true;
  }

  override bool getUniRange(ref UniRange rng) {
    INTTYPE iType;
    if (this.getIntType(iType)) {
      rng.map(iType);
      return true;
    }
    else {
      return false;
    }
  }

  override bool getIntType(ref INTTYPE iType) {
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
      // final
      switch (iType) {
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
      default: assert(false);
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

  override void reset() {
    _state = State.INIT;
    _resolveLap = 0;
  }
  
  override uint resolveLap() {
    if (isSolved()) return 0;
    else return _resolveLap;
  }

  override void resolveLap(uint lap) {
    if (isSolved()) _resolveLap = 0;
    else _resolveLap = lap;
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

  override void setVal(ulong val) {
    static if (isBitVector!T) {
      assert (T.SIZE <= 64);
    }
    static if (HAS_RAND_ATTRIB) {
      Unconst!T newVal;
      static if(isIntegral!T || isBoolean!T) {
	newVal = cast(T) val;
      }
      else {
	newVal._setNthWord(val, 0);
      }
      assert (getRef() !is null);
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
      if (! isSolved()) {
	Unconst!T newVal;
	randGen.gen(newVal);
	if (newVal != *(getRef())) {
	  _valueChanged = true;
	  *(getRef()) = newVal;
	}
	else {
	  _valueChanged = false;
	}
      }
    }
    else {
      assert(false);
    }
  }

  bool _valueChanged = true;

  override bool hasChanged() {
    return _valueChanged;
  }
  
  override bool updateVal() {
    assert(isRand() !is true);
    Unconst!T newVal;
    assert (_root !is null);
    if (! this.isSolved()) {
      newVal = *(getRef());
      this.markSolved();
      if (newVal != _shadowValue) {
	_shadowValue = newVal;
	_valueChanged = true;
	return true;
      }
      else {
	_valueChanged = false;
	return false;
      }
    }
    return true;
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
    enum bool tSigned = false;
    enum size_t tSize = 1;
    enum bool IS_RANGE = true;
  }
  else static if (isSomeChar!T) {
    enum bool tSigned = false;
    enum size_t tSize = T.sizeof * 8;
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
    // final
    switch(this._type) {
    case DomType.TRUEMONO:
      if (this._rs.isEmpty()) {
	assert(false, "Constraints on domain " ~ this.name() ~
	       " do not converge");
      }
      this.setVal(this._rs.uniform(randGen));
      break;
    case DomType.LAZYMONO:
      auto rns = this._rs.dup();
      foreach (rp; this._rndPreds) {
	if (rp._vars.length > 0) {
	  IntRangeSet!RangeT tmprns;
	  if (! rp.getExpr().getUniRangeSet(tmprns)) {
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
      foreach (rp; this._rndPreds) {
	if (rp._vars.length > 0) {
	  IntRangeSet!RangeT tmprns;
	  if (! rp.getExpr().getUniRangeSet(tmprns)) {
	    return false;
	  }
	  rns &= tmprns;
	}
      }
      foreach (tp; this._tempPreds) {
	IntRangeSet!RangeT tmprns;
	if (! tp.getExpr().getUniRangeSet(tmprns)) {
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
    default:
      assert(false);
    }
    return true;
  }

  override void registerRndPred(CstPredicate rndPred) {
    static if(IS_RANGE) {
      foreach (pred; _rndPreds) {
	if (pred is rndPred) {
	  return;
	}
      }
      if (_type !is DomType.MULTI && !rndPred.isDist()) {

	IntRangeSet!RangeT rs;
	if (rndPred._vars.length == 0) {
	  if (rndPred.getExpr().getUniRangeSet(rs)) {
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
      _rndPreds ~= rndPred;
    }
  }
  
  // override void registerVarPred(CstPredicate varPred) {
  //   foreach (pred; _varPreds) {
  //     if (pred is varPred) {
  // 	return;
  //     }
  //   }
  //   _varPreds ~= varPred;
  // }
  
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


  final override void markSolved() {
    super.markSolved();
    static if (HAS_RAND_ATTRIB) {
      if (this.isRand()) {
	_domN = uint.max;
      }
    }
  }
  
  final override string describe() {
    import std.conv: to;
    string desc = "CstDomain: " ~ name();
    desc ~= "\n	DomType: " ~ _type.to!string();
    if (_type !is DomType.MULTI) {
      desc ~= "\nIntRS: " ~ _rs.toString();
    }
    if (_rndPreds.length > 0) {
      desc ~= "\n	Preds:";
      foreach (pred; _rndPreds) {
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

abstract class CstLogicTerm: CstLogicExpr
{
  abstract override CstLogicTerm unroll(CstIterator iter, uint n);

  CstLogicTerm opBinary(string op)(CstLogicTerm other)
  {
    static if(op == "&") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICAND);
    }
    static if(op == "|") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICOR);
    }
    static if(op == ">>") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICIMP);
    }
  }

  CstLogicTerm opOpAssign(string op)(CstLogicTerm other)
  {
    static if(op == ">>>") {
      return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICIMP);
    }
  }
  
  CstLogicTerm opUnary(string op)() if(op == "*")
  {
    static if(op == "*") {	// "!" in cstx is translated as "*"
      return new CstNotLogicExpr(this);
    }
  }

  CstLogicTerm opUnary(string op)() if(op == "~")
  {
    static if(op == "~") {	// "!" in cstx is translated as "*"
      return new CstNotLogicExpr(this);
    }
  }

  final CstLogicTerm implies(CstLogicTerm other)
  {
    return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICIMP);
  }

  final CstLogicTerm implies(CstVecTerm other)
  {
    return new CstLogic2LogicExpr(this, other.toBoolExpr(), CstLogicOp.LOGICIMP);
  }

  final CstLogicTerm logicOr(CstLogicTerm other)
  {
    return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICOR);
  }

  final CstLogicTerm logicOr(CstVecTerm other)
  {
    return new CstLogic2LogicExpr(this, other.toBoolExpr(), CstLogicOp.LOGICOR);
  }

  final CstLogicTerm logicAnd(CstLogicTerm other)
  {
    return new CstLogic2LogicExpr(this, other, CstLogicOp.LOGICAND);
  }

  final CstLogicTerm logicAnd(CstVecTerm other)
  {
    return new CstLogic2LogicExpr(this, other.toBoolExpr(), CstLogicOp.LOGICAND);
  }

}

class CstArrIterator(RV): CstIterator
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
  
  override uint size() {
    if(! getLenVec().isSolved()) {
      assert(false, "Can not find size since the " ~
	     "Iter Variable is unrollable");
    }
    // import std.stdio;
    // writeln("size for arrVar: ", _arrVar.name(), " is ",
    // 	    _arrVar.arrLen.value);
    return cast(uint) _arrVar.arrLen.value;
  }

  override string name() {
    string n = _arrVar.name();
    return n ~ "->iterator";
  }

  override string fullName() {
    string n = _arrVar.fullName();
    return n ~ "->iterator";
  }

  override string describe() {
    return name();
  }

  // while an iterator is a singleton wrt to an array, the array
  // itself could have multiple object instances in case it is not
  // concrete -- eg foo[foo.iter].iter
  override bool opEquals(Object other) {
    auto rhs = cast(typeof(this)) other;
    if (rhs is null) return false;
    else return (_arrVar == rhs._arrVar);
  }

  override CstVecExpr unroll(CstIterator iter, uint n) {
    if(this !is iter) {
      return _arrVar.unroll(iter,n).arrLen().makeIterVar();
    }
    else {
      return new CstVecValue!size_t(n); // CstVecValue!size_t.allocate(n);
    }
  }

  override CstIterator unrollIterator(CstIterator iter, uint n) {
    assert(this !is iter);
    return _arrVar.unroll(iter,n).arrLen().makeIterVar();
  }

  override uint resolveLap() {
    assert (false, "resolveLap should never be called on CstArrIterator");
  }

  override void resolveLap(uint lap) {}

  override void visit(CstSolver solver) {
    assert (false, "Can not visit an Iter Variable without unrolling");
  }

  // override bool getVal(ref long val) {
  //   return false;
  // }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    deps ~= getLenVec();
    iters ~= this;
  }

  override bool isSolved() {
    return _arrVar._arrLen.isSolved();
  }


  override void writeExprString(ref Charbuf str) {
    // assert(false);
  }
}

class CstArrLength(RV): CstVecDomain!(uint, RV.RAND), CstVecPrim
{

  enum HAS_RAND_ATTRIB = RV.RAND.isRand();

  CstArrIterator!RV _iterVar;

  RV _parent;

  string _name;

  CstVecPrim[] _preReqs;

  override string name() {
    return _name;
  }

  override string fullName() {
    return _parent.fullName() ~ "->length";
  }

  this(string name, RV parent) {
    assert (parent !is null);
    super(name, parent.getProxyRoot());
    _name = name;
    _parent = parent;
    _iterVar = new CstArrIterator!RV(_parent);
  }

  ~this() { }

  override _esdl__Proxy getProxyRoot() {
    return _parent.getProxyRoot();
  }

  override CstArrLength!RV getResolved() { // always self
    return this;
  }

  override void visit(CstSolver solver) {
    solver.pushToEvalStack(this);
  }

  override void randomizeIfUnconstrained(_esdl__Proxy proxy) {
    if (! isSolved()) {
      if (_rndPreds.length == 0) {
	_esdl__doRandomize(getProxyRoot()._esdl__getRandGen());
	proxy.solvedSome();
	markSolved();
	proxy.addSolvedDomain(this);
	execCbs();
      }
    }
    if (! isRand()) {
      _parent.buildElements(_parent.getLen());
    }
    execCbs();
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    // this function will only be called when array lenght is
    // unconstrainted
    _parent.buildElements(_parent.getLen());
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

  void iterVar(CstArrIterator!RV var) {
    _iterVar = var;
  }

  CstArrIterator!RV iterVar() {
    return _iterVar;
  }

  CstArrIterator!RV makeIterVar() {
    if(_iterVar is null) {
      _iterVar = new CstArrIterator!RV(_parent);
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

  override CstVecExpr unroll(CstIterator iter, uint n) {
    return _parent.unroll(iter,n).arrLen();
  }

  void solveBefore(CstVecPrim other) {
    other.addPreRequisite(this);
  }

  void addPreRequisite(CstVecPrim domain) {
    _preReqs ~= domain;
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
    bool listed;
    foreach (rnd; rnds) {
      if (rnd is this) {
	listed = true;
	break;
      }
    }
    if (listed is false) {
      rnds ~= this;
    }
    static if (HAS_RAND_ATTRIB) {
      if (! this.isStatic()) {
	if (_type <= DomType.LAZYMONO) _type = DomType.MAYBEMONO;
      }
    }
    _parent.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
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

  override bool updateVal() {
    assert(isRand() !is true);
    uint newVal;
    assert(_root !is null);
    if (! this.isSolved()) {
      newVal = cast(uint)_parent.getLen();
      this.markSolved();
      if (newVal != _shadowValue) {
	_shadowValue = cast(uint) newVal;
	_valueChanged = true;
	return true;
      }
      else {
	_valueChanged = false;
	return false;
      }
    }
    return true;
  }
  
  final override bool isStatic() {
    return _parent.isStatic();
  }

}

abstract class CstValue: CstVecTerm
{
  CstLogicExpr _cstExpr;
  
  override bool isConst() {
    return true;
  }

  override bool isIterator() {
    return false;
  }

  override CstVecExpr unroll(CstIterator l, uint n) {
    return this;
  }

  abstract long value();
  abstract bool signed();
  abstract uint bitcount();
}

auto _esdl__cstVal(T)(T val) {
  return new CstVecValue!(T)(val); // CstVecValue!(T).allocate(val);
}

class CstVecValue(T = int): CstValue
{
  static if (isIntegral!T) {
    import std.traits;
    enum bool SIGNED = isSigned!T;
    enum uint BITCOUNT = T.sizeof * 8;
  }
  else static if (isBitVector!T) {
    enum bool SIGNED = T.ISSIGNED;
    enum uint BITCOUNT = T.SIZE;
  }

  override bool signed() {
    return SIGNED;
  }

  override uint bitcount() {
    return BITCOUNT;
  }

  override long value() {
    return _val;
  }

  import std.conv;

  // static Allocator _allocator;

  // static this() {
  //   CstVecValue!T._allocator = new Allocator;
  //   CstValueAllocator.allocators ~= CstVecValue!T._allocator;
  // }

  T _val;			// the value of the constant

  override string describe() {
    return _val.to!string();
  }

  // static CstVecValue!T allocate(T value) {
  //   Allocator allocator = _allocator;
  //   if (allocator is null) {
  //     allocator = new Allocator;
  //     _allocator = allocator;
  //     CstValueAllocator.allocators ~= allocator;
  //   }

  //   // return new CstVecValue!T(value);
  //   return allocator.allocate(value);
  // }

  this(T value) {
    _val = value;
  }

  ~this() {
  }

  override void visit(CstSolver solver) {
    solver.pushToEvalStack(this);
  }

  const(T)* getRef() {
    return &_val;
  }

  // bool getVal(ref long val) {
  //   val = _val;
  //   return true;
  // }

  override long evaluate() {
    return _val;
  }

  override uint resolveLap() {
    return 0;			// const
  }

  override void resolveLap(uint lap) {}

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  override bool isSolved() {
    return true;
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    vals ~= this;
  }

  override bool getIntRange(ref IntR rng) {
    assert(false, "getIntRange should never be called for a CstVecValue");
  }

  override bool getUniRange(ref UniRange rng) {
    assert(false, "UniRange should never be called for a CstVecValue");
  }

  override bool getIntType(ref INTTYPE iType) {
    static if (BITCOUNT <= 64) {
      // final
      switch (iType) {
      case INTTYPE.UINT: iType = BITCOUNT <= 32 ?
	  (SIGNED ? INTTYPE.INT : INTTYPE.UINT) :
	(SIGNED ? INTTYPE.LONG : INTTYPE.ULONG);
	break;
      case INTTYPE.INT: iType = BITCOUNT <= 32 ?
	  INTTYPE.INT : INTTYPE.LONG;
	break;
      case INTTYPE.ULONG: iType = SIGNED ?
	  INTTYPE.LONG : INTTYPE.ULONG;
	break;
      case INTTYPE.LONG: break;
      default: assert(false);
      }
      return true;
    }
    else {
      return false;
    }
  }


  override void writeExprString(ref Charbuf str) {
    // VSxxxxx or VUxxxxx
    str ~= 'V';
    static if (isBoolean!T) {
      str ~= 'U';
    }
    static if (isIntegral!T) {
      static if (isSigned!T) {
	str ~= 'S';
      }
      else {
	str ~= 'U';
      }
    }
    else {
      static if (T.ISSIGNED) {
	str ~= 'S';
      }
      else {
	str ~= 'U';
      }
    }
    _val.writeHexString(str);
  }
}


// This class would hold two(bin) vector nodes and produces a vector
// only after processing those two nodes
class CstVec2VecExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;
  CstBinaryOp _op;

  override string describe() {
    return "( " ~ _lhs.describe ~ " " ~ _op.to!string() ~ " " ~ _rhs.describe ~ " )";
  }

  override void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  //   long lval;
  //   long rval;
  //   if (! _lhs.getVal(lval)) {
  //     return false;
  //   }
  //   if (! _rhs.getVal(rval)) {
  //     return false;
  //   }

  //   final switch(_op) {
  //   case CstBinaryOp.AND: val = lval &  rval; return true;
  //   case CstBinaryOp.OR:  val = lval |  rval; return true;
  //   case CstBinaryOp.XOR: val = lval ^  rval; return true;
  //   case CstBinaryOp.ADD: val = lval +  rval; return true;
  //   case CstBinaryOp.SUB: val = lval -  rval; return true;
  //   case CstBinaryOp.MUL: val = lval *  rval; return true;
  //   case CstBinaryOp.DIV: val = lval /  rval; return true;
  //   case CstBinaryOp.REM: val = lval %  rval; return true;
  //   case CstBinaryOp.LSH: val = lval << rval; return true;
  //   case CstBinaryOp.RSH: val = lval >> rval; return true;
  //   case CstBinaryOp.BITINDEX:
  //     assert(false, "BITINDEX is not implemented yet!");
  //   }
  // }

  override long evaluate() {
    auto lvec = _lhs.evaluate();
    auto rvec = _rhs.evaluate();

    final switch(_op) {
    case CstBinaryOp.AND: return lvec &  rvec;
    case CstBinaryOp.OR:  return lvec |  rvec;
    case CstBinaryOp.XOR: return lvec ^  rvec;
    case CstBinaryOp.ADD: return lvec +  rvec;
    case CstBinaryOp.SUB: return lvec -  rvec;
    case CstBinaryOp.MUL: return lvec *  rvec;
    case CstBinaryOp.DIV: return lvec /  rvec;
    case CstBinaryOp.REM: return lvec %  rvec;
    case CstBinaryOp.LSH: return lvec << rvec;
    case CstBinaryOp.RSH: return lvec >> rvec;
    case CstBinaryOp.LRSH: return lvec >>> rvec;
    }
  }

  override CstVec2VecExpr unroll(CstIterator iter, uint n) {
    return new CstVec2VecExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
  }

  this(CstVecExpr lhs, CstVecExpr rhs, CstBinaryOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  override uint resolveLap() {
    auto lhs = _lhs.resolveLap();
    auto rhs = _rhs.resolveLap();
    if (rhs > lhs) return rhs;
    else return lhs;
  }

  override void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }
  
  override bool isConst() {
    return _lhs.isConst() && _rhs.isConst();
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
    _lhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
  }

  override bool getUniRange(ref UniRange rng) {
    INTTYPE iType;
    if (this.getIntType(iType)) {
      rng.map(iType);
      if (_rhs.isSolved()) {
	assert(! _lhs.isSolved());
	long rhs = _rhs.evaluate();
	switch(_op) {
	case CstBinaryOp.ADD:
	  UniRangeMod(IntRangeModOp.ADD, rhs).apply(rng);
	  return _lhs.getUniRange(rng);
	case CstBinaryOp.SUB: 
	  UniRangeMod(IntRangeModOp.SUB, rhs).apply(rng);
	  return _lhs.getUniRange(rng);
	default:
	  return false;
	}
      }
      else if (_lhs.isSolved()) {
	assert(! _rhs.isSolved());
	long lhs = _lhs.evaluate();
	switch(_op) {
	case CstBinaryOp.ADD:
	  UniRangeMod(IntRangeModOp.ADD, lhs).apply(rng);
	  return _rhs.getUniRange(rng);
	case CstBinaryOp.SUB: 
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

  override bool getIntRange(ref IntR rng) {
    if (_rhs.isSolved()) {
      assert(! _lhs.isSolved());
      auto rhs = cast(int) _rhs.evaluate();
      switch(_op) {
      case CstBinaryOp.ADD:
	IntRangeMod!int(IntRangeModOp.ADD, rhs).apply(rng);
	return _lhs.getIntRange(rng);
      case CstBinaryOp.SUB: 
	IntRangeMod!int(IntRangeModOp.SUB, rhs).apply(rng);
	return _lhs.getIntRange(rng);
      default:
	return false;
      }
    }
    else if (_lhs.isSolved()) {
      assert(! _rhs.isSolved());
      auto lhs = cast(int) _lhs.evaluate();
      switch(_op) {
      case CstBinaryOp.ADD:
	IntRangeMod!int(IntRangeModOp.ADD, lhs).apply(rng);
	return _rhs.getIntRange(rng);
      case CstBinaryOp.SUB: 
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

  override bool getIntType(ref INTTYPE iType) {
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

  override bool isSolved() {
    return _lhs.isSolved() && _rhs.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    str ~= '(';
    str ~= _op.to!string;
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ')';
  }
}

class CstRangeExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;

  bool _inclusive = false;

  override string describe() {
    if (_rhs is null)
      return "( " ~ _lhs.describe ~ " )";
    else if (_inclusive)
      return "( " ~ _lhs.describe ~ " : " ~ _rhs.describe ~ " )";
    else
      return "( " ~ _lhs.describe ~ " .. " ~ _rhs.describe ~ " )";
  }

  override void visit(CstSolver solver) {
    // assert (_lhs.isSolved());
    // assert (_rhs.isSolved());
    // solver.pushIndexToEvalStack(_lhs.evaluate());
    // solver.pushIndexToEvalStack(_rhs.evaluate());
    // if (_inclusive) solver.processEvalStack(CstSliceOp.SLICEINC);
    // else solver.processEvalStack(CstSliceOp.SLICE);
    assert (false);
  }

  override long evaluate() {
    assert (_rhs is null);
    return _lhs.evaluate();
  }

  override CstRangeExpr unroll(CstIterator iter, uint n) {
    if (_rhs is null)
      return new CstRangeExpr(_lhs.unroll(iter, n), null, _inclusive);
    else
      return new CstRangeExpr(_lhs.unroll(iter, n),
			      _rhs.unroll(iter, n), _inclusive);
  }

  this(CstVecExpr lhs, CstVecExpr rhs, bool inclusive=false) {
    _lhs = lhs;
    _rhs = rhs;
    _inclusive = inclusive;
  }

  override uint resolveLap() {
    // auto lhs = _lhs.resolveLap();
    // auto rhs = _rhs.resolveLap();
    // if (rhs > lhs) return rhs;
    // else return lhs;
    assert (false);
  }

  override void resolveLap(uint lap) {
    // _lhs.resolveLap(lap);
    // _rhs.resolveLap(lap);
    assert (false);
  }
  
  override bool isConst() {
    return _rhs is null && _lhs.isConst();
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
    _lhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
  }

  override bool getUniRange(ref UniRange rng) {
    assert (false);
  }

  override bool getIntRange(ref IntR rng) {
    assert (false);
  }

  override bool getIntType(ref INTTYPE iType) {
    assert (false);
  }

  override bool isSolved() {
    return _lhs.isSolved() && (_rhs is null || _rhs.isSolved());
  }

  override void writeExprString(ref Charbuf str) {
    _lhs.writeExprString(str);
    if (_rhs !is null) {
      if (_inclusive) str ~= " : ";
      else str ~= " .. ";
      _rhs.writeExprString(str);
    }
  }
}

class CstDistRangeExpr: CstVecTerm
{
  import std.conv;

  CstRangeExpr _range;
  CstVecExpr   _weight;
  bool         _perItem = false;

  override string describe() {
    string str = "( " ~ _range.describe;
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.describe() ~ " )";
    return str;
  }

  override void visit(CstSolver solver) {
    assert (false);
  }

  override long evaluate() {
    assert (false);
  }

  override CstDistRangeExpr unroll(CstIterator iter, uint n) {
    return this;
  }

  this(CstRangeExpr range, CstVecExpr weight, bool perItem=false) {
    _range = range;
    _weight = weight;
    _perItem = perItem;
  }

  override uint resolveLap() {
    assert (false);
  }

  override void resolveLap(uint lap) {
    assert (false);
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
			ref CstDomain[] deps) { }

  override bool getUniRange(ref UniRange rng) {
    assert (false);
  }

  override bool getIntRange(ref IntR rng) {
    assert (false);
  }

  override bool getIntType(ref INTTYPE iType) {
    assert (false);
  }

  override bool isSolved() {
    return _range.isSolved() && _weight.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    import std.conv: to;
    _range.writeExprString(str);
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.evaluate().to!string;
  }
}

class CstDistExpr(T): CstLogicTerm
{
  import std.conv;

  CstDomain _vec;
  CstDistRangeExpr[] _dists;

  DistRangeSet!T _rs;
  
  this(CstDomain vec, CstDistRangeExpr[] dists) {
    _vec = vec;
    _dists = dists;
    _rs = new DistRangeSet!T;
    foreach (dist; _dists) {
      T lhs = cast(T) dist._range._lhs.evaluate();
      T rhs;
      if (dist._range._rhs is null) {
	rhs = lhs;
      }
      else {
	rhs = cast(T) dist._range._rhs.evaluate();
      }
      int weight = cast(int) dist._weight.evaluate();
      bool perItem = dist._perItem;
      _rs ~= DistRange!T(lhs, rhs, weight, perItem);
    }
  }

  override DistRangeSetBase getDist() {
    return _rs;
  }

  override string describe() {
    string str = "( " ~ _vec.describe() ~ " dist ";
    foreach (dist; _dists) {
      assert (dist !is null);
      str ~= dist.describe() ~ ", ";
    }
    str ~= " )";
    return str;
  }

  override void visit(CstSolver solver) {
    assert (false, "Can not visit Dist Constraint: " ~ describe());
  }

  override CstDistExpr!T unroll(CstIterator iter, uint n) {
    // import std.stdio;
    // writeln(_lhs.describe() ~ " " ~ _op.to!string ~ " " ~ _rhs.describe() ~ " Getting unwound!");
    // writeln("RHS: ", _rhs.unroll(iter, n).describe());
    // writeln("LHS: ", _lhs.unroll(iter, n).describe());
    return new CstDistExpr!T(cast (CstDomain) (_vec.unroll(iter, n)), _dists);
  }

  override uint resolveLap() {
    return _vec.resolveLap();
  }
  
  override void resolveLap(uint lap) {
    _vec.resolveLap(lap);
  }


  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    rnds ~= _vec;
    pred.isDist(true);
    _vec.isDist(true);
  }

  bool getIntType(ref INTTYPE iType) {
    assert (false);
  }
  
  override bool getUniRangeSet(ref IntRS rs) {
    assert (false);
  }
    
  override bool getUniRangeSet(ref UIntRS rs) {
    assert (false);
  }
    
  override bool getUniRangeSet(ref LongRS rs) {
    assert (false);
  }
    
  override bool getUniRangeSet(ref ULongRS rs) {
    assert (false);
  }
    
  bool getUniRangeSetImpl(RS)(ref RS rs) {
    assert (false);
  }

  override bool getIntRangeSet(ref IntRS rs) {
    assert (false);
  }

  override bool isSolved() {
    return _vec.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    assert(false);
  }
  override CstVecExpr isNot(CstDomain A){
    return null;
  }
}

// class CstVecSliceExpr: CstVecTerm
// {
//   CstVecExpr _vec;
//   CstVecExpr _lhs;
//   CstVecExpr _rhs;
  
//   string describe() {
//     if (_rhs is null)
//       return _vec.describe() ~ "[ " ~ _lhs.describe() ~ " ]";
//     else
//       return _vec.describe() ~ "[ " ~ _lhs.describe() ~ " .. " ~ _rhs.describe() ~ " ]";
//   }

//   void visit(CstSolver solver) {
//     _vec.visit(solver);
//     assert (_lhs.isSolved());
//     if (_rhs !is null) assert (_rhs.isSolved());
//     solver.pushIndexToEvalStack(_lhs.evaluate());
//     if (_rhs is null) solver.pushIndexToEvalStack(_lhs.evaluate() + 1);
//     else solver.pushIndexToEvalStack(_rhs.evaluate());
//     solver.processEvalStack(CstSliceOp.SLICE);
//   }

//   // bool getVal(ref long val) {
//   //   return false;
//   // }

//   long evaluate() {
//     // auto vec  = _vec.evaluate();
//     // auto lvec = _lhs.evaluate();
//     // auto rvec = _range._rhs.evaluate();

//     assert(false, "Can not evaluate a CstVecSliceExpr!");
//   }

//   override CstVecSliceExpr unroll(CstIterator iter, uint n) {
//     if (_rhs is null)
//       return new CstVecSliceExpr(_vec.unroll(iter, n),
// 				 _lhs.unroll(iter, n), null);
//     else 
//       return new CstVecSliceExpr(_vec.unroll(iter, n),
// 				 _lhs.unroll(iter, n), _rhs.unroll(iter, n));
//   }

//   this(CstVecExpr vec, CstVecExpr lhs, CstVecExpr rhs) {
//     _vec = vec;
//     _lhs = lhs;
//     _rhs = rhs;
//   }

//   uint resolveLap() {
//     return _vec.resolveLap();
//   }

//   void resolveLap(uint lap) {
//     _vec.resolveLap(lap);
//   }

//   bool isConst() {
//     return false;
//   }

//   bool isIterator() {
//     return false;
//   }

//   bool isOrderingExpr() {
//     return false;		// only CstVecOrderingExpr return true
//   }

//   void setDomainContext(CstPredicate pred,
// 			ref CstDomain[] rnds,
// 			ref CstDomain[] vars,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstDomain[] idxs,
// 			ref CstDomain[] bitIdxs,
// 			ref CstDomain[] deps) {
//     _vec.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
//     _lhs.setDomainContext(pred, bitIdxs, bitIdxs, vals, iters, idxs, bitIdxs, deps);
//     if (_rhs !is null)
//       _rhs.setDomainContext(pred, bitIdxs, bitIdxs, vals, iters, idxs, bitIdxs, deps);
//   }

//   bool getIntRange(ref IntR rng) {
//     return false;
//   }

//   bool getUniRange(ref UniRange rng) {
//     return false;
//   }

//   bool getIntType(ref INTTYPE iType) {
//     return false;
//   }
  
//   override bool isSolved() {
//     if (_rhs is null) return _lhs.isSolved() && _vec.isSolved();
//     else return _lhs.isSolved() && _rhs.isSolved() && _vec.isSolved();
//   }
  
//   override void writeExprString(ref Charbuf str) {
//     _vec.writeExprString(str);
//     str ~= '[';
//     _lhs.writeExprString(str);
//     if (_rhs !is null) {
//       str ~= "..";
//       _rhs.writeExprString(str);
//     }
//     str ~= ']';
//   }
// }

class CstVecSliceExpr: CstVecTerm
{
  CstVecExpr _vec;
  CstRangeExpr _range;
  
  override string describe() {
    return _vec.describe() ~ "[ " ~ _range.describe() ~ " ]";
  }

  override void visit(CstSolver solver) {
    _vec.visit(solver);
    // _range.visit(solver);
    assert (_range._lhs.isSolved());
    if (_range._rhs !is null) assert (_range._rhs.isSolved());
    solver.pushIndexToEvalStack(_range._lhs.evaluate());
    if (_range._rhs is null)
      solver.pushIndexToEvalStack(_range._lhs.evaluate()+1);
    else
      solver.pushIndexToEvalStack(_range._rhs.evaluate());
    if (_range._inclusive) solver.processEvalStack(CstSliceOp.SLICEINC);
    else solver.processEvalStack(CstSliceOp.SLICE);
  }

  // bool getVal(ref long val) {
  //   return false;
  // }

  override long evaluate() {
    // auto vec  = _vec.evaluate();
    // auto lvec = _lhs.evaluate();
    // auto rvec = _range._rhs.evaluate();

    assert(false, "Can not evaluate a CstVecSliceExpr!");
  }

  override CstVecSliceExpr unroll(CstIterator iter, uint n) {
    return new CstVecSliceExpr(_vec.unroll(iter, n),
			       _range.unroll(iter, n));
  }

  this(CstVecExpr vec, CstRangeExpr range) {
    _vec = vec;
    _range = range;
  }

  override uint resolveLap() {
    return _vec.resolveLap();
  }

  override void resolveLap(uint lap) {
    _vec.resolveLap(lap);
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
    _vec.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
    _range.setDomainContext(pred, bitIdxs, bitIdxs, vals, iters, idxs, bitIdxs, deps);
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
  
  override bool isSolved() {
    return _range.isSolved() && _vec.isSolved();
  }
  
  override void writeExprString(ref Charbuf str) {
    _vec.writeExprString(str);
    str ~= '[';
    _range.writeExprString(str);
    str ~= ']';
  }
}

// class CstVecIndexExpr: CstVecTerm
// {
//   CstVecExpr _vec;
//   CstVecExpr _index;
  
//   string describe() {
//     return _vec.describe() ~ "[ " ~ _index.describe() ~ " ]";
//   }

//   void visit(CstSolver solver) {
//     _vec.visit(solver);
//     assert (_index.isSolved());
//     solver.pushIndexToEvalStack(_index.evaluate());
//     solver.pushIndexToEvalStack(_index.evaluate() + 1);
//     solver.processEvalStack(CstSliceOp.SLICE);
//   }

//   // bool getVal(ref long val) {
//   //   return false;
//   // }

//   long evaluate() {
//     assert(false, "Can not evaluate a CstVecIndexExpr!");
//   }

//   override CstVecIndexExpr unroll(CstIterator iter, uint n) {
//     return new CstVecIndexExpr(_vec.unroll(iter, n),
// 			       _index.unroll(iter, n));
//   }

//   this(CstVecExpr vec, CstVecExpr index) {
//     _vec = vec;
//     _index = index;
//   }

//   uint resolveLap() {
//     return _vec.resolveLap();
//   }

//   void resolveLap(uint lap) {
//     _vec.resolveLap(lap);
//   }

//   bool isConst() {
//     return false;
//   }

//   bool isIterator() {
//     return false;
//   }

//   bool isOrderingExpr() {
//     return false;		// only CstVecOrderingExpr return true
//   }

//   void setDomainContext(CstPredicate pred,
// 			ref CstDomain[] rnds,
// 			ref CstDomain[] vars,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstDomain[] idxs,
// 			ref CstDomain[] bitIdxs,
// 			ref CstDomain[] deps) {
//     _vec.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
//     _index.setDomainContext(pred, bitIdxs, bitIdxs, vals, iters, idxs, bitIdxs, deps);
//   }

//   bool getIntRange(ref IntR rng) {
//     return false;
//   }

//   bool getUniRange(ref UniRange rng) {
//     return false;
//   }

//   bool getIntType(ref INTTYPE iType) {
//     return false;
//   }
  
//   override bool isSolved() {
//     return _index.isSolved() && _vec.isSolved();
//   }
  
//   override void writeExprString(ref Charbuf str) {
//     _vec.writeExprString(str);
//     str ~= '[';
//     _index.writeExprString(str);
//     str ~= ']';
//   }
// }

class CstNotVecExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _expr;

  override string describe() {
    return "( ~ " ~ _expr.describe ~ " )";
  }

  override void visit(CstSolver solver) {
    _expr.visit(solver);
    solver.processEvalStack(CstUnaryOp.NOT);
  }

  // bool getVal(ref long val) {
  //   auto retval = _expr.getVal(val);
  //   val = ~val;
  //   return retval;
  // }

  override long evaluate() {
    return ~(_expr.evaluate());
  }

  override CstNotVecExpr unroll(CstIterator iter, uint n) {
    return new CstNotVecExpr(_expr.unroll(iter, n));
  }

  this(CstVecExpr expr) {
    _expr = expr;
  }

  override uint resolveLap() {
    return _expr.resolveLap();
  }

  override void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }
  
  override bool isConst() {
    return _expr.isConst();
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
    _expr.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
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

  override bool isSolved() {
    return _expr.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    str ~= "(NOT ";
    _expr.writeExprString(str);
    str ~= ')';
  }
}

class CstNegVecExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _expr;

  override string describe() {
    return "( - " ~ _expr.describe ~ " )";
  }

  override void visit(CstSolver solver) {
    _expr.visit(solver);
    solver.processEvalStack(CstUnaryOp.NEG);
  }

  // bool getVal(ref long val) {
  //   auto retval = _expr.getVal(val);
  //   val = -val;
  //   return retval;
  // }

  override long evaluate() {
    return -(_expr.evaluate());
  }

  override CstNegVecExpr unroll(CstIterator iter, uint n) {
    return new CstNegVecExpr(_expr.unroll(iter, n));
  }

  this(CstVecExpr expr) {
    _expr = expr;
  }

  override uint resolveLap() {
    return _expr.resolveLap();
  }

  override void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }
  
  override bool isConst() {
    return _expr.isConst();
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
    _expr.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
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

  override bool isSolved() {
    return _expr.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    str ~= "(NEG ";
    _expr.writeExprString(str);
    str ~= ')';
  }
}


class CstLogic2LogicExpr: CstLogicTerm
{
  import std.conv;

  CstLogicExpr _lhs;
  CstLogicExpr _rhs;
  CstLogicOp _op;

  this(CstLogicExpr lhs, CstLogicExpr rhs, CstLogicOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  override string describe() {
    return "( " ~ _lhs.describe ~ " " ~ _op.to!string ~ " " ~ _rhs.describe ~ " )";
  }

  override void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  override CstLogic2LogicExpr unroll(CstIterator iter, uint n) {
    return new CstLogic2LogicExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
  }

  override uint resolveLap() {
    uint lhs = _lhs.resolveLap();
    uint rhs = _rhs.resolveLap();
    if (lhs > rhs) return lhs;
    else return rhs;
  }
  override void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    _lhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
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
  
  override CstVecExpr isNot(CstDomain A){
    return null;
  }
  
  bool getUniRangeSetImpl(T)(ref T rs) {
    if (_lhs.isSolved()) return false;
    if (_rhs.isSolved()) return false;

    T lhs;
    T rhs;

    if (_lhs.getUniRangeSet(lhs) is false) return false;
    if (_rhs.getUniRangeSet(rhs) is false) return false;

    final switch(_op) {
    case CstLogicOp.LOGICAND: lhs &= rhs; break;
    case CstLogicOp.LOGICOR:  lhs |= rhs; break;
    case CstLogicOp.LOGICIMP: return false;
    case CstLogicOp.LOGICNOT: assert(false);
    }

    rs = lhs;
    return true;
  }

  override bool getIntRangeSet(ref IntRS rs) {
    assert(! _lhs.isSolved());
    assert(! _rhs.isSolved());

    IntRS lhs;
    IntRS rhs;

    if (_lhs.getIntRangeSet(lhs) is false) return false;
    if (_rhs.getIntRangeSet(rhs) is false) return false;

    final switch(_op) {
    case CstLogicOp.LOGICAND: lhs &= rhs; break;
    case CstLogicOp.LOGICOR:  lhs |= rhs; break;
    case CstLogicOp.LOGICIMP: return false;
    case CstLogicOp.LOGICNOT: assert(false);
    }

    rs = lhs;
    return true;
  }

  bool cstExprIsNop() {
    return false;
  }

  override bool isSolved() {
    return _lhs.isSolved && _rhs.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    str ~= '(';
    str ~= _op.to!string;
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ")\n";
  }

  override DistRangeSetBase getDist() {
    assert (false);
  }
}

// TBD
class CstIteLogicExpr: CstLogicTerm
{
  override string describe() {
    return "CstIteLogicExpr";
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
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
  
  override CstVecExpr isNot(CstDomain A){
    return null;
  }

  bool cstExprIsNop() {
    return false;
  }

  override uint resolveLap() {
    assert(false, "TBD");
  }    

  override void resolveLap(uint lap) {
    assert(false, "TBD");
  }    

  override CstLogicTerm unroll(CstIterator iter, uint n) {
    assert(false, "TBD");
  }

  override abstract void visit(CstSolver solver) {
    assert(false, "TBD");
  }

  override bool isSolved() {
    assert(false, "TBD");
  }

  override DistRangeSetBase getDist() {
    assert (false);
  }
}

class CstVec2LogicExpr: CstLogicTerm
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;
  CstCompareOp _op;

  this(CstVecExpr lhs, CstVecExpr rhs, CstCompareOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  override string describe() {
    return "( " ~ _lhs.describe ~ " " ~ _op.to!string ~ " " ~ _rhs.describe ~ " )";
  }

  override void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  override CstVec2LogicExpr unroll(CstIterator iter, uint n) {
    // import std.stdio;
    // writeln(_lhs.describe() ~ " " ~ _op.to!string ~ " " ~ _rhs.describe() ~ " Getting unwound!");
    // writeln("RHS: ", _rhs.unroll(iter, n).describe());
    // writeln("LHS: ", _lhs.unroll(iter, n).describe());
    return new CstVec2LogicExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
  }

  override uint resolveLap() {
    uint lhs = _lhs.resolveLap();
    uint rhs = _rhs.resolveLap();
    if (lhs > rhs) return lhs;
    else return rhs;
  }
  
  override void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }


  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    _lhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
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
  
  override CstVecExpr isNot(CstDomain A){
    if (_op is CstCompareOp.NEQ) {
      if (_lhs !is A) {
	assert(false, "Constraint " ~ describe() ~ " not allowed since " ~ A.name()
	       ~ " is dist");
      }
      return _rhs;
    }
    return null;
  }
    
  bool getUniRangeSetImpl(RS)(ref RS rs) {
    static if (is (RS == IntRangeSet!T, T)) {
      if (_rhs.isSolved()) {
	INTTYPE iType;
	assert(! _lhs.isSolved(), this.describe());
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
      else if (_lhs.isSolved()) {
	INTTYPE iType;
	assert(! _rhs.isSolved(), this.describe());
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
    if (_rhs.isSolved()) {
      assert(! _lhs.isSolved(), "Expression: " ~ _lhs.describe());
      auto rhs = cast(int) _rhs.evaluate();
      IntR rn = IntR(_op, rhs);
      bool valid = _lhs.getIntRange(rn);
      rs ~= rn;
      return valid;
    }
    else if (_lhs.isSolved()) {
      assert(! _rhs.isSolved(), "Expression: " ~ _rhs.describe());
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

  override bool isSolved() {
    return _lhs.isSolved && _rhs.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    str ~= '(';
    str ~= _op.to!string;
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ")\n";
  }

  override DistRangeSetBase getDist() {
    assert (false);
  }
}

class CstLogicConst: CstLogicTerm
{
  immutable bool _expr;

  this(bool expr) {
    _expr = expr;
  }

  override void visit(CstSolver solver) {
    solver.pushToEvalStack(_expr);
  }

  override string describe() {
    if(_expr) return "TRUE";
    else return "FALSE";
  }

  override CstLogicConst unroll(CstIterator iter, uint n) {
    return this;
  }

  override uint resolveLap() {
    return 0;
  }
  override void resolveLap(uint lap) {}

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    // nothing for CstLogicConst
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
  
  override CstVecExpr isNot(CstDomain A){
    return null;
  }

  override bool isSolved() {
    return true;
  }

  override void writeExprString(ref Charbuf str) {
    if (_expr) str ~= "TRUE";
    else str ~= "FALSE";
  }

  override DistRangeSetBase getDist() {
    assert (false);
  }
}

class CstNotLogicExpr: CstLogicTerm
{
  CstLogicExpr _expr;

  this(CstLogicExpr expr) {
    _expr = expr;
  }

  override string describe() {
    return "( " ~ "!" ~ " " ~ _expr.describe ~ " )";
  }

  override void visit(CstSolver solver) {
    _expr.visit(solver);
    solver.processEvalStack(CstLogicOp.LOGICNOT);
  }

  override CstNotLogicExpr unroll(CstIterator iter, uint n) {
    return new CstNotLogicExpr(_expr.unroll(iter, n));
  }

  override uint resolveLap() {
    return _expr.resolveLap();
  }
  override void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    _expr.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
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
  
  override CstVecExpr isNot(CstDomain A){
    return null;
  }

  override bool isSolved() {
    return _expr.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    str ~= "(NOT ";
    _expr.writeExprString(str);
    str ~= ")\n";
  }
  
  override DistRangeSetBase getDist() {
    assert (false);
  }
}

class CstObjVisitorExpr: CstLogicTerm
{
  CstObjIntf _obj;

  this(CstObjIntf obj) {
    _obj = obj;
  }

  override string describe() {
    return "Visitor: " ~ _obj.fullName();
  }

  override void visit(CstSolver solver) {
    assert (false);
  }

  override void visit() {
    assert (_obj !is null);
    _obj.visit();
  }

  override CstObjVisitorExpr unroll(CstIterator i, uint n) {
    CstIterator iter = _obj._esdl__iter();
    if (iter is i) {
      return new CstObjVisitorExpr(_obj._esdl__getChild(n));
    }
    else {
      return this;
    }
  }

  override uint resolveLap() {
    assert (false);
  }

  override void resolveLap(uint lap) {
    assert (false);
  }
  
  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomain[] vars,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstDomain[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstDomain[] deps) {
    CstIterator iter = _obj._esdl__iter();
    if (iter !is null) {
      iter.setDomainContext(pred, rnds, vars, vals, iters, idxs, bitIdxs, deps);
    }
  }

  bool getIntType(ref INTTYPE iType) {
    assert (false);
  }
  
  override bool getUniRangeSet(ref IntRS rs) {
    assert (false);
  }
    
  override bool getUniRangeSet(ref UIntRS rs) {
    assert (false);
  }
    
  override bool getUniRangeSet(ref LongRS rs) {
    assert (false);
  }
    
  override bool getUniRangeSet(ref ULongRS rs) {
    assert (false);
  }
    
  bool getUniRangeSetImpl(RS)(ref RS rs) {
    assert (false);
  }

  override bool getIntRangeSet(ref IntRS rs) {
    assert (false);
  }

  override bool isSolved() {
    return false;
  }

  override void writeExprString(ref Charbuf str) {
    str ~= this.describe();
  }

  override CstVecExpr isNot(CstDomain A){
    return null;
  }

  override DistRangeSetBase getDist() {
    assert (false);
  }
}


// CstLogic2LogicExpr logicOr(CstVecExpr other)
// {
//   return new CstLogic2LogicExpr(toBoolExpr(this), toBoolExpr(other), CstLogicOp.LOGICOR);
// }

auto _esdl__logicOr(P, Q)(P p, Q q) {
  CstLogicTerm _p;
  CstLogicTerm _q;
  static if (is (P == bool)) {
    _p = new CstLogicConst(p);
  }
  else static if (is (P: CstVecExpr)) {
    _p = toBoolExpr(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstLogicConst(q);
  }
  else static if (is (Q: CstVecExpr)) {
    _q = toBoolExpr(q);
  }
  else {
    _q = q;
  }
  return _p.logicOr(_q);
}

auto _esdl__logicAnd(P, Q)(P p, Q q) {
  CstLogicTerm _p;
  CstLogicTerm _q;
  static if(is(P == bool)) {
    _p = new CstLogicConst(p);
  }
  else static if (is (P: CstVecExpr)) {
    _p = toBoolExpr(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstLogicConst(q);
  }
  else static if (is (Q: CstVecExpr)) {
    _q = toBoolExpr(q);
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
    return new CstLogicConst(p < q);
  }
}

CstVec2LogicExpr _esdl__lth_impl(Q)(CstVecExpr left, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__lth_impl(left, qq);
  }

CstVec2LogicExpr _esdl__lth_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.LTH);
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
    return new CstLogicConst(p <= q);
  }
}

CstVec2LogicExpr _esdl__lte_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__lte_impl(p, qq);
  }

CstVec2LogicExpr _esdl__lte_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.LTE);
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
    return new CstLogicConst(p > q);
  }
}

CstVec2LogicExpr _esdl__gth_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__gth_impl(p, qq);
  }

CstVec2LogicExpr _esdl__gth_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.GTH);
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
    return new CstLogicConst(p >= q);
  }
}

CstVec2LogicExpr _esdl__gte_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__gte_impl(p, qq);
  }

CstVec2LogicExpr _esdl__gte_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.GTE);
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
    return new CstLogicConst(p == q);
  }
}

CstVec2LogicExpr _esdl__equ_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__equ_impl(p, qq);
  }

CstVec2LogicExpr _esdl__equ_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.EQU);
}

auto _esdl__range(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__range_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__range_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    static assert (false);
  }
}

CstRangeExpr _esdl__range_impl(Q)(CstVecExpr p, Q q)
  if (isBitVector!Q || isIntegral!Q) {
    if (q is null) return _esdl__range_impl(p, q);
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__range_impl(p, qq);
  }

CstRangeExpr _esdl__range_impl(CstVecExpr p, CstVecExpr q) {
  return new CstRangeExpr(p, q);
}

auto _esdl__rangeinc(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__rangeinc_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__rangeinc_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicConst(p == q);
  }
}

CstRangeExpr _esdl__rangeinc_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__rangeinc_impl(p, qq);
  }

CstRangeExpr _esdl__rangeinc_impl(CstVecExpr p, CstVecExpr q) {
  return new CstRangeExpr(p, q, true);
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
    return new CstLogicConst(p != q);
  }
}
CstVec2LogicExpr _esdl__neq_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__neq(p, qq);
  }

CstVec2LogicExpr _esdl__neq_impl(CstVecExpr p, CstVecExpr q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.NEQ);
}

CstLogicTerm _esdl__inside(CstVecTerm vec, CstRangeExpr[] ranges) {
  CstLogicTerm result = new CstLogicConst(false);
  foreach (r; ranges) {
    result = result | vec.inside(r);
  }
  return result;
}

CstDistRangeExpr _esdl__rangeWeight(CstRangeExpr range, CstVecExpr weight) {
  return new CstDistRangeExpr(range, weight, false);
}

CstDistRangeExpr _esdl__itemWeight(CstRangeExpr range, CstVecExpr weight) {
  return new CstDistRangeExpr(range, weight, true);
}

auto _esdl__dist(T, rand RAND)(CstVecDomain!(T, RAND) vec,
			       CstDistRangeExpr[] ranges) {
  return new CstDistExpr!T(vec, ranges);
}
