module esdl.rand.expr;

import esdl.rand.dist;

import esdl.solver.base: CstSolver;

import esdl.rand.misc: rand, _esdl__RandGen, isVecSigned, Unconst, CstVectorOp, CstInsideOp;
import esdl.rand.misc: CstBinaryOp, CstCompareOp, CstLogicOp,
  CstUnaryOp, CstSliceOp, writeHexString, CstUniqueOp;

import esdl.rand.base;
import esdl.rand.func;
import esdl.rand.proxy: _esdl__Proxy;

import esdl.data.bvec: isBitVector, toBitVec;
import esdl.data.charbuf;
import std.traits: isIntegral, isBoolean, isStaticArray,
  isSomeChar, EnumMembers, isSigned, OriginalType;

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

  final CstLogicTerm inside(CstInsideSetElem range) {
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

  Unconst!T _shadowValue;

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
  }
  else static if (isBoolean!T) {
    enum bool tSigned = false;
    enum size_t tSize = 1;
  }
  else static if (isSomeChar!T) {
    enum bool tSigned = false;
    enum size_t tSize = T.sizeof * 8;
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
    }
  }


  override void registerRndPred(CstPredicate rndPred) {
    foreach (pred; _rndPreds) {
      if (pred is rndPred) {
	return;
      }
    }
    _rndPreds ~= rndPred;
  }
  
  // override void registerVarPred(CstPredicate varPred) {
  //   foreach (pred; _varPreds) {
  //     if (pred is varPred) {
  // 	return;
  //     }
  //   }
  //   _varPreds ~= varPred;
  // }
  
  override void markSolved() {
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
    // desc ~= "\n	DomType: " ~ _type.to!string();
    // if (_type !is DomType.MULTI) {
    //   desc ~= "\nIntRS: " ~ _rs.toString();
    // }
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

  override void visit(CstSolver solver) {
    assert (false, "Can not visit an Iter Variable without unrolling");
  }

  // override bool getVal(ref long val) {
  //   return false;
  // }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    deps ~= getLenVec();
    iters ~= this;
  }

  override bool signed() {
    return false;
  }

  override uint bitcount() {
    return 64;
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
    if ((! isSolved()) && isStatic() && (! isRolled())) {
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
      execCbs();
    }
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
    _parent.setLen(cast(size_t) value);
    markSolved();
    execCbs();
  }

  override void setVal(ulong[] v) {
    assert(v.length == 1);
    _parent.setLen(cast(size_t) v[0]);
    markSolved();
    execCbs();
  }

  override void markSolved() {
    super.markSolved();
    _parent.markArrLen(value());
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
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
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
    _parent.setDomainContext(pred, rnds, rndArrs, vars, varArrs,
			     vals, iters, idxs, bitIdxs, deps);
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

  final override bool isRolled() {
    return _parent.isRolled();
  }

  override CstDomSet getParentDomSet() {
    static if (is (RV: CstDomSet)) return _parent;
    else return null;
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
  // abstract bool signed();
  // abstract uint bitcount();
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

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

  override bool isSolved() {
    return true;
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    vals ~= this;
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


class CstVecArrExpr: CstVecTerm
{
  import std.conv;

  CstDomSet _arr;
  CstVectorOp _op;

  override string describe() {
    return "( " ~ _arr.fullName ~ " " ~ _op.to!string() ~ " )";
  }

  override void visit(CstSolver solver) {
    CstVecArrIntf.Range range = _arr[];
    solver.pushToEvalStack(0, 32, true);

    foreach (dom; range) {
      solver.pushToEvalStack(dom);
      solver.processEvalStack(CstBinaryOp.ADD);
    }
    // assert (! range.empty());
    // CstDomain dom = range.front();
    // uint bitcount = dom.bitcount();
    // bool signed = dom.signed();
    // if (signed) {
    //   if (bitcount <= 32) solver.processEvalStack(CstVectorOp.BEGIN_INT);
    //   else                solver.processEvalStack(CstVectorOp.BEGIN_LONG);
    // }
    // else {
    //   if (bitcount <= 32) solver.processEvalStack(CstVectorOp.BEGIN_UINT);
    //   else                solver.processEvalStack(CstVectorOp.BEGIN_ULONG);
    // }
    // _arr.visit(solver);
    // solver.processEvalStack(_op);
  }

  override long evaluate() {
    assert (false, "TBD");
  }

  override CstVecArrExpr unroll(CstIterator iter, uint n) {
    return this;
  }

  this(CstDomSet arr// , CstVectorOp op
       ) {
    _arr = arr;
    _op = CstVectorOp.SUM;
  }

  override uint bitcount() {
    uint _elemBitCount = _arr.elemBitcount();

    if (_elemBitCount <= 32) return 32;
    else if (_elemBitCount <= 64) return 64;
    else {
      assert (false, "CstVecArrExpr works only for bitcount <= 64");
    }
  }

  override bool signed() {
    uint _elemBitCount = _arr.elemBitcount();
    bool _elemSigned = _arr.elemSigned();

    if (_elemBitCount < 32) return true;
    else if (_elemBitCount == 32) return _elemSigned;
    else if (_elemBitCount < 64) return true;
    else if (_elemBitCount == 64) return _elemSigned;
    else {
      assert (false, "CstVecArrExpr works only for bitcount <= 64");
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
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    pred._vectorOp = _op;
    _arr.setDomainArrContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    assert (rndArrs.length > 0 || varArrs.length > 0);
  }

  override bool isSolved() {
    return false;
  }

  override void writeExprString(ref Charbuf str) {
    str ~= '(';
    str ~= _op.to!string;
    str ~= ' ';
    _arr.writeExprString(str);
    str ~= ')';
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

  override uint bitcount() {
    uint lhsBitcount = _lhs.bitcount();
    uint rhsBitCount = _rhs.bitcount();
    uint count = rhsBitCount > lhsBitcount ? rhsBitCount : lhsBitcount;

    if (count <= 32) return 32;
    else if (count <= 64) return 64;
    else return count;
  }
  
  override bool signed() {
    uint lhsBitcount = _lhs.bitcount();
    uint rhsBitcount = _rhs.bitcount();
    bool lhsSigned = _lhs.signed();
    bool rhsSigned = _rhs.signed();

    if (lhsSigned && rhsSigned) return true; // both signed
    else if (lhsBitcount > rhsBitcount) {
      if (lhsBitcount == 32 || lhsBitcount == 64) return lhsSigned;
      else return false;
    }
    else if (rhsBitcount > lhsBitcount) {
      if (rhsBitcount == 32 || rhsBitcount == 64) return rhsSigned;
      else return false;
    }
    else {			// size is same
      if (rhsBitcount == 32 || rhsBitcount == 64) return rhsSigned && lhsSigned;
      else return false;
    }
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
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
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

class CstRangeExpr
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;

  bool _inclusive = false;

  string describe() {
    if (_rhs is null)
      return "( " ~ _lhs.describe ~ " )";
    else if (_inclusive)
      return "( " ~ _lhs.describe ~ " : " ~ _rhs.describe ~ " )";
    else
      return "( " ~ _lhs.describe ~ " .. " ~ _rhs.describe ~ " )";
  }

  long evaluate() {
    assert (_rhs is null);
    return _lhs.evaluate();
  }

  CstRangeExpr unroll(CstIterator iter, uint n) {
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

  // bool isConst() {
  //   return _rhs is null && _lhs.isConst();
  // }

  // bool isIterator() {
  //   return false;
  // }

  // bool isOrderingExpr() {
  //   return false;		// only CstVecOrderingExpr return true
  // }

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
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _lhs.isSolved() && (_rhs is null || _rhs.isSolved());
  }

  void writeExprString(ref Charbuf str) {
    _lhs.writeExprString(str);
    if (_rhs !is null) {
      if (_inclusive) str ~= " : ";
      else str ~= " .. ";
      _rhs.writeExprString(str);
    }
  }
}

class CstDistSetElem
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;

  bool _inclusive = false;

  string describe() {
    if (_rhs is null)
      return "( " ~ _lhs.describe ~ " )";
    else if (_inclusive)
      return "( " ~ _lhs.describe ~ " : " ~ _rhs.describe ~ " )";
    else
      return "( " ~ _lhs.describe ~ " .. " ~ _rhs.describe ~ " )";
  }

  long evaluate() {
    assert (_rhs is null);
    return _lhs.evaluate();
  }

  CstDistSetElem unroll(CstIterator iter, uint n) {
    if (_rhs is null)
      return new CstDistSetElem(_lhs.unroll(iter, n), null, _inclusive);
    else
      return new CstDistSetElem(_lhs.unroll(iter, n),
				  _rhs.unroll(iter, n), _inclusive);
  }

  this(CstVecExpr lhs, CstVecExpr rhs, bool inclusive=false) {
    _lhs = lhs;
    _rhs = rhs;
    _inclusive = inclusive;
  }

  // bool isConst() {
  //   return _rhs is null && _lhs.isConst();
  // }

  // bool isIterator() {
  //   return false;
  // }

  // bool isOrderingExpr() {
  //   return false;		// only CstVecOrderingExpr return true
  // }

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
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _lhs.isSolved() && (_rhs is null || _rhs.isSolved());
  }

  void writeExprString(ref Charbuf str) {
    _lhs.writeExprString(str);
    if (_rhs !is null) {
      if (_inclusive) str ~= " : ";
      else str ~= " .. ";
      _rhs.writeExprString(str);
    }
  }
}

class CstUniqueSetElem
{
  import std.conv;

  CstVecExpr _vec;
  CstDomSet  _arr;

  bool _inclusive = false;

  string describe() {
    if (_arr !is null) {
      assert (_vec is null);
      return "( " ~ _arr.fullName ~ "[] )";
    }
    else {
      assert (_arr is null);
      return "( " ~ _vec.describe ~ " )";
    }
  }

  CstUniqueSetElem unroll(CstIterator iter, uint n) {
    if (_arr !is null) {
      assert (_vec is null);
      return new CstUniqueSetElem(_arr.unroll(iter, n));
    }
    else {
      assert (_arr is null);
      return new CstUniqueSetElem(_vec.unroll(iter, n));
    }
  }

  this(CstVecExpr vec) {
    _vec = vec;
  }

  this(CstDomSet arr) {
    _arr = arr;
  }

  bool signed() {
    if (_arr !is null) return _arr.elemSigned();
    else return _vec.signed();
  }

  uint bitcount() {
    if (_arr !is null) return _arr.elemBitcount();
    else return _vec.bitcount();
  }

  void fixIntType(ref CstUniqueOp type) {
    uint count = this.bitcount();
    bool sign = this.signed();

    CstUniqueOp t;
    if (count < 32) t = CstUniqueOp.INT;
    else if (count == 32) t = sign ? CstUniqueOp.INT : CstUniqueOp.UINT;
    else if (count < 64) t = CstUniqueOp.LONG;
    else if (count == 64) t = sign ? CstUniqueOp.LONG : CstUniqueOp.ULONG;
    else assert (false, "unique not supported for bitcount > 64");

    if (t > type) type = t;
  }
  // bool isConst() {
  //   if (_arr !is null) return false;
  //   return _vec.isConst();
  // }

  // bool isIterator() {
  //   return false;
  // }

  // bool isOrderingExpr() {
  //   return false;		// only CstVecOrderingExpr return true
  // }

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
    if (_arr !is null) {
      _arr.setDomainArrContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
      assert (rndArrs.length > 0 || varArrs.length > 0);
    }
    if (_vec !is null)
      _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return false;
  }

  void writeExprString(ref Charbuf str) {
    if (_arr !is null) {
      str ~= "[ ";
      _arr.writeExprString(str);
      str ~= " ]";
    }
    else {
      _vec.writeExprString(str);
    }
  }
}


class CstInsideSetElem
{
  import std.conv;

  CstVecExpr _lhs;
  CstVecExpr _rhs;

  CstDomSet  _arr;

  bool _inclusive = false;

  string describe() {
    if (_arr !is null)
      return "( " ~ _arr.fullName ~ "[] )";
    else {
      assert (_arr is null);
      if (_rhs is null)
	return "( " ~ _lhs.describe ~ " )";
      else if (_inclusive)
	return "( " ~ _lhs.describe ~ " : " ~ _rhs.describe ~ " )";
      else
	return "( " ~ _lhs.describe ~ " .. " ~ _rhs.describe ~ " )";
    }
  }

  CstInsideSetElem unroll(CstIterator iter, uint n) {
    if (_arr !is null) {
      assert (_lhs is null);
      return new CstInsideSetElem(_arr.unroll(iter, n));
    }
    else {
      assert (_arr is null);
      if (_rhs is null)
	return new CstInsideSetElem(_lhs.unroll(iter, n), null, _inclusive);
      else
	return new CstInsideSetElem(_lhs.unroll(iter, n),
				    _rhs.unroll(iter, n), _inclusive);
    }
  }

  this(CstVecExpr lhs, CstVecExpr rhs, bool inclusive=false) {
    _lhs = lhs;
    _rhs = rhs;
    _inclusive = inclusive;
  }

  this(CstDomSet arr) {
    _arr = arr;
  }

  // bool isConst() {
  //   if (_arr !is null) return false;
  //   if (_rhs !is null) return false;
  //   return _lhs.isConst();
  // }

  // bool isIterator() {
  //   return false;
  // }

  // bool isOrderingExpr() {
  //   return false;		// only CstVecOrderingExpr return true
  // }

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
    if (_arr !is null) {
      _arr.setDomainArrContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
      assert (rndArrs.length > 0 || varArrs.length > 0);
    }
    if (_lhs !is null)
      _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return false;
  }

  void writeExprString(ref Charbuf str) {
    if (_arr !is null) {
      str ~= "[ ";
      _arr.writeExprString(str);
      str ~= " ]";
    }
    else {
      _lhs.writeExprString(str);
      if (_rhs !is null) {
	if (_inclusive) str ~= " : ";
	else str ~= " .. ";
	_rhs.writeExprString(str);
      }
    }
  }
}

class CstWeightedDistSetElem
{
  import std.conv;

  CstDistSetElem _range;
  CstVecExpr   _weight;
  bool         _perItem = false;

  string describe() {
    string str = "( " ~ _range.describe;
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.describe() ~ " )";
    return str;
  }

  CstWeightedDistSetElem unroll(CstIterator iter, uint n) {
    return this;
  }

  this(CstDistSetElem range, CstVecExpr weight, bool perItem=false) {
    _range = range;
    _weight = weight;
    _perItem = perItem;
  }

  // bool isConst() {
  //   return false;
  // }

  // bool isIterator() {
  //   return false;
  // }

  // bool isOrderingExpr() {
  //   return false;		// only CstVecOrderingExpr return true
  // }

  void setDomainContext(CstPredicate pred,
			ref CstDomain[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomain[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomain[] bitIdxs,
			ref CstVecNodeIntf[] deps) { }

  bool isSolved() {
    return _range.isSolved() && _weight.isSolved();
  }

  void writeExprString(ref Charbuf str) {
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
  CstWeightedDistSetElem[] _dists;

  DistRangeSet!T _rs;
  
  this(CstDomain vec, CstWeightedDistSetElem[] dists) {
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

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    rnds ~= _vec;
    pred.isDist(true);
    _vec.isDist(true);
  }

  override bool isSolved() {
    return _vec.isSolved();
  }

  override void writeExprString(ref Charbuf str) {
    assert(false);
  }
  override CstVecExpr isNot(CstDomain dom){
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
//		        ref CstDomSet[] rndArrs,
// 			ref CstDomain[] vars,
//			ref CstDomSet[] varArrs,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstVecNodeIntf[] idxs,
// 			ref CstDomain[] bitIdxs,
// 			ref CstVecNodeIntf[] deps) {
//     _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
//     _lhs.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, vals, iters, idxs, bitIdxs, deps);
//     if (_rhs !is null)
//       _rhs.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, vals, iters, idxs, bitIdxs, deps);
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

  override uint bitcount() {
    return _vec.bitcount();
  }
  
  override bool signed() {
    return false;
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
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _range.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, vals, iters, idxs, bitIdxs, deps);
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
//			ref CstDomSet[] rndArrs,
// 			ref CstDomain[] vars,
//			ref CstDomSet[] varArrs,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstVecNodeIntf[] idxs,
// 			ref CstDomain[] bitIdxs,
// 			ref CstVecNodeIntf[] deps) {
//     _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
//     _index.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, vals, iters, idxs, bitIdxs, deps);
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

  override uint bitcount() {
    uint count = _expr.bitcount();

    if (count <= 32) return 32;
    else if (count <= 64) return 64;
    else return count;
  }
  
  override bool signed() {
    bool sign = _expr.signed();
    uint count = _expr.bitcount();

    if (count == 32 || count == 64) return sign;
    else return true;		// int promotion
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
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
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

  override uint bitcount() {
    uint count = _expr.bitcount();

    if (count <= 32) return 32;
    else if (count <= 64) return 64;
    else return count;
  }
  
  override bool signed() {
    bool sign = _expr.signed();
    uint count = _expr.bitcount();

    if (count == 32 || count == 64) return sign;
    else return true;		// int promotion
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
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
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

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  override CstVecExpr isNot(CstDomain dom){
    return null;
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

class CstInsideArrExpr: CstLogicTerm
{
  CstInsideSetElem[] _elems;

  CstVecExpr _term;

  bool _notinside = false;

  void setNotInside() { _notinside = true; }

  override string describe() {
    string description = "( " ~ _term.describe() ~ " inside [";
    foreach (elem; _elems) {
      description ~= elem.describe();
    }
    description ~= "]";
    return description;
  }

  override void visit(CstSolver solver) {
    solver.pushToEvalStack(false);
    _term.visit(solver);
    solver.processEvalStack(CstInsideOp.INSIDE);
    foreach (elem; _elems) {
      if (elem._lhs !is null) {
	assert (elem._arr is null);
	elem._lhs.visit(solver);
	if (elem._rhs !is null) {
	  elem._rhs.visit(solver);
	  if (elem._inclusive) solver.processEvalStack(CstInsideOp.RANGEINCL);
	  else solver.processEvalStack(CstInsideOp.RANGE);
	  // solver.processEvalStack(CstLogicOp.LOGICAND);
	}
	else {
	  solver.processEvalStack(CstInsideOp.EQUAL);
	}
	// solver.processEvalStack(CstLogicOp.LOGICOR);
      }
      else {
	assert (elem._arr !is null);
	foreach (dom; elem._arr[]) {
	  dom.visit(solver);
	  solver.processEvalStack(CstInsideOp.EQUAL);
	  // solver.processEvalStack(CstLogicOp.LOGICOR);
	}
      }
    }
    solver.processEvalStack(CstInsideOp.DONE);
    if (_notinside) solver.processEvalStack(CstLogicOp.LOGICNOT);
  }

  this(CstVecExpr term) {
    _term = term;
  }

  void addElem(CstInsideSetElem elem) {
    _elems ~= elem;
  }

  override CstInsideArrExpr unroll(CstIterator iter, uint n) {
    CstInsideArrExpr unrolled = new CstInsideArrExpr(_term.unroll(iter, n));
    foreach (elem; _elems) {
      unrolled.addElem(elem.unroll(iter, n));
    }
    return unrolled;
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _term.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    foreach (elem; _elems) {
      elem.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    }
  }

  override CstVecExpr isNot(CstDomain dom){
    return null;
  }
  
  bool cstExprIsNop() {
    return false;
  }

  override bool isSolved() {
    return false;
  }

  override void writeExprString(ref Charbuf str) {
    str ~= "(INSIDE ";
    _term.writeExprString(str);
    str ~= " [";
    foreach (elem; _elems)
      elem.writeExprString(str);
    str ~= "])\n";
  }

  override DistRangeSetBase getDist() {
    assert (false);
  }
}

class CstUniqueArrExpr: CstLogicTerm
{
  CstUniqueSetElem[] _elems;

  override string describe() {
    string description = "( unique [";
    foreach (elem; _elems) {
      description ~= elem.describe();
    }
    description ~= "]";
    return description;
  }

  override void visit(CstSolver solver) {
    CstUniqueOp intT = CstUniqueOp.INT;
    foreach (elem; _elems) elem.fixIntType(intT);
    foreach (elem; _elems) {
      if (elem._vec !is null) {
	elem._vec.visit(solver);
	solver.processEvalStack(intT);
      }
      else {
	foreach (arrElem; elem._arr[]) {
	  arrElem.visit(solver);
	  solver.processEvalStack(intT);
	}
      }
    }
    solver.processEvalStack(CstUniqueOp.UNIQUE);
  }

  this() { }

  void addElem(CstUniqueSetElem elem) {
    _elems ~= elem;
  }

  override CstUniqueArrExpr unroll(CstIterator iter, uint n) {
    CstUniqueArrExpr unrolled = new CstUniqueArrExpr();
    foreach (elem; _elems) {
      unrolled.addElem(elem.unroll(iter, n));
    }
    return unrolled;
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    pred.setUniqueFlag();
    foreach (elem; _elems) {
      elem.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    }
  }

  override CstVecExpr isNot(CstDomain dom){
    return null;
  }
  
  bool cstExprIsNop() {
    return false;
  }

  override bool isSolved() {
    return false;
  }

  override void writeExprString(ref Charbuf str) {
    str ~= "(UNIQUE ";
    str ~= " [";
    foreach (elem; _elems)
      elem.writeExprString(str);
    str ~= "])\n";
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
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    assert(false, "TBD");
  }

  override CstVecExpr isNot(CstDomain dom){
    return null;
  }

  bool cstExprIsNop() {
    return false;
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

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }
  
  override CstVecExpr isNot(CstDomain dom){
    if (_op is CstCompareOp.NEQ) {
      if (_lhs !is dom) {
	assert(false, "Constraint " ~ describe() ~ " not allowed since " ~ dom.name()
	       ~ " is dist");
      }
      return _rhs;
    }
    return null;
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

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    // nothing for CstLogicConst
  }

  override CstVecExpr isNot(CstDomain dom){
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

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  override CstVecExpr isNot(CstDomain dom){
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

class CstVarVisitorExpr: CstLogicTerm
{
  CstVarNodeIntf _obj;

  this(CstVarNodeIntf obj) {
    assert (obj !is null);
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

  override CstVarVisitorExpr unroll(CstIterator i, uint n) {
    assert (_obj !is null);
    CstIterator iter = _obj._esdl__iter();
    if (iter is i) {
      return new CstVarVisitorExpr(_obj._esdl__getChild(n));
    }
    else {
      return this;
    }
  }

  override void setDomainContext(CstPredicate pred,
				 ref CstDomain[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomain[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomain[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    assert (_obj !is null);
    CstIterator iter = _obj._esdl__iter();
    if (iter !is null) {
      iter.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    }
  }

  override bool isSolved() {
    return false;
  }

  override void writeExprString(ref Charbuf str) {
    str ~= this.describe();
  }

  override CstVecExpr isNot(CstDomain dom){
    return null;
  }

  override DistRangeSetBase getDist() {
    assert (false);
  }
}
