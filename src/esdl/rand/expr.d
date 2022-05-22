module esdl.rand.expr;

import esdl.solver.base: CstSolver, CstDistSolverBase;

import esdl.rand.misc: rand, isVecSigned, Unconst, CstVecType,
  CstVectorOp, CstInsideOp, CstBinaryOp, CstCompareOp, CstLogicOp,
  CstUnaryOp, CstSliceOp, writeHexString, CstUniqueOp, DomainContextEnum,
  getCommonVecType, _esdl__Sigbuf;

import esdl.rand.base: DomDistEnum, CstTerm, CstDomBase, CstDomSet,
  CstIterator, CstVecNodeIntf, CstVarNodeIntf, CstVecArrIntf,
  CstVecPrim, CstValue, CstVecTerm, CstLogicTerm, CstDepIntf;
import esdl.rand.pred: CstPredicate, Hash;
import esdl.rand.agent: CstSolverAgent;

import esdl.rand.func;

import esdl.data.bvec: isBitVector, toBitVec;
import esdl.data.deck: Charbuf;
import std.traits: isIntegral, isBoolean, isStaticArray,
  isSomeChar, EnumMembers, isSigned, OriginalType;
import std.algorithm: canFind;

abstract class CstLogicExpr: CstLogicTerm
{
  void setDistPredContext(CstPredicate pred) { }
  CstDomBase getDomain() { return null; }
}

abstract class CstVecExpr: CstVecTerm
{
  CstDomBase getDomain() { return null; }
  final override bool isDistVar() { return false; }
}

class CstVecArrExpr: CstVecExpr
{
  import std.conv;

  CstDomSet _arr;
  CstVectorOp _op;

  string describe(bool descExpr=false) {
    return "( " ~ _arr._esdl__getFullName ~ " " ~ _op.to!string() ~ " )";
  }

  void visit(CstSolver solver) {
    CstVecArrIntf.Range range = _arr[];
    solver.pushToEvalStack(0, 32, true);

    foreach (dom; range) {
      solver.pushToEvalStack(dom);
      solver.processEvalStack(CstBinaryOp.ADD);
    }
    // assert (! range.empty());
    // CstDomBase dom = range.front();
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

  long evaluate() {
    CstVecType type = _arr.getVecType();

    switch (type) {
    case CstVecType.BOOL, CstVecType.INT:
      int sum = 0;
      foreach (v; _arr[]) { sum += cast(int) v.evaluate(); }
      return sum;
    case CstVecType.UINT:
      uint sum = 0;
      foreach (v; _arr[]) { sum += cast(uint) v.evaluate(); }
      return sum;
    case CstVecType.LONG:
      long sum = 0;
      foreach (v; _arr[]) { sum += cast(long) v.evaluate(); }
      return sum;
    case CstVecType.ULONG:
      ulong sum = 0;
      foreach (v; _arr[]) { sum += cast(ulong) v.evaluate(); }
      return sum;
    default: assert (false, "Unsupported expression type: " ~
		     type.to!string());
    }
  }

  CstVecArrExpr _esdl__unroll(CstIterator iter, ulong n) {
    return this;
  }

  this(CstDomSet arr// , CstVectorOp op
       ) {
    _arr = arr;
    _op = CstVectorOp.SUM;
  }

  uint bitcount() {
    uint _elemBitCount = _arr.elemBitcount();

    if (_elemBitCount <= 32) return 32;
    else if (_elemBitCount <= 64) return 64;
    else {
      assert (false, "CstVecArrExpr works only for bitcount <= 64");
    }
  }

  bool signed() {
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
  
  bool isConst() {
    return false;
  }

  bool isIterator() {
    return false;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    pred._vectorOp = _op;
    _arr.setDomainArrContext(pred, context);
    assert (pred._unresolvedRndArrs.length > 0 || pred._unresolvedVarArrs.length > 0);
  }

  bool isSolved() {
    return false;
  }

  void annotate(CstSolverAgent agent) {
    _arr.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    import std.format: sformat;
    char[16] buff;
    str ~= '(';
    str ~= sformat(buff[], "%s", _op);
    str ~= ' ';
    _arr.writeExprString(str);
    str ~= ')';
  }
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(_op);
    hash.modify(32);
    _arr.calcHash(hash);
    hash.modify(41);
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    _hash.modify(_op);
    _hash.modify(32);
    _arr.makeHash();
    _hash.modify(_arr.hashValue());
    _hash.modify(41);
  }
  
  void _esdl__scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

  final override CstVecType getVecType() {
    return _arr.getVecType();
  }
}

// This class would hold two(bin) vector nodes and produces a vector
// only after processing those two nodes
class CstVec2VecExpr: CstVecExpr
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;
  CstBinaryOp _op;

  string describe(bool descExpr=false) {
    return "( " ~ _lhs.describe(true) ~ " " ~ _op.to!string() ~ " " ~ _rhs.describe(true) ~ " )";
  }

  void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  long evaluate() {
    long lvec = _lhs.evaluate();
    long rvec = _rhs.evaluate();

    CstVecType ltype = _lhs.getVecType();
    CstVecType rtype = _rhs.getVecType();

    CstVecType type = getCommonVecType(ltype, rtype);

    switch (type) {
    case CstVecType.BOOL, CstVecType.INT:
      return _esdl__evaluate(cast(int) lvec, cast(int) rvec, _op);
    case CstVecType.UINT:
      return _esdl__evaluate(cast(uint) lvec, cast(uint) rvec, _op);
    case CstVecType.LONG:
      return _esdl__evaluate(cast(long) lvec, cast(long) rvec, _op);
    case CstVecType.ULONG:
      return _esdl__evaluate(cast(ulong) lvec, cast(ulong) rvec, _op);
    default: assert (false, "Unsupported expression type: " ~
		     type.to!string());
    }
  }

  CstVec2VecExpr _esdl__unroll(CstIterator iter, ulong n) {
    return new CstVec2VecExpr(_lhs._esdl__unroll(iter, n),
			      _rhs._esdl__unroll(iter, n), _op);
  }

  this(CstVecTerm lhs, CstVecTerm rhs, CstBinaryOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  uint bitcount() {
    uint lhsBitcount = _lhs.bitcount();
    uint rhsBitCount = _rhs.bitcount();
    uint count = rhsBitCount > lhsBitcount ? rhsBitCount : lhsBitcount;

    if (count <= 32) return 32;
    else if (count <= 64) return 64;
    else return count;
  }
  
  bool signed() {
    uint lhsBitcount = _lhs.bitcount();
    uint rhsBitcount = _rhs.bitcount();
    bool lhsSigned = _lhs.signed();
    bool rhsSigned = _rhs.signed();

    if (lhsSigned && rhsSigned) return true; // both signed
    else if (lhsBitcount > rhsBitcount) {
      if (lhsBitcount == 32 || lhsBitcount == 64) return lhsSigned;
      else return true;
    }
    else if (rhsBitcount > lhsBitcount) {
      if (rhsBitcount == 32 || rhsBitcount == 64) return rhsSigned;
      else return true;
    }
    else {			// size is same
      if (rhsBitcount == 32 || rhsBitcount == 64) return rhsSigned && lhsSigned;
      else return true;
    }
  }
  
  bool isConst() {
    return _lhs.isConst() && _rhs.isConst();
  }

  bool isIterator() {
    return false;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _lhs.setDomainContext(pred, context);
    _rhs.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _lhs.isSolved() && _rhs.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _lhs.annotate(agent);
    _rhs.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    import std.format: sformat;
    char[16] buff;
    str ~= '(';
    str ~= sformat(buff[], "%s", _op);
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ')';
  }
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(_op);
    hash.modify(32);
    _lhs.calcHash(hash);
    hash.modify(32);
    _rhs.calcHash(hash);
    hash.modify(41);
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    bool isSymmetric;
    _lhs.makeHash();
    _rhs.makeHash();
    final switch (_op){
    case CstBinaryOp.AND:
      isSymmetric = true;
      break;
    case CstBinaryOp.OR:
      isSymmetric = true;
      break;
    case CstBinaryOp.XOR:
      isSymmetric = true;
      break;
    case CstBinaryOp.ADD:
      isSymmetric = true;
      break;
    case CstBinaryOp.SUB:
      isSymmetric = false;
      break;
    case CstBinaryOp.MUL:
      isSymmetric = true;
      break;
    case CstBinaryOp.DIV:
      isSymmetric = false;
      break;
    case CstBinaryOp.REM:
      isSymmetric = false;
      break;
    case CstBinaryOp.LSH:
      isSymmetric = false;
      break;
    case CstBinaryOp.RSH:
      isSymmetric = false;
      break;
    case CstBinaryOp.LRSH:
      isSymmetric = false;
      break;
    }
    if (isSymmetric){
      if (_lhs.hashValue() > _rhs.hashValue()){
    	CstVecTerm temp = _lhs;
    	_lhs = _rhs;
    	_rhs = temp;
      }
    }
    _hash.modify(_op);
    _hash.modify(32);
    _hash.modify(_lhs.hashValue());
    _hash.modify(32);
    _hash.modify(_rhs.hashValue());
    _hash.modify(41);
  }
  
  void _esdl__scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

  final override CstVecType getVecType() {
    return getCommonVecType(_lhs.getVecType(), _rhs.getVecType);
  }

}

class CstRangeExpr
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;

  bool _inclusive = false;

  string describe(bool descExpr=false) {
    if (_rhs is null)
      return "( " ~ _lhs.describe(true) ~ " )";
    else if (_inclusive)
      return "( " ~ _lhs.describe(true) ~ " : " ~ _rhs.describe(true) ~ " )";
    else
      return "( " ~ _lhs.describe(true) ~ " .. " ~ _rhs.describe(true) ~ " )";
  }

  long evaluate() {
    assert (_rhs is null);
    return _lhs.evaluate();
  }

  CstRangeExpr _esdl__unroll(CstIterator iter, ulong n) {
    if (_rhs is null)
      return new CstRangeExpr(_lhs._esdl__unroll(iter, n), null, _inclusive);
    else
      return new CstRangeExpr(_lhs._esdl__unroll(iter, n),
			      _rhs._esdl__unroll(iter, n), _inclusive);
  }

  this(CstVecTerm lhs, CstVecTerm rhs, bool inclusive=false) {
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

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _lhs.setDomainContext(pred, context);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _lhs.isSolved() && (_rhs is null || _rhs.isSolved());
  }

  void annotate(CstSolverAgent agent) {
    _lhs.annotate(agent);
    if (_rhs !is null) {
      _rhs.annotate(agent);
    }
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    _lhs.writeExprString(str);
    if (_rhs !is null) {
      if (_inclusive) str ~= " : ";
      else str ~= " .. ";
      _rhs.writeExprString(str);
    }
  }
  
  void calcHash(ref Hash hash){
    _lhs.calcHash(hash);
    if (_rhs !is null) {
      if (_inclusive) hash.modify(58);
      else hash.modify(46);
      _rhs.calcHash(hash);
    }
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(0);
    _lhs.makeHash();
    _hash.modify(_lhs.hashValue());
    if (_rhs !is null) {
      _rhs.makeHash();
      if (_inclusive) _hash.modify(58);
      else _hash.modify(46);
      _hash.modify(_rhs.hashValue());
    }
  }
}

class CstVecDistSetElem
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;

  bool _inclusive = false;

  string describe(bool descExpr=false) {
    if (_rhs is null)
      return "( " ~ _lhs.describe(true) ~ " )";
    else if (_inclusive)
      return "( " ~ _lhs.describe(true) ~ " : " ~ _rhs.describe(true) ~ " )";
    else
      return "( " ~ _lhs.describe(true) ~ " .. " ~ _rhs.describe(true) ~ " )";
  }

  long evaluate() {
    assert (_rhs is null);
    return _lhs.evaluate();
  }

  CstVecDistSetElem _esdl__unroll(CstIterator iter, ulong n) {
    if (_rhs is null)
      return new CstVecDistSetElem(_lhs._esdl__unroll(iter, n), null, _inclusive);
    else
      return new CstVecDistSetElem(_lhs._esdl__unroll(iter, n),
				   _rhs._esdl__unroll(iter, n), _inclusive);
  }

  this(CstVecTerm lhs, CstVecTerm rhs, bool inclusive=false) {
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

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _lhs.setDomainContext(pred, context);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _lhs.isSolved() && (_rhs is null || _rhs.isSolved());
  }

  void annotate(CstSolverAgent agent) {
    _lhs.annotate(agent);
    if (_rhs !is null) {
      _rhs.annotate(agent);
    }
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    _lhs.writeExprString(str);
    if (_rhs !is null) {
      if (_inclusive) str ~= " : ";
      else str ~= " .. ";
      _rhs.writeExprString(str);
    }
  }
  
  void calcHash(ref Hash hash){
    _lhs.calcHash(hash);
    if (_rhs !is null) {
      if (_inclusive) hash.modify(58);
      else hash.modify(46);
      _rhs.calcHash(hash);
    }
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(0);
    _lhs.makeHash();
    _hash.modify(_lhs.hashValue());
    if (_rhs !is null) {
      _rhs.makeHash();
      if (_inclusive) _hash.modify(58);
      else _hash.modify(46);
      _hash.modify(_rhs.hashValue());
    }
  }

}

class CstUniqueSetElem
{
  import std.conv;

  // to make that more generic, could _vec be CstVecExpr
  CstVecTerm _vec;
  CstDomSet  _arr;

  bool _inclusive = false;

  string describe(bool descExpr=false) {
    if (_arr !is null) {
      assert (_vec is null);
      return "( " ~ _arr._esdl__getFullName ~ "[] )";
    }
    else {
      assert (_arr is null);
      return "( " ~ _vec.describe(true) ~ " )";
    }
  }

  CstUniqueSetElem _esdl__unroll(CstIterator iter, ulong n) {
    if (_arr !is null) {
      assert (_vec is null);
      return new CstUniqueSetElem(_arr._esdl__unroll(iter, n));
    }
    else {
      assert (_arr is null);
      return new CstUniqueSetElem(_vec._esdl__unroll(iter, n));
    }
  }

  this(CstVecTerm vec) {
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

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    if (_arr !is null) {
      _arr.setDomainArrContext(pred, context);
      assert (pred._unresolvedRndArrs.length > 0 || pred._unresolvedVarArrs.length > 0);
    }
    if (_vec !is null)
      _vec.setDomainContext(pred, context);
  }

  bool isSolved() {
    return false;
  }

  void annotate(CstSolverAgent agent) {
    if (_arr !is null) _arr.annotate(agent);
    else               _vec.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    if (_arr !is null) {
      str ~= "[ ";
      _arr.writeExprString(str);
      str ~= " ]";
    }
    else {
      _vec.writeExprString(str);
    }
  }
  
  void calcHash(ref Hash hash){
    if (_arr !is null) {
      hash.modify(91);
      _arr.calcHash(hash);
      hash.modify(93);
    }
    else {
      _vec.calcHash(hash);
    }
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }

  void makeHash() {
    if (_arr !is null){
      _hash = Hash(91);
      _arr.makeHash();
      _hash.modify(_arr.hashValue());
      _hash.modify(93);
    }
    else {
      _hash = Hash(0);
      _vec.makeHash();
      _hash.modify(_vec.hashValue());
    }
  }

  CstVecType getVecType() {
    if (_arr !is null) return _arr.getVecType();
    else return _vec.getVecType();
  }
  

  bool inAssoc(ref bool[bool] assoc) {
    if (_arr !is null) {
      foreach (leaf; _arr[]) {
	bool val = cast(bool) leaf.evaluate();
	if (val in assoc) return true;
	else assoc[val] = true;
      }
      return false;
    }
    else {
      bool val = cast(bool) _vec.evaluate();
      if (val in assoc) return true;
      else assoc[val] = true;
      return false;
    }
  }

  bool inAssoc(ref bool[int] assoc) {
    if (_arr !is null) {
      foreach (leaf; _arr[]) {
	int val = cast(int) leaf.evaluate();
	if (val in assoc) return true;
	else assoc[val] = true;
      }
      return false;
    }
    else {
      int val = cast(int) _vec.evaluate();
      if (val in assoc) return true;
      else assoc[val] = true;
      return false;
    }
  }  

  bool inAssoc(ref bool[uint] assoc) {
    if (_arr !is null) {
      foreach (leaf; _arr[]) {
	uint val = cast(uint) leaf.evaluate();
	if (val in assoc) return true;
	else assoc[val] = true;
      }
      return false;
    }
    else {
      uint val = cast(uint) _vec.evaluate();
      if (val in assoc) return true;
      else assoc[val] = true;
      return false;
    }
  }

  bool inAssoc(ref bool[long] assoc) {
    if (_arr !is null) {
      foreach (leaf; _arr[]) {
	long val = cast(long) leaf.evaluate();
	if (val in assoc) return true;
	else assoc[val] = true;
      }
      return false;
    }
    else {
      long val = cast(long) _vec.evaluate();
      if (val in assoc) return true;
      else assoc[val] = true;
      return false;
    }
  }  

  bool inAssoc(ref bool[ulong] assoc) {
    if (_arr !is null) {
      foreach (leaf; _arr[]) {
	ulong val = cast(ulong) leaf.evaluate();
	if (val in assoc) return true;
	else assoc[val] = true;
      }
      return false;
    }
    else {
      ulong val = cast(ulong) _vec.evaluate();
      if (val in assoc) return true;
      else assoc[val] = true;
      return false;
    }
  }
}


class CstInsideSetElem
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;

  CstDomSet  _arr;

  bool _inclusive = false;

  string describe(bool descExpr=false) {
    if (_arr !is null)
      return "( " ~ _arr._esdl__getFullName ~ "[] )";
    else {
      assert (_arr is null);
      if (_rhs is null)
	return "( " ~ _lhs.describe(true) ~ " )";
      else if (_inclusive)
	return "( " ~ _lhs.describe(true) ~ " : " ~ _rhs.describe(true) ~ " )";
      else
	return "( " ~ _lhs.describe(true) ~ " .. " ~ _rhs.describe(true) ~ " )";
    }
  }

  CstInsideSetElem _esdl__unroll(CstIterator iter, ulong n) {
    if (_arr !is null) {
      assert (_lhs is null);
      return new CstInsideSetElem(_arr._esdl__unroll(iter, n));
    }
    else {
      assert (_arr is null);
      if (_rhs is null)
	return new CstInsideSetElem(_lhs._esdl__unroll(iter, n), null, _inclusive);
      else
	return new CstInsideSetElem(_lhs._esdl__unroll(iter, n),
				    _rhs._esdl__unroll(iter, n), _inclusive);
    }
  }

  this(CstVecTerm lhs, CstVecTerm rhs, bool inclusive=false) {
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

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    if (_arr !is null) {
      _arr.setDomainArrContext(pred, context);
      // assert (rndArrs.length > 0 || varArrs.length > 0);
    }
    if (_lhs !is null)
      _lhs.setDomainContext(pred, context);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, context);
  }

  bool isSolved() {
    return false;
  }

  void annotate(CstSolverAgent agent) {
    if (_arr !is null) _arr.annotate(agent);
    else {
      _lhs.annotate(agent);
      if (_rhs !is null) _rhs.annotate(agent);
    }
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
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
  
  void calcHash(ref Hash hash){
    if (_arr !is null) {
      hash.modify(91);
      _arr.calcHash(hash);
      hash.modify(93);
    }
    else {
      _lhs.calcHash(hash);
      if (_rhs !is null) {
	if (_inclusive) hash.modify(58);
	else hash.modify(46);
	_rhs.calcHash(hash);
      }
    }
  }

  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    if (_arr !is null){
      _hash = Hash(91);
      _arr.makeHash();
      _hash.modify(_arr.hashValue());
      _hash.modify(93);
    }
    else {
      _hash = Hash(0);
      _lhs.makeHash();
      _hash.modify(_lhs.hashValue());
      if (_rhs !is null) {
	if (_inclusive) _hash.modify(58);
	else _hash.modify(46);
	_hash.modify(_rhs.hashValue());
      }
    }
  }
  
  final void visit(CstDistSolverBase dist) {
    if (_arr !is null) _arr.visit(dist);
    else if (_lhs !is null) {
      if (_rhs !is null) {
	if (_inclusive) {
	  assert (_lhs.evaluate() <= _rhs.evaluate());
	  for (ulong val = _lhs.evaluate(); val <= _rhs.evaluate(); val += 1) {
	    dist.purge(val);
	  }
	}
	else {
	  assert (_lhs.evaluate() < _rhs.evaluate());
	  for (ulong val = _lhs.evaluate(); val < _rhs.evaluate(); val += 1) {
	    dist.purge(val);
	  }
	}
      }
      else {
	dist.purge(_lhs.evaluate());
      }
    }
  }

  final bool eval(CstVecTerm vec) {
    import std.conv: to;
    if (_arr !is null) {
      CstVecType type = getCommonVecType(_arr.getVecType(), vec.getVecType());

      switch (type) {
      case CstVecType.BOOL:
	return canFind!((CstDomBase a, CstVecTerm b) {
	    return cast(bool) a.evaluate() == cast(bool) b.evaluate();
	  }) (_arr[], vec);
      case CstVecType.INT:
	return canFind!((CstDomBase a, CstVecTerm b) {
	    return cast(int) a.evaluate() == cast(int) b.evaluate();
	  }) (_arr[], vec);
      case CstVecType.UINT:
	return canFind!((CstDomBase a, CstVecTerm b) {
	    return cast(uint) a.evaluate() == cast(uint) b.evaluate();
	  }) (_arr[], vec);
      case CstVecType.LONG:
	return canFind!((CstDomBase a, CstVecTerm b) {
	    return cast(long) a.evaluate() == cast(long) b.evaluate();
	  }) (_arr[], vec);
      case CstVecType.ULONG:
	return canFind!((CstDomBase a, CstVecTerm b) {
	    return cast(ulong) a.evaluate() == cast(ulong) b.evaluate();
	  }) (_arr[], vec);
      // case CstVecType.CENT:
      // 	return canFind!((CstDomBase a, CstVecTerm b) {
      // 	    return cast(cent) a.evaluate() == cast(cent) b.evaluate();
      // 	  }) (_arr[], vec);
      // case CstVecType.UCENT:
      // 	return canFind!((CstDomBase a, CstVecTerm b) {
      // 	    return cast(ucent) a.evaluate() == cast(ucent) b.evaluate();
      // 	  }) (_arr[], vec);
      default: assert (false, "Type " ~ type.to!string() ~ " not supported");
      }
    }
    else if (_rhs is null) {
      CstVecType type = getCommonVecType(_lhs.getVecType(), vec.getVecType());
      switch (type) {
      case CstVecType.BOOL:
	return cast(bool) vec.evaluate() == cast(bool) _lhs.evaluate();
      case CstVecType.INT:
	return cast(int) vec.evaluate() == cast(int) _lhs.evaluate();
      case CstVecType.UINT:
	return cast(uint) vec.evaluate() == cast(uint) _lhs.evaluate();
      case CstVecType.LONG:
	return cast(long) vec.evaluate() == cast(long) _lhs.evaluate();
      case CstVecType.ULONG:
	return cast(ulong) vec.evaluate() == cast(ulong) _lhs.evaluate();
      default: assert (false, "Type " ~ type.to!string() ~ " not supported");
      }
    }
    else {
      CstVecType type = getCommonVecType(vec.getVecType(),
					 getCommonVecType(_lhs.getVecType(),
							  _rhs.getVecType()));
      switch (type) {
      case CstVecType.BOOL: 
	return cast(bool) vec.evaluate() >= cast(bool) _lhs.evaluate()
	  && (_inclusive ? cast(bool) vec.evaluate() <= cast(bool) _rhs.evaluate() :
	      cast(bool) vec.evaluate() < cast(bool) _rhs.evaluate());
      case CstVecType.INT: 
	return cast(int) vec.evaluate() >= cast(int) _lhs.evaluate()
	  && (_inclusive ? cast(int) vec.evaluate() <= cast(int) _rhs.evaluate() :
	      cast(int) vec.evaluate() < cast(int) _rhs.evaluate());
      case CstVecType.UINT: 
	return cast(uint) vec.evaluate() >= cast(uint) _lhs.evaluate()
	  && (_inclusive ? cast(uint) vec.evaluate() <= cast(uint) _rhs.evaluate() :
	      cast(uint) vec.evaluate() < cast(uint) _rhs.evaluate());
      case CstVecType.LONG: 
	return cast(long) vec.evaluate() >= cast(long) _lhs.evaluate()
	  && (_inclusive ? cast(long) vec.evaluate() <= cast(long) _rhs.evaluate() :
	      cast(long) vec.evaluate() < cast(long) _rhs.evaluate());
      case CstVecType.ULONG: 
	return cast(ulong) vec.evaluate() >= cast(ulong) _lhs.evaluate()
	  && (_inclusive ? cast(ulong) vec.evaluate() <= cast(ulong) _rhs.evaluate() :
	      cast(ulong) vec.evaluate() < cast(ulong) _rhs.evaluate());
      default: assert (false, "Type " ~ type.to!string() ~ " not supported");
      }
    }
  }
}

class CstLogicWeightedDistSetElem
{
  import std.conv;

  CstLogicTerm _term;
  CstVecTerm   _weight;
  bool         _perItem = false;

  string describe(bool descExpr=false) {
    string str = "( " ~ _term.describe(true);
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.describe(true) ~ " )";
    return str;
  }

  CstLogicWeightedDistSetElem _esdl__unroll(CstIterator iter, ulong n) {
    return new CstLogicWeightedDistSetElem(_term._esdl__unroll(iter, n),
					   _weight._esdl__unroll(iter, n),
					   _perItem);
  }

  this(CstLogicTerm term, CstVecTerm weight, bool perItem=false) {
    _term = term;
    _weight = weight;
    _perItem = perItem;
  }

  // bool isConst() {
  //   return false;
  // }

  // bool isIterator() {
  //   return false;
  // }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _term.setDomainContext(pred, context);
    _weight.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _term.isSolved() && _weight.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _term.annotate(agent);
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    import std.conv: to;
    _term.writeExprString(str);
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.evaluate().to!string;
  }
  
  void calcHash(ref Hash hash){
    _term.calcHash(hash);
    if (_perItem) hash.modify(64);
    else hash.modify(42);
    hash.modify(_weight.evaluate());
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(0);
    _term.makeHash();
    _hash.modify(_term.hashValue());
    if (_perItem) _hash.modify(64);
    else _hash.modify(42);
    // _hash.modify(_weight.evaluate()); // cant call evaluate here because it isnt resolved
    _hash.modify('w');
  }
}

class CstVecWeightedDistSetElem
{
  import std.conv;

  CstVecDistSetElem _range;
  CstVecTerm   _weight;
  bool         _perItem = false;

  string describe(bool descExpr=false) {
    string str = "( " ~ _range.describe(true);
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.describe(true) ~ " )";
    return str;
  }

  CstVecWeightedDistSetElem _esdl__unroll(CstIterator iter, ulong n) {
    return new CstVecWeightedDistSetElem(_range._esdl__unroll(iter, n),
					 _weight._esdl__unroll(iter, n),
					 _perItem);
  }

  this(CstVecDistSetElem range, CstVecTerm weight, bool perItem=false) {
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

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _range.setDomainContext(pred, context);
    _weight.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _range.isSolved() && _weight.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _range.annotate(agent);
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    import std.conv: to;
    _range.writeExprString(str);
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.evaluate().to!string;
  }

  void calcHash(ref Hash hash){
    _range.calcHash(hash);
    if (_perItem) hash.modify(64);
    else hash.modify(42);
    hash.modify(_weight.evaluate());
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(0);
    _range.makeHash();
    _hash.modify(_range.hashValue());
    if (_perItem) _hash.modify(64);
    else _hash.modify(42);
    _hash.modify(_weight.evaluate());
  }
}

class CstLogicDistExpr(T): CstLogicExpr
{
  import std.conv;
  import esdl.solver.dist: CstLogicDistSolver, CstLogicDistRange;

  CstDomBase _vec;
  CstLogicWeightedDistSetElem[] _dists;

  CstLogicDistSolver!T _rs;
  
  this(CstDomBase vec, CstLogicWeightedDistSetElem[] dists) {
    _vec = vec;
    _dists = dists;
  }

  private final void initDistSolver() {
    _rs = new CstLogicDistSolver!T(_vec);
    foreach (dist; _dists) {
      T term = cast(T) dist._term.eval();
      T rhs;
      int weight = cast(int) dist._weight.evaluate();
      bool perItem = dist._perItem;
      _rs ~= CstLogicDistRange!T(term, weight, perItem);
    }
  }

  CstDistSolverBase getDist() {
    if (_rs is null) initDistSolver();
    return _rs;
  }

  string describe(bool descExpr=false) {
    string str = "( " ~ _vec.describe(true) ~ " dist ";
    foreach (dist; _dists) {
      assert (dist !is null);
      str ~= dist.describe(true) ~ ", ";
    }
    str ~= " )";
    return str;
  }

  void visit(CstSolver solver) {
    solver.pushToEvalStack(false);
    _vec.visit(solver);
    solver.processEvalStack(CstInsideOp.INSIDE);
    foreach (dist; _dists) {
      auto elem = dist._term;
      elem.visit(solver);
      solver.processEvalStack(CstInsideOp.EQUAL);
    }
    solver.processEvalStack(CstInsideOp.DONE);
  }
  
  override CstLogicDistExpr!T _esdl__unroll(CstIterator iter, ulong n) {
    CstLogicWeightedDistSetElem[] dists;
    foreach (dist; _dists) {
      dists ~= dist._esdl__unroll(iter, n);
    }
    return new CstLogicDistExpr!T(cast (CstDomBase) (_vec._esdl__unroll(iter, n)), dists);
  }

  override void setDistPredContext(CstPredicate pred) {
    pred.distDomain(_vec);
    _vec.setDistPred(pred);
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    pred.addUnresolvedRnd(_vec);
    size_t rndLen = pred._unresolvedRnds.length;
    size_t rndArrLen = pred._unresolvedRndArrs.length;
    size_t distLen = pred._dists.length;
    foreach (dist; _dists)	// CstLogicWeightedDistSetElem
      dist.setDomainContext(pred, context);
    assert (pred._unresolvedRnds.length == rndLen &&
	    pred._dists.length == distLen &&
	    pred._unresolvedRndArrs.length == rndArrLen);
  }

  bool isSolved() {
    return _vec.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _vec.annotate(agent);
    foreach (dist; _dists) dist.annotate(agent);
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    str ~= "DIST ";
    _vec.writeExprString(str);
    foreach (dist; _dists) {
      dist.writeExprString(str);
    }
  }
  
  void calcHash(ref Hash hash){
    hash.modify(100);
    _vec.calcHash(hash);
    foreach (dist; _dists) {
      dist.calcHash(hash);
    }
  }

  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(100);
    _vec.makeHash();
    _hash.modify(_vec.hashValue());
    foreach (dist; _dists){
      dist.makeHash();
      _hash.modify(dist.hashValue());
    }
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }

  void visit (CstDistSolverBase solver) { assert (false); }
  
  bool eval() {assert (false, "Unable to evaluate CstLogicDistExpr");}

  override void _esdl__scan() { }
}

class CstVecDistExpr(T): CstLogicExpr
{
  import std.conv;
  import esdl.solver.dist: CstVecDistSolver, CstVecDistRange;

  CstDomBase _vec;
  CstVecWeightedDistSetElem[] _dists;

  CstVecDistSolver!T _rs;
  
  this(CstDomBase vec, CstVecWeightedDistSetElem[] dists) {
    _vec = vec;
    _dists = dists;
  }

  private final void initDistSolver() {
    _rs = new CstVecDistSolver!T(_vec);
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
      _rs ~= CstVecDistRange!T(lhs, rhs, weight, perItem);
    }
  }

  CstDistSolverBase getDist() {
    if (_rs is null) initDistSolver();
    return _rs;
  }

  string describe(bool descExpr=false) {
    string str = "( " ~ _vec.describe(true) ~ " dist ";
    foreach (dist; _dists) {
      assert (dist !is null);
      str ~= dist.describe(true) ~ ", ";
    }
    str ~= " )";
    return str;
  }

  void visit(CstSolver solver) {
    solver.pushToEvalStack(false);
    _vec.visit(solver);
    solver.processEvalStack(CstInsideOp.INSIDE);
    foreach (dist; _dists) {
      auto elem = dist._range;
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
    }
    solver.processEvalStack(CstInsideOp.DONE);
  }
  
  override CstVecDistExpr!T _esdl__unroll(CstIterator iter, ulong n) {
    CstVecWeightedDistSetElem[] dists;
    foreach (dist; _dists) {
      dists ~= dist._esdl__unroll(iter, n);
    }
    return new CstVecDistExpr!T(cast (CstDomBase) (_vec._esdl__unroll(iter, n)), dists);
  }

  override void setDistPredContext(CstPredicate pred) {
    pred.distDomain(_vec);
    _vec.setDistPred(pred);
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    size_t rndLen = pred._unresolvedRnds.length;
    size_t rndArrLen = pred._unresolvedRndArrs.length;
    size_t distLen = pred._dists.length;
    foreach (dist; _dists)	// CstVecWeightedDistSetElem
      dist.setDomainContext(pred, context);
    assert (pred._unresolvedRnds.length == rndLen &&
	    pred._dists.length == distLen &&
	    pred._unresolvedRndArrs.length == rndArrLen);
    _vec.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _vec.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _vec.annotate(agent);
    foreach (dist; _dists) dist.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    str ~= "DIST ";
    _vec.writeExprString(str);
    foreach (dist; _dists) {
      dist.writeExprString(str);
    }
  }
  
  void calcHash(ref Hash hash){
    hash.modify(100);
    _vec.calcHash(hash);
    foreach (dist; _dists) {
      dist.calcHash(hash);
    }
  }

  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(100);
    _vec.makeHash();
    _hash.modify(_vec.hashValue());
    foreach (dist; _dists){
      dist.makeHash();
      _hash.modify(dist.hashValue());
    }
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }

  void visit (CstDistSolverBase solver) { assert (false); }
  
  bool eval() {assert (false, "Unable to evaluate CstVecDistExpr");}

  override void _esdl__scan() { }
}

// class CstVecSliceExpr: CstVecExpr
// {
//   CstVecTerm _vec;
//   CstVecTerm _lhs;
//   CstVecTerm _rhs;
  
//   string describe(bool descExpr=false) {
//     if (_rhs is null)
//       return _vec.describe(true) ~ "[ " ~ _lhs.describe(true) ~ " ]";
//     else
//       return _vec.describe(true) ~ "[ " ~ _lhs.describe(true) ~ " .. " ~ _rhs.describe(true) ~ " ]";
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

//   override CstVecSliceExpr _esdl__unroll(CstIterator iter, ulong n) {
//     if (_rhs is null)
//       return new CstVecSliceExpr(_vec._esdl__unroll(iter, n),
// 				 _lhs._esdl__unroll(iter, n), null);
//     else 
//       return new CstVecSliceExpr(_vec._esdl__unroll(iter, n),
// 				 _lhs._esdl__unroll(iter, n), _rhs._esdl__unroll(iter, n));
//   }

//   this(CstVecTerm vec, CstVecTerm lhs, CstVecTerm rhs) {
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

//   void setDomainContext(CstPredicate pred, DomainContextEnum context) {
//     _vec.setDomainContext(pred, context);
//     _lhs.setDomainContext(pred, DomainContextEnum.BITINDEX);
//     if (_rhs !is null)
//       _rhs.setDomainContext(pred, DomainContextEnum.BITINDEX);
//   }

//   override bool isSolved() {
//     if (_rhs is null) return _lhs.isSolved() && _vec.isSolved();
//     else return _lhs.isSolved() && _rhs.isSolved() && _vec.isSolved();
//   }
  
//   override void writeExprString(ref _esdl__Sigbuf str) {
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

class CstVecSliceExpr: CstVecExpr
{
  CstVecTerm _vec;
  CstRangeExpr _range;
  
  string describe(bool descExpr=false) {
    return _vec.describe(true) ~ "[ " ~ _range.describe(true) ~ " ]";
  }

  void visit(CstSolver solver) {
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

  long evaluate() {
    ulong vec  = _vec.evaluate();

    ulong lvec = _range._lhs.evaluate();

    ulong rvec;
    if (_range._rhs is null) rvec = lvec + 1;
    else       rvec = _range._rhs.evaluate();

    ulong mask = (1L << (rvec - lvec)) - 1;

    vec = vec >> lvec;

    vec = vec & mask;

    return vec;
  }

  override CstVecType getVecType() {
    return _vec.getVecType();
  }

  CstVecSliceExpr _esdl__unroll(CstIterator iter, ulong n) {
    return new CstVecSliceExpr(_vec._esdl__unroll(iter, n),
			       _range._esdl__unroll(iter, n));
  }

  this(CstVecTerm vec, CstRangeExpr range) {
    _vec = vec;
    _range = range;
  }

  uint bitcount() {
    return _vec.bitcount();
  }
  
  bool signed() {
    return false;
  }
  
  bool isConst() {
    return false;
  }

  bool isIterator() {
    return false;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _vec.setDomainContext(pred, context);
    _range.setDomainContext(pred, DomainContextEnum.BITINDEX);
  }

  bool isSolved() {
    return _range.isSolved() && _vec.isSolved();
  }
  
  void annotate(CstSolverAgent agent) {
    _vec.annotate(agent);
    _range.annotate(agent);
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    _vec.writeExprString(str);
    str ~= '[';
    _range.writeExprString(str);
    str ~= ']';
  }

  void calcHash(ref Hash hash){
    _vec.calcHash(hash);
    hash.modify(91);
    _range.calcHash(hash);
    hash.modify(93);
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(0);
    _vec.makeHash();
    _hash.modify(_vec.hashValue());
    _range.makeHash();
    _hash.modify(_range.hashValue());
  }

  void _esdl__scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

}

// class CstVecIndexExpr: CstVecExpr
// {
//   CstVecTerm _vec;
//   CstVecTerm _index;
  
//   string describe(bool descExpr=false) {
//     return _vec.describe(true) ~ "[ " ~ _index.describe(true) ~ " ]";
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

//   override CstVecIndexExpr _esdl__unroll(CstIterator iter, ulong n) {
//     return new CstVecIndexExpr(_vec._esdl__unroll(iter, n),
// 			       _index._esdl__unroll(iter, n));
//   }

//   this(CstVecTerm vec, CstVecTerm index) {
//     _vec = vec;
//     _index = index;
//   }

//   bool isConst() {
//     return false;
//   }

//   bool isIterator() {
//     return false;
//   }

//   void setDomainContext(CstPredicate pred, DomainContextEnum context) {
//     _vec.setDomainContext(pred, context);
//     _index.setDomainContext(pred, DomainContextEnum.BITINDEX);
//   }

//   override bool isSolved() {
//     return _index.isSolved() && _vec.isSolved();
//   }
  
//   override void writeExprString(ref _esdl__Sigbuf str) {
//     _vec.writeExprString(str);
//     str ~= '[';
//     _index.writeExprString(str);
//     str ~= ']';
//   }
// }

class CstNotVecExpr: CstVecExpr
{
  import std.conv;

  CstVecTerm _expr;

  string describe(bool descExpr=false) {
    return "( ~ " ~ _expr.describe(true) ~ " )";
  }

  void visit(CstSolver solver) {
    _expr.visit(solver);
    solver.processEvalStack(CstUnaryOp.NOT);
  }

  // bool getVal(ref long val) {
  //   auto retval = _expr.getVal(val);
  //   val = ~val;
  //   return retval;
  // }

  long evaluate() {
    return ~(_expr.evaluate());
  }

  override CstVecType getVecType() {
    return _expr.getVecType();
  }

  CstNotVecExpr _esdl__unroll(CstIterator iter, ulong n) {
    return new CstNotVecExpr(_expr._esdl__unroll(iter, n));
  }

  this(CstVecTerm expr) {
    _expr = expr;
  }

  uint bitcount() {
    uint count = _expr.bitcount();

    if (count <= 32) return 32;
    else if (count <= 64) return 64;
    else return count;
  }
  
  bool signed() {
    bool sign = _expr.signed();
    uint count = _expr.bitcount();

    if (count == 32 || count == 64) return sign;
    else return true;		// int promotion
  }
  
  bool isConst() {
    return _expr.isConst();
  }

  bool isIterator() {
    return false;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _expr.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _expr.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _expr.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    str ~= "(NOT ";
    _expr.writeExprString(str);
    str ~= ')';
  }
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(78);
    _expr.calcHash(hash);
    hash.modify(41);
  }

  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    _hash.modify(78);
    _expr.makeHash();
    _hash.modify(_expr.hashValue());
    _hash.modify(41);
  }

  void _esdl__scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

}

class CstNegVecExpr: CstVecExpr
{
  import std.conv;

  CstVecTerm _expr;

  string describe(bool descExpr=false) {
    return "( - " ~ _expr.describe(true) ~ " )";
  }

  void visit(CstSolver solver) {
    _expr.visit(solver);
    solver.processEvalStack(CstUnaryOp.NEG);
  }

  // bool getVal(ref long val) {
  //   auto retval = _expr.getVal(val);
  //   val = -val;
  //   return retval;
  // }

  long evaluate() {
    return -(_expr.evaluate());
  }

  override CstVecType getVecType() {
    return _expr.getVecType();
  }

  CstNegVecExpr _esdl__unroll(CstIterator iter, ulong n) {
    return new CstNegVecExpr(_expr._esdl__unroll(iter, n));
  }

  this(CstVecTerm expr) {
    _expr = expr;
  }

  uint bitcount() {
    uint count = _expr.bitcount();

    if (count <= 32) return 32;
    else if (count <= 64) return 64;
    else return count;
  }
  
  bool signed() {
    bool sign = _expr.signed();
    uint count = _expr.bitcount();

    if (count == 32 || count == 64) return sign;
    else return true;		// int promotion
  }
  
  bool isConst() {
    return _expr.isConst();
  }

  bool isIterator() {
    return false;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _expr.setDomainContext(pred, context);
  }

  bool isSolved() {
    return _expr.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _expr.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    str ~= "(NEG ";
    _expr.writeExprString(str);
    str ~= ')';
  }
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(126);
    _expr.calcHash(hash);
    hash.modify(41);
  }
    
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    _hash.modify(126);
    _expr.makeHash();
    _hash.modify(_expr.hashValue());
    _hash.modify(41);
  }

  void _esdl__scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

}


class CstLogic2LogicExpr: CstLogicExpr
{
  import std.conv;

  CstLogicTerm _lhs;
  CstLogicTerm _rhs;
  CstLogicOp _op;

  this(CstLogicTerm lhs, CstLogicTerm rhs, CstLogicOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  string describe(bool descExpr=false) {
    return "( " ~ _lhs.describe(true) ~ " " ~ _op.to!string ~ " " ~ _rhs.describe(true) ~ " )";
  }

  void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  override CstLogic2LogicExpr _esdl__unroll(CstIterator iter, ulong n) {
    return new CstLogic2LogicExpr(_lhs._esdl__unroll(iter, n),
				  _rhs._esdl__unroll(iter, n), _op);
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _lhs.setDomainContext(pred, context);
    _rhs.setDomainContext(pred, context);
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }

  
  bool isSolved() { return _lhs.isSolved && _rhs.isSolved(); }

  void annotate(CstSolverAgent agent) {
    _lhs.annotate(agent);
    _rhs.annotate(agent);
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    import std.format: sformat;
    char[16] buff;
    str ~= '(';
    str ~= sformat(buff[], "%s", _op);
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ")\n";
  }

  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(_op);
    hash.modify(32);
    _lhs.calcHash(hash);
    hash.modify(32);
    _rhs.calcHash(hash);
    hash.modify(41);
  }
    
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    bool isSymetrical;
    _lhs.makeHash();
    _rhs.makeHash();
    final switch (_op){
    case CstLogicOp.LOGICAND:
      isSymetrical = true;
      break;
    case CstLogicOp.LOGICOR:
      isSymetrical = true;
      break;
    case CstLogicOp.LOGICIMP:
      isSymetrical = false;
      break;
    case CstLogicOp.LOGICNOT:
      isSymetrical = false;
      break;
    case CstLogicOp.LOGICEQ:
      isSymetrical = true;
      break;
    case CstLogicOp.LOGICNEQ:
      isSymetrical = true;
      break;
    }
    if (isSymetrical){
      if (_lhs.hashValue() > _rhs.hashValue()){
    	CstLogicTerm temp = _lhs;
    	_lhs = _rhs;
    	_rhs = temp;
      }
    }
    _hash.modify(_op);
    _hash.modify(32);
    _hash.modify(_lhs.hashValue());
    _hash.modify(32);
    _hash.modify(_rhs.hashValue());
    _hash.modify(41);
  }
  
  CstDistSolverBase getDist() {
    assert (false);
  }

  override bool eval() {
    final switch (_op) {
    case CstLogicOp.LOGICAND:
      return _lhs.eval() && _rhs.eval();
    case CstLogicOp.LOGICOR:
      return _lhs.eval() || _rhs.eval();
    case CstLogicOp.LOGICIMP:
      return (! _lhs.eval()) || _rhs.eval();
    case CstLogicOp.LOGICNOT:
      assert (false);
    case CstLogicOp.LOGICEQ:
      return (_lhs.eval() == _rhs.eval());
    case CstLogicOp.LOGICNEQ:
      return (_lhs.eval() != _rhs.eval());
    }
  }
  
  override void _esdl__scan() { }
}

class CstInsideArrExpr: CstLogicExpr
{
  CstInsideSetElem[] _elems;

  CstVecTerm _term;

  bool _notinside = false;

  void negate() {
    _notinside = !_notinside;
  }

  CstInsideArrExpr dup() {
    CstInsideArrExpr expr = new CstInsideArrExpr(_term);
    expr._elems = _elems;
    return expr;
  }

  string describe(bool descExpr=false) {
    string description = "( " ~ _term.describe(true) ~ " inside [";
    foreach (elem; _elems) {
      description ~= elem.describe(true);
    }
    description ~= "]";
    return description;
  }

  void visit(CstSolver solver) {
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

  void visit(CstDistSolverBase solver) {
    assert (_term == solver.getDomain());
    assert (_notinside is true);
    foreach (elem; _elems) {
      // import std.stdio;
      // writeln("visit CstDistSolverBase");
      elem.visit(solver);
    }
  }
  

  this(CstVecTerm term) {
    _term = term;
  }

  void addElem(CstInsideSetElem elem) {
    _elems ~= elem;
  }

  override CstInsideArrExpr _esdl__unroll(CstIterator iter, ulong n) {
    CstInsideArrExpr unrolled = new CstInsideArrExpr(_term._esdl__unroll(iter, n));
    foreach (elem; _elems) {
      unrolled.addElem(elem._esdl__unroll(iter, n));
    }
    unrolled._notinside = _notinside;
    return unrolled;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    // if (_notinside) {
    //   // special processing for dist domains
    //   CstDomBase tdom = _term.getDomain();
    //   if (tdom !is null && tdom.getDistPred() !is null) {
    // 	CstPredicate distPred = tdom.getDistPred();
    // 	foreach (elem; _elems) {
    // 	  elem.setDomainContext(pred, DomainContextEnum.DIST);
    // 	}
    // 	if (pred._distRnds.length > 0) {
    // 	  foreach (rnd; pred._distRnds)
    // 	    distPred.addDep(rnd, context);
    // 	  pred._distRnds.reset();
    // 	}
    //   }
    // }

    _term.setDomainContext(pred, context);
    foreach (elem; _elems) {
      elem.setDomainContext(pred, context);
    }
  }

  bool isCompatWithDist(CstDomBase dom) {
    CstTerm term = cast(CstTerm) _term;
    if (_notinside && term == dom) return true;
    else return false;
  }
  
  bool isSolved() { return false; }

  void annotate(CstSolverAgent agent) {
    _term.annotate(agent);
    foreach (elem; _elems) elem.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    if (_notinside) str ~= "(! INSIDE ";
    else            str ~= "(INSIDE ";
    _term.writeExprString(str);
    str ~= " [ ";
    foreach (elem; _elems) {
      elem.writeExprString(str);
      str ~= ' ';
    }
    str ~= "])\n";
  }
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    if (_notinside) hash.modify(92);
    else            hash.modify(47);
    _term.calcHash(hash);
    hash.modify(91);
    foreach (elem; _elems)
      elem.calcHash(hash);
    hash.modify(93);
    hash.modify(41);
  }
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    if (_notinside) _hash.modify(92);
    else            _hash.modify(47);
    _term.makeHash();
    _hash.modify(_term.hashValue());
    _hash.modify(91);
    foreach (elem; _elems){
      elem.makeHash();
      _hash.modify(elem.hashValue());
    }
    _hash.modify(93);
    _hash.modify(41);
  }
  
  CstDistSolverBase getDist() {
    assert (false);
  }

  override bool eval() {
    bool inside = canFind!((CstInsideSetElem a, CstVecTerm b) =>
			   a.eval(b))(_elems, _term);
    if (_notinside) return ! inside;
    else return inside;
  }

  override void _esdl__scan() { }

}

class CstUniqueArrExpr: CstLogicExpr
{
  CstUniqueSetElem[] _elems;

  string describe(bool descExpr=false) {
    string description = "( unique [";
    foreach (elem; _elems) {
      description ~= elem.describe(true);
    }
    description ~= "]";
    return description;
  }

  void visit(CstSolver solver) {
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

  override CstUniqueArrExpr _esdl__unroll(CstIterator iter, ulong n) {
    CstUniqueArrExpr unrolled = new CstUniqueArrExpr();
    foreach (elem; _elems) {
      unrolled.addElem(elem._esdl__unroll(iter, n));
    }
    return unrolled;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    pred.setUniqueFlag();
    foreach (elem; _elems) {
      elem.setDomainContext(pred, context);
    }
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }
  
  bool isSolved() { return false; }

  void annotate(CstSolverAgent agent) {
    foreach (elem; _elems) elem.annotate(agent);
  }
  
  void writeExprString(ref _esdl__Sigbuf str) {
    str ~= "(UNIQUE ";
    str ~= " [";
    foreach (elem; _elems)
      elem.writeExprString(str);
    str ~= "])\n";
  }
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(117);
    hash.modify(91);
    foreach (elem; _elems)
      elem.calcHash(hash);
    hash.modify(93);
    hash.modify(41);
  }
 
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    _hash = Hash(117);
    _hash = Hash(91);
    foreach (elem; _elems){
      elem.makeHash();
      _hash.modify(elem.hashValue());
    }
    _hash.modify(93);
    _hash.modify(41);
  }
  

  CstDistSolverBase getDist() { assert (false); }

  override bool eval() {
    import std.conv: to;
    CstVecType type;
    foreach (elem; _elems) {
      if (type < elem.getVecType()) {
	type = elem.getVecType();
      }
    }

    switch (type) {
    case CstVecType.BOOL:
      bool[bool] assoc;
      foreach (elem; _elems) {if (elem.inAssoc(assoc)) return false;}
      return true;
    case CstVecType.INT:
      bool[int] assoc;
      foreach (elem; _elems) {if (elem.inAssoc(assoc)) return false;}
      return true;
    case CstVecType.UINT:
      bool[uint] assoc;
      foreach (elem; _elems) {if (elem.inAssoc(assoc)) return false;}
      return true;
    case CstVecType.LONG:
      bool[long] assoc;
      foreach (elem; _elems) {if (elem.inAssoc(assoc)) return false;}
      return true;
    case CstVecType.ULONG:
      bool[ulong] assoc;
      foreach (elem; _elems) {if (elem.inAssoc(assoc)) return false;}
      return true;
    default: assert (false, "Type " ~ type.to!string() ~ " not supported");
    }
  }

  override void _esdl__scan() { }
}

// TBD
class CstIteLogicExpr: CstLogicExpr
{
  string describe(bool descExpr=false) {
    return "CstIteLogicExpr";
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    assert(false, "TBD");
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }
  

  override CstLogicTerm _esdl__unroll(CstIterator iter, ulong n) {
    assert(false, "TBD");
  }

  void visit(CstSolver solver) { assert(false, "TBD"); }

  bool isSolved() { assert(false, "TBD"); }

  CstDistSolverBase getDist() { assert (false); }

  void annotate(CstSolverAgent agent) {
    assert (false, "TBD");
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    assert (false, "TBD");
  }

  void calcHash(ref Hash hash){
    assert (false, "TBD");
  }

  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    assert(false, "TBD");
  }
  

  override bool eval() { assert(false, "TBD"); }
  override void _esdl__scan() { }
}

class CstVec2LogicExpr: CstLogicExpr
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;
  CstCompareOp _op;

  this(CstVecTerm lhs, CstVecTerm rhs, CstCompareOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
  }

  string describe(bool descExpr=false) {
    return "( " ~ _lhs.describe(true) ~ " " ~ _op.to!string ~ " " ~ _rhs.describe(true) ~ " )";
  }

  void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  override CstVec2LogicExpr _esdl__unroll(CstIterator iter, ulong n) {
    // import std.stdio;
    // writeln(_lhs.describe(true) ~ " " ~ _op.to!string ~ " " ~ _rhs.describe(true) ~ " Getting unwound!");
    // writeln("RHS: ", _rhs._esdl__unroll(iter, n).describe(true));
    // writeln("LHS: ", _lhs._esdl__unroll(iter, n).describe(true));
    return new CstVec2LogicExpr(_lhs._esdl__unroll(iter, n),
				_rhs._esdl__unroll(iter, n), _op);
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    // if (_op == CstCompareOp.NEQ) {
    //   // special processing for dist domains
    //   CstDomBase ldom = _lhs.getDomain();
    //   if (ldom !is null && ldom.getDistPred() !is null) {
    // 	CstPredicate distPred = ldom.getDistPred();
    // 	// find if RHS is also a dist domain
    // 	CstDomBase rdom = _rhs.getDomain();
    // 	if (rdom !is null && rdom.getDistPred() !is null) {
    // 	  distPred.addDep(rdom, context);
    // 	}
    // 	else {
    // 	  _rhs.setDomainContext(pred, DomainContextEnum.DIST);
    // 	  if (pred._distRnds.length > 0) {
    // 	    foreach (rnd; pred._distRnds) distPred.addDep(rnd, context);
    // 	    pred._distRnds.reset();
    // 	  }
    // 	}
    //   }
    //   else {
    // 	assert (_rhs !is null);
    // 	CstDomBase rdom = _rhs.getDomain();
    // 	if (rdom !is null && rdom.getDistPred() !is null) {
    // 	  CstPredicate distPred = rdom.getDistPred();
    // 	  _lhs.setDomainContext(pred, DomainContextEnum.DIST);
    // 	  if (pred._distRnds.length > 0) {
    // 	    foreach (rnd; pred._distRnds) distPred.addDep(rnd, context);
    // 	    pred._distRnds.reset();
    // 	  }
    // 	}
    //   }
    // }
    _lhs.setDomainContext(pred, context);
    _rhs.setDomainContext(pred, context);
  }
  
  bool isCompatWithDist(CstDomBase dom) {
    if (_op is CstCompareOp.NEQ) {
      CstDomBase ldom = _lhs.getDomain();
      if (ldom !is null && ldom is dom) return true;
      CstDomBase rdom = _rhs.getDomain();
      if (rdom !is null && rdom is dom) return true;
    }
    return false;
  }

  void visit (CstDistSolverBase solver) {
    assert (_op is CstCompareOp.NEQ);
    // try considering LHS as dom
    CstDomBase ldom = _lhs.getDomain();
    CstDomBase rdom = _rhs.getDomain();
    assert (ldom !is null || rdom !is null);
    if (ldom !is null && ldom is solver.getDomain()) {
      solver.purge(_rhs.evaluate());
    }
    if (rdom !is null && rdom is solver.getDomain()) {
      solver.purge(_lhs.evaluate());
    }
  }
    
  bool isSolved() {
    return _lhs.isSolved && _rhs.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _lhs.annotate(agent);
    _rhs.annotate(agent);
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    import std.format: sformat;
    char[16] buff;
    str ~= '(';
    str ~= sformat(buff[], "%s", _op);
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ")\n";
  }

  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(_op);
    hash.modify(32);
    _lhs.calcHash(hash);
    hash.modify(32);
    _rhs.calcHash(hash);
    hash.modify(41);
  }

  Hash _hash;
  
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    _lhs.makeHash();
    _rhs.makeHash();
    final switch(_op){
    case CstCompareOp.LTH:
      break;
    case CstCompareOp.LTE:
      break;
    case CstCompareOp.GTH:
      CstVecTerm temp = _lhs;
      _lhs = _rhs;
      _rhs = temp;
      _op = CstCompareOp.LTH;
      break;
    case CstCompareOp.GTE:
      CstVecTerm temp = _lhs;
      _lhs = _rhs;
      _rhs = temp;
      _op = CstCompareOp.LTE;
      break;
    case CstCompareOp.EQU:
      if (_lhs.hashValue() > _rhs.hashValue()){
    	CstVecTerm temp = _lhs;
    	_lhs = _rhs;
    	_rhs = temp;
      }
      break;
    case CstCompareOp.NEQ:
      if (_lhs.isDistVar() || _rhs.isDistVar()){
	break;
      }
      if (_lhs.hashValue() > _rhs.hashValue()){
    	CstVecTerm temp = _lhs;
    	_lhs = _rhs;
    	_rhs = temp;
      }
      break;
    }
    _hash.modify(_op);
    _hash.modify(32);
    _hash.modify(_lhs.hashValue());
    _hash.modify(32);
    _hash.modify(_rhs.hashValue());
    _hash.modify(41);
  }

  CstDistSolverBase getDist() {
    assert (false);
  }

  override bool eval() {
    auto lvec = _lhs.evaluate();
    auto rvec = _rhs.evaluate();

    if (_lhs.bitcount() < 32 || (_lhs.bitcount() == 32 && _lhs.signed())) {
      int lhs_ = cast(int) lvec;
      if (_rhs.bitcount() < 32 || (_rhs.bitcount() == 32 && _rhs.signed())) {
	int rhs_ = cast(int) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 32 && !_rhs.signed()) {
	uint rhs_ = cast(uint) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() < 64 || (_rhs.bitcount() == 64 && _rhs.signed())) {
	long rhs_ = cast(long) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 64 && !_rhs.signed()) {
	ulong rhs_ = cast(ulong) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      assert(false, "TBD -- Can not yet handle > 64 bit math operations");
    }
    if (_lhs.bitcount() == 32 && !_lhs.signed) {
      uint lhs_ = cast(uint) lvec;
      if (_rhs.bitcount() < 32 || (_rhs.bitcount() == 32 && _rhs.signed())) {
	int rhs_ = cast(int) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 32 && !_rhs.signed()) {
	uint rhs_ = cast(uint) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() < 64 || (_rhs.bitcount() == 64 && _rhs.signed())) {
	long rhs_ = cast(long) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 64 && !_rhs.signed()) {
	ulong rhs_ = cast(ulong) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      assert(false, "TBD -- Can not yet handle > 64 bit math operations");
    }
    if (_lhs.bitcount() < 64 || (_lhs.bitcount() == 64 && _lhs.signed())) {
      long lhs_ = cast(long) lvec;
      if (_rhs.bitcount() < 32 || (_rhs.bitcount() == 32 && _rhs.signed())) {
	int rhs_ = cast(int) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 32 && !_rhs.signed()) {
	uint rhs_ = cast(uint) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() < 64 || (_rhs.bitcount() == 64 && _rhs.signed())) {
	long rhs_ = cast(long) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 64 && !_rhs.signed()) {
	ulong rhs_ = cast(ulong) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      assert(false, "TBD -- Can not yet handle > 64 bit math operations");
    }
    if (_lhs.bitcount() == 64 && !_lhs.signed()) {
      ulong lhs_ = cast(ulong) lvec;
      if (_rhs.bitcount() < 32 || (_rhs.bitcount() == 32 && _rhs.signed())) {
	int rhs_ = cast(int) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 32 && !_rhs.signed()) {
	uint rhs_ = cast(uint) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() < 64 || (_rhs.bitcount() == 64 && _rhs.signed())) {
	long rhs_ = cast(long) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      if (_rhs.bitcount() == 64 && !_rhs.signed()) {
	ulong rhs_ = cast(ulong) rvec;
	return _esdl__evaluate(lhs_, rhs_, _op);
      }
      assert(false, "TBD -- Can not yet handle > 64 bit math operations");
    }
    assert(false, "TBD -- Can not yet handle > 64 bit math operations");
  }

  override void _esdl__scan() { }
}

class CstNotLogicExpr: CstLogicExpr
{
  CstLogicTerm _expr;

  this(CstLogicTerm expr) {
    _expr = expr;
  }

  string describe(bool descExpr=false) {
    return "( " ~ "!" ~ " " ~ _expr.describe(true) ~ " )";
  }

  void visit(CstSolver solver) {
    _expr.visit(solver);
    solver.processEvalStack(CstLogicOp.LOGICNOT);
  }

  override CstNotLogicExpr _esdl__unroll(CstIterator iter, ulong n) {
    return new CstNotLogicExpr(_expr._esdl__unroll(iter, n));
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    _expr.setDomainContext(pred, context);
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }

  bool isSolved() {
    return _expr.isSolved();
  }

  void annotate(CstSolverAgent agent) {
    _expr.annotate(agent);
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    str ~= "(NOT ";
    _expr.writeExprString(str);
    str ~= ")\n";
  }

  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(78);
    _expr.calcHash(hash);
    hash.modify(41);
  }
  
  Hash _hash;
  
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(40);
    _hash.modify(78);
    _expr.makeHash();
    _hash.modify(_expr.hashValue());
    _hash.modify(41);
  }
  
  CstDistSolverBase getDist() {
    assert (false);
  }

  override bool eval() {return !_expr.eval();}

  override void _esdl__scan() { }
}

class CstVarVisitorExpr: CstLogicExpr
{
  CstVarNodeIntf _obj;

  this(CstVarNodeIntf obj) {
    assert (obj !is null);
    _obj = obj;
  }

  string describe(bool descExpr=false) {
    return "Visitor: " ~ _obj._esdl__getFullName() ~ '\n';
  }

  void visit(CstSolver solver) {
    solver.pushToEvalStack(true);
  }

  override CstVarVisitorExpr _esdl__unroll(CstIterator iter, ulong n) {
    assert (_obj !is null);
    CstIterator iter_ = _obj._esdl__iter();
    if (iter_ is iter) {
      return new CstVarVisitorExpr(_obj._esdl__getChild(n));
    }
    else {
      return this;
    }
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    assert (_obj !is null);
    CstIterator iter = _obj._esdl__iter();
    if (iter !is null) {
      iter.setDomainContext(pred, context);
      pred.addUnresolvedRnd(iter.getLenVec(), context);
    }
  }

  bool isSolved() {
    return false;
  }

  void annotate(CstSolverAgent agent) { }

  void writeExprString(ref _esdl__Sigbuf str) {
    str ~= this.describe(true);
  }

  
  void calcHash(ref Hash hash){
    hash.modify(118);
    hash.modify(_obj._esdl__getFullName());
  }
  Hash _hash;
  
  size_t hashValue() {
    return _hash.hash;
  }
  
  void makeHash(){
    _hash = Hash(118);
    _hash.modify(_obj._esdl__getFullName());
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }

  CstDistSolverBase getDist() {
    assert (false);
  }

  override void _esdl__scan() {
    assert (_obj !is null);
    _obj._esdl__scan();
  }

  override bool eval() {assert(false);}

}
