module esdl.rand.expr;

import esdl.rand.dist;

import esdl.solver.base: CstSolver;

import esdl.rand.misc: rand, _esdl__RandGen, isVecSigned, Unconst, CstVectorOp, CstInsideOp;
import esdl.rand.misc: CstBinaryOp, CstCompareOp, CstLogicOp,
  CstUnaryOp, CstSliceOp, writeHexString, CstUniqueOp;

import esdl.rand.base: DomDistEnum, CstVecExpr, CstLogicExpr, CstDomBase, CstDomSet,
  CstIterator, CstVecNodeIntf, CstVarNodeIntf, CstVecArrIntf, CstVecPrim, DomType,
  CstValue, CstVecTerm, CstLogicTerm;
import esdl.rand.pred: CstPredicate, CstPredGroup;
import esdl.rand.func;

import esdl.data.bvec: isBitVector, toBitVec;
import esdl.data.charbuf;
import std.traits: isIntegral, isBoolean, isStaticArray,
  isSomeChar, EnumMembers, isSigned, OriginalType;

class CstOrderingExpr: CstLogicExpr
{
  CstDomBase _first;
  CstDomBase _second;
  bool _isSolved;
  this (CstDomBase a, CstDomBase b) {
    _first = a;
    _second = b;
  }
  override bool isOrderingExpr() {
    return true;
  }
  override DistRangeSetBase getDist() {
    assert(false);
  }
  override CstVecExpr isNot(CstDomBase A) {
    assert(false);
  }
  override CstLogicExpr unroll(CstIterator iter, ulong n) {
    assert(false);
  }
  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    rnds ~= _first;
    rnds ~= _second;
  }
  bool isSolved() {
    return _isSolved;
  }
  void visit(CstSolver solver) {
    assert(false, "cannot visit an ordering expression");
  }
  void writeExprString(ref Charbuf str) {
    assert(false);
  }
  string describe() {
    string str = "( " ~ _first.describe() ~ " is solved before " ~ _second.describe() ~ " )";
    return str;
  }
  void scan() { }
  bool eval() {
    assert (false);
  }
  void setBool(bool val) {
    assert (false);
  }
}

class CstVecArrExpr: CstVecTerm
{
  import std.conv;

  CstDomSet _arr;
  CstVectorOp _op;

  string describe() {
    return "( " ~ _arr.fullName ~ " " ~ _op.to!string() ~ " )";
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
    assert (false, "TBD");
  }

  CstVecArrExpr unroll(CstIterator iter, ulong n) {
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    pred._vectorOp = _op;
    _arr.setDomainArrContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    assert (rndArrs.length > 0 || varArrs.length > 0);
  }

  bool isSolved() {
    return false;
  }

  void writeExprString(ref Charbuf str) {
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

  string describe() {
    return "( " ~ _lhs.describe ~ " " ~ _op.to!string() ~ " " ~ _rhs.describe ~ " )";
  }

  void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  long evaluate() {
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

  CstVec2VecExpr unroll(CstIterator iter, ulong n) {
    return new CstVec2VecExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
  }

  this(CstVecExpr lhs, CstVecExpr rhs, CstBinaryOp op) {
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
  
  bool isConst() {
    return _lhs.isConst() && _rhs.isConst();
  }

  bool isIterator() {
    return false;
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _lhs.isSolved() && _rhs.isSolved();
  }

  void writeExprString(ref Charbuf str) {
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

  CstRangeExpr unroll(CstIterator iter, ulong n) {
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

  void setDomainContext(CstPredicate pred,
				 ref CstDomBase[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomBase[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomBase[] bitIdxs,
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

  CstDistSetElem unroll(CstIterator iter, ulong n) {
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

  void setDomainContext(CstPredicate pred,
				 ref CstDomBase[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomBase[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomBase[] bitIdxs,
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

  CstUniqueSetElem unroll(CstIterator iter, ulong n) {
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
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

  CstInsideSetElem unroll(CstIterator iter, ulong n) {
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
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

  CstWeightedDistSetElem unroll(CstIterator iter, ulong n) {
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
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

  CstDomBase _vec;
  CstWeightedDistSetElem[] _dists;

  DistRangeSet!T _rs;
  
  this(CstDomBase vec, CstWeightedDistSetElem[] dists) {
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

  DistRangeSetBase getDist() {
    return _rs;
  }

  string describe() {
    string str = "( " ~ _vec.describe() ~ " dist ";
    foreach (dist; _dists) {
      assert (dist !is null);
      str ~= dist.describe() ~ ", ";
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
  
  override CstDistExpr!T unroll(CstIterator iter, ulong n) {
    // import std.stdio;
    // writeln(_lhs.describe() ~ " " ~ _op.to!string ~ " " ~ _rhs.describe() ~ " Getting unwound!");
    // writeln("RHS: ", _rhs.unroll(iter, n).describe());
    // writeln("LHS: ", _lhs.unroll(iter, n).describe());
    return new CstDistExpr!T(cast (CstDomBase) (_vec.unroll(iter, n)), _dists);
  }

  void setDomainContext(CstPredicate pred,
				 ref CstDomBase[] rnds,
				 ref CstDomSet[] rndArrs,
				 ref CstDomBase[] vars,
				 ref CstDomSet[] varArrs,
				 ref CstValue[] vals,
				 ref CstIterator[] iters,
				 ref CstVecNodeIntf[] idxs,
				 ref CstDomBase[] bitIdxs,
				 ref CstVecNodeIntf[] deps) {
    rnds ~= _vec;
    pred.distDomain(_vec);
    _vec.isDist(DomDistEnum.DETECT);
  }

  bool isSolved() {
    return _vec.isSolved();
  }

  void writeExprString(ref Charbuf str) {
    str ~= "DIST ";
    _vec.writeExprString(str);
    foreach (dist; _dists) {
      dist.writeExprString(str);
    }
  }
  
  CstVecExpr isNot(CstDomBase dom){
    return null;
  }

  bool eval() {assert (false, "Enable to evaluate CstDistExpr");}

  void scan() { }
  bool isOrderingExpr() { return false; }
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

//   override CstVecSliceExpr unroll(CstIterator iter, ulong n) {
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

//   void setDomainContext(CstPredicate pred,
// 			ref CstDomBase[] rnds,
//		        ref CstDomSet[] rndArrs,
// 			ref CstDomBase[] vars,
//			ref CstDomSet[] varArrs,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstVecNodeIntf[] idxs,
// 			ref CstDomBase[] bitIdxs,
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
  
  string describe() {
    return _vec.describe() ~ "[ " ~ _range.describe() ~ " ]";
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
    // auto vec  = _vec.evaluate();
    // auto lvec = _lhs.evaluate();
    // auto rvec = _range._rhs.evaluate();

    assert(false, "Can not evaluate a CstVecSliceExpr!");
  }

  CstVecSliceExpr unroll(CstIterator iter, ulong n) {
    return new CstVecSliceExpr(_vec.unroll(iter, n),
			       _range.unroll(iter, n));
  }

  this(CstVecExpr vec, CstRangeExpr range) {
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _range.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _range.isSolved() && _vec.isSolved();
  }
  
  void writeExprString(ref Charbuf str) {
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

//   override CstVecIndexExpr unroll(CstIterator iter, ulong n) {
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

//   void setDomainContext(CstPredicate pred,
// 			ref CstDomBase[] rnds,
//			ref CstDomSet[] rndArrs,
// 			ref CstDomBase[] vars,
//			ref CstDomSet[] varArrs,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstVecNodeIntf[] idxs,
// 			ref CstDomBase[] bitIdxs,
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

  string describe() {
    return "( ~ " ~ _expr.describe ~ " )";
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

  CstNotVecExpr unroll(CstIterator iter, ulong n) {
    return new CstNotVecExpr(_expr.unroll(iter, n));
  }

  this(CstVecExpr expr) {
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _expr.isSolved();
  }

  void writeExprString(ref Charbuf str) {
    str ~= "(NOT ";
    _expr.writeExprString(str);
    str ~= ')';
  }
}

class CstNegVecExpr: CstVecTerm
{
  import std.conv;

  CstVecExpr _expr;

  string describe() {
    return "( - " ~ _expr.describe ~ " )";
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

  CstNegVecExpr unroll(CstIterator iter, ulong n) {
    return new CstNegVecExpr(_expr.unroll(iter, n));
  }

  this(CstVecExpr expr) {
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _expr.isSolved();
  }

  void writeExprString(ref Charbuf str) {
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

  string describe() {
    return "( " ~ _lhs.describe ~ " " ~ _op.to!string ~ " " ~ _rhs.describe ~ " )";
  }

  void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  override CstLogic2LogicExpr unroll(CstIterator iter, ulong n) {
    return new CstLogic2LogicExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  CstVecExpr isNot(CstDomBase dom){
    return null;
  }
  
  bool cstExprIsNop() {
    return false;
  }

  bool isSolved() {
    return _lhs.isSolved && _rhs.isSolved();
  }

  void writeExprString(ref Charbuf str) {
    str ~= '(';
    str ~= _op.to!string;
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ")\n";
  }

  DistRangeSetBase getDist() {
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
    }
  }
  
  override void scan() { }
  override bool isOrderingExpr() { return false; }
}

class CstInsideArrExpr: CstLogicTerm
{
  CstInsideSetElem[] _elems;

  CstVecExpr _term;

  bool _notinside = false;

  void setNotInside() { _notinside = true; }

  string describe() {
    string description = "( " ~ _term.describe() ~ " inside [";
    foreach (elem; _elems) {
      description ~= elem.describe();
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

  this(CstVecExpr term) {
    _term = term;
  }

  void addElem(CstInsideSetElem elem) {
    _elems ~= elem;
  }

  override CstInsideArrExpr unroll(CstIterator iter, ulong n) {
    CstInsideArrExpr unrolled = new CstInsideArrExpr(_term.unroll(iter, n));
    foreach (elem; _elems) {
      unrolled.addElem(elem.unroll(iter, n));
    }
    return unrolled;
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _term.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    foreach (elem; _elems) {
      elem.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    }
  }

  CstVecExpr isNot(CstDomBase dom){
    return null;
  }
  
  bool cstExprIsNop() {
    return false;
  }

  bool isSolved() {
    return false;
  }

  void writeExprString(ref Charbuf str) {
    str ~= "(INSIDE ";
    _term.writeExprString(str);
    str ~= " [";
    foreach (elem; _elems)
      elem.writeExprString(str);
    str ~= "])\n";
  }

  DistRangeSetBase getDist() {
    assert (false);
  }

  override bool eval() {assert (false, "Enable to evaluate CstInsideArrExpr");}

  override void scan() { }

  override bool isOrderingExpr() { return false; }
}

class CstUniqueArrExpr: CstLogicTerm
{
  CstUniqueSetElem[] _elems;

  string describe() {
    string description = "( unique [";
    foreach (elem; _elems) {
      description ~= elem.describe();
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

  override CstUniqueArrExpr unroll(CstIterator iter, ulong n) {
    CstUniqueArrExpr unrolled = new CstUniqueArrExpr();
    foreach (elem; _elems) {
      unrolled.addElem(elem.unroll(iter, n));
    }
    return unrolled;
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    pred.setUniqueFlag();
    foreach (elem; _elems) {
      elem.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    }
  }

  CstVecExpr isNot(CstDomBase dom){
    return null;
  }
  
  bool cstExprIsNop() {
    return false;
  }

  bool isSolved() {
    return false;
  }

  void writeExprString(ref Charbuf str) {
    str ~= "(UNIQUE ";
    str ~= " [";
    foreach (elem; _elems)
      elem.writeExprString(str);
    str ~= "])\n";
  }

  DistRangeSetBase getDist() {
    assert (false);
  }

  override bool eval() {assert (false, "Enable to evaluate CstUniqueArrExpr");}

  override void scan() { }
  override bool isOrderingExpr() { return false; }
}

// TBD
class CstIteLogicExpr: CstLogicTerm
{
  string describe() {
    return "CstIteLogicExpr";
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    assert(false, "TBD");
  }

  CstVecExpr isNot(CstDomBase dom){
    return null;
  }

  bool cstExprIsNop() {
    return false;
  }

  override CstLogicTerm unroll(CstIterator iter, ulong n) {
    assert(false, "TBD");
  }

  void visit(CstSolver solver) {
    assert(false, "TBD");
  }

  bool isSolved() {
    assert(false, "TBD");
  }

  DistRangeSetBase getDist() {
    assert (false);
  }

  void writeExprString(ref Charbuf str) {
    assert (false, "TBD");
  }

  override bool eval() {assert (false, "Enable to evaluate CstIteLogicExpr");}
  override void scan() { }
  override bool isOrderingExpr() { return false; }
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

  string describe() {
    return "( " ~ _lhs.describe ~ " " ~ _op.to!string ~ " " ~ _rhs.describe ~ " )";
  }

  void visit(CstSolver solver) {
    _lhs.visit(solver);
    _rhs.visit(solver);
    solver.processEvalStack(_op);
  }

  override CstVec2LogicExpr unroll(CstIterator iter, ulong n) {
    // import std.stdio;
    // writeln(_lhs.describe() ~ " " ~ _op.to!string ~ " " ~ _rhs.describe() ~ " Getting unwound!");
    // writeln("RHS: ", _rhs.unroll(iter, n).describe());
    // writeln("LHS: ", _lhs.unroll(iter, n).describe());
    return new CstVec2LogicExpr(_lhs.unroll(iter, n), _rhs.unroll(iter, n), _op);
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }
  
  CstVecExpr isNot(CstDomBase dom){
    if (_op is CstCompareOp.NEQ) {
      if (_lhs !is dom) {
	assert(false, "Constraint " ~ describe() ~ " not allowed since " ~ dom.name()
	       ~ " is dist");
      }
      return _rhs;
    }
    return null;
  }
    
  bool isSolved() {
    return _lhs.isSolved && _rhs.isSolved();
  }

  void writeExprString(ref Charbuf str) {
    str ~= '(';
    str ~= _op.to!string;
    str ~= ' ';
    _lhs.writeExprString(str);
    str ~= ' ';
    _rhs.writeExprString(str);
    str ~= ")\n";
  }

  DistRangeSetBase getDist() {
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

  override void scan() { }
  override bool isOrderingExpr() { return false; }
}

class CstLogicConst: CstLogicTerm
{
  immutable bool _bool;

  this(bool val) {
    _bool = val;
  }

  void visit(CstSolver solver) {
    solver.pushToEvalStack(_bool);
  }

  string describe() {
    if(_bool) return "TRUE";
    else return "FALSE";
  }

  override CstLogicConst unroll(CstIterator iter, ulong n) {
    return this;
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    // nothing for CstLogicConst
  }

  CstVecExpr isNot(CstDomBase dom){
    return null;
  }

  bool isSolved() {
    return true;
  }

  void writeExprString(ref Charbuf str) {
    if (_bool) str ~= "TRUE";
    else str ~= "FALSE";
  }

  DistRangeSetBase getDist() {
    assert (false);
  }

  override bool eval() {return _bool;}

  override void scan() { }
  override bool isOrderingExpr() { return false; }
}

class CstNotLogicExpr: CstLogicTerm
{
  CstLogicExpr _expr;

  this(CstLogicExpr expr) {
    _expr = expr;
  }

  string describe() {
    return "( " ~ "!" ~ " " ~ _expr.describe ~ " )";
  }

  void visit(CstSolver solver) {
    _expr.visit(solver);
    solver.processEvalStack(CstLogicOp.LOGICNOT);
  }

  override CstNotLogicExpr unroll(CstIterator iter, ulong n) {
    return new CstNotLogicExpr(_expr.unroll(iter, n));
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
  }

  CstVecExpr isNot(CstDomBase dom){
    return null;
  }

  bool isSolved() {
    return _expr.isSolved();
  }

  void writeExprString(ref Charbuf str) {
    str ~= "(NOT ";
    _expr.writeExprString(str);
    str ~= ")\n";
  }
  
  DistRangeSetBase getDist() {
    assert (false);
  }

  override bool eval() {return !_expr.eval();}

  override void scan() { }
  override bool isOrderingExpr() { return false; }
}

class CstVarVisitorExpr: CstLogicTerm
{
  CstVarNodeIntf _obj;

  this(CstVarNodeIntf obj) {
    assert (obj !is null);
    _obj = obj;
  }

  string describe() {
    return "Visitor: " ~ _obj.fullName();
  }

  void visit(CstSolver solver) {
    assert (false);
  }

  override CstVarVisitorExpr unroll(CstIterator iter, ulong n) {
    assert (_obj !is null);
    CstIterator iter_ = _obj._esdl__iter();
    if (iter_ is iter) {
      return new CstVarVisitorExpr(_obj._esdl__getChild(n));
    }
    else {
      return this;
    }
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstVecNodeIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstVecNodeIntf[] deps) {
    assert (_obj !is null);
    CstIterator iter = _obj._esdl__iter();
    if (iter !is null) {
      iter.setDomainContext(pred, rnds, rndArrs, vars, varArrs, vals, iters, idxs, bitIdxs, deps);
    }
  }

  bool isSolved() {
    return false;
  }

  void writeExprString(ref Charbuf str) {
    str ~= this.describe();
  }

  CstVecExpr isNot(CstDomBase dom){
    return null;
  }

  DistRangeSetBase getDist() {
    assert (false);
  }

  override void scan() {
    assert (_obj !is null);
    _obj.scan();
  }

  override bool eval() {assert(false);}

  override bool isOrderingExpr() { return false; }
}
