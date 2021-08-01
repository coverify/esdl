module esdl.rand.expr;

import esdl.solver.base: CstSolver, CstDistSolverBase;

import esdl.rand.misc: rand, _esdl__RandGen, isVecSigned, Unconst,
  CstVectorOp, CstInsideOp;
import esdl.rand.misc: CstBinaryOp, CstCompareOp, CstLogicOp,
  CstUnaryOp, CstSliceOp, writeHexString, CstUniqueOp;

import esdl.rand.base: DomDistEnum, CstTerm, CstDomBase, CstDomSet,
  CstIterator, CstVecNodeIntf, CstVarNodeIntf, CstVecArrIntf,
  CstVecPrim, DomType,  CstValue, CstVecTerm, CstLogicTerm, CstDepIntf;
import esdl.rand.pred: CstPredicate, CstPredGroup, Hash;
import esdl.rand.func;

import esdl.data.bvec: isBitVector, toBitVec;
import esdl.data.charbuf;
import std.traits: isIntegral, isBoolean, isStaticArray,
  isSomeChar, EnumMembers, isSigned, OriginalType;
import std.algorithm: canFind;

abstract class CstLogicExpr: CstLogicTerm
{
  void setPredContext(CstPredicate pred) { }
  CstDomBase getDomain() { return null; }
}

abstract class CstVecExpr: CstVecTerm
{
  CstDomBase getDomain() { return null; }
}

// class CstOrderingExpr: CstLogicExpr
// {
//   CstDomBase _first;
//   CstDomBase _second;
//   bool _isSolved;
//   this (CstDomBase a, CstDomBase b) {
//     _first = a;
//     _second = b;
//   }
//   override bool isOrderingExpr() { return true; }
//   override CstDistSolverBase getDist() { assert(false); }
//   override bool isCompatWithDist(CstDomBase A) { assert(false); }
//   override void visit(CstDistSolverBase solver) { assert(false); }
  
//   override CstLogicTerm unroll(CstIterator iter, ulong n) { assert(false); }

//   void setDomainContext(CstPredicate pred,
// 			ref CstDomBase[] rnds,
// 			ref CstDomSet[] rndArrs,
// 			ref CstDomBase[] vars,
// 			ref CstDomSet[] varArrs,
// 			ref CstDomBase[] dists,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstDepIntf[] idxs,
// 			ref CstDomBase[] bitIdxs,
// 			ref CstDepIntf[] deps) {
//     rnds ~= _first;
//     rnds ~= _second;
//   }
//   bool isSolved() {
//     return _isSolved;
//   }
//   void visit(CstSolver solver) {
//     assert(false, "cannot visit an ordering expression");
//   }
//   void writeExprString(ref Charbuf str) {
//     assert(false);
//   }
//   string describe() {
//     string str = "( " ~ _first.describe() ~ " is solved before " ~ _second.describe() ~ " )";
//     return str;
//   }
//   void scan() { }
//   bool eval() {
//     assert (false);
//   }
// }

class CstVecArrExpr: CstVecExpr
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
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    pred._vectorOp = _op;
    _arr.setDomainArrContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(_op);
    hash.modify(32);
    _arr.calcHash(hash);
    hash.modify(41);
  }

  void scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

}

// This class would hold two(bin) vector nodes and produces a vector
// only after processing those two nodes
class CstVec2VecExpr: CstVecExpr
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;
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
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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
  
  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(_op);
    hash.modify(32);
    _lhs.calcHash(hash);
    hash.modify(32);
    _rhs.calcHash(hash);
    hash.modify(41);
  }
  
  void scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

}

class CstRangeExpr
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;

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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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
  
  void calcHash(ref Hash hash){
    _lhs.calcHash(hash);
    if (_rhs !is null) {
      if (_inclusive) hash.modify(58);
      else hash.modify(46);
      _rhs.calcHash(hash);
    }
  }

}

class CstVecDistSetElem
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;

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

  CstVecDistSetElem unroll(CstIterator iter, ulong n) {
    if (_rhs is null)
      return new CstVecDistSetElem(_lhs.unroll(iter, n), null, _inclusive);
    else
      return new CstVecDistSetElem(_lhs.unroll(iter, n),
				  _rhs.unroll(iter, n), _inclusive);
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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
  
  void calcHash(ref Hash hash){
    _lhs.calcHash(hash);
    if (_rhs !is null) {
      if (_inclusive) hash.modify(58);
      else hash.modify(46);
      _rhs.calcHash(hash);
    }
  }

}

class CstUniqueSetElem
{
  import std.conv;

  CstVecTerm _vec;
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    if (_arr !is null) {
      _arr.setDomainArrContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
      assert (rndArrs.length > 0 || varArrs.length > 0);
    }
    if (_vec !is null)
      _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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
  
}


class CstInsideSetElem
{
  import std.conv;

  CstVecTerm _lhs;
  CstVecTerm _rhs;

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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    if (_arr !is null) {
      _arr.setDomainArrContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
      // assert (rndArrs.length > 0 || varArrs.length > 0);
    }
    if (_lhs !is null)
      _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    if (_rhs !is null)
      _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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
    if (_arr !is null) return canFind!((CstDomBase a, CstVecTerm b)
				       => a.value() == b.evaluate())(_arr[], vec);
    else if (_rhs is null) return vec.evaluate() == _lhs.evaluate();
    else {
      return vec.evaluate() >= _lhs.evaluate()
	&& (_inclusive ? vec.evaluate() <= _rhs.evaluate() :
	    vec.evaluate() < _rhs.evaluate());
    }
  }
}

class CstLogicWeightedDistSetElem
{
  import std.conv;

  CstLogicTerm _term;
  CstVecTerm   _weight;
  bool         _perItem = false;

  string describe() {
    string str = "( " ~ _term.describe;
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.describe() ~ " )";
    return str;
  }

  CstLogicWeightedDistSetElem unroll(CstIterator iter, ulong n) {
    return new CstLogicWeightedDistSetElem(_term.unroll(iter, n), _weight.unroll(iter, n), _perItem);
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _term.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    _weight.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _term.isSolved() && _weight.isSolved();
  }

  void writeExprString(ref Charbuf str) {
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
    hash.modify(cast(uint)_weight.evaluate());
  }

}

class CstVecWeightedDistSetElem
{
  import std.conv;

  CstVecDistSetElem _range;
  CstVecTerm   _weight;
  bool         _perItem = false;

  string describe() {
    string str = "( " ~ _range.describe;
    if (_perItem) str ~= " := ";
    else str ~= " :/ ";
    str ~= _weight.describe() ~ " )";
    return str;
  }

  CstVecWeightedDistSetElem unroll(CstIterator iter, ulong n) {
    return new CstVecWeightedDistSetElem(_range.unroll(iter, n), _weight.unroll(iter, n), _perItem);
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _range.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    _weight.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
  }

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
  void calcHash(ref Hash hash){
    _range.calcHash(hash);
    if (_perItem) hash.modify(64);
    else hash.modify(42);
    hash.modify(cast(uint)_weight.evaluate());
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
      auto elem = dist._term;
      elem.visit(solver);
      solver.processEvalStack(CstInsideOp.EQUAL);
    }
    solver.processEvalStack(CstInsideOp.DONE);
  }
  
  override CstLogicDistExpr!T unroll(CstIterator iter, ulong n) {
    CstLogicWeightedDistSetElem[] dists;
    foreach (dist; _dists) {
      dists ~= dist.unroll(iter, n);
    }
    return new CstLogicDistExpr!T(cast (CstDomBase) (_vec.unroll(iter, n)), dists);
  }

  override void setPredContext(CstPredicate pred) {
    pred.distDomain(_vec);
    _vec.isDist(DomDistEnum.DETECT);
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    rnds ~= _vec;
    CstDomBase[] rnds_;
    CstDomBase[] dists_;
    CstDomSet[] rndArrs_;
    foreach (dist; _dists)
      dist.setDomainContext(pred, rnds_, rndArrs_, vars, varArrs, dists_, vals, iters, idxs, bitIdxs, deps);
    assert (rnds_.length == 0 && dists_.length == 0 && rndArrs_.length == 0);
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
  
  void calcHash(ref Hash hash){
    hash.modify(100);
    _vec.calcHash(hash);
    foreach (dist; _dists) {
      dist.calcHash(hash);
    }
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }

  void visit (CstDistSolverBase solver) { assert (false); }
  
  bool eval() {assert (false, "Enable to evaluate CstLogicDistExpr");}

  override void scan() { }
  override bool isOrderingExpr() { return false; }
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
  
  override CstVecDistExpr!T unroll(CstIterator iter, ulong n) {
    CstVecWeightedDistSetElem[] dists;
    foreach (dist; _dists) {
      dists ~= dist.unroll(iter, n);
    }
    return new CstVecDistExpr!T(cast (CstDomBase) (_vec.unroll(iter, n)), dists);
  }

  override void setPredContext(CstPredicate pred) {
    pred.distDomain(_vec);
    _vec.isDist(DomDistEnum.DETECT);
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    CstDomBase[] rnds_;
    CstDomBase[] dists_;
    CstDomSet[] rndArrs_;
    foreach (dist; _dists)
      dist.setDomainContext(pred, rnds_, rndArrs_, vars, varArrs, dists_, vals, iters, idxs, bitIdxs, deps);
    assert (rnds_.length == 0 && dists_.length == 0 && rndArrs_.length == 0);
    _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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
  
  void calcHash(ref Hash hash){
    hash.modify(100);
    _vec.calcHash(hash);
    foreach (dist; _dists) {
      dist.calcHash(hash);
    }
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }

  void visit (CstDistSolverBase solver) { assert (false); }
  
  bool eval() {assert (false, "Enable to evaluate CstVecDistExpr");}

  override void scan() { }
  override bool isOrderingExpr() { return false; }
}

// class CstVecSliceExpr: CstVecExpr
// {
//   CstVecTerm _vec;
//   CstVecTerm _lhs;
//   CstVecTerm _rhs;
  
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

//   void setDomainContext(CstPredicate pred,
// 			ref CstDomBase[] rnds,
//		        ref CstDomSet[] rndArrs,
// 			ref CstDomBase[] vars,
//			ref CstDomSet[] varArrs,
//			ref CstDomBase[] dists,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstDepIntf[] idxs,
// 			ref CstDomBase[] bitIdxs,
// 			ref CstDepIntf[] deps) {
//     _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
//     _lhs.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
//     if (_rhs !is null)
//       _rhs.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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

class CstVecSliceExpr: CstVecExpr
{
  CstVecTerm _vec;
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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    _range.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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

  void calcHash(ref Hash hash){
    _vec.calcHash(hash);
    hash.modify(91);
    _range.calcHash(hash);
    hash.modify(93);
  }

  void scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

}

// class CstVecIndexExpr: CstVecExpr
// {
//   CstVecTerm _vec;
//   CstVecTerm _index;
  
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

//   void setDomainContext(CstPredicate pred,
// 			ref CstDomBase[] rnds,
//			ref CstDomSet[] rndArrs,
// 			ref CstDomBase[] vars,
//			ref CstDomSet[] varArrs,
//			ref CstDomBase[] dists,
// 			ref CstValue[] vals,
// 			ref CstIterator[] iters,
// 			ref CstDepIntf[] idxs,
// 			ref CstDomBase[] bitIdxs,
// 			ref CstDepIntf[] deps) {
//     _vec.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
//     _index.setDomainContext(pred, bitIdxs, rndArrs, bitIdxs, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
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

class CstNotVecExpr: CstVecExpr
{
  import std.conv;

  CstVecTerm _expr;

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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _expr.isSolved();
  }

  void writeExprString(ref Charbuf str) {
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

  void scan() { }

  final void visit(CstDistSolverBase dist) { assert(false); }

}

class CstNegVecExpr: CstVecExpr
{
  import std.conv;

  CstVecTerm _expr;

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

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
  }

  bool isSolved() {
    return _expr.isSolved();
  }

  void writeExprString(ref Charbuf str) {
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

  void scan() { }

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
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }

  
  bool isSolved() { return _lhs.isSolved && _rhs.isSolved(); }

  void writeExprString(ref Charbuf str) {
    str ~= '(';
    str ~= _op.to!string;
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
  
  override void scan() { }
  override bool isOrderingExpr() { return false; }
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

  override CstInsideArrExpr unroll(CstIterator iter, ulong n) {
    CstInsideArrExpr unrolled = new CstInsideArrExpr(_term.unroll(iter, n));
    foreach (elem; _elems) {
      unrolled.addElem(elem.unroll(iter, n));
    }
    unrolled._notinside = _notinside;
    return unrolled;
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    if (_notinside) {
      // special processing for dist domains
      CstDomBase tdom = _term.getDomain();
      if (tdom !is null && tdom.isDist()) {
	rnds ~= tdom;
	CstDomBase[] rnds_;
	foreach (elem; _elems) {
	  elem.setDomainContext(pred, rnds_, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
	}
	if (rnds_.length > 0) {
	  foreach (rnd; rnds_) {
	    // tdom.addDep(rnd);	// random has to be solved first
	    if (! deps.canFind(rnd)) deps ~= rnd;
	    if (! vars.canFind(rnd)) vars ~= rnd;
	  }
	}
	return;
      }
    }
    _term.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    foreach (elem; _elems) {
      elem.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    }
  }

  bool isCompatWithDist(CstDomBase dom) {
    CstTerm term = cast(CstTerm) _term;
    if (_notinside && term == dom) return true;
    else return false;
  }
  
  bool isSolved() { return false; }

  void writeExprString(ref Charbuf str) {
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
  
  CstDistSolverBase getDist() {
    assert (false);
  }

  override bool eval() {
    bool inside = canFind!((CstInsideSetElem a, CstVecTerm b) =>
			   a.eval(b))(_elems, _term);
    if (_notinside) return ! inside;
    else return inside;
  }

  override void scan() { }

  override bool isOrderingExpr() { return false; }

}

class CstUniqueArrExpr: CstLogicExpr
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
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    pred.setUniqueFlag();
    foreach (elem; _elems) {
      elem.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    }
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }
  
  bool isSolved() { return false; }

  void writeExprString(ref Charbuf str) {
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

  CstDistSolverBase getDist() { assert (false); }

  override bool eval() {assert (false, "Enable to evaluate CstUniqueArrExpr");}

  override void scan() { }
  override bool isOrderingExpr() { return false; }

}

// TBD
class CstIteLogicExpr: CstLogicExpr
{
  string describe() {
    return "CstIteLogicExpr";
  }

  void setDomainContext(CstPredicate pred,
			ref CstDomBase[] rnds,
			ref CstDomSet[] rndArrs,
			ref CstDomBase[] vars,
			ref CstDomSet[] varArrs,
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    assert(false, "TBD");
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }
  

  override CstLogicTerm unroll(CstIterator iter, ulong n) {
    assert(false, "TBD");
  }

  void visit(CstSolver solver) { assert(false, "TBD"); }

  bool isSolved() { assert(false, "TBD"); }

  CstDistSolverBase getDist() { assert (false); }

  void writeExprString(ref Charbuf str) {
    assert (false, "TBD");
  }

  void calcHash(ref Hash hash){
    assert (false, "TBD");
  }

  override bool eval() {assert (false, "Enable to evaluate CstIteLogicExpr");}
  override void scan() { }
  override bool isOrderingExpr() { return false; }

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
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    if (_op == CstCompareOp.NEQ) {
      // special processing for dist domains
      CstDomBase ldom = _lhs.getDomain();
      if (ldom !is null && ldom.isDist()) {
	// find if RHS is also a dist domain
	CstDomBase rdom = _rhs.getDomain();
	if (rdom !is null && rdom.isDist()) {
	  // ldom.addDep(rdom);	// RHS needs to be solved first
	  if (! deps.canFind(rdom)) deps ~= rdom;
	  if (! vars.canFind(rdom)) vars ~= rdom;
	  if (! rnds.canFind(ldom)) rnds ~= ldom;
	  return;
	}
	else {
	  CstDomBase[] rnds_;
	  _rhs.setDomainContext(pred, rnds_, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
	  if (rnds_.length > 0) {
	    foreach (rnd; rnds_) {
	      // rnd.addDep(ldom);	// random variables will be solved only after this dist is resolved
	      if (! rnds.canFind(rnd)) rnds ~= rnd;
	    }
	    if (! deps.canFind(ldom)) deps ~= ldom;
	    if (! vars.canFind(ldom)) vars ~= ldom;
	    return;
	  }
	  else {
	    if (! rnds.canFind(ldom)) rnds ~= ldom;
	    return;
	  }
	}
      }
    }
    if (_op == CstCompareOp.NEQ) {
      assert (_rhs !is null);
      CstDomBase rdom = _rhs.getDomain();
      if (rdom !is null && rdom.isDist()) {
	CstDomBase[] rnds_;
	_lhs.setDomainContext(pred, rnds_, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
	if (rnds_.length > 0) {
	  foreach (rnd; rnds_) {
	    // rnd.addDep(rdom);	// random variables will be solved only after this dist is resolved
	    rnds ~= rnd;
	  }
	  if (! deps.canFind(rdom)) deps ~= rdom;
	  if (! vars.canFind(rdom)) vars ~= rdom;
	  return;
	}
	else {
	  assert (false);
	  // rnds ~= rdom;
	  // return;
	}
      }
    }
    _lhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
    _rhs.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
  }
  
  bool isCompatWithDist(CstDomBase dom) {
    if (_op is CstCompareOp.NEQ) {
      CstTerm lhs = _lhs;
      CstTerm dom_ = dom;
      if (lhs != dom_) {
	assert(false, "Constraint " ~ describe() ~ " not allowed since " ~ dom.name()
	       ~ " is dist");
      }
      return true;
    }
    return false;
  }

  void visit (CstDistSolverBase solver) {
    CstTerm lhs = _lhs;
    CstTerm dom = solver.getDomain();
    assert (lhs == dom);
    solver.purge(_rhs.evaluate());
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

  void calcHash(ref Hash hash){
    hash.modify(40);
    hash.modify(_op);
    hash.modify(32);
    _lhs.calcHash(hash);
    hash.modify(32);
    _rhs.calcHash(hash);
    hash.modify(41);
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

  override void scan() { }
  override bool isOrderingExpr() { return false; }

}

class CstNotLogicExpr: CstLogicExpr
{
  CstLogicTerm _expr;

  this(CstLogicTerm expr) {
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
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    _expr.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }

  bool isSolved() {
    return _expr.isSolved();
  }

  void writeExprString(ref Charbuf str) {
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
  
  CstDistSolverBase getDist() {
    assert (false);
  }

  override bool eval() {return !_expr.eval();}

  override void scan() { }
  override bool isOrderingExpr() { return false; }

}

class CstVarVisitorExpr: CstLogicExpr
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
    solver.pushToEvalStack(true);
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
			ref CstDomBase[] dists,
			ref CstValue[] vals,
			ref CstIterator[] iters,
			ref CstDepIntf[] idxs,
			ref CstDomBase[] bitIdxs,
			ref CstDepIntf[] deps) {
    assert (_obj !is null);
    CstIterator iter = _obj._esdl__iter();
    if (iter !is null) {
      iter.setDomainContext(pred, rnds, rndArrs, vars, varArrs, dists, vals, iters, idxs, bitIdxs, deps);
      rnds ~= iter.getLenVec();
    }
  }

  bool isSolved() {
    return false;
  }

  void writeExprString(ref Charbuf str) {
    str ~= this.describe();
  }

  
  void calcHash(ref Hash hash){
    hash.modify(118);
    hash.modify(_obj.fullName());
  }

  bool isCompatWithDist(CstDomBase dom) { return false; }
  void visit (CstDistSolverBase solver) { assert (false); }

  CstDistSolverBase getDist() {
    assert (false);
  }

  override void scan() {
    assert (_obj !is null);
    _obj.scan();
  }

  override bool eval() {assert(false);}

  override bool isOrderingExpr() { return false; }

}
