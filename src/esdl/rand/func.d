module esdl.rand.func;

import std.traits: isIntegral, isBoolean, isStaticArray,
  isSomeChar, EnumMembers, isSigned, OriginalType;
import esdl.data.bvec: isBitVector;
import esdl.rand.misc;
import esdl.rand.base: CstLogicTerm, CstVecTerm, CstDomSet, CstDomBase;
import esdl.rand.expr: CstVec2LogicExpr, CstRangeExpr, CstVecDistSetElem,
  CstInsideSetElem, CstUniqueSetElem, CstUniqueArrExpr,
  CstVecWeightedDistSetElem, CstLogicWeightedDistSetElem,
  CstInsideArrExpr, CstVecDistExpr, CstLogicDistExpr, CstLogic2LogicExpr;
import esdl.rand.domain: CstDomain;
// import esdl.base.alloc: make;



auto _esdl__cstVal(T)(T val) {
  return new CstVecValue!T(val); // CstVecValue!(T).allocate(val);
}

auto _esdl__logicOr(P, Q)(P p, Q q) {
  CstLogicTerm _p;
  CstLogicTerm _q;
  static if (is (P == bool)) {
    _p = new CstLogicValue(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstLogicValue(q);
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
    _p = new CstLogicValue(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstLogicValue(q);
  }
  else {
    _q = q;
  }
  return _p.logicAnd(_q);
}


auto _esdl__lth(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__lth_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__gte_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p < q);
  }
}

CstVec2LogicExpr _esdl__lth_impl(Q)(CstVecTerm left, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__lth_impl(left, qq);
  }

CstVec2LogicExpr _esdl__lth_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.LTH);
}

auto _esdl__lte(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__lte_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__gth_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p <= q);
  }
}

CstVec2LogicExpr _esdl__lte_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__lte_impl(p, qq);
  }

CstVec2LogicExpr _esdl__lte_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.LTE);
}

auto _esdl__gth(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__gth_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__lte_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p > q);
  }
}

CstVec2LogicExpr _esdl__gth_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__gth_impl(p, qq);
  }

CstVec2LogicExpr _esdl__gth_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.GTH);
}

auto _esdl__gte(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__gte_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__lth_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p >= q);
  }
}

CstVec2LogicExpr _esdl__gte_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__gte_impl(p, qq);
  }

CstVec2LogicExpr _esdl__gte_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.GTE);
}

auto _esdl__equ(P, Q)(P p, Q q) {
  static if(is (P: CstLogicTerm)) {
    return _esdl__equ_logic_impl(p, q);
  }
  else static if(is(P: CstVecTerm)) {
    return _esdl__equ_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__equ_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p == q);
  }
}

CstLogic2LogicExpr _esdl__equ_logic_impl(P, Q)(P p, Q q)
  if (is (P: CstLogicTerm) && is (Q: CstLogicTerm)) {
    return new CstLogic2LogicExpr(p, q, CstLogicOp.LOGICEQ);
  }

CstVec2LogicExpr _esdl__equ_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__equ_impl(p, qq);
  }

CstVec2LogicExpr _esdl__equ_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.EQU);
}

auto _esdl__index_range(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__index_range_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__index_range_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    static assert (false);
  }
}

CstRangeExpr _esdl__index_range_impl(Q)(CstVecTerm p, Q q)
  if (isBitVector!Q || isIntegral!Q) {
    if (q is null) return _esdl__index_range_impl(p, q);
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__index_range_impl(p, qq);
  }

CstRangeExpr _esdl__index_range_impl(CstVecTerm p, CstVecTerm q) {
  return new CstRangeExpr(p, q);
}

auto _esdl__index_rangeinc(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__index_rangeinc_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__index_rangeinc_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p == q);
  }
}

CstRangeExpr _esdl__index_rangeinc_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__index_rangeinc_impl(p, qq);
  }

CstRangeExpr _esdl__index_rangeinc_impl(CstVecTerm p, CstVecTerm q) {
  return new CstRangeExpr(p, q, true);
}

auto _esdl__dist_range(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__dist_range_impl(p, q);
  }
  else static if(is(P: CstLogicTerm)) {
    assert (q is null);
    return p;
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__dist_range_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    static assert (false);
  }
}


CstVecDistSetElem _esdl__dist_range_impl(Q)(CstVecTerm p, Q q)
  if (isBitVector!Q || isIntegral!Q) {
    if (q is null) return _esdl__dist_range_impl(p, q);
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__dist_range_impl(p, qq);
  }

CstVecDistSetElem _esdl__dist_range_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVecDistSetElem(p, q);
}

auto _esdl__dist_rangeinc(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__dist_rangeinc_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__dist_rangeinc_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p == q);
  }
}

CstVecDistSetElem _esdl__dist_rangeinc_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__dist_rangeinc_impl(p, qq);
  }

CstVecDistSetElem _esdl__dist_rangeinc_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVecDistSetElem(p, q, true);
}

auto _esdl__inside_range(P, Q)(P p, Q q) {
  static if(is(P: CstDomSet)) {
    return _esdl__inside_range_impl(p, q);
  }
  else static if(is(P: CstVecTerm)) {
    return _esdl__inside_range_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__inside_range_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    static assert (false);
  }
}

CstInsideSetElem _esdl__inside_range_impl(Q)(CstDomSet p, Q q) {
  assert (q is null);
  return new CstInsideSetElem(p);
}


CstInsideSetElem _esdl__inside_range_impl(Q)(CstVecTerm p, Q q)
  if (isBitVector!Q || isIntegral!Q) {
    if (q is null) return _esdl__inside_range_impl(p, q);
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__inside_range_impl(p, qq);
  }

CstInsideSetElem _esdl__inside_range_impl(CstVecTerm p, CstVecTerm q) {
  return new CstInsideSetElem(p, q);
}

auto _esdl__inside_rangeinc(P, Q)(P p, Q q) {
  static if(is(P: CstVecTerm)) {
    return _esdl__inside_rangeinc_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__inside_rangeinc_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p == q);
  }
}

CstInsideSetElem _esdl__inside_rangeinc_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__inside_rangeinc_impl(p, qq);
  }

CstInsideSetElem _esdl__inside_rangeinc_impl(CstVecTerm p, CstVecTerm q) {
  return new CstInsideSetElem(p, q, true);
}

auto _esdl__unique_elem(P)(P p) {
  return new CstUniqueSetElem(p);
}

auto _esdl__neq(P, Q)(P p, Q q) {
  static if(is (P: CstLogicTerm)) {
    return _esdl__neq_logic_impl(p, q);
  }
  else static if(is(P: CstVecTerm)) {
    return _esdl__neq_impl(p, q);
  }
  else static if(is(Q: CstVecTerm)) {
    return _esdl__neq_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicValue(p != q);
  }
}

CstLogic2LogicExpr _esdl__neq_logic_impl(P, Q)(P p, Q q)
  if (is (P: CstLogicTerm) && is (Q: CstLogicTerm)) {
    return new CstLogic2LogicExpr(p, q, CstLogicOp.LOGICNEQ);
  }

CstVec2LogicExpr _esdl__neq_impl(Q)(CstVecTerm p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__neq(p, qq);
  }

CstVec2LogicExpr _esdl__neq_impl(CstVecTerm p, CstVecTerm q) {
  return new CstVec2LogicExpr(p, q, CstCompareOp.NEQ);
}

CstInsideArrExpr _esdl__inside(CstVecTerm vec, CstInsideSetElem[] ranges) {
  CstInsideArrExpr expr = new CstInsideArrExpr(vec);
  foreach (r; ranges) {
    expr.addElem(r);
  }
  return expr;
}

CstInsideArrExpr _esdl__notinside(CstVecTerm vec, CstInsideSetElem[] ranges) {
  CstInsideArrExpr expr = _esdl__inside(vec, ranges);
  expr.negate();
  return expr;
}

CstUniqueArrExpr _esdl__unique(CstUniqueSetElem[] ranges) {
  CstUniqueArrExpr expr = new CstUniqueArrExpr();
  foreach (r; ranges) {
    expr.addElem(r);
  }
  return expr;
}

CstVecWeightedDistSetElem _esdl__rangeWeight(CstVecDistSetElem range, CstVecTerm weight) {
  return new CstVecWeightedDistSetElem(range, weight, false);
}

CstVecWeightedDistSetElem _esdl__itemWeight(CstVecDistSetElem range, CstVecTerm weight) {
  return new CstVecWeightedDistSetElem(range, weight, true);
}

CstLogicWeightedDistSetElem _esdl__itemWeight(CstLogicTerm term, CstVecTerm weight) {
  return new CstLogicWeightedDistSetElem(term, weight, true);
}

auto _esdl__dist(T, rand RAND)(CstDomain!(T, RAND) vec,
			       CstLogicWeightedDistSetElem[] ranges) if (isBoolean!T) {
  return new CstLogicDistExpr!T(vec, ranges);
}

auto _esdl__dist(T, rand RAND)(CstDomain!(T, RAND) vec,
			       CstVecWeightedDistSetElem[] ranges) if (! isBoolean!T) {
  return new CstVecDistExpr!T(vec, ranges);
}

void _esdl__order(CstDomBase a, CstDomBase b){
  a.orderBefore(b);
}
void _esdl__order(CstDomBase a, CstDomSet b){
  a.orderBefore(b);
}
void _esdl__order(CstDomSet a, CstDomBase b){
  a.orderBefore(b);
}
void _esdl__order(CstDomSet a, CstDomSet b){
  a.orderBefore(b);
}

CstLogicTerm _esdl__bool(CstVecTerm term) {
  return term.toBoolExpr();
}

auto _esdl__evaluate(T, U)(T lvec, U rvec, CstBinaryOp op) {
  final switch(op) {
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

auto _esdl__evaluate(T, U)(T lvec, U rvec, CstCompareOp op) {
  final switch(op) {
  case CstCompareOp.LTH: return lvec <  rvec;
  case CstCompareOp.LTE: return lvec <= rvec;
  case CstCompareOp.GTH: return lvec >  rvec;
  case CstCompareOp.GTE: return lvec >= rvec;
  case CstCompareOp.EQU: return lvec == rvec;
  case CstCompareOp.NEQ: return lvec != rvec;
  }
}

