module esdl.rand.func;

import std.traits: isIntegral, isBoolean, isStaticArray,
  isSomeChar, EnumMembers, isSigned, OriginalType;
import esdl.data.bvec: isBitVector;
import esdl.rand.misc;
import esdl.rand.base: CstVecExpr, CstDomSet;
import esdl.rand.expr: CstLogicTerm, CstVec2LogicExpr, CstRangeExpr, CstDistSetElem,
  CstInsideSetElem, CstUniqueSetElem, CstUniqueArrExpr, CstWeightedDistSetElem,
  CstInsideArrExpr, CstVecDomain, CstDistExpr;



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

auto _esdl__index_range(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__index_range_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__index_range_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    static assert (false);
  }
}

CstRangeExpr _esdl__index_range_impl(Q)(CstVecExpr p, Q q)
  if (isBitVector!Q || isIntegral!Q) {
    if (q is null) return _esdl__index_range_impl(p, q);
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__index_range_impl(p, qq);
  }

CstRangeExpr _esdl__index_range_impl(CstVecExpr p, CstVecExpr q) {
  return new CstRangeExpr(p, q);
}

auto _esdl__index_rangeinc(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__index_rangeinc_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__index_rangeinc_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicConst(p == q);
  }
}

CstRangeExpr _esdl__index_rangeinc_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__index_rangeinc_impl(p, qq);
  }

CstRangeExpr _esdl__index_rangeinc_impl(CstVecExpr p, CstVecExpr q) {
  return new CstRangeExpr(p, q, true);
}

auto _esdl__dist_range(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__dist_range_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__dist_range_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    static assert (false);
  }
}

CstDistSetElem _esdl__dist_range_impl(Q)(CstVecExpr p, Q q)
  if (isBitVector!Q || isIntegral!Q) {
    if (q is null) return _esdl__dist_range_impl(p, q);
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__dist_range_impl(p, qq);
  }

CstDistSetElem _esdl__dist_range_impl(CstVecExpr p, CstVecExpr q) {
  return new CstDistSetElem(p, q);
}

auto _esdl__dist_rangeinc(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__dist_rangeinc_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__dist_rangeinc_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicConst(p == q);
  }
}

CstDistSetElem _esdl__dist_rangeinc_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__dist_rangeinc_impl(p, qq);
  }

CstDistSetElem _esdl__dist_rangeinc_impl(CstVecExpr p, CstVecExpr q) {
  return new CstDistSetElem(p, q, true);
}

auto _esdl__inside_range(P, Q)(P p, Q q) {
  static if(is(P: CstDomSet)) {
    return _esdl__inside_range_impl(p, q);
  }
  else static if(is(P: CstVecExpr)) {
    return _esdl__inside_range_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
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


CstInsideSetElem _esdl__inside_range_impl(Q)(CstVecExpr p, Q q)
  if (isBitVector!Q || isIntegral!Q) {
    if (q is null) return _esdl__inside_range_impl(p, q);
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__inside_range_impl(p, qq);
  }

CstInsideSetElem _esdl__inside_range_impl(CstVecExpr p, CstVecExpr q) {
  return new CstInsideSetElem(p, q);
}

auto _esdl__inside_rangeinc(P, Q)(P p, Q q) {
  static if(is(P: CstVecExpr)) {
    return _esdl__inside_rangeinc_impl(p, q);
  }
  else static if(is(Q: CstVecExpr)) {
    return _esdl__inside_rangeinc_impl(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstLogicConst(p == q);
  }
}

CstInsideSetElem _esdl__inside_rangeinc_impl(Q)(CstVecExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVecValue!Q(q); // CstVecValue!Q.allocate(q);
    return _esdl__inside_rangeinc_impl(p, qq);
  }

CstInsideSetElem _esdl__inside_rangeinc_impl(CstVecExpr p, CstVecExpr q) {
  return new CstInsideSetElem(p, q, true);
}

auto _esdl__unique_elem(P)(P p) {
  return new CstUniqueSetElem(p);
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

CstInsideArrExpr _esdl__inside(CstVecExpr vec, CstInsideSetElem[] ranges) {
  CstInsideArrExpr expr = new CstInsideArrExpr(vec);
  foreach (r; ranges) {
    expr.addElem(r);
  }
  return expr;
}

CstInsideArrExpr _esdl__notinside(CstVecExpr vec, CstInsideSetElem[] ranges) {
  CstInsideArrExpr expr = _esdl__inside(vec, ranges);
  expr.setNotInside();
  return expr;
}

CstUniqueArrExpr _esdl__unique(CstUniqueSetElem[] ranges) {
  CstUniqueArrExpr expr = new CstUniqueArrExpr();
  foreach (r; ranges) {
    expr.addElem(r);
  }
  return expr;
}

CstWeightedDistSetElem _esdl__rangeWeight(CstDistSetElem range, CstVecExpr weight) {
  return new CstWeightedDistSetElem(range, weight, false);
}

CstWeightedDistSetElem _esdl__itemWeight(CstDistSetElem range, CstVecExpr weight) {
  return new CstWeightedDistSetElem(range, weight, true);
}

auto _esdl__dist(T, rand RAND)(CstVecDomain!(T, RAND) vec,
			       CstWeightedDistSetElem[] ranges) {
  return new CstDistExpr!T(vec, ranges);
}
