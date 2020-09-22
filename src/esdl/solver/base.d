module esdl.solver.base;
import esdl.rand.base;
import esdl.rand.expr;
import esdl.rand.misc;

abstract class CstSolver
{
  string _signature;

  this(string signature) {
    _signature = signature;
  }

  // abstract void registerDomain(CstDomain domain);
  // abstract void registerValue(CstValue value);

  abstract void solve(CstPredGroup group);

  abstract void pushToEvalStack(CstDomain domain);
  abstract void pushToEvalStack(CstValue value);

  abstract void pushToEvalStack(ulong value, uint bitcount, bool signed);
  abstract void pushToEvalStack(bool value);
  
  abstract void pushIndexToEvalStack(ulong value);

  abstract void processEvalStack(CstUnaryOp op);
  abstract void processEvalStack(CstBinaryOp op);
  abstract void processEvalStack(CstCompareOp op);
  abstract void processEvalStack(CstLogicOp op);
  abstract void processEvalStack(CstSliceOp op);
}
