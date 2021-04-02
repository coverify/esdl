module esdl.solver.base;

// import esdl.rand.base;

import esdl.rand.misc;
import esdl.rand.pred: CstPredGroup;
import esdl.rand.base: CstDomBase, CstVecValueBase;

abstract class CstSolver
{
  string _signature;

  __gshared uint _count;

  immutable uint _id;

  this(string signature) {
    _signature = signature;
    synchronized {
      _id = _count++;
    }
    // import std.stdio;
    // writeln(this.describe());
  }

  string describe() {
    import std.conv: to;
    return "\nID: " ~ _id.to!string ~ "\nSignature: " ~ _signature;
  }

  // abstract void registerDomain(CstDomBase domain);
  // abstract void registerValue(CstVecValueBase value);

  abstract bool solve(CstPredGroup group);

  // abstract void pushToEvalStack();
  abstract void pushToEvalStack(CstDomBase domain);
  abstract void pushToEvalStack(CstVecValueBase value);

  abstract void pushToEvalStack(ulong value, uint bitcount, bool signed);
  abstract void pushToEvalStack(bool value);
  
  abstract void pushIndexToEvalStack(ulong value);

  abstract void processEvalStack(CstUnaryOp op);
  abstract void processEvalStack(CstBinaryOp op);
  abstract void processEvalStack(CstCompareOp op);
  abstract void processEvalStack(CstLogicOp op);
  abstract void processEvalStack(CstSliceOp op);
  abstract void processEvalStack(CstVectorOp op);
  abstract void processEvalStack(CstInsideOp op);
  abstract void processEvalStack(CstUniqueOp op);
}

abstract class DistRangeSetBase {
  abstract void purge(long item);
  abstract void uniform(CstDomBase dom, _esdl__RandGen randGen);
  abstract void reset();
}
