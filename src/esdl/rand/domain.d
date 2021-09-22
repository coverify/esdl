module esdl.rand.domain;

import std.traits: isIntegral, isBoolean, isSigned, Unconst,
  OriginalType, EnumMembers, isSomeChar, isStaticArray;
import std.algorithm: canFind;

import esdl.data.bvec: isBitVector;
import esdl.data.charbuf: Charbuf;

import esdl.rand.base: CstValue, CstDomBase, CstDomSet, CstIterator,
  CstVecNodeIntf, CstVarNodeIntf, CstVecPrim, DomType, CstLogicTerm,
  CstVecTerm, CstVecValueBase, CstDepIntf;
import esdl.rand.misc: rand, writeHexString, isVecSigned,
  CstVectorOp, CstInsideOp, CstCompareOp, CstLogicOp, DomainContextEnum;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.pred: CstPredicate, Hash;
import esdl.rand.expr: CstNotLogicExpr, CstLogic2LogicExpr;

import esdl.solver.base: CstSolver, CstDistSolverBase;

import esdl.base.rand: _esdl__RandGen;


abstract class CstDomain(T, rand RAND_ATTR) if (is (T == bool)):
  CstVecDomain!(T, RAND_ATTR), CstLogicTerm
    {
      this(string name, _esdl__Proxy root) {
	super(name, root);
      }


      CstDistSolverBase getDist() { assert (false); }

      bool isCompatWithDist(CstDomBase A) { return false; }
      void visit(CstDistSolverBase solver) { assert (false); }

      override bool getBool() {	return eval(); }

      override void setBool(bool val) {
	static if (HAS_RAND_ATTRIB) {
	  assert (getRef() !is null,
		  "Domain does not have a valid R-Value pointer: " ~ fullName());
	  if (val != *(getRef())) {
	    _valueChanged = true;
	  }
	  else {
	    _valueChanged = false;
	  }
	  *(getRef()) = val;
	  markSolved();
	  execCbs();
	}
	else {
	  assert(false);
	}
      }

      override bool isBool() {return true;}
      
      bool eval() {
	return cast(bool) *(getRef());
      }

      override void scan() { }

      override uint bitcount() { return 1; }
      
      override bool signed() { return false; }
      override void setDistPredContext(CstPredicate pred) { }

      override CstDomBase getDomain() { return this; }
    }

abstract class CstDomain(T, rand RAND_ATTR) if (!is (T == bool)):
  CstVecDomain!(T, RAND_ATTR), CstVecTerm
    {
      this(string name, _esdl__Proxy root) {
	super(name, root);
      }

      final override bool isBool() {return false;}

      final override bool getBool() {assert (false);}

      final override void setBool(bool val) {assert (false);}

      long evaluate() {
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

      override uint bitcount() {
	static if (isBoolean!T)         return 1;
	else static if (isIntegral!T || isSomeChar!T)   return T.sizeof * 8;
	else static if (isBitVector!T)  return T.SIZE;
	else static if (is (T == enum)) {
	  alias OT = OriginalType!T;
	  static if (isBoolean!OT)         return 1;
	  else static if (isIntegral!OT || isSomeChar!OT)   return OT.sizeof * 8;
	  else static if (isBitVector!OT)  return OT.SIZE;
	  else static assert(false, "bitcount can not operate on: " ~ T.stringof);
	}
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

      override CstDomBase getDomain() { return this; }
    }

abstract class CstVecDomain(T, rand RAND_ATTR): CstDomBase
{
  enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();

  Unconst!T _shadowValue;

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

  void writeExprString(ref Charbuf str) {
    if (this.isSolved()) {
      // import std.stdio;
      // writeln(fullName(), " has a value of: ", value());
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

  void calcHash(ref Hash hash){
    if (this.isSolved()) {
      hash.modify(86);
      hash.modify(_domN);
      hash.modify(35);
      hash.modify(_varN);
    }
    else {
      hash.modify(82);
      hash.modify(_domN);
      hash.modify(T.stringof);
    }
  }

  this(string name, _esdl__Proxy root) {
    _name = name;
    _root = root;
  }

  
  abstract T* getRef();

  override long value() {
    return cast(long) *(getRef());
  }

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
      debug (CSTSOLVER) {
	import std.stdio;
	writeln("Setting value of ", fullName(), " to: ", newVal);
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
      static if (isIntegral!T || isBoolean!T) {
	newVal = cast(T) val;
      }
      else {
	newVal._setNthWord(val, 0);
      }
      assert (getRef() !is null,
	      "Domain does not have a valid R-Value pointer: " ~ fullName());
      if (newVal != *(getRef())) {
	_valueChanged = true;
      }
      else {
	_valueChanged = false;
      }
      debug (CSTSOLVER) {
	import std.stdio;
	writeln("Setting value of ", fullName(), " to: ", newVal);
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
	assert (randGen !is null);
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


  // override void registerVarPred(CstPredicate varPred) {
  //   foreach (pred; _varPreds) {
  //     if (pred is varPred) {
  // 	return;
  //     }
  //   }
  //   _varPreds ~= varPred;
  // }
  
  final override string describe(bool descExpr=false) {
    import std.conv: to;
    if (descExpr is true) {
      return name();
    }
    else {
      string desc = "CstDomBase: " ~ name();
      // desc ~= "\n	DomType: " ~ _type.to!string();
      // if (_type !is DomType.MULTI) {
      //   desc ~= "\nIntRS: " ~ _rs.toString();
      // }
      if (_unresolvedDomainPreds.length > 0) {
	desc ~= "\n	Unresolved Domain Preds:";
	foreach (pred; _unresolvedDomainPreds) {
	  desc ~= "\n		" ~ pred.name();
	}
	desc ~= "\n";
      }
      if (_resolvedDomainPreds.length > 0) {
	desc ~= "\n	Resolved Domain Preds:";
	foreach (pred; _resolvedDomainPreds) {
	  desc ~= "\n		" ~ pred.name();
	}
	desc ~= "\n";
      }
      return desc;
    }
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

  final override CstDomBase getLenVec() {
    return _arrVar.arrLen();
  }
  
  final override ulong mapIter(size_t i) {
    return _arrVar.mapIter(i);
  }

  override ulong size() {
    if(! getLenVec().isSolved()) {
      assert(false, "Can not find size since the " ~
	     "Iter Variable has not been unrolled");
    }
    // import std.stdio;
    // writeln("size for arrVar: ", _arrVar.name(), " is ",
    // 	    _arrVar.arrLen.value);
    return _arrVar.arrLen.value;
  }

  override string name() {
    string n = _arrVar.name();
    return n ~ "->iterator";
  }

  override string fullName() {
    string n = _arrVar.fullName();
    return n ~ "->iterator";
  }

  string describe(bool descExpr=false) {
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

  CstVecTerm unroll(CstIterator iter, ulong n) {
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

  void visit(CstSolver solver) {
    assert (false, "Can not visit an Iter Variable without unrolling");
  }

  // override bool getVal(ref long val) {
  //   return false;
  // }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    auto len = getLenVec();
    pred.addDep(len, context);
    pred.addVarIter(this, context);
  }

  bool signed() {
    return false;
  }

  uint bitcount() {
    return 64;
  }
  
  bool isSolved() {
    return _arrVar._arrLen.isSolved();
  }


  void writeExprString(ref Charbuf str) {
    // assert(false);
  }
  void calcHash(ref Hash hash) { }
}

class CstArrLength(RV): CstVecDomain!(uint, RV.RAND), CstVecTerm, CstVecPrim
{

  alias AV = typeof(this);
  
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

  override void forceResolve(_esdl__Proxy proxy) {
    import std.algorithm.iteration: filter;
    if (isRand() && isSolved()) {
      _parent.buildElements(_parent.getLen());
      execCbs();
    }
    else {
      markSolved();
      _parent.buildElements(_parent.getLen());
      execCbs();
    }
  }

  override bool tryResolve(_esdl__Proxy proxy) {
    import std.algorithm.iteration: filter;
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("tryResolve: ", fullName());
    }
    // if (isRand() && isSolved()) {
    //   forceResolve(proxy);
    // }
    if (! this.depsAreResolved()) return false;
    if (isMarkedSolved()) {
      debug (CSTSOLVER) {
	import std.stdio;
	writeln("tryResolve: Already marked solved: ", fullName());
      }
      execCbs();
      return false;
    }
    else {
      // foreach (pred; _unresolvedDomainPreds) {
      // 	import std.stdio;
      // 	writeln (pred.name());
      // }
      if ((! this.isRand()) ||
	  _unresolvedDomainPreds.length == 0 ||
	  _unresolvedDomainPreds[].filter!(pred => ! (pred.isGuard() || pred.isVisitor())).empty()) {
	debug (CSTSOLVER) {
	  import std.stdio;
	  writeln("tryResolve: Resoling: ", fullName());
	}
	randomizeWithoutConstraints(proxy);
	return true;
      }
    }
    return false;

    // import std.algorithm.iteration: filter;
    // if (isRand() && isSolved()) {
    //   execCbs();
    //   return true;
    // }
    // if (! isRand()) {
    //   markSolved();
    //   _parent.buildElements(_parent.getLen());
    //   execCbs();
    //   return true;
    // }
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

  override bool inRange() {
    return _parent.inRange();
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
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Setting value of ", fullName(), " to: ", value);
    }
    _parent.setLen(cast(size_t) value);
    markSolved();
    execCbs();
  }

  override void setVal(ulong[] v) {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Setting value of ", fullName(), " to: ", v[0]);
    }
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

  CstVecTerm unroll(CstIterator iter, ulong n) {
    return _parent.unroll(iter,n).arrLen();
  }

  override AV getResolvedNode() {
    if (_parent.depsAreResolved()) return this;
    else return _parent.getResolvedNode().arrLen;
  }

  override bool depsAreResolved() {
    return _parent.depsAreResolved();
  }

  void solveBefore(CstVecPrim other) {
    other.addPreRequisite(this);
  }

  void addPreRequisite(CstVecPrim domain) {
    _preReqs ~= domain;
  }

  bool isConst() { return false; }
  
  bool isIterator() { return false; }
  
  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    if (pred._scope is null || ! pred._scope.isRelated(this))
      pred.addUnresolvedRnd(this, context);
    else
      pred.addVar(this, context);
    static if (HAS_RAND_ATTRIB) {
      if (! this.isStatic()) {
	if (_type <= DomType.LAZYMONO) _type = DomType.MAYBEMONO;
      }
    }
    _parent.setDomainContext(pred, context);
  }

  override void execIterCbs() {
    assert(_iterVar !is null);
    _iterVar.unrollCbs();
    assert (_root !is null);
    _root.procUnrolledNewPredicates();
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

  
  final override bool isBool() {return false;}

  final override bool getBool() {assert (false);}

  final override void setBool(bool val) {assert (false);}

  final override long evaluate() {
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

  final void visit(CstDistSolverBase dist) { assert(false); }

  override CstDomBase getDomain() { return this; }
  
}

class CstLogicValue: CstValue, CstLogicTerm
{
  bool _val;
  
  this(bool value) {
    _val = value;
  }

  override bool isBool() {
    return true;
  }

  override bool getBool() {
    return _val;
  }

  override long value() {
    return cast(long) _val;
  }

  override bool eval() {
    return _val;
  }

  string describe(bool descExpr=false) {
    import std.conv: to;
    return _val.to!string();
  }

  void visit(CstSolver solver) {
    solver.pushToEvalStack(_val);
  }

  long evaluate() {
    return cast(long) _val;
  }

  bool isSolved() {
    return true;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    pred.addVal(this, context);
  }

  void writeExprString(ref Charbuf str) {
    // VSxxxxx or VUxxxxx
    str ~= 'V';
    _val.writeHexString(str);
  }

  void calcHash(ref Hash hash){
    hash.modify(86);
    hash.modify(0);
  }

  override CstDistSolverBase getDist() { assert(false); }
  override bool isCompatWithDist(CstDomBase A) { assert(false); }
  override void visit(CstDistSolverBase solver) { assert(false); }
  override CstLogicValue unroll(CstIterator iter, ulong n) { return this; }
  override void setDistPredContext(CstPredicate pred) { }
  override CstDomBase getDomain() { return null; }
}

class CstVecValue(T): CstVecValueBase
{
  alias RV = typeof(this);
  static if (isIntegral!T) {
    import std.traits;
    enum bool SIGNED = isSigned!T;
    enum uint BITCOUNT = T.sizeof * 8;
  }
  else static if (isBitVector!T) {
    enum bool SIGNED = T.ISSIGNED;
    enum uint BITCOUNT = T.SIZE;
  }
  else static if (isBoolean!T) {
    enum bool SIGNED = false;
    enum uint BITCOUNT = 1;
  }

  override bool isBool() {
    return isBoolean!T;
  }

  bool signed() {
    return SIGNED;
  }

  uint bitcount() {
    return BITCOUNT;
  }

  override bool getBool() {
    static if (isBoolean!T) {
      return _val;
    }
    else {
      assert (false, "getBool called on non-boolean CstVecValue");
    }
  }

  override long value() {
    return cast(long) _val;
  }

  // static Allocator _allocator;

  // static this() {
  //   CstVecValue!T._allocator = new Allocator;
  //   CstValueAllocator.allocators ~= CstVecValue!T._allocator;
  // }

  T _val;			// the value of the constant

  override RV unroll(CstIterator iters, ulong n) {
    return this;
  }


  string describe(bool descExpr=false) {
    import std.conv;
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

  void visit(CstSolver solver) {
    solver.pushToEvalStack(this);
  }

  // const(T)* getRef() {
  //   return &_val;
  // }

  // bool getVal(ref long val) {
  //   val = _val;
  //   return true;
  // }

  long evaluate() {
    return cast(long) _val;
  }

  bool isSolved() {
    return true;
  }

  void setDomainContext(CstPredicate pred, DomainContextEnum context) {
    pred.addVal(this, context);
  }

  void writeExprString(ref Charbuf str) {
    // VSxxxxx or VUxxxxx
    str ~= 'V';
    static if (isBoolean!T) {
      str ~= 'U';
    }
    else static if (isIntegral!T) {
      static if (isSigned!T) {
	str ~= 'S';
      }
      else {
	str ~= 'U';
      }
    }
    else static if (isBitVector!T) {
      static if (T.ISSIGNED) {
	str ~= 'S';
      }
      else {
	str ~= 'U';
      }
    }
    else {
      static assert (false);
    }
    _val.writeHexString(str);
  }

  void calcHash(ref Hash hash){
    hash.modify(86);
    static if (isBoolean!T) {
      hash.modify(85);
    }
    else static if (isIntegral!T) {
      static if (isSigned!T) {
	hash.modify(83);
      }
      else {
	hash.modify(85);
      }
    }
    else static if (isBitVector!T) {
      static if (T.ISSIGNED) {
	hash.modify(83);
      }
      else {
	hash.modify(85);
      }
    }
    else {
      static assert (false);
    }
    hash.modify(cast(uint)_val);
  }

}
