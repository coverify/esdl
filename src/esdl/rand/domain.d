module esdl.rand.domain;

import std.traits: isIntegral, isBoolean, isSigned, Unconst,
  OriginalType, EnumMembers, isSomeChar, isStaticArray;
import std.algorithm: canFind;

import esdl.data.bvec: isBitVector;
import esdl.data.folder: Charbuf;

import esdl.rand.base: CstValue, CstDomBase, CstDomSet, CstIterator,
  CstVecNodeIntf, CstVarNodeIntf, CstVecPrim, CstLogicTerm,
  CstVecTerm, CstVecValueBase, CstDepIntf;
import esdl.rand.misc: rand, writeHexString, isVecSigned, CstVectorOp,
  CstInsideOp, CstCompareOp, CstLogicOp, DomainContextEnum, GetVecType,
  CstVecType, _esdl__Sigbuf, EnumRange, EnumRanges;
import esdl.rand.proxy: _esdl__Proxy, _esdl__CstProcessor;
import esdl.rand.pred: CstPredicate, Hash;
import esdl.rand.agent: CstSolverAgent;
import esdl.rand.expr: CstNotLogicExpr, CstLogic2LogicExpr;
import esdl.rand.meta: _esdl__staticCast;

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
		  "Domain does not have a valid R-Value pointer: " ~
		  _esdl__getFullName());
	  if (val != *(getRef())) {
	    _valueChanged = true;
	  }
	  else {
	    _valueChanged = false;
	  }
	  *(getRef()) = val;
	  markSolved();
	}
	else {
	  assert(false);
	}
      }

      override bool isBool() {return true;}
      
      bool eval() {
	return cast(bool) *(getRef());
      }

      override long evaluate() {
	return cast(long) eval();
      }

      override void _esdl__scan() { }

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

      final override bool isDistVar() { return getDistPred() !is null; }

      override long evaluate() {
	static if (HAS_RAND_ATTRIB) {
	  if (! this._esdl__isRand || this.isSolved()) {
	    return value();
	  }
	  else {
	    assert (false, "Error evaluating " ~ _esdl__name);
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

      final override CstVecType getVecType() {
	return GetVecType!T;
      }
    }

abstract class CstVecDomain(T, rand RAND_ATTR): CstDomBase
{
  enum HAS_RAND_ATTRIB = RAND_ATTR.isRand();

  Unconst!T _shadowValue;

  static if (is (T == enum)) {
    alias OT = OriginalType!T;

    // T[] _enumSortedVals;

    // void _enumSortedValsPopulate() {
    //   import std.algorithm.sorting: sort;
    //   _enumSortedVals = cast(T[]) [EnumMembers!T];
    //   _enumSortedVals.sort();
    // }


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
    static if (is (T == enum) && isIntegral!T) {
      // uint count;

      // EnumRange!T enumRanges[] = [EnumRanges!T];
      // if (_enumSortedVals.length == 0) {
      // 	_enumSortedValsPopulate();
      // }
      // T min;
      // T max;
      // foreach (i, val; _enumSortedVals) {
      // 	if (i == 0) {
      // 	  min = val;
      // 	  max = val;
      // 	}
      // 	else {
      // 	  if (val - max == 1) {
      // 	    max = val;
      // 	  }
      // 	  else {
      // 	    _addRangeConstraint(solver, min, max);
      // 	    count += 1;
      // 	    min = val;
      // 	    max = val;
      // 	  }
      // 	}
      // }

      foreach (enumRange; [EnumRanges!T]) {
	_addRangeConstraint(solver, enumRange.min(), enumRange.max());
      }

      for (uint i=0; i!=(EnumRanges!T).length-1; ++i)
	solver.processEvalStack(CstLogicOp.LOGICOR);

      return true;
    }
    else {
      return false;
    }
  }

  void writeExprString(ref _esdl__Sigbuf str) {
    alias TYPE = typeof(this);
    TYPE resolved = _esdl__staticCast!TYPE(this._esdl__getResolvedNode());
    resolved.writeExprStringResolved(str);
  }

  void writeExprStringResolved(ref _esdl__Sigbuf str) {
    assert (this is this._esdl__getResolvedNode());
    if (this.isSolved()) {
      // import std.stdio;
      // writeln(_esdl__getFullName(), " has a value of: ", value());
      str ~= 'V';
      if (_domN < 256) (cast(ubyte) _domN).writeHexString(str);
      else (cast(ushort) _domN).writeHexString(str);
      // str ~= '#';
      // if (_varN < 256) (cast(ubyte) _varN).writeHexString(str);
      // else (cast(ushort) _varN).writeHexString(str);
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
  
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  void makeHash(){
    _hash = Hash(82);
    _hash.modify(T.stringof);
  }
  
  this(string name, _esdl__Proxy root) {
    super(name, root);
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
	writeln("Setting value of ", _esdl__getFullName(), " to: ", newVal);
      }
      *(getRef()) = newVal;
      markSolved();
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
	      "Domain does not have a valid R-Value pointer: " ~
	      _esdl__getFullName());
      if (newVal != *(getRef())) {
	_valueChanged = true;
      }
      else {
	_valueChanged = false;
      }
      debug (CSTSOLVER) {
	import std.stdio;
	writeln("Setting value of ", _esdl__getFullName(), " to: ", newVal);
      }
      *(getRef()) = newVal;
      markSolved();
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
	this.reset();
      }
    }
    else {
      assert (false);
    }
  }

  bool _valueChanged = true;

  override bool hasChanged() {
    return _valueChanged;
  }
  
  override bool updateVal() {
    assert(_esdl__isRand() !is true);
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
      return _esdl__getName();
    }
    else {
      string desc = "CstDomBase: " ~ _esdl__getName();
      // desc ~= "\n	DomType: " ~ _type.to!string();
      // if (_type !is DomType.MULTI) {
      //   desc ~= "\nIntRS: " ~ _rs.toString();
      // }
      if (_unresolvedDomainPreds.length > 0) {
	desc ~= "\n	Unresolved Domain Preds:";
	foreach (pred; _unresolvedDomainPreds) {
	  desc ~= "\n		" ~ pred._esdl__getName();
	}
	desc ~= "\n";
      }
      if (_lambdaDomainPreds.length > 0) {
	desc ~= "\n	Lambda Domain Preds:";
	foreach (pred; _lambdaDomainPreds) {
	  desc ~= "\n		" ~ pred._esdl__getName();
	}
	desc ~= "\n";
      }
      if (_resolvedDomainPreds.length > 0) {
	desc ~= "\n	Resolved Domain Preds:";
	foreach (pred; _resolvedDomainPreds) {
	  desc ~= "\n		" ~ pred._esdl__getName();
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

  string _esdl__name;

  this(RV arrVar) {
    _esdl__name = "iterVar";
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
    // writeln("size for arrVar: ", _arrVar._esdl__getName(), " is ",
    // 	    _arrVar.arrLen.value);
    return _arrVar.arrLen.value;
  }

  override string _esdl__getName() {
    string n = _arrVar._esdl__getName();
    return n ~ "->iterator";
  }

  override string _esdl__getFullName() {
    string n = _arrVar._esdl__getFullName();
    return n ~ "->iterator";
  }

  string describe(bool descExpr=false) {
    return _esdl__getName();
  }

  // while an iterator is a singleton wrt to an array, the array
  // itself could have multiple object instances in case it is not
  // concrete -- eg foo[foo.iter].iter
  override bool opEquals(Object other) {
    auto rhs = cast(typeof(this)) other;
    if (rhs is null) return false;
    else return (_arrVar == rhs._arrVar);
  }

  CstVecTerm _esdl__unroll(CstIterator iter, ulong n) {
    if(this !is iter) {
      return _arrVar._esdl__unroll(iter,n).arrLen().makeIterVar();
    }
    else {
      return new CstVecValue!size_t(n); // CstVecValue!size_t.allocate(n);
    }
  }

  override CstIterator unrollIterator(CstIterator iter, uint n) {
    assert(this !is iter);
    return _arrVar._esdl__unroll(iter,n).arrLen().makeIterVar();
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

  void annotate(CstSolverAgent agent) { }
  void writeExprString(ref _esdl__Sigbuf str) {
    // assert(false);
  }
  void calcHash(ref Hash hash) { }
  void makeHash(){}
  size_t hashValue(){
    return 1729;
  }
}

class CstArrLength(RV): CstVecDomain!(uint, RV.RAND), CstVecTerm, CstVecPrim
{

  alias AV = typeof(this);
  
  enum bool HAS_RAND_ATTRIB = RV.RAND.isRand();

  CstArrIterator!RV _iterVar;

  RV _parent;

  string _esdl__name;

  CstVecPrim[] _preReqs;

  _esdl__CstProcessor _proc;

  final override bool isDistVar() { return false; }

  override string _esdl__getName() {
    return _esdl__name;
  }

  override string _esdl__getFullName() {
    return _parent._esdl__getFullName() ~ "->length";
  }

  this(string _esdl__getName, RV parent) {
    assert (parent !is null);
    super(_esdl__getName, parent._esdl__getRootProxy());
    _esdl__name = _esdl__getName;
    _parent = parent;
    _proc = parent._esdl__getProc();
    _iterVar = new CstArrIterator!RV(_parent);
  }

  ~this() { }

  override _esdl__Proxy _esdl__getRootProxy() {
    return _parent._esdl__getRootProxy();
  }

  override bool tryResolveDep(_esdl__CstProcessor proc) {
    assert (proc is _proc);
    import std.algorithm.iteration: filter;
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("tryResolveDep: ", _esdl__getFullName());
    }
    if (! this._esdl__depsAreResolved()) return false;
    if (isMarkedSolved()) {
      debug (CSTSOLVER) {
	import std.stdio;
	writeln("tryResolveDep: Already marked solved: ", _esdl__getFullName());
      }
      // execCbs();
      return true;
    }
    else {
      if ((! this._esdl__isRand()) ||
	  _unresolvedDomainPreds.length + _lambdaDomainPreds.length == 0 ||
	  (_unresolvedDomainPreds[].filter!(pred => ! (pred.isGuard() || pred.isVisitor())).empty() &&
	   _lambdaDomainPreds[].filter!(pred => ! (pred.isGuard() || pred.isVisitor())).empty())) {
	debug (CSTSOLVER) {
	  import std.stdio;
	  writeln("tryResolveDep: Resolving: ", _esdl__getFullName());
	}
	randomizeWithoutConstraints(proc);
	return true;
      }
    }
    return false;
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    // this function will only be called when array lenght is
    // unconstrainted
    _parent.buildElements(_parent.getLen());
  }
  
  override bool _esdl__isRand() {
    static if (HAS_RAND_ATTRIB) {
      import std.traits;
      if (isStaticArray!(RV.L)) return false;
      else return true;
    }
    else {
      return false;
    }
  }

  override bool _esdl__isDomainInRange() {
    return _parent._esdl__isDomainInRange();
  }

  T to(T)()
    if(is(T == string)) {
      import std.conv;
      if(_esdl__isRand) {
	return "RAND-" ~ "#" ~ _esdl__name ~ ":" ~ value().to!string();
      }
      else {
	return "VAL#" ~ _esdl__name ~ ":" ~ value().to!string();
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
      writeln("Setting value of ", _esdl__getFullName(), " to: ", value);
    }
    _parent.setLen(cast(size_t) value);
    markSolved();
  }

  override void setVal(ulong[] v) {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Setting value of ", _esdl__getFullName(), " to: ", v[0]);
    }
    assert(v.length == 1);
    _parent.setLen(cast(size_t) v[0]);
    markSolved();
  }

  override void markSolved() {
    super.markSolved();
    _parent.markArrLen(value());
  }

  // override void collate(ulong v, int word = 0) {
  //   assert(word == 0);
  //   _parent.setLen(cast(size_t) v);
  // }

  CstVecTerm _esdl__unroll(CstIterator iter, ulong n) {
    return _parent._esdl__unroll(iter,n).arrLen();
  }

  override AV _esdl__getResolvedNode() {
    if (_parent._esdl__depsAreResolved()) return this;
    else return _parent._esdl__getResolvedNode().arrLen;
  }

  override bool _esdl__depsAreResolved() {
    return _parent._esdl__depsAreResolved();
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
    _parent.setDomainContext(pred, context);
  }

  override void execIterCbs() {
    assert(_iterVar !is null);
    _iterVar.unrollCbs();
    // assert (_root !is null);
    // _root.procUnrolledNewPredicates();
  }

  override uint* getRef() {
    assert(false);
  }

  override bool updateVal() {
    assert(_esdl__isRand() !is true);
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
  
  final override bool _esdl__isStatic() {
    return _parent._esdl__isStatic();
  }

  final override bool _esdl__isRolled() {
    return _parent._esdl__isRolled();
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
      if (! this._esdl__isRand || this.isSolved()) {
	return value();
      }
      else {
	import std.conv: to;
	assert (false, "Error evaluating " ~ _esdl__name ~
		" State: " ~ _state.to!string());
      }
    }
    else {
      return value();
    }
  }

  final void visit(CstDistSolverBase dist) { assert(false); }

  override CstDomBase getDomain() { return this; }

  // return false for array length since array lengths need to be solved
  // before any constraint on domain sets can be considered
  final override bool _esdl__parentIsConstrained() {
    // static if (is (RV: CstVecNodeIntf)) {
    //   return _parent._esdl__parentIsConstrained();
    // }
    // else {
    return false;
    // }
  }

  override final CstVecType getVecType() {
    return CstVecType.ULONG;
  }
  
}

class CstArrHierLength(RV): CstVecDomain!(uint, rand(false, false)), CstVecTerm, CstVecPrim
{

  alias AV = typeof(this);
  
  enum bool HAS_RAND_ATTRIB = true;

  // CstArrIterator!RV _iterVar;

  RV _parent;

  string _esdl__name;

  CstVecPrim[] _preReqs;

  final override bool isDistVar() { return false; }

  override string _esdl__getName() {
    return _esdl__name;
  }

  override string _esdl__getFullName() {
    return _parent._esdl__getFullName() ~ "->hierLength";
  }

  this(string _esdl__getName, RV parent) {
    assert (parent !is null);
    super(_esdl__getName, parent._esdl__getRootProxy());
    _esdl__name = _esdl__getName;
    _parent = parent;
    // _iterVar = new CstArrIterator!RV(_parent);
  }

  ~this() { }

  override _esdl__Proxy _esdl__getRootProxy() {
    return _parent._esdl__getRootProxy();
  }

  override bool tryResolveDep(_esdl__CstProcessor proc) {
    // import std.stdio;
    // writeln("Invoking tryResolveDep on: ", _esdl__getFullName());
    if (isMarkedSolved()) {
      debug (CSTSOLVER) {
	import std.stdio;
	writeln("tryResolveDep: Already marked solved: ", _esdl__getFullName());
      }
      // execCbs();
      return true;
    }
    else {
      // writeln("Invoking tryResolveDep on: ", false);
      return false;
    }
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen) { }
  
  override bool _esdl__isRand() {
    return false;
  }

  override bool _esdl__isDomainInRange() {
    return _parent._esdl__isDomainInRange();
  }

  T to(T)()
    if(is(T == string)) {
      import std.conv;
      if(_esdl__isRand) {
	return "RAND-" ~ "#" ~ _esdl__name ~ ":" ~ value().to!string();
      }
      else {
	return "VAL#" ~ _esdl__name ~ ":" ~ value().to!string();
      }
    }

  override string toString() {
    return this.to!string();
  }

  // void iterVar(CstArrIterator!RV var) {
  //   _iterVar = var;
  // }

  // CstArrIterator!RV iterVar() {
  //   return _iterVar;
  // }

  // CstArrIterator!RV makeIterVar() {
  //   if(_iterVar is null) {
  //     _iterVar = new CstArrIterator!RV(_parent);
  //   }
  //   return _iterVar;
  // }

  override uint bitcount() {
    return 32;
    // if (_parent.maxArrLen == -1) {
    //   return 32;
    // }
    // uint i = 1;
    // for (size_t c=1; c < _parent.maxArrLen; c *= 2) {
    //   i++;
    // }
    // return i;
  }

  override bool signed() {
    return false;
  }

  uint _val;
  
  override long value() {
    return _val;
  }

  override void setVal(ulong value) {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Setting value of ", _esdl__getFullName(), " to: ", value);
    }
    _val = cast(uint) value;
    markSolved();
  }

  override void setVal(ulong[] v) {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Setting value of ", _esdl__getFullName(), " to: ", v[0]);
    }
    assert(v.length == 1);
    _val = cast(uint) v[0];
    markSolved();
  }

  // override void markSolved() {
  //   super.markSolved();
  //   // _parent.markArrLen(value());
  // }

  // override bool isDepResolved() {
  //   if (_state == State.SOLVED) return true;
  //   else return false;
  // }

  // override void collate(ulong v, int word = 0) {
  //   assert(word == 0);
  //   _parent.setLen(cast(size_t) v);
  // }

  CstVecTerm _esdl__unroll(CstIterator iter, ulong n) {
    return _parent._esdl__unroll(iter,n).arrLen();
  }

  override AV _esdl__getResolvedNode() {
    if (_parent._esdl__depsAreResolved()) return this;
    else return _parent._esdl__getResolvedNode().arrHierLen;
  }

  override bool _esdl__depsAreResolved() {
    return _parent._esdl__depsAreResolved();
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
    _parent.setDomainContext(pred, context);
  }

  // override void execIterCbs() {
  //   assert(_iterVar !is null);
  //   _iterVar.unrollCbs();
  //   // assert (_root !is null);
  //   // _root.procUnrolledNewPredicates();
  // }

  override uint* getRef() {
    assert(false);
  }

  override bool updateVal() {
    return true;
  }
  
  final override bool _esdl__isStatic() {
    return _parent._esdl__isStatic();
  }

  final override bool _esdl__isRolled() {
    return _parent._esdl__isRolled();
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
      if (! this._esdl__isRand || this.isSolved()) {
	return value();
      }
      else {
	import std.conv: to;
	assert (false, "Error evaluating " ~ _esdl__name ~
		" State: " ~ _state.to!string());
      }
    }
    else {
      return value();
    }
  }

  final void visit(CstDistSolverBase dist) { assert(false); }

  override CstDomBase getDomain() { return this; }

  // return false for array length since array lengths need to be solved
  // before any constraint on domain sets can be considered
  final override bool _esdl__parentIsConstrained() {
    // static if (is (RV: CstVecNodeIntf)) {
    //   return _parent._esdl__parentIsConstrained();
    // }
    // else {
    return false;
    // }
  }

  override final CstVecType getVecType() {
    return CstVecType.ULONG;
  }
  
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

  void annotate(CstSolverAgent agent) { }

  void writeExprString(ref _esdl__Sigbuf str) {
    // VSxxxxx or VUxxxxx
    str ~= 'V';
    _val.writeHexString(str);
  }

  void calcHash(ref Hash hash){
    hash.modify(86);
    hash.modify(_val);
  }
    
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  void makeHash(){
    _hash = Hash(86);
    _hash.modify(_val);
  }

  override CstDistSolverBase getDist() { assert(false); }
  override bool isCompatWithDist(CstDomBase A) { assert(false); }
  override void visit(CstDistSolverBase solver) { assert(false); }
  override CstLogicValue _esdl__unroll(CstIterator iter, ulong n) { return this; }
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

  final override CstVecType getVecType() {
    return GetVecType!T;
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

  override RV _esdl__unroll(CstIterator iters, ulong n) {
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

  void annotate(CstSolverAgent agent) { }

  void writeExprString(ref _esdl__Sigbuf str) {
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
    hash.modify(_val);
  }
    
  Hash _hash;
  size_t hashValue() {
    return _hash.hash;
  }
  void makeHash(){
    _hash = Hash(86);
    static if (isBoolean!T) {
      _hash.modify(85);
    }
    else static if (isIntegral!T) {
      static if (isSigned!T) {
	_hash.modify(83);
      }
      else {
	_hash.modify(85);
      }
    }
    else static if (isBitVector!T) {
      static if (T.ISSIGNED) {
	_hash.modify(83);
      }
      else {
	_hash.modify(85);
      }
    }
    else {
      static assert (false);
    }
    _hash.modify(_val);
  }
  
}
