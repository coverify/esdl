module esdl.rand.expr;

import esdl.rand.obdd;
import esdl.rand.base: _esdl__RandGen, _esdl__norand, isVecSigned;
import esdl.data.bvec: isBitVector;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray, isDynamicArray;


class CstStage {
  int _id = -1;
  // List of randomized variables associated with this stage. A
  // variable can be associated with only one stage
  CstDomain[] _domVars;
  // The Bdd expressions that apply to this stage
  CstBddExpr[] _bddExprs;
  // These are the length variables that this stage will solve
  // CstVarPrim[] _preReqs;
  
  BDD _solveBDD;

  ~this() {
    _solveBDD.reset();
  }
  
  void id(uint i) {
    _id = i;
  }

  uint id() {
    return _id;
  }

  bool solved() {
    if(_id != -1) return true;
    else return false;
  }
}

// abstract class CstValAllocator {
//   static CstValAllocator[] allocators;

//   static void mark() {
//     foreach (allocator; allocators) {
//       allocator.markIndex();
//     }
//   }
  
//   static void reset() {
//     foreach (allocator; allocators) {
//       allocator.resetIndex();
//     }
//   }
  
//   abstract void resetIndex();

//   abstract void markIndex();
// }


interface CstDomain
{
  abstract string name();
  abstract ref BddVec bddvec();
  abstract void bddvec(BddVec b);
  abstract void collate(ulong v, int word=0);
  abstract CstStage stage();
  abstract void stage(CstStage s);
  abstract uint domIndex();
  abstract void domIndex(uint s);
  abstract bool signed();
  abstract bool isRand();
  abstract uint bitcount();
  abstract void reset();
  abstract BDD getPrimBdd(Buddy buddy);
  final bool solved() {
    if(isRand()) {
      return stage() !is null && stage().solved();
    }
    else {
      return true;
    }
  }
}

abstract class CstVecDomain(alias R): CstVarExpr, CstDomain
{
  enum HAS_RAND_ATTRIB = (! __traits(isSame, R, _esdl__norand));

  BddVec _valvec;

  static if (HAS_RAND_ATTRIB) {
    BddVec       _domvec;
    uint         _domIndex = uint.max;
    CstStage     _stage = null;
    uint         _resolveLap = 0;
  }
  
  ~this() {
    static if (HAS_RAND_ATTRIB) {
      _domvec.reset();
    }
    _valvec.reset();
  }    

  ref BddVec bddvec() {
    static if (HAS_RAND_ATTRIB) {
      return _domvec;
    }
    else {
      return _valvec;
    }
  }

  void bddvec(BddVec b) {
    static if (HAS_RAND_ATTRIB) {
      _domvec = b;
    }
    else {
      assert(false);
    }
  }

  uint domIndex() {
    static if (HAS_RAND_ATTRIB) {
      return _domIndex;
    }
    else {
      assert(false);
    }
  }

  void domIndex(uint s) {
    static if (HAS_RAND_ATTRIB) {
      _domIndex = s;
    }
    else {
      assert(false);
    }
  }

  void reset() {
    static if (HAS_RAND_ATTRIB) {
      _domIndex = uint.max;
    }
  }
  
  CstStage stage() {
    static if (HAS_RAND_ATTRIB) {
      return _stage;
    }
    else {
      assert(false);
    }
  }

  void stage(CstStage s) {
    static if (HAS_RAND_ATTRIB) {
      _stage = s;
    }
    else {
      assert(false);
    }
  }

  override uint resolveLap() {
    static if (HAS_RAND_ATTRIB) {
      if (_stage !is null && _stage.solved()) {
	return 0;
      }
      else {
	static if (HAS_RAND_ATTRIB) {
	  return _resolveLap;
	}
	else {
	  return 0;
	}
      }
    }
    else return 0;
  }

  override void resolveLap(uint lap) {
    static if (HAS_RAND_ATTRIB) {
      if (_stage !is null && _stage.solved()) {
	_resolveLap = 0;
      }
      else {
	static if (HAS_RAND_ATTRIB) {
	  _resolveLap = lap;
	}
      }
    }
  }

}

interface CstVarPrim
{
  abstract string name();
  abstract void _esdl__doRandomize(_esdl__RandGen randGen);
  abstract bool isRand();
  // abstract ulong value();

  abstract void _esdl__reset();
  abstract bool isVarArr();
  abstract CstDomain[] getDomainLens();
  abstract void solveBefore(CstVarPrim other);
  abstract void addPreRequisite(CstVarPrim other);

  // this method is used for getting implicit constraints that are required for
  // dynamic arrays and for enums
  abstract BDD getPrimBdd(Buddy buddy);
  abstract void resetPrimeBdd();
}


abstract class CstVarExpr
{

  // alias evaluate this;

  abstract string name();
  
  CstBddExpr toBdd() {
    auto zero = new CstVal!int(0); // CstVal!int.allocate(0);
    return new CstVec2BddExpr(this, zero, CstBinBddOp.NEQ);
  }

  // Array of indexes this expression has to resolve before it can be
  // convertted into an BDD
  abstract CstVarIterBase[] itrVars();
  abstract bool hasUnresolvedIdx();

  abstract uint resolveLap();
  abstract void resolveLap(uint lap);
  
  // List of Array Variables
  abstract CstVarPrim[] preReqs();

  bool isConst() {
    return false;
  }

  // get all the primary bdd vectors that constitute a given bdd
  // expression
  // The idea here is that we need to solve all the bdd vectors of a
  // given constraint equation together. And so, given a constraint
  // equation, we want to list out the elements that need to be
  // grouped together.
  abstract CstDomain[] getRndDomains();

  // get the list of stages this expression should be avaluated in
  // abstract CstStage[] getStages();
  abstract BddVec getBDD(CstStage stage, Buddy buddy);

  // refresh the _valvec if the current value is not the same as previous value
  abstract bool refresh(CstStage stage, Buddy buddy);

  abstract long evaluate();

  abstract CstVarExpr unwind(CstVarIterBase itr, uint n);

  bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }


  CstVec2VecExpr opBinary(string op)(CstVarExpr other)
  {
    static if(op == "&") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.AND);
    }
    static if(op == "|") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.OR);
    }
    static if(op == "^") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.XOR);
    }
    static if(op == "+") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.ADD);
    }
    static if(op == "-") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.SUB);
    }
    static if(op == "*") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.MUL);
    }
    static if(op == "/") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.DIV);
    }
    static if(op == "%") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.REM);
    }
    static if(op == "<<") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.LSH);
    }
    static if(op == ">>") {
      return new CstVec2VecExpr(this, other, CstBinVecOp.RSH);
    }
  }

  CstVec2VecExpr opBinary(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
  	auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
  	static if(op == "&") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.AND);
  	}
  	static if(op == "|") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.OR);
  	}
  	static if(op == "^") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.XOR);
  	}
  	static if(op == "+") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.ADD);
  	}
  	static if(op == "-") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.SUB);
  	}
  	static if(op == "*") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.MUL);
  	}
  	static if(op == "/") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.DIV);
  	}
  	static if(op == "%") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.REM);
  	}
  	static if(op == "<<") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.LSH);
  	}
  	static if(op == ">>") {
  	  return new CstVec2VecExpr(this, qq, CstBinVecOp.RSH);
  	}
      }

  CstVec2VecExpr opBinaryRight(string op, Q)(Q q)
    if(isBitVector!Q || isIntegral!Q)
      {
	auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
	static if(op == "&") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.AND);
	}
	static if(op == "|") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.OR);
	}
	static if(op == "^") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.XOR);
	}
	static if(op == "+") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.ADD);
	}
	static if(op == "-") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.SUB);
	}
	static if(op == "*") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.MUL);
	}
	static if(op == "/") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.DIV);
	}
	static if(op == "%") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.REM);
	}
	static if(op == "<<") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.LSH);
	}
	static if(op == ">>") {
	  return new CstVec2VecExpr(qq, this, CstBinVecOp.RSH);
	}
      }

  CstVarExpr opIndex(CstVarExpr index)
  {
    // assert(false, "Index operation defined only for Arrays");
    return new CstVecSliceExpr(this, index);
  }

  CstVarExpr opSlice(P)(P p)
    if(isIntegral!P || isBitVector!P) {
      return new CstVecSliceExpr(this, new CstVal!P(p)); // CstVal!P.allocate(p));
    }

  CstVarExpr opSlice(CstVarExpr lhs, CstVarExpr rhs)
  {
    return new CstVecSliceExpr(this, lhs, rhs);
  }

  CstVarExpr opSlice(P, Q)(P p, Q q)
    if((isIntegral!P || isBitVector!P) && (isIntegral!Q || isBitVector!Q)) {
      return new CstVecSliceExpr(this, new CstVal!P(p), // CstVal!P.allocate(p),
				 new CstVal!Q(q)); // CstVal!Q.allocate(q));
    }
  CstNotBddExpr opUnary(string op)() if(op == "*") {
    // static if(op == "*") {	// "!" in cstx is translated as "*"
    return new CstNotBddExpr(_esdl__toBdd(this));
    // }
    // else {
    //   static assert(false);
    // }
  }
  CstNotVecExpr opUnary(string op)() if(op == "~") {
    // static if(op == "*") {	// "!" in cstx is translated as "*"
    return new CstNotVecExpr(this);
    // }
    // else {
    //   static assert(false);
    // }
  }
  CstNegVecExpr opUnary(string op)() if(op == "-") {
    // static if(op == "*") {	// "!" in cstx is translated as "*"
    return new CstNegVecExpr(this);
    // }
    // else {
    //   static assert(false);
    // }
  }
}

abstract class CstValBase: CstVarExpr
{
  override CstVarPrim[] preReqs() {
    return [];
  }

  override CstVarIterBase[] itrVars() {
    return [];
  }

  override bool hasUnresolvedIdx() {
    return false;
  }
      
  override bool isConst() {
    return true;
  }

  override CstDomain[] getRndDomains() {
    return [];
  }

  override CstVarExpr unwind(CstVarIterBase l, uint n) {
    return this;
  }
}

auto _esdl__cstVal(T)(T val) {
  return new CstVal!(T)(val); // CstVal!(T).allocate(val);
}

class CstVal(T = int): CstValBase
{
  // static class Allocator: CstValAllocator {
  //   CstVal!T[] container;
  //   uint _index = 0;

  //   uint _mark;

  //   override void markIndex() {
  //     _mark = _index;
  //   }

  //   override void resetIndex() {
  //     for (uint i = _mark; i != _index; ++i) {
  // 	container[i]._valvec.reset();
  //     }
  //     _index = _mark;
      
  //   }


  //   CstVal!T allocate(T val) {
  //     // return new CstVal!T(val);
  //     if (_index >= container.length) {
  //   	container.length += 1;
  //   	container[$-1] = new CstVal!T(val);
  //     }
      
  //     auto cstVal = container[_index];
  //     cstVal._val = val;
  //     _index++;
  //     return cstVal;
  //   }
  // }

  import std.conv;

  // static Allocator _allocator;

  // static this() {
  //   CstVal!T._allocator = new Allocator;
  //   CstValAllocator.allocators ~= CstVal!T._allocator;
  // }

  T _val;			// the value of the constant
  BddVec _valvec;

  override string name() {
    return _val.to!string();
  }

  // static CstVal!T allocate(T value) {
  //   Allocator allocator = _allocator;
  //   if (allocator is null) {
  //     allocator = new Allocator;
  //     _allocator = allocator;
  //     CstValAllocator.allocators ~= allocator;
  //   }

  //   // return new CstVal!T(value);
  //   return allocator.allocate(value);
  // }

  this(T value) {
    _val = value;
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    if (_valvec.isNull()) {
      _valvec.buildVec(buddy, _val);
      return true;
    }
    else {
      return false;
    }
  }
  
  override BddVec getBDD(CstStage stage, Buddy buddy) {
    return _valvec;
  }

  const(T)* getRef() {
    return &_val;
  }

  override long evaluate() {
    return _val;
  }

  override bool hasUnresolvedIdx() {
    return false;
  }

  override uint resolveLap() {
    return 0;			// const
  }

  override void resolveLap(uint lap) {}

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }
}


// This class represents an unwound Foreach itr at vec level
abstract class CstVarIterBase: CstVarExpr
{
  string _name;

  override string name() {
    return name;
  }

  this(string name) {
    _name = name;
  }

  abstract uint maxVal();

  // this will not return the arrVar since the length variable is
  // not getting constrained here
  override CstVarPrim[] preReqs() {
    return [];
  }

  abstract bool isUnwindable();

  // get the list of stages this expression should be avaluated in
  // override CstStage[] getStages() {
  //   return arrVar.arrLen.getStages();
  // }

  override bool refresh(CstStage s, Buddy buddy) {
    assert(false, "Can not refresh for a Itr Variable without unwinding");
  }
  
  override BddVec getBDD(CstStage stage, Buddy buddy) {
    assert(false, "Can not getBDD for a Itr Variable without unwinding");
  }

  override long evaluate() {
    assert(false, "Can not evaluate a Itr Variable without unwinding");
  }

}

class CstVarIter(RV): CstVarIterBase
{
  RV _arrVar;

  RV arrVar() {
    return _arrVar;
  }

  this(RV arrVar) {
    super("itrVar");
    _arrVar = arrVar;
    _arrVar._arrLen.itrVar(this);
  }

  override CstVarIterBase[] itrVars() {
    return _arrVar.itrVars() ~ this;
  }

  override bool hasUnresolvedIdx() {
    return true;
  }
      
  override uint maxVal() {
    if(! this.isUnwindable()) {
      assert(false, "Can not find maxVal since the " ~
	     "Itr Variable is unwindable");
    }
    // import std.stdio;
    // writeln("maxVal for arrVar: ", _arrVar.name(), " is ",
    // 	    _arrVar.arrLen.value);
    return cast(uint) _arrVar.arrLen.value;
  }

  override bool isUnwindable() {
    return _arrVar.isUnwindable();
  }

  // get all the primary bdd vectors that constitute a given bdd expression
  override CstDomain[] getRndDomains() {
    return [_arrVar._arrLen]; // _arrVar.arrLen.getRndDomains();
  }

  override string name() {
    string n = _arrVar.arrLen.name();
    return n[0..$-3] ~ "iter";
  }
  override CstVarExpr unwind(CstVarIterBase itr, uint n) {
    if(this !is itr) {
      return _arrVar.unwind(itr,n).arrLen().makeItrVar();
    }
    else {
      return new CstVal!size_t(n); // CstVal!size_t.allocate(n);
    }
  }

  override uint resolveLap() {
    assert (false, "resolveLap should never be called on CstVarIter");
  }

  override void resolveLap(uint lap) {}

  override bool isConst() {
    return false;
  }

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }
}

class CstVarLen(RV): CstVecDomain!(RV.RAND), CstVarPrim
{

  enum HAS_RAND_ATTRIB = (! __traits(isSame, RV.RAND, _esdl__norand));

  // This bdd has the constraint on the max length of the array
  BDD _primBdd;
  
  CstVarIter!RV _itrVar;

  RV _parent;

  BddVec _valvec;
  
  string _name;

  CstVarPrim[] _preReqs;

  override string name() {
    return _name;
  }

  this(string name, RV parent) {
    assert(parent !is null);
    _name = name;
    _parent = parent;
  }

  ~this() {
    _domvec.reset();
    _valvec.reset();
    _primBdd.reset();
  }

  override CstVarPrim[] preReqs() {
    return _preReqs ~ _parent.preReqs();
  }

  override CstVarIterBase[] itrVars() {
    return _parent.itrVars();
  }

  override bool hasUnresolvedIdx() {
    // just must make sure that the parents length has been resolved
    return _parent.parentLenIsUnresolved();
  }
      
  override CstDomain[] getRndDomains() {
    return _parent.getDomainLens();
  }

  CstDomain[] getDomainLens() {
    return [this];
  }
  
  private bool refreshNoRand(Buddy buddy) {
    auto val = _parent.getLen();
    if (! _valvec.isNull()) {
      return false;
    }
    else {
      _valvec.buildVec(buddy, val);
      return true;
    }
  }

  // override CstStage[] getStages() {
  //   CstStage[] stages;
  //   if(isRand) stages = [this.stage()];
  //   return stages;
  // }
  override bool refresh(CstStage s, Buddy buddy) {
    static if (HAS_RAND_ATTRIB) {
      auto fparent = _parent.flatten();
      if (fparent !is _parent) {
	return _parent.flatten().arrLen.refresh(s, buddy);
      }
      else {
	assert(stage() !is null, "stage null for: " ~ name());
	if(this.isRand && stage() is s) {
	  return false;
	}
	else if((! this.isRand) ||
		this.isRand && stage().solved()) { // work with the value
	  return refreshNoRand(buddy);
	}
	else {
	  assert(false, "Constraint evaluation in wrong stage");
	}
      }
    }
    else {
      return refreshNoRand(buddy);
    }
  }

  override BddVec getBDD(CstStage s, Buddy buddy) {
    static if (HAS_RAND_ATTRIB) {
      auto fparent = _parent.flatten();
      if (fparent !is _parent) {
	return _parent.flatten().arrLen.getBDD(s, buddy);
      }
      else {
	assert(stage() !is null, "stage null for: " ~ name());
	if(this.isRand && stage() is s) {
	  return _domvec;
	}
	else if((! this.isRand) ||
		this.isRand && stage().solved()) { // work with the value
	  return _valvec;
	}
	else {
	  assert(false, "Constraint evaluation in wrong stage");
	}
      }
    }
    else {
      return _valvec;
    }
  }

  override long evaluate() {
    static if (HAS_RAND_ATTRIB) {
      if(! this.isRand || stage().solved()) {
	return value();
      }
      else {
	import std.conv;
	assert(false, "Rand variable " ~ _name ~ " evaluation in wrong stage: " ~
	       stage()._id.to!string);
      }
    }
    else {
      return value();
    }
  }

  void _esdl__doRandomize(_esdl__RandGen randGen) {
    assert(false);
  }
  
  bool isRand() {
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

  BDD getPrimBdd(Buddy buddy) {
    if(_primBdd.isZero()) {
      _primBdd = this.bddvec.lte(buddy.buildVec(_parent.maxArrLen));
    }
    return _primBdd;
  }
  
  void resetPrimeBdd() {
    _primBdd.reset();
  }

  void itrVar(CstVarIter!RV var) {
    _itrVar = var;
  }

  CstVarIter!RV itrVar() {
    return _itrVar;
  }

  CstVarIter!RV makeItrVar() {
    if(_itrVar is null) {
      _itrVar = new CstVarIter!RV(_parent);
    }
    return _itrVar;
  }

  uint bitcount() {
    uint i = 1;
    for (size_t c=1; c < _parent.maxArrLen; c *= 2) {
      i++;
    }
    return i;
  }

  bool signed() {
    return false;
  }

  ulong value() {
    return _parent.getLen();
  }

  void collate(ulong v, int word = 0) {
    assert(word == 0);
    // import std.stdio;
    // writeln("Setting value for arrlen for ", _parent.name, " to ", v);
    // import std.stdio;
    // writeln("Setting length for array: ", _parent.name(), " to ", v);
    _parent.setLen(cast(size_t) v);
    _parent.build();
    // writeln("Getting length for array: ", _parent.name(), " as ", _parent.getLen());
    
  }

  override CstVarLen!RV unwind(CstVarIterBase itr, uint n) {
    return _parent.unwind(itr,n).arrLen();
  }

  void _esdl__reset() {
    _stage = null;
    _resolveLap = 0;
  }

  bool isVarArr() {
    return false;
  }

  void solveBefore(CstVarPrim other) {
    other.addPreRequisite(this);
  }

  void addPreRequisite(CstVarPrim domain) {
    _preReqs ~= domain;
  }

  override bool isConst() {
    return false;
  }
  
  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }

}

// All the operations that produce a BddVec
enum CstBinVecOp: byte
  {   AND,
      OR ,
      XOR,
      ADD,
      SUB,
      MUL,
      DIV,
      REM,
      LSH,
      RSH,
      BITINDEX,
      }

// All the operations that produce a Bdd
enum CstBinBddOp: byte
  {   LTH,
      LTE,
      GTH,
      GTE,
      EQU,
      NEQ,
      }

// This class would hold two(bin) vector nodes and produces a vector
// only after processing those two nodes
class CstVec2VecExpr: CstVarExpr
{
  import std.conv;

  CstVarExpr _lhs;
  CstVarExpr _rhs;
  CstBinVecOp _op;

  // CstDomain[] _preReqs;
  override CstVarPrim[] preReqs() {
    return _lhs.preReqs() ~ _rhs.preReqs();
  }

  CstVarIterBase[] _itrVars;
  override CstVarIterBase[] itrVars() {
    return _itrVars;
  }

  override bool hasUnresolvedIdx() {
    return _lhs.hasUnresolvedIdx() || _rhs.hasUnresolvedIdx();
  }
      
  override string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string() ~ " " ~ _rhs.name ~ " )";
  }

  override CstDomain[] getRndDomains() {
    return _lhs.getRndDomains() ~ _rhs.getRndDomains();
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  override BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.itrVars.length !is 0) {
      assert(false,
	     "CstVec2VecExpr: Need to unwind the itrVars" ~
	     " before attempting to solve BDD");
    }

    // auto lvec = _lhs.getBDD(stage, buddy);
    // auto rvec = _rhs.getBDD(stage, buddy);

    final switch(_op) {
    case CstBinVecOp.AND: return _lhs.getBDD(stage, buddy) &
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.OR:  return _lhs.getBDD(stage, buddy) |
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.XOR: return _lhs.getBDD(stage, buddy) ^
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.ADD: return _lhs.getBDD(stage, buddy) +
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.SUB: return _lhs.getBDD(stage, buddy) -
	_rhs.getBDD(stage, buddy);
    case CstBinVecOp.MUL:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) *
			   _rhs.evaluate();
      if(_lhs.isConst()) return _lhs.evaluate() *
			   _rhs.getBDD(stage, buddy);
      return _lhs.getBDD(stage, buddy) * _rhs.getBDD(stage, buddy);
    case CstBinVecOp.DIV:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) /
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) / _rhs.getBDD(stage, buddy);
    case CstBinVecOp.REM:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) %
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) % _rhs.getBDD(stage, buddy);
    case CstBinVecOp.LSH:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) <<
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) << _rhs.getBDD(stage, buddy);
    case CstBinVecOp.RSH:
      if(_rhs.isConst()) return _lhs.getBDD(stage, buddy) >>
			   _rhs.evaluate();
      return _lhs.getBDD(stage, buddy) >> _rhs.getBDD(stage, buddy);
    case CstBinVecOp.BITINDEX:
      assert(false, "BITINDEX is not implemented yet!");
    }
  }

  override long evaluate() {
    auto lvec = _lhs.evaluate();
    auto rvec = _rhs.evaluate();

    final switch(_op) {
    case CstBinVecOp.AND: return lvec &  rvec;
    case CstBinVecOp.OR:  return lvec |  rvec;
    case CstBinVecOp.XOR: return lvec ^  rvec;
    case CstBinVecOp.ADD: return lvec +  rvec;
    case CstBinVecOp.SUB: return lvec -  rvec;
    case CstBinVecOp.MUL: return lvec *  rvec;
    case CstBinVecOp.DIV: return lvec /  rvec;
    case CstBinVecOp.REM: return lvec %  rvec;
    case CstBinVecOp.LSH: return lvec << rvec;
    case CstBinVecOp.RSH: return lvec >> rvec;
    case CstBinVecOp.BITINDEX:
      assert(false, "BITINDEX is not implemented yet!");
    }
  }

  override CstVec2VecExpr unwind(CstVarIterBase itr, uint n) {
    bool found = false;
    foreach(var; itrVars()) {
      if(itr is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstVec2VecExpr(_lhs.unwind(itr, n), _rhs.unwind(itr, n), _op);
    }
  }

  this(CstVarExpr lhs, CstVarExpr rhs, CstBinVecOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
    _itrVars = lhs.itrVars ~ rhs.itrVars;
    // foreach(var; lhs.itrVars ~ rhs.itrVars) {
    //   bool add = true;
    //   foreach(l; _itrVars) {
    // 	if(l is var) add = false;
    // 	break;
    //   }
    //   if(add) _itrVars ~= var;
    // }
  }

  override uint resolveLap() {
    auto lhs = _lhs.resolveLap();
    auto rhs = _rhs.resolveLap();
    if (rhs > lhs) return rhs;
    else return lhs;
  }

  override void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }
  
  override bool isConst() {
    return false;
  }

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }
}

class CstVecSliceExpr: CstVarExpr
{
  CstVarExpr _vec;
  CstVarExpr _lhs;
  CstVarExpr _rhs;

  // CstDomain[] _preReqs;
  override CstVarPrim[] preReqs() {
    CstVarPrim[] reqs;
    if(_rhs is null) {
      return _vec.preReqs() ~ _lhs.preReqs();
      // foreach(req; _vec.preReqs() ~ _lhs.preReqs()) {
      // 	if(! req.solved()) {
      // 	  reqs ~= req;
      // 	}
      // }
    }
    else {
      return _vec.preReqs() ~ _lhs.preReqs() ~ _rhs.preReqs();
      // foreach(req; _vec.preReqs() ~ _lhs.preReqs() ~ _rhs.preReqs()) {
      // 	if(! req.solved()) {
      // 	  reqs ~= req;
      // 	}
      // }
    }
    return reqs;
  }
  
  CstVarIterBase[] _itrVars;
  override CstVarIterBase[] itrVars() {
    return _itrVars;
  }

  override bool hasUnresolvedIdx() {
    return
      _lhs.hasUnresolvedIdx() ||
      _rhs.hasUnresolvedIdx() ||
      _vec.hasUnresolvedIdx();
  }

  override string name() {
    return _vec.name() ~ "[ " ~ _lhs.name() ~ " .. " ~ _rhs.name() ~ " ]";
  }

  override CstDomain[] getRndDomains() {
    if(_rhs is null) {
      return _vec.getRndDomains() ~ _lhs.getRndDomains();
    }
    else {
      return _vec.getRndDomains() ~ _lhs.getRndDomains() ~ _rhs.getRndDomains();
    }
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  override BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.itrVars.length !is 0) {
      assert(false,
	     "CstVecSliceExpr: Need to unwind the itrVars" ~
	     " before attempting to solve BDD");
    }

    auto vec  = _vec.getBDD(stage, buddy);
    size_t lvec = cast(size_t) _lhs.evaluate();
    size_t rvec = lvec;
    if(_rhs is null) {
      rvec = lvec + 1;
    }
    else {
      rvec = cast(size_t) _rhs.evaluate();
    }
    return vec[lvec..rvec];
  }

  override long evaluate() {
    // auto vec  = _vec.evaluate();
    // auto lvec = _lhs.evaluate();
    // auto rvec = _rhs.evaluate();

    assert(false, "Can not evaluate a CstVecSliceExpr!");
  }

  override CstVecSliceExpr unwind(CstVarIterBase itr, uint n) {
    bool found = false;
    foreach(var; itrVars()) {
      if(itr is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      if(_rhs is null) {
	return new CstVecSliceExpr(_vec.unwind(itr, n), _lhs.unwind(itr, n));
      }
      else {
	return new CstVecSliceExpr(_vec.unwind(itr, n),
				   _lhs.unwind(itr, n), _rhs.unwind(itr, n));
      }
    }
  }

  this(CstVarExpr vec, CstVarExpr lhs, CstVarExpr rhs=null) {
    _vec = vec;
    _lhs = lhs;
    _rhs = rhs;
    auto itrVars = vec.itrVars ~ lhs.itrVars;
    if(rhs !is null) {
      itrVars ~= rhs.itrVars;
    }
    foreach(var; itrVars) {
      bool add = true;
      foreach(l; _itrVars) {
	if(l is var) add = false;
	break;
      }
      if(add) _itrVars ~= var;
    }
  }

  override uint resolveLap() {
    return _vec.resolveLap();
  }

  override void resolveLap(uint lap) {
    _vec.resolveLap(lap);
  }

  override bool isConst() {
    return false;
  }

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }
}

class CstNotVecExpr: CstVarExpr
{
  import std.conv;

  CstVarExpr _expr;

  // CstDomain[] _preReqs;
  override CstVarPrim[] preReqs() {
    return _expr.preReqs();
  }

  CstVarIterBase[] _itrVars;
  override CstVarIterBase[] itrVars() {
    return _itrVars;
  }

  override bool hasUnresolvedIdx() {
    return _expr.hasUnresolvedIdx();
  }
      
  override string name() {
    return "( ~ " ~ _expr.name ~ " )";
  }

  override CstDomain[] getRndDomains() {
    return _expr.getRndDomains();
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    return _expr.refresh(stage, buddy);
  }
  
  override BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.itrVars.length !is 0) {
      assert(false,
	     "CstNotVecExpr: Need to unwind the itrVars" ~
	     " before attempting to solve BDD");
    }

    return ~(_expr.getBDD(stage, buddy));
  }

  override long evaluate() {
    return ~(_expr.evaluate());
  }

  override CstNotVecExpr unwind(CstVarIterBase itr, uint n) {
    bool found = false;
    foreach(var; itrVars()) {
      if(itr is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstNotVecExpr(_expr.unwind(itr, n));
    }
  }

  this(CstVarExpr expr) {
    _expr = expr;
    _itrVars = _expr.itrVars;
  }

  override uint resolveLap() {
    return _expr.resolveLap();
  }

  override void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }
  
  override bool isConst() {
    return false;
  }

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }
}

class CstNegVecExpr: CstVarExpr
{
  import std.conv;

  CstVarExpr _expr;

  // CstDomain[] _preReqs;
  override CstVarPrim[] preReqs() {
    return _expr.preReqs();
  }

  CstVarIterBase[] _itrVars;
  override CstVarIterBase[] itrVars() {
    return _itrVars;
  }

  override bool hasUnresolvedIdx() {
    return _expr.hasUnresolvedIdx();
  }
      
  override string name() {
    return "( - " ~ _expr.name ~ " )";
  }

  override CstDomain[] getRndDomains() {
    return _expr.getRndDomains();
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    return _expr.refresh(stage, buddy);
  }
  
  override BddVec getBDD(CstStage stage, Buddy buddy) {
    if(this.itrVars.length !is 0) {
      assert(false,
	     "CstNegVecExpr: Need to unwind the itrVars" ~
	     " before attempting to solve BDD");
    }

    return -(_expr.getBDD(stage, buddy));
  }

  override long evaluate() {
    return -(_expr.evaluate());
  }

  override CstNegVecExpr unwind(CstVarIterBase itr, uint n) {
    bool found = false;
    foreach(var; itrVars()) {
      if(itr is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstNegVecExpr(_expr.unwind(itr, n));
    }
  }

  this(CstVarExpr expr) {
    _expr = expr;
    _itrVars = _expr.itrVars;
  }

  override uint resolveLap() {
    return _expr.resolveLap();
  }

  override void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }
  
  override bool isConst() {
    return false;
  }

  override bool isOrderingExpr() {
    return false;		// only CstVecOrderingExpr return true
  }
}


enum CstBddOp: byte
  {   LOGICAND,
      LOGICOR ,
      LOGICIMP,
      }

abstract class CstBddExpr
{
  string name();

  abstract bool refresh(CstStage stage, Buddy buddy);
  
  abstract CstVarIterBase[] itrVars(); //  {

  abstract CstVarPrim[] preReqs();

  abstract bool hasUnresolvedIdx();

  abstract uint resolveLap();
  abstract void resolveLap(uint lap);
  
  // unwind recursively untill no unwinding is possible
  CstBddExpr[] unwind() {
    CstBddExpr[] unwound;
    auto itr = this.unwindableItr();
    if(itr is null) {
      return [this];
    }
    else {
      foreach(expr; this.unwind(itr)) {
	// import std.stdio;
	// writeln(this.name(), " unwound expr: ", expr.name());
	// writeln(expr.name());
	if(expr.unwindableItr() is null) unwound ~= expr;
	else unwound ~= expr.unwind();
      }
    }
    return unwound;
  }

  CstBddExpr[] unwind(CstVarIterBase itr) {
    CstBddExpr[] retval;
    if(! itr.isUnwindable()) {
      assert(false, "CstVarIterBase is not unwindabe yet");
    }
    auto max = itr.maxVal();
    // import std.stdio;
    // writeln("maxVal is ", max);
    for (uint i = 0; i != max; ++i) {
      retval ~= this.unwind(itr, i);
    }
    return retval;
  }

  CstVarIterBase unwindableItr() {
    foreach(itr; itrVars()) {
      if(itr.isUnwindable()) return itr;
    }
    return null;
  }

  abstract CstBddExpr unwind(CstVarIterBase itr, uint n);

  abstract CstDomain[] getRndDomains();

  // abstract CstStage[] getStages();

  abstract BDD getBDD(CstStage stage, Buddy buddy);

  CstBdd2BddExpr opBinary(string op)(CstBddExpr other)
  {
    static if(op == "&") {
      return new CstBdd2BddExpr(this, other, CstBddOp.LOGICAND);
    }
    static if(op == "|") {
      return new CstBdd2BddExpr(this, other, CstBddOp.LOGICOR);
    }
    static if(op == ">>") {
      return new CstBdd2BddExpr(this, other, CstBddOp.LOGICIMP);
    }
  }

  CstNotBddExpr opUnary(string op)()
  {
    static if(op == "*") {	// "!" in cstx is translated as "*"
      return new CstNotBddExpr(this);
    }
  }

  CstBdd2BddExpr implies(CstBddExpr other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICIMP);
  }

  CstBdd2BddExpr implies(CstVarExpr other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICIMP);
  }

  CstBdd2BddExpr logicOr(CstBddExpr other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICOR);
  }

  CstBdd2BddExpr logicOr(CstVarExpr other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICOR);
  }

  CstBdd2BddExpr logicAnd(CstBddExpr other)
  {
    return new CstBdd2BddExpr(this, other, CstBddOp.LOGICAND);
  }

  CstBdd2BddExpr logicAnd(CstVarExpr other)
  {
    return new CstBdd2BddExpr(this, other.toBdd(), CstBddOp.LOGICAND);
  }

}

class CstBdd2BddExpr: CstBddExpr
{
  import std.conv;

  CstBddExpr _lhs;
  CstBddExpr _rhs;
  CstBddOp _op;

  CstVarIterBase[] _itrVars;

  override CstVarIterBase[] itrVars() {
       return _itrVars;
  }

  this(CstBddExpr lhs, CstBddExpr rhs, CstBddOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
    foreach(var; lhs.itrVars ~ rhs.itrVars) {
      bool add = true;
      foreach(l; _itrVars) {
	if(l is var) add = false;
	break;
      }
      if(add) _itrVars ~= var;
    }
  }
  override bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  override bool hasUnresolvedIdx() {
    return _lhs.hasUnresolvedIdx() || _rhs.hasUnresolvedIdx();
  }

  override string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string ~ " " ~ _rhs.name ~ " )";
  }

  override CstVarPrim[] preReqs() {
    return _lhs.preReqs() ~ _rhs.preReqs();
    // CstVarPrim[] reqs;
    // foreach(req; _lhs.preReqs() ~ _rhs.preReqs()) {
    //   if(! req.solved()) {
    // 	reqs ~= req;
    //   }
    // }
    // return reqs;
  }

  override CstDomain[] getRndDomains() {
    return _lhs.getRndDomains() ~ _rhs.getRndDomains();
  }


  override BDD getBDD(CstStage stage, Buddy buddy) {
    if(this.itrVars.length !is 0) {
      assert(false,
	     "CstBdd2BddExpr: Need to unwind the itrVars" ~
	     " before attempting to solve BDD");
    }
    auto lvec = _lhs.getBDD(stage, buddy);
    auto rvec = _rhs.getBDD(stage, buddy);

    BDD retval;
    final switch(_op) {
    case CstBddOp.LOGICAND: retval = lvec &  rvec; break;
    case CstBddOp.LOGICOR:  retval = lvec |  rvec; break;
    case CstBddOp.LOGICIMP: retval = lvec >> rvec; break;
    }
    return retval;
  }

  override CstBdd2BddExpr unwind(CstVarIterBase itr, uint n) {
    bool found = false;
    foreach(var; itrVars()) {
      if(itr is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      return new CstBdd2BddExpr(_lhs.unwind(itr, n), _rhs.unwind(itr, n), _op);
    }
  }

  override uint resolveLap() {
    uint lhs = _lhs.resolveLap();
    uint rhs = _rhs.resolveLap();
    if (lhs > rhs) return lhs;
    else return rhs;
  }
  override void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }
}

// TBD
class CstIteBddExpr: CstBddExpr
{
  CstVarIterBase[] _itrVars;

  override CstVarIterBase[] itrVars() {
    return _itrVars;
  }

  override bool hasUnresolvedIdx() {
    assert(false, "TBD");
  }

  override string name() {
    return "CstIteBddExpr";
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    assert(false);
  }
}

class CstVec2BddExpr: CstBddExpr
{
  import std.conv;

  CstVarExpr _lhs;
  CstVarExpr _rhs;
  CstBinBddOp _op;

  CstVarIterBase[] _itrVars;

  override CstVarIterBase[] itrVars() {
       return _itrVars;
  }

  this(CstVarExpr lhs, CstVarExpr rhs, CstBinBddOp op) {
    _lhs = lhs;
    _rhs = rhs;
    _op = op;
    foreach(var; lhs.itrVars ~ rhs.itrVars) {
      bool add = true;
      foreach(l; _itrVars) {
	if(l is var) add = false;
	break;
      }
      if(add) _itrVars ~= var;
    }
  }

  override string name() {
    return "( " ~ _lhs.name ~ " " ~ _op.to!string ~ " " ~ _rhs.name ~ " )";
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    auto l = _lhs.refresh(stage, buddy);
    auto r = _rhs.refresh(stage, buddy);
    return r || l;
  }
  
  override CstVarPrim[] preReqs() {
    return _lhs.preReqs() ~ _rhs.preReqs();
    // CstVarPrim[] reqs;
    // foreach(req; _lhs.preReqs() ~ _rhs.preReqs()) {
    //   if(! req.solved()) {
    // 	reqs ~= req;
    //   }
    // }
    // return reqs;
  }
    
  override CstDomain[] getRndDomains() {
    return _lhs.getRndDomains() ~ _rhs.getRndDomains();
  }

  override BDD getBDD(CstStage stage, Buddy buddy) {
    if (this.itrVars.length !is 0) {
      // foreach (itr; itrVars) {
      // 	import std.stdio;
      // 	writeln(name(), " : ", itr.name());
      // }
      assert(false,
	     "CstVec2BddExpr: Need to unwind the itrVars" ~
	     " before attempting to solve BDD");
    }
    auto lvec = _lhs.getBDD(stage, buddy);
    auto rvec = _rhs.getBDD(stage, buddy);

    BDD retval;
    final switch(_op) {
    case CstBinBddOp.LTH: retval = lvec.lth(rvec); break;
    case CstBinBddOp.LTE: retval = lvec.lte(rvec); break;
    case CstBinBddOp.GTH: retval = lvec.gth(rvec); break;
    case CstBinBddOp.GTE: retval = lvec.gte(rvec); break;
    case CstBinBddOp.EQU: retval = lvec.equ(rvec); break;
    case CstBinBddOp.NEQ: retval = lvec.neq(rvec); break;
    }
    return retval;
  }

  override CstVec2BddExpr unwind(CstVarIterBase itr, uint n) {
    // import std.stdio;
    // writeln(_lhs.name() ~ " " ~ _op.to!string ~ " " ~ _rhs.name() ~ " Getting unwound!");
    bool found = false;
    foreach(var; itrVars()) {
      if(itr is var) {
	found = true;
	break;
      }
    }
    if(! found) return this;
    else {
      // writeln("RHS: ", _rhs.unwind(itr, n).name());
      // writeln("LHS: ", _lhs.unwind(itr, n).name());
      return new CstVec2BddExpr(_lhs.unwind(itr, n), _rhs.unwind(itr, n), _op);
    }
  }

  override bool hasUnresolvedIdx() {
    return _lhs.hasUnresolvedIdx() || _rhs.hasUnresolvedIdx();
  }

  override uint resolveLap() {
    uint lhs = _lhs.resolveLap();
    uint rhs = _rhs.resolveLap();
    if (lhs > rhs) return lhs;
    else return rhs;
  }
  
  override void resolveLap(uint lap) {
    _lhs.resolveLap(lap);
    _rhs.resolveLap(lap);
  }
}

class CstBddConst: CstBddExpr
{
  immutable bool _expr;

  override CstVarIterBase[] itrVars() {
       return [];
  }

  this(bool expr) {
    _expr = expr;
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    return false;
  }
  
  override BDD getBDD(CstStage stage, Buddy buddy) {
    if(_expr) return buddy.one();
    else return buddy.zero();
  }

  override string name() {
    if(_expr) return "TRUE";
    else return "FALSE";
  }

  override CstDomain[] getRndDomains() {
    return [];
  }

  override CstVarPrim[] preReqs() {
    return [];
  }

  override CstBddConst unwind(CstVarIterBase itr, uint n) {
    return this;
  }

  override bool hasUnresolvedIdx() {
    return false;
  }

  override uint resolveLap() {
    return 0;
  }
  override void resolveLap(uint lap) {}
}

class CstNotBddExpr: CstBddExpr
{
  CstBddExpr _expr;

  this(CstBddExpr expr) {
    _expr = expr;
  }

  override CstVarIterBase[] itrVars() {
    return _expr.itrVars();
  }

  override string name() {
    return "( " ~ "!" ~ " " ~ _expr.name ~ " )";
  }

  override bool refresh(CstStage stage, Buddy buddy) {
    return _expr.refresh(stage, buddy);
  }
  
  override CstVarPrim[] preReqs() {
    return _expr.preReqs();
  }

  override CstDomain[] getRndDomains() {
    return _expr.getRndDomains();
  }

  override BDD getBDD(CstStage stage, Buddy buddy) {
    if(this.itrVars.length !is 0) {
      assert(false,
	     "CstBdd2BddExpr: Need to unwind the itrVars" ~
	     " before attempting to solve BDD");
    }
    auto bdd = _expr.getBDD(stage, buddy);
    return (~ bdd);
  }

  override CstNotBddExpr unwind(CstVarIterBase itr, uint n) {
    bool shouldUnwind = false;
    foreach(var; itrVars()) {
      if(itr is var) {
	shouldUnwind = true;
	break;
      }
    }
    if(! shouldUnwind) return this;
    else {
      return new CstNotBddExpr(_expr.unwind(itr, n));
    }
  }

  override bool hasUnresolvedIdx() {
    return _expr.hasUnresolvedIdx();
  }

  override uint resolveLap() {
    return _expr.resolveLap();
  }
  override void resolveLap(uint lap) {
    _expr.resolveLap(lap);
  }
}

class CstBlock: CstBddExpr
{
  CstBddExpr[] _exprs;
  bool[] _booleans;

  // CstVarIterBase[] _itrVars;

  override CstVarIterBase[] itrVars() {
    assert(false, "itrVars() is not implemented for CstBlock");
    // return _itrVars;
  }

  override bool hasUnresolvedIdx() {
    assert(false, "hasUnresolvedIdx() is not implemented for CstBlock");
  }
  
  override bool refresh(CstStage stage, Buddy buddy) {
    bool result = false;
    foreach (expr; _exprs) {
      result |= expr.refresh(stage, buddy);
    }
    return result;
  }
  
  
  override string name() {
    string name_ = "";
    foreach(expr; _exprs) {
      name_ ~= " & " ~ expr.name() ~ "\n";
    }
    return name_;
  }

  override CstVarPrim[] preReqs() {
    assert(false);
  }
    
  void _esdl__reset() {
    _exprs.length = 0;
  }

  bool isEmpty() {
    return _exprs.length == 0;
  }
  
  override CstDomain[] getRndDomains() {
    assert(false);
  }

  override CstBlock unwind(CstVarIterBase itr, uint n) {
    assert(false, "Can not unwind a CstBlock");
  }

  override BDD getBDD(CstStage stage, Buddy buddy) {
    assert(false, "getBDD not implemented for CstBlock");
  }

  void opOpAssign(string op)(bool other)
    if(op == "~") {
      _booleans ~= other;
    }

  void opOpAssign(string op)(CstBddExpr other)
    if(op == "~") {
      _exprs ~= other;
    }

  void opOpAssign(string op)(CstVarExpr other)
    if(op == "~") {
      _exprs ~= _esdl__toBdd(other);
    }

  void opOpAssign(string op)(CstBlock other)
    if(op == "~") {
      if(other is null) return;
      foreach(expr; other._exprs) {
	_exprs ~= expr;
      }
      foreach(boolean; other._booleans) {
	_booleans ~= boolean;
      }
    }

  override uint resolveLap() {
    assert(false, "resolveLap not callable for CstBlock");
  }
  override void resolveLap(uint lap) {
    assert(false, "resolveLap not callable for CstBlock");
  }
}

// CstBdd2BddExpr logicOr(CstVarExpr other)
// {
//   return new CstBdd2BddExpr(_esdl__toBdd(this), _esdl__toBdd(other), CstBddOp.LOGICOR);
// }

auto _esdl__logicOr(P, Q)(P p, Q q) {
  CstBddExpr _p;
  CstBddExpr _q;
  static if (is (P == bool)) {
    _p = new CstBddConst(p);
  }
  else static if (is (P: CstVarExpr)) {
    _p = _esdl__toBdd(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstBddConst(q);
  }
  else static if (is (Q: CstVarExpr)) {
    _q = _esdl__toBdd(q);
  }
  else {
    _q = q;
  }
  return _p.logicOr(_q);
}

auto _esdl__logicAnd(P, Q)(P p, Q q) {
  CstBddExpr _p;
  CstBddExpr _q;
  static if(is(P == bool)) {
    _p = new CstBddConst(p);
  }
  else static if (is (P: CstVarExpr)) {
    _p = _esdl__toBdd(p);
  }
  else {
    _p = p;
  }
  static if(is(Q == bool)) {
    _q = new CstBddConst(q);
  }
  else static if (is (Q: CstVarExpr)) {
    _q = _esdl__toBdd(q);
  }
  else {
    _q = q;
  }
  return _p.logicAnd(_q);
}


CstVec2BddExpr _esdl__lth(Q)(CstVarExpr left, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__lth(left, qq);
  }

CstVec2BddExpr _esdl__lth(CstVarExpr p, CstVarExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.LTH);
}

auto _esdl__lth(P, Q)(P p, Q q) {
  static if(is(P: CstVarExpr)) {
    return _esdl__lth(p, q);
  }
  else static if(is(Q: CstVarExpr)) {
    return _esdl__gte(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p < q);
  }
}

CstVec2BddExpr _esdl__lte(Q)(CstVarExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__lte(p, qq);
  }

CstVec2BddExpr _esdl__lte(CstVarExpr p, CstVarExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.LTE);
}

auto _esdl__lte(P, Q)(P p, Q q) {
  static if(is(P: CstVarExpr)) {
    return _esdl__lte(p, q);
  }
  else static if(is(Q: CstVarExpr)) {
    return _esdl__gth(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p <= q);
  }
}

CstVec2BddExpr _esdl__gth(Q)(CstVarExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__gth(p, qq);
  }

CstVec2BddExpr _esdl__gth(CstVarExpr p, CstVarExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.GTH);
}

auto _esdl__gth(P, Q)(P p, Q q) {
  static if(is(P: CstVarExpr)) {
    return _esdl__gth(p, q);
  }
  else static if(is(Q: CstVarExpr)) {
    return _esdl__lte(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p > q);
  }
}

CstVec2BddExpr _esdl__gte(Q)(CstVarExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__gte(p, qq);
  }

CstVec2BddExpr _esdl__gte(CstVarExpr p, CstVarExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.GTE);
}

auto _esdl__gte(P, Q)(P p, Q q) {
  static if(is(P: CstVarExpr)) {
    return _esdl__gte(p, q);
  }
  else static if(is(Q: CstVarExpr)) {
    return _esdl__lth(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p >= q);
  }
}

CstVec2BddExpr _esdl__equ(Q)(CstVarExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__equ(p, qq);
  }

CstVec2BddExpr _esdl__equ(CstVarExpr p, CstVarExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.EQU);
}

auto _esdl__equ(P, Q)(P p, Q q) {
  static if(is(P: CstVarExpr)) {
    return _esdl__equ(p, q);
  }
  else static if(is(Q: CstVarExpr)) {
    return _esdl__equ(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p == q);
  }
}

CstVec2BddExpr _esdl__neq(Q)(CstVarExpr p, Q q)
  if(isBitVector!Q || isIntegral!Q) {
    auto qq = new CstVal!Q(q); // CstVal!Q.allocate(q);
    return _esdl__neq(p, qq);
  }

CstVec2BddExpr _esdl__neq(CstVarExpr p, CstVarExpr q) {
  return new CstVec2BddExpr(p, q, CstBinBddOp.NEQ);
}

auto _esdl__neq(P, Q)(P p, Q q) {
  static if(is(P: CstVarExpr)) {
    return _esdl__neq(p, q);
  }
  else static if(is(Q: CstVarExpr)) {
    return _esdl__neq(q, p);
  }
  else static if((isBitVector!P || isIntegral!P) &&
		 (isBitVector!Q || isIntegral!Q)) {
    return new CstBddConst(p != q);
  }
}
