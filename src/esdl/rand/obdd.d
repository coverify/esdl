// Written in the D programming language.

// Copyright: Coverify Systems Technology 2011 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>
// Credits:   Ported from the Buddy C++ library by Jorn Lind-Nielsen

module esdl.rand.obdd;

import std.stdio;
import std.datetime;
import std.array;
import std.math;
import std.bigint;
import std.container: Array;
import std.algorithm;
import std.string: format;
// import std.conv;
// import core.memory: GC;
import core.stdc.string: memset;

import core.memory: pureMalloc, pureRealloc, pureFree;
alias malloc = pureMalloc;
alias free = pureFree;
alias realloc = pureRealloc;

enum uint BddTrue = 1;		// kernel.c:66
enum uint BddFalse = 0;		// kernel.c: 76

enum BddOp : ubyte {		// bdd.h:50
    AND = 0,
    XOR = 1,
    OR = 2,
    NAND = 3,
    NOR = 4,
    IMP = 5,
    BIIMP = 6,
    DIFF = 7,
    LESS = 8,
    INVIMP = 9,
    // Should *not* be used in bdd_apply calls !!!
    NOT = 10,
    SIMPLIFY = 11
    }

// bdd.h:75
class BddPair
{
  int *result;
  int last;
  int id;
  BddPair next;

  void set(int oldvar, int newvar) {
    getBuddy.bdd_setpair(this, oldvar, newvar);
  }

  // pair.c:161
  void set(int oldvar, BDD newvar) {
    getBuddy.bdd_setbddpair(this, oldvar, newvar._index);
  }

  // pair.c:252
  void set(ref Array!int oldvar, ref Array!int newvar) {
    if(oldvar.length != newvar.length)
      throw new BddException("Sizes of the BDD Arrays do not match");

    for(size_t n = 0; n != oldvar.length; ++n)
      this.set(oldvar[n], newvar[n]);
  }

  void set(int[] oldvar, int[] newvar) {
    if(oldvar.length != newvar.length) {
      throw new BddException("Sizes of the BDD Arrays do not match");
    }

    for(size_t n = 0; n != oldvar.length; ++n)
      this.set(oldvar[n], newvar[n]);
  }

  // void set(int[] oldvar, BDD[] newvar)
  // {
  //   if(oldvar.length != newvar.length)
  //     throw new BddException("Sizes of the BDD Arrays do not match");

  //   for(int n = 0; n != newvar.length; ++n)
  //     this.set(oldvar[n], newvar[n]);
  // }

  void set(BddDomain p1, BddDomain p2) {
    auto ivar1 = p1.get_ivars();
    auto ivar2 = p2.get_ivars();
    this.set(ivar1, ivar2);
  }

  // FIXME -- do not use dynamic arrays.
  
  // void set(BddDomain[] p1, BddDomain[] p2)
  // {
  //   if(p1.length != p2.length)
  //     throw new BddException("SIZE MISMATCH");

  //   for(int n = 0; n < p1.length; n++)
  //     if(p1[n].varNum() != p2[n].varNum())
  // 	throw new BddException("SIZE MISMATCH");

  //   for(int n = 0; n < p1.length; n++)
  //     {
  // 	this.set(p1[n], p2[n]);
  //     }
  // }

  void reset() {
    getBuddy.bdd_resetpair(this);
  }

  // override string toString() {
  //   string sb = "";
  //   sb ~= '{';
  //   bool any = false;
  //   for (int i = 0; i < result.length; ++i) {
  //     if (result[i] != getBuddy.bdd_ithvar(getBuddy._level2Var[i])) {
  // 	if (any) sb ~= ", ";
  // 	any = true;
  // 	BDD b = BDD(result[i], getBuddy());
  // 	sb ~= format("%s = %s", getBuddy._level2Var[i], b);
  //     }
  //   }
  //   sb ~= '}';
  //   return sb;
  // }
}


struct BddDomain // fdd.c:52
{
  /* The name of this _domain. */
  // private string _name;
  /* The index of this _domain. */
  private int _index;

  /* The specified _domains(0...N-1) */
  ulong _realsize;

  /* The number of BDD variables representing the domain */
  uint _binsize;
  
  /* Variable indices for the variable set */
  private int* _ivar;
  /* The BDD variable set.  Actually constructed in extDomain(), etc. */
  private BDD _var;		// FIXBDD

  // void name(string n) {
  //   _name = n;
  // }

  string name() {
    return format("%s", index);
  }

  void index(int i) {
    _index = i;
  }

  int index() {
    return _index;
  }

  void realsize(ulong r) {
    _realsize = r;
  }

  ulong realsize() {
    return _realsize;
  }

  void var(BDD v) {
    _var = v;
  }

  BDD var() {
    return var;
  }


  // this(int index, long range) {
  //   import std.conv;
  //   long calcsize = 2;
  //   if (range <= 0L) {
  //     throw new BddException();
  //   }
  //   this._index = index;
  //   this._realsize = range;
  //   uint binsize = 1;
  //   while(calcsize < range) {
  //     binsize++;
  //     calcsize <<= 1;
  //   }
  //   this._ivar._binsize = binsize;
  // }


  // TODO -- explicit delete
  ~this() {
    // import std.stdio;
    // writeln("Calling destructor on BddDomain with BDD: ", _var._index);
    _var.reset();
  }

  void freeMem() {
    free(_ivar);
    _ivar = null;
  }
   
  
  this(int index, uint bits) {	// fdd.c:1033
    this._index = index;	// not in c version
    this._realsize = (cast(ulong) 2) ^^bits;
    this._binsize = bits;
    this._ivar = cast(int*) malloc(int.sizeof * bits);
    for (size_t i=0; i!=bits; ++i) {
      this._ivar[i] = 0;
    }
    this._var = getBuddy().one();
  }

  void reset() {
    _var.reset();
  }

  // void setName(string name) {
  //   this._name = name;
  // }

  string getName() {
    return name();
  }

  int getIndex() {
    return index;
  }

  BDD domain() {

    /* Encode V<=X-1. V is the variables in 'var' and X is the domain size */
    long val = _realsize - 1;
    BDD d = getBuddy.one();
    auto ivar = get_ivars();
    for (int n = 0; n < this.varNum(); n++) {
      if (val & 1) {		// test LSB
	d = d.or(getBuddy.nithVar(ivar[n]));
      }
      else {
	d = d.and(getBuddy.nithVar(ivar[n]));
      }
      val >>= 1;
    }
    return d;
  }

  // ulong size() {
  //   return cast(ulong) this.realsize;
  // }

  BDD buildAdd(BddDomain that, long value)
  {
    if(this.varNum() != that.varNum())
      throw new BddException();
    return buildAdd(that, this.varNum(), value);
  }

  BDD buildAdd(BddDomain that, int bits, long value)
  {
    if(bits > this.varNum() ||
       bits > that.varNum())
      throw new BddException(format("Number of bits requested(%s) is larger than domain sizes %s, %s",
				    bits, this.varNum(), that.varNum()));

    if(value == 0L)
      {
	BDD result = getBuddy.one();
	int n;
	for(n = 0; n < bits; n++)
	  {
	    BDD b = ithVar(this._ivar[n]);
	    b = b.biimp(ithVar(that._ivar[n]));
	    result = result.and(b);
	  }
	for( ; n < max(this.varNum(), that.varNum()); n++)
	  {
	    BDD b =(n < this.varNum()) ? getBuddy.nithVar(this._ivar[n]) : getBuddy.one();
	    b = b.and((n < that.varNum()) ? getBuddy.nithVar(that._ivar[n]) : getBuddy.one());
	    result = result.and(b);
	  }
	return result;
      }

    auto vars = (this._ivar[0..bits]);
    BddVec y = getBuddy.buildVec(vars);
    BddVec v = getBuddy.buildVec(bits, value);
    BddVec z = y.add(v);

    auto thatvars = (this._ivar[0..bits]);
    BddVec x = getBuddy.buildVec(thatvars);
    BDD result = getBuddy.one();
    int n;
    for (n = 0; n < x.size(); n++) {
	BDD b = x.bitvec[n].biimp(z.bitvec[n]);
	result = result.and(b);
      }
    for ( ; n < max(this.varNum(), that.varNum()); n++) {
      BDD b =(n < this.varNum()) ? getBuddy.nithVar(this._ivar[n]) : getBuddy.one();
      b = b.and((n < that.varNum()) ? getBuddy.nithVar(that._ivar[n]) : getBuddy.one());
      result = result.and(b);
    }
    return result;
  }

  BDD buildEquals(BddDomain that)
  {
    if(this._realsize != that._realsize)
      {
	throw new BddException(format("Size of %s != size of that %s ( %s vs %s",
				      this, that, this._realsize, that._realsize));
      }

    BDD e = getBuddy.one();

    auto this_ivar = this.get_ivars();
    auto that_ivar = that.get_ivars();

    for(int n = 0; n < this.varNum(); n++)
      {
	BDD a = ithVar(this_ivar[n]);
	BDD b = ithVar(that_ivar[n]);
	a = a.biimp(b);
	e = e.and(a);
      }

    return e;
  }

  BDD set()
  {
    return var.dup();
  }

  BDD ithVar(long val)
  {
    if(val < 0 || val > _realsize)
      {
	throw new BddException(format("%s is out of range", val));
      }

    BDD v = getBuddy.one();
    auto ivar = this.get_ivars();
    for(int n = 0; n < ivar.length; n++)
      {
	if(val & 1)
	  v = v.and(ithVar(ivar[n]));
	else
	  v = v.and(getBuddy.nithVar(ivar[n]));
	val >>= 1;
      }

    return v;
  }

  BDD varRange(long lo, long hi)
  {
    if(lo < 0 || hi >= _realsize || lo > hi)
      {
	throw new BddException(format("range < %s, %s > is invalid", lo, hi));
      }

    BDD result = getBuddy.zero();
    auto ivar = this.get_ivars();
    while(lo <= hi)
      {
	BDD v = getBuddy.one();
	for(int n = cast(int) ivar.length - 1; ; n--)
	  {
	    if(lo &(1 << n)) {
	      v = v.and(ithVar(ivar[n]));
	    }
	    else {
	      v = v.and(getBuddy.nithVar(ivar[n]));
	    }
	    long mask =((cast(long) 1) << n) - 1;
	    if(((lo &(1 << n)) == 0) &&
	       (lo | mask) <= hi)
	      {
		lo =(lo | mask) + 1;
		break;
	      }
	  }
	result = result.or(v);
      }
    return result;
  }

  int varNum() {
    return _binsize;
  }

  int[] get_ivars() {
    return this._ivar[0.._binsize];
  }

  // int ensureCapacity(ulong range)
  // {
  //   ulong calcsize = 2L;

  //   if (range < 0) throw new BddException();
  //   if (range < realsize) return _binsize;

  //   this._realsize = range + 1;
  //   uint binsize = 1;

  //   while (calcsize <= range)
  //     {
  // 	binsize++;
  // 	calcsize = calcsize << 1;
  //     }
  //   if (_binsize == binsize) return binsize;

  //   // int[] new_ivar = new int[binsize];
  //   int[] new_ivar = _ivar.dup;
  //   new_ivar.length = binsize;
  //   for(size_t i = _ivar.length; i < new_ivar.length; ++i)
  //     {
  // 	int newVar = getBuddy.duplicateVar(new_ivar[i-1]);
  // 	getBuddy.incr_firstbddvar();
  // 	new_ivar[i] = newVar;
  //     }
  //   this._ivar = new_ivar;
  //   BDD nvar = getBuddy.one();
  //   for(int i = 0; i < _ivar.length; ++i)
  //     {
  // 	nvar = nvar.and(ithVar(_ivar[i]));
  //     }
  //   this.var = nvar;
  //   return binsize;
  // }

  string toString()
  {
    return getName();
  }

  /**
   * Convert a bdd that to a list of indices of this domain.
   * This method assumes that the bdd passed is a disjunction
   * of ithVar(i_1) to ithVar(i_k).  It returns an array
   * of length 'k' with elements [i_1,...,i_k].
   * <p>
   * Be careful when using this method for BDDs with a large number
   * of entries, as it allocates a long[] array of dimension k.
   *
   * @param bdd bdd that is the disjunction of domain indices
   * @see #getVarIndices(bdd,int)
   * @see #ithVar(long)
   */
  // long[] getVarIndices(BDD bdd)
  // {
  //   return getVarIndices(bdd, -1);
  // }

  /**
   * Convert a bdd that to a list of indices of this domain.
   * Same as getVarIndices(bdd), except only 'max' indices
   * are extracted.
   *
   * @param bdd bdd that is the disjunction of domain indices
   * @param max maximum number of entries to be returned
   *
   * @see #ithVar(long)
   */

  // Uses Iterator -- not yet implemented in D
  // long[] getVarIndices(BDD bdd, int max)
  // {
  //   BDD myvarset = set(); // can't use var here, must respect
  // // subclass a factory may provide
  //   int n =(int)bdd.satCount(myvarset);
  //   if(max != -1 && n > max)
  //     n = max;
  //   long[] res = new long[](n);

  //   Iterator it = bdd.iterator(myvarset);
  //   for(int i = 0; i < n; i++)
  // {
  //     BDD bi =(bdd) it.next();
  //     res[i] = bi.scanVar(this);
  //   }
  //   return res;
  // }

}



struct BddVec
{

  import esdl.data.bvec: isBitVector;
  
  private Array!BDD _bitvec;
  
  private bool _signed = false;

  bool isNull() {
    return (_bitvec.length == 0);
  }

  bool signed()
  {
    return _signed;
  }

  auto bitvec()
  {
    return _bitvec;
  }
    

  @property size_t length()
  {
    return _bitvec.length;
  }

  @property size_t size()
  {
    return length;
  }

  protected this(size_t bitnum, bool signed = false)
  {
    _signed = signed;
    _bitvec.length = bitnum;

    // _bitvec = cast(BDD*) GC.malloc(bitnum * BDD.sizeof);
    // _length = bitnum;
    // BDD.disable_delref();
    // for (size_t i=0; i!=_length; ++i) {
    // 	_bitvec[i] = BDD.init;
    // }
    // BDD.enable_delref();
  }

  // ~this() {
  //   foreach (bdd; _bitvec) {
  //   	bdd.reset();
  //   }
  //   for (size_t i=0; i!=_bitvec.length; ++i) {
  //	auto bdd = _bitvec[i];
  //	bdd.reset();
  //   }
  // }


  void buildVec(T)(T val)
  {
    buildVec(getBuddy(), val);
  }

  void buildVec(T)(Buddy buddy, T val)
  {
    import std.traits;
    
    static if(isBitVector!T) {
      _bitvec.length = T.SIZE;
      _signed = T.ISSIGNED;
    }
    else static if(isIntegral!T) {
      _bitvec.length = T.sizeof * 8;
      _signed = isSigned!T;
    }
    else static if(is(T == bool)) {
      _bitvec.length = 1;
      _signed = false;
    }
    initialize(buddy, val);
  }

  void buildVec(uint di, bool signed = false) {
    auto d = getBuddy()._domains[di];
    _signed = signed;
    _bitvec.length = d.varNum();
    initialize(getBuddy(), d);
  }

  void buildVec(BddDomain d, bool signed = false) {
    _signed = signed;
    _bitvec.length = d.varNum();
    initialize(getBuddy(), d);
  }

  void initialize(bool isTrue) {
    initialize(getBuddy(), isTrue);
  }

  void initialize(T)(T val) if (isBitVector!T) {
    initialize(getBuddy(), val);
  }

  void initialize(T)(Buddy buddy, T val) if (isBitVector!T) {
    for (size_t i=0; i!=length; ++i) {
      if(val[i]) {
	_bitvec[i] = one(buddy);
      }
      else {
	_bitvec[i] = zero(buddy);
      }
    }
  }
  
  void initialize(Buddy buddy, bool isTrue) {
    for (size_t i=0; i!=length; ++i) {
      if(isTrue) _bitvec[i] = one(buddy);
      else _bitvec[i] = zero(buddy);
    }
  }


  void initialize(int val) {
    initialize(getBuddy(), val);
  }

  void initialize(Buddy buddy, int val) {
    for (size_t i=0; i!=length; ++i) {
      if((val & 0x1) != 0) _bitvec[i] = one(buddy);
      else _bitvec[i] = zero(buddy);
      val >>= 1;
    }
  }
  
  void initialize(long val) {
    initialize(getBuddy(), val);
  }

  void initialize(Buddy buddy, long val) {
    for (size_t i=0; i!=length; ++i) {
      if((val & 0x1) != 0) _bitvec[i] = one(buddy);
      else _bitvec[i] = zero(buddy);
      val >>= 1;
    }
  }


  void initialize(uint offset, uint step) {
    initialize(getBuddy(), offset, step);
  }

  void initialize(Buddy buddy, uint offset, uint step) {
    for(int n=0 ; n < size ; n++) {
      this.bitvec[n] = buddy.ithVar(offset+n*step);
    }
  }

  void initialize(BddDomain d) {
    initialize(d.get_ivars());
  }

  void initialize(Buddy buddy, BddDomain d) {
    initialize(buddy, d.get_ivars());
  }

  void initialize(int[] var) {
    for (int n = 0 ; n < size ; n++) {
      this.bitvec[n] = getBuddy.ithVar(var[n]);
    }
  }

  void initialize(ref Array!int var) {
    for(int n = 0 ; n < size ; n++) {
      this.bitvec[n] = getBuddy.ithVar(var[n]);
    }
  }

  void initialize(Buddy buddy, int[] var) {
    for(int n = 0 ; n < size ; n++) {
      this.bitvec[n] = buddy.ithVar(var[n]);
    }
  }

  void initialize(Buddy buddy, ref Array!int var) {
    for(int n = 0 ; n < size ; n++) {
      this.bitvec[n] = buddy.ithVar(var[n]);
    }
  }

  BddVec dup() {
    return this.copy();
  }

  BddVec copy() {
    BddVec dst = BddVec(size, false);
    dst._signed = this._signed;
    // dst.bitvec[0..$] = this.bitvec[0..$];
    for (int n = 0; n < size; n++) {
      dst.bitvec[n] = this.bitvec[n].dup();
    }
    return dst;
  }

  final BddVec opUnary(string op)()
    if (op == "+" || op == "-" || op == "~") {
      static if(op == "+") {
	return this;
      }
      static if (op == "-") {
	return this.opNeg();
      }
      static if (op == "~") {
	return this.opCom();
      }
    }

  final BddVec opBinary(string op)(long rhs)
    if(op == "<<" || op == ">>" || op == "*" || op == "/" || op == "%")
      {
	static if(op == "<<")
	  {
	    return this.shl(cast(int) rhs, zero());
	  }
	static if(op == ">>")
	  {
	    return this.shr(cast(int) rhs, zero());
	  }
	static if(op == "*")
	  {
	    return this.mul(rhs);
	  }
	static if(op == "/")
	  {
	    return this.div(rhs);
	  }
	static if(op == "%")
	  {
	    return this.rem(rhs);
	  }
      }

  final BddVec opBinaryRight(string op)(long rhs)
    if(op == "*")
      {
	static if(op == "*")
	  {
	    return this.mul(rhs);
	  }
      }

  final BddVec opBinary(string op)(BddVec rhs)
    if(op == "&" || op == "|" || op == "^" ||
       op == "<<" || op == ">>" || op == "+" ||
       op == "-" || op == "*"  || op == "/" ||
       op == "%")
      {
	static if(op == "&")
	  {
	    return this.apply(rhs, BddOp.AND);
	  }
	static if(op == "^")
	  {
	    return this.apply(rhs, BddOp.XOR);
	  }
	static if(op == "|")
	  {
	    return this.apply(rhs, BddOp.OR);
	  }
	static if(op == "<<")
	  {
	    return this.shl(rhs, zero());
	  }
	static if(op == ">>")
	  {
	    return this.shr(rhs, zero());
	  }
	static if(op == "+")
	  {
	    return this.add(rhs);
	  }
	static if(op == "-")
	  {
	    return this.sub(rhs);
	  }
	static if(op == "*")
	  {
	    return this.mul(rhs);
	  }
	static if(op == "/")
	  {
	    return this.div(rhs);
	  }
	static if(op == "%")
	  {
	    return this.rem(rhs);
	  }
      }
  final BDD opBinary(string op)(BddVec rhs)
    if((op == "<") ||(op == "<=") ||(op == ">") ||
       (op == ">=") ||(op == "==") ||(op == "!="))
      {
	static if(op == "<")
	  {
	    return this.lth(rhs);
	  }
	static if(op == "<=")
	  {
	    return this.lte(rhs);
	  }
	static if(op == ">")
	  {
	    return this.gth(rhs);
	  }
	static if(op == ">=")
	  {
	    return this.gte(rhs);
	  }
	static if(op == "==")
	  {
	    return this.equ(rhs);
	  }
	static if(op == "!=")
	  {
	    return this.neq(rhs);
	  }
      }

  size_t opDollar() {
    return length;
  }
  
  BddVec coerceSign()
  {
    if(signed) return copy();
    else
      {
	BddVec dst = BddVec(size+1, true);
	// dst.bitvec[0..$-1] = this.bitvec[0..$];
	for(int n = 0; n < size; n++) {
	  dst.bitvec[n] = this.bitvec[n].dup();
	}
	dst.bitvec[dst.size-1] = zero();
	return dst;
      }
  }

  BddVec coerce(size_t bitnum)
  {
    BddVec dst = BddVec(bitnum, this._signed);
    ulong minnum = min(bitnum, size);
    uint n;
    for(n = 0; n < minnum; n++)
      dst.bitvec[n] = this.bitvec[n].dup();
    for(uint m = n; m < bitnum; m++)
      if(this._signed == false)
	dst.bitvec[m] = zero();
      else			// extend sign
	dst.bitvec[m] = this.bitvec[n-1].dup();
    return dst;
  }

  bool isConst()
  {
    for (size_t i=0; i!=size; ++i)
      {
	if(!_bitvec[i].isOne() && !_bitvec[i].isZero()) return false;
      }
    return true;
  }

  long val()
  {
    long val = 0;

    for(size_t n = size - 1; n >= 0; n--)
      if(this.bitvec[n].isOne())
	val =(val << 1) | 1;
      else if(this.bitvec[n].isZero())
	val = val << 1;
      else
	return 0;
    return val;
  }

  void reset() {
    // size = 0;
    foreach(ref bdd; _bitvec) {
      bdd.reset();
    }
    _bitvec.clear();
  }

  // bvec addref(bvec v)
  // {
  //   foreach(ref b; _bitvec) b.addref();
  //   return v;
  // }

  // bvec delref(bvec v)
  // {
  //   foreach(ref b; _bitvec) b.delref();
  //   return v;
  // }

  BddVec apply(BddVec that, BddOp op)
  {
    size_t maxsize = max(size, that.size);
    size_t minsize = min(size, that.size);
    // if(size != that.size)
    // 	// throw new BddException();
    // 	bdd_error(BddError.BVEC_SIZE);

    BddVec res = BddVec(maxsize, _signed);
    for(size_t n=0 ; n < minsize ; n++)
      res.bitvec[n] = this.bitvec[n].apply(that.bitvec[n], op);

    for(size_t n=minsize ; n < size ; n++)
      res.bitvec[n] = this.bitvec[n].apply(zero(), op);

    for(size_t n=minsize ; n < that.size ; n++)
      res.bitvec[n] = zero.apply(that.bitvec[n], op);

    return res;
  }

  BddVec opCom()
  {
    BddVec res = BddVec(size, false);
    for(int n=0 ; n < size ; n++)
      res.bitvec[n] = this.bitvec[n].not();
    return res;
  }

  BddVec opNeg()
  {
    BddVec lhs = BddVec(size, false);
    return lhs.sub(this);
  }

  BddVec add(BddVec that)
  {

    // if(size != b.size)
    // 	// throw new BddException();
    // 	bdd_error(BddError.BVEC_SIZE);
    BddVec a = this.coerceSign();
    BddVec b = that.coerceSign();

    size_t minsize = min(a.size, b.size);
    size_t maxsize = max(a.size, b.size);

    BDD c = zero();
    BddVec res = BddVec(maxsize+1, false);
    res._signed = true;

    for(size_t n = 0; n < minsize; n++)
      {
	/* this[n] = l[n] ^ r[n] ^ c; */
	res.bitvec[n] = a.bitvec[n] ^ b.bitvec[n];
	res.bitvec[n] = res.bitvec[n] ^ c.dup();

	/* c =(l[n] & r[n]) |(c &(l[n] | r[n])); */
	BDD c1 = a.bitvec[n] | b.bitvec[n];
	c1 = c1 & c;
	BDD c2 = a.bitvec[n] & b.bitvec[n];
	c2 = c2 | c1;
	c = c2;
      }

    // a.size > b.size
    for(size_t n = minsize; n < a.size; n++)
      {
	// sign extend
	BDD ext = b.signed ? b.bitvec[b.size-1] : zero();

	/* this[n] = l[n] ^ r[n] ^ c; */
	res.bitvec[n] = a.bitvec[n] ^ ext;
	res.bitvec[n] = res.bitvec[n] ^ c.dup();

	/* c =(l[n] & r[n]) |(c &(l[n] | r[n])); */
	BDD c1 = a.bitvec[n] | ext;
	c1 = c1 & c;
	BDD c2 = a.bitvec[n] & ext;
	c2 = c2 | c1;
	c = c2;
      }

    // b.size > a.size
    for(size_t n = minsize; n < b.size; n++)
      {
	// sign extend
	BDD ext = a.signed ? a.bitvec[a.size-1] : zero();

	/* this[n] = l[n] ^ r[n] ^ c; */
	res.bitvec[n] = ext ^ b.bitvec[n];
	res.bitvec[n] = res.bitvec[n] ^ c.dup();

	/* c =(l[n] & r[n]) |(c &(l[n] | r[n])); */
	BDD c1 = ext | b.bitvec[n];
	c1 = c1 & c;
	BDD c2 = ext & b.bitvec[n];
	c2 = c2 | c1;
	c = c2;
      }

    if(a.signed)
      {
	c = a.bitvec[a.size-1].ite(c.not(), c);
      }
    if(b.signed)
      {
	c = b.bitvec[b.size-1].ite(c.not(), c);
      }
    res.bitvec[res.size-1] = c;

    // if(a.signed && b.signed)
    // 	{
    // 	  // extend sign
    // 	  res[$-1] = res[$-2].dup();
    // 	}

    // if(!a.signed && !b.signed)
    // 	{
    // 	  // unsigned 0 extend
    // 	  res[$-1] = zero();
    // 	}

    // if(a.signed && !b.signed)
    // 	{
    // 	  // if the signed number negative and the result is negative
    // 	  res[$-1] = a[$-1] & res[$-2];
    // 	}

    // if(!a.signed && b.signed)
    // 	{
    // 	  // if the signed number negative and the result is negative
    // 	  res[$-1] = b[$-1] & res[$-2];
    // 	}

    return res;
  }

  // required for division and remainder operation with rhs of type long
  BddVec sub_samesize(BddVec that)
  {

    BDD c = zero();
    BddVec res = BddVec(size, false);

   if (size != that.size)
   {
     bdd_error(BddError.BVEC_SIZE);
   }
   
    for(int n = 0; n < size; n++)
      {
	/* this[n] = l[n] ^ r[n] ^ c; */
	res.bitvec[n] = this.bitvec[n] ^ that.bitvec[n];
	res.bitvec[n] = res.bitvec[n] ^ c.dup();

	/* c =(l[n] & r[n] & c) |(!l[n] &(r[n] | c)); */
	BDD tmp1 = that.bitvec[n] | c;
	BDD tmp2 = this.bitvec[n].lth(tmp1);
	tmp1 = this.bitvec[n] & that.bitvec[n];
	tmp1 = tmp1 & c;
	tmp1 = tmp1 | tmp2;
	c = tmp1;
      }
    return res;
  }

  BddVec sub(BddVec that)
  {

    size_t minsize = min(size, that.size);
    size_t maxsize = max(size, that.size);

    BDD c = zero();
    BddVec res = BddVec(maxsize+1, false);

    for(int n = 0; n < minsize; n++)
      {
	/* this[n] = l[n] ^ r[n] ^ c; */
	res.bitvec[n] = this.bitvec[n] ^ that.bitvec[n];
	res.bitvec[n] = res.bitvec[n] ^ c.dup();

	/* c =(l[n] & r[n] & c) |(!l[n] &(r[n] | c)); */
	BDD tmp1 = that.bitvec[n] | c;
	BDD tmp2 = this.bitvec[n].lth(tmp1);
	tmp1 = this.bitvec[n] & that.bitvec[n];
	tmp1 = tmp1 & c;
	tmp1 = tmp1 | tmp2;
	c = tmp1;
      }

    // this.size > that.size
    for(size_t n = minsize; n < size; n++)
      {
	// sign extend
	BDD ext = that.signed ? that.bitvec[that.size-1] : zero();
	/* this[n] = l[n] ^ r[n] ^ c; */
	res.bitvec[n] = this.bitvec[n] ^ ext;
	res.bitvec[n] = res.bitvec[n] ^ c.dup();

	/* c =(l[n] & r[n] & c) |(!l[n] &(r[n] | c)); */
	BDD tmp1 = ext | c;
	BDD tmp2 = this.bitvec[n].lth(tmp1);
	tmp1 = this.bitvec[n] & ext;
	tmp1 = tmp1 & c;
	tmp1 = tmp1 | tmp2;
	c = tmp1;
      }
    // that.size > this.size
    for(size_t n = minsize; n < that.size; n++)
      {
	// sign extend
	BDD ext = signed ? this.bitvec[this.size-1] : zero();
	/* this[n] = l[n] ^ r[n] ^ c; */
	res.bitvec[n] = ext ^ that.bitvec[n];
	res.bitvec[n] = res.bitvec[n] ^ c.dup();

	/* c =(l[n] & r[n] & c) |(!l[n] &(r[n] | c)); */
	BDD tmp1 = that.bitvec[n] | c;
	BDD tmp2 = ext.lth(tmp1);
	tmp1 = ext & that.bitvec[n];
	tmp1 = tmp1 & c;
	tmp1 = tmp1 | tmp2;
	c = tmp1;
      }
    res.bitvec[res.size-1] = c;
    return res;
  }

  BddVec mul(long c)
  {
    BddVec next = getBuddy.buildVec(size, false);
    if(c == 0) return next;	// base case

    for(size_t n=1 ; n < size ; n++)
      next.bitvec[n] = this.bitvec[n-1];

    BddVec rest = next.mul(c >> 1);

    BddVec result;
    if(c & 0x1)
      {
	result = this.add(rest);
      } else {
      result = rest;
    }

    return result;

  }

  BddVec mul(BddVec rhs)
  {
    size_t bitnum = size + rhs.size;
    BddVec result = getBuddy.buildVec(bitnum, false);
    BddVec leftshifttmp = this.dup();

    BddVec leftshift = leftshifttmp.coerce(bitnum);

    for (size_t i=0; i!=rhs.size; ++i)
      {
	BddVec added = result.add(leftshift);
	for(size_t m=0; m < bitnum; ++m)
	  {
	    BDD tmpres = rhs.bitvec[i].ite(added.bitvec[m], result.bitvec[m]);
	    result.bitvec[m] = tmpres;
	  }
	for(size_t m = bitnum-1; m >= 1; --m)
	  {
	    leftshift.bitvec[m] = leftshift.bitvec[m-1];
	  }
	leftshift.bitvec[0] = zero();
      }
    return result;
  }

  void div_rec(BddVec divisor, ref BddVec remainder,
		      ref BddVec result, long step)
  {
    BDD isSmaller = divisor.lte(remainder);
    BddVec newResult = result.shl(1, isSmaller);
    BddVec zero = getBuddy.buildVec(divisor.size, false);
    BddVec sub = getBuddy.buildVec(divisor.size, false);

    for(size_t n = 0; n < divisor.size; n++)
      sub.bitvec[n] = isSmaller.ite(divisor.bitvec[n], zero.bitvec[n]);

    BddVec tmp = remainder.sub_samesize(sub);
    BddVec newRemainder =
      tmp.shl(1, result.bitvec[divisor.size - 1]);
    if(step > 1)
      div_rec(divisor, newRemainder, newResult, step - 1);

    result.replaceWith(newResult);
    remainder.replaceWith(newRemainder);
  }

  void replaceWith(BddVec that)
  {
    if(size != that.size) {
      // throw new BddException();
      bdd_error(BddError.BVEC_SIZE);
    }
    reset();
    this._bitvec = that.bitvec;
  }


  int div(ulong c, ref BddVec res, ref BddVec rem)
  {
    if(c > 0)
      {
	BddVec divisor = getBuddy.buildVec(size, c);
	BddVec tmp = getBuddy.buildVec(size, false);
	BddVec tmpremainder = tmp.shl(1, this.bitvec[size-1]);
	BddVec result = this.shl(1, zero());
	BddVec remainder;

	div_rec(divisor, tmpremainder, result, divisor.size);
	remainder = tmpremainder.shr(1, zero());

	res = result;
	rem = remainder;

	return 0;
      }
    else {
      throw new BddException("Bit Vector divide by 0");
    }
  }

  BddVec rem(BddVec rhs) {
    BddVec result = BddVec(size, _signed);
    BddVec remainder = BddVec(size, _signed);
    div(rhs, result, remainder);
    return remainder;
  }

  BddVec rem(ulong rhs) {
    BddVec result = BddVec(size, _signed);
    BddVec remainder = BddVec(size, _signed);
    div(rhs, result, remainder);
    return remainder;
  }

  BddVec div(BddVec rhs) {
    BddVec result = BddVec(size, _signed);
    BddVec remainder = BddVec(size, _signed);
    div(rhs, result, remainder);
    return result;
  }

  BddVec div(ulong rhs) {
    BddVec result = BddVec(size, _signed);
    BddVec remainder = BddVec(size, _signed);
    div(rhs, result, remainder);
    return result;
  }

  int div(BddVec rhs, ref BddVec result, ref BddVec remainder)
  {

    size_t bitnum = size + rhs.size;
    if(size != rhs.size)
      // throw new BddException("Bit Vector sizes do not match");
      bdd_error(BddError.BVEC_SIZE);

    BddVec rem = this.coerce(bitnum);
    BddVec divtmp = rhs.coerce(bitnum);

    BddVec div = divtmp.shl(size, zero());

    BddVec res = getBuddy.buildVec(rhs.size, false);

    for(size_t n = 0; n < rhs.size + 1; ++n)
      {
	BDD divLteRem = div.lte(rem);
	BddVec remSubDiv = rem.sub(div);

	for(size_t m = 0; m < bitnum; ++m)
	  {
	    BDD remtmp = divLteRem.ite(remSubDiv.bitvec[m], rem.bitvec[m]);
	    rem.bitvec[m] = remtmp;
	  }

	if(n > 0)
	  res.bitvec[rhs.size - n] = divLteRem;

	/* Shift 'div' one bit right */
	for(size_t m = 0 ; m < bitnum-1 ; ++m)
	  div.bitvec[m] = div.bitvec[m+1];
	div.bitvec[bitnum-1] = zero();
      }


    result = res;
    remainder = rem.coerce(rhs.size);
    return 0;
  }

  BDD zero(Buddy buddy) {
    return buddy.zero();
  }

  BDD zero() {
    return getBuddy.zero();
  }

  BDD one(Buddy buddy) {
    return buddy.one();
  }

  BDD one() {
    return getBuddy.one();
  }

  BddVec shl(ptrdiff_t pos, BDD c)
  {
    size_t minnum = min(this.size, pos);
    if(pos < 0)
      throw new BddException();

    BddVec res = getBuddy.buildVec(size, false);

    size_t n;
    for(n = 0; n != size; ++n) {
      if (n < minnum) {
	res.bitvec[n] = c;
      }
      else {
	res.bitvec[n] = this.bitvec[n-pos];
      }
    }
    return res;
  }

  BddVec shl(BddVec r, BDD c)
  {
    BddVec val;
    BDD tmp1, tmp2, rEquN;

    BddVec res = getBuddy.buildVec(this.size, false);

    for(size_t n = 0 ; n <= this.size ; ++n)
      {
	val = getBuddy.buildVec(r.size, n);
	rEquN = r.equ(val);

	for(size_t m = 0 ; m < this.size ; ++m)
	  {
	    /* Set the m'th new location to be the(m-n)'th old location */
	    if(m  >= n) {
	      tmp1 = rEquN.and(this.bitvec[m-n]);
	    }
	    else
	      tmp1 = rEquN.and(c);
	    tmp2 = res.bitvec[m].or(tmp1);

	    res.bitvec[m] = tmp2;
	  }

      }

    /* At last make sure 'c' is shiftet in for r-values > l-size */
    val = getBuddy.buildVec(r.size, this.size);
    rEquN = r.gth(val);
    tmp1 = rEquN.and(c);

    for(size_t m = 0; m < this.size; ++m)
      {
	tmp2 = res.bitvec[m].or(tmp1);

	res.bitvec[m] = tmp2;
      }

    return res;
  }


  BddVec shr(ptrdiff_t pos, BDD c)
  {
    size_t maxnum = max(0, size - pos);
    if(pos < 0)
      throw new BddException();

    BddVec res = getBuddy.buildVec(size, false);

    for(size_t n=maxnum; n < size; ++n)
      res.bitvec[n] = c;

    for(size_t n = 0; n < maxnum; ++n)
      res.bitvec[n] = this.bitvec[n+pos];

    return res;
  }

  BddVec shr(BddVec r, BDD c)
  {
    BddVec val;
    BDD tmp1, tmp2, rEquN;

    BddVec res = getBuddy.buildVec(this.size, false);

    for(size_t n = 0 ; n <= this.size ; ++n)
      {
	val = getBuddy.buildVec(r.size, n);
	rEquN = r.equ(val);

	for(size_t m = 0 ; m < this.size ; m++)
	  {
	    /* Set the m'th new location to be the(m+n)'th old location */
	    if(m+n <= 2)
	      tmp1 = rEquN.and(this.bitvec[m+n]);
	    else
	      tmp1 = rEquN.and(c);
	    tmp2 = res.bitvec[m].or(tmp1);
	    res.bitvec[m] = tmp2;
	  }

      }

    /* At last make sure 'c' is shiftet in for r-values > l-size */
    val = getBuddy.buildVec(r.size, this.size);
    rEquN = r.gth(val);
    tmp1 = rEquN.and(c);

    for(size_t m = 0; m < this.size; ++m)
      {
	tmp2 = res.bitvec[m].or(tmp1);
	res.bitvec[m] = tmp2;
      }

    return res;
  }

  BDD lth(BddVec r)
  {
    return less(r, false);
  }

  BDD lte(BddVec r)
  {
    return less(r, true);
  }

  BDD less(BddVec that, bool equalP)
  {
    BDD p = equalP ? one() : zero();

    if(this.size == 0  ||  that.size == 0)
      return zero;

    // if(this.size != that.size)
    // 	// throw new BddException("Size Mismatch!");
    // 	bdd_error(BddError.BVEC_SIZE);

    BddVec a = this.coerceSign();
    BddVec b = that.coerceSign();

    size_t minsize = min(a.size, b.size);
    size_t maxsize = max(a.size, b.size);

    for(size_t n=0; n < minsize; ++n)
      {
	/* p =(!l[n] & that[n]) |
	 *     bdd_apply(l[n], that[n], bddop_biimp) & p; */

	BDD tmp1 = a.bitvec[n].lth(b.bitvec[n]);
	BDD tmp2 = a.bitvec[n].biimp(b.bitvec[n]);
	BDD tmp3 = tmp2 & p;
	BDD tmp4 = tmp1 | tmp3;
	p = tmp4;
      }

    // a.size > b.size
    for(size_t n=minsize; n < a.size; ++n)
      {
	// sign extend
	BDD ext = b.signed ? b.bitvec[b.size-1] : zero();

	/* p =(!l[n] & that[n]) |
	 *     bdd_apply(l[n], that[n], bddop_biimp) & p; */

	BDD tmp1 = a.bitvec[n].lth(ext);
	BDD tmp2 = a.bitvec[n].biimp(ext);
	BDD tmp3 = tmp2 & p;
	BDD tmp4 = tmp1 | tmp3;
	p = tmp4;
      }

    // b.size > a.size
    for(size_t n=minsize; n < b.size; ++n)
      {
	// sign extend
	BDD ext = a.signed ? a.bitvec[a.size-1] : zero();
	/* p =(!l[n] & that[n]) |
	 *     bdd_apply(l[n], that[n], bddop_biimp) & p; */

	BDD tmp1 = ext.lth(b.bitvec[n]);
	BDD tmp2 = ext.biimp(b.bitvec[n]);
	BDD tmp3 = tmp2 & p;
	BDD tmp4 = tmp1 | tmp3;
	p = tmp4;
      }

    p = (a.bitvec[a.size-1] & (b.bitvec[b.size-1].not())).ite(one(), p);
    p = ((a.bitvec[a.size-1].not()) & b.bitvec[b.size-1]).ite(zero(), p);
    // if both this and that are either signed or unsigned, what we
    // have done till now is sufficient

    // If this is signed and that is not signed
    // if(a.signed & !(b.signed))
    // 	{
    // 	  p = a[$-1].ite(zero(), p);
    // 	}

    // If that is signed and this is not signed
    // if(b.signed & !(a.signed))
    // 	{
    // 	  p = b[$-1].ite(one(), p);
    // 	}

    return p;
  }

  BDD equ(BddVec r)
  {
    BDD p = one;

    if(this.size == 0  ||  r.size == 0)
      return zero;

    // if(this.size != r.size)
    // 	// throw new BddException("Size Mismatch!");
    // 	bdd_error(BddError.BVEC_SIZE);

    size_t minsize = min(size, r.size);
    size_t maxsize = max(size, r.size);

    for(size_t n=0; n < minsize; ++n)
      {
	p = p & this.bitvec[n].biimp(r.bitvec[n]);
      }

    // this.size > r.size
    for(size_t n=minsize; n < size; ++n)
      {
	// sign extend
	BDD ext = r.signed ? r.bitvec[r.size-1] : zero();
	p = p & this.bitvec[n].biimp(ext);
      }

    // this.size > r.size
    for(size_t n=minsize; n < r.size; ++n)
      {
	// sign extend
	BDD ext = signed ? this.bitvec[size-1] : zero();
	p = p & ext.biimp(r.bitvec[n]);
      }
    return p;
  }

  BDD gth(BddVec r)
  {
    BDD tmp = this.lte(r);
    BDD p = tmp.not();
    return p;
  }

  BDD gte(BddVec r)
  {
    BDD tmp = this.lth(r);
    BDD p = tmp.not();
    return p;
  }

  BDD neq(BddVec r)
  {
    BDD tmp = this.equ(r);
    BDD p = tmp.not();
    return p;
  }

  BddVec divmod(long c, bool which)
  {
    if(c <= 0L)
      throw new BddException();
    BddVec divisor = getBuddy.buildVec(cast(int) size, c);
    BddVec tmp = getBuddy.buildVec(cast(int) size, false);
    BddVec tmpremainder = tmp.shl(1, this.bitvec[size-1]);
    BddVec result = this.shl(1, zero());

    BddVec remainder;

    div_rec(divisor, tmpremainder, result, cast(int) divisor.size);
    remainder = tmpremainder.shr(1, zero());

    if(which)
      {
	return result;
      } else {
      return remainder;
    }
  }

  BddVec opSlice(size_t n, size_t m) {
    if(n >= m) throw new BddException();
    if(n >= size) throw new BddException();
    if(m > size) throw new BddException();
    BddVec res = getBuddy.buildVec(cast (int) (m - n), false);
    for(size_t i = 0; i < m - n; ++i) {
      res.bitvec[i] = this.bitvec[n+i];
    }
    return res;
  }

  BDD opIndex(size_t i) {
    if(i >= size) throw new BddException();
    return bitvec[i];
  }
}


version(BUDDY_ROOT) {
   void useBuddy(Buddy buddy) {}
   void exitBuddy() {}
 }
 else {
   void useBuddy(Buddy buddy) {
     BDD._buddy = buddy;
   }
   void exitBuddy() {
     BDD._buddy = null;
   }
   Buddy getBuddy() {
     assert(BDD._buddy !is null);
     return BDD._buddy;
   }
 }

struct BDD
{
  uint _index;

  alias _index this;

  version(BUDDY_ROOT) {
    Buddy _buddy;
    const bool opEquals(ref const BDD other) {
      return (this._index == other._index &&
	      this._buddy is other._buddy);
    }
  }
  else {
    static Buddy _buddy;
    const bool opEquals(ref const BDD other) {
      return (this._index == other._index);
    }
  }

  size_t toHash() const nothrow @safe {
    return _index;
  }

  @property Buddy buddy()
  {
    return _buddy;
  }

  void delRef() {
    if (_index !is 0 &&
	_buddy !is null) {
      _buddy.delRef(_index);
    }
    _index = 0;		// destructor might still get called
  }
  
  void reset() {
    // call this from the destructor of BddVec/BddDomain
    // when buddy is getting GCed, the BDDs that are members of the
    // various BddVec and BddDomain instances need not be delRef'ed
    // also delRef requires a buddy instance that will not be
    // available at the time GC kicks in -- buddy instance being
    // thread local (static). GC runs on a different thread
    debug(BUDDY) writeln("Reset called for ", _index);
    _index = 0;
  }

  // TODO -- explicit delete
  ~this()
  {
    if (_index !is 0 &&
    	_buddy !is null) {
      _buddy.delRef(_index);
    }
  }

  version(BUDDY_ROOT) {
    this(int index, Buddy buddy)
      {
	// writeln(count++);
	this._index = index;
	this._buddy = buddy;
	_buddy.addRef(_index);
      }
  }
  else {
    this(int index, Buddy buddy)
      {
	// writeln(count++);
	assert(_buddy is buddy);
	this._index = index;
	_buddy.addRef(_index);
      }
  }
  this(this)
  {
    if(_index != 0 && _buddy !is null) {
      _buddy.addRef(_index);
    }
  }
    
  void opAssign(BDD that) {
    if (_buddy !is null && _index !is 0) {
      _buddy.delRef(_index);
    }
    this._buddy = that._buddy;
    this._index = that._index;
    _buddy.addRef(_index);
  }

  BDD makeBdd(int index)
  {
    return BDD(index, this._buddy);
  }

  bool isZero()
  {
    return _index == BddFalse;
  }

  bool isOne()
  {
    return _index == BddTrue;
  }

  int var()
  {
    return buddy.bdd_var(_index);
  }

  int level()
  {
    return buddy.var2Level(this.var);
  }

  BDD high()
  {
    return makeBdd(buddy.HIGH(_index));
  }

  BDD low()
  {
    return makeBdd(buddy.LOW(_index));
  }

  // BDD id()
  // {
  //   return BDD(_index);
  // }

  BDD dup()
  {
    return makeBdd(_index);
  }

  BDD opCom()
  {
    return this.not();
  }

  BDD not()
  {
    return makeBdd(buddy.bdd_not(_index));
  }

  bool opEquals(BDD rhs)
  {
    return(this._index == rhs._index);
  }

  final BDD lth(BDD other)
  {
    return this.apply(other, BddOp.LESS);
  }

  final BDD gth(BDD other)
  {
    return this.apply(other, BddOp.DIFF);
  }

  final BDD opUnary(string op)() {
    static if(op == "~")
      {
	return this.not();
      }
  }
  
  final BDD opBinary(string op)(BDD other)
  {
    static if(op == "|")
      {
	return this.apply(other, BddOp.OR);
      }
    static if(op == "&")
      {
	return this.apply(other, BddOp.AND);
      }
    static if(op == "^")
      {
	return this.apply(other, BddOp.XOR);
      }
    static if(op == "<")
      {
	return this.apply(other, BddOp.LESS);
      }
    static if(op == "-")
      {
	return this.apply(other, BddOp.DIFF);
      }
    static if(op == ">")
      {
	return this.apply(other, BddOp.DIFF);
      }
    static if(op == ">>")
      {
	return this.apply(other, BddOp.IMP);
      }
    static if(op == "<<")
      {
	return this.apply(other, BddOp.INVIMP);
      }
  }

  BDD and(BDD other)
  {
    return this.apply(other, BddOp.AND);
  }

  BDD nand(BDD other)
  {
    return this.apply(other, BddOp.NAND);
  }

  /**
   * <p>Returns the logical 'or' of two bdds.  This is a shortcut for calling
   * "apply" with the "or" operator.</p>
   *
   * <p>Compare to bdd_or.</p>
   *
   * @param that the bdd to 'or' with
   * @return the logical 'or' of two bdds
   */
  BDD or(BDD other)
  {
    return this.apply(other, BddOp.OR);
  }

  BDD nor(BDD other)
  {
    return this.apply(other, BddOp.NOR);
  }


  /**
   * <p>Returns the logical 'xor' of two bdds.  This is a shortcut for calling
   * "apply" with the "xor" operator.</p>
   *
   * <p>Compare to bdd_xor.</p>
   *
   * @param that the bdd to 'xor' with
   * @return the logical 'xor' of two bdds
   */
  BDD xor(BDD other)
  {
    return this.apply(other, BddOp.XOR);
  }

  /**
   * <p>Returns the logical 'implication' of two bdds.  This is a shortcut for
   * calling "apply" with the "imp" operator.</p>
   *
   * <p>Compare to bdd_imp.</p>
   *
   * @param that the bdd to 'implication' with
   * @return the logical 'implication' of two bdds
   */
  BDD imp(BDD other)
  {
    return this.apply(other, BddOp.IMP);
  }


  /**
   * <p>Returns the logical 'bi-implication' of two bdds.  This is a shortcut for
   * calling "apply" with the "biimp" operator.</p>
   *
   * <p>Compare to bdd_biimp.</p>
   *
   * @param that the bdd to 'bi-implication' with
   * @return the logical 'bi-implication' of two bdds
   */
  BDD biimp(BDD other)
  {
    return this.apply(other, BddOp.BIIMP);
  }

  BDD ite(BDD thenBDD, BDD elseBDD)
  {
    uint x = _index;
    uint y = thenBDD._index;
    uint z = elseBDD._index;
    return makeBdd(buddy.bdd_ite(x, y, z));
  }

  // compare with bvec_ite
  BddVec ite(BddVec b, BddVec c)
  {
    if(b.size != c.size)
      {
	bdd_error(BddError.BVEC_SIZE);
      }

    BddVec res = buddy.buildVec(b.size, false);

    for(size_t n = 0 ; n < b.size ; ++n)
      {
	res.bitvec[n] = this.ite(b.bitvec[n], c.bitvec[n]);
      }

    return res;
  }

  BDD relprod(BDD that, BDD var)
  {
    uint x = _index;
    uint y = that._index;
    uint z = var._index;
    return makeBdd(buddy.bdd_relprod(x, y, z));
  }

  BDD compose(BDD g, int var)
  {
    uint x = _index;
    uint y = g._index;
    return makeBdd(buddy.bdd_compose(x, y, var));
  }

  BDD veccompose(BddPair pair)
  {
    uint x = _index;
    return makeBdd(buddy.bdd_veccompose(x, pair));
  }

  BDD constrain(BDD that)
  {
    uint x = _index;
    uint y = that._index;
    return makeBdd(buddy.bdd_constrain(x, y));
  }

  BDD exist(BDD var)
  {
    uint x = _index;
    uint y = var._index;
    return makeBdd(buddy.bdd_exist(x, y));
  }

  BDD forAll(BDD var)
  {
    uint x = _index;
    uint y = var._index;
    return makeBdd(buddy.bdd_forall(x, y));
  }

  BDD unique(BDD var)
  {
    uint x = _index;
    uint y = var._index;
    return makeBdd(buddy.bdd_unique(x, y));
  }

  BDD restrict(BDD var)
  {
    uint x = _index;
    uint y = var._index;
    return makeBdd(buddy.bdd_restrict(x, y));
  }

  BDD simplify(BDD d)
  {
    uint x = _index;
    uint y = d._index;
    return makeBdd(buddy.bdd_simplify(x, y));
  }

  BDD support()
  {
    uint x = _index;
    return makeBdd(buddy.bdd_support(x));
  }

  BDD apply(BDD that, BddOp opr)
  {
    uint x = _index;
    uint y = that._index;
    // BddOp z = opr.dup;
    return makeBdd(buddy.bdd_apply(x, y, opr));
  }

  BDD applyAll(BDD that, BddOp opr, BDD var)
  {
    uint x = _index;
    uint y = that._index;
    // BddOp z = opr.dup;
    uint a = var._index;
    return makeBdd(buddy.bdd_appall(x, y, opr, a));
  }

  BDD applyEx(BDD that, BddOp opr, BDD var)
  {
    uint x = _index;
    uint y = that._index;
    // BddOp z = opr.dup;
    uint a = var._index;
    return makeBdd(buddy.bdd_appex(x, y, opr, a));
  }

  BDD applyUni(BDD that, BddOp opr, BDD var)
  {
    uint x = _index;
    uint y = that._index;
    // BddOp z = opr.dup;
    uint a = var._index;
    return makeBdd(buddy.bdd_appuni(x, y, opr, a));
  }

  BDD satOne()
  {
    uint x = _index;
    return makeBdd(buddy.bdd_satone(x));
  }

  BDD randSatOne(double rand, double[uint] dist)
  {
    return makeBdd(buddy.bdd_randsatone(rand, dist, _index));
  }

  BDD fullSatOne()
  {
    uint x = _index;
    return makeBdd(buddy.bdd_fullsatone(x));
  }

  BDD satOne(BDD var, bool pol)
  {
    uint x = _index;
    uint y = var._index;
    int z = pol ? 1 : 0;
    return makeBdd(buddy.bdd_satoneset(x, y, z));
  }

  byte[][] allSat()
  {
    uint x = _index;
    byte[][] result;
    buddy.bdd_allsat(x, result);
    return result;
  }

  int[] scanSet()
  {
    int[] varset;
    if(isOne() || isZero())
      {
	// return it empty
	return varset;
      }

    BDD n = this.dup();
    // TBD This should be more efficient for D
    version(BDDD_FIX1)
      {
	do {
	  varset ~= n.var();
	  bdd n2 = n.high();
	  n = n2;
	} while(!n.isZero() && !n.isOne());
      }
    else {
      int num = 0;
      do {
	num++;
	BDD n2 = n.high();
	n = n2;
      } while(!n.isZero() && !n.isOne());

      varset.length = num;

      num = 0;
      n = this.dup();
      do {
	varset[num++] = n.var();
	BDD n2 = n.high();
	n = n2;
      } while(!n.isZero() && !n.isOne());
    }
    return varset;
  }

  int[] scanSetDomains()
  {
    int[] fv;
    int[] varset;
    long fn;
    int num, n, m, i;

    fv = this.scanSet();
    // if(fv is null)
    //   return null;
    fn = fv.length;

    if(fn == 0) return fv;

    version(BDDD_FIX2)
      {
	for(n = 0; n < buddy.numberOfDomains(); n++)
	  {
	    BddDomain dom = buddy.getDomain(n);
	    auto ivar = dom.get_ivars();
	    bool found = false;
	    for(m = 0; m < dom.varNum() && !found; m++)
	      {
		for(i = 0; i < fn && !found; i++)
		  {
		    if(ivar[m] == fv[i])
		      {
			varset ~= n;
			found = true;
		      }
		  }
	      }
	  }
      } else {
      for(n = 0, num = 0; n < buddy.numberOfDomains(); n++)
	{
	  BddDomain dom = buddy.getDomain(n);
	  auto ivar = dom.get_ivars();
	  bool found = false;
	  for(m = 0; m < dom.varNum() && !found; m++)
	    {
	      for(i = 0; i < fn && !found; i++)
		{
		  if(ivar[m] == fv[i])
		    {
		      num++;
		      found = true;
		    }
		}
	    }
	}

      // varset = new int[num];
      varset.length = num;

      for(n = 0, num = 0; n < buddy.numberOfDomains(); n++)
	{
	  BddDomain dom = buddy.getDomain(n);
	  auto ivar = dom.get_ivars();
	  bool found = false;
	  for(m = 0; m < dom.varNum() && !found; m++)
	    {
	      for(i = 0; i < fn && !found; i++)
		{
		  if(ivar[m] == fv[i])
		    {
		      varset[num++] = n;
		      found = true;
		    }
		}
	    }
	}
    }
    return varset;
  }

  long scanVar(BddDomain d)
  {
    if(this.isZero())
      {
	long bi = -1;
	return bi;
      }
    long[] allvar = this.scanAllVar();
    long res = allvar[d.getIndex()];
    return res;
  }

  long[] scanAllVar()
  {
    int n;
    bool[] store;
    long[] res;

    if(this.isZero())
      return null;

    int _varNum = buddy.varNum();
    store = new bool[_varNum];

    BDD p = this.dup();
    while(!p.isOne() && !p.isZero())
      {
	BDD lo = p.low();
	if(!lo.isZero())
	  {
	    store[p.var()] = false;
	    BDD p2 = p.low();
	    p = p2;
	  } else {
	  store[p.var()] = true;
	  BDD p2 = p.high();
	  p = p2;
	}
      }

    int fdvarnum = buddy.numberOfDomains();
    res.length = fdvarnum;

    for(n = 0; n < fdvarnum; n++)
      {
	BddDomain dom = buddy.getDomain(n);
	auto ivar = dom.get_ivars();

	long val = 0;
	for(int m = dom.varNum() - 1; m >= 0; m--)
	  {
	    val <<= 1;
	    if(store[ivar[m]]) ++val;
	  }

	res[n] = val;
      }

    return res;
  }

  private static int[] varset2levels(BDD r) {
    int size = 0;
    BDD p = r.dup();
    while (!p.isOne() && !p.isZero()) {
      ++size;
      BDD p2 = p.high();
      p = p2;
    }
    int[] result = new int[size];
    size = -1;
    p = r.dup();
    while(!p.isOne() && !p.isZero()) {
      result[++size] = p.level();
      BDD p2 = p.high();
      p = p2;
    }
    return result;
  }

  BDD replace(BddPair pair) {
    uint x = _index;
    return makeBdd(buddy.bdd_replace(x, pair));
  }

  void printSet()
  {
    writeln(this.toString());
  }

  void printSetWithDomains()
  {
    writeln(this.toStringWithDomains());
  }

  void printDot()
  {
    writeln("digraph G {");
    writeln("0 [shape=box, label=\"0\", style=filled, shape=box, height=0.3, width=0.3];");
    writeln("1 [shape=box, label=\"1\", style=filled, shape=box, height=0.3, width=0.3];");

    bool[] visited = new bool[nodeCount()+2];
    visited[0] = true; visited[1] = true;

    int[BDD] map;
    // HashMap map = new HashMap();

    map[buddy.zero()] = 0;
    map[buddy.one()] = 1;

    printdot_rec(stdout, 1, visited, map);
    writeln("}");
  }

  int printdot_rec(File f, int current, bool[] visited,
			  int[BDD] map)
  {
    int ri = map[this];
    if((this in map) is null)
      {
	ri = ++current;
	map[this.dup()] = ri;
      }

    if(visited[ri]) return current;

    visited[ri] = true;

    // TODO: support labelling of vars.
    f.writeln(ri, " [label=\"", this.var(), "\"];");

    BDD l = this.low();
    BDD h = this.high();
    int li = map[l];

    if((l in map) is null)
      {
	li = ++current;
	map[l] = li;
      }

    int low = li;

    int hi = map[h];
    if((h in map) is null)
      {
	hi = ++current;
	map[h] = hi;
      }
    int high = hi;

    f.writeln(ri, " -> ", low, " [style=dotted];");
    f.writeln(ri, " -> ", high, " [style=filled];");

    current = l.printdot_rec(f, current, visited, map);
    current = h.printdot_rec(f, current, visited, map);
    return current;
  }

  int nodeCount()
  {
    return buddy.bdd_nodecount(_index);
  }

  double pathCount()
  {
    return buddy.bdd_pathcount(_index);
  }

  void satDist(out double[uint] dist)
  {
    buddy.bdd_satdist(_index, dist);
  }

  double satCount()
  {
    return buddy.bdd_satcount(_index);
  }

  double satCount(BDD varset)
  {
    double unused = buddy.varNum();

    if(varset.isZero() || varset.isOne() || isZero()) /* empty set */
      return 0.;

    BDD n = varset.dup();
    do {
      BDD n2 = n.high();
      n = n2;
      unused--;
    } while(!n.isOne() && !n.isZero());

    unused = satCount() /(2.0 ^^ unused);

    return unused >= 1.0 ? unused : 1.0;
  }

  double logSatCount()
  {
    return log(satCount());
  }

  double logSatCount(BDD varset)
  {
    return log(satCount(varset));
  }


  int[] varProfile()
  {
    uint x = _index;
    return buddy.bdd_varprofile(x);
  }

  bool equals(BDD that)
  {
    bool b = this._index == that._index;
    return b;
  }

  int hashCode()
  {
    return _index;
  }

  string toString()
  {
    if(_index < 2) return _index == 0 ? "F" : "T";
    byte[] set = new byte[](buddy.varNum());
    // StringBuffer sb = new StringBuffer();
    string sb;
    bdd_printset_rec(sb, this, set);
    return sb;
  }

  void bdd_printset_rec(ref string sb, BDD r, byte[] set)
  {
    bool first = true;

    if(r.isZero())
      return;
    else if(r.isOne())
      {
	sb ~= '<';
	for(int n = 0; n < set.length; n++)
	  {
	    if(set[n] > 0)
	      {
		if(!first) sb ~= ", ";
		first = false;
		sb ~= format("%s: %s", buddy.level2Var(n),
			     set[n] == 2 ? 1 : 0);
	      }
	  }
	sb ~= '>';
      }
    else
      {
	// set[buddy.var2Level(r.var())] = 1;
	set[buddy.LEVEL(r._index)] = 1;
	bdd_printset_rec(sb, r.low(), set);

	// set[buddy.var2Level(r.var())] = 2;
	set[buddy.LEVEL(r._index)] = 2;
	bdd_printset_rec(sb, r.high(), set);

	// set[buddy.var2Level(r.var())] = 0;
	set[buddy.LEVEL(r._index)] = 0;
      }
  }

  byte[][] toVector() {
    byte[] set;
    byte[][] res;
    if (_index < 2) {
      if (_index == 0) {
	assert(false, "Constraints do not converge");
      }
      else {
	// empty set
	return res;
      }
    }

    // set = new byte[](buddy.varNum());
    set.length = buddy.varNum();
    set[] = -1;
    bdd_tovec_rec(res, this, set);
    return res;
  }

  void bdd_tovec_rec(ref byte[][] res, BDD r, ref byte[] set)
  {
    if(r.isZero()) return;
    else if(r.isOne()) {
      res ~= set.dup;
    }
    else
      {
	set[buddy.LEVEL(r._index)] = 0;
	bdd_tovec_rec(res, r.low(), set);
	set[buddy.LEVEL(r._index)] = 1;
	bdd_tovec_rec(res, r.high(), set);
	set[buddy.LEVEL(r._index)] = -1;
      }
  }

  int[] getIndices(uint index)
  {
    BddDomain domain_n = buddy.getDomain(index);
    return domain_n.get_ivars();
  }

  string toStringWithDomains()
  {
    if(this.isZero()) return "F";
    if(this.isOne()) return "T";

    string sb;
    int[] set = new int[](buddy.varNum());
    fdd_printset_rec(sb, this, set);
    return sb;
  }

  private void fdd_printset_rec(ref string sb, BDD r, int[] set)
  {
    int fdvarnum = buddy.numberOfDomains();

    bool used = false;
    bool first;

    if(r.isZero())
      return;
    else if(r.isOne())
      {
	sb ~= '<';
	first = true;

	for(int n = 0 ; n < fdvarnum ; n++)
	  {
	    // import std.stdio;
	    bool firstval = true;
	    used = false;

	    BddDomain domain_n = buddy.getDomain(n);

	    auto vars = domain_n.get_ivars();
	    size_t binsize = vars.length;
	    for(int m=0 ; m<binsize ; m++)
	      if(set[vars[m]] != 0)
		used = true;

	    if(used)
	      {
		if(!first)
		  sb ~= ", ";
		first = false;
		sb ~= domain_n.getName();
		sb ~= ':';

		// writeln("Domain: ", n, binsize);
		for (int m=0 ; m<(1LU << binsize) ; m++)
		  {
		    int ok=1;

		    for (int i=0 ; i<binsize && ok ; i++)
		      if (set[vars[i]] == 1  &&  ((m >> i) & 1) != 0)
			ok = 0;
		      else if (set[vars[i]] == 2  && ((m >> i) & 1) != 1)
			ok = 0;

		    if (ok)
		      {
			if (!firstval) sb ~= "/";
			sb ~= format("%s", m);
			firstval = false;
		      }
		  }
	      }
	  }
	sb ~= '>';
      }
    else
      {
	// set[buddy.var2Level(r.var())] = 1;
	set[buddy.LEVEL(r._index)] = 1;
	fdd_printset_rec(sb, r.low(), set);

	// set[buddy.var2Level(r.var())] = 2;
	set[buddy.LEVEL(r._index)] = 2;
	fdd_printset_rec(sb, r.high(), set);

	// set[buddy.var2Level(r.var())] = 0;
	set[buddy.LEVEL(r._index)] = 0;
      }
  }
}

private void _delete(T)(T obj) {
  import core.memory;
  import std.stdio;
  // writeln("Deleting Buddy");
  destroy(obj);
  // GC.free(cast(void*)obj);
}


class Buddy
{
  // VERIFY_ASSERTIONS would be handled as a debug behavior

  enum string REVISION = "$Revision: 1.0 $";
  
  bool gbc_enabled = true;

  void disableGC() {
    gbc_enabled = false;
  }

  void enableGC() {
    gbc_enabled = true;
  }

  string getVersion()
  {
    import std.regex;
    return "Buddy " ~ split(REVISION, regex(" "))[1];
  }

  private this()
  {
    gcstats = new GCStats();
    reorderstats = new ReorderStats();
    _cacheStats = new CacheStats();
    // BDD.peer = new Aux();
  }

  static Buddy init(uint nodenum, uint cachesize)
  {
    Buddy f = new Buddy();
    f.initialize(nodenum, cachesize);
    return f;
  }


  this(uint nodenum, uint cachesize)
  {
    this();
    this.initialize(nodenum, cachesize);
  }

  // FLUSH_CACHE_ON_GC would be treated as a debug feature
  // and since by default it is set to true, we shall use
  // DONT_FLUSH_CACHE_ON_GC with a default value of false

  /**
   * Private helper function to create BDD objects.
   */
  // private BDD makeBDD(int id)
  // {
  //   if(freeList is null)
  // {
  //     BDD b = new BDD(id);
  //     return b;
  //   }

  //   BDD b = freeList;
  //   freeList = freeList.next;
  //   // writeln("using freelist:", b._index);
  //   b._index = id;
  //   addRef(b._index);
  //   return b;
  // }

  // BDD freeList = null;


  private Buddy getBuddy()
  {
    return this;
  }

  // class Aux {
  //   Buddy getRoot()
  //   {
  //     return getBuddy();
  //   }
  // }


  struct BddNode
  {
    import std.bitmanip;

    enum int MARK_MASK = 0x00200000;
    enum int MAXVAR = 0x001FFFFF;
    enum uint MAXREF = 0x3FF; // 10 bit, all ones

    union
    {
      mixin(bitfields!(uint, "levelAndMark", 22,
		       uint, "refcount", 10));
      mixin(bitfields!(uint, "level", 21,
		       bool, "mark", 1,
		       uint, "refcou", 10));
    }

    uint low;
    uint high;
    uint hash;
    uint next;
    // Do not know why this MAXVAR(actually "level") in original code
    // is a signed integer

    bool hasRef()
    {
      return this.refcou != 0;
    }

    void setMaxRef()
    {
      this.refcou = MAXREF;	// 0xFFC00000;
    }

    void clearRef()
    {
      this.refcou = 0;
    }

    void incRef()
    {
      if(this.refcou != MAXREF)
	this.refcou = this.refcou + 1;
    }

    void decRef()
    {
      if(this.refcou != MAXREF && this.refcou != 0)
	this.refcou = this.refcou - 1;
    }

    uint getRef()
    {
      return this.refcou;
    }

    void setMark()
    {
      this.mark = true;
    }

    void unMark()
    {
      this.mark = false;
    }

    bool marked()
    {
      return this.mark;
    }

    // final @property int ref()
    // {
    //   return this.refcou;
    // }
  }


  private final bool HASREF(uint n)
  {
    return _nodes[n].hasRef();
  }

  private final void SETMAXREF(uint n)
  {
    _nodes[n].setMaxRef();
  }

  private final void CLEARREF(uint n)
  {
    _nodes[n].clearRef();
  }

  private final void INCREF(uint n)
  {
    _nodes[n].incRef();
  }

  private final void DECREF(uint n)
  {
    _nodes[n].decRef();
  }

  private final uint GETREF(uint n)
  {
    return _nodes[n].getRef();
  }

  private final uint LEVEL(uint n)
  {
    return _nodes[n].level;
  }

  private final uint LEVELANDMARK(uint n)
  {
    return _nodes[n].levelAndMark;
  }

  private final void SETLEVEL(uint n, uint val)
  {
    _nodes[n].level = val;
  }

  private final void SETLEVELANDMARK(uint n, uint val)
  {
    _nodes[n].levelAndMark = val;
  }

  private final void SETMARK(uint n)
  {
    _nodes[n].setMark();
  }

  private final void UNMARK(uint n)
  {
    _nodes[n].unMark();
  }

  private final bool MARKED(uint n)
  {
    return _nodes[n].marked();
  }

  private final uint LOW(uint r)
  {
    return _nodes[r].low;
  }

  private final void SETLOW(uint r, uint v)
  {
    _nodes[r].low = v;
  }

  private final uint HIGH(uint r)
  {
    return _nodes[r].high;
  }

  private final void SETHIGH(uint r, uint v)
  {
    _nodes[r].high = v;
  }

  private final uint HASH(uint r)
  {
    return _nodes[r].hash;
  }

  private final void SETHASH(uint r, uint v)
  {
    _nodes[r].hash = v;
  }

  private final uint NEXT(uint r)
  {
    return _nodes[r].next;
  }

  private final void SETNEXT(uint r, uint v)
  {
    _nodes[r].next = v;
  }

  private final uint VARr(uint n)
  {
    return LEVELANDMARK(n);
  }

  void SETVARr(uint n, uint val)
  {
    SETLEVELANDMARK(n, val);
  }

  struct BddCacheData
  {
    union
    {
      double dres;
      int res;
    }
    int a,b,c;
  }

  struct BddCacheDataPointer {
    BddCacheData* _ptr;
    this(BddCacheData* ptr)
    {
      _ptr = ptr;
    }
    @property double dres()
    {
      return(*_ptr).dres;
    }
    @property void dres(double dres_)
    {
      (*_ptr).dres = dres_;
    }
    @property int res()
    {
      return(*_ptr).res;
    }
    @property void res(int res_)
    {
      (*_ptr).res = res_;
    }
    @property int a()
    {
      return(*_ptr).a;
    }
    @property void a(int a_)
    {
      (*_ptr).a = a_;
    }
    @property int b()
    {
      return(*_ptr).b;
    }
    @property void b(int b_)
    {
      (*_ptr).b = b_;
    }
    @property int c()
    {
      return(*_ptr).c;
    }
    @property void c(int c_)
    {
      (*_ptr).c = c_;
    }
  }

  struct BddCache
  {
    Array!BddCacheData table;
    bool initialized = false;

    void init(uint size)
    {
      size = primeGte(size);
      table.reserve(size);
      table.length = size;

      foreach(ref entry; table)
	{
	  entry.a = -1;
	}
      this.initialized = true;
    }

    // call init if not already initialized
    void initIfNull(uint size)
    {
      if(!initialized) this.init(size);
    }

    this(uint size)
    {
      this.init(size);
    }

    // postblit
    this(this)
    {
      this.table = this.table.dup;
    }

    // Do we need the next two functions
    BddCache copy()
    {
      return this.dup();
    }

    BddCache dup()
    {
      BddCache that;
      that.table = this.table.dup;
      that.initialized = this.initialized;
      return that;
    }

    void done()
    {
      table.length = 0;
      table.reserve(0);
      this.initialized = false;
    }

    int resize(uint newsize)
    {
      this.done();
      this.init(newsize);
      return 0;
    }

    void reset()
    {
      foreach(ref entry; table)
	{
	  entry.a = -1;
	}
    }

    // BddCacheData lookup(int hash)
    // {
    //   return this.table[abs(hash % this.table.length)];
    // }

    BddCacheData* lookup(int hash)
    {
      // return BddCacheDataPointer(&(this.table[abs(hash % this.table.length)]));
      return &(this.table[abs(hash % this.table.length)]);
    }

    void cache(int hash, BddCacheData entry)
    {
      this.table[abs(hash % this.table.length)] = entry;
    }

    void clean_d(Buddy buddy)
    {
      int n;
      foreach(ref entry; this.table)
	{
	  int a = entry.a;
	  if(a >= 0 && buddy.LOW(a) == INVALID_BDD)
	    {
	      entry.a = -1;
	    }
	}
    }

    void clean_a(Buddy buddy)
    {
      int n;
      foreach(ref entry; this.table)
	{
	  int a = entry.a;
	  if(a < 0) continue;
	  if(buddy.LOW(a) == INVALID_BDD ||
	     buddy.LOW(entry.res) == INVALID_BDD)
	    {
	      entry.a = -1;
	    }
	}
    }

    void clean_ab(Buddy buddy)
    {
      int n;
      foreach(ref entry; this.table)
	{
	  int a = entry.a;
	  if(a < 0) continue;
	  if(buddy.LOW(a) == INVALID_BDD ||
	     (entry.b != 0 && buddy.LOW(entry.b) == INVALID_BDD) ||
	     buddy.LOW(entry.res) == INVALID_BDD)
	    {
	      entry.a = -1;
	    }
	}
    }

    void clean_abc(Buddy buddy)
    {
      int n;
      foreach(ref entry; this.table)
	{
	  int a = entry.a;
	  if(a < 0) continue;
	  if(buddy.LOW(a) == -1 ||
	     buddy.LOW(entry.b) == INVALID_BDD ||
	     buddy.LOW(entry.c) == INVALID_BDD ||
	     buddy.LOW(entry.res) == INVALID_BDD)
	    {
	      entry.a = -1;
	    }
	}
    }
  }



  struct BddCacheStat
  {
    ulong uniqueAccess;
    ulong uniqueChain;
    ulong uniqueHit;
    ulong uniqueMiss;
    ulong opHit;
    ulong opMiss;
    ulong swapCount;
  }


  enum uint BDDONE = 1;
  enum uint BDDZERO = 0;

  enum uint INVALID_BDD = uint.max; // -1;

  bool _running; /* Flag - package initialized */
  int _errorCond; /* Some error condition */
  uint _nodeSize() @property {return cast(uint) _nodes.length;}
  int _maxNodeSize; /* Maximum allowed number of _nodes */
  int _maxNodeIncr; /* Max. # of _nodes used to inc. table */
  Array!BddNode _nodes; /* All of the BDD _nodes */
  int _freePos; /* First free node */
  int _freeNum; /* Number of free _nodes */
  int _produced; /* Number of new _nodes ever produced */
  int _varNum; /* Number of defined BDD variables */
  Array!int _refStack; /* Internal node reference stack */
  int _refStackTop; /* Internal node reference stack top */
  Array!int _var2Level; /* Variable -> level table */
  Array!int _level2Var; /* Level -> variable table */
  bool _resized; /* Flag indicating a resize of the nodetable */

  BddCacheStat bddcachestats;

  void cacheStats()
  {
    writeln(_cacheStats.opHit, " ", _cacheStats.opMiss);
  }

  int _minFreeNodes = 20;

  /*=== PRIVATE KERNEL VARIABLES =========================================*/

  Array!int _varSet; /* Set of defined BDD variables */
  int _gbCollectNum; /* Number of garbage collections */
  int _cacheSize; /* Size of the operator caches */
  long _gbcClock; /* Clock ticks used in GBC */
  int _usedNodesNextReorder; /* When to do reorder next time */

  enum int DEFAULTMAXNODEINC = 50000;

  /*=== OTHER INTERNAL DEFINITIONS =======================================*/

  static final int PAIR(int a, int b)
  {
    //return Math.abs((a + b) *(a + b + 1) / 2 + a);
    return((a + b) *(a + b + 1) / 2 + a);
  }
  static final int TRIPLE(int a, int b, int c)
  {
    //return Math.abs(PAIR(c, PAIR(a, b)));
    int d =((a + b) *(a + b + 1) / 2 + a);
    return((c + d) *(c + d + 1) / 2 + c);
  }

  final int NODEHASH(int a, int b, int c)
  {
    int d =((a + b) *(a + b + 1) / 2 + a);
    return abs(((c + d) *(c + d + 1) / 2 + c) % _nodeSize);
  }

  BDD zero()
  {
    return BDD(BddFalse, this);
  }

  BDD one()
  {
    return BDD(BddTrue, this);
  }

  // BDD buildCube(int value, BDD[] variables)
  // {
  //   BDD result = one();
  //   foreach_reverse(ref var; variables)
  //     {
  // 	BDD v;
  // 	if((value & 0x1) != 0) v = var.dup();
  // 	else                   v = var.not();

  // 	result = result.and(v);
  // 	value >>= 1;
  //     }
  //   return result;
  // }

  // in place of bdd_ibuildcube
  BDD buildCube(int value, int[] variables)
  {
    BDD result = one();
    foreach_reverse(ref var; variables)
      {
	BDD v;
	if((value & 0x1) != 0) v = ithVar(var);
	else                   v = nithVar(var);
	result = result.and(v);
	value >>= 1;
      }
    return result;
  }

  BDD makeSet(int[] varset)
  {
    BDD res = one();
    int varnum = cast(int) varset.length;
    for(int v = varnum-1 ; v >= 0 ; --v) {
      res = res.and(ithVar(varset[v]));
    }
    return res;
  }

  BDD makeSet(ref Array!int varset)
  {
    BDD res = one();
    int varnum = cast(int) varset.length;
    for(int v = varnum-1 ; v >= 0 ; --v) {
      res = res.and(ithVar(varset[v]));
    }
    return res;
  }


  int bdd_ithvar(int var)
  {
    if(var < 0 || var >= _varNum)
      {
	bdd_error(BddError.BDD_VAR);
	return BddFalse;
      }

    return _varSet[var * 2];
  }

  int bdd_nithvar(int var)
  {
    if(var < 0 || var >= _varNum)
      {
	bdd_error(BddError.BDD_VAR);
	return BddFalse;
      }

    return _varSet[(var * 2) + 1];
  }

  int bdd_varnum()
  {
    return _varNum;
  }

  static bool ISZERO(int r)
  {
    return r == BddFalse;
  }

  static bool ISONE(int r)
  {
    return r == BddTrue;
  }

  static bool ISCONST(int r)
  {
    //return r == BddFalse || r == BddTrue;
    return r < 2;
  }

  void CHECK(int r)
  {
    if(!isRunning())
      bdd_error(BddError.BDD_RUNNING);
    else if(r < 0 || r >= _nodeSize) {
      bdd_error(BddError.BDD_ILLBDD);
    }
    else if(r >= 2 && LOW(r) == INVALID_BDD) {
      bdd_error(BddError.BDD_ILLBDD);
    }
  }

  void CHECKa(int r, int x)
  {
    CHECK(r);
  }

  int bdd_var(int r)
  {
    CHECK(r);
    if(r < 2) {
      bdd_error(BddError.BDD_ILLBDD);
    }

    return(_level2Var[LEVEL(r)]);
  }

  int bdd_low(int r)
  {
    CHECK(r);
    if(r < 2) {
      return bdd_error(BddError.BDD_ILLBDD);
    }

    return(LOW(r));
  }

  int bdd_high(int r)
  {
    CHECK(r);
    if(r < 2) {
      return bdd_error(BddError.BDD_ILLBDD);
    }

    return(HIGH(r));
  }

  // TBD
  void checkresize()
  {
    if(_resized)
      bdd_operator_noderesize();
    _resized = false;
  }

  static final int NOTHASH(int r)
  {
    return r;
  }
  static final int APPLYHASH(int a, int b, int c)
  {
    int d =((a + b) *(a + b + 1) / 2 + a);
    return((c + d) *(c + d + 1) / 2 + c);
  }
  static final int ITEHASH(int f, int g, int h)
  {
    return TRIPLE(f, g, h);
  }
  static final int RESTRHASH(int r, int var)
  {
    return PAIR(r, var);
  }
  static final int CONSTRAINHASH(int f, int c)
  {
    return PAIR(f, c);
  }
  static final int QUANTHASH(int r)
  {
    return r;
  }
  static final int REPLACEHASH(int r)
  {
    return r;
  }
  static final int VECCOMPOSEHASH(int f)
  {
    return f;
  }
  static final int COMPOSEHASH(int f, int g)
  {
    return PAIR(f, g);
  }
  static final int SATCOUHASH(int r)
  {
    return r;
  }
  static final int LOG2SATCOUHASH(int r)
  {
    return r;
  }
  static final int PATHCOUHASH(int r)
  {
    return r;
  }
  static final int LOG2PATHCOUHASH(int r)
  {
    return r;
  }
  static final int APPEXHASH(int l, int r, int op)
  {
    return PAIR(l, r);
  }

  enum double M_LN2 = 0.69314718055994530942;

  static double log1p(double a)
  {
    return log(1.0 + a);
  }

  final bool INVARSET(int a)
  {
    return(quantvarset[a] == quantvarsetID); /* unsigned check */
  }
  final bool INSVARSET(int a)
  {
    return abs(quantvarset[a]) == quantvarsetID; /* signed check */
  }


  int bdd_not(int r)
  {
    int res;
    firstReorder = 1;
    CHECKa(r, BddFalse);

    _applyCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	INITREF();

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = not_rec(r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();
	  if(--firstReorder == 0)
	    continue; // again;
	  res = BddFalse;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int not_rec(int r)
  {
    int res;

    if(r == 0)
      return BddTrue;
    if(r == 1)
      return BddFalse;

    BddCacheData* entry = _applyCache.lookup(NOTHASH(r));

    if((*entry).a == r && (*entry).c == BddOp.NOT)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    PUSHREF(not_rec(LOW(r)));
    PUSHREF(not_rec(HIGH(r)));
    res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
    POPREF(2);

    (*entry).a = r;
    (*entry).c = BddOp.NOT;
    (*entry).res = res;

    return res;
  }


  int bdd_ite(int f, int g, int h)
  {
    int res;
    firstReorder = 1;

    CHECKa(f, BddFalse);
    CHECKa(g, BddFalse);
    CHECKa(h, BddFalse);

    _applyCache.initIfNull(_cacheSize);
    _iteCache.initIfNull(_cacheSize);

    // again :
    while(true) {
      try {
	INITREF();

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = ite_rec(f, g, h);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int ite_rec(int f, int g, int h)
  {
    int res;

    if(f == 1)
      return g;
    if(f == 0)
      return h;
    if(g == h)
      return g;
    if(g == 1 && h == 0)
      return f;
    if(g == 0 && h == 1)
      return not_rec(f);

    BddCacheData* entry = _iteCache.lookup(ITEHASH(f, g, h));
    if((*entry).a == f &&(*entry).b == g &&(*entry).c == h)
      {
	debug(CACHESTATS)
	  {
	    _cacheStats.opHit++;
	  }
	return(*entry).res;
      }
    debug(CACHESTATS)
      {
	_cacheStats.opMiss++;
      }

    if(LEVEL(f) == LEVEL(g))
      {
	if(LEVEL(f) == LEVEL(h))
	  {
	    PUSHREF(ite_rec(LOW(f), LOW(g), LOW(h)));
	    PUSHREF(ite_rec(HIGH(f), HIGH(g), HIGH(h)));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	  }
	else if(LEVEL(f) < LEVEL(h))
	  {
	    PUSHREF(ite_rec(LOW(f), LOW(g), h));
	    PUSHREF(ite_rec(HIGH(f), HIGH(g), h));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	  }
	else /* f > h */
	  {
	    PUSHREF(ite_rec(f, g, LOW(h)));
	    PUSHREF(ite_rec(f, g, HIGH(h)));
	    res = bdd_makenode(LEVEL(h), READREF(2), READREF(1));
	  }
      }
    else if(LEVEL(f) < LEVEL(g))
      {
	if(LEVEL(f) == LEVEL(h))
	  {
	    PUSHREF(ite_rec(LOW(f), g, LOW(h)));
	    PUSHREF(ite_rec(HIGH(f), g, HIGH(h)));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	  }
	else if(LEVEL(f) < LEVEL(h))
	  {
	    PUSHREF(ite_rec(LOW(f), g, h));
	    PUSHREF(ite_rec(HIGH(f), g, h));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	  }
	else /* f > h */
	  {
	    PUSHREF(ite_rec(f, g, LOW(h)));
	    PUSHREF(ite_rec(f, g, HIGH(h)));
	    res = bdd_makenode(LEVEL(h), READREF(2), READREF(1));
	  }
      }
    else /* f > g */
      {
	if(LEVEL(g) == LEVEL(h))
	  {
	    PUSHREF(ite_rec(f, LOW(g), LOW(h)));
	    PUSHREF(ite_rec(f, HIGH(g), HIGH(h)));
	    res = bdd_makenode(LEVEL(g), READREF(2), READREF(1));
	  }
	else if(LEVEL(g) < LEVEL(h))
	  {
	    PUSHREF(ite_rec(f, LOW(g), h));
	    PUSHREF(ite_rec(f, HIGH(g), h));
	    res = bdd_makenode(LEVEL(g), READREF(2), READREF(1));
	  }
	else /* g > h */
	  {
	    PUSHREF(ite_rec(f, g, LOW(h)));
	    PUSHREF(ite_rec(f, g, HIGH(h)));
	    res = bdd_makenode(LEVEL(h), READREF(2), READREF(1));
	  }
      }

    POPREF(2);

    (*entry).a = f;
    (*entry).b = g;
    (*entry).c = h;
    (*entry).res = res;

    return res;
  }

  int bdd_replace(int r, BddPair pair)
  {
    int res;
    firstReorder = 1;

    CHECKa(r, BddFalse);

    _replaceCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	INITREF();
	replacepair = pair.result;
	replacelast = pair.last;
	replaceid =(pair.id << 2) | CACHEID_REPLACE;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = replace_rec(r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int replace_rec(int r)
  {
    int res;

    if(r < 2 || LEVEL(r) > replacelast)
      return r;

    BddCacheData* entry = _replaceCache.lookup(REPLACEHASH(r));
    if((*entry).a == r &&(*entry).c == replaceid)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    PUSHREF(replace_rec(LOW(r)));
    PUSHREF(replace_rec(HIGH(r)));

    res = bdd_correctify(LEVEL(replacepair[LEVEL(r)]),
			 READREF(2), READREF(1));
    POPREF(2);

    (*entry).a = r;
    (*entry).c = replaceid;
    (*entry).res = res;
    return res;
  }

  int bdd_correctify(int level, int l, int r)
  {
    int res;

    if(level < LEVEL(l) && level < LEVEL(r))
      return bdd_makenode(level, l, r);

    if(level == LEVEL(l) || level == LEVEL(r))
      {
	bdd_error(BddError.BDD_REPLACE);
	return 0;
      }

    if(LEVEL(l) == LEVEL(r))
      {
	PUSHREF(bdd_correctify(level, LOW(l), LOW(r)));
	PUSHREF(bdd_correctify(level, HIGH(l), HIGH(r)));
	res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
      }
    else if(LEVEL(l) < LEVEL(r))
      {
	PUSHREF(bdd_correctify(level, LOW(l), r));
	PUSHREF(bdd_correctify(level, HIGH(l), r));
	res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
      }
    else
      {
	PUSHREF(bdd_correctify(level, l, LOW(r)));
	PUSHREF(bdd_correctify(level, l, HIGH(r)));
	res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
      }
    POPREF(2);

    return res; /* FIXME: cache ? */
  }

  int bdd_apply(int l, int r, int op)
  {
    int res;
    firstReorder = 1;

    CHECKa(l, BddFalse);
    CHECKa(r, BddFalse);

    if(op < 0 || op > BddOp.INVIMP)
      {
	bdd_error(BddError.BDD_OP);
	return BddFalse;
      }

    _applyCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	INITREF();
	applyop = op;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = apply_rec(l, r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    //validate(res);

    checkresize();
    return res;
  }

  final int apply_rec(int l, int r)
  {
    int res;
    // static uint count = 0;
    // static uint cache = 0;
    // count++;
    // writeln("apply_rec:",l,":",r,"-",applyop,"    ",rec,"|",cache);

    switch(applyop)
      {
      case BddOp.AND:
	if(l == r)
	  return l;
	if(l == 0  || r == 0)
	  return 0;
	if(l == 1)
	  return r;
	if(r == 1)
	  return l;
	break;
      case BddOp.OR:
	if(l == r)
	  return l;
	if(l == 1  ||  r == 1)
	  return 1;
	if(l == 0)
	  return r;
	if(r == 0)
	  return l;
	break;
      case BddOp.XOR :
	if(l == r)
	  return 0;
	if(l == 0)
	  return r;
	if(r == 0)
	  return l;
	break;
      case BddOp.NAND :
	if(l == 0 || r == 0)
	  return 1;
	break;
      case BddOp.NOR :
	if(l == 1 || r == 1)
	  return 0;
	break;
      case BddOp.IMP :
	if(l == 0)
	  return 1;
	if(l == 1)
	  return r;
	if(r == 1)
	  return 1;
	break;
      default:
	assert(applyop != BddOp.NOT && applyop != BddOp.SIMPLIFY);
	// assert(false);
	break;
      }

    // ISCONST(l)  &&  ISCONST(r)
    if(l < 2 && r < 2)
      res = oprres[applyop][l << 1 | r];
    else {
      BddCacheData* entry = _applyCache.lookup(APPLYHASH(l, r, applyop));

      if((*entry).a == l &&(*entry).b == r &&(*entry).c == applyop)
	{
	  debug(CACHESTATS) {_cacheStats.opHit++;}

	  return(*entry).res;
	}
      debug(CACHESTATS)	{_cacheStats.opMiss++;}

      if(LEVEL(l) == LEVEL(r))
	{
	  PUSHREF(apply_rec(LOW(l), LOW(r)));
	  PUSHREF(apply_rec(HIGH(l), HIGH(r)));
	  res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
	}
      else if(LEVEL(l) < LEVEL(r))
	{
	  PUSHREF(apply_rec(LOW(l), r));
	  PUSHREF(apply_rec(HIGH(l), r));
	  res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
	}
      else {
	PUSHREF(apply_rec(l, LOW(r)));
	PUSHREF(apply_rec(l, HIGH(r)));
	res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
      }

      POPREF(2);

      (*entry).a = l;
      (*entry).b = r;
      (*entry).c = applyop;
      (*entry).res = res;
    }

    return res;
  }

  int and_rec(int l, int r)
  {
    int res;

    if(l == r)
      return l;
    if(l == 0 || r == 0)
      return 0;
    if(l == 1)
      return r;
    if(r == 1)
      return l;
    BddCacheData* entry = _applyCache.lookup(APPLYHASH(l, r, BddOp.AND));

    if((*entry).a == l &&(*entry).b == r &&(*entry).c == BddOp.AND)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    if(LEVEL(l) == LEVEL(r))
      {
	PUSHREF(and_rec(LOW(l), LOW(r)));
	PUSHREF(and_rec(HIGH(l), HIGH(r)));
	res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
      } else if(LEVEL(l) < LEVEL(r))
      {
	PUSHREF(and_rec(LOW(l), r));
	PUSHREF(and_rec(HIGH(l), r));
	res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
      } else {
      PUSHREF(and_rec(l, LOW(r)));
      PUSHREF(and_rec(l, HIGH(r)));
      res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
    }

    POPREF(2);

    (*entry).a = l;
    (*entry).b = r;
    (*entry).c = BddOp.AND;
    (*entry).res = res;
    return res;
  }

  int or_rec(int l, int r)
  {
    int res;

    if(l == r)
      return l;
    if(l == 1 || r == 1)
      return 1;
    if(l == 0)
      return r;
    if(r == 0)
      return l;
    BddCacheData* entry = _applyCache.lookup(APPLYHASH(l, r, BddOp.OR));

    if((*entry).a == l &&(*entry).b == r &&(*entry).c == BddOp.OR)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    if(LEVEL(l) == LEVEL(r))
      {
	PUSHREF(or_rec(LOW(l), LOW(r)));
	PUSHREF(or_rec(HIGH(l), HIGH(r)));
	res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
      } else if(LEVEL(l) < LEVEL(r))
      {
	PUSHREF(or_rec(LOW(l), r));
	PUSHREF(or_rec(HIGH(l), r));
	res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
      } else {
      PUSHREF(or_rec(l, LOW(r)));
      PUSHREF(or_rec(l, HIGH(r)));
      res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
    }

    POPREF(2);

    (*entry).a = l;
    (*entry).b = r;
    (*entry).c = BddOp.OR;
    (*entry).res = res;

    return res;
  }

  int relprod_rec(int l, int r)
  {
    int res;

    if(l == 0 || r == 0)
      return 0;
    if(l == r)
      return quant_rec(l);
    if(l == 1)
      return quant_rec(r);
    if(r == 1)
      return quant_rec(l);

    int LEVEL_l = LEVEL(l);
    int LEVEL_r = LEVEL(r);
    if(LEVEL_l > quantlast && LEVEL_r > quantlast)
      {
	applyop = BddOp.AND;
	res = and_rec(l, r);
	applyop = BddOp.OR;
      } else {
      BddCacheData* entry = _appexCache.lookup(APPEXHASH(l, r, BddOp.AND));
      if((*entry).a == l &&(*entry).b == r &&(*entry).c == appexid)
	{
	  debug(CACHESTATS) {_cacheStats.opHit++;}
	  return(*entry).res;
	}
      debug(CACHESTATS) {_cacheStats.opMiss++;}

      if(LEVEL_l == LEVEL_r)
	{
	  PUSHREF(relprod_rec(LOW(l), LOW(r)));
	  PUSHREF(relprod_rec(HIGH(l), HIGH(r)));
	  if(INVARSET(LEVEL_l))
	    res = or_rec(READREF(2), READREF(1));
	  else
	    res = bdd_makenode(LEVEL_l, READREF(2), READREF(1));
	} else if(LEVEL_l < LEVEL_r)
	{
	  PUSHREF(relprod_rec(LOW(l), r));
	  PUSHREF(relprod_rec(HIGH(l), r));
	  if(INVARSET(LEVEL_l))
	    res = or_rec(READREF(2), READREF(1));
	  else
	    res = bdd_makenode(LEVEL_l, READREF(2), READREF(1));
	} else {
	PUSHREF(relprod_rec(l, LOW(r)));
	PUSHREF(relprod_rec(l, HIGH(r)));
	if(INVARSET(LEVEL_r))
	  res = or_rec(READREF(2), READREF(1));
	else
	  res = bdd_makenode(LEVEL_r, READREF(2), READREF(1));
      }

      POPREF(2);

      (*entry).a = l;
      (*entry).b = r;
      (*entry).c = appexid;
      (*entry).res = res;
    }

    return res;
  }

  int bdd_relprod(int a, int b, int var)
  {
    return bdd_appex(a, b, BddOp.AND, var);
  }

  int bdd_appex(int l, int r, int opr, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(l, BddFalse);
    CHECKa(r, BddFalse);
    CHECKa(var, BddFalse);

    if(opr < 0 || opr > BddOp.INVIMP)
      {
	bdd_error(BddError.BDD_OP);
	return BddFalse;
      }

    if(var < 2) /* Empty set */
      return bdd_apply(l, r, opr);

    _applyCache.initIfNull(_cacheSize);
    _appexCache.initIfNull(_cacheSize);
    _quantCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	if(varset2vartable(var) < 0)
	  return BddFalse;

	INITREF();

	applyop = BddOp.OR;
	appexop = opr;
	appexid =(var << 5) | (appexop << 1); /* FIXME: range! */
	quantid =(appexid << 3) | CACHEID_APPEX;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = appquant_rec(l, r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; //  again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }


  int varset2vartable(int r)
  {
    int n;

    if(r < 2)
      return bdd_error(BddError.BDD_VARSET);

    quantvarsetID++;

    if(quantvarsetID == int.max)
      {
	for(int i = 0; i < _varNum; ++i)
	  quantvarset[i] = 0;
	quantvarsetID = 1;
      }

    quantlast = -1;
    for(n = r; n > 1; n = HIGH(n))
      {
	quantvarset[LEVEL(n)] = quantvarsetID;
	debug(VERIFY_ASSERTIONS) {assert(quantlast < LEVEL(n));}
	quantlast = LEVEL(n);
      }

    return 0;
  }

  int varset2svartable(int r)
  {
    int n;

    if(r < 2)
      return bdd_error(BddError.BDD_VARSET);

    quantvarsetID++;

    if(quantvarsetID == int.max / 2)
      {
	for(int i = 0; i < _varNum; ++i)
	  quantvarset[i] = 0;
	quantvarsetID = 1;
      }

    quantlast = 0;
    for(n = r; n > 1;)
      {
	if(LOW(n) == 0)
	  {
	    quantvarset[LEVEL(n)] = quantvarsetID;
	    n = HIGH(n);
	  } else {
	  quantvarset[LEVEL(n)] = -quantvarsetID;
	  n = LOW(n);
	}
	debug(VERIFY_ASSERTIONS) {assert(quantlast < LEVEL(n));}
	quantlast = LEVEL(n);
      }

    return 0;
  }

  final int appquant_rec(int l, int r)
  {
    int res;

    switch(appexop)
      {
      case BddOp.AND:
	if (l == 0  ||  r == 0)
	  return 0;
	if (l == r)
	  return quant_rec(l);
	if (l == 1)
	  return quant_rec(r);
	if (r == 1)
	  return quant_rec(l);
	break;
      case BddOp.OR :
	if(l == 1 || r == 1)
	  return 1;
	if(l == r)
	  return quant_rec(l);
	if(l == 0)
	  return quant_rec(r);
	if(r == 0)
	  return quant_rec(l);
	break;
      case BddOp.XOR :
	if(l == r)
	  return 0;
	if(l == 0)
	  return quant_rec(r);
	if(r == 0)
	  return quant_rec(l);
	break;
      case BddOp.NAND :
	if(l == 0 || r == 0)
	  return 1;
	break;
      case BddOp.NOR :
	if(l == 1 || r == 1)
	  return 0;
	break;
      default:
	assert(appexop != BddOp.NOT &&
	       appexop != BddOp.SIMPLIFY);
	break;
      }

    if(l < 2 && r < 2)
      res = oprres[appexop][(l << 1) | r];
    else if(LEVEL(l) > quantlast && LEVEL(r) > quantlast)
      {
	int oldop = applyop;
	applyop = appexop;
	apply_rec(l, r);
	applyop = oldop;
      }
    else {
      BddCacheData* entry = _appexCache.lookup(APPEXHASH(l, r, appexop));
      if((*entry).a == l &&(*entry).b == r &&(*entry).c == appexid)
	{
	  debug(CACHESTATS) {_cacheStats.opHit++;}
	  return(*entry).res;
	}
      debug(CACHESTATS) {_cacheStats.opMiss++;}

      if(LEVEL(l) == LEVEL(r))
	{
	  PUSHREF(appquant_rec(LOW(l), LOW(r)));
	  PUSHREF(appquant_rec(HIGH(l), HIGH(r)));
	  if (INVARSET(LEVEL(l)))
	    res = apply_rec(READREF(2), READREF(1));
	  else
	    res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
	}

      else if(LEVEL(l) < LEVEL(r))
	{
	  PUSHREF(appquant_rec(LOW(l), r));
	  PUSHREF(appquant_rec(HIGH(l), r));
	  if (INVARSET(LEVEL(l)))
	    res = apply_rec(READREF(2), READREF(1));
	  else
	    res = bdd_makenode(LEVEL(l), READREF(2), READREF(1));
	  
	}
      else
	{
	  PUSHREF(appquant_rec(l, LOW(r)));
	  PUSHREF(appquant_rec(l, HIGH(r)));
	  if (INVARSET(LEVEL(r)))
	    res = apply_rec(READREF(2), READREF(1));
	  else
	    res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
	}

      POPREF(2);

      (*entry).a = l;
      (*entry).b = r;
      (*entry).c = appexid;
      (*entry).res = res;
    }

    return res;
  }

  int quant_rec(int r)
  {
    int res;

    if(r < 2 || LEVEL(r) > quantlast)
      return r;

    BddCacheData* entry = _quantCache.lookup(QUANTHASH(r));
    if((*entry).a == r &&(*entry).c == quantid)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    PUSHREF(quant_rec(LOW(r)));
    PUSHREF(quant_rec(HIGH(r)));

    if(INVARSET(LEVEL(r))) {
      res = apply_rec(READREF(2), READREF(1));
    }
    else {
      res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
    }

    POPREF(2);

    (*entry).a = r;
    (*entry).c = quantid;
    (*entry).res = res;

    return res;
  }

  int bdd_constrain(int f, int c)
  {
    int res;
    firstReorder = 1;

    CHECKa(f, BddFalse);
    CHECKa(c, BddFalse);

    _miscCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	INITREF();
	miscid = CACHEID_CONSTRAIN;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = constrain_rec(f, c);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int constrain_rec(int f, int c)
  {
    int res;

    if(c == 1)
      return f;
    if(f < 2)
      return f;
    if(c == f)
      return BDDONE;
    if(c == 0)
      return BDDZERO;

    BddCacheData* entry = _miscCache.lookup(CONSTRAINHASH(f, c));
    if((*entry).a == f &&(*entry).b == c &&(*entry).c == miscid)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    if(LEVEL(f) == LEVEL(c))
      {
	if(LOW(c) == 0)
	  res = constrain_rec(HIGH(f), HIGH(c));
	else if(HIGH(c) == 0)
	  res = constrain_rec(LOW(f), LOW(c));
	else
	  {
	    PUSHREF(constrain_rec(LOW(f), LOW(c)));
	    PUSHREF(constrain_rec(HIGH(f), HIGH(c)));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	    POPREF(2);
	  }
      }
    else if(LEVEL(f) < LEVEL(c))
      {
	PUSHREF(constrain_rec(LOW(f), c));
	PUSHREF(constrain_rec(HIGH(f), c));
	res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	POPREF(2);
      }
    else
      {
	if(LOW(c) == 0)
	  res = constrain_rec(f, HIGH(c));
	else if(HIGH(c) == 0)
	  res = constrain_rec(f, LOW(c));
	else {
	  PUSHREF(constrain_rec(f, LOW(c)));
	  PUSHREF(constrain_rec(f, HIGH(c)));
	  res = bdd_makenode(LEVEL(c), READREF(2), READREF(1));
	  POPREF(2);
	}
      }

    (*entry).a = f;
    (*entry).b = c;
    (*entry).c = miscid;
    (*entry).res = res;

    return res;
  }

  int bdd_compose(int f, int g, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(f, BddFalse);
    CHECKa(g, BddFalse);
    if(var < 0 || var >= _varNum)
      {
	bdd_error(BddError.BDD_VAR);
	return BddFalse;
      }

    _applyCache.initIfNull(_cacheSize);
    _iteCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	INITREF();
	composelevel = _var2Level[var];
	replaceid = (composelevel << 2) | CACHEID_COMPOSE;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = compose_rec(f, g);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int compose_rec(int f, int g)
  {
    int res;

    if(LEVEL(f) > composelevel)
      return f;

    BddCacheData* entry = _replaceCache.lookup(COMPOSEHASH(f, g));
    if((*entry).a == f &&(*entry).b == g &&(*entry).c == replaceid)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    if(LEVEL(f) < composelevel)
      {
	if(LEVEL(f) == LEVEL(g))
	  {
	    PUSHREF(compose_rec(LOW(f), LOW(g)));
	    PUSHREF(compose_rec(HIGH(f), HIGH(g)));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	  }
	else if(LEVEL(f) < LEVEL(g))
	  {
	    PUSHREF(compose_rec(LOW(f), g));
	    PUSHREF(compose_rec(HIGH(f), g));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	  }
	else
	  {
	    PUSHREF(compose_rec(f, LOW(g)));
	    PUSHREF(compose_rec(f, HIGH(g)));
	    res = bdd_makenode(LEVEL(g), READREF(2), READREF(1));
	  }
	POPREF(2);
      }
    else
      /*if(LEVEL(f) == composelevel) changed 2-nov-98 */
      {
	res = ite_rec(g, HIGH(f), LOW(f));
      }

    (*entry).a = f;
    (*entry).b = g;
    (*entry).c = replaceid;
    (*entry).res = res;

    return res;
  }

  int bdd_veccompose(int f, BddPair pair)
  {
    int res;
    firstReorder = 1;

    CHECKa(f, BddFalse);

    _applyCache.initIfNull(_cacheSize);
    _iteCache.initIfNull(_cacheSize);
    _replaceCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	INITREF();
	replacepair = pair.result;
	replaceid = (pair.id << 2) | CACHEID_VECCOMPOSE;
	replacelast = pair.last;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = veccompose_rec(f);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int veccompose_rec(int f)
  {
    int res;

    if(LEVEL(f) > replacelast)
      return f;

    BddCacheData* entry = _replaceCache.lookup(VECCOMPOSEHASH(f));
    if((*entry).a == f &&(*entry).c == replaceid)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    PUSHREF(veccompose_rec(LOW(f)));
    PUSHREF(veccompose_rec(HIGH(f)));
    res = ite_rec(replacepair[LEVEL(f)], READREF(1), READREF(2));
    POPREF(2);

    (*entry).a = f;
    (*entry).c = replaceid;
    (*entry).res = res;

    return res;
  }

  int bdd_exist(int r, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(r, BddFalse);
    CHECKa(var, BddFalse);

    if(var < 2) /* Empty set */
      return r;

    _applyCache.initIfNull(_cacheSize);
    _quantCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	if(varset2vartable(var) < 0)
	  return BddFalse;

	INITREF();

	quantid =(var << 3) | CACHEID_EXIST; /* FIXME: range */
	applyop = BddOp.OR;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = quant_rec(r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; //  again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int bdd_forall(int r, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(r, BddFalse);
    CHECKa(var, BddFalse);

    if(var < 2) /* Empty set */
      return r;

    _applyCache.initIfNull(_cacheSize);
    _quantCache.initIfNull(_cacheSize);

  again:
    while(true) {
      try {
	if(varset2vartable(var) < 0)
	  return BddFalse;

	INITREF();
	quantid =(var << 3) | CACHEID_FORALL;
	applyop = BddOp.AND;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = quant_rec(r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; //  again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int bdd_unique(int r, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(r, BddFalse);
    CHECKa(var, BddFalse);

    if(var < 2) /* Empty set */
      return r;

    _applyCache.initIfNull(_cacheSize);
    _quantCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	if (varset2vartable(var) < 0)
	  return BddFalse;

	INITREF();
	quantid =(var << 3) | CACHEID_UNIQUE;
	applyop = BddOp.XOR;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = quant_rec(r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int bdd_restrict(int r, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(r, BddFalse);
    CHECKa(var, BddFalse);

    if(var < 2) /* Empty set */
      return r;

    _miscCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	if(varset2svartable(var) < 0)
	  return BddFalse;
	INITREF();
	miscid =(var << 3) | CACHEID_RESTRICT;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = restrict_rec(r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int restrict_rec(int r)
  {
    int res;

    if(r < 2 || LEVEL(r) > quantlast)
      return r;

    BddCacheData* entry = _miscCache.lookup(RESTRHASH(r, miscid));
    if((*entry).a == r &&(*entry).c == miscid)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    if(INSVARSET(LEVEL(r)))
      {
	if(quantvarset[LEVEL(r)] > 0)
	  res = restrict_rec(HIGH(r));
	else
	  res = restrict_rec(LOW(r));
      }
    else
      {
	PUSHREF(restrict_rec(LOW(r)));
	PUSHREF(restrict_rec(HIGH(r)));
	res = bdd_makenode(LEVEL(r), READREF(2), READREF(1));
	POPREF(2);
      }

    (*entry).a = r;
    (*entry).c = miscid;
    (*entry).res = res;

    return res;
  }

  int bdd_simplify(int f, int d)
  {
    int res;
    firstReorder = 1;

    CHECKa(f, BddFalse);
    CHECKa(d, BddFalse);

    _applyCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	INITREF();
	applyop = BddOp.OR;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = simplify_rec(f, d);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int simplify_rec(int f, int d)
  {
    int res;

    if(d == 1 || f < 2)
      return f;
    if(d == f)
      return BDDONE;
    if(d == 0)
      return BDDZERO;

    BddCacheData* entry = _applyCache.lookup(APPLYHASH(f, d, BddOp.SIMPLIFY));

    if((*entry).a == f &&(*entry).b == d &&(*entry).c == BddOp.SIMPLIFY)
      {
	debug(CACHESTATS) {_cacheStats.opHit++;}
	return(*entry).res;
      }
    debug(CACHESTATS) {_cacheStats.opMiss++;}

    if(LEVEL(f) == LEVEL(d))
      {
	if(LOW(d) == 0)
	  res = simplify_rec(HIGH(f), HIGH(d));
	else if(HIGH(d) == 0)
	  res = simplify_rec(LOW(f), LOW(d));
	else
	  {
	    PUSHREF(simplify_rec(LOW(f), LOW(d)));
	    PUSHREF(simplify_rec(HIGH(f), HIGH(d)));
	    res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	    POPREF(2);
	  }
      }
    else if(LEVEL(f) < LEVEL(d))
      {
	PUSHREF(simplify_rec(LOW(f), d));
	PUSHREF(simplify_rec(HIGH(f), d));
	res = bdd_makenode(LEVEL(f), READREF(2), READREF(1));
	POPREF(2);
      }
    else /* LEVEL(d) < LEVEL(f) */
      {
	PUSHREF(or_rec(LOW(d), HIGH(d))); /* Exist quant */
	res = simplify_rec(f, READREF(1));
	POPREF(1);
      }

    (*entry).a = f;
    (*entry).b = d;
    (*entry).c = BddOp.SIMPLIFY;
    (*entry).res = res;

    return res;
  }

  int bdd_support(int r) {
    import core.stdc.string: memset;
    static int supportSize = 0;
    int n;
    int res = 1;

    CHECKa(r, BddFalse);

    if(r < 2)
      return BddTrue;

    /* On-demand allocation of support set */
    if(supportSize < _varNum) {
	if ((supportSet= cast (int*) malloc(_varNum * int.sizeof)) is null) {
	  bdd_error(BddError.BDD_MEMORY);
	  return BddFalse;
	}
	memset(supportSet, 0, _varNum*int.sizeof);
	supportSize = _varNum;
	supportID = 0;
      }

    /* Update global variables used to speed up bdd_support()
     * - instead of always memsetting support to zero, we use
     *   a change counter.
     * - and instead of reading the whole array afterwards, we just
     *   look from 'min' to 'max' used BDD variables.
     */
    if(supportID == 0x0FFFFFFF) {
      /* We probably don't get here -- but let's just be sure */
      memset(supportSet, 0, _varNum * int.sizeof);
      supportID = 0;
    }
    ++supportID;
    supportMin = LEVEL(r);
    supportMax = supportMin;

    support_rec(r, supportSet);
    bdd_unmark(r);

    bdd_disable_reorder();

    for (n = supportMax; n >= supportMin; --n) {
      if (supportSet[n] == supportID) {
	int tmp;
	// res is an int -- so delref and addref are required
	addRef(res);
	tmp = bdd_makenode(n, 0, res);
	delRef(res);
	res = tmp;
      }
    }

    bdd_enable_reorder();

    return res;
  }

  void support_rec(int r, int* support)
  {

    if(r < 2)
      return;

    if(MARKED(r) || LOW(r) == INVALID_BDD)
      return;

    support[LEVEL(r)] = supportID;

    if(LEVEL(r) > supportMax)
      supportMax = LEVEL(r);

    SETMARK(r);

    support_rec(LOW(r), support);
    support_rec(HIGH(r), support);
  }

  int bdd_appall(int l, int r, int opr, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(l, BddFalse);
    CHECKa(r, BddFalse);
    CHECKa(var, BddFalse);

    if(opr < 0 || opr > BddOp.INVIMP)
      {
	bdd_error(BddError.BDD_OP);
	return BddFalse;
      }

    if(var < 2) /* Empty set */
      return bdd_apply(l, r, opr);

    _applyCache.initIfNull(_cacheSize);
    _appexCache.initIfNull(_cacheSize);
    _quantCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	if(varset2vartable(var) < 0)
	  return BddFalse;

	INITREF();
	applyop = BddOp.AND;
	appexop = opr;
	appexid =(var << 5) | (appexop << 1) | 1; /* FIXME: range! */
	quantid =(appexid << 3) | CACHEID_APPAL;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = appquant_rec(l, r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();

	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int bdd_appuni(int l, int r, int opr, int var)
  {
    int res;
    firstReorder = 1;

    CHECKa(l, BddFalse);
    CHECKa(r, BddFalse);
    CHECKa(var, BddFalse);

    if(opr < 0 || opr > BddOp.INVIMP)
      {
	bdd_error(BddError.BDD_OP);
	return BddFalse;
      }

    if(var < 2) /* Empty set */
      return bdd_apply(l, r, opr);

    _applyCache.initIfNull(_cacheSize);
    _appexCache.initIfNull(_cacheSize);
    _quantCache.initIfNull(_cacheSize);

    // again:
    while(true) {
      try {
	if (varset2vartable(var) < 0)
	  return BddFalse;

	INITREF();
	applyop = BddOp.XOR;
	appexop = opr;
	appexid = (var << 5) | (appexop << 1) | 1; /* FIXME: range! */
	quantid = (appexid << 3) | CACHEID_APPUN;

	if(firstReorder == 0)
	  bdd_disable_reorder();
	res = appquant_rec(l, r);
	if(firstReorder == 0)
	  bdd_enable_reorder();
      }
      catch(ReorderException x)
	{
	  bdd_checkreorder();
	  if(--firstReorder == 0)
	    continue; // again;
	  res = BDDZERO;
	  /* avoid warning about res being uninitialized */
	}
      break;
    }

    checkresize();
    return res;
  }

  int bdd_satone(int r)
  {
    int res;

    CHECKa(r, BddFalse);
    if(r < 2)
      return r;

    bdd_disable_reorder();

    INITREF();
    res = satone_rec(r);

    bdd_enable_reorder();

    checkresize();
    return res;
  }

  int satone_rec(int r)
  {
    if(r < 2)
      return r;

    if(LOW(r) == 0)
      {
	int res = satone_rec(HIGH(r));
	return PUSHREF(bdd_makenode(LEVEL(r), BDDZERO, res));
      }
    else
      {
	int res = satone_rec(LOW(r));
	return PUSHREF(bdd_makenode(LEVEL(r), res, BDDZERO));
      }
  }

  int bdd_satoneset(int r, int var, int pol)
  {
    int res;

    CHECKa(r, BddFalse);
    if(r == 0)
      return r;
    if(pol > 1)
      {
	bdd_error(BddError.BDD_ILLBDD);
	return BddFalse;
      }

    bdd_disable_reorder();

    INITREF();
    satPolarity = pol;
    res = satoneset_rec(r, var);

    bdd_enable_reorder();

    checkresize();
    return res;
  }

  int satoneset_rec(int r, int var)
  {
    if(r < 2 && var < 2)
      return r;

    if(LEVEL(r) < LEVEL(var))
      {
	if(LOW(r) == 0)
	  {
	    int res = satoneset_rec(HIGH(r), var);
	    return PUSHREF(bdd_makenode(LEVEL(r), BDDZERO, res));
	  }
	else {
	  int res = satoneset_rec(LOW(r), var);
	  return PUSHREF(bdd_makenode(LEVEL(r), res, BDDZERO));
	}
      }
    else if(LEVEL(var) < LEVEL(r))
      {
	int res = satoneset_rec(r, HIGH(var));
	if(satPolarity == BDDONE)
	  return PUSHREF(bdd_makenode(LEVEL(var), BDDZERO, res));
	else
	  return PUSHREF(bdd_makenode(LEVEL(var), res, BDDZERO));
      }
    else /* LEVEL(r) == LEVEL(var) */
      {
	if(LOW(r) == 0)
	  {
	    int res = satoneset_rec(HIGH(r), HIGH(var));
	    return PUSHREF(bdd_makenode(LEVEL(r), BDDZERO, res));
	  }
	else
	  {
	    int res = satoneset_rec(LOW(r), HIGH(var));
	    return PUSHREF(bdd_makenode(LEVEL(r), res, BDDZERO));
	  }
      }

  }

  int bdd_randsatone(double rnd, ref double[uint] dist, int r)
  {
    // import std.stdio;
    // writeln(rnd, dist);
    int res;
    // int v;

    CHECKa(r, BddFalse);
    if(r == 0)
      return 0;

    bdd_disable_reorder();

    INITREF();
    res = randsatone_rec(rnd, dist, r);

    bdd_enable_reorder();

    checkresize();
    return res;
  }

  int randsatone_rec(double rnd, ref double[uint] dist, int r)
  {
    if(r < 2)
      return r;

    double limit = dist[r];

    if (rnd < limit)
      {
	if(LOW(r) != 0)
	  {
	    // writeln("LL r: ", r, " dist[r]: ", dist[r], " rnd: ", rnd);
	    int res = randsatone_rec(rnd/limit, dist, LOW(r));
	    return PUSHREF(bdd_makenode(LEVEL(r), res, 0));
	  }
	else
	  {
	    writeln("-- r: ", r, " dist[r]: ", dist[r], " rnd: ", rnd);
	    assert(false, "dist table gives wrong path");
	  }
      }
    else
      {
	if(HIGH(r) != 0)
	  {

	    // writeln("HH r: ", r, " dist[r]: ", dist[r], " rnd: ", rnd);
	    int res = randsatone_rec((rnd - limit)/(1.0 - limit),
				     dist, HIGH(r));
	    return PUSHREF(bdd_makenode(LEVEL(r), 0, res));
	  }
	else
	  {
	    writeln("++ r: ", r, " dist[r]: ", dist[r], " rnd: ", rnd);
	    assert(false, "dist table gives wrong path");
	  }
      }
  }

  int bdd_fullsatone(int r)
  {
    int res;
    int v;

    CHECKa(r, BddFalse);
    if(r == 0)
      return 0;

    bdd_disable_reorder();

    INITREF();
    res = fullsatone_rec(r);

    for(v = LEVEL(r) - 1; v >= 0; v--)
      {
	res = PUSHREF(bdd_makenode(v, res, 0));
      }

    bdd_enable_reorder();

    checkresize();
    return res;
  }

  int fullsatone_rec(int r)
  {
    if(r < 2)
      return r;

    if(LOW(r) != 0)
      {
	int res = fullsatone_rec(LOW(r));
	int v;

	for(v = LEVEL(LOW(r)) - 1; v > LEVEL(r); v--)
	  {
	    res = PUSHREF(bdd_makenode(v, 0, res));
	  }

	return PUSHREF(bdd_makenode(LEVEL(r), res, 0));
      }
    else
      {
	int res = fullsatone_rec(HIGH(r));
	int v;

	for(v = LEVEL(HIGH(r)) - 1; v > LEVEL(r); v--)
	  {
	    res = PUSHREF(bdd_makenode(v, 0, res));
	  }

	return PUSHREF(bdd_makenode(LEVEL(r), 0, res));
      }
  }

  void bdd_gbc_rehash()
  {
    int n;

    _freePos = 0;
    _freeNum = 0;

    for(n = _nodeSize - 1; n >= 2; n--)
      {
	if(LOW(n) != INVALID_BDD)
	  {
	    int hash2;

	    hash2 = NODEHASH(LEVEL(n), LOW(n), HIGH(n));
	    SETNEXT(n, HASH(hash2));
	    SETHASH(hash2, n);
	  } else {
	  SETNEXT(n, _freePos);
	  _freePos = n;
	  _freeNum++;
	}
      }
  }


  static final long clock()
  {
    return Clock.currStdTime()/10000;
  }

  void INITREF()
  {
    _refStackTop = 0;
  }

  int PUSHREF(int a)
  {
    _refStack[_refStackTop++] = a;
    return a;
  }

  int READREF(int a)
  {
    return _refStack[_refStackTop - a];
  }

  void POPREF(int a)
  {
    _refStackTop -= a;
  }

  int bdd_nodecount(int r)
  {
    int num = 0;

    CHECK(r);

    bdd_markcount(r, num);
    bdd_unmark(r);

    return num;
  }

  int bdd_anodecount(int[] r)
  {
    int n;
    int cou = 0;

    for(n = 0; n < r.length; n++)
      bdd_markcount(r[n], cou);

    for(n = 0; n < r.length; n++)
      bdd_unmark(r[n]);

    return cou;
  }

  int[] bdd_varprofile(int r)
  {
    import core.stdc.string : memset, memcpy;
    CHECK(r);

    int[] varprofile = new int[](_varNum);
    memset(varprofile.ptr, 0, int.sizeof * _varNum);

    varprofile_rec(r, varprofile);
    bdd_unmark(r);
    return varprofile;
  }

  void varprofile_rec(int r, int[] varprofile)
  {

    if(r < 2)
      return;

    if(MARKED(r))
      return;

    varprofile[_level2Var[LEVEL(r)]]++;
    SETMARK(r);

    varprofile_rec(LOW(r), varprofile);
    varprofile_rec(HIGH(r), varprofile);
  }

  double bdd_pathcount(int r)
  {
    CHECK(r);

    miscid = CACHEID_PATHCOU;

    _countCache.initIfNull(_cacheSize);

    return bdd_pathcount_rec(r);
  }

  double bdd_pathcount_rec(int r)
  {
    double size;

    if(r == 0)
      return 0.0;
    if(r == 1)
      return 1.0;

    BddCacheData* entry = _countCache.lookup(PATHCOUHASH(r));
    if((*entry).a == r &&(*entry).c == miscid)
      return(*entry).dres;

    size = bdd_pathcount_rec(LOW(r)) + bdd_pathcount_rec(HIGH(r));

    (*entry).a = r;
    (*entry).c = miscid;
    (*entry).dres = size;

    return size;
  }

  double bdd_log2pathcount(int r)
  {
    CHECK(r);

    miscid = CACHEID_LOG2PATHCOU;

    _log2countCache.initIfNull(_cacheSize);

    return bdd_log2pathcount_rec(r);
  }

  double log2add(double a, double b) {
    // well, suppose that x >= y, and that we are using the natural base:
    // log(x + y) = log(x * (1 + y/x)) = log(x) + log(1 + y/x)
    // y/x = exp(log(y/x)) = exp(log(y) - log(x))
    // log(x + y) = log(x) + log(1 + exp(log(y) - log(x)))
    auto x = max(a, b);
    auto y = min(a, b);
    return (x + log2(1 + (2.00 ^^ (y - x))));
  }

  double bdd_log2pathcount_rec(int r)
  {
    if(r == 0)
      return log2(0.0);		// -inf
    if(r == 1)
      return log2(1.0);		// 0

    BddCacheData* entry = _log2countCache.lookup(LOG2PATHCOUHASH(r));
    if((*entry).a == r &&(*entry).c == miscid)
      return(*entry).dres;

    auto size = log2add(bdd_log2pathcount_rec(LOW(r)),
			bdd_log2pathcount_rec(HIGH(r)));

    (*entry).a = r;
    (*entry).c = miscid;
    (*entry).dres = size;

    return size;
  }

  void bdd_allsat(int r, byte[][] result)
  {
    int v;

    CHECK(r);

    if ((allsatProfile = cast(byte*) malloc(_varNum)) is null) {
      bdd_error(BddError.BDD_MEMORY);
      return;
    }

    for(v = LEVEL(r) - 1; v >= 0; --v) {
      allsatProfile[_level2Var[v]] = -1;
    }

    INITREF();

    allsat_rec(r, result);

    free(allsatProfile);
  }

  void allsat_rec(int r, byte[][] result) {
    if (r == 1) {
      byte[] b = allsatProfile[0.._varNum].dup;
      result ~= b;
      return;
    }

    if (r == 0) {
      return;
    }

    if (!LOW(r) == 0) {
      int v;

      allsatProfile[_level2Var[LEVEL(r)]] = 0;

      for (v = LEVEL(LOW(r)) - 1; v > LEVEL(r); --v) {
	allsatProfile[_level2Var[v]] = -1;
      }

      allsat_rec(LOW(r), result);
    }

    if(!HIGH(r) == 0) {
      int v;

      allsatProfile[_level2Var[LEVEL(r)]] = 1;

      for (v = LEVEL(HIGH(r)) - 1; v > LEVEL(r); --v) {
	allsatProfile[_level2Var[v]] = -1;
      }

      allsat_rec(HIGH(r), result);
    }
  }

  void bdd_satdist(int r, ref double[uint] dist)
  {
    // make sure that bdd_satcount has already initialized the sizes
    version(NOLOG2) {
      bdd_satcount(r);
    }
    else {
      bdd_log2satcount(r);
    }
    satdist_rec(r, dist);
  }

  double bdd_log2satcount(int r)
  {
    double size = 1;

    CHECK(r);

    _log2countCache.initIfNull(_cacheSize);

    miscid = CACHEID_LOG2SATCOU;
    size = LEVEL(r);

    // import std.stdio;
    // double s = satcount_rec(r);
    // writeln("s is: ", s);
    // writeln("level of r is: ", LEVEL(r));

    return size + log2satcount_rec(r);
  }

  double bdd_satcount(int r)
  {
    double size = 1;

    CHECK(r);

    _countCache.initIfNull(_cacheSize);

    miscid = CACHEID_SATCOU;
    size = 2.0 ^^ LEVEL(r);

    // import std.stdio;
    // double s = satcount_rec(r);
    // writeln("s is: ", s);
    // writeln("level of r is: ", LEVEL(r));

    return size * satcount_rec(r);
  }

  double bdd_satcountset(int r, int varset)
  {
    double unused = _varNum;
    int n;

    if(varset < 2 || r == 0) /* empty set */
      return 0.0;

    for(n = varset; n > 1; n = HIGH(n))
      unused--;

    unused = bdd_satcount(r) / cast(double)(2.00 ^^ unused);

    return unused >= 1.0 ? unused : 1.0;
  }

  void satdist_rec(int root, ref double[uint] dist)
  {
    if(root < 2) return;	// always take the path leading to one

    if(root in dist) return;

    version(NOLOG2) {
      double lCount = (2.0 ^^ (LEVEL(LOW(root)) - LEVEL(root) - 1)) *
	satcount_rec(LOW(root));
      double hCount = (2.0 ^^ (LEVEL(HIGH(root)) - LEVEL(root) - 1)) *
	satcount_rec(HIGH(root));

      double limit = lCount/(lCount + hCount);
      // import std.stdio;
      // writeln("lCount: ", lCount, " hCount: ", hCount, " limit: ", limit);
    }
    else {
      auto log2l = log2satcount_rec(LOW(root)) + LEVEL(LOW(root)) - LEVEL(root) - 1;
      auto log2h = log2satcount_rec(HIGH(root)) + LEVEL(HIGH(root)) - LEVEL(root) - 1;

      auto limit = 1.0 / (1.0 + 2.0 ^^ (log2h - log2l));
      // import std.stdio;
      // writeln("log2l: ", log2l, " log2h: ", log2h, " limit: ", limit);
    }      

    dist[root] = limit;

    satdist_rec(LOW(root), dist);
    satdist_rec(HIGH(root), dist);
  }


  double log2satcount_rec(int root)
  {
    if(root < 2)
      return log2(root);

    BddCacheData* entry = _log2countCache.lookup(LOG2SATCOUHASH(root));
    if((*entry).a == root &&(*entry).c == miscid)
      return(*entry).dres;

    auto llr = LEVEL(LOW(root)) - LEVEL(root) - 1;
    auto lhr = LEVEL(HIGH(root)) - LEVEL(root) - 1;

    auto size = log2add(llr + log2satcount_rec(LOW(root)),
			lhr + log2satcount_rec(HIGH(root)));

    (*entry).a = root;
    (*entry).c = miscid;
    (*entry).dres = size;

    return size;
  }

  double satcount_rec(int root)
  {
    double size, s;

    if(root < 2)
      return root;

    BddCacheData* entry = _countCache.lookup(SATCOUHASH(root));
    if((*entry).a == root &&(*entry).c == miscid)
      return(*entry).dres;

    size = 0;
    s = 1;

    s *= 2.0 ^^(LEVEL(LOW(root)) - LEVEL(root) - 1);
    size += s * satcount_rec(LOW(root));

    s = 1;
    s *= 2.0 ^^(LEVEL(HIGH(root)) - LEVEL(root) - 1);
    size += s * satcount_rec(HIGH(root));

    (*entry).a = root;
    (*entry).c = miscid;
    (*entry).dres = size;

    return size;
  }

  void bdd_gbc()
  {
    int r;
    int n;
    long c2, c1 = clock();

    if(gbc_enabled == true) 
      {
	//if(gbc_handler != NULL)
	// {
	gcstats.nodes = _nodeSize;
	gcstats.freenodes = _freeNum;
	gcstats.time = 0;
	gcstats.sumtime = _gbcClock;
	gcstats.num = _gbCollectNum;
	gbc_handler(true, gcstats);
	// }
	for(r = 0; r < _refStackTop; r++)
	  bdd_mark(_refStack[r]);

	for(n = 0; n < _nodeSize; n++)
	  {
	    if(HASREF(n))
	      bdd_mark(n);
	    SETHASH(n, 0);
	  }

	_freePos = 0;
	_freeNum = 0;

	for(n = _nodeSize - 1; n >= 2; n--)
	  {

	    if(MARKED(n) && LOW(n) != INVALID_BDD)
	      {
		int hash2;

		UNMARK(n);
		hash2 = NODEHASH(LEVEL(n), LOW(n), HIGH(n));
		SETNEXT(n, HASH(hash2));
		SETHASH(hash2, n);
	      } else {
	      SETLOW(n, INVALID_BDD);
	      SETNEXT(n, _freePos);
	      _freePos = n;
	      _freeNum++;
	    }
	  }

	debug(DONT_FLUSH_CACHE_ON_GC)
	  {
	    bdd_operator_clean();
	  } else {
	  bdd_operator_reset();
	}

	c2 = clock();
	_gbcClock += c2 - c1;
	_gbCollectNum++;

	//if(gbc_handler != NULL)
	{
	  gcstats.nodes = _nodeSize;
	  gcstats.freenodes = _freeNum;
	  gcstats.time = c2 - c1;
	  gcstats.sumtime = _gbcClock;
	  gcstats.num = _gbCollectNum;
	  gbc_handler(false, gcstats);
	}

	//validate_all();
      }
  }

  int addRef(int root)
  {
    if(root == INVALID_BDD)
      bdd_error(BddError.BDD_BREAK); /* distinctive */
    if(root < 2 || !isRunning())
      return root;
    if(root >= _nodeSize) {
      return bdd_error(BddError.BDD_ILLBDD);
    }
    if(LOW(root) == INVALID_BDD) {
      return bdd_error(BddError.BDD_ILLBDD);
    }

    INCREF(root);

    debug(BUDDY) {writeln("INCREF(", root, ") = ",GETREF(root));}
    return root;
  }

  int delRef(int root)
  {
    if(root == INVALID_BDD) {
      bdd_error(BddError.BDD_BREAK); /* distinctive */
    }
    if(root < 2 || !isRunning()) {
      return root;
    }
    if(root >= _nodeSize) {
      return bdd_error(BddError.BDD_ILLBDD);
    }
    if(LOW(root) == INVALID_BDD) {
      return bdd_error(BddError.BDD_ILLBDD);
    }

    /* if the following line is present, fails there much earlier */
    if(!HASREF(root)) {
      bdd_error(BddError.BDD_BREAK); /* distinctive */
    }
    
    DECREF(root);

    debug(BUDDY) {writeln("DECREF(", root, ") = ", GETREF(root));}
    return root;
  }

  void bdd_mark(int i)
  {

    if(i < 2)
      return;

    if(MARKED(i) || LOW(i) == INVALID_BDD)
      return;

    SETMARK(i);

    bdd_mark(LOW(i));
    bdd_mark(HIGH(i));
  }

  void bdd_markcount(int i, ref int cou)
  {

    if(i < 2)
      return;

    if(MARKED(i) || LOW(i) == INVALID_BDD)
      return;

    SETMARK(i);
    cou += 1;

    bdd_markcount(LOW(i), cou);
    bdd_markcount(HIGH(i), cou);
  }

  void bdd_unmark(int i)
  {

    if(i < 2)
      return;

    if(!MARKED(i) || LOW(i) == INVALID_BDD)
      return;
    UNMARK(i);

    bdd_unmark(LOW(i));
    bdd_unmark(HIGH(i));
  }


  int bdd_makenode(uint level, int low, int high)
  {
    int hash;
    int res;

    debug(CACHESTATS) {_cacheStats.uniqueAccess++;}

    /* check whether childs are equal */
    if(low == high)
      return low;

    /* Try to find an existing node of this kind */
    hash = NODEHASH(level, low, high);
    res = _nodes[hash].hash;

    while(res != 0)
      {
	if(LEVEL(res) == level
	   && LOW(res) == low && HIGH(res) == high)
	  {
	    debug(CACHESTATS) {_cacheStats.uniqueHit++;}
	    return res;
	  }

	res = _nodes[res].next;
	debug(CACHESTATS) {_cacheStats.uniqueChain++;}
      }

    /* No existing node => build one */
    debug(CACHESTATS) {_cacheStats.uniqueMiss++;}

    /* Any free _nodes to use ? */
    if(_freePos == 0)
      {
	if(_errorCond != 0)
	  return 0;

	/* Try to allocate more _nodes */
	bdd_gbc();

	if((_nodeSize - _freeNum) >= _usedNodesNextReorder  &&
	   bdd_reorder_ready())
	  {
	    throw new ReorderException();
	  }

	if((_freeNum * 100) / _nodeSize <= _minFreeNodes)
	  {
	    bdd_noderesize(true);
	    hash = NODEHASH(level, low, high);
	  }

	/* Panic if that is not possible */
	if(_freePos == 0)
	  {
	    bdd_error(BddError.BDD_NODENUM);
	    _errorCond = abs(BddError.BDD_NODENUM);
	    return 0;
	  }
      }

    /* Build new node */
    res = _freePos;
    _freePos = _nodes[_freePos].next;
    --_freeNum;
    ++_produced;

    _nodes[res].levelAndMark = level;
    _nodes[res].low = low;
    _nodes[res].high = high;

    /* Insert node */
    _nodes[res].next = _nodes[hash].hash;
    _nodes[hash].hash =  res;

    return res;
  }

  int bdd_noderesize(bool doRehash)
  {
    int oldsize = _nodeSize;
    int newsize = _nodeSize;

    if(_maxNodeSize > 0)
      {
	if(newsize >= _maxNodeSize)
	  return -1;
      }

    if(increasefactor > 0)
      {
	newsize += cast(int)(newsize * increasefactor);
      } else {
      newsize = newsize << 1;
    }

    if(_maxNodeIncr > 0)
      {
	if(newsize > oldsize + _maxNodeIncr)
	  newsize = oldsize + _maxNodeIncr;
      }

    if(_maxNodeSize > 0)
      {
	if(newsize > _maxNodeSize)
	  newsize = _maxNodeSize;
      }

    return doResize(doRehash, oldsize, newsize);
  }

  int setNodeTableSize(int size)
  {
    int old = _nodeSize;
    doResize(true, old, size);
    return old;
  }

  int doResize(bool doRehash, int oldsize, int newsize)
  {
    newsize = primeLte(newsize);

    if(oldsize > newsize) return 0;

    resize_handler(oldsize, newsize);

    _nodes.length = newsize;

    if(doRehash)
      for(int n = 0; n < oldsize; n++)
	SETHASH(n, 0);

    for(int n = oldsize; n < _nodeSize; n++)
      {
	SETLOW(n, INVALID_BDD);
	//SETREFCOU(n, 0);
	//SETHASH(n, 0);
	//SETLEVEL(n, 0);
	SETNEXT(n, n+1);
      }
    SETNEXT(_nodeSize-1, _freePos);
    _freePos = oldsize;
    _freeNum += _nodeSize - oldsize;

    if(doRehash)
      bdd_gbc_rehash();

    _resized = true;

    return 0;
  }

  protected void initialize(int initnodesize, int cs)
  {
    if(isRunning())
      bdd_error(BddError.BDD_RUNNING);

    _nodes.length = primeGte(initnodesize);

    _resized = false;

    for(int n = 0; n < _nodeSize; n++)
      {
	SETLOW(n, INVALID_BDD);
	//SETREFCOU(n, 0);
	//SETHASH(n, 0);
	//SETLEVEL(n, 0);
	SETNEXT(n, n+1);
      }
    SETNEXT(_nodeSize-1, 0);

    SETMAXREF(0);
    SETMAXREF(1);
    SETLOW(0, 0); SETHIGH(0, 0);
    SETLOW(1, 1); SETHIGH(1, 1);

    bdd_operator_init(cs);

    _freePos = 2;
    _freeNum = _nodeSize - 2;
    _running = true;
    _varNum = 0;
    _gbCollectNum = 0;
    _gbcClock = 0;
    _cacheSize = cs;
    _usedNodesNextReorder = _nodeSize;
    _maxNodeIncr = DEFAULTMAXNODEINC;

    _errorCond = 0;

    debug(CACHESTATS) {//_cacheStats = new CacheStats();
    }

    //bdd_gbc_hook(bdd_default_gbchandler);
    //bdd_error_hook(bdd_default_errhandler);
    //bdd_resize_hook(NULL);
    bdd_pairs_init();
    bdd_reorder_init();

    return;
  }

  /* Hash value modifiers to distinguish between entries in _miscCache */
  enum int CACHEID_CONSTRAIN = 0x0;
  enum int CACHEID_RESTRICT = 0x1;
  enum int CACHEID_SATCOU = 0x2;
  enum int CACHEID_SATCOULN = 0x3;
  enum int CACHEID_PATHCOU = 0x4;
  enum int CACHEID_LOG2PATHCOU = 0x5;
  enum int CACHEID_LOG2SATCOU = 0x5;

  /* Hash value modifiers for replace/compose */
  enum int CACHEID_REPLACE = 0x0;
  enum int CACHEID_COMPOSE = 0x1;
  enum int CACHEID_VECCOMPOSE = 0x2;

  /* Hash value modifiers for quantification */
  enum int CACHEID_EXIST = 0x0;
  enum int CACHEID_FORALL = 0x1;
  enum int CACHEID_UNIQUE = 0x2;
  enum int CACHEID_APPEX = 0x3;
  enum int CACHEID_APPAL = 0x4;
  enum int CACHEID_APPUN = 0x5;

  /* Number of bool operators */
  enum int OPERATOR_NUM = 11;

  /* Operator results - entry = left<<1 | right(left,right in {0,1}) */
  enum oprres =
    [ [ 0, 0, 0, 1 ], // and( & )
      [ 0, 1, 1, 0 ], // xor( ^ )
      [ 0, 1, 1, 1 ], // or( | )
      [ 1, 1, 1, 0 ], // nand
      [ 1, 0, 0, 0 ], // nor
      [ 1, 1, 0, 1 ], // implication( >> )
      [ 1, 0, 0, 1 ], // bi-implication
      [ 0, 0, 1, 0 ], // difference /greater than( - )( > )
      [ 0, 1, 0, 0 ], // less than( < )
      [ 1, 0, 1, 1 ], // inverse implication( << )
      [ 1, 1, 0, 0 ]  // not( ! )
      ];

  int applyop; /* Current operator for apply */
  int appexop; /* Current operator for appex */
  int appexid; /* Current cache id for appex */
  int quantid; /* Current cache id for quantifications */
  int* quantvarset; /* Current variable set for quant. */
  int quantvarsetID; /* Current id used in quantvarset */
  int quantlast; /* Current last variable to be quant. */
  int replaceid; /* Current cache id for replace */
  int* replacepair; /* Current replace pair */
  int replacelast; /* Current last var. level to replace */
  int composelevel; /* Current variable used for compose */
  int miscid; /* Current cache id for other results */
  int supportID; /* Current ID(true value) for support */
  int supportMin; /* Min. used level in support calc. */
  int supportMax; /* Max. used level in support calc. */
  int* supportSet; /* The found support set */
  BddCache _applyCache; /* Cache for apply results */
  BddCache _iteCache; /* Cache for ITE results */
  BddCache _quantCache; /* Cache for exist/forall results */
  BddCache _appexCache; /* Cache for appex/appall results */
  BddCache _replaceCache; /* Cache for replace results */
  BddCache _miscCache; /* Cache for other results */
  BddCache _countCache; /* Cache for count results */
  BddCache _log2countCache; /* Cache for count results */
  int cacheratio;
  int satPolarity;
  int firstReorder;
  /* Used instead of local variable in order
     to avoid compiler warning about 'first'
     being clobbered by setjmp */

  byte* allsatProfile; /* Variable profile for bdd_allsat() */

  void bdd_operator_init(int cachesize)
  {
    if(false)
      {
	_applyCache.init(cachesize);
	_iteCache.init(cachesize);
	_quantCache.init(cachesize);
	_appexCache.init(cachesize);
	_replaceCache.init(cachesize);
	_miscCache.init(cachesize);
	_countCache.init(cachesize);
	_log2countCache.init(cachesize);
      }

    quantvarsetID = 0;
    quantvarset = null;
    cacheratio = 0;
    supportSet = null;
  }

  void bdd_operator_done()
  {
    if (quantvarset !is null) {
      free(quantvarset);
    }

    _applyCache.done();
    _iteCache.done();
    _quantCache.done();
    _appexCache.done();
    _replaceCache.done();
    _miscCache.done();
    _countCache.done();
    _log2countCache.done();

    if (supportSet !is null) {
      free(supportSet);
    }
  }

  void bdd_operator_reset()
  {
    _applyCache.reset();
    _iteCache.reset();
    _quantCache.reset();
    _appexCache.reset();
    _replaceCache.reset();
    _miscCache.reset();
    _countCache.reset();
    _log2countCache.reset();
  }

  void bdd_operator_clean()
  {
    _applyCache.clean_ab(this);
    _iteCache.clean_abc(this);
    _quantCache.clean_a(this);
    _appexCache.clean_ab(this);
    _replaceCache.clean_ab(this);
    _miscCache.clean_ab(this);
    _countCache.clean_d(this);
    _log2countCache.clean_d(this);
  }

  void bdd_operator_varresize()
  {
    import core.stdc.string : memset, memcpy;

    if (quantvarset !is null) {
      free(quantvarset);
    }

    // #define NEW(t,n) ( (t*)malloc(sizeof(t)*(n)) )
    if ((quantvarset = cast(int*) malloc(int.sizeof * _varNum)) is null) {
      bdd_error(BddError.BDD_MEMORY);
    }

    memset(quantvarset, 0, int.sizeof * _varNum);
    quantvarsetID = 0;

    _countCache.reset();
    _log2countCache.reset();
  }

  int setCacheSize(int newcachesize)
  {
    int old = _cacheSize;
    _applyCache.resize(newcachesize);
    _iteCache.resize(newcachesize);
    _quantCache.resize(newcachesize);
    _appexCache.resize(newcachesize);
    _replaceCache.resize(newcachesize);
    _miscCache.resize(newcachesize);
    _countCache.resize(newcachesize);
    _log2countCache.resize(newcachesize);
    return old;
  }

  void bdd_operator_noderesize()
  {
    if(cacheratio > 0)
      {
	int newcachesize = _nodeSize / cacheratio;

	_applyCache.resize(newcachesize);
	_iteCache.resize(newcachesize);
	_quantCache.resize(newcachesize);
	_appexCache.resize(newcachesize);
	_replaceCache.resize(newcachesize);
	_miscCache.resize(newcachesize);
	_countCache.resize(newcachesize);
	_log2countCache.resize(newcachesize);
      }
  }


  BddPair pairs; /* List of all replacement pairs in use */
  int pairsid; /* Pair identifier */

  static final void remove(Object o)
  {
  }

  /*************************************************************************
   *************************************************************************/

  // pairs.c:50
  void bdd_pairs_init() {
    pairsid = 0;
    pairs = null;
  }

  // pairs.c:57
  void bdd_pairs_done() {
    BddPair p = pairs;
    int n;

    while (p !is null) {
      BddPair next = p.next;
      for(n = 0; n < _varNum; n++) {
	// result is an array of ints
	delRef(p.result[n]);
      }
      free(p.result);
      // p.result.length = 0;
      // free(p); // GC
      p = next;
    }
  }

  // pairs.c:74
  int update_pairsid() {
    pairsid += 1;

    if (pairsid == (int.max >> 2)) {
      BddPair p;
      pairsid = 0;
      for (p = pairs; p !is null; p = p.next) {
	p.id = pairsid++;
      }
      bdd_operator_reset();
    }
    return pairsid;
  }

  // pairs.c:91
  void bdd_register_pair(BddPair p) {
    p.next = pairs;
    pairs = p;
  }

  // pairs.c:98
  void bdd_pairs_vardown(int level) {
    BddPair p;

    for (p = pairs; p !is null; p = p.next) {
      int tmp = p.result[level];
      p.result[level] = p.result[level + 1];
      p.result[level + 1] = tmp;

      if(p.last == level) {
	p.last++;
      }
    }
  }

  // pairs.c:116
  void bdd_pairs_resize(int oldsize, int newsize) {

    for (BddPair p = pairs; p !is null; p = p.next) {
      if ((p.result =
	   cast(int*) realloc(p.result,
			      int.sizeof * newsize)) is null) {
	bdd_error(BddError.BDD_MEMORY);
      }

      for (int n = oldsize; n < newsize; n++) {
	p.result[n] = bdd_ithvar(_level2Var[n]);
      }
    }
  }

  // pairs.c:146
  BddPair bdd_newpair() {
    BddPair p = new BddPair();
   
    if ((p.result = cast(int*) malloc(int.sizeof * _varNum)) is null) {
      bdd_error(BddError.BDD_MEMORY);
      return null;
    }

    for (uint n=0; n<_varNum; n++) {
      p.result[n] = bdd_ithvar(_level2Var[n]);
    }

    p.id = update_pairsid();
    p.last = -1;
   
    bdd_register_pair(p);
    return p;
  }

  // pairs.c:196
  void bdd_setpair(BddPair pair, int oldvar, int newvar)
  {
    if (pair is null) {
      return;
    }

    if (oldvar < 0 || oldvar > _varNum - 1) {
      bdd_error(BddError.BDD_VAR);
    }
    if (newvar < 0 || newvar > _varNum - 1) {
      bdd_error(BddError.BDD_VAR);
    }
    // delref is required
    // BddPair.result is an array of ints
    delRef(pair.result[_var2Level[oldvar]]);
    pair.result[_var2Level[oldvar]] = bdd_ithvar(newvar);
    pair.id = update_pairsid();

    if (_var2Level[oldvar] > pair.last) {
      pair.last = _var2Level[oldvar];
    }
    return;
  }

  // pairs.c:217
  void bdd_setbddpair(BddPair pair, int oldvar, int newvar)
  {
    if (pair is null) {
      return;
    }

    CHECK(newvar);
    if(oldvar < 0 || oldvar >= _varNum) {
      bdd_error(BddError.BDD_VAR);
    }
    int oldlevel = _var2Level[oldvar];

    // delref is required
    // BddPair.result is an array of ints
    delRef(pair.result[oldlevel]);
    // newvar is an int
    pair.result[oldlevel] = addRef(newvar);
    pair.id = update_pairsid();

    if (oldlevel > pair.last) {
      pair.last = oldlevel;
    }

    return;
  }

  // pair.c:252
  void bdd_setpairs(BddPair pair, int *oldvar, int *newvar, int size) {
    if (pair is null) {
      return;
    }
   
    for (int n=0 ; n<size ; n++) {
      bdd_setpair(pair, oldvar[n], newvar[n]);
    }
  }

  // pair.c:266
  void bdd_setbddpairs(BddPair pair, int *oldvar, int *newvar, int size) {
    if (pair is null) {
      return;
    }
   
    for (uint n=0 ; n<size ; n++) {
      bdd_setbddpair(pair, oldvar[n], newvar[n]);
    }
  }

  // pair.c:289
  void bdd_freepair(BddPair p) {
    if (p is null) {
      return;
    }
   
    if (pairs !is p) {
      BddPair bp = pairs;
      while (bp !is null  &&  bp.next !is p) {
	bp = bp.next;
      }

      if (bp !is null) {
	bp.next = p.next;
      }
    }
    else {
      pairs = p.next;
    }

    for (int n=0 ; n<_varNum ; n++) {
      delRef( p.result[n] );
    }
    free(p.result);
    // free(p);
  }

  // pair.c:324
  void bdd_resetpair(BddPair p) {
    for (int n = 0; n < _varNum; n++) {
      p.result[n] = bdd_ithvar(_level2Var[n]);
    }
    p.last = 0;
  }

  void bdd_disable_reorder()
  {
    reorderdisabled = 1;
  }

  void bdd_enable_reorder()
  {
    reorderdisabled = 0;
  }

  void bdd_checkreorder()
  {
    bdd_reorder_auto();

    /* Do not reorder before twice as many _nodes have been used */
    _usedNodesNextReorder = 2 *(_nodeSize - _freeNum);

    /* And if very little was gained this time(< 20%) then wait until
     * even more _nodes(upto twice as many again) have been used */
    if(bdd_reorder_gain() < 20)
      _usedNodesNextReorder
	+=(_usedNodesNextReorder *(20 - bdd_reorder_gain()))
	/ 20;
  }

  enum ReorderMethod : byte { NONE = 0, WIN2 = 1,
      WIN2ITE = 2, SIFT = 3, SIFTITE = 4,
      WIN3 = 5, WIN3ITE = 6, RANDOM = 7 }

  bool bdd_reorder_ready()
  {
    if((bddreordermethod == ReorderMethod.NONE)
       ||(vartree is null)
       ||(bddreordertimes == 0)
       ||(reorderdisabled != 0))
      return false;
    return true;
  }

  void bdd_reorder(ReorderMethod method)
  {
    BddTree top;
    ReorderMethod savemethod = bddreordermethod;
    int savetimes = bddreordertimes;

    bddreordermethod = method;
    bddreordertimes = 1;

    if((top = bddtree_new(-1)) !is null)
      {
	if(reorder_init() >= 0)
	  {

	    usednum_before = _nodeSize - _freeNum;

	    top.first = 0;
	    top.last = bdd_varnum() - 1;
	    top.fixed = false;
	    top.next = null;
	    top.nextlevel = vartree;

	    reorder_block(top, method);
	    vartree = top.nextlevel;
	    remove(top);

	    usednum_after = _nodeSize - _freeNum;

	    reorder_done();
	    bddreordermethod = savemethod;
	    bddreordertimes = savetimes;
	  }
      }
  }

  BddTree bddtree_new(int id)
  {
    BddTree t = new BddTree();

    t.first = t.last = -1;
    t.fixed = true;
    t.next = t.prev = t.nextlevel = null;
    t.seq = null;
    t.id = id;
    return t;
  }

  BddTree reorder_block(BddTree t, ReorderMethod method)
  {
    BddTree dis;

    if(t is null)
      return null;

    if(!t.fixed /*ReorderMethod.FREE*/
       && t.nextlevel !is null)
      {
	switch(method)
	  {
	  case ReorderMethod.WIN2 :
	    t.nextlevel = reorder_win2(t.nextlevel);
	    break;
	  case ReorderMethod.WIN2ITE :
	    t.nextlevel = reorder_win2ite(t.nextlevel);
	    break;
	  case ReorderMethod.SIFT :
	    t.nextlevel = reorder_sift(t.nextlevel);
	    break;
	  case ReorderMethod.SIFTITE :
	    t.nextlevel = reorder_siftite(t.nextlevel);
	    break;
	  case ReorderMethod.WIN3 :
	    t.nextlevel = reorder_win3(t.nextlevel);
	    break;
	  case ReorderMethod.WIN3ITE :
	    t.nextlevel = reorder_win3ite(t.nextlevel);
	    break;
	  case ReorderMethod.RANDOM :
	    t.nextlevel = reorder_random(t.nextlevel);
	    break;
	  default:
	    throw new BddException("Unhandled Reorder Method");
	    // break;
	  }
      }

    for(dis = t.nextlevel; dis !is null; dis = dis.next)
      reorder_block(dis, method);

    if(t.seq !is null)
      {
	varseq_qsort(t.seq, 0, t.last-t.first + 1);
      }

    return t;
  }

  // due to Akihiko Tozawa
  void varseq_qsort(int[] target, int from, int to)
  {

    int x, i, j;

    switch(to - from)
      {
      case 0 :
	return;

      case 1 :
	return;

      case 2 :
	if(_var2Level[target[from]] <= _var2Level[target[from + 1]])
	  return;
	else {
	  x = target[from];
	  target[from] = target[from + 1];
	  target[from + 1] = x;
	}
	return;
      default:
	// do nothing
	break;
      }

    int r = target[from];
    int s = target[(from + to) / 2];
    int t = target[to - 1];

    if(_var2Level[r] <= _var2Level[s])
      {
	if(_var2Level[s] <= _var2Level[t])
	  {
	  } else if(_var2Level[r] <= _var2Level[t])
	  {
	    target[to - 1] = s;
	    target[(from + to) / 2] = t;
	  } else {
	  target[to - 1] = s;
	  target[from] = t;
	  target[(from + to) / 2] = r;
	}
      } else {
      if(_var2Level[r] <= _var2Level[t])
	{
	  target[(from + to) / 2] = r;
	  target[from] = s;
	} else if(_var2Level[s] <= _var2Level[t])
	{
	  target[to - 1] = r;
	  target[(from + to) / 2] = t;
	  target[from] = s;
	} else {
	target[to - 1] = r;
	target[from] = t;
      }
    }

    int mid = target[(from + to) / 2];

    for(i = from + 1, j = to - 1; i + 1 != j;)
      {
	if(target[i] == mid)
	  {
	    target[i] = target[i + 1];
	    target[i + 1] = mid;
	  }

	x = target[i];

	if(x <= mid)
	  i++;
	else {
	  x = target[--j];
	  target[j] = target[i];
	  target[i] = x;
	}
      }

    varseq_qsort(target, from, i);
    varseq_qsort(target, i + 1, to);
  }

  BddTree reorder_win2(BddTree t)
  {
    BddTree dis = t, first = t;

    if(t is null)
      return t;

    if(_verbose > 1)
      {
	writeln("Win2 start: ", reorder_nodenum(), " _nodes");
	// System.out.flush();
      }

    while(dis.next !is null)
      {
	int best = reorder_nodenum();
	blockdown(dis);

	if(best < reorder_nodenum())
	  {
	    blockdown(dis.prev);
	    dis = dis.next;
	  } else if(first == dis)
	  first = dis.prev;

	if(_verbose > 1)
	  {
	    write(".");
	    // System.out.flush();
	  }
      }

    if(_verbose > 1)
      {
	writeln();
	writeln("Win2 end: ", reorder_nodenum(), " _nodes");
	// System.out.flush();
      }

    return first;
  }

  BddTree reorder_win3(BddTree t)
  {
    BddTree dis = t, first = t;

    if(t is null)
      return t;

    if(_verbose > 1)
      {
	writeln("Win3 start: ", reorder_nodenum(), " _nodes");
	// System.out.flush();
      }

    while(dis.next !is null)
      {
	dis = reorder_swapwin3(dis, first);

	if(_verbose > 1)
	  {
	    write(".");
	    // System.out.flush();
	  }
      }

    if(_verbose > 1)
      {
	writeln();
	writeln("Win3 end: ", reorder_nodenum(), " _nodes");
	// System.out.flush();
      }

    return first;
  }

  BddTree reorder_win3ite(BddTree t)
  {
    BddTree dis = t, first = t;
    int lastsize;

    if(t is null)
      return t;

    if(_verbose > 1)
      writeln("Win3ite start: ", reorder_nodenum(), " _nodes");

    do {
      lastsize = reorder_nodenum();
      dis = first;

      while(dis.next !is null && dis.next.next !is null)
	{
	  dis = reorder_swapwin3(dis, first);

	  if(_verbose > 1)
	    {
	      write(".");
	      // System.out.flush();
	    }
	}

      if(_verbose > 1)
	writeln(" ", reorder_nodenum(), " _nodes");
    }
    while(reorder_nodenum() != lastsize);

    if(_verbose > 1)
      writeln("Win3ite end: ", reorder_nodenum(), " _nodes");

    return first;
  }

  BddTree reorder_swapwin3(BddTree dis, ref BddTree first)
  {
    bool setfirst = dis.prev is null;
    BddTree next = dis;
    int best = reorder_nodenum();

    if(dis.next.next is null) /* Only two blocks left => win2 swap */ {
      blockdown(dis.prev);

      if(best < reorder_nodenum())
	{
	  blockdown(dis.prev);
	  next = dis.next;
	} else {
	next = dis;
	if(setfirst)
	  first = dis.prev;
      }
    } else /* Real win3 swap */ {
      int pos = 0;
      blockdown(dis); /* B A* C(4) */
      pos++;
      if(best > reorder_nodenum())
	{
	  pos = 0;
	  best = reorder_nodenum();
	}

      blockdown(dis); /* B C A*(3) */
      pos++;
      if(best > reorder_nodenum())
	{
	  pos = 0;
	  best = reorder_nodenum();
	}

      dis = dis.prev.prev;
      blockdown(dis); /* C B* A(2) */
      pos++;
      if(best > reorder_nodenum())
	{
	  pos = 0;
	  best = reorder_nodenum();
	}

      blockdown(dis); /* C A B*(1) */
      pos++;
      if(best > reorder_nodenum())
	{
	  pos = 0;
	  best = reorder_nodenum();
	}

      dis = dis.prev.prev;
      blockdown(dis); /* A C* B(0)*/
      pos++;
      if(best > reorder_nodenum())
	{
	  pos = 0;
	  best = reorder_nodenum();
	}

      if(pos >= 1) /* A C B -> C A* B */ {
	dis = dis.prev;
	blockdown(dis);
	next = dis;
	if(setfirst)
	  first = dis.prev;
      }

      if(pos >= 2) /* C A B -> C B A* */ {
	blockdown(dis);
	next = dis.prev;
	if(setfirst)
	  first = dis.prev.prev;
      }

      if(pos >= 3) /* C B A -> B C* A */ {
	dis = dis.prev.prev;
	blockdown(dis);
	next = dis;
	if(setfirst)
	  first = dis.prev;
      }

      if(pos >= 4) /* B C A -> B A C* */ {
	blockdown(dis);
	next = dis.prev;
	if(setfirst)
	  first = dis.prev.prev;
      }

      if(pos >= 5) /* B A C -> A B* C */ {
	dis = dis.prev.prev;
	blockdown(dis);
	next = dis;
	if(setfirst)
	  first = dis.prev;
      }
    }

    return next;
  }

  BddTree reorder_sift_seq(BddTree t, ref Array!BddTree seq, int num)
  {
    BddTree dis;
    int n;

    if(t is null)
      return t;

    for(n = 0; n < num; n++)
      {
	long c2, c1 = clock();

	if(_verbose > 1)
	  {
	    write("Sift ");
	    //if(reorder_filehandler)
	    //   reorder_filehandler(stdout, seq[n].id);
	    //else
	    write(seq[n].id);
	    write(": ");
	  }

	reorder_sift_bestpos(seq[n], num / 2);

	if(_verbose > 1)
	  {
	    writeln();
	    write("> ", reorder_nodenum(), " _nodes");
	  }

	c2 = clock();
	if(_verbose > 1)
	  writeln("(",(cast(double)(c2 - c1)) / 1000.0, " sec)\n");
      }

    /* Find first block */
    for(dis = t; dis.prev !is null; dis = dis.prev)
      {}
    /* nil */

    return dis;
  }

  void reorder_sift_bestpos(BddTree blk, int middlePos)
  {
    int best = reorder_nodenum();
    int maxAllowed;
    int bestpos = 0;
    bool dirIsUp = true;
    int n;

    if(_maxNodeSize > 0)
      maxAllowed =
	MIN(best / 5 + best, _maxNodeSize - _maxNodeIncr - 2);
    else
      maxAllowed = best / 5 + best;

    /* Determine initial direction */
    if(blk.pos > middlePos)
      dirIsUp = false;

    /* Move block back and forth */
    for(n = 0; n < 2; n++)
      {
	int first = 1;

	if(dirIsUp)
	  {
	    while(blk.prev !is null
		  &&(reorder_nodenum() <= maxAllowed || first != 0))
	      {
		first = 0;
		blockdown(blk.prev);
		bestpos--;

		if(_verbose > 1)
		  {
		    write("-");
		    // System.out.flush();
		  }

		if(reorder_nodenum() < best)
		  {
		    best = reorder_nodenum();
		    bestpos = 0;

		    if(_maxNodeSize > 0)
		      maxAllowed =
			MIN(
			    best / 5 + best,
			    _maxNodeSize - _maxNodeIncr - 2);
		    else
		      maxAllowed = best / 5 + best;
		  }
	      }
	  } else {
	  while(blk.next !is null
		&&(reorder_nodenum() <= maxAllowed || first != 0))
	    {
	      first = 0;
	      blockdown(blk);
	      bestpos++;

	      if(_verbose > 1)
		{
		  write("+");
		  // System.out.flush();
		}

	      if(reorder_nodenum() < best)
		{
		  best = reorder_nodenum();
		  bestpos = 0;

		  if(_maxNodeSize > 0)
		    maxAllowed =
		      MIN(
			  best / 5 + best,
			  _maxNodeSize - _maxNodeIncr - 2);
		  else
		    maxAllowed = best / 5 + best;
		}
	    }
	}

	if(reorder_nodenum() > maxAllowed && _verbose > 1)
	  {
	    write("!");
	    // System.out.flush();
	  }

	dirIsUp = !dirIsUp;
      }

    /* Move to best pos */
    while(bestpos < 0)
      {
	blockdown(blk);
	bestpos++;
      }
    while(bestpos > 0)
      {
	blockdown(blk.prev);
	bestpos--;
      }
  }

  BddTree reorder_random(BddTree t)
  {
    import std.random;

    BddTree dis;
    Array!BddTree seq;
    int n, num = 0;

    if(t is null)
      return t;

    for(dis = t; dis !is null; dis = dis.next)
      num++;
    seq.length = num;
    for(dis = t, num = 0; dis !is null; dis = dis.next)
      seq[num++] = dis;

    for(n = 0; n < 4 * num; n++)
      {
	int blk = uniform(0, num-1);
	if(seq[blk].next !is null)
	  blockdown(seq[blk]);
      }

    /* Find first block */
    for(dis = t; dis.prev !is null; dis = dis.prev)
      {}
    /* nil */

    // free(seq);

    if(_verbose != 0)
      writeln("Random order: ", reorder_nodenum(), " _nodes");
    return dis;
  }

  // static int siftTestCmp(sizePair a, sizePair b)
  // {
  //   if(a.val < b.val)
  //     return -1;
  //   if(a.val > b.val)
  //     return 1;
  //   return 0;
  // }

  static class sizePair
  {
    int val;
    BddTree block;
    final int opCmp(sizePair rhs)
    {
      if(this.val < rhs.val) return -1;
      if(this.val > rhs.val) return 1;
      return 0;
    }
  }

  BddTree reorder_sift(BddTree t)
  {
    BddTree dis;
    Array!BddTree seq;
    sizePair[] p;
    int n, num;

    import std.algorithm;

    for(dis = t, num = 0; dis !is null; dis = dis.next)
      dis.pos = num++;

    p.length = num;
    seq.length = num;

    for(dis = t, n = 0; dis !is null; dis = dis.next, n++)
      {
	int v;

	/* Accumulate number of _nodes for each block */
	p[n].val = 0;
	for(v = dis.first; v <= dis.last; v++)
	  p[n].val -= levels[v].nodenum;

	p[n].block = dis;
      }

    /* Sort according to the number of _nodes at each level */
    // Arrays.sort(p, 0, num, new Comparator()
    // {

    //	int compare(sizePair o1, sizePair o2)
    // {
    //	  return siftTestCmp(o1, o2);
    //	}

    //   });
    sort(p);
    
    /* Create sequence */
    for(n = 0; n < num; n++)
      seq[n] = p[n].block;

    /* Do the sifting on this sequence */
    t = reorder_sift_seq(t, seq, num);

    // free(seq);
    // free(p);

    return t;
  }

  BddTree reorder_siftite(BddTree t)
  {
    BddTree first = t;
    int lastsize;
    int c = 1;

    if(t is null)
      return t;

    do {
      if(_verbose > 1)
	writeln("Reorder ", c++, "\n");

      lastsize = reorder_nodenum();
      first = reorder_sift(first);
    } while(reorder_nodenum() != lastsize);

    return first;
  }

  void blockdown(BddTree left)
  {
    BddTree right = left.next;
    int n;
    int leftsize = left.last - left.first;
    int rightsize = right.last - right.first;
    int leftstart = _var2Level[left.seq[0]];
    int[] lseq = left.seq;
    int[] rseq = right.seq;

    /* Move left past right */
    while(_var2Level[lseq[0]] < _var2Level[rseq[rightsize]])
      {
	for(n = 0; n < leftsize; n++)
	  {
	    if(_var2Level[lseq[n]] + 1 != _var2Level[lseq[n + 1]]
	       && _var2Level[lseq[n]] < _var2Level[rseq[rightsize]])
	      {
		reorder_vardown(lseq[n]);
	      }
	  }

	if(_var2Level[lseq[leftsize]] < _var2Level[rseq[rightsize]])
	  {
	    reorder_vardown(lseq[leftsize]);
	  }
      }

    /* Move right to where left started */
    while(_var2Level[rseq[0]] > leftstart)
      {
	for(n = rightsize; n > 0; n--)
	  {
	    if(_var2Level[rseq[n]] - 1 != _var2Level[rseq[n - 1]]
	       && _var2Level[rseq[n]] > leftstart)
	      {
		reorder_varup(rseq[n]);
	      }
	  }

	if(_var2Level[rseq[0]] > leftstart)
	  reorder_varup(rseq[0]);
      }

    /* Swap left and right data in the order */
    left.next = right.next;
    right.prev = left.prev;
    left.prev = right;
    right.next = left;

    if(right.prev !is null)
      right.prev.next = right;
    if(left.next !is null)
      left.next.prev = left;

    n = left.pos;
    left.pos = right.pos;
    right.pos = n;
  }

  BddTree reorder_win2ite(BddTree t)
  {
    BddTree dis, first = t;
    int lastsize;
    int c = 1;

    if(t is null)
      return t;

    if(_verbose > 1)
      writeln("Win2ite start: ", reorder_nodenum(), " _nodes");

    do {
      lastsize = reorder_nodenum();

      dis = t;
      while(dis.next !is null)
	{
	  int best = reorder_nodenum();

	  blockdown(dis);

	  if(best < reorder_nodenum())
	    {
	      blockdown(dis.prev);
	      dis = dis.next;
	    } else if(first == dis)
	    first = dis.prev;
	  if(_verbose > 1)
	    {
	      write(".");
	      // System.out.flush();
	    }
	}

      if(_verbose > 1)
	writeln(" ", reorder_nodenum(), " _nodes");
      c++;
    }
    while(reorder_nodenum() != lastsize);

    return first;
  }

  void bdd_reorder_auto()
  {
    if(!bdd_reorder_ready())
      return;

    bdd_reorder(bddreordermethod);
    bddreordertimes--;
  }

  int bdd_reorder_gain()
  {
    if(usednum_before == 0)
      return 0;

    return(100 *(usednum_before - usednum_after)) / usednum_before;
  }

  bool isInitialized()
  {
    return this.isRunning();
  }

  void reset()
  {
    int _nodes = getNodeTableSize();
    int cache = getCacheSize();

    bdd_fdd_done();
    bdd_vec_done();
    bdd_fdd_init();
    // FIXMALLOC
    // if(_domains !is null) {
    //   GC.free(cast(void*)_domains);
    //   _domains = null;
    // }
    // _domainsLen = 0;
    
    bdd_done();
    initialize(_nodes, cache);
  }

  void bdd_done() {
    /*sanitycheck(); FIXME */
    bdd_fdd_done();
    bdd_vec_done();
    bdd_reorder_done();
    bdd_pairs_done();


    // free(_nodes);
    // _nodes = null; 
    // // free(_refStack);
    // _refStack = null;
    // // free(_varSet);
    // _varSet = null; 
    // // free(_var2Level);
    // _var2Level = null;
    // // free(_level2Var);
    // _level2Var = null;

    bdd_operator_done();

    _running = false;
    _maxNodeSize = 0;
    _varNum = 0;
    _produced = 0;

    //err_handler = null;
    //gbc_handler = null;
    //resize_handler = null;
  }

  // void setError(int code)
  // {
  //   _errorCond = code;
  // }

  // void clearError()
  // {
  //   _errorCond = 0;
  // }

  int bdd_setmaxnodenum(int size) {
    if (size > _nodeSize || size == 0)  {
      int old = _maxNodeSize;
      _maxNodeSize = size;
      return old;
    }

    return bdd_error(BddError.BDD_NODES);
  }

  alias setMaxNodeNum = bdd_setmaxnodenum;
  
  double setMinFreeNodes(double x)
  {
    return bdd_setminfreenodes(cast(int)(x * 100.)) / 100.;
  }

  int bdd_setminfreenodes(int mf)
  {
    int old = _minFreeNodes;

    if(mf < 0 || mf > 100)
      return bdd_error(BddError.BDD_RANGE);

    _minFreeNodes = mf;
    return old;
  }

  int setMaxIncrease(int x)
  {
    return bdd_setmaxincrease(x);
  }

  int bdd_setmaxincrease(int size)
  {
    int old = _maxNodeIncr;

    if(size < 0)
      return bdd_error(BddError.BDD_SIZE);

    _maxNodeIncr = size;
    return old;
  }

  double increasefactor;

  double setIncreaseFactor(double x)
  {
    if(x < 0)
      return bdd_error(BddError.BDD_RANGE);
    double old = increasefactor;
    increasefactor = x;
    return old;
  }

  double setCacheRatio(double x)
  {
    return bdd_setcacheratio(cast(int)(x * 100)) / 100.;
  }

  int bdd_setcacheratio(int r)
  {
    int old = cacheratio;

    if(r <= 0)
      return bdd_error(BddError.BDD_RANGE);
    if(_nodeSize == 0)
      return old;

    cacheratio = r;
    bdd_operator_noderesize();
    return old;
  }

  int varNum()
  {
    return bdd_varnum();
  }

  int setVarNum(int num)
  {
    return bdd_setvarnum(num);
  }


  int extVarNum(int num)
  {
    return bdd_extvarnum(num);
  }

  int duplicateVar(int var)
  {
    if(var < 0 || var >= _varNum)
      {
	bdd_error(BddError.BDD_VAR);
	return BddFalse;
      }

    bdd_disable_reorder();

    int newVar = _varNum;
    int lev = _var2Level[var];
    //writeln("Adding new variable "+newVar+" at level "+(lev+1));
    // Increase the size of the various data structures.
    bdd_setvarnum(_varNum+1);
    // Actually duplicate the var in all BDDs.
    insert_level(lev);
    dup_level(lev, 0);
    // Fix up _var2Level
    for(int i = 0; i < _varNum; ++i)
      {
	if(_var2Level[i] > lev && _var2Level[i] < _varNum)
	  ++_var2Level[i];
      }
    _var2Level[newVar] = lev+1;
    // Fix up _level2Var
    for(int i = _varNum-2; i > lev; --i)
      {
	_level2Var[i+1] = _level2Var[i];
      }
    _level2Var[lev+1] = newVar;
    // Fix up _varSet
    for(int bdv = 0; bdv < _varNum; bdv++)
      {
	_varSet[bdv * 2] = PUSHREF(bdd_makenode(_var2Level[bdv], 0, 1));
	_varSet[bdv * 2 + 1] = bdd_makenode(_var2Level[bdv], 1, 0);
	POPREF(1);

	SETMAXREF(_varSet[bdv * 2]);
	SETMAXREF(_varSet[bdv * 2 + 1]);
      }
    // Fix up pairs
    for(BddPair pair = pairs; pair !is null; pair = pair.next)
      {
	// BddPair.result is an array of ints
	delRef(pair.result[_varNum-1]);
	for(int i = _varNum-1; i > lev+1; --i)
	  {
	    pair.result[i] = pair.result[i-1];
	    if(i != LEVEL(pair.result[i]) && i > pair.last)
	      {
		pair.last = i;
	      }
	  }
	pair.result[lev+1] = bdd_ithvar(newVar);
	//writeln("Pair "+pair);
      }

    bdd_enable_reorder();

    return newVar;
  }

  int bdd_setvarnum(int num)
  {
    int bdv;
    int _oldVarNum = _varNum;

    bdd_disable_reorder();

    if(num < 1 || num > BddNode.MAXVAR)
      {
	bdd_error(BddError.BDD_RANGE);
	return BddFalse;
      }

    if(num < _varNum)
      return bdd_error(BddError.BDD_DECVNUM);
    if(num == _varNum)
      return 0;

    _varSet.length = num * 2;
    _level2Var.length = num + 1;
    _var2Level.length = num + 1;

    _refStack.length = 0;
    _refStack.length = num * 2 + 1;
    INITREF();

    for(bdv = _varNum; _varNum < num; _varNum++)
      {
	_varSet[_varNum * 2] = PUSHREF(bdd_makenode(_varNum, 0, 1));
	_varSet[_varNum * 2 + 1] = bdd_makenode(_varNum, 1, 0);
	POPREF(1);

	if(_errorCond != 0)
	  {
	    _varNum = bdv;
	    return -_errorCond;
	  }

	SETMAXREF(_varSet[_varNum * 2]);
	SETMAXREF(_varSet[_varNum * 2 + 1]);
	_level2Var[_varNum] = _varNum;
	_var2Level[_varNum] = _varNum;
      }

    SETLEVELANDMARK(0, num);
    SETLEVELANDMARK(1, num);
    _var2Level[num] = num;
    _level2Var[num] = num;

    bdd_pairs_resize(_oldVarNum, _varNum);
    bdd_operator_varresize();

    bdd_enable_reorder();

    return 0;
  }

  int bdd_extvarnum(int num) {
    int start = varNum();
    if(num < 0 || num > 0x3FFFFFFF)
      throw new BddException();
    setVarNum(start+num);
    return start;
  }

  BDD ithVar(int var)
  {
    return BDD(bdd_ithvar(var), this);
  }

  BDD nithVar(int var)
  {
    return BDD(bdd_nithvar(var), this);
  }

  void printAll()
  {
    bdd_fprintall(stdout);
  }

  void printTable(BDD b)
  {
    int x = b._index;
    // bdd_fprinttable(stdout, x);
  }

  BDD load(File input)
  {
    // int result = bdd_load(input);
    // return BDD(result, buddyID);
    return BDD(0, this);
  }

  void save(File output, BDD b)
  {
    int x = b._index;
    // bdd_save(output, x);
  }

  int level2Var(int level)
  {
    return _level2Var[level];
  }

  int var2Level(int var)
  {
    return _var2Level[var];
  }

  void reorder(ReorderMethod m)
  {
    // int x = m.id;
    bdd_reorder(m);
  }

  void autoReorder(ReorderMethod method)
  {
    // int x = method.id;
    bdd_autoreorder(method);
  }

  void autoReorder(ReorderMethod method, int max)
  {
    // int x = method.id;
    bdd_autoreorder_times(method, max);
  }

  ReorderMethod getReorderMethod()
  {
    return bddreordermethod;
  }

  int getReorderTimes()
  {
    return bddreordertimes;
  }

  void disableReorder()
  {
    bdd_disable_reorder();
  }

  void enableReorder()
  {
    bdd_enable_reorder();
  }

  int reorderVerbose(int v)
  {
    return bdd_reorder_verbose(v);
  }

  void setVarOrder(int[] neworder)
  {
    bdd_setvarorder(neworder);
  }

  static class BddTree
  {
    int first, last; /* First and last variable in this block */
    int pos; /* Sifting position */
    int[] seq; /* Sequence of first...last in the current order */
    bool fixed; /* Are the sub-blocks fixed or may they be reordered */
    int id; /* A sequential id number given by addblock */
    BddTree next, prev;
    BddTree nextlevel;
  }

  /* Current auto reord. method and number of automatic reorderings left */
  ReorderMethod bddreordermethod;
  int bddreordertimes;

  /* Flag for disabling reordering temporarily */
  int reorderdisabled;

  BddTree vartree;
  int blockid;

  int* extroots;
  int extrootsize;

  levelData* levels; /* Indexed by variable! */

  static class levelData
  {
    int start; /* Start of this sub-table(entry in "_nodes") */
    int size; /* Size of this sub-table */
    int maxsize; /* Max. allowed size of sub-table */
    int nodenum; /* Number of _nodes in this level */
  }

  static class imatrix
  {
    byte[][] rows;
    int size;
  }

  /* Interaction matrix */
  imatrix iactmtx;

  int _verbose;
  //bddinthandler reorder_handler;
  //bddfilehandler reorder_filehandler;
  //bddsizehandler reorder_nodenum;

  /* Number of live _nodes before and after a reordering session */
  int usednum_before;
  int usednum_after;

  void bdd_reorder_init()
  {
    reorderdisabled = 0;
    vartree = null;

    bdd_clrvarblocks();
    //bdd_reorder_hook(bdd_default_reohandler);
    bdd_reorder_verbose(0);
    bdd_autoreorder_times(ReorderMethod.NONE, 0);
    //reorder_nodenum = bdd_getnodenum;
    usednum_before = usednum_after = 0;
    blockid = 0;
  }

  int reorder_nodenum()
  {
    return bdd_getnodenum();
  }

  int bdd_getnodenum()
  {
    return _nodeSize - _freeNum;
  }

  int bdd_reorder_verbose(int v)
  {
    int tmp = _verbose;
    _verbose = v;
    return tmp;
  }

  ReorderMethod bdd_autoreorder(ReorderMethod method)
  {
    ReorderMethod tmp = bddreordermethod;
    bddreordermethod = method;
    bddreordertimes = -1;
    return tmp;
  }

  int bdd_autoreorder_times(ReorderMethod method, int num)
  {
    int tmp = bddreordermethod;
    bddreordermethod = method;
    bddreordertimes = num;
    return tmp;
  }

  // enum BddReorder : ubyte {
  //   NONE = 0,
  //     WIN2 = 1,
  //     WIN2ITE = 2,
  //     SIFT = 3,
  //     SIFTITE = 4,
  //     WIN3 = 5,
  //     WIN3ITE = 6,
  //     RANDOM = 7
  //     }

  static long c1;

  void bdd_reorder_done()
  {
    bddtree_del(vartree);
    bdd_operator_reset();
    vartree = null;
  }

  void bddtree_del(BddTree t)
  {
    if(t is null)
      return;

    bddtree_del(t.nextlevel);
    bddtree_del(t.next);
    t.seq.length = 0;
    remove(t);
  }

  void bdd_clrvarblocks()
  {
    bddtree_del(vartree);
    vartree = null;
    blockid = 0;
  }

  int NODEHASHr(int var, int l, int h)
  {
    return(abs(PAIR(l,(h)) % levels[var].size) + levels[var].start);
  }

  void bdd_setvarorder(int[] neworder)
  {
    int level;

    /* Do not set order when variable-blocks are used */
    if(vartree !is null)
      {
	bdd_error(BddError.BDD_VARBLK);
	return;
      }

    reorder_init();

    for(level = 0; level < _varNum; level++)
      {
	int lowvar = neworder[level];

	while(_var2Level[lowvar] > level)
	  reorder_varup(lowvar);
      }

    reorder_done();
  }

  int reorder_varup(int var)
  {
    if(var < 0 || var >= _varNum)
      return bdd_error(BddError.BDD_VAR);
    if(_var2Level[var] == 0)
      return 0;
    return reorder_vardown(_level2Var[_var2Level[var] - 1]);
  }

  int reorder_vardown(int var)
  {
    int n, level;

    if(var < 0 || var >= _varNum)
      return bdd_error(BddError.BDD_VAR);
    if((level = _var2Level[var]) >= _varNum - 1)
      return 0;

    resizedInMakenode = false;

    if(imatrixDepends(iactmtx, var, _level2Var[level + 1]))
      {
	int toBeProcessed = reorder_downSimple(var);
	levelData l = levels[var];

	if(l.nodenum <(l.size) / 3
	   || l.nodenum >=(l.size * 3) / 2
	   && l.size < l.maxsize)
	  {
	    reorder_swapResize(toBeProcessed, var);
	    reorder_localGbcResize(toBeProcessed, var);
	  } else {
	  reorder_swap(toBeProcessed, var);
	  reorder_localGbc(var);
	}
      }

    /* Swap the var<->level tables */
    n = _level2Var[level];
    _level2Var[level] = _level2Var[level + 1];
    _level2Var[level + 1] = n;

    n = _var2Level[var];
    _var2Level[var] = _var2Level[_level2Var[level]];
    _var2Level[_level2Var[level]] = n;

    /* Update all rename pairs */
    bdd_pairs_vardown(level);

    if(resizedInMakenode)
      reorder_rehashAll();

    return 0;
  }

  bool imatrixDepends(imatrix mtx, int a, int b)
  {
    return(mtx.rows[a][b / 8] &(1 <<(b % 8))) != 0;
  }

  void reorder_setLevellookup()
  {
    for(uint n = 0; n < _varNum; n++)
      {
	levels[n].maxsize = _nodeSize / _varNum;
	levels[n].start = n * levels[n].maxsize;
	levels[n].size =
	  min(levels[n].maxsize,(levels[n].nodenum * 5) / 4);

	if(levels[n].size >= 4)
	  levels[n].size = primeLte(levels[n].size);

      }
  }

  void reorder_rehashAll()
  {
    int n;

    reorder_setLevellookup();
    _freePos = 0;

    for(n = _nodeSize - 1; n >= 0; n--)
      SETHASH(n, 0);

    for(n = _nodeSize - 1; n >= 2; n--)
      {

	if(HASREF(n))
	  {
	    int hash2;

	    hash2 = NODEHASH2(VARr(n), LOW(n), HIGH(n));
	    SETNEXT(n, hash2);
	    SETHASH(hash2, n);
	  } else {
	  SETNEXT(n, _freePos);
	  _freePos = n;
	}
      }
  }

  void reorder_localGbc(int var0)
  {
    int var1 = _level2Var[_var2Level[var0] + 1];
    int vl1 = levels[var1].start;
    int size1 = levels[var1].size;
    int n;

    for(n = 0; n < size1; n++)
      {
	int hash = n + vl1;
	int r = HASH(hash);
	SETHASH(hash, 0);

	while(r != 0)
	  {
	    int next = NEXT(r);

	    if(HASREF(r))
	      {
		SETNEXT(r, HASH(hash));
		SETHASH(hash, r);
	      } else {
	      DECREF(LOW(r));
	      DECREF(HIGH(r));

	      SETLOW(r, INVALID_BDD);
	      SETNEXT(r, _freePos);
	      _freePos = r;
	      levels[var1].nodenum--;
	      _freeNum++;
	    }

	    r = next;
	  }
      }
  }

  enum bool SWAPCOUNT = false;

  int reorder_downSimple(int var0)
  {
    int toBeProcessed = 0;
    int var1 = _level2Var[_var2Level[var0] + 1];
    int vl0 = levels[var0].start;
    int size0 = levels[var0].size;
    int n;

    levels[var0].nodenum = 0;

    for(n = 0; n < size0; n++)
      {
	int r;

	r = HASH(n + vl0);
	SETHASH(n + vl0, 0);

	while(r != 0)
	  {
	    int next = NEXT(r);

	    if(VARr(LOW(r)) != var1 && VARr(HIGH(r)) != var1)
	      {
		/* Node does not depend on next var, let it stay in the chain */
		SETNEXT(r, HASH(n + vl0));
		SETHASH(n + vl0, r);
		levels[var0].nodenum++;
	      } else {
	      /* Node depends on next var - save it for later procesing */
	      SETNEXT(r, toBeProcessed);
	      toBeProcessed = r;
	      if(SWAPCOUNT)
		_cacheStats.swapCount++;

	    }

	    r = next;
	  }
      }

    return toBeProcessed;
  }

  void reorder_swapResize(int toBeProcessed, int var0)
  {
    int var1 = _level2Var[_var2Level[var0] + 1];

    while(toBeProcessed != 0)
      {
	int next = NEXT(toBeProcessed);
	int f0 = LOW(toBeProcessed);
	int f1 = HIGH(toBeProcessed);
	int f00, f01, f10, f11;

	/* Find the cofactors for the new _nodes */
	if(VARr(f0) == var1)
	  {
	    f00 = LOW(f0);
	    f01 = HIGH(f0);
	  } else
	  f00 = f01 = f0;

	if(VARr(f1) == var1)
	  {
	    f10 = LOW(f1);
	    f11 = HIGH(f1);
	  } else
	  f10 = f11 = f1;

	/* Note: makenode does refcou. */
	f0 = reorder_makenode(var0, f00, f10);
	f1 = reorder_makenode(var0, f01, f11);
	//node = _nodes[toBeProcessed]; /* Might change in makenode */

	/* We know that the refcou of the grandchilds of this node
	 * is greater than one(these are f00...f11), so there is
	 * no need to do a recursive refcou decrease. It is also
	 * possible for the node.low/high _nodes to come alive again,
	 * so deref. of the childs is delayed until the local GBC. */

	DECREF(LOW(toBeProcessed));
	DECREF(HIGH(toBeProcessed));

	/* Update in-place */
	SETVARr(toBeProcessed, var1);
	SETLOW(toBeProcessed, f0);
	SETHIGH(toBeProcessed, f1);

	levels[var1].nodenum++;

	/* Do not rehash yet since we are going to resize the hash table */

	toBeProcessed = next;
      }
  }

  static final int MIN(int a, int b)
  {
    return min(a, b);
  }

  void reorder_localGbcResize(int toBeProcessed, int var0)
  {
    int var1 = _level2Var[_var2Level[var0] + 1];
    int vl1 = levels[var1].start;
    int size1 = levels[var1].size;
    int n;

    for(n = 0; n < size1; n++)
      {
	int hash = n + vl1;
	int r = HASH(hash);
	SETHASH(hash, 0);

	while(r != 0)
	  {
	    int next = NEXT(r);

	    if(HASREF(r))
	      {
		SETNEXT(r, toBeProcessed);
		toBeProcessed = r;
	      } else {
	      DECREF(LOW(r));
	      DECREF(HIGH(r));

	      SETLOW(r, INVALID_BDD);
	      SETNEXT(r, _freePos);
	      _freePos = r;
	      levels[var1].nodenum--;
	      _freeNum++;
	    }

	    r = next;
	  }
      }

    /* Resize */
    if(levels[var1].nodenum < levels[var1].size)
      levels[var1].size =
	MIN(levels[var1].maxsize, levels[var1].size / 2);
    else
      levels[var1].size =
	MIN(levels[var1].maxsize, levels[var1].size * 2);

    if(levels[var1].size >= 4)
      levels[var1].size = primeLte(levels[var1].size);

    /* Rehash the remaining live _nodes */
    while(toBeProcessed != 0)
      {
	int next = NEXT(toBeProcessed);
	int hash = NODEHASH2(VARr(toBeProcessed), LOW(toBeProcessed), HIGH(toBeProcessed));

	SETNEXT(toBeProcessed, HASH(hash));
	SETHASH(hash, toBeProcessed);

	toBeProcessed = next;
      }
  }

  void reorder_swap(int toBeProcessed, int var0)
  {
    int var1 = _level2Var[_var2Level[var0] + 1];

    while(toBeProcessed != 0)
      {
	int next = NEXT(toBeProcessed);
	int f0 = LOW(toBeProcessed);
	int f1 = HIGH(toBeProcessed);
	int f00, f01, f10, f11, hash;

	/* Find the cofactors for the new _nodes */
	if(VARr(f0) == var1)
	  {
	    f00 = LOW(f0);
	    f01 = HIGH(f0);
	  } else
	  f00 = f01 = f0;

	if(VARr(f1) == var1)
	  {
	    f10 = LOW(f1);
	    f11 = HIGH(f1);
	  } else
	  f10 = f11 = f1;

	/* Note: makenode does refcou. */
	f0 = reorder_makenode(var0, f00, f10);
	f1 = reorder_makenode(var0, f01, f11);
	//node = _nodes[toBeProcessed]; /* Might change in makenode */

	/* We know that the refcou of the grandchilds of this node
	 * is greater than one(these are f00...f11), so there is
	 * no need to do a recursive refcou decrease. It is also
	 * possible for the node.low/high _nodes to come alive again,
	 * so deref. of the childs is delayed until the local GBC. */

	DECREF(LOW(toBeProcessed));
	DECREF(HIGH(toBeProcessed));

	/* Update in-place */
	SETVARr(toBeProcessed, var1);
	SETLOW(toBeProcessed, f0);
	SETHIGH(toBeProcessed, f1);

	levels[var1].nodenum++;

	/* Rehash the node since it got new childs */
	hash = NODEHASH2(VARr(toBeProcessed), LOW(toBeProcessed), HIGH(toBeProcessed));
	SETNEXT(toBeProcessed, HASH(hash));
	SETHASH(hash, toBeProcessed);

	toBeProcessed = next;
      }
  }

  int NODEHASH2(int var, int l, int h)
  {
    return(abs(PAIR(l, h) % levels[var].size) + levels[var].start);
  }

  bool resizedInMakenode;

  int reorder_makenode(int var, int low, int high)
  {
    int hash;
    int res;

    debug(CACHESTATS) {_cacheStats.uniqueAccess++;}

    /* Note: We know that low,high has a refcou greater than zero, so
       there is no need to add reference *recursively* */

    /* check whether childs are equal */
    if(low == high)
      {
	INCREF(low);
	return low;
      }

    /* Try to find an existing node of this kind */
    hash = NODEHASH2(var, low, high);
    res = HASH(hash);

    while(res != 0)
      {
	if(LOW(res) == low && HIGH(res) == high)
	  {
	    debug(CACHESTATS) {_cacheStats.uniqueHit++;}
	    INCREF(res);
	    return res;
	  }
	res = NEXT(res);

	debug(CACHESTATS) {_cacheStats.uniqueChain++;}
      }

    /* No existing node -> build one */
    debug(CACHESTATS) {_cacheStats.uniqueMiss++;}

    /* Any free _nodes to use ? */
    if(_freePos == 0)
      {
	if(_errorCond != 0)
	  return 0;

	/* Try to allocate more _nodes - call noderesize without
	 * enabling rehashing.
	 * Note: if ever rehashing is allowed here, then remember to
	 * update local variable "hash" */
	bdd_noderesize(false);
	resizedInMakenode = true;

	/* Panic if that is not possible */
	if(_freePos == 0)
	  {
	    bdd_error(BddError.BDD_NODENUM);
	    _errorCond = abs(BddError.BDD_NODENUM);
	    return 0;
	  }
      }

    /* Build new node */
    res = _freePos;
    _freePos = NEXT(_freePos);
    levels[var].nodenum++;
    _produced++;
    _freeNum--;

    SETVARr(res, var);
    SETLOW(res, low);
    SETHIGH(res, high);

    /* Insert node in hash chain */
    SETNEXT(res, HASH(hash));
    SETHASH(hash, res);

    /* Make sure it is reference counted */
    CLEARREF(res);
    INCREF(res);
    INCREF(LOW(res));
    INCREF(HIGH(res));

    return res;
  }

  int reorder_init() {
    int n;

    reorder_handler(true, reorderstats);

    if ((levels = cast(levelData*) malloc(levelData.sizeof * _varNum)) is null) {
      return -1;
    }

    for (n = 0; n < _varNum; n++)  {
      levels[n] = new levelData();
      levels[n].start = -1;
      levels[n].size = 0;
      levels[n].nodenum = 0;
    }

    /* First mark and recursive refcou. all roots and childs. Also do some
     * setup here for both setLevellookup and reorder_gbc */
    if(mark_roots() < 0) {
      return -1;
    }

    /* Initialize the hash tables */
    reorder_setLevellookup();

    /* Garbage collect and rehash to new scheme */
    reorder_gbc();

    return 0;
  }

  void insert_level(int levToInsert)
  {
    for(int n = 2; n < _nodeSize; n++)
      {
	if(LOW(n) == INVALID_BDD) continue;
	int lev = LEVEL(n);
	if(lev <= levToInsert || lev == _varNum-1)
	  {
	    // Stays the same.
	    continue;
	  }
	int lo, hi, newLev;
	lo = LOW(n);
	hi = HIGH(n);
	// Need to increase level by one.
	newLev = lev+1;

	// Find this node in its hash chain.
	int hash = NODEHASH(lev, lo, hi);
	int r = HASH(hash), r2 = 0;
	while(r != n && r != 0)
	  {
	    r2 = r;
	    r = NEXT(r);
	  }
	if(r == 0)
	  {
	    // Cannot find node in the hash chain ?!
	    throw new BddException("Internal Error");
	  }
	// Remove from this hash chain.
	int NEXT_r = NEXT(r);
	if(r2 == 0)
	  {
	    SETHASH(hash, NEXT_r);
	  } else {
	  SETNEXT(r2, NEXT_r);
	}
	// Set level of this node.
	SETLEVEL(n, newLev);
	lo = LOW(n); hi = HIGH(n);
	// Add to new hash chain.
	hash = NODEHASH(newLev, lo, hi);
	r = HASH(hash);
	SETHASH(hash, n);
	SETNEXT(n, r);
      }
  }

  void dup_level(int levToInsert, int val)
  {
    for(int n = 2; n < _nodeSize; n++)
      {
	if(LOW(n) == INVALID_BDD) continue;
	int lev = LEVEL(n);
	if(lev != levToInsert || lev == _varNum-1)
	  {
	    // Stays the same.
	    continue;
	  }
	int lo, hi, newLev;
	lo = LOW(n);
	hi = HIGH(n);
	// Duplicate this node.
	assert(LEVEL(lo) > levToInsert + 1);
	assert(LEVEL(hi) > levToInsert + 1);
	int n_low, n_high;
	// n is an int
	addRef(n);
	// 0 = var == zero, 1 = var == one, -1 = var equals other
	n_low = bdd_makenode(levToInsert+1, val<=0 ? lo : 0, val<=0 ? 0 : lo);
	n_high = bdd_makenode(levToInsert+1, val==0 ? hi : 0, val==0 ? 0 : hi);
	delRef(n);
	//writeln("Lev = "+lev+" old low = "+lo+" old high = "+hi+" new low = "+n_low+"("+new BDD(n_low)+") new high = "+n_high+"("+new BDD(n_high)+")");
	newLev = lev;
	SETLOW(n, n_low);
	SETHIGH(n, n_high);

	// Find this node in its hash chain.
	int hash = NODEHASH(lev, lo, hi);
	int r = HASH(hash), r2 = 0;
	while(r != n && r != 0)
	  {
	    r2 = r;
	    r = NEXT(r);
	  }
	if(r == 0)
	  {
	    // Cannot find node in the hash chain ?!
	    throw new BddException("Internal Error");
	  }
	// Remove from this hash chain.
	int NEXT_r = NEXT(r);
	if(r2 == 0)
	  {
	    SETHASH(hash, NEXT_r);
	  } else {
	  SETNEXT(r2, NEXT_r);
	}
	// Set level of this node.
	SETLEVEL(n, newLev);
	lo = LOW(n); hi = HIGH(n);
	// Add to new hash chain.
	hash = NODEHASH(newLev, lo, hi);
	r = HASH(hash);
	SETHASH(hash, n);
	SETNEXT(n, r);
      }
  }

  int mark_roots() {
    bool* dep = cast(bool*) malloc(_varNum);
    int n;

    for (n = 2, extrootsize = 0; n < _nodeSize; n++) {
	/* This is where we go from .level to .var!
	 * - Do NOT use the LEVEL macro here. */
	SETLEVELANDMARK(n, _level2Var[LEVELANDMARK(n)]);

	if (HASREF(n)) {
	  SETMARK(n);
	  extrootsize++;
	}
    }

    if ((extroots = cast(int*) (malloc (int.sizeof * extrootsize))) is null) {
      return bdd_error(BddError.BDD_MEMORY);
    }

    iactmtx = imatrixNew(_varNum);

    for (n = 2, extrootsize = 0; n < _nodeSize; n++) {

      if (MARKED(n)) {
	UNMARK(n);
	extroots[extrootsize++] = n;

	for (int i = 0; i < _varNum; ++i) {
	  dep[i] = false;
	}
	dep[VARr(n)] = true;
	levels[VARr(n)].nodenum++;

	addref_rec(LOW(n), dep);
	addref_rec(HIGH(n), dep);

	addDependencies(dep);
      }

      /* Make sure the hash field is empty. This saves a loop in the
	 initial GBC */
      SETHASH(n, 0);
    }

    SETHASH(0, 0);
    SETHASH(1, 0);

    free(dep);
    return 0;
  }

  imatrix imatrixNew(int size)
  {
    imatrix mtx = new imatrix();
    int n;

    mtx.rows.length = size;

    for(n = 0; n < size; n++)
      {
	mtx.rows[n].length = size/8 + 1;
      }

    mtx.size = size;

    return mtx;
  }

  void addref_rec(int r, bool* dep)
  {
    if(r < 2)
      return;

    if(!HASREF(r) || MARKED(r))
      {
	_freeNum--;

	/* Detect variable dependencies for the interaction matrix */
	dep[VARr(r) & ~(BddNode.MARK_MASK)] = true;

	/* Make sure the nodenum field is updated. Used in the initial GBC */
	levels[VARr(r) & ~(BddNode.MARK_MASK)].nodenum++;

	addref_rec(LOW(r), dep);
	addref_rec(HIGH(r), dep);
      } else {
      int n;

      /* Update(from previously found) variable dependencies
       * for the interaction matrix */
      for(n = 0; n < _varNum; n++)
	dep[n]
	  |= imatrixDepends(iactmtx, VARr(r) & ~(BddNode.MARK_MASK), n);
    }

    INCREF(r);
  }

  void addDependencies(bool* dep) {
    int n, m;

    for (n = 0; n < _varNum; n++) {
      for (m = n; m < _varNum; m++) {
	if ((dep[n]) && (dep[m])) {
	  imatrixSet(iactmtx, n, m);
	  imatrixSet(iactmtx, m, n);
	}
      }
    }
  }

  void imatrixSet(imatrix mtx, int a, int b)
  {
    mtx.rows[a][b / 8] |= 1 <<(b % 8);
  }

  void reorder_gbc()
  {
    int n;

    _freePos = 0;
    _freeNum = 0;

    /* No need to zero all hash fields - this is done in mark_roots */

    for(n = _nodeSize - 1; n >= 2; n--)
      {

	if(HASREF(n))
	  {
	    int hash;

	    hash = NODEHASH2(VARr(n), LOW(n), HIGH(n));
	    SETNEXT(n, HASH(hash));
	    SETHASH(hash, n);

	  } else {
	  SETLOW(n, INVALID_BDD);
	  SETNEXT(n, _freePos);
	  _freePos = n;
	  _freeNum++;
	}
      }
  }

  void reorder_done() {
    int n;

    for (n = 0; n < extrootsize; n++) {
      SETMARK(extroots[n]);
    }
    for(n = 2; n < _nodeSize; n++) {
      if(MARKED(n)) UNMARK(n);
      else          CLEARREF(n);

      /* This is where we go from .var to .level again!
       * - Do NOT use the LEVEL macro here. */
      SETLEVELANDMARK(n, _var2Level[LEVELANDMARK(n)]);
    }

    free(extroots);
    free(levels);
    imatrixDelete(iactmtx);
    bdd_gbc();

    reorder_handler(false, reorderstats);
  }

  void imatrixDelete(imatrix mtx)
  {
    int n;

    for(n = 0; n < mtx.size; n++)
      {
	// free(mtx.rows[n]);
	mtx.rows[n].length = 0;
      }
    mtx.rows.length = 0;
    remove(mtx);
  }

  void addVarBlock(BDD var, bool fixed)
  {
    //int x = var._index;
    int[] set = var.scanSet();
    bdd_addvarblock(set, fixed);
  }

  void addVarBlock(int first, int last, bool fixed)
  {
    bdd_intaddvarblock(first, last, fixed);
  }

  void varBlockAll()
  {
    bdd_varblockall();
  }

  void clearVarBlocks()
  {
    bdd_clrvarblocks();
  }

  void printOrder()
  {
    bdd_fprintorder(stdout);
  }

  // int nodeCount(BDD[] arr)
  // {
  //   int[] a = new int[](arr.length);
  //   int j = 0;
  //   foreach(ref r; arr)
  //     {
  // 	a[j++] = r._index;
  //     }
  //   return bdd_anodecount(a);
  // }

  int getNodeTableSize()
  {
    return bdd_getallocnum();
  }

  int bdd_getallocnum()
  {
    return _nodeSize;
  }

  bool isRunning() {
    return bdd_isrunning();
  }

  bool bdd_isrunning() {
    return _running;
  }
  
  int getNodeNum()
  {
    return bdd_getnodenum();
  }

  int getCacheSize()
  {
    return _cacheSize;
  }

  int reorderGain()
  {
    return bdd_reorder_gain();
  }

  void printStat()
  {
    bdd_fprintstat(stdout);
  }

  // BddPair makePair()
  // {
  //   BddPair p = new BddPair();
  //   p.result.length = _varNum;
  //   int n;
  //   for(n = 0; n < _varNum; n++)
  //     p.result[n] = bdd_ithvar(_level2Var[n]);

  //   p.id = update_pairsid();
  //   p.last = -1;

  //   bdd_register_pair(p);
  //   return p;
  // }

  // BddPair makePair(int oldvar, int newvar)
  // {
  //   BddPair p = makePair();
  //   p.set(oldvar, newvar);
  //   return p;
  // }

  // BddPair makePair(int oldvar, BDD newvar)
  // {
  //   BddPair p = makePair();
  //   p.set(oldvar, newvar);
  //   return p;
  // }

  // BddPair makePair(BddDomain oldvar, BddDomain newvar)
  // {
  //   BddPair p = makePair();
  //   p.set(oldvar, newvar);
  //   return p;
  // }

  void swapVar(int v1, int v2)
  {
    bdd_swapvar(v1, v2);
  }

  int bdd_swapvar(int v1, int v2)
  {
    int l1, l2;

    /* Do not swap when variable-blocks are used */
    if(vartree !is null)
      return bdd_error(BddError.BDD_VARBLK);

    /* Don't bother swapping x with x */
    if(v1 == v2)
      return 0;

    /* Make sure the variable exists */
    if(v1 < 0 || v1 >= _varNum || v2 < 0 || v2 >= _varNum)
      return bdd_error(BddError.BDD_VAR);

    l1 = _var2Level[v1];
    l2 = _var2Level[v2];

    /* Make sure v1 is before v2 */
    if(l1 > l2)
      {
	int tmp = v1;
	v1 = v2;
	v2 = tmp;
	l1 = _var2Level[v1];
	l2 = _var2Level[v2];
      }

    reorder_init();

    /* Move v1 to v2's position */
    while(_var2Level[v1] < l2)
      reorder_vardown(v1);

    /* Move v2 to v1's position */
    while(_var2Level[v2] > l1)
      reorder_varup(v2);

    reorder_done();

    return 0;
  }

  void bdd_fprintall(File output)
  {
    int n;

    for(n = 0; n < _nodeSize; n++)
      {
	if(LOW(n) != INVALID_BDD)
	  {
	    output.write("[", right(n, 5), " - ", right(GETREF(n), 2), "] ");
	    // TODO: labelling of vars
	    output.write(right(_level2Var[LEVEL(n)], 3));

	    output.write(": ", right(LOW(n), 3));
	    output.writeln(" ", right(HIGH(n), 3));
	  }
      }
  }

  // void bdd_fprinttable(File output, int r)
  // {
  //   int n;

  //   output.writeln("ROOT: " + r);
  //   if(r < 2)
  //     return;

  //   bdd_mark(r);

  //   for(n = 0; n < _nodeSize; n++)
  // {
  //     if(MARKED(n))
  // {
  //	UNMARK(n);

  //	output.write("[" + right(n, 5) + "] ");
  //	// TODO: labelling of vars
  //	output.write(right(_level2Var[LEVEL(n)], 3));

  //	output.write(": " + right(LOW(n), 3));
  //	output.writeln(" " + right(HIGH(n), 3));
  //     }
  //   }
  // }

  int lh_nodenum;
  int lh_freepos;
  int[] loadvar2level;
  LoadHash[] lh_table;

  // int bdd_load(File ifile)
  // {
  //   int n, vnum, tmproot;
  //   int root;

  //   lh_nodenum = Integer.parseInt(readNext(ifile));
  //   vnum = Integer.parseInt(readNext(ifile));

  //   // Check for constant true / false
  //   if(lh_nodenum == 0 && vnum == 0)
  // {
  //     root = Integer.parseInt(readNext(ifile));
  //     return root;
  //   }

  //   // Not actually used.
  //   loadvar2level.length = vnum;
  //   for(n = 0; n < vnum; n++)
  // {
  //     loadvar2level[n] = Integer.parseInt(readNext(ifile));
  //   }

  //   if(vnum > _varNum)
  //     bdd_setvarnum(vnum);

  //   lh_table.length = lh_nodenum;

  //   for(n = 0; n < lh_nodenum; n++)
  // {
  //     lh_table[n] = new LoadHash();
  //     lh_table[n].first = -1;
  //     lh_table[n].next = n + 1;
  //   }
  //   lh_table[lh_nodenum - 1].next = -1;
  //   lh_freepos = 0;

  //   tmproot = bdd_loaddata(ifile);

  //   for(n = 0; n < lh_nodenum; n++)
  //     delRef(lh_table[n].data);

  //   free(lh_table);
  //   lh_table = null;
  //   free(loadvar2level);
  //   loadvar2level = null;

  //   root = tmproot;
  //   return root;
  // }

  static class LoadHash
  {
    int key;
    int data;
    int first;
    int next;
  }

  // int bdd_loaddata(File ifile)  {
  //   int key, var, low, high, root = 0, n;

  //   for(n = 0; n < lh_nodenum; n++)
  // {
  //     key = Integer.parseInt(readNext(ifile));
  //     var = Integer.parseInt(readNext(ifile));
  //     low = Integer.parseInt(readNext(ifile));
  //     high = Integer.parseInt(readNext(ifile));

  //     if(low >= 2)
  //	low = loadhash_get(low);
  //     if(high >= 2)
  //	high = loadhash_get(high);

  //     if(low < 0 || high < 0 || var < 0)
  //	return bdd_error(BddError.BDD_FORMAT);

  //     root = addRef(bdd_ite(bdd_ithvar(var), high, low));

  //     loadhash_add(key, root);
  //   }

  //   return root;
  // }

  // void loadhash_add(int key, int data)
  // {
  //   int hash = key % lh_nodenum;
  //   int pos = lh_freepos;

  //   lh_freepos = lh_table[pos].next;
  //   lh_table[pos].next = lh_table[hash].first;
  //   lh_table[hash].first = pos;

  //   lh_table[pos].key = key;
  //   lh_table[pos].data = data;
  // }

  int loadhash_get(int key)
  {
    int hash = lh_table[key % lh_nodenum].first;

    while(hash != -1 && lh_table[hash].key != key)
      hash = lh_table[hash].next;

    if(hash == -1)
      return -1;
    return lh_table[hash].data;
  }

  // void bdd_save(File output, int r)  {
  //   int[] n = new int[](1);

  //   if(r < 2)
  // {
  //     output.write("0 0 " + r + "\n");
  //     return;
  //   }

  //   bdd_markcount(r, n);
  //   bdd_unmark(r);
  //   output.write(n[0] + " " + _varNum + "\n");

  //   for(int x = 0; x < _varNum; x++)
  //     output.write(_var2Level[x] + " ");
  //   output.write("\n");

  //   bdd_save_rec(output, r);
  //   bdd_unmark(r);

  //   // output.flush();
  //   return;
  // }

  // void bdd_save_rec(File output, int root)  {

  //   if(root < 2)
  //     return;

  //   if(MARKED(root))
  //     return;
  //   SETMARK(root);

  //   bdd_save_rec(output, LOW(root));
  //   bdd_save_rec(output, HIGH(root));

  //   output.write(root + " ");
  //   output.write(_level2Var[LEVEL(root)] + " ");
  //   output.write(LOW(root) + " ");
  //   output.write(HIGH(root) + "\n");

  //   return;
  // }

  static string right(int x, int w)
  {
    return right(format("%s", x), w);
  }
  static string right(string s, int w)
  {
    int n = cast(int) s.length;
    //if(w < n) return s.substring(n - w);
    string b;
    for(int i = n; i < w; ++i)
      {
	b ~= ' ';
      }
    b ~= s;
    return b;
  }

  int bdd_addvarblock(int[] v, bool fixed)
  {
    BddTree t;
    int first, last;

    if(v.length < 1)
      return bdd_error(BddError.BDD_VARBLK);

    first = last = v[0];

    for(int n = 0; n < v.length; n++)
      {
	if(v[n] < first)
	  first = v[n];
	if(v[n] > last)
	  last = v[n];
      }

    if((t = bddtree_addrange(vartree, first, last, fixed, blockid))
       is null)
      return bdd_error(BddError.BDD_VARBLK);

    vartree = t;
    return blockid++;
  }

  int bdd_intaddvarblock(int first, int last, bool fixed)
  {
    BddTree t;

    if(first < 0 || first >= _varNum || last < 0 || last >= _varNum)
      return bdd_error(BddError.BDD_VAR);

    if((t = bddtree_addrange(vartree, first, last, fixed, blockid))
       is null)
      return bdd_error(BddError.BDD_VARBLK);

    vartree = t;
    return blockid++;
  }

  BddTree bddtree_addrange_rec(
			       BddTree t,
			       BddTree prev,
			       int first,
			       int last,
			       bool fixed,
			       int id)
  {
    if(first < 0 || last < 0 || last < first)
      return null;

    /* Empty tree -> build one */
    if(t is null)
      {
	if((t = bddtree_new(id)) is null)
	  return null;
	t.first = first;
	t.fixed = fixed;
	t.seq.length = last - first + 1;
	t.last = last;
	update_seq(t);
	t.prev = prev;
	return t;
      }

    /* Check for identity */
    if(first == t.first && last == t.last)
      return t;

    /* Before this section -> insert */
    if(last < t.first)
      {
	BddTree tnew = bddtree_new(id);
	if(tnew is null)
	  return null;
	tnew.first = first;
	tnew.last = last;
	tnew.fixed = fixed;
	tnew.seq.length = last - first + 1;
	update_seq(tnew);
	tnew.next = t;
	tnew.prev = t.prev;
	t.prev = tnew;
	return tnew;
      }

    /* After this this section -> go to next */
    if(first > t.last)
      {
	t.next = bddtree_addrange_rec(t.next, t, first, last, fixed, id);
	return t;
      }

    /* Inside this section -> insert in next level */
    if(first >= t.first && last <= t.last)
      {
	t.nextlevel =
	  bddtree_addrange_rec(t.nextlevel, null, first, last, fixed, id);
	return t;
      }

    /* Covering this section -> insert above this level */
    if(first <= t.first)
      {
	BddTree tnew;
	BddTree dis = t;

	while(true)
	  {
	    /* Partial cover ->error */
	    if(last >= dis.first && last < dis.last)
	      return null;

	    if(dis.next is null || last < dis.next.first)
	      {
		tnew = bddtree_new(id);
		if(tnew is null)
		  return null;
		tnew.first = first;
		tnew.last = last;
		tnew.fixed = fixed;
		tnew.seq.length = last - first + 1;
		update_seq(tnew);
		tnew.nextlevel = t;
		tnew.next = dis.next;
		tnew.prev = t.prev;
		if(dis.next !is null)
		  dis.next.prev = tnew;
		dis.next = null;
		t.prev = null;
		return tnew;
	      }

	    dis = dis.next;
	  }

      }

    return null;
  }

  void update_seq(BddTree t)
  {
    int n;
    int low = t.first;

    for(n = t.first; n <= t.last; n++)
      if(_var2Level[n] < _var2Level[low])
	low = n;

    for(n = t.first; n <= t.last; n++)
      t.seq[_var2Level[n] - _var2Level[low]] = n;
  }

  BddTree bddtree_addrange(
			   BddTree t,
			   int first,
			   int last,
			   bool fixed,
			   int id)
  {
    return bddtree_addrange_rec(t, null, first, last, fixed, id);
  }

  void bdd_varblockall()
  {
    int n;

    for(n = 0; n < _varNum; n++)
      bdd_intaddvarblock(n, n, true);
  }

  void print_order_rec(File o, BddTree t, int level)
  {
    if(t is null)
      return;

    if(t.nextlevel !is null)
      {
	for(int i = 0; i < level; ++i)
	  o.write("   ");
	// todo: better reorder id printout
	o.write(right(t.id, 3));
	o.writeln("{\n");

	print_order_rec(o, t.nextlevel, level + 1);

	for(int i = 0; i < level; ++i)
	  o.write("   ");
	// todo: better reorder id printout
	o.write(right(t.id, 3));
	o.writeln("}\n");

	print_order_rec(o, t.next, level);
      } else {
      for(int i = 0; i < level; ++i)
	o.write("   ");
      // todo: better reorder id printout
      o.writeln(right(t.id, 3));

      print_order_rec(o, t.next, level);
    }
  }

  void bdd_fprintorder(File ofile)
  {
    print_order_rec(ofile, vartree, 0);
  }

  void bdd_fprintstat(File output)
  {
    CacheStats s = _cacheStats;
    output.write(s.toString());
  }

  void validateAll()
  {
    validate_all();
  }

  void validateBDD(BDD b)
  {
    validate(b._index);
  }

  void validate_all()
  {
    int n;
    for(n = _nodeSize - 1; n >= 2; n--)
      {
	if(HASREF(n))
	  {
	    validate(n);
	  }
      }
  }
  void validate(int k)
  {
    validate(k, -1);
  }
  void validate(int k, int lastLevel)
  {
    if(k < 2) return;
    int lev = LEVEL(k);
    //writeln("Level("+k+") = "+lev);
    if(lev <= lastLevel)
      throw new BddException(format("%s <= %s", lev, lastLevel));
    //writeln("Low:");
    validate(LOW(k), lev);
    //writeln("High:");
    validate(HIGH(k), lev);
  }

  /**** FINITE DOMAINS ****/

  protected int _firstbddvar;
  protected int _fdvaralloc;
  protected int _fdvarnum;

  // FIXMALLOC
  protected Array!BddDomain _domains; // define as domain in fdd.c:67
  // protected BddDomain* _domains;
  // protected size_t _domainsLen;

  protected Array!BddVec _vecs;
  
  void incr_firstbddvar()
  {
    _firstbddvar++;
  }

  // fdd.c:1033
  void Domain_allocate(int a, long range) {
    ulong calcsize = 2;
    int binsize;
   
    if (range <= 0  || range > long.max/2) {
      bdd_error(BddError.BDD_RANGE);
      return;
    }

    while (calcsize < range) {
      binsize++;
      calcsize <<= 1;
    }

    Domain_create(a, binsize);
  }

  // We diverge from c version in that the parameter b is number of
  // bits instead of range
  protected BddDomain Domain_create(int a, uint b) {
    return BddDomain(a, b);
  }

  alias createDomain = Domain_create;

  uint extDomVec(uint domainSize) {
    _vecs.length = _vecs.length + 1;
    return extDomain(domainSize);
  }

  uint extDomain(uint domainSize) {
    int offset = _fdvarnum;

    _domains.length = _domains.length + 1;

    /* Create BDD variable tables */
    _domains[_fdvarnum] = Domain_create(_fdvarnum, domainSize);
    uint extravars = _domains[_fdvarnum].varNum();

    uint binoffset = _firstbddvar;
    int _varNum = varNum();
    if(_firstbddvar + extravars > _varNum) {
      setVarNum(_firstbddvar + extravars);
    }

    /* Set correct variable sequence(interleaved) */
    bool more = true;
    for (uint bn = 0; more; ++bn) {
      more = false;
      if(bn < _domains[_fdvarnum].varNum()) {
	more = true;
	_domains[_fdvarnum].get_ivars[bn] = binoffset++;
      }
    }

    _domains[_fdvarnum].var = makeSet(_domains[_fdvarnum].get_ivars);

    _fdvarnum += 1;
    _firstbddvar += extravars;

    return offset;
  }

  // BddDomain[] extDomain(uint[] domainSizes)
  // {
  //   int offset = _fdvarnum;
  //   int binoffset;
  //   int extravars = 0;
  //   int n, bn;
  //   bool more;
  //   size_t num = domainSizes.length;

  //   /* Build _domains table */
  //   // FIXMALLOC
  //   // if(_domains.length == 0) /* First time */ {
  //   //   _domains.length = num;
  //   //   // if(_domainsLen == 0) /* First time */ {
  //   //   //   void* mem = GC.malloc(BddDomain.sizeof * num);
  //   //   //   memset(mem, 0, BddDomain.sizeof * num);
  //   //   //   _domains = cast(BddDomain*) mem; // GC.malloc(BddDomain.sizeof * num);
  //   //   // for (size_t i=0; i!=num; ++i) {
  //   //   // 	_domains[i] = BddDomain.init;
  //   //   // }
  //   //   // _domainsLen = num;
  //   // } else /* Allocated before */ {
  //   //   // FIXMALLOC
  //   //   if(_fdvarnum + num > _domains.length)
  //   //   // if(_fdvarnum + num > _domainsLen)
  //   // 	{
  //   // 	  // FIXMALLOC
  //   // 	  // auto fdvaralloc = _domains.length + max(num, _domains.length);
  //   // 	  // auto fdvaralloc = _domainsLen + max(num, _domainsLen);

  //   // 	  // BddDomain[] d2 = _domains.dup;
  //   // 	  // d2.length = fdvaralloc;
  //   // 	  // _domains = d2;
  //   // 	  _domains.length = _domains.length + max(num, _domains.length); // fdvaralloc;

  //   // 	  // FIXMALLOC
  //   // 	  // _domains.length = fdvaralloc;
  //   // 	  // void* mem2 = GC.malloc(BddDomain.sizeof * fdvaralloc);
  //   // 	  // memset(mem2, 0, BddDomain.sizeof * fdvaralloc);
  //   // 	  // BddDomain* d2 = cast(BddDomain*) mem2; // GC.malloc(BddDomain.sizeof * fdvaralloc);
  //   // 	  // for (size_t i=0; i!=_domainsLen; ++i) {
  //   // 	  //   d2[i] = _domains[i];
  //   // 	  // }
  //   // 	  // for (size_t i=_domainsLen; i!=fdvaralloc; ++i) {
  //   // 	  //   d2[i] = BddDomain.init;
  //   // 	  // }
  //   // 	  // GC.free(cast(void*)_domains);
  //   // 	  // _domains = d2;
  //   // 	  // _domainsLen = fdvaralloc;
  //   // 	}
  //   // }
  //   _domains.length(_domains.length + num);

  //   /* Create BDD variable tables */
  //   for(n = 0; n < num; n++) {
  //     _domains[n + _fdvarnum] = Domain_create(n + _fdvarnum, domainSizes[n]);
  //     extravars += _domains[n + _fdvarnum].varNum();
  //   }

  //   binoffset = _firstbddvar;
  //   int _varNum = varNum();
  //   if(_firstbddvar + extravars > _varNum) {
  //     setVarNum(_firstbddvar + extravars);
  //   }

  //   /* Set correct variable sequence(interleaved) */
  //   for(bn = 0, more = true; more; bn++) {
  //     more = false;

  //     for(n = 0; n < num; n++)
  // 	{
  // 	  if(bn < _domains[n + _fdvarnum].varNum())
  // 	    {
  // 	      more = true;
  // 	      _domains[n + _fdvarnum].get_ivars[bn] = binoffset++;
  // 	    }
  // 	}
  //   }

  //   for(n = 0; n < num; n++) {
  //     _domains[n + _fdvarnum].var =
  // 	makeSet(_domains[n + _fdvarnum].get_ivars);
  //   }

  //   _fdvarnum += num;
  //   _firstbddvar += extravars;

  //   // FIXMALLOC
  //   // BddDomain[] r = _domains[offset..offset+num];
  //   // return r.ptr;

  //   return _domains[offset..offset+num]; // _domains + offset;
  // }

  /**
   * <p>This function takes two finite _domains blocks and merges them
   * into a new one, such that the new one is encoded using both sets
   * of BDD variables.</p>
   *
   * <p>Compare to fdd_overlapdomain.</p>
   */
  BddDomain overlapDomain(BddDomain d1, BddDomain d2)
  {
    BddDomain d;
    int n;

    // FIXMALLOC
    auto fdvaralloc = _domains.length;
    // auto fdvaralloc = _domainsLen;
    if (_fdvarnum + 1 > fdvaralloc) {
      fdvaralloc += fdvaralloc;
    }

    d = _domains[_fdvarnum];
    d.realsize = d1.realsize * d2.realsize;
    d._ivar = cast(int*) realloc(d._ivar, int.sizeof * (d1.varNum() + d2.varNum()));
    d._binsize = d1.varNum() + d2.varNum();

    for(n = 0; n < d1.varNum(); n++)
      d.get_ivars[n] = d1.get_ivars[n];
    for(n = 0; n < d2.varNum(); n++)
      d.get_ivars[d1.varNum() + n] = d2.get_ivars[n];

    d.var = makeSet(d.get_ivars);
    //addRef(d.var);

    _fdvarnum++;
    return d;
  }

  void Domain_done(ref BddDomain d) {
    free(d._ivar);
    d._var.reset();		// do not use delRef -- see comments
				// in BDD.reset method definition
  }


  /**
   * <p>Returns a BDD defining all the variable sets used to define the variable
   * blocks in the given array.</p>
   *
   * <p>Compare to fdd_makeset.</p>
   */
  // FIXME -- DO NO USE DYNAMIC ARRAYS

  // BDD makeSet(BddDomain[] v)
  // {
  //   BDD res = one();

  //   for(size_t n = 0; n < v.length; ++n) {
  //     res = res.and(v[n].set());
  //   }

  //   return res;
  // }

  void bdd_fdd_init() {
    _domains.clear();
    _fdvarnum = 0;
    _fdvaralloc = 0;
    _firstbddvar = 0;
  }


  void bdd_vec_done() {
    if (_vecs.length > 0) {
      for (int n=0 ; n < _fdvarnum ; n++) {
	_vecs[n].reset();
      }
      _vecs.clear();
    }
  }
  
  void bdd_fdd_done() {
    if (_domains.length > 0) {
      for (int n=0 ; n < _fdvarnum ; n++) {
	Domain_done(_domains[n]);
      }
      // free(domain);
      _domains.clear();
    }
  }
  
  void fdd_clearall() {
    bdd_vec_done();
    bdd_fdd_done();
    bdd_fdd_init();
  }

  /**
   * <p>Clear all allocated finite _domains blocks that were defined by extDomain()
   * or overlapDomain().</p>
   *
   * <p>Compare to fdd_clearall.</p>
   */
  alias clearAllDomains = fdd_clearall;

  /**
   * <p>Returns the number of finite _domains blocks defined by calls to
   * extDomain().</p>
   *
   * <p>Compare to fdd_domainsnum.</p>
   */
  int fdd_domainnum() {
    if (! _running) {
      bdd_error(BddError.BDD_RUNNING);
    }
    return _fdvarnum;
  }
  
  alias numberOfDomains = fdd_domainnum;

  /**
   * <p>Returns the ith finite _domains block, as defined by calls to
   * extDomain().</p>
   */
  BddDomain getDomain(int i)
  {
    if(i < 0 || i >= _fdvarnum)
      throw new BddException("Index out of bound!");
    return _domains[i];
  }

  ref BddVec getVec(int i)
  {
    if(i < 0 || i >= _fdvarnum)
      throw new BddException("Index out of bound!");
    return _vecs[i];
  }

  // TODO: fdd_file_hook, fdd_strm_hook

  int[] makeVarOrdering(bool reverseLocal, string ordering)
  {
    import std.regex;
    int varnum = varNum();

    int nDomains = numberOfDomains();
    int[][] localOrders = new int[][](nDomains, 0);
    for(int i=0; i<localOrders.length; ++i)
      {
	localOrders[i].length = getDomain(i).varNum();
      }

    for(int i=0; i<nDomains; ++i)
      {
	BddDomain d = getDomain(i);
	int nVars = d.varNum();
	for(int j=0; j<nVars; ++j)
	  {
	    if(reverseLocal)
	      {
		localOrders[i][j] = nVars - j - 1;
	      } else {
	      localOrders[i][j] = j;
	    }
	  }
      }

    // BddDomain[] doms = new BddDomain[](nDomains);
    BddDomain[] doms;
    doms.length = nDomains;

    int[] varorder = new int[](varnum);

    //System.out.println("Ordering: "+ordering);
    // auto domainGroups = map!((a){return splitter(a, regex("x"));})
    //(splitter(ordering, regex("_")));
    int indexInGroup = 0, bitIndex = 0;
    bool[] done = new bool[](nDomains);
    BddDomain d;
    int index = 0;
    writeln("ordering: ", ordering);
    foreach(sdg;(split(ordering, regex("_"))))
      {
	indexInGroup = 0;
	foreach(sd; split(sdg, regex("x")))
	  {
	    for(int j=0; ; ++j)
	      {
		if(j == nDomains)
		  throw new BddException("bad domain: " ~ sd);
		d = getDomain(j);
		if(d.getName() == sd) break;
	      }
	    if(done[d.getIndex()])
	      throw new BddException("duplicate domain: " ~ sd);
	    done[d.getIndex()] = true;
	    doms[index] = d;
	    // writeln(doms);
	    ++indexInGroup; ++index;
	  }
	bitIndex = fillInVarIndices(doms, index-indexInGroup,
				    indexInGroup, localOrders,
				    bitIndex, varorder);
      }
    for(int i=0; i<doms.length; ++i)
      {
	if(!done[i])
	  {
	    throw new BddException(format("missing domain # %s: %s",
					  i, getDomain(i)));
	  }
	doms[i] = getDomain(i);
      }

    int[] test = varorder.dup;
    test.sort();
    for(int i=0; i<test.length; ++i)
      {
	if(test[i] != i)
	  throw new BddException(format("%s != %s", test[i], i));
      }
    return varorder;
  }

  /**
   * Helper function for makeVarOrder().
   */
  static int fillInVarIndices(BddDomain[] doms, int domainIndex,
			      int index, int[][] localOrders,
			      int bitIndex, int[] varorder)
  {
    // calculate size of largest domain to interleave
    int maxBits = 0;
    // writeln("domains: ", doms.length);
    // writeln("domainIndex: ", domainIndex);
    // writeln("index: ", index);
    // writeln(doms);
    for(int i=0; i < index; ++i)
      {
	BddDomain d = doms[domainIndex+i];
	maxBits = max(maxBits, d.varNum());
      }
    // interleave the domains
    for(int bitNumber=0; bitNumber<maxBits; ++bitNumber)
      {
	for(int i=0; i<index; ++i)
	  {
	    BddDomain d = doms[domainIndex+i];
	    if(bitNumber < d.varNum())
	      {
		int di = d.getIndex();
		int local = localOrders[di][bitNumber];
		if(local >= d.get_ivars().length)
		  {
		    writeln("bug!");
		  }
		if(bitIndex >= varorder.length)
		  {
		    writeln("bug2!");
		  }
		varorder[bitIndex++] = d.get_ivars()[local];
	      }
	  }
      }
    return bitIndex;
  }

  /**** BIT VECTORS ****/

  BddVec createVec(size_t a, bool signed = false)
  {
    return BddVec(a, signed);
  }

  BddVec buildVec(size_t bitnum, bool b, bool signed = false)
  {
    BddVec v = BddVec(bitnum, signed);
    v.initialize(b);
    return v;
  }

  BddVec buildVec(size_t bitnum, long val, bool signed = false)
  {
    BddVec v = BddVec(bitnum, signed);
    v.initialize(val);
    return v;
  }

  // BddVec buildVec(long val)
  // {
  //   uint bits()
  //   {
  //     import std.math: abs;
  //     long aval = abs(val);
  //     for(uint _bits=1; _bits != 64; ++_bits)
  // 	if((1L << _bits) > aval) {
  // 	  if(aval == val) return _bits; // positive numbers
  // 	  else return _bits + 1; // neg numbers need another bit for sign
  // 	}
  //     return 64;
  //   }
  //   return buildVec(bits(), val, val < 0);
  // }

  BddVec buildVec(T)(T val) {
    import esdl.data.bvec: isBitVector;
    import std.traits;
    
    ulong val_;
    int bitnum = 0;
    bool signed;
    
    static if(isBitVector!T) {
      bitnum = T.SIZE;
      val_ = cast(ulong) val;
      signed = T.ISSIGNED;
    }
    else static if(isIntegral!T) {
      bitnum = T.sizeof * 8;
      val_ = val;
      signed = isSigned!T;
    }
    else static if(is(T == bool)) {
      bitnum = 1;
      val_ = val;
      signed = false;
    }
    return buildVec(bitnum, val_, signed);
  }

  BddVec buildVec(size_t bitnum, int offset, int step, bool signed = false)
  {
    BddVec v = BddVec(bitnum, signed);
    v.initialize(offset, step);
    return v;
  }

  BddVec buildVec(BddDomain d, bool signed = false)
  {
    BddVec v = BddVec(d.varNum(), signed);
    v.initialize(d);
    return v;
  }

  BddVec buildVec(int[] var, bool signed = false)
  {
    BddVec v = BddVec(var.length, signed);
    v.initialize(var);
    return v;
  }


  Buddy cloneBuddy()
  {
    Buddy INSTANCE = new Buddy();
    INSTANCE._applyCache = this._applyCache.copy();
    INSTANCE._iteCache = this._iteCache.copy();
    INSTANCE._quantCache = this._quantCache.copy();
    INSTANCE._appexCache = this._appexCache.copy();
    INSTANCE._replaceCache = this._replaceCache.copy();
    INSTANCE._miscCache = this._miscCache.copy();
    INSTANCE._countCache = this._countCache.copy();
    INSTANCE._log2countCache = this._log2countCache.copy();
    // TODO: potential difference here(!)
    INSTANCE._verbose = this._verbose;
    INSTANCE._cacheStats.copyFrom(this._cacheStats);

    INSTANCE._running = this._running;
    INSTANCE._errorCond = this._errorCond;
    INSTANCE._maxNodeSize = this._maxNodeSize;
    INSTANCE._maxNodeIncr = this._maxNodeIncr;
    INSTANCE._freePos = this._freePos;
    INSTANCE._freeNum = this._freeNum;
    INSTANCE._produced = this._produced;
    INSTANCE._varNum = this._varNum;

    INSTANCE._gbCollectNum = this._gbCollectNum;
    INSTANCE._cacheSize = this._cacheSize;
    INSTANCE._gbcClock = this._gbcClock;
    INSTANCE._usedNodesNextReorder = this._usedNodesNextReorder;

    INSTANCE._refStackTop = this._refStackTop;
    INSTANCE._resized = this._resized;
    INSTANCE._minFreeNodes = this._minFreeNodes;
    INSTANCE._nodes = this._nodes.dup;
    INSTANCE._refStack = this._refStack.dup;
    INSTANCE._var2Level = this._var2Level.dup;
    INSTANCE._level2Var = this._level2Var.dup;
    INSTANCE._varSet = this._varSet.dup;

    // FIXMALLOC
    INSTANCE._domains = this._domains.dup;
    // void* mem = GC.malloc(BddDomain.sizeof * this._domainsLen);
    // memset(mem, 0, BddDomain.sizeof * this._domainsLen);
    // BddDomain* d2 = cast(BddDomain*) mem; // GC.malloc(BddDomain.sizeof * this._domainsLen);
    // for (size_t i=0; i!=this._domainsLen; ++i) {
    //   d2[i] = this._domains[i];
    // }
    // INSTANCE._domainsLen = this._domainsLen;
    // INSTANCE._domains = d2;

    
    // FIXMALLOC
    for(int i = 0; i < INSTANCE._domains.length; ++i) {
      INSTANCE._domains[i] =
	INSTANCE.Domain_create(i, this._domains[i]._binsize);
    }
    return INSTANCE;
  }

  BDD copyNode(BDD that)
  {
    return BDD(that._index, this);
  }

  static class GCStats
  {
    int nodes;
    int freenodes;
    long time;
    long sumtime;
    int num;

    protected this()
    { }

    override string toString()
    {
      return format("Garbage collection #%s: %s nodes / free / %s sec / %s sec total",
		    num, nodes, freenodes,
		    cast(double) time / 1000.0,
		    cast(double) sumtime / 1000.0);
    }
  }

  /**
   * Singleton object for GC statistics.
   */
  protected GCStats gcstats;

  /**
   * <p>Return the current GC statistics for this Buddy instance.</p>
   *
   * @return  GC statistics
   */
  GCStats getGCStats()
  {
    return gcstats;
  }
  /**** CALLBACKS ****/

  abstract class Callback
  {
  }

  abstract class GCCallback: Callback
  {
    void notify(bool pre, GCStats s);
  }

  abstract class ReorderCallback: Callback
  {
    void notify(bool b, ReorderStats s);
  }

  abstract class ResizeCallback: Callback
  {
    void notify(int oldsize, int newsize);
  }

  protected GCCallback[] gc_callbacks;
  protected ReorderCallback[] reorder_callbacks;
  protected ResizeCallback[] resize_callbacks;


  /**
   * <p>Register a callback that is called when garbage collection is about
   * to occur.</p>
   *
   * @param o  base object
   * @param m  method
   */
  void registerCallback(T)(T cb)
    if(is(T: Callback))
      {
	static if(is(T: GCCallback)) gc_callbacks ~= cb;
	static if(is(T: ReorderCallback)) reorder_callbacks ~= cb;
	static if(is(T: ResixeCallback)) resixe_callbacks ~= cb;
      }

  /**
   * <p>Unregister a garbage collection callback that was previously
   * registered.</p>
   *
   * @param o  base object
   * @param m  method
   */
  void unregisterCallback(T)(T cb)
    if(is(T: Callback))
      {
	static if(is(T: GCCallback))
	  {
	    foreach(int i, ref c; gc_callbacks)
	      {
		if(c == cb)
		  {
		    gc_callbacks[i] = gc_callbacks[$-1];
		    gc_callbacks.length -= 1;
		    return;
		  }
	      }
	  }
	static if(is(T: ReorderCallback))
	  {
	    foreach(int i, ref c; reorder_callbacks)
	      {
		if(c == cb)
		  {
		    reorder_callbacks[i] = reorder_callbacks[$-1];
		    reorder_callbacks.length -= 1;
		    return;
		  }
	      }
	  }
	static if(is(T: ResizeCallback))
	  {
	    foreach(int i, ref c; resize_callbacks)
	      {
		if(c == cb)
		  {
		    resize_callbacks[i] = resize_callbacks[$-1];
		    resize_callbacks.length -= 1;
		    return;
		  }
	      }
	  }
	throw new BddException("unregisterCallback: Callback not registered");
      }


  protected void gbc_handler(bool pre, GCStats s)
  {
    if(gc_callbacks.length == 0)
      {
	bdd_default_gbchandler(pre, s);
      } else {
      foreach(ref cb; gc_callbacks)
	{
	  cb.notify(pre, s);
	}
    }
  }

  protected static void bdd_default_gbchandler(bool pre, GCStats s)
  {
    debug(BDDGC) {if(!pre) writeln(s.toString());}
  }

  void reorder_handler(bool b, ReorderStats s)
  {
    if(b)
      {
	s.usednum_before = getNodeNum();
	s.time = Clock.currStdTime()/10000;
      } else {
      s.time = Clock.currStdTime()/10000 - s.time;
      s.usednum_after = getNodeNum();
    }
    if(reorder_callbacks is null)
      {
	bdd_default_reohandler(b, s);
      } else {
      foreach(ref cb; reorder_callbacks)
	{
	  cb.notify(b, s);
	}
    }
  }

  protected void bdd_default_reohandler(bool prestate, ReorderStats s)
  {
    if(_verbose > 0)
      {
	if(prestate)
	  {
	    writeln("Start reordering");
	    s.usednum_before = getNodeNum();
	    s.time = Clock.currStdTime()/10000;
	  } else {
	  s.time = Clock.currStdTime()/10000 - s.time;
	  s.usednum_after = getNodeNum();
	  writeln("End reordering. ", s);
	}
      }
  }

  protected void resize_handler(int oldsize, int newsize)
  {
    if(resize_callbacks is null)
      {
	bdd_default_reshandler(oldsize, newsize);
      } else {
      foreach(ref cb; resize_callbacks)
	{
	  cb.notify(oldsize, newsize);
	}
    }
  }

  protected void bdd_default_reshandler(int oldsize, int newsize)
  {
    if(_verbose > 0)
      {
	writeln("Resizing node table from ", oldsize, " to ", newsize);
      }
  }


  static class ReorderStats
  {

    long time;
    int usednum_before, usednum_after;

    protected this()
    { }

    int gain()
    {
      if(usednum_before == 0)
	return 0;

      return(100 *(usednum_before - usednum_after)) / usednum_before;
    }

    override string toString()
    {
      return format("Went from %s to %s nodes, gain = %s %(%s sec)",
		    usednum_before, usednum_after,
		    gain(), cast(double) time / 1000.0);
    }
  }

  /**
   * Singleton object for reorder statistics.
   */
  protected ReorderStats reorderstats;

  /**
   * <p>Return the current reordering statistics for this Buddy Instance.</p>
   *
   * @return  reorder statistics
   */
  ReorderStats getReorderStats()
  {
    return reorderstats;
  }

  static class CacheStats
  {
    int uniqueAccess;
    int uniqueChain;
    int uniqueHit;
    int uniqueMiss;
    int opHit;
    int opMiss;
    int swapCount;

    protected this()
    { }

    void copyFrom(CacheStats that)
    {
      this.uniqueAccess = that.uniqueAccess;
      this.uniqueChain = that.uniqueChain;
      this.uniqueHit = that.uniqueHit;
      this.uniqueMiss = that.uniqueMiss;
      this.opHit = that.opHit;
      this.opMiss = that.opMiss;
      this.swapCount = that.swapCount;
    }

    override string toString()
    {
      string sb;
      string newLine = "\n";
      sb ~= format("\nCache statistics\n----------------\n" ~
		   "Unique Access:  %s\nUnique Chain:   %s\n" ~
		   "Unique Hit:     %s\n" ~
		   "Unique Miss:    %s\n" ~
		   "=> Hit rate =   ",
		   uniqueAccess, uniqueChain, uniqueHit, uniqueMiss);
      if(uniqueHit + uniqueMiss > 0)
	sb ~= format("%s", (cast(double) uniqueHit) /
		     (cast(double) uniqueHit + uniqueMiss));
      else
	sb ~= "0.0";
      sb ~= format("\nOperator Hits:  %s\n" ~
		 "Operator Miss:  %s\n" ~
		   "=> Hit rate =   ", opHit, opMiss);
      if(opHit + opMiss > 0)
	sb ~= format("%s", (cast(double) opHit) /
		     (cast(double) opHit + opMiss));
      else
	sb ~= "0.0";
      sb ~= format("\nSwap count =    %s\n", swapCount);
      return sb;
    }
  }

  /**
   * Singleton object for cache statistics.
   */
  protected CacheStats _cacheStats;

  /**
   * <p>Return the current cache statistics for this Buddy Instance.</p>
   *
   * @return  cache statistics
   */
  CacheStats getCacheStats()
  {
    return _cacheStats;
  }

  ~this() {
    foreach (ref dom; _domains) {
      dom.reset();
      dom.freeMem();
    }
  }

}

private bool bitIsSet(uint n, uint i) {return (n & (1 << i)) != 0;}

private ulong mulmod(ulong a, ulong b, ulong c) {
  return (a*b)%c;
}

/* NOT REQUIRED -- REPLACED by bsr */
// static uint numberOfBits(uint src)
// {
//   uint b;

//   if (src == 0)
//     return 0;
  
//   for (b=(uint.sizeof *8)-1 ; b>0 ; --b)
//     if (bitIsSet(src,b))
//       return b+1;

//   return 1;
// }

private bool isWitness(uint witness, uint src)
{
  import core.bitop;
  uint bitNum = bsr(src-1);
  // uint bitNum = numberOfBits(src-1) -1;
  // import std.stdio;
  // writeln("bitNum: ", bitNum);

  uint d = 1;

  for (int i = bitNum ; i >= 0 ; --i)
    {
      uint x = d;

      d = cast(uint) mulmod(d, d, src);
      // writeln("d: ", d, " i: ", i);
    
      if (d == 1  &&  x != 1  &&  x != src-1)
	return true;
    
      if (bitIsSet(src-1, i))
	{
	  d = cast(uint) mulmod(d, witness, src);
	  // writeln("d: ", d);
	}
    }

  return d != 1;
}


private bool isMillerRabinPrime(uint src)
{
  import std.random;
  enum uint CHECKTIMES = 1000;
  for (size_t n=0 ; n != CHECKTIMES ; ++n)
    {
      // import std.stdio;
      // writeln("src: ", src);
      uint witness = uniform(1, src);

      if (isWitness(witness, src)) {
	// writeln("Found witness: ", witness);
	return false;
      }
    }

  return true;
}

// want to return a false if the arguments are equal
private bool hasFactor(uint n, uint m) {return n != m && n % m == 0;}

private bool hasEasyFactors(uint src)
{
  return hasFactor(src, 3)
    || hasFactor(src, 5)
    || hasFactor(src, 7)
    || hasFactor(src, 11)
    || hasFactor(src, 13);
}


private bool isPrime(uint src) {
  if (hasEasyFactors(src))
    return false;
  return isMillerRabinPrime(src);
}


private bool isEven(uint n) {return !(n & 0x1);}

uint primeGte(uint src) {
  if (isEven(src)) ++src;
  while (!isPrime(src)) src += 2;
  return src;
}


uint primeLte(uint src) {
  if (isEven(src)) --src;
  while (!isPrime(src)) src -= 2;
  return src;
}

unittest {
  import std.stdio;
  for (size_t n=0 ; n<1000 ; ++n) {
    uint x = uniform(0, 100000);
    uint a = primeLte(x);
    uint b = primeGte(x);
    // printf("%d: %d, %d  ", x, );
    writeln("x: ", x, "  <x: ", a, ";  >x: ", b);
  }
}

int bdd_error(BddError v)
{
  throw new BddException(v);
}


enum BddError
  {   BDD_MEMORY = -1, // Out of memory
      BDD_VAR = -2, // Unknown variable
      BDD_RANGE = -3,
      // Variable value out of range(not in domain)
      BDD_DEREF = -4,
      // Removing external reference to unknown node
      BDD_RUNNING = -5,
      // Called bdd_init() twice whithout bdd_done()
      BDD_FILE = -6, // Some file operation failed
      BDD_FORMAT = -7, // Incorrect file format
      BDD_ORDER = -8,
      // Vars. not in order for vector based functions
      BDD_BREAK = -9, // User called break
      BDD_VARNUM = -10,
      // Different number of vars. for vector pair
      BDD_NODES = -11,
      // Tried to set max. number of _nodes to be fewer
      // than there already has been allocated
      BDD_OP = -12, // Unknown operator
      BDD_VARSET = -13, // Illegal variable set
      BDD_VARBLK = -14, // Bad variable block operation
      BDD_DECVNUM = -15,
      // Trying to decrease the number of variables
      BDD_REPLACE = -16,
      // Replacing to already existing variables
      BDD_NODENUM = -17,
      // Number of _nodes reached user defined maximum
      BDD_ILLBDD = -18, // Illegal BDD argument
      BDD_SIZE = -19, // Illegal size argument

      BVEC_SIZE = -20, // Mismatch in bitvector size
      BVEC_SHIFT = -21,
      // Illegal shift-left/right parameter
      BVEC_DIVZERO = -22
      }

enum errorstrings =
  ["",			// empty for 0
   "Out of memory",
   "Unknown variable",
   "Value out of range",
   "Unknown BDD root dereferenced",
   "bdd_init() called twice",
   "File operation failed",
   "Incorrect file format",
   "Variables not in ascending order",
   "User called break",
   "Mismatch in size of variable sets",
   "Cannot allocate fewer _nodes than already in use",
   "Unknown operator",
   "Illegal variable set",
   "Bad variable block operation",
   "Trying to decrease the number of variables",
   "Trying to replace with variables already in the BDD",
   "Number of _nodes reached user defined maximum",
   "Unknown BDD - was not in node table",
   "Bad size argument",
   "Mismatch in bitvector size",
   "Illegal shift-left/right parameter",
   "Division by zero"];

private static class BddException: Throwable
{
  this(string err="Unknown Exception")
  {
    super(err);
  }
  this(BddError err)
  {
    int index = -(cast(int) err);
    assert(index >= 0);
    super(errorstrings[index]);
  }

}

private static class ReorderException: Throwable
{
  /**
   * Version ID for serialization.
   */
  enum long serialVersionUID = 3256727264505772345L;
  this()
  {
    super("Reorder Exception!");
  }
}
