module esdl.intf.btor.btor;

import esdl.intf.btor.api;
import esdl.intf.btor.types;

class Boolector
{
  Btor* _btor;

  this() {
    _btor = boolector_new();
    _nodes.reserve(32);
    _vecSorts.reserve(16);
    // this.setOpt(BtorOption.AUTO_CLEANUP, 1);
  }

  BoolectorNodeP[] _nodes;
  BoolectorSort[] _vecSorts;
  BoolectorSort _boolSort;

  ~this() {
    foreach (node; _nodes) boolector_release(_btor, node);
    foreach (sort; _vecSorts) boolector_release_sort(_btor, sort);
    if (_boolSort !is null) boolector_release_sort(_btor, _boolSort);
    assert (boolector_get_refs (_btor) == 0);
    boolector_delete(_btor);
  }
  
  Btor* native() {
    return _btor;
  }

  alias native this;

  void setOpt(BtorOption opt, uint val) {
    boolector_set_opt(_btor, opt, val);
  }

  void srandom(uint seed) {
    setOpt(BtorOption.SEED, seed);
  }

  BvExpr constant(int val) {
    BoolectorNodeP r = boolector_int(_btor, val, vecSort(32));
    addNode(r);
    return BvExpr(this, r, 32, true);
  }
	      
  BvExpr constant(uint val) {
    BoolectorNodeP r = boolector_int(_btor, val, vecSort(32));
    addNode(r);
    return BvExpr(this, r, 32, false);
  }
	      
  BvExpr constant(long val) {
    BoolectorNodeP lo = boolector_int(_btor, cast(int) val, vecSort(32));
    BoolectorNodeP hi = boolector_int(_btor, cast(int) (val >> 32), vecSort(32));
    BoolectorNodeP r = boolector_concat(_btor, hi, lo);
    boolector_release(_btor, lo);
    boolector_release(_btor, hi);
    addNode(r);
    return BvExpr(this, r, 64, true);
  }
	      
  BvExpr constant(ulong val) {
    BoolectorNodeP lo = boolector_int(_btor, cast(uint) val, vecSort(32));
    BoolectorNodeP hi = boolector_int(_btor, cast(uint) (val >> 32), vecSort(32));
    BoolectorNodeP r = boolector_concat(_btor, hi, lo);
    boolector_release(_btor, lo);
    boolector_release(_btor, hi);
    addNode(r);
    return BvExpr(this, r, 64, false);
  }
	      
  BtorSolverResult sat() {
    return cast (BtorSolverResult) boolector_sat(_btor);
  }

  void print() {
    import core.stdc.stdio: stdout;
    import std.string: toStringz;
    boolector_print_model(_btor, cast(char*) "btor".toStringz(), stdout);
  }

  void addNode(BoolectorNodeP node) {
    _nodes ~= node;
  }

  BoolectorSort vecSort(uint n) {
    foreach (sort; _vecSorts) {
      if (boolector_bitvec_sort_get_width(_btor, sort) == n)
	return sort;
    }
    BoolectorSort sort = boolector_bitvec_sort(_btor, n);
    _vecSorts ~= sort;
    return sort;
  }
  
  BoolectorSort boolSort() {
    if (_boolSort !is null) return _boolSort;
    _boolSort = boolector_bool_sort(_btor);
    return _boolSort;
  }

  BvExpr makeBvec(uint n, string name="") {
    import std.string: toStringz;
    BoolectorSort sort = vecSort(n);
    BoolectorNodeP node = name == "" ?
      boolector_var(_btor, sort, null) :
      boolector_var(_btor, sort, name.toStringz());
    addNode(node);
    return BvExpr(this, node, n, true);
  }

  BvExpr makeUbvec(uint n, string name="") {
    import std.string: toStringz;
    BoolectorSort sort = vecSort(n);
    BoolectorNodeP node = name == "" ?
      boolector_var(_btor, sort, null) :
      boolector_var(_btor, sort, name.toStringz());
    addNode(node);
    return BvExpr(this, node, n, false);
  }

  BoolExpr makeBool(string name="") {
    import std.string: toStringz;
    BoolectorNodeP node = name == "" ?
      boolector_var(_btor, boolSort(), null) :
      boolector_var(_btor, boolSort(), name.toStringz());
    addNode(node);
    return BoolExpr(this, node);
  }
}

// struct Sort {
//   BoolectorSort _sort;
//   Boolector _boolector;

//   alias _sort this;
  
//   @disable this();

//   this(Boolector boolector, BoolectorSort sort) {
//     _boolector = boolector;
//     _sort = sort;
//   }
// }

enum IntType: ubyte { INT32, UINT32, INT64, UINT64 }

IntType commonType(IntType a, IntType b) {
  if (a > b) return a;
  else       return b;
}

struct BvExpr {
  BoolectorNodeP _node;
  Boolector _boolector;
  bool _signed;
  uint _size;

  alias _node this;

  @disable this();

  Btor* context() {
    return _boolector;
  }

  this (Boolector boolector, BoolectorNodeP node, IntType type) {
    uint size;
    bool signed;
    if (type == IntType.INT32)  size = 32; signed = true;
    if (type == IntType.UINT32) size = 32; signed = false;
    if (type == IntType.INT64)  size = 64; signed = true;
    if (type == IntType.UINT64) size = 64; signed = false;
    this(boolector, node, size, signed);
  }
  
  this (Boolector boolector, BoolectorNodeP node, uint size, bool signed) {
    _boolector = boolector;
    _node = node;
    _size = size;
    _signed = signed;
  }

  IntType getIntType() {
    assert (_size <= 64);
    if (_signed is true) return _size <= 32 ? IntType.INT32  : IntType.INT64;
    else                 return _size <= 32 ? IntType.UINT32 : IntType.UINT64;
  }

  BvExpr convertTo(IntType intType) {
    final switch (intType) {
    case IntType.INT32: return this.toInt32();
    case IntType.UINT32: return this.toUint32();
    case IntType.INT64: return this.toInt64();
    case IntType.UINT64: return this.toUint64();
    }
  }

  BvExpr extendTo(uint n, bool signed) {
    assert (n >= _size);
    BoolectorNodeP r;
    if (_signed) r = boolector_sext (_boolector, _node, n - _size);
    else         r = boolector_uext (_boolector, _node, n - _size);
    _boolector.addNode(r);
    return BvExpr(_boolector, r, n, signed);
  }

  BvExpr toInt32() {
    if (_size == 32) {
      BvExpr expr = this;		// postblit does not register node with boolctor instance
      expr._signed = true;
      return expr;
    }
    else return extendTo(32, true);
  }

  BvExpr toUint32() {
    if (_size == 32) {
      BvExpr expr = this;		// postblit does not register node with boolctor instance
      expr._signed = false;
      return expr;
    }
    else return extendTo(32, false);
  }

  BvExpr toInt64() {
    if (_size == 64) {
      BvExpr expr = this;		// postblit does not register node with boolctor instance
      expr._signed = true;
      return expr;
    }
    else return extendTo(64, true);
  }

  BvExpr toUint64() {
    if (_size == 64) {
      BvExpr expr = this;		// postblit does not register node with boolctor instance
      expr._signed = false;
      return expr;
    }
    else return extendTo(64, false);
  }

  BvExpr opUnary(string op)() if(op == "~") {
    BoolectorNodeP node = boolector_not(context(), _node);
    _boolector.addNode(node);
    return BvExpr(context(), node, _size, _signed);
  }

  BvExpr opUnary(string op)() if(op == "-") {
    BoolectorNodeP node = boolector_neg(context(), _node);
    _boolector.addNode(node);
    return BvExpr(context(), node, _size, _signed);
  }

  BvExpr opBinary(string op)(BvExpr other)
       if (op == "&" || op == "|" || op == "^" || op == "+" ||
	   op == "-" || op == "*" || op == "/" || op == "%" ||
	   op == "<<" || op == ">>" || op == ">>>") {

	 BvExpr lexpr = this;
	 BvExpr rexpr = other;
	 
	 IntType type = commonType(lexpr.getIntType(), rexpr.getIntType());

	 lexpr = lexpr.convertTo(type);
	 rexpr = rexpr.convertTo(type);
	 
	 BoolectorNodeP r = null;
	 static if(op == "&") {
	   r = boolector_and(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == "|") {
	   r = boolector_or(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == "^") {
	   r = boolector_xor(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == "+") {
	   r = boolector_add(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == "-") {
	   r = boolector_sub(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == "*") {
	   r = boolector_mul(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == "/") {
	   if (type == IntType.INT64 || type == IntType.INT32) {
	     r = boolector_sdiv(context(), lexpr._node, rexpr._node);
	   }
	   else {
	     r = boolector_udiv(context(), lexpr._node, rexpr._node);
	   }
	 }
	 static if(op == "%") {
	   if (type == IntType.INT64 || type == IntType.INT32) {
	     r = boolector_srem(context(), lexpr._node, rexpr._node);
	   }
	   else {
	     r = boolector_urem(context(), lexpr._node, rexpr._node);
	   }
	 }
	 static if(op == "<<") {
	   r = boolector_sll(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == ">>") {
	   r = boolector_srl(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == ">>>") {
	   r = boolector_sra(context(), lexpr._node, rexpr._node);
	 }
	 _boolector.addNode(r);
	 return BvExpr(_boolector, r, type);
       }

  BvExpr opBinary(string op)(BvExpr other) if (op == "~")
    {
      BoolectorNodeP r = boolector_concat(context(), _node, other._node);
      _boolector.addNode(r);
      return BvExpr(_boolector, r, _size + other._size, _signed);
    }

  BoolExpr opLogic(string op)(BvExpr other)
       if (op == "==" || op == "<=" || op == ">=" || 
	   op == "!=" || op == "<"  || op == ">") {

	 BvExpr lexpr = this;
	 BvExpr rexpr = other;
	 
	 IntType type = commonType(lexpr.getIntType(), rexpr.getIntType());

	 lexpr = lexpr.convertTo(type);
	 rexpr = rexpr.convertTo(type);
	 
	 BoolectorNodeP r = null;

	 static if(op == "==") {
	   r = boolector_eq(context(), lexpr._node, rexpr._node);
	 }
	 static if(op == "<=") {
	   if (type == IntType.INT64 || type == IntType.INT32) {
	     r = boolector_slte(context(), lexpr._node, rexpr._node);
	   }
	   else {
	     r = boolector_ulte(context(), lexpr._node, rexpr._node);
	   }
	 }
	 static if(op == ">=") {
	   if (type == IntType.INT64 || type == IntType.INT32) {
	     r = boolector_sgte(context(), lexpr._node, rexpr._node);
	   }
	   else {
	     r = boolector_ugte(context(), lexpr._node, rexpr._node);
	   }
	 }
	 static if(op == "!=") {
	   r = boolector_not (context(),
			      boolector_eq(context(), lexpr._node, rexpr._node));
	 }
	 static if(op == "<") {
	   if (type == IntType.INT64 || type == IntType.INT32) {
	     r = boolector_slt(context(), lexpr._node, rexpr._node);
	   }
	   else {
	     r = boolector_ult(context(), lexpr._node, rexpr._node);
	   }
	 }
	 static if(op == ">") {
	   if (type == IntType.INT64 || type == IntType.INT32) {
	     r = boolector_sgt(context(), lexpr._node, rexpr._node);
	   }
	   else {
	     r = boolector_ugt(context(), lexpr._node, rexpr._node);
	   }
	 }
	 _boolector.addNode(r);
	 return BoolExpr(_boolector, r);
       }


  BvExpr opSlice(uint lower, uint upper) {
    import std.stdio;
    import std.conv: to;
    BoolectorNodeP r = boolector_slice(context(), _node, upper-1, lower);
    // assert (boolector_get_width(context(), _node) == upper - lower,
    // 	    boolector_get_width(context(), _node).to!string());
    _boolector.addNode(r);
    return BvExpr(_boolector, r, upper - lower, false);
  }

  void print() {
    import std.stdio: writeln;
    import core.stdc.string: strlen;
    auto assignment = boolector_bv_assignment(_boolector, _node);
    
    writeln(assignment[0..strlen(assignment)]);
    boolector_free_bv_assignment(_boolector, assignment);
  }
}

BvExpr and(BvExpr a, BvExpr b) {return a & b;}
BvExpr or(BvExpr a, BvExpr b) {return a | b;}
BvExpr xor(BvExpr a, BvExpr b) {return a ^ b;}
BvExpr add(BvExpr a, BvExpr b) {return a + b;}
BvExpr sub(BvExpr a, BvExpr b) {return a - b;}
BvExpr mul(BvExpr a, BvExpr b) {return a * b;}
BvExpr div(BvExpr a, BvExpr b) {return a / b;}
BvExpr rem(BvExpr a, BvExpr b) {return a % b;}
BvExpr llsh(BvExpr a, BvExpr b) {return a << b;}
BvExpr lrsh(BvExpr a, BvExpr b) {return a >> b;}
BvExpr arsh(BvExpr a, BvExpr b) {return a >>> b;}
BvExpr concat(BvExpr a, BvExpr b) {return a ~ b;}

struct BoolExpr {
  BoolectorNodeP _node;
  Boolector _boolector;

  Btor* context() {
    return _boolector;
  }

  alias _node this;

  @disable this();

  this (Boolector boolector, BoolectorNodeP node) {
    _boolector = boolector;
    _node = node;
  }

  void enforce() {		// assert is a keyword
    boolector_assert(_boolector, this);
  }
  
  void assume() {
    boolector_assume(_boolector, this);
  }
  
  BoolExpr and(BoolExpr other) {
    BoolectorNodeP r = boolector_and(context(), _node, other._node);
    return BoolExpr(_boolector, r);
  }

  BoolExpr or(BoolExpr other) {
    BoolectorNodeP r = boolector_or(context(), _node, other._node);
    return BoolExpr(_boolector, r);
  }

  BoolExpr not() {
    BoolectorNodeP r = boolector_not(context(), _node);
    return BoolExpr(_boolector, r);
  }
}

BoolExpr gt(BvExpr a, BvExpr b) {return a.opLogic!(">")(b);}
BoolExpr lt(BvExpr a, BvExpr b) {return a.opLogic!("<")(b);}
BoolExpr gte(BvExpr a, BvExpr b) {return a.opLogic!(">=")(b);}
BoolExpr lte(BvExpr a, BvExpr b) {return a.opLogic!("<=")(b);}
BoolExpr eq(BvExpr a, BvExpr b) {return a.opLogic!("==")(b);}
BoolExpr neq(BvExpr a, BvExpr b) {return a.opLogic!("!=")(b);}

