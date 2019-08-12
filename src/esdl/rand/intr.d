module esdl.rand.intr;

import std.traits: isIntegral, isSigned;
import std.container.array;
import std.traits: Unsigned, Signed, isUnsigned, isSigned;
import esdl.data.bvec;
import esdl.rand.misc: CstBinVecOp, CstBinBddOp, CstBddOp, _esdl__RandGen;

T larger(T) (T a, T b) {
  if (a > b) return a;
  else return b;
}

T smaller(T) (T a, T b) {
  if (a < b) return a;
  else return b;
}

alias IntR = IntRange!int;
alias IntRS = IntRangeSet!int;
alias UIntR = IntRange!uint;
alias UIntRS = IntRangeSet!uint;

alias LongR = IntRange!long;
alias LongRS = IntRangeSet!long;
alias ULongR = IntRange!ulong;
alias ULongRS = IntRangeSet!ulong;

interface IntegralRangeSet
{
}


enum INTTYPE: ubyte { UINT, INT, ULONG, LONG }

struct UniRange
{
  INTTYPE _type;
  ulong _min;
  ulong _max;
  bool _full;

  this(bool full, INTTYPE iType) {
    assert(full);
    _full = full;
    _type = iType;
  }
  
  this(long min, long max, INTTYPE iType) {
    _full = false;
    _min = min;
    _max = max;
    _type = iType;
  }

  this(IR)(IR iRange) if (is (IR: IntRange!T, T)) {
    static if (is (IR: IntRange!T, T)) {
      _full = iRange._full;
      static if (is (T == uint)) {
	this(iRange._min, iRange._max, INTTYPE.UINT);
      }
      else static if (is (T == int)) {
	this(iRange._min, iRange._max, INTTYPE.INT);
      }
      static if (is (T == ulong)) {
	this(iRange._min, iRange._max, INTTYPE.ULONG);
      }
      static if (is (T == long)) {
	this(iRange._min, iRange._max, INTTYPE.LONG);
      }
    }
  }
  
  
  this(CstBinBddOp op, INTTYPE iType, long val, bool reverse=false) {
    if (iType == INTTYPE.UINT) {
      uint iVal = cast(uint) val;
      assert (iVal == val);
      UIntR iRange = UIntR(op, iVal, reverse);
      this(iRange);
    }
    else if (iType == INTTYPE.INT) {
      int iVal = cast(int) val;
      assert (iVal == val);
      IntR iRange = IntR(op, iVal, reverse);
      this(iRange);
    }
    else if (iType == INTTYPE.ULONG) {
      ulong iVal = cast(ulong) val;
      assert (iVal == val);
      ULongR iRange = ULongR(op, iVal, reverse);
      this(iRange);
    }
    else if (iType == INTTYPE.LONG) {
      long iVal = cast(long) val;
      assert (iVal == val);
      LongR iRange = LongR(op, iVal, reverse);
      this(iRange);
    }
    else {
      assert (false);
    }
  }

  void map(INTTYPE iType) {
    final switch(_type) {
    case INTTYPE.UINT:
      final switch (iType) {
      case INTTYPE.UINT:
	UIntR iRange = cast (UIntR) this;
	UIntR tRange = cast (UIntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.INT:
	UIntR iRange = cast (UIntR) this;
	IntR tRange = cast (IntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.ULONG:
      case INTTYPE.LONG:
	assert (false);
      }
      break;
    case INTTYPE.INT:
      final switch (iType) {
      case INTTYPE.UINT:
	IntR iRange = cast (IntR) this;
	UIntR tRange = cast (UIntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.INT:
	IntR iRange = cast (IntR) this;
	IntR tRange = cast (IntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.ULONG:
      case INTTYPE.LONG:
	assert (false);
      }
      break;
    case INTTYPE.ULONG:
      final switch(iType) {
      case INTTYPE.UINT:
	ULongR iRange = cast (ULongR) this;
	UIntR tRange = cast (UIntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.INT:
	ULongR iRange = cast (ULongR) this;
	IntR tRange = cast (IntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.ULONG:
	ULongR iRange = cast (ULongR) this;
	ULongR tRange = cast (ULongR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.LONG:
	ULongR iRange = cast (ULongR) this;
	LongR tRange = cast (LongR) iRange;
	this = UniRange(tRange);
	break;
      }
      break;
    case INTTYPE.LONG:
      final switch(iType) {
      case INTTYPE.UINT:
	LongR iRange = cast (LongR) this;
	UIntR tRange = cast (UIntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.INT:
	LongR iRange = cast (LongR) this;
	IntR tRange = cast (IntR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.ULONG:
	LongR iRange = cast (LongR) this;
	ULongR tRange = cast (ULongR) iRange;
	this = UniRange(tRange);
	break;
      case INTTYPE.LONG:
	LongR iRange = cast (LongR) this;
	LongR tRange = cast (LongR) iRange;
	this = UniRange(tRange);
	break;
      }
    }
  }

  string toString() {
    final switch(_type) {
    case INTTYPE.UINT:
      UIntR iRange = UIntR(this);
      return iRange.toString();
    case INTTYPE.INT:
      IntR iRange = IntR(this);
      return iRange.toString();
    case INTTYPE.ULONG:
      ULongR iRange = ULongR(this);
      return iRange.toString();
    case INTTYPE.LONG:
      LongR iRange = LongR(this);
      return iRange.toString();
    }
  }

  ulong count() {
    final switch(_type) {
    case INTTYPE.UINT:
      UIntR iRange = UIntR(this);
      return iRange.count();
    case INTTYPE.INT:
      IntR iRange = IntR(this);
      return iRange.count();
    case INTTYPE.ULONG:
      ULongR iRange = ULongR(this);
      return iRange.count();
    case INTTYPE.LONG:
      LongR iRange = LongR(this);
      return iRange.count();
    }
  }

  bool isEmpty() {
    return (this._full is false) && (this._min == this._max);
  }

  bool isFull() {
    return this._full;
  }
}

struct IntRange(T) if (isIntegral!T) {
  T _min = T.min;
  T _max = T.min;

  bool _full;
  
  T min() {
    return _min;
  }
  
  T max() {
    return _max;
  }
  
  Unsigned!T _count;

  static IntRange!T full() {
    return IntRange!T(true);
  }

  this(bool full) {
    assert(full);
    _full = full;
  }
  
  this(T min, T max) {
    _full = false;
    _min = min;
    _max = max;
  }

  this(UniRange uRange) {
    if (uRange._type == INTTYPE.UINT) {
      assert (is (T == uint));
    }
    else if (uRange._type == INTTYPE.INT) {
      assert (is (T == int));
    }
    else if (uRange._type == INTTYPE.ULONG) {
      assert (is (T == ulong));
    }
    else if (uRange._type == INTTYPE.LONG) {
      assert (is (T == long));
    }
    _min = cast(T) uRange._min;
    assert (_min == uRange._min);
    _max = cast(T) uRange._max;
    assert (_max == uRange._max);
    _full = uRange._full;
  }

  this(CstBinBddOp op, T val, bool reverse=false) {
    if (! reverse) {
      final switch(op) {
      case CstBinBddOp.LTH: _min = T.min; _max = val; break;
      case CstBinBddOp.GTH: _min = ++val; _max = T.max; break;
      case CstBinBddOp.LTE: _min = T.min; _max = ++val; break;
      case CstBinBddOp.GTE: _min = val; _max = T.max; break;
      case CstBinBddOp.EQU: _min = val; _max = ++val; break;
      case CstBinBddOp.NEQ: _min = ++val; _max = val; break;
      }
    }
    else {
      final switch(op) {
      case CstBinBddOp.GTH: _min = T.min; _max = val; break;
      case CstBinBddOp.LTH: _min = ++val; _max = T.max; break;
      case CstBinBddOp.GTE: _min = T.min; _max = ++val; break;
      case CstBinBddOp.LTE: _min = val; _max = T.max; break;
      case CstBinBddOp.EQU: _min = val; _max = ++val; break;
      case CstBinBddOp.NEQ: _min = ++val; _max = val; break;
      }
    }
  }

  G opCast(G)() if (is (G: IntRange!U, U)) {
    static if (is (G: IntRange!U, U)) {
      G casted;
      static if (U.sizeof == T.sizeof) { // signed/unsigned
	casted._min = cast(U) this._min;
	casted._max = cast(U) this._max;
	return casted;
      }
      else static if (isSigned!T && isUnsigned!U) {
	return cast(G) (cast(IntRange!(Unsigned!T)) this);
      }
      else static if (isUnsigned!T && isSigned!U) {
	return cast(G) (cast(IntRange!(Signed!T)) this);
      }
      else static if (is (U: T)) {
	if ((this._full is true) ||
	    (this._min <= U.min && this._max > U.max) ||
	    (this._max < this._min && this._min <= U.min) ||
	    (this._max < this._min && this._max > U.max)) {
	  casted._full = true;
	}
	if (this._min < U.min || this._min > U.max) {
	  casted._min = U.min;
	}
	else {
	  casted._min = cast(U) this._min;
	}
	if (this._max < U.min || this._max > U.max) {
	  casted._max = U.min;
	}
	else {
	  casted._max = cast(U) this._max;
	}
	return casted;
      }
    }
  }
  
  bool opBinary(string op)(ref IntRange other) if (op == "|") {
    bool result = false;
    if (this._full) {
      result = true;
    }
    else if (other._full) {
      this._full = other._full;
      this._min = other._min;
      this._max = other._max;
      result = true;
    }
    else if (this._min == this._max) { // null range
      this._full = other._full;
      this._min = other._min;
      this._max = other._max;
      result = true;
    }
    else if (other._min == other._max) { // null range
      result = true;
    }
    // both ranges normal
    else if (this._min < this._max && other._min < other._max) {
      if (this._max < other._min || this._min > other._min) {
	result = false;
      }
      else {
	this._min = smaller(this._min, other._min);
	this._max = larger(this._max, other._max);
	result = true;
      }
    }
    else if (this._min > this._max && other._min < other._max) {
      // [33, 64) ,[64, 33)
      if (this._max >= other._min && this._min <= other._max) {
	this = this.init;
	result = true;
      }
      // [60, 0), [-16, 32)
      else if (this._max >= other._min) {
	this._max = other._max;
	result = true;
      }
      // [60, 0), [16, 64)
      else if (this._min <= other._max) {
	this._min = other._min;
	result = true;
      }
      else {
	result = false;
      }
    }
    else if (other._min > other._max && this._min < this._max) {
      // [33, 64) ,[64, 33)
      if (other._max >= this._min && other._min <= this._max) {
	this = this.init;
	result = true;
      }
      // [60, 0), [32, 64)
      else if (other._max >= this._min) {
	this._min = other._min;
	result = true;
      }
      // [32, 64) ,[60, 0)
      else if (other._min <= this._max) {
	this._max = other._max;
	result = true;
      }
      else {
	result = false;
      }
    }
    else if (this._min > this._max && other._min > other._max) {
      this._min = smaller(this._min, other._min);
      this._max = larger(this._max, other._max);
      result = true;
    }
    return result;
  }
    
  int opBinary(string op)(ref IntRange other)
    if (op == "&") {
      int rcount;
      if (this._full) {
	this = other;
	rcount = 1;
      }
      else if (other._full) {
	rcount = 1;
      }
      else if (this._min == this._max) {
	assert(false);
	// rcount = 0;
      }
      else if (other._min == other._max) {
	assert(false);
	// rcount = 0;
      }
      // both ranges normal
      else if (this._min < this._max && other._min < other._max) {
	if (this._max <= other._min || other._max <= this._min) {
	  rcount = 0;
	}
	else {
	  this._min = larger(this._min, other._min);
	  this._max = smaller(this._max, other._max);
	  rcount = 1;
	}
      }
      else if (this._min > this._max && other._min < other._max) {
	IntRange!T s1;
	IntRange!T s2;
	int count;
	if (other._min < this._max) {
	  s1._min = other._min;
	  s1._max = smaller(other._max, this._max);
	  count += 1;
	}
	if (other._max > this._min) {
	  if (count == 0) {
	    s1._max = other._max;
	    s1._min = larger(other._min, this._min);
	    count += 1;
	  }
	  else if (count == 1) {
	    s2._max = other._max;
	    s2._min = larger(other._min, this._min);
	    count += 1;
	  }
	}
	if (count == 1) {
	  this = s1;
	}
	if (count == 2) {
	  this = s1;
	  other = s2;
	}
	rcount = count;
      }
      //  [96, 512) ,[256, 32)
      else if (other._min > other._max && this._min < this._max) {
	IntRange!T s1;
	IntRange!T s2;
	int count;
	if (this._min < other._max) {
	  s1._min = this._min;
	  s1._max = smaller(this._max, other._max);
	  count += 1;
	}
	if (this._max > other._min) {
	  if (count == 0) {
	    s1._max = this._max;
	    s1._min = larger(this._min, other._min);
	    count += 1;
	  }
	  else if (count == 1) {
	    s2._max = this._max;
	    s2._min = larger(this._min, other._min);
	    count += 1;
	  }
	}
	if (count == 1) {
	  this = s1;
	}
	if (count == 2) {
	  this = s1;
	  other = s2;
	}
	rcount = count;
      }
      else if (this._min > this._max && other._min > other._max) {
	this._min = larger(this._min, other._min);
	this._max = smaller(this._max, other._max);
	rcount = 1;
      }
      return rcount;
    }

  string toString() {
    import std.string;
    string str = T.stringof ~ ": ";
    if (_full) {
      return str ~ "[-, -)";
    }
    return str ~ format("[%s, %s)", this._min, this._max);
  }

  Unsigned!T count() {
    if (this._full) {
      assert(false, "Can not count a full range");
    }
    else {
      return cast(Unsigned!T) (_max - this._min);
    }
  }

  bool isEmpty() {
    return (this._full is false) && (this._min == this._max);
  }

  bool isFull() {
    return this._full;
  }

}

unittest {
  import std.stdio;

  LongR foo = LongR(-2147483680, -2147483664);
  IntR bar = cast(IntR) foo;

  assert (bar.isEmpty());
  writeln("Cast Test 1 Passed");

  foo = LongR(-2147483680, 0);
  bar = cast(IntR) foo;

  assert (bar == IntR(int.min, 0));
  writeln("Cast Test 2 Passed");

  foo = LongR(-2147483680, 2147483680);
  bar = cast(IntR) foo;

  assert (bar.isFull());
  writeln("Cast Test 3 Passed");

  foo = LongR(-32, 32);
  bar = cast(IntR) foo;

  assert (bar == IntR(-32, 32));
  writeln("Cast Test 4 Passed");

  foo = LongR(0, 2147483680);
  bar = cast(IntR) foo;

  assert (bar == IntR(0, int.min));
  writeln("Cast Test 5 Passed");

  foo = LongR(2147483676, 2147483680);
  bar = cast(IntR) foo;

  assert (bar.isEmpty());
  writeln("Cast Test 6 Passed");

  foo = LongR(-2147483664, -2147483680);
  bar = cast(IntR) foo;

  assert (bar.isFull());
  writeln("Cast Test 7 Passed");

  foo = LongR(0, -2147483680);
  bar = cast(IntR) foo;

  assert (bar == IntR(0, int.min));
  writeln("Cast Test 8 Passed");

  foo = LongR(2147483680, -2147483680);
  bar = cast(IntR) foo;

  assert (bar.isEmpty());
  writeln("Cast Test 9 Passed");

  foo = LongR(32, -32);
  bar = cast(IntR) foo;

  assert (bar == IntR(32, -32));
  writeln("Cast Test 10 Passed");

  foo = LongR(2147483680, 0);
  bar = cast(IntR) foo;

  assert (bar == IntR(int.min, 0));
  writeln("Cast Test 11 Passed");

  foo = LongR(2147483680, 2147483676);
  bar = cast(IntR) foo;

  assert (bar.isFull());
  writeln("Cast Test 12 Passed");
}


unittest {
  import std.stdio;
  import esdl.data.bvec;

  alias irange = IntRange!int;
  
  // if (this._max == this._min) {
  IntRange!int test1_r1 = IntRange!int(true);
  IntRange!int test1_r2 = IntRange!int(0, 32);

  test1_r1 | test1_r2;

  assert (test1_r1._full);
  writeln("Test 1 Passed");

  // else if (other._max == other._min) {
  IntRange!int test2_r1 = IntRange!int(0, 32);
  IntRange!int test2_r2 = IntRange!int(true);

  test2_r1 | test2_r2;

  assert (test2_r1._full);
  writeln("Test 2 Passed");


  // else if (this._min < this._max && other._min < other._max) {
  irange test3_r1 = irange(0, 32);
  irange test3_r2 = irange(32, 64);

  assert(test3_r1 | test3_r2);
  assert (test3_r1 == irange(0, 64));
  writeln("Test 3a Passed");

  test3_r1 = irange(0, 32);
  test3_r2 = irange(33, 64);

  if (! (test3_r1 | test3_r2)) {
    writeln("Test 3b Passed");
  }

  test3_r1 = irange(33, 64);
  test3_r2 = irange(0, 32);

  if (! (test3_r1 | test3_r2)) {
    writeln("Test 3c Passed");
  }

  test3_r1 = irange(-5, 16);
  test3_r2 = irange(14, 38);

  assert(test3_r1 | test3_r2);
  assert (test3_r1 == irange(-5, 38));
  writeln("Test 3d Passed");

  // else if (other._min > other._max && this._min < this._max) {

  irange test4_r1 = irange(32, 64);
  irange test4_r2 = irange(64, 32);

  assert(test4_r1 | test4_r2);
  assert(test4_r1 == irange.init);
  writeln("Test 4a Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(60, 0);

  assert(test4_r1 | test4_r2);
  assert(test4_r1 == irange(32,0));
  writeln("Test 4b Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(96, 0);

  assert(! (test4_r1 | test4_r2));
  writeln("Test 4c Passed");
  // 	      else if (this._min > this._max && other._min < other._max) {

  irange test5_r1 = irange(60, 0);
  irange test5_r2 = irange(16, 64);
  assert(test5_r1 | test5_r2);
  assert(test5_r1 == irange(16, 0));
  writeln("Test 5a Passed");

  test5_r1 = irange(60, 0);
  test5_r2 = irange(-16, 32);
  assert(test5_r1 | test5_r2);
  assert(test5_r1 == irange(60, 32));
  writeln("Test 5b Passed");
  
  // [33, 64) ,[64, 33)
  test5_r1 = irange(33, 64);
  test5_r2 = irange(64, 33);
  assert(test5_r1 | test5_r2);
  assert(test5_r1 == irange.init);
  writeln("Test 5c Passed");
  

  // else if (this._min > this._max && other._min > other._max) {
  irange test6_r1 = irange(64, -64);
  irange test6_r2 = irange(32, -32);
  assert(test6_r1 | test6_r2);
  assert(test6_r1 == irange(32, -32));
  writeln("Test 6a Passed");
		
  test6_r1 = irange(64, -32);
  test6_r2 = irange(32, -64);
  assert(test6_r1 | test6_r2);
  assert(test6_r1 == irange(32, -32));
  writeln("Test 6b Passed");
		

}

unittest {
  import std.stdio;
  import esdl.data.bvec;

  alias irange = IntRange!int;
  
  // if (this._max == this._min) {
  IntRange!int test1_r1 = IntRange!int(true);
  IntRange!int test1_r2 = IntRange!int(0, 32);

  assert((test1_r1 & test1_r2) == 1);
  assert(test1_r1 == irange(0, 32));
  writeln("AND Test 1 Passed");

  // else if (other._max == other._min) {
  IntRange!int test2_r1 = IntRange!int(0, 32);
  IntRange!int test2_r2 = IntRange!int(true);

  assert((test2_r1 & test2_r2) == 1);
  assert(test2_r1 == irange(0, 32));
  writeln("AND Test 2 Passed");


  // else if (this._min < this._max && other._min < other._max) {
  irange test3_r1 = irange(0, 32);
  irange test3_r2 = irange(32, 64);

  assert((test3_r1 & test3_r2) == 0);
  writeln("AND Test 3a Passed");

  test3_r1 = irange(0, 32);
  test3_r2 = irange(33, 64);

  assert((test3_r1 & test3_r2) == 0);
  writeln("AND Test 3b Passed");

  test3_r1 = irange(33, 64);
  test3_r2 = irange(0, 32);

  assert((test3_r1 & test3_r2) == 0);
  writeln("AND Test 3c Passed");

  test3_r1 = irange(-5, 16);
  test3_r2 = irange(14, 38);

  assert((test3_r1 & test3_r2) == 1);
  assert (test3_r1 == irange(14, 16));
  writeln("AND Test 3d Passed");

  // else if (other._min > other._max && this._min < this._max) {

  irange test4_r1 = irange(32, 64);
  irange test4_r2 = irange(64, 32);

  assert((test4_r1 & test4_r2) == 0);
  writeln("AND Test 4a Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(60, 0);

  assert((test4_r1 & test4_r2) == 1);
  assert(test4_r1 == irange(60, 64));
  writeln("AND Test 4b Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(96, 0);

  assert((test4_r1 & test4_r2) == 0);
  writeln("AND Test 4c Passed");
  // 	      else if (this._min > this._max && other._min < other._max) {

  irange test5_r1 = irange(60, 0);
  irange test5_r2 = irange(16, 64);

  assert((test5_r1 & test5_r2) == 1);
  assert(test5_r1 == irange(60, 64));
  writeln("AND Test 5a Passed");

  test5_r1 = irange(60, 0);
  test5_r2 = irange(-16, 32);
  assert((test5_r1 & test5_r2) == 1);
  assert(test5_r1 == irange(-16, 0));
  writeln("AND Test 5b Passed");
  
  // [33, 64) ,[64, 33)
  test5_r1 = irange(33, 64);
  test5_r2 = irange(64, 33);
  assert((test5_r1 & test5_r2) == 0);
  writeln("AND Test 5c Passed");
  

  // else if (this._min > this._max && other._min > other._max) {
  irange test6_r1 = irange(64, -64);
  irange test6_r2 = irange(32, -32);
  assert((test6_r1 & test6_r2) == 1);
  assert(test6_r1 == irange(64, -64));
  writeln("AND Test 6a Passed");
		
  test6_r1 = irange(64, -32);
  test6_r2 = irange(32, -64);
  assert((test6_r1 & test6_r2) == 1);
  assert(test6_r1 == irange(64, -64));
  writeln("AND Test 6b Passed");
		
  // Double overlap
  irange test7_r1 = irange(32, -32);
  irange test7_r2 = irange(-64, 64);
  assert((test7_r1 & test7_r2) == 2);
  assert(test7_r1 == irange(-64, -32));
  assert(test7_r2 == irange(32, 64));
  writeln("AND Test 7 Passed");
}


struct IntRangeSet(T)
{
  import std.random: uniform, rndGen, Random;
  Array!(IntRange!T) _ranges;

  Unsigned!T _count;
  
  IntRangeSet!T dup() {
    IntRangeSet!T rns;
    rns._ranges = _ranges.dup();
    rns._count = _count;
    return rns;
  }

  void optimize() {
    import std.algorithm.sorting;
    IntRange!T r = IntRange!T(true);
    Array!(IntRange!T) optRanges;
    auto sortedRanges = sort!((a, b) => a.min < b.min)(_ranges[]);
    bool first = true;
    foreach (ref sr; sortedRanges) {
      if (first) {
      	r = sr;
	first = false;
      	continue;
      }
      if (r | sr) continue;
      else {
      	optRanges ~= r;
      	r = sr;
      }
    }
    optRanges ~= r;
    this._ranges = optRanges;
    if (! this.isFull()) {
      _count = count();
    }
  }

  void opOpAssign(string op)(IntRangeSet!T other) {
    static if (op == "|") {
      _ranges ~= other._ranges;
      optimize();
    }
    static if (op == "&") {
      this.optimize();
      other.optimize();
      Array!(IntRange!T) newRanges;
      foreach (oRange; other._ranges) {
	foreach (tRange; this._ranges) {
	  // rangeAnd is destructive
	  auto or = oRange;
	  auto tr = tRange;
	  int c = (or & tr);
	  if (c >= 1) {
	    newRanges ~= or;
	  }
	  if (c == 2) {
	    newRanges ~= tr;
	  }
	}
      }
      _ranges = newRanges;
      this.optimize();
    }
  }

  void opOpAssign(string op)(IntRange!T other) {
    static if (op == "~") {
      _ranges ~= other;
      this.optimize();
    }
    static if (op == "|") {
      _ranges ~= other;
      optimize();
    }
    static if (op == "&") {
      this.optimize();
      Array!(IntRange!T) newRanges;
      foreach (tRange; this._ranges) {
	auto rc = tRange & other;
	if (rc >= 1) {
	  newRanges ~= tRange;
	}
	if (rc == 2) {
	  newRanges ~= other;
	}
      }
      _ranges = newRanges;
      this.optimize();
    }
  }

  bool isEmpty() {
    return (_ranges.length == 0);
  }

  bool isFull() {
    return (_ranges.length == 1 &&
	    _ranges[0]._full);
  }

  string toString() {
    import std.conv;
    string str = T.stringof ~ ": ";
    return str ~ _ranges[].to!string();
  }

  Unsigned!T count() {
    Unsigned!T cou;
    foreach(r; _ranges) {
      auto c = r.count();
      cou += c;
    }
    _count = cou;
    return cou;
  }

  T uniform(ref Random gen = rndGen()) {
    assert (! isEmpty());

    if (this.isFull()) {
      return uniform!T(gen);
    }
    else {
      Unsigned!T rn;

      if (_count == 0) count();
      assert(_count != 0);

      rn = uniform(0, _count, gen);
      foreach (r; _ranges) {
	auto cou = r.count();
	if (cou > rn) {
	  return cast(T) (r.min + rn);
	}
	else {
	  rn -= cou;
	}
      }
      assert(false, "Random number generated is outside scope");
    }
  }

  T uniform(_esdl__RandGen rgen) {
    assert (! isEmpty());

    if (this.isFull()) {
      return rgen.gen!T;
    }
    else {
      Unsigned!T rn;

      if (_count == 0) count();
      assert(_count != 0);

      rn = rgen.gen(0, _count);
      foreach (r; _ranges) {
	auto cou = r.count();
	if (cou > rn) {
	  return cast(T) (r.min + rn);
	}
	else {
	  rn -= cou;
	}
      }
      assert(false, "Random number generated is outside scope");
    }
  }
}

template IntRangeType(V)
{
  static if (isIntegral!V)
    {
      enum N = V.sizeof * 8;
      enum S = isSigned!V;
    }
  else static if (isBitVector!V)
    {
      enum N = V.SIZE;
      enum S = V.ISSIGNED;
    }
  else static if (isBoolean!V)
    {
      enum N = 1;
      enum S = false;
    }

  static if (N >= 32) {
    static if (S) alias IntRangeType = long;
    else alias IntRangeType = ulong;
  }
  else // static if (N > 16)
    {
      static if (S) alias IntRangeType = int;
      else alias IntRangeType = uint;
    }
  // else static if (N > 8) {
  //   static if (S) alias IntRangeType = short;
  //   else alias IntRangeType = ushort;
  // }
  // else {
  //   static if (S) alias IntRangeType = byte;
  //   else alias IntRangeType = ubyte;
  // }
}

enum IntRangeModOp: byte {ADD, SUB, SUBD, MULT, DIV, DIVD}

struct IntRangeMod(T)
{
  this(IntRangeModOp op, T arg) {
    _op = op;
    _arg = arg;
  }

  T             _arg;
  IntRangeModOp _op;

  bool          _signedArg;
  ubyte         _bitsArg;

  bool          _signed;
  ubyte         _bits;

  
  
  void apply(ref IntRange!T ir) {
    switch(_op) {
    case IntRangeModOp.ADD:
      ir._min -= _arg;
      ir._max -= _arg;
      break;
    case IntRangeModOp.SUB:
      ir._min += _arg;
      ir._max += _arg;
      break;
    case IntRangeModOp.SUBD:
      T tmp = ir._min;
      ir._min = cast(T) (_arg - ir._max + 1);
      ir._max = cast(T) (_arg - tmp + 1);
      break;
    default: assert(false);
    }
  }
}

struct UniRangeMod
{
  this(IntRangeModOp op, long arg) {
    _op = op;
    _arg = arg;
  }

  long          _arg;
  IntRangeModOp _op;

  void apply(ref UniRange ur) {
    final switch (ur._type) {
    case INTTYPE.UINT:
      uint iArg = cast(uint) _arg;
      assert (iArg == _arg);
      UIntR ir = cast(UIntR) ur;
      IntRangeMod!(uint) iMod = IntRangeMod!(uint)(_op, iArg);
      iMod.apply(ir);
      ur = UniRange(ir);
      break;
    case INTTYPE.INT:
      int iArg = cast(int) _arg;
      assert (iArg == _arg);
      IntR ir = cast(IntR) ur;
      IntRangeMod!(int) iMod = IntRangeMod!(int)(_op, iArg);
      iMod.apply(ir);
      ur = UniRange(ir);
      break;
    case INTTYPE.ULONG:
      ulong iArg = cast(ulong) _arg;
      assert (iArg == _arg);
      ULongR ir = cast(ULongR) ur;
      IntRangeMod!(ulong) iMod = IntRangeMod!(ulong)(_op, iArg);
      iMod.apply(ir);
      ur = UniRange(ir);
      break;
    case INTTYPE.LONG:
      long iArg = cast(long) _arg;
      assert (iArg == _arg);
      LongR ir = cast(LongR) ur;
      IntRangeMod!(long) iMod = IntRangeMod!(long)(_op, iArg);
      iMod.apply(ir);
      ur = UniRange(ir);
      break;
    }
  }
}
