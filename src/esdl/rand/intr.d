module esdl.rand.intr;

import std.traits: isIntegral, isSigned;
import std.container.array;
import std.traits: Unsigned;
import esdl.data.bvec;
import esdl.rand.misc: CstBinVecOp, CstBinBddOp, CstBddOp;

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

struct IntRange(T) if (isIntegral!T) {
  T _min = T.min;
  T _max = T.min;

  T min() {
    return _min;
  }
  
  T max() {
    return _max;
  }
  
  Unsigned!T _count;

  this(T min, T max) {
    _min = min;
    _max = max;
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

  bool opOpAssign(string op)(IntRange other) {
    static if (op == "|") {
      bool result = false;
      if (this._max == this._min) {
	result = true;
      }
      else if (other._max == other._min) {
	this._min = other._min;
	this._max = other._max;
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
    static if (op == "&") {
      if (this._max <= this._min)
      if (this._max == T.min) {
	if (other._max == T.min || other._max > this._min) {
	  this._min = larger(this._min, other._min);
	  this._max = other._max;
	  return true;
	}
	else return false;
      }
      if (other._max == T.min) {
	if (this._max == T.min || this._max > other._min) {
	  this._min = larger(this._min, other._min);
	  return true;
	}
	else return false;
      }
      if (other._min >= this._max || this._min >= other._max) {
	return false;
      }
      else {
	this._min = larger(this._min, other._min);
	this._max = smaller(this._max, other._max);
	return true;
      }
    }    
  }

  string toString() {
    import std.string;
    if (this._max == T.min) {
      return format("[%s, ..)", this._min);
    }
    else {
      return format("[%s, %s)", this._min, this._max);
    }
  }

  Unsigned!T count() {
    if (this._min == this._max) {
      assert(false, "Too big to count");
    }
    else {
      return cast(Unsigned!T) (_max - this._min);
    }
  }

  Unsigned!T unsafeCount() {
    return cast(Unsigned!T) (_max - this._min);
  }
}

unittest {
  import std.stdio;
  import esdl.data.bvec;

  alias irange = IntRange!int;
  
  // if (this._max == this._min) {
  IntRange!int test1_r1 = IntRange!int(32, 32);
  IntRange!int test1_r2 = IntRange!int(0, 32);

  test1_r1 |= test1_r2;

  assert (test1_r1 == IntRange!int(32, 32));
  writeln("Test 1 Passed");

  // else if (other._max == other._min) {
  IntRange!int test2_r1 = IntRange!int(0, 32);
  IntRange!int test2_r2 = IntRange!int(32, 32);

  test2_r1 |= test2_r2;

  assert (test2_r1 == IntRange!int(32, 32));
  writeln("Test 2 Passed");


  // else if (this._min < this._max && other._min < other._max) {
  irange test3_r1 = irange(0, 32);
  irange test3_r2 = irange(32, 64);

  assert(test3_r1 |= test3_r2);
  assert (test3_r1 == irange(0, 64));
  writeln("Test 3a Passed");

  test3_r1 = irange(0, 32);
  test3_r2 = irange(33, 64);

  if (! (test3_r1 |= test3_r2)) {
    writeln("Test 3b Passed");
  }

  test3_r1 = irange(33, 64);
  test3_r2 = irange(0, 32);

  if (! (test3_r1 |= test3_r2)) {
    writeln("Test 3c Passed");
  }

  test3_r1 = irange(-5, 16);
  test3_r2 = irange(14, 38);

  assert(test3_r1 |= test3_r2);
  assert (test3_r1 == irange(-5, 38));
  writeln("Test 3d Passed");

  // else if (other._min > other._max && this._min < this._max) {

  irange test4_r1 = irange(32, 64);
  irange test4_r2 = irange(64, 32);

  assert(test4_r1 |= test4_r2);
  assert(test4_r1 == irange.init);
  writeln("Test 4a Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(60, 0);

  assert(test4_r1 |= test4_r2);
  assert(test4_r1 == irange(32,0));
  writeln("Test 4b Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(96, 0);

  assert(! (test4_r1 |= test4_r2));
  writeln("Test 4c Passed");
  // 	      else if (this._min > this._max && other._min < other._max) {

  irange test5_r1 = irange(60, 0);
  irange test5_r2 = irange(16, 64);
  assert(test5_r1 |= test5_r2);
  assert(test5_r1 == irange(16, 0));
  writeln("Test 5a Passed");

  test5_r1 = irange(60, 0);
  test5_r2 = irange(-16, 32);
  assert(test5_r1 |= test5_r2);
  assert(test5_r1 == irange(60, 32));
  writeln("Test 5b Passed");
  
  // [33, 64) ,[64, 33)
  test5_r1 = irange(33, 64);
  test5_r2 = irange(64, 33);
  assert(test5_r1 |= test5_r2);
  assert(test5_r1 == irange.init);
  writeln("Test 5c Passed");
  

  // else if (this._min > this._max && other._min > other._max) {
  irange test6_r1 = irange(64, -64);
  irange test6_r2 = irange(32, -32);
  assert(test6_r1 |= test6_r2);
  assert(test6_r1 == irange(32, -32));
  writeln("Test 6a Passed");
		
  test6_r1 = irange(64, -32);
  test6_r2 = irange(32, -64);
  assert(test6_r1 |= test6_r2);
  assert(test6_r1 == irange(32, -32));
  writeln("Test 6b Passed");
		

}

unittest {
  import std.stdio;
  import esdl.data.bvec;

  alias irange = IntRange!int;
  
  // if (this._max == this._min) {
  IntRange!int test1_r1 = IntRange!int(32, 32);
  IntRange!int test1_r2 = IntRange!int(0, 32);

  assert(rangeAnd(test1_r1, test1_r2) == 1);
  assert(test1_r1 == irange(0, 32));
  writeln("AND Test 1 Passed");

  // else if (other._max == other._min) {
  IntRange!int test2_r1 = IntRange!int(0, 32);
  IntRange!int test2_r2 = IntRange!int(32, 32);

  assert(rangeAnd(test2_r1, test2_r2) == 1);
  assert(test2_r1 == irange(0, 32));
  writeln("AND Test 2 Passed");


  // else if (this._min < this._max && other._min < other._max) {
  irange test3_r1 = irange(0, 32);
  irange test3_r2 = irange(32, 64);

  assert(rangeAnd(test3_r1, test3_r2) == 0);
  writeln("AND Test 3a Passed");

  test3_r1 = irange(0, 32);
  test3_r2 = irange(33, 64);

  assert(rangeAnd(test3_r1, test3_r2) == 0);
  writeln("AND Test 3b Passed");

  test3_r1 = irange(33, 64);
  test3_r2 = irange(0, 32);

  assert(rangeAnd(test3_r1, test3_r2) == 0);
  writeln("AND Test 3c Passed");

  test3_r1 = irange(-5, 16);
  test3_r2 = irange(14, 38);

  assert(rangeAnd(test3_r1, test3_r2) == 1);
  assert (test3_r1 == irange(14, 16));
  writeln("AND Test 3d Passed");

  // else if (other._min > other._max && this._min < this._max) {

  irange test4_r1 = irange(32, 64);
  irange test4_r2 = irange(64, 32);

  assert(rangeAnd(test4_r1, test4_r2) == 0);
  writeln("AND Test 4a Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(60, 0);

  assert(rangeAnd(test4_r1, test4_r2) == 1);
  assert(test4_r1 == irange(60, 64));
  writeln("AND Test 4b Passed");

  test4_r1 = irange(32, 64);
  test4_r2 = irange(96, 0);

  assert(rangeAnd(test4_r1, test4_r2) == 0);
  writeln("AND Test 4c Passed");
  // 	      else if (this._min > this._max && other._min < other._max) {

  irange test5_r1 = irange(60, 0);
  irange test5_r2 = irange(16, 64);

  assert(rangeAnd(test5_r1, test5_r2) == 1);
  assert(test5_r1 == irange(60, 64));
  writeln("AND Test 5a Passed");

  test5_r1 = irange(60, 0);
  test5_r2 = irange(-16, 32);
  assert(rangeAnd(test5_r1, test5_r2) == 1);
  assert(test5_r1 == irange(-16, 0));
  writeln("AND Test 5b Passed");
  
  // [33, 64) ,[64, 33)
  test5_r1 = irange(33, 64);
  test5_r2 = irange(64, 33);
  assert(rangeAnd(test5_r1, test5_r2) == 0);
  writeln("AND Test 5c Passed");
  

  // else if (this._min > this._max && other._min > other._max) {
  irange test6_r1 = irange(64, -64);
  irange test6_r2 = irange(32, -32);
  assert(rangeAnd(test6_r1, test6_r2) == 1);
  assert(test6_r1 == irange(64, -64));
  writeln("AND Test 6a Passed");
		
  test6_r1 = irange(64, -32);
  test6_r2 = irange(32, -64);
  assert(rangeAnd(test6_r1, test6_r2) == 1);
  assert(test6_r1 == irange(64, -64));
  writeln("AND Test 6b Passed");
		
  // Double overlap
  irange test7_r1 = irange(32, -32);
  irange test7_r2 = irange(-64, 64);
  assert(rangeAnd(test7_r1, test7_r2) == 2);
  assert(test7_r1 == irange(-64, -32));
  assert(test7_r2 == irange(32, 64));
  writeln("AND Test 7 Passed");
}

int rangeAnd(T)(ref IntRange!T r1, ref IntRange!T r2) {
  int rcount;
  if (r1._min == r1._max) {
    r1 = r2;
    rcount = 1;
  }
  if (r2._min == r2._max) {
    rcount = 1;
  }
  // both ranges normal
  if (r1._min < r1._max && r2._min < r2._max) {
    if (r1._max <= r2._min || r2._max <= r1._min) {
      rcount = 0;
    }
    else {
      r1._min = larger(r1._min, r2._min);
      r1._max = smaller(r1._max, r2._max);
      rcount = 1;
    }
  }
  if (r1._min > r1._max && r2._min < r2._max) {
    IntRange!T s1;
    IntRange!T s2;
    int count;
    if (r2._min < r1._max) {
      s1._min = r2._min;
      s1._max = smaller(r2._max, r1._max);
      count += 1;
    }
    if (r2._max > r1._min) {
      if (count == 0) {
	s1._max = r2._max;
	s1._min = larger(r2._min, r1._min);
	count += 1;
      }
      else if (count == 1) {
	s2._max = r2._max;
	s2._min = larger(r2._min, r1._min);
	count += 1;
      }
    }
    if (count == 1) {
      r1 = s1;
    }
    if (count == 2) {
      r1 = s1;
      r2 = s2;
    }
    rcount = count;
  }
  //  [96, 512) ,[256, 32)
  if (r2._min > r2._max && r1._min < r1._max) {
    IntRange!T s1;
    IntRange!T s2;
    int count;
    if (r1._min < r2._max) {
      s1._min = r1._min;
      s1._max = smaller(r1._max, r2._max);
      count += 1;
    }
    if (r1._max > r2._min) {
      if (count == 0) {
	s1._max = r1._max;
	s1._min = larger(r1._min, r2._min);
	count += 1;
      }
      else if (count == 1) {
	s2._max = r1._max;
	s2._min = larger(r1._min, r2._min);
	count += 1;
      }
    }
    if (count == 1) {
      r1 = s1;
    }
    if (count == 2) {
      r1 = s1;
      r2 = s2;
    }
    rcount = count;
  }
  if (r1._min > r1._max && r2._min > r2._max) {
    r1._min = larger(r1._min, r2._min);
    r1._max = smaller(r1._max, r2._max);
    rcount = 1;
  }
  return rcount;
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
    IntRange!T r;
    Array!(IntRange!T) optRanges;
    auto sortedRanges = sort!((a, b) => a.min < b.min)(_ranges[]);
    bool first = true;
    foreach (ref sr; sortedRanges) {
      if (first) {
      	r = sr;
	first = false;
      	continue;
      }
      if (r |= sr) continue;
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
	  int c = rangeAnd(or, tr);
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
	if (tRange &= other) {
	  newRanges ~= tRange;
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
	    _ranges[0] == IntRange!T.init);
  }

  string toString() {
    import std.conv;
    return _ranges[].to!string();
  }

  Unsigned!T count() {
    Unsigned!T cou;
    foreach(r; _ranges) {
      auto c = r.unsafeCount();
      if (c == 0) {
	return 0;
      }
      else {
	cou += c;
      }
    }
    return cou;
  }

  T uniform(ref Random gen = rndGen()) {
    if (this.isFull()) {
      return uniform!T(gen);
    }
    else {
      Unsigned!T rn;
      if (_count == 0) {
	rn = uniform!(Unsigned!T)(gen);
      }
      else {
	rn = uniform(0, _count, gen);
      }

      foreach (r; _ranges) {
	auto cou = r.unsafeCount();
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

  T _arg;
  IntRangeModOp _op;
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
