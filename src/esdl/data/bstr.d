// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2019
//            Copyright Digital Mars 2007 - 2011.
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   $(WEB digitalmars.com, Walter Bright),
// 	   $(WEB erdani.org, Andrei Alexandrescu),
// 	   Jonathan M Davis,
// 	   Alex Rønne Petersen,
// 	   Damian Ziemba
// 	   Puneet Goel <puneet@coverify.com>

module esdl.data.bstr;

import std.conv;
import std.string;
import std.traits;
import std.format;
import std.bitmanip;
import core.bitop;
import esdl.data.bvec;

alias BitString!true  lstr;
alias BitString!false bstr;

// required by toCharString
private ubyte _log2(size_t n) {
  if(n == 1) return 0;
  else return cast(ubyte)(1 + _log2(n/2));
}

template isBitString(T) {
  static if(is(T unused == BitString!(L), bool L))
    enum bool isBitString = true;
  else
  enum bool isBitString = false;
}

struct BitString(bool L)
{

  size_t len;

  alias len opDollar;

  size_t* aptr;
  static if(L)
    {
      size_t* bptr;
    }

  enum bitsPerSizeT = size_t.sizeof * 8;

  /**********************************************
   * Gets the amount of native words backing this $(D BitArray).
   */
  @property const size_t dim() {
    return (len + (bitsPerSizeT-1)) / bitsPerSizeT;
  }

  /**********************************************
   * Gets the amount of bits in the $(D BitArray).
   */
  @property const size_t length() {
    return len;
  }

  /**********************************************
   * Sets the amount of bits in the $(D BitArray).
   */
  @property size_t length(size_t newlen) {
    if (newlen != len) {
      size_t olddim = dim;
      size_t newdim = (newlen + (bitsPerSizeT-1)) / bitsPerSizeT;

      if (newdim != olddim) {
        // Create a fake array so we can use D's realloc machinery
        auto a = aptr[0 .. olddim];
        a.length = newdim;                // realloc
        aptr = a.ptr;
        static if(L) {
          auto b = bptr[0 .. olddim];
          b.length = newdim;                // realloc
          bptr = b.ptr;
        }
        if (newlen & (bitsPerSizeT-1)) {   // Set any pad bits to 0
          aptr[newdim - 1] &= ~(~0L << (newlen & (bitsPerSizeT-1)));
          static if(L) {
            bptr[newdim - 1] &= ~(~0L << (newlen & (bitsPerSizeT-1)));
          }
        }
      }
      len = newlen;
    }
    return len;
  }

  /**********************************************
   * Gets the $(D i)'th bit in the $(D BitArray).
   */
  auto opIndex(size_t i) const
  in {
    assert(i < len);
  }
  body {
    static if(L) {
      if(bt(bptr, i)) {
        if(bt(aptr, i)) return LOGIC_X;
        else            return LOGIC_Z;
      }
      else {
        if(bt(aptr, i)) return LOGIC_1;
        else            return LOGIC_0;
      }
    }
    else {
      if(bt(aptr, i)) return BIT_1;
      else            return BIT_0;
    }
  }

  unittest
  {
    void Fun(const lstr arr)
    {
      auto x = arr[0];
      assert(x == LOGIC_X);
    }
    LogicArray a;
    a.length = 3;
    a[0] = LOGIC_X;
    Fun(a);
  }

  /**********************************************
   * Sets the $(D i)'th bit in the $(D BitArray).
   */
  bool opIndexAssign()(bool b, size_t i)
    in {
      assert(i < len);
    }
  body {
    static if(L) btr(bptr, i);
    if (b)       bts(aptr, i);
    else         btr(aptr, i);
    return b;
  }

  auto opIndexAssign(T)(T b, size_t i)
  if(isBitVector!T && T.SIZE == 1 && (L || (! T.IS4STATE)))
    in {
      assert(i < len);
    }
  body {
    static if(L) {
      if (b.getValueVec) bts(bptr, i);
      else        btr(bptr, i);
    }
    if (b.getMetaVec)   bts(aptr, i);
    else          btr(aptr, i);
    return b;
  }

  /**********************************************
   * Duplicates the $(D BitArray) and its contents.
   */
  @property BitString!L dup() const {
    BitString!L ba;
    auto a = aptr[0 .. dim].dup;
    ba.aptr = a.ptr;
    static if(L) {
      auto b = bptr[0 .. dim].dup;
      ba.bptr = b.ptr;
    }
    ba.len = len;
    return ba;
  }

  unittest
  {
    bstr a;
    bstr b;
    int i;

    debug(bitstream) printf("BitArray.dup.unittest\n");

    a.length = 3;
    a[0] = true; a[1] = false; a[2] = true;
    b = a.dup;
    assert(b.length is 3);
    for (i = 0; i < 3; i++)
      {   debug(bitarray) printf("b[%d] = %d\n", i, b[i]);
        assert(b[i] == (((i ^ 1) & 1) ? true : false));
      }
  }

  // Will include later -- not required for mow.
  /**********************************************
   * Support for $(D foreach) loops for $(D BitArray).
   */
  int opApply(T)(scope int delegate(ref T) dg)
  {
    int result;

    for (size_t i = 0; i < len; i++)
      {
	auto b = opIndex(i);
	result = dg(b);
	this[i] = b;
	if (result)
	  break;
      }
    return result;
  }

  /** ditto */
  int opApply(T)(scope int delegate(T) dg) const
  {
    int result;

    for (size_t i = 0; i < len; i++)
      {
	auto b = opIndex(i);
	result = dg(b);
	if (result)
	  break;
      }
    return result;
  }

  /** ditto */
  int opApply(T)(scope int delegate(ref size_t, ref T) dg)
  {
    int result;

    for (size_t i = 0; i < len; i++)
      {
	auto b = opIndex(i);
	result = dg(i, b);
	this[i] = b;
	if (result)
	  break;
      }
    return result;
  }

  /** ditto */
  int opApply(T)(scope int delegate(size_t, T) dg) const
  {
    int result;

    for (size_t i = 0; i < len; i++)
      {
	auto b = opIndex(i);
	result = dg(i, b);
	if (result)
	  break;
      }
    return result;
  }
  unittest
  {
    debug(bitstring) printf("BitString.opApply unittest\n");

    static bool[] ba = [1,0,1];

    BitArray a; a.init(ba);

    int i;
    foreach (b;a)
      {
     switch (i)
       {
       case 0: assert(b is true); break;
       case 1: assert(b is false); break;
       case 2: assert(b is true); break;
       default: assert(0);
       }
     i++;
      }

    foreach (j,b;a)
      {
     switch (j)
       {
       case 0: assert(b is true); break;
       case 1: assert(b is false); break;
       case 2: assert(b is true); break;
       default: assert(0);
       }
      }
  }


  /**********************************************
   * Reverses the bits of the $(D BitArray).
   */
  @property BitString!L reverse()
  out (result) {
    assert(result == this);
  }
  body {
    if (len >= 2) {
      size_t lo, hi;
      lo = 0;
      hi = len - 1;
      for (; lo < hi; ++lo, --hi) {
        auto t = this[lo];
        this[lo] = this[hi];
        this[hi] = t;
      }
    }
    return this;
  }

  unittest
  {
    debug(bitstring) printf("BitString.reverse.unittest\n");

    BitString b;
    static bool[5] data = [1,0,1,1,0];
    int i;

    b.init(data);
    b.reverse;
    for (i = 0; i < data.length; i++)
      {
        assert(b[i] == data[4 - i]);
      }
  }



  /***************************************
   * Support for operator ~= for $(D BitArray).
   */

  auto opCatAssign(bool BIGENDIAN=false, T)(T t, size_t count = 0)
    if(is(T == bool) || isIntegral!T ||
       (isBitVector!T && (L || (! T.IS4STATE)))) {
      static if(is(T == bool)) {
	alias UBit!(1) V;
	V v = t;
      }
      else static if(isIntegral!T) {
	alias V = UBit!(T.sizeof*8);
	V v = t;
      }
      else {
        alias T V;
        alias t v;
      }
      size_t bits;
      if(count == 0) {
	bits = V.SIZE;
      }
      else {
	assert(count <= V.SIZE);
	bits = count;
      }
      length = len + bits;
      static if(BIGENDIAN) {
	for (size_t i=0; i != bits; ++i) {
	  this[$-bits+i] = v[$-i-1];
	}
      }
      else {
	for (size_t i=0; i != bits; ++i) {
	  this[$-bits+i] = v[i];
	}
      }
      return this;
    }

  void pushBack(T)(T t, bool bigEndian=false, size_t count = 0)
    if(is(T == bool) || isIntegral!T ||
       (isBitVector!T && (L || (! T.IS4STATE)))) {
      if(bigEndian) {
        this.opCatAssign!true(t, count);
      }
      else {
        this.opCatAssign(t, count);
      }
    }

  void getFront(T)(out T t, size_t index, bool bigEndian=false, size_t count = 0)
    if(((! L) && (is(T == bool) || isIntegral!T)) ||
       (isBitVector!T && (T.IS4STATE || (! L)))) {
      static if(is(T == bool))     alias UBit!(1) V;
      else static if(isIntegral!T) alias UBit!(T.sizeof*8) V;
        else                       alias T V;
      size_t bits;
      if(count == 0) {
	bits = V.SIZE;
      }
      else {
	assert(count <= V.SIZE);
	bits = count;
      }
      assert(len-index >= bits);
      V v;
      if(bigEndian) {
        for (size_t i=0; i != bits; ++i) {
          v[$-i-1] = this[index+i];
        }
      }
      else {
        for (size_t i=0; i != bits; ++i) {
          v[i] = this[index+i];
        }
      }
      t = cast(T) v;
    }

  void getBack(T)(out T t, size_t index, bool bigEndian=false)
    if(((! L) && (is(T == bool) || isIntegral!T)) ||
       (isBitVector!T && (T.IS4STATE || (! L)))) {
      static if(is(T == bool))     alias UBit!(1) V;
      else static if(isIntegral!T) alias UBit!(T.sizeof*8) V;
        else                       alias T V;
      getFront(t, index-V.SIZE, bigEndian);
    }

  void popBack(T)(out T t, bool bigEndian=false)
    if(((! L) && (is(T == bool) || isIntegral!T)) ||
       (isBitVector!T && (T.IS4STATE || (! L)))) {
      static if(is(T == bool))     alias UBit!(1) V;
      else static if(isIntegral!T) alias UBit!(T.sizeof*8) V;
        else                       alias T V;
      getBack(t, len, bigEndian);
      length = len - V.SIZE;
    }

  unittest
  {
    debug(bitarray) printf("BitArray.opCatAssign unittest\n");

    static bool[] ba = [1,0,1,0,1];

    BitArray a; a.init(ba);
    BitArray b;

    b = (a ~= true);
    assert(a[0] is 1);
    assert(a[1] is 0);
    assert(a[2] is 1);
    assert(a[3] is 0);
    assert(a[4] is 1);
    assert(a[5] is 1);

    assert(b is a);
  }

  // /***************************************
  //  * ditto
  //  */

  auto opCatAssign(T)(T b)
  if(is(T unused == BitString!_L, bool _L)
     && (L || (! _L))) {
    auto istart = len;
    length = len + b.length;
    for (auto i = istart; i < len; i++) {
      this[i] = b[i - istart];
    }
    return this;
  }

  unittest
  {
    debug(bitarray) printf("BitArray.opCatAssign unittest\n");

    static bool[] ba = [1,0];
    static bool[] bb = [0,1,0];

    BitArray a; a.init(ba);
    BitArray b; b.init(bb);
    BitArray c;

    c = (a ~= b);
    assert(a.length is 5);
    assert(a[0] is 1);
    assert(a[1] is 0);
    assert(a[2] is 0);
    assert(a[3] is 1);
    assert(a[4] is 0);

    assert(c is a);
  }

  // /***************************************
  //  * Support for binary operator ~ for $(D BitArray).
  //  */

  auto opCat(T)(T t) const
  if(is(T == bool) || isIntegral!T ||
     (isBitVector!T && (L || (! T.IS4STATE)))) {
    BitString!L r = this.dup;
    r ~= t;
  }

  /** ditto */
  auto opCat_r(T)(T t) const
  if(is(T == bool) || isIntegral!T ||
     (isBitVector!T && (L || (! T.IS4STATE)))) {
    static if(is(T == bool)) {
      alias UBit!(1) V;
      V v = t;
    }
    else static if(isIntegral!T) {
        alias UBit!(T.sizeof*8) V;
        V v = t;
      }
      else {
        alias T V;
        alias t v;
      }
    BitString!L r;

    r.length = len + V.SIZE;
    for (size_t i=0; i!=V.SIZE; ++i) {
      r[i] = v[i];
    }
    for (size_t i = 0; i < len; i++) {
      r[V.SIZE + i] = this[i];
    }
    return r;
  }

  // /** ditto */
  auto opCat(T)(T v) const
  if(is(T unused == BitString!_L, bool _L) && (L || (! _L))) {
    auto r = this.dup;
    r ~= v;
    return r;
  }

  unittest
  {
    debug(bitarray) printf("BitArray.opCat unittest\n");

    static bool[] ba = [1,0];
    static bool[] bb = [0,1,0];

    BitArray a; a.init(ba);
    BitArray b; b.init(bb);
    BitArray c;

    c = (a ~ b);
    assert(c.length is 5);
    assert(c[0] is 1);
    assert(c[1] is 0);
    assert(c[2] is 0);
    assert(c[3] is 1);
    assert(c[4] is 0);

    c = (a ~ true);
    assert(c.length is 3);
    assert(c[0] is 1);
    assert(c[1] is 0);
    assert(c[2] is 1);

    c = (false ~ a);
    assert(c.length is 3);
    assert(c[0] is 0);
    assert(c[1] is 1);
    assert(c[2] is 0);
  }

  T to(T, size_t RADIX = 2)() if((is(T == string) ||
                                  is(T == char[]))
                                 &&(RADIX == 2 ||
                                    RADIX == 8 ||
                                    RADIX == 16)) {
    static if(RADIX == 8) {
      return logicToOctal(this.to!(T, 2));
    }
    else {
      return toCharString!(T, RADIX);
    }
  }

  string toString() {
    return this.to!(string, 2);
  }

  void toString(void delegate(scope const(char)[]) pure nothrow @safe sink, const(FormatSpec!char) f) {
    char[] buff;
    switch(f.spec) {
    case 'd'     : buff = this.toDecimalString(); break;
    case 's'     :              // should print as hex when %s
    case 'h'     :              // should print as hex for %h too
    case 'x'     : buff = "0x" ~ toLower(this.to!(char[], 16)); break;
    case 'H'     :              // should print as HEX for %H
    case 'X'     : buff = "0x" ~ this.to!(char[], 16); break;
    case 'o'     : buff = this.to!(char[], 8); break;
    case 'b'     : buff = "0b" ~ this.to!(char[], 2); break;
    default      :
      throw new FormatException("Format specifier not understood: %" ~ f.spec);
    }

    assert(buff.length > 0);

    sink(buff);
  }

  private T toCharString(T, size_t RADIX)() {
    char[] str;
    if(dim > 1) {
      for(size_t i = 0; i != dim-1; ++i) {
        import std.string;
        static if(RADIX == 2)  string fmtstr = "%b";
        static if(RADIX == 8)  string fmtstr = "%o";
        static if(RADIX == 16) string fmtstr = "%X";
        char[] wstr;
        string astr =
          rightJustify(format(fmtstr, aptr[i]),
                       cast(int)((_log2(RADIX) - 1) +
                                 8*size_t.sizeof)/_log2(RADIX), '0');
        static if(L) {
          string zstr =
            rightJustify(format(fmtstr, bptr[i]),
                         cast(int)((_log2(RADIX) - 1) +
                                   8*size_t.sizeof)/_log2(RADIX), '0');
          string xstr =
            rightJustify(format(fmtstr,(cast(size_t)
                                        (aptr[i] & bptr[i]))),
                         cast(int)((_log2(RADIX) - 1) +
                                   8*size_t.sizeof)/_log2(RADIX), '0');
        }
        foreach(j, c; astr) {
          char s = c;
          static if(L) {
            if(zstr[j] != '0') {
              s = 'Z';
              if(xstr[j] != '0') s = 'X';
            }
          }
          wstr ~= s;
        }
        str = wstr ~ str;
      }
    }

    char[] wstr;
    size_t umask = 1;
    umask <<= (len % (size_t.sizeof * 8));
    umask -= 1;
    if(umask is 0) umask = size_t.max;
    auto foo = cast(size_t)(aptr[len-1] & umask);
    static if(RADIX == 16) string fmtstr = "%X";
    static if(RADIX == 8)  string fmtstr = "%o";
    static if(RADIX == 2)  string fmtstr = "%b";

    import std.string;
    string astr =
      rightJustify(format(fmtstr, aptr[dim-1] & umask),
                   cast(int)((_log2(RADIX) - 1) +
                             ((len-1)%(8*size_t.sizeof) + 1))
                   /_log2(RADIX), '0');
    static if(L) {
      string zstr =
        rightJustify(format(fmtstr, bptr[dim-1] & umask),
                     cast(int)((_log2(RADIX) - 1) +
                               ((len-1)%(8*size_t.sizeof) + 1))
                     /_log2(RADIX), '0');
      string xstr =
        rightJustify(format(fmtstr, aptr[dim-1] & bptr[dim-1] & umask),
                     cast(int)((_log2(RADIX) - 1) +
                               ((len-1)%(8*size_t.sizeof) + 1))
                     /_log2(RADIX), '0');
    }

    foreach(i, c; astr) {
      char s = c;
      static if(L) {
        if(zstr[i] != '0') {
          s = 'Z';
          if(xstr[i] != '0') s = 'X';
        }
      }
      wstr ~= s;
    }
    str = wstr ~ str;
    return cast(T) str;
  }

  char [] toDecimalString() const {
    if(dim is 1) {
      auto val = this.aptr[0];
      string str = format("%d", val);
      char[] buff;
      foreach(c; str) buff ~= c;
      return buff;
    }
    else {
      uint[] data =(cast(uint[]) this.toArrA).dup;
      auto predictlength = 20+20*(data.length/2); // just over 19
      char [] buff = new char[predictlength];
      size_t sofar = biguintToDecimal(buff, data.dup);
      return buff[sofar..$];
    }
  }

  private size_t[] toArrA() const {
    size_t[] arr;
    arr.length = dim;
    for(size_t i=0; i != dim; ++i) {
      arr[i] = aptr[i];
    }
    return arr;
  }

  static if(L) {
    private size_t[] toArrB() const {
      size_t[] arr;
      arr.length = dim;
      for(size_t i=0; i != dim; ++i) {
        arr[i] = bptr[i];
      }
      return arr;
    }
  }

  public void clear() {
    this.length = 0;
  }

  public bool isEmpty() {
    if(len is 0) return true;
    else return false;
  }

  public void fromArray(bool BIGENDIAN=false, T)(T[] arr)
    if((! L) && (isIntegral!T || is(T == bool) || is(T == Bit!1) ||
		 isSomeChar!T)) {
      assert(isEmpty());
      // special case, no array element is going to spread across bstr elements boundry
      foreach(a; arr) {
        auto shft = len & (bitsPerSizeT-1);
        static if(is(T == bool)) length = len + 1;
        else length = len + T.sizeof*8;
        static if(BIGENDIAN) {
	  size_t v = (cast(size_t) (a.reverse)) << shft;
	}
        else {
	  size_t v = (cast(size_t) a) << shft;
	}
        aptr[dim-1] |= v;
      }
      // mask out unused portion of the MSW
      auto shft = (arr.length * BitLength!T) & (bitsPerSizeT - 1);
      if(shft != 0) {
	aptr[dim-1] &= ~(~0L << shft);
      }
    }

  public void fromStr(bool BIGENDIAN=false)(string str) if((! L)) {
    fromArray!BIGENDIAN(str);
  }

  public void toArray(bool BIGENDIAN=false, T)(out T[] arr)
    if((! L) && (isIntegral!T || is(T == bool) || is(T == Bit!1) ||
		 isSomeChar!T)) {
      for (size_t i=0; i*BitLength!T < len; ++i) {
        auto v = aptr[(i*BitLength!T)/bitsPerSizeT];
        static if(BIGENDIAN) arr ~= (cast(T) (v >> ((i*BitLength!T) & (bitsPerSizeT-1)))).reverse;
        else {
	  // FIXME
	  static if(is(T == Bit!1)) {
	    if((v >> ((i*BitLength!T) & (bitsPerSizeT-1))) % 2) {
	      arr ~= cast(T) false;
	    }
	    else {
	      arr ~= cast(T) true;
	    }
	    // arr ~= cast(T) (v >> ((i*BitLength!T) & (bitsPerSizeT-1)));
	  }
	}
      }
    }

  // public void toStr(bool BIGENDIAN=false, T)(out string str) if((! L)) {
  //   char[] cstr;

  // }
}


ulong reverse(ulong x) {
  x = (((x & 0xaaaaaaaaaaaaaaaa) >> 1)  | ((x & 0x5555555555555555) << 1));
  x = (((x & 0xcccccccccccccccc) >> 2)  | ((x & 0x3333333333333333) << 2));
  x = (((x & 0xf0f0f0f0f0f0f0f0) >> 4)  | ((x & 0x0f0f0f0f0f0f0f0f) << 4));
  x = (((x & 0xff00ff00ff00ff00) >> 8)  | ((x & 0x00ff00ff00ff00ff) << 8));
  x = (((x & 0xffff0000ffff0000) >> 16) | ((x & 0x0000ffff0000ffff) << 16));
  return((x >> 32) | (x << 32));
}

uint reverse(uint x) {
  x = (((x & 0xaaaaaaaa) >> 1) | ((x & 0x55555555) << 1));
  x = (((x & 0xcccccccc) >> 2) | ((x & 0x33333333) << 2));
  x = (((x & 0xf0f0f0f0) >> 4) | ((x & 0x0f0f0f0f) << 4));
  x = (((x & 0xff00ff00) >> 8) | ((x & 0x00ff00ff) << 8));
  return((x >> 16) | (x << 16));
}

ushort reverse(ushort x) {
  x = cast(ushort)(((x & 0xaaaa) >> 1) | ((x & 0x5555) << 1));
  x = cast(ushort)(((x & 0xcccc) >> 2) | ((x & 0x3333) << 2));
  x = cast(ushort)(((x & 0xf0f0) >> 4) | ((x & 0x0f0f) << 4));
  return cast(ushort)((x >> 8) | (x << 8));
}

ubyte reverse(ubyte x) {
  x = cast(ubyte) (((x & 0xaa) >> 1) | ((x & 0x55) << 1));
  x = cast(ubyte) (((x & 0xcc) >> 2) | ((x & 0x33) << 2));
  return cast(ubyte)((x >> 4) | (x << 4));
}
