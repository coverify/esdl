module esdl.rand.misc;

import esdl.data.bvec: isBitVector;
import esdl.data.queue;
import esdl.data.charbuf;
import std.traits: isIntegral, isBoolean, isArray,
  EnumMembers, isSomeChar;
import std.meta: AliasSeq;

interface _esdl__Norand { } 	// classes derived from this interface shall not have a proxy

// Different types attributes for UI
// template _esdl__norand() {}
// enum norand;



// write in Hex form for all the bytes of data
size_t writeHexString(T)(T val, ref Charbuf str) {
  static if (isBitVector!T) {
    enum size_t NIBBLES = 2 * (T.SIZE + 7)/8;
    enum size_t NIBBLESPERWORD = 2 * T.STORE_T.sizeof;
    enum T.STORE_T NIBBLEMASK = 0xF;
    for (size_t i=NIBBLES; i != 0; --i) {
      import std.stdio;
      size_t j = (i-1) / NIBBLESPERWORD;
      size_t k = (i-1) % NIBBLESPERWORD;
      auto C = (val.aVal[j] >> (k * 4)) & NIBBLEMASK;
      if (C < 10) str ~= (cast(char) ('0' + C));
      else str ~= cast(char) ('A' + C - 10);
    }
    return NIBBLES;
  }
  else {
    enum size_t NIBBLES = 2 * T.sizeof;
    enum ubyte NIBBLEMASK = 0xF;
    for (size_t i=NIBBLES; i != 0; --i) {
      auto C = (val >> ((i-1) * 4)) & NIBBLEMASK;
      if (C < 10) str ~= (cast(char) ('0' + C));
      else str ~= cast(char) ('A' + C - 10);
    }
    return NIBBLES;
  }
}

struct rand
{
  bool _noRand;
  bool _noProxy;

  uint[] _counts;

  this(uint[] counts ...) {
    _counts = counts;
  }
  
  this(bool hasProxy) {
    _noProxy = ! hasProxy;
    _noRand  = _noProxy;
  }

  this(bool noRand, bool noProxy) {
    _noRand = noRand;
    _noProxy = noProxy;
  }

  bool hasProxy() {
    return ! _noProxy;
  }

  bool isRand() {
    return ! _noRand;
  }

  uint opIndex(size_t N) {
    if (_counts.length <= N) return uint.max;
    else return _counts[N];
  }
}


// template rand(N...) if (CheckRandParams!N) {
//   enum LENGTH = N.length;
//   // enum _esdl__isRandAttribute = true;
//   enum IDX(size_t I) = N[I];
//   alias RAND = _esdl__rand!(N);
// }


// This is part of the user API, but is intended to be seldom used
// We do not want to create proxy rand objects for evey element of a
// Randomizable class. But there could be scenarios where someone uses
// an array of objects or ints in a loop constraint only for its
// iterator. In such cases, a user will be required to add @norand
// with such arrays. For example:
// class Foo {
//   @norand int[] a;
//   @rand int[] b;
//   Constraint!q{
//     foreach(i, aa; a) {
//       b[i] < aa;
//     }
//   } cst_b;
// }

// struct _esdl__rand(N...) { }

template isVecSigned(L) {
  import std.traits: isIntegral, isSigned;
  static if (is(L: bool))
    enum bool isVecSigned = false;
  else static if (isBitVector!L)
    enum bool isVecSigned = L.ISSIGNED;
  else static if (isIntegral!L)
    enum bool isVecSigned = isSigned!L;
  else static if (isSomeChar!L)
    enum bool isVecSigned = false;
  else
    static assert(false, "isVecSigned: Can not determine sign of type " ~
		  L.stringof);
}

template LeafElementType(T)
{
  import std.range;		// ElementType
  static if (is (T == string)) {
    alias LeafElementType = immutable(char);
  }
  else static if (isArray!T) {
    alias LeafElementType = LeafElementType!(ElementType!T);
  }
  else static if (isQueue!T) {
    alias LeafElementType = LeafElementType!(T.ElementType);
  }
  else {
    alias LeafElementType = T;
  }
}

template ElementTypeN(T, int N=0)
{
  import std.range;		// ElementType
  static if(N==0) {
    alias ElementTypeN = T;
  }
  else {
    alias ElementTypeN = ElementTypeN!(ElementType!T, N-1);
  }
}

template Unconst(T) {
  static if (is(T U ==   immutable U)) alias Unconst = U;
  else static if (is(T U == inout const U)) alias Unconst = U;
  else static if (is(T U == inout       U)) alias Unconst = U;
  else static if (is(T U ==       const U)) alias Unconst = U;
  else                                      alias Unconst = T;
}

template PointersOf(ARGS...) {
  static if (ARGS.length == 0) alias PointersOf = AliasSeq!();
  else alias PointersOf = AliasSeq!(ARGS[0] *, PointersOf!(ARGS[1..$]));
}

template _esdl__ArrOrder(T, int N=0) {
  import std.traits;
  import std.range;
  static if (isArray!T) {
    enum int _esdl__ArrOrder = 1 + _esdl__ArrOrder!(ElementType!T) - N;
  }
  else static if (isQueue!T) {
    enum int _esdl__ArrOrder = 1 + _esdl__ArrOrder!(T.ElementType) - N;
  }
  else {
    static assert (N == 0);
    enum int _esdl__ArrOrder = 0;
  }
}

// template _esdl__ArrOrder(T, int I, int N=0) {
//   enum int _esdl__ArrOrder = _esdl__ArrOrder!(typeof(T.tupleof[I])) - N;
// }

// Make sure that all the parameters are of type size_t
// template CheckRandParamsLoop(N...) {
//   static if(N.length > 0) {
//     static if(!is(typeof(N[0]) == bool) && // do not confuse bool as size_t
// 	      is(typeof(N[0]) : size_t)) {
//       static assert(N[0] != 0, "Can not have arrays with size 0");
//       static assert(N[0] > 0, "Can not have arrays with negative size");
//       enum bool CheckRecurse = CheckRandParamsLoop!(N[1..$]);
//       enum bool CheckRandParamsLoop = CheckRecurse;
//     }
//     else {
//       static assert(false, "Only positive integral values are allowed as array dimensions");
//       enum bool CheckRandParamsLoop = false;
//     }
//   }
//   else {
//     enum bool CheckRandParamsLoop = true;
//   }
// }

// template CheckRandParams(N...) {
//   static if(N.length == 1 && N[0] == false) {
//     enum bool CheckRandParams = true;
//   }
//   else {
//     enum bool CheckRandParams = CheckRandParamsLoop!N;
//   }
// }

// // generates the code for rand structure inside the class object getting
// // randomized
// template _esdl__ListRands(T, int I=0) {
//   // import std.typetuple;
//   static if(I == T.tupleof.length) {
//     alias _esdl__ListRands = TypeTuple!();
//   }
//   else {
//     static if(hasRandAttr!(T, I)) {
//       alias _esdl__ListRands = TypeTuple!(T, I, _esdl__ListRands!(T, I+1));
//     }
//     else {
//       alias _esdl__ListRands = _esdl__ListRands!(T, I+1);
//     }
//   }
// }

// template hasRandAttr(T, int I=0) {
//   enum hasRandAttr = hasRandInList!(__traits(getAttributes, T.tupleof[I]));
// }

// template hasRandInList(A...) {
//   static if(A.length == 0) {
//     enum bool hasRandInList = false;
//   }
//   else static if(__traits(isSame, A[0], rand) ||
// 		 is(A[0] unused: rand!M, M...)) {
//       enum bool hasRandInList = true;
//     }
//     else {
//       enum bool hasRandInList = hasRandInList!(A[1..$]);
//     }
// }

// template getRandAttr(T, string R) {
//   alias getRandAttr = scanRandAttr!(__traits(getAttributes,
// 					     __traits(getMember, T, R)));
// }

// template getRandAttr(T, int I, int N) {
//   alias Attr = getRandAttr!(T, I);
//   static if (is (Attr == _esdl__rand!A, A...)) {
//     static assert(A.length > N);
//     enum int getRandAttr = A[N];
//   }
//   else {
//     static assert(false);
//   }
// }

template _esdl__TypeHasNorandAttr(T) {
  static if (is (T == class) || is (T == struct)) {
    enum rand RAND = scanRandAttr!(__traits(getAttributes, T));
    static if (RAND.hasProxy()) {
      enum bool _esdl__TypeHasNorandAttr = false;
    }
    else {
      enum bool _esdl__TypeHasNorandAttr = true;
    }
  }
  else {
      enum bool _esdl__TypeHasNorandAttr = false;
  }
}

// template scanNorandHierAttr(A...) {
//   static if(A.length == 0) {
//     enum bool scanNorandHierAttr = false;
//   }
//   else static if(__traits(isSame, A[0], _esdl__NorandHier)) {
//     enum bool scanNorandHierAttr = true;
//   }
//   else {
//     enum rand scanNorandHierAttr = scanNorandHierAttr!(A[1..$]);
//   }
// }

template getRandAttr(T, int I) {
  alias getRandAttr = scanRandAttr!(__traits(getAttributes, T.tupleof[I]));
}

template scanRandAttr(A...) {
  static if(A.length == 0) {
    enum rand scanRandAttr = rand(true, false);
  }
  else static if(__traits(isSame, A[0], rand)) {
    enum rand scanRandAttr = rand(false, false);
  }
  else static if (__traits(compiles, typeof(A[0])) &&
		  (is (typeof(A[0]) == rand))) {
    enum rand scanRandAttr = A[0];
  }
  else {
    enum rand scanRandAttr = scanRandAttr!(A[1..$]);
  }
}


class _esdl__RandGen
{
  import std.random;

  private Random _gen;

  private uint _seed;

  this(uint seed) {
    _seed = seed;
    _gen = Random(seed);
  }

  void seed(uint seed) {
    _seed = seed;
    _gen.seed(seed);
  }

  bool flip() {
    auto x = dice(_gen, 50, 50);
    if (x == 0) return false;
    else return true;
  }

  double get() {
    return uniform(0.0, 1.0, _gen);
  }

  @property T gen(T)() {
    static if (isBoolean!T) {
      return flip();
    }
    else static if (is (T == enum)) {
      static immutable T[EnumMembers!T.length] vals = [EnumMembers!T];
      return vals[uniform(0, cast(uint) vals.length, _gen)];
    }
    else static if (isIntegral!T) {
      return uniform!(T)(_gen);
    }
    else static if (isBitVector!T) {
      T val;
      val.randomize(_gen);
      return val;
    }
    else {
      static assert(false);
    }
  }

  @property void gen(T)(T* t) {
    static if (isBoolean!T) {
      *t = cast(T) flip();
    }
    else static if (is (T == enum)) {
      static immutable T[EnumMembers!T.length] vals = [EnumMembers!T];
      *t = vals[uniform(0, cast(uint) vals.length, _gen)];
    }
    else static if(isIntegral!T) {
      *t = uniform!(T)(_gen);
    }
    else static if(isBitVector!T) {
      t.randomize(_gen);
    }
    else {
      static assert(false);
    }
  }

  @property void gen(T)(ref T t) {
    static if (isBoolean!T) {
      t = cast(T) flip();
    }
    else static if (is (T == enum)) {
      static immutable T[EnumMembers!T.length] vals = [EnumMembers!T];
      t = vals[uniform(0, cast(uint) vals.length, _gen)];
    }
    else static if(isIntegral!T) {
      t = uniform!(T)(_gen);
    }
    else static if(isBitVector!T) {
      t.randomize(_gen);
    }
    else {
      static assert(false);
    }
  }

  @property auto gen(T1, T2)(T1 a, T2 b)
    if(isIntegral!T1 && isIntegral!T2) {
      return uniform(a, b, _gen);
    }

  @property void gen(T, T1, T2)(ref T t, T1 a, T2 b)
    if(isIntegral!T1 && isIntegral!T2) {
      t = uniform(a, b, _gen);
    }

  @property void gen(T, T1, T2)(T* t, T1 a, T2 b)
    if(isIntegral!T1 && isIntegral!T2) {
      *t = uniform(a, b, _gen);
    }
}

enum CstUnaryOp: byte
{   NOT,
    NEG,
    }

enum CstBinaryOp: byte
{   AND,
    OR ,
    XOR,
    ADD,
    SUB,
    MUL,
    DIV,
    REM,
    LSH,
    RSH,			// Arith shift right ">>"
    LRSH,			// Logic shift right ">>>"
    }

enum CstSliceOp: byte
{   SLICE,
    SLICEINC,
}

enum CstCompareOp: byte
{   LTH,
    LTE,
    GTH,
    GTE,
    EQU,
    NEQ,
    }


enum CstLogicOp: byte
{   LOGICAND,
    LOGICOR,
    LOGICIMP,
    LOGICNOT,
    }


enum CstVectorOp: byte
{   NONE,
    BEGIN_INT,
    BEGIN_UINT,
    BEGIN_LONG,
    BEGIN_ULONG,
    SUM,
    MULT
    }

enum CstUniqueOp: byte
{   INIT,
    INT,
    UINT,
    LONG,
    ULONG,
    UNIQUE
    }


enum CstInsideOp: byte
{   INSIDE,
    EQUAL,
    RANGE,
    RANGEINCL,
    DONE
    }

enum isLvalue(alias A) = is(typeof((ref _){}(A)));
