module esdl.rand.misc;

import esdl.data.queue;
import esdl.data.folder: Charbuf;
import std.traits: isIntegral, isBoolean, isArray, EnumMembers, isSigned,
  isSomeChar, isAssociativeArray, ValueType, KeyType, OriginalType;
import std.range: ElementType;
import std.meta: AliasSeq;
import esdl.data.bvec: isBitVector;

alias _esdl__Sigbuf = Charbuf!("Signature", 0);

public enum SolveOrder: ubyte { UNDECIDED, NOW, LATER }

// https://stackoverflow.com/questions/46073295/implicit-type-promotion-rules
// Mainly two things:
// 1. if a number smaller than int can fit into an int, it will be promoted to int
//    We can extend this principle to vectors with < 64 bits and promote that to long
// 2. if a signed integer interacts with a non-singed interger of the same size,
//    both will be promoted to unsigned
public enum CstVecType: ubyte { BOOL, INT, UINT, LONG, ULONG, CENT, UCENT, NAN }

template GetVecType(T) // if (isIntegral!T || isBitVector!T || isBoolean!T)
{
  static assert (isIntegral!T || isBitVector!T || isBoolean!T);

  static if (isIntegral!T) {
    enum size_t tSize = T.sizeof * 8;
    enum bool tSign = isSigned!T;
  }
  else static if (isBitVector!T) {
    enum size_t tSize = T.SIZE * 8;
    enum bool tSign = T.ISSIGNED;
  }
  else static if (isBoolean!T) {
    enum size_t tSize = 1;
    enum bool tSign = false;
  }

  static if (tSign) {
    static if (tSize <= 32) enum CstVecType GetVecType = CstVecType.INT;
    else static if (tSize <= 64) enum CstVecType GetVecType = CstVecType.LONG;
    else static if (tSize <= 128) enum CstVecType GetVecType = CstVecType.CENT;
    else enum CstVecType GetVecType = CstVecType.NAN;
  }
  else {
    static if (tSize == 1) enum CstVecType GetVecType = CstVecType.BOOL;
    else static if (tSize < 32) enum CstVecType GetVecType = CstVecType.INT;
    else static if (tSize == 32) enum CstVecType GetVecType = CstVecType.UINT;
    else static if (tSize < 64) enum CstVecType GetVecType = CstVecType.LONG;
    else static if (tSize == 64) enum CstVecType GetVecType = CstVecType.ULONG;
    else static if (tSize < 128) enum CstVecType GetVecType = CstVecType.CENT;
    else static if (tSize == 128) enum CstVecType GetVecType = CstVecType.UCENT;
    else enum CstVecType GetVecType = CstVecType.NAN;
  }
}

CstVecType getCommonVecType(CstVecType lhs, CstVecType rhs) {
  if (rhs > lhs) return rhs;
  else return lhs;
}

public enum DomainContextEnum: ubyte { DEFAULT, INDEX, BITINDEX, DIST }

// write in Hex form for all the bytes of data
size_t writeHexString(T)(T val, ref _esdl__Sigbuf str) {
  import esdl.data.bvec: isBitVector;
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
  // enum phony;
  static interface disable { }
  static interface barrier { }

  bool _noRand;
  bool _noProxy;

  uint[] _counts;

  this(uint[] counts ...) {
    _counts = counts;
  }
  
  this(bool hasRand) {
    _noRand  = ! hasRand;
    _noProxy = false;
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

template isRandomizableInt(T) {
  import esdl.data.bvec: isBitVector;
  enum bool isRandomizableInt =
    isIntegral!T || isBitVector!T || isBoolean!T; // || isSomeChar!T
}

template isRandomizableEnum(T) {
  alias OT = OriginalType!T;
  enum bool isRandomizableEnum = is (T == enum) && isRandomizableInt!OT;
}

template isRandomizable(T) {
  enum bool isRandomizable = isRandomizableInt!T || isRandomizableEnum!T;
}


template isRandVectorSet(T) {
  enum bool isRandVectorSet = isRandVectorAssoc!T || isRandVectorArray!T;
}

// template isRandStructSet(T) {
//   enum bool isRandStructSet = isRandStructAssoc!T || isRandStructArray!T;
// }

// template isRandClassSet(T) {
//   enum bool isRandClassSet = isRandClassAssoc!T || isRandClassArray!T;
// }

template isRandObjectSet(T) {
  enum bool isRandObjectSet = isRandObjectAssoc!T || isRandObjectArray!T;
}

template isRandObject(T) {	// exclude extern C++ classes using is (T: Object)
  static if ((is (T == class) && is (T: Object)) ||
	     (is (T == struct) && !isQueue!T)) {
    enum bool isRandObject = ! _esdl__TypeHasRandBarrier!T;
  }
  else static if (is (T == U*, U)) {
    static if (is (U == struct))
      enum bool isRandObject = ! _esdl__TypeHasRandBarrier!U;
    else
      enum bool isRandObject = false;
  }
  else enum bool isRandObject = false;
}

// Associative arrays that can be randomized
template isRandVectorAssoc(T) {
  // only the top level array can be Assoc
  static if (isAssociativeArray!T) {
    alias K = KeyType!T; 
    static if (isRandomizable!K) {
      alias E = ValueType!T;
      enum bool isRandVectorAssoc =
	isRandVectorArray!E || isRandomizable!E;
    }
    else {
      enum bool isRandVectorAssoc = false;
    }
  }
  else {
    enum bool isRandVectorAssoc = false;
  }
}

// template isRandStructAssoc(T) {
//   // only the top level array can be Assoc
//   static if (isAssociativeArray!T) {
//     alias K = KeyType!T; 
//     static if (isRandomizable!K) {
//       alias E = ValueType!T;
//       enum bool isRandStructAssoc =
// 	isRandStructArray!E || is (E == struct);
//     }
//     else {
//       enum bool isRandStructAssoc = false;
//     }
//   }
//   else {
//     enum bool isRandStructAssoc = false;
//   }
// }

// template isRandClassAssoc(T) {
//   // only the top level array can be Assoc
//   static if (isAssociativeArray!T) {
//     alias K = KeyType!T; 
//     static if (isRandomizable!K) {
//       alias E = ValueType!T;
//       enum bool isRandClassAssoc =
// 	isRandClassArray!E || is (E == class) ||
// 	(is (E == U*, U) && is (U == struct));
//     }
//     else {
//       enum bool isRandClassAssoc = false;
//     }
//   }
//   else {
//     enum bool isRandClassAssoc = false;
//   }
// }

template isRandObjectAssoc(T) {
  // only the top level array can be Assoc
  static if (isAssociativeArray!T) {
    alias K = KeyType!T; 
    static if (isRandomizable!K) {
      alias E = ValueType!T;
      enum bool isRandObjectAssoc =
	isRandObjectArray!E || isRandObject!E;
    }
    else {
      enum bool isRandObjectAssoc = false;
    }
  }
  else {
    enum bool isRandObjectAssoc = false;
  }
}

template isRandVectorArray(T) {
  static if (isArray!T) {
    alias E = ElementType!T;
    enum bool isRandVectorArray =
      isRandVectorArray!E || isRandomizable!E;
  }
  else static if (isQueue!T) {
    alias E = T.ElementType;
    enum bool isRandVectorArray =
      isRandVectorArray!E || isRandomizable!E;
  }
  else {
    enum bool isRandVectorArray = false;
  }
}

// template isRandStructArray(T) {
//   static if (isArray!T) {
//     alias E = ElementType!T;
//     enum bool isRandStructArray =
//       isRandStructArray!E || is (E == struct);
//   }
//   else static if (isQueue!T) {
//     alias E = T.ElementType;
//     enum bool isRandStructArray =
//       isRandStructArray!E || is (E == struct);
//   }
//   else {
//     enum bool isRandStructArray = false;
//   }
// }

// template isRandClassArray(T) {
//   static if (isArray!T) {
//     alias E = ElementType!T;
//     enum bool isRandClassArray =
//       isRandClassArray!E || is (E == class) ||
//       (is (E == U*, U) && is (U == struct));
//   }
//   else static if (isQueue!T) {
//     alias E = T.ElementType;
//     enum bool isRandClassArray =
//       isRandClassArray!E || is (E == class) ||
//       (is (E == U*, U) && is (U == struct));
//   }
//   else {
//     enum bool isRandClassArray = false;
//   }
// }

template isRandObjectArray(T) {
  static if (isArray!T) {
    alias E = ElementType!T;
    enum bool isRandObjectArray =
      isRandObjectArray!E || isRandObject!E;
  }
  else static if (isQueue!T) {
    alias E = T.ElementType;
    enum bool isRandObjectArray =
      isRandObjectArray!E || isRandObject!E;
  }
  else {
    enum bool isRandObjectArray = false;
  }
}

template isVecSigned(L) {
  import esdl.data.bvec: isBitVector;
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
  // static if (is (T == string)) {
  //   alias LeafElementType = immutable(char);
  // }
  // else
  static if (isArray!T) {
    alias LeafElementType = LeafElementType!(ElementType!T);
  }
  else static if (isQueue!T) {
    alias LeafElementType = LeafElementType!(T.ElementType);
  }
  else static if (isAssociativeArray!T) {
    alias LeafElementType = LeafElementType!(ValueType!T);
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
  else static if (isArray!T) {
    alias ElementTypeN = ElementTypeN!(ElementType!T, N-1);
  }
  else static if (isQueue!T) {
    alias ElementTypeN = ElementTypeN!(T.ElementType, N-1);
  }
  else static if (isAssociativeArray!T) {
    alias ElementTypeN = ElementTypeN!(ValueType!T, N-1);
  }
  else static assert(false);
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
  else static if (isAssociativeArray!T) {
    enum int _esdl__ArrOrder = 1 + _esdl__ArrOrder!(ValueType!T) - N;
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

template _esdl__TypeHasRandBarrier(T) {
  static if (is (T == class) &&
	     is (T B == super) &&
	     _esdl__TypeEnlistsRandBarrier!B) {
    enum bool _esdl__TypeHasRandBarrier = true;
  }
  else static if (is (T == struct) &&
		  __traits (compiles,  T._esdl__TypeHasRandBarrier)
		  ) {
    enum bool _esdl__TypeHasRandBarrier = true;
  }
  else {
    enum bool _esdl__TypeHasRandBarrier = false;
  }
}

template _esdl__TypeEnlistsRandBarrier(B...) {
  static if (B.length == 0)
    enum bool _esdl__TypeEnlistsRandBarrier = false;
  else static if (is (B[0] == rand.barrier))
    enum bool _esdl__TypeEnlistsRandBarrier = true;
  else
    enum bool _esdl__TypeEnlistsRandBarrier =
      _esdl__TypeEnlistsRandBarrier!(B[1..$]);
}

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
  static if (A.length == 0) {
    enum rand scanRandAttr = rand(true, true);
  }
  else static if (__traits(isSame, A[0], rand)) {
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
    LOGICEQ,
    LOGICNEQ
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

struct EnumRange(E) if (is(E == enum))
  {
    private E _min;
    private E _max;
    E min() { return _min; }
    E max() { return _max; }
}

template EnumRanges(E) if (is(E == enum) && isIntegral!E)
  {
    import std.meta : AliasSeq;
    template EnumSpecificRanges(names...)
    {
      static if (names.length == 0) {
	alias EnumSpecificRanges = AliasSeq!();
      }
      else static if (names.length == 1) {
	enum VAL = __traits(getMember, E, names[0]);
	alias EnumSpecificRanges =
	  AliasSeq!(EnumRange!E(VAL, VAL));
      }
      else {
	alias PART1 = EnumSpecificRanges!(names[0 .. $/2]);
	alias PART2 = EnumSpecificRanges!(names[$/2 .. $]);

	enum MIN1 = PART1[$-1]._min;
	enum MAX1 = PART1[$-1]._max;
	enum MIN2 = PART2[0]._min;
	enum MAX2 = PART2[0]._max;

	static if (MIN2 >= MIN1 && // MAX1 + 1 > MAX1 &&
		   (MIN2 <= MAX1 || MIN2 <= MAX1 + 1) &&
		   MAX2 >= MAX1) {
	  alias EnumSpecificRanges =
	    AliasSeq!(PART1[0..$-1], EnumRange!E(MIN1, MAX2), PART2[1..$]);
	}
	else {
	  alias EnumSpecificRanges = AliasSeq!(PART1, PART2);
	}
      }
    }

    alias EnumRanges = EnumSpecificRanges!(__traits(allMembers, E));
}
