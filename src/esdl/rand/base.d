module esdl.rand.base;

import esdl.data.bvec: isBitVector;
import std.traits: isIntegral, isBoolean, isArray, isStaticArray, isDynamicArray;
import std.meta: AliasSeq;

// To be returned when no @rand or @norand is found
enum _esdl__norand;


interface _esdl__Norand {}

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
enum norand;

template rand(N...) {
  static if(CheckRandParams!N) {
    struct rand { }
  }
}

template isVecSigned(L) {
  import std.traits: isIntegral, isSigned;
  static if (is(L: bool))
    enum bool isVecSigned = false;
  else static if (isBitVector!L)
    enum bool isVecSigned = L.ISSIGNED;
  else static if (isIntegral!L)
    enum bool isVecSigned = isSigned!L;
  else
    static assert(false, "isVecSigned: Can not determine sign of type " ~
		  L.stringof);
}

template LeafElementType(T)
{
  import std.range;		// ElementType
  static if(isArray!T) {
    alias LeafElementType = LeafElementType!(ElementType!T);
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
  static if(isArray!T) {
    enum int _esdl__ArrOrder = 1 + _esdl__ArrOrder!(ElementType!T) - N;
  }
  else {
    enum int _esdl__ArrOrder = 0;
  }
}

template _esdl__ArrOrder(T, int I, int N=0) {
  enum int _esdl__ArrOrder = _esdl__ArrOrder!(typeof(T.tupleof[I])) - N;
}

// Make sure that all the parameters are of type size_t
template CheckRandParamsLoop(N...) {
  static if(N.length > 0) {
    static if(!is(typeof(N[0]) == bool) && // do not confuse bool as size_t
	      is(typeof(N[0]) : size_t)) {
      static assert(N[0] != 0, "Can not have arrays with size 0");
      static assert(N[0] > 0, "Can not have arrays with negative size");
      enum bool CheckRecurse = CheckRandParamsLoop!(N[1..$]);
      enum bool CheckRandParamsLoop = CheckRecurse;
    }
    else {
      static assert(false, "Only positive integral values are allowed as array dimensions");
      enum bool CheckRandParamsLoop = false;
    }
  }
  else {
    enum bool CheckRandParamsLoop = true;
  }
}

template CheckRandParams(N...) {
  static if(N.length == 1 && N[0] == false) {
    enum bool CheckRandParams = true;
  }
  else {
    enum bool CheckRandParams = CheckRandParamsLoop!N;
  }
}

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

template hasRandAttr(T, int I=0) {
  enum hasRandAttr = hasRandInList!(__traits(getAttributes, T.tupleof[I]));
}

template hasRandInList(A...) {
  static if(A.length == 0) {
    enum bool hasRandInList = false;
  }
  else static if(__traits(isSame, A[0], rand) ||
		 is(A[0] unused: rand!M, M...)) {
      enum bool hasRandInList = true;
    }
    else {
      enum bool hasRandInList = hasRandInList!(A[1..$]);
    }
}

template getRandAttr(T, string R) {
  alias getRandAttr = scanRandAttr!(__traits(getAttributes,
					     __traits(getMember, T, R)));
}

template getRandAttrN(alias R, int N) {
  static if(is(R == rand!A, A...)) {
    static assert(A.length > N);
    enum int getRandAttrN = A[N];
  }
  else {
    static assert(false);
  }
}

template getRandAttr(T, int I, int N) {
  alias Attr = getRandAttr!(T, I);
  static if(is(Attr == rand!A, A...)) {
    static assert(A.length > N);
    enum int getRandAttr = A[N];
  }
  else {
    static assert(false);
  }
}

template getRandAttr(T, int I) {
  alias getRandAttr = scanRandAttr!(__traits(getAttributes, T.tupleof[I]));
}

template scanRandAttr(A...) {
  static if(A.length == 0) {
    alias scanRandAttr = _esdl__norand;
  }
  else static if(__traits(isSame, A[0], norand)) {
      static assert(__traits(isSame, scanRandAttr!(A[1..$]), _esdl__norand));
      alias scanRandAttr = A[0];
  }
  else static if(__traits(isSame, A[0], rand) ||
		 is(A[0] unused: rand!M, M...)) {
      static assert(__traits(isSame, scanRandAttr!(A[1..$]), _esdl__norand));
      alias scanRandAttr = A[0];
    }
    else {
      alias scanRandAttr = scanRandAttr!(A[1..$]);
    }
}

class _esdl__RandGen
{
  import std.random;

  private Random _gen;

  this(uint _seed) {
    _gen = Random(_seed);
  }

  void seed(uint _seed) {
    _gen.seed(_seed);
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
      T val = flip();
      return val;
    }
    else static if(isIntegral!T) {
      T val = uniform!(T)(_gen);
      return val;
    }
    else static if(isBitVector!T) {
	T val;
	val.randomize(_gen);
	return val;
      }
      else {
	static assert(false);
      }
  }

  @property void gen(T)(ref T t) {
    static if (isBoolean!T) {
      t = flip();
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
}
