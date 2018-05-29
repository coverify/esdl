// Written in the D programming language.

// Copyright: Copyright Digital Mars 2007 - 2011
//            Coverify Systems Technology 2011 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>
//            Sumit Adhikari <adhikari@ieee.org>
// Credit:    Some code inherited from Dlang Phobos, authored by:
//            $(WEB digitalmars.com, Walter Bright),
//            $(WEB erdani.org, Andrei Alexandrescu),

// This file is part of esdl.

module esdl.data.bvec;

import std.conv;
import std.string;
import std.traits;
import std.format;
import std.bitmanip;
// required for ElementType
import std.range;
import core.bitop;
import core.exception;
import esdl.base.comm;

static import std.algorithm; 	// required for min, max

import esdl.intf.vpi: s_vpi_vecval;
    

// required for appender
// import std.array;

alias BitArray barray;

version(BVEC_NOCHECK) {
  private enum bool SAFE_BVEC=false;
  private enum bool NO_CHECK_SIZE=true;
}
 else {
   private enum bool SAFE_BVEC=true;
   private enum bool NO_CHECK_SIZE=false;
 }

template isBitVector(T) {
  static if(is(T unused == _bvec!(S, L, N), bool S, bool L, N...))
    enum bool isBitVector = true;
  else
  enum bool isBitVector = false;
}

template BitLength(T) {
  static if(isBitVector!T)      enum size_t BitLength = T.SIZE;
  else static if(isBoolean!T)   enum size_t BitLength = 1;
    else                        enum size_t BitLength = 8 * T.sizeof;
}

public class LogicError: Error
{
  this(string err, string file, size_t line, Throwable next = null) {
    super(err, file, line);
  }
}

// gets called at compile time
private string removeDelimiters(string bits) {
  if(bits.length == 0) return "";
  if(bits.length == 1) {
    if(bits == " " || bits == "_") return "";
    else return bits;
  }
  else
    return removeDelimiters(bits[0..$/2]) ~
      removeDelimiters(bits[$/2..$]);
}

private string octalToLogic(string value) {
  string result; // = "0b";
  // chomp the first 0
  // import std.exception;
  // enforce(value[0..1] == "0");
  string v = value; // value[1..$];
  foreach(c; v) {
    switch(c) {
    case '0': result ~= "000"; break;
    case '1': result ~= "001"; break;
    case '2': result ~= "010"; break;
    case '3': result ~= "011"; break;
    case '4': result ~= "100"; break;
    case '5': result ~= "101"; break;
    case '6': result ~= "110"; break;
    case '7': result ~= "111"; break;
    case 'z':
    case 'Z': result ~= "ZZZ"; break;
    case 'x':
    case 'X': result ~= "XXX"; break;
    default: assert(false, "illegal character: " ~ c);
    }
  }
  return result;
}

package T logicToOctal(T)(T value) if(is(T == string) || is(T == char[])) {
  // zfill to a multiple of 3
  char[] v = rightJustify(value, cast(int)(3*((value.length + 2)/3)), '0');
  char[] result; //  = ['0'];
  for(size_t i = 0; i != v.length/3; ++i) {
    bool isX = false;
    bool isZ = false;
    foreach(b; v[3*i..3*(i+1)]) {
      if(b == 'Z' || b == 'z') isZ = true;
      if(b == 'X' || b == 'x') isX = true;
    }
    if(isX) result ~= 'X';
    else if(isZ)
      if(v[3*i..3*(i+1)] == "ZZZ" ||
	 v[3*i..3*(i+1)] == "zzz") result ~= 'Z';
      else result ~= 'X';
    else {
      switch(v[3*i..3*(i+1)]) {
      case "000": result ~= '0'; break;
      case "001": result ~= '1'; break;
      case "010": result ~= '2'; break;
      case "011": result ~= '3'; break;
      case "100": result ~= '4'; break;
      case "101": result ~= '5'; break;
      case "110": result ~= '6'; break;
      case "111": result ~= '7'; break;
      default: assert(false, "illegal octal sequence: " ~ v[i..i+3]);
      }
    }
  }
  return cast(T) result;
 }

// works for binary, octal and hex string literals
private bool isStr4State(string str) {
  if(str.length == 0) return false;
  if(str.length == 1)
    if(str[0] == 'x' || str[0] == 'X' || str[0] == 'z' || str[0] == 'Z')
      return true;
    else
      return false;
  else
    return isStr4State(str[0..$/2]) || isStr4State(str[$/2..$]);
}

// works for binary, octal and hex string literals
private string extractBits(bool isA, size_t RADIX)(string str) {
  string v = removeDelimiters(str);
  string value = "";
  static if(RADIX == 2) { // binary
    value ~= "0b";
    foreach(char digit; v) {
      switch(digit) {
      case '0','1':
	static if(isA) value ~= digit;
	else           value ~= '0';
	break;
      case 'Z','z':
	static if(isA) value ~= '0';
	else value ~= '1';
	break;
      case 'X','x':
	static if(isA) value ~= '1';
	else value ~= '1';
	break;
      default: assert(false,
		      "Unrecognised string literal format: " ~ str);
      }
    }
    return value;
  }
  else
    static if(RADIX == 16) { // hexadecimal
      value ~= "0x";
      foreach(char digit; v) {
	switch(digit) {
	case
	  '0','1','2','3','4','5','6','7','8','9',
	  'A','B','C','D','E','F',
	  'a','b','c','d','e','f':
	  static if(isA) value ~= digit;
	  else           value ~= '0';
	  break;
	case 'Z','z':
	  static if(isA) value ~= '0';
	  else value ~= 'F';
	  break;
	case 'X','x':
	  static if(isA) value ~= 'F';
	  else value ~= 'F';
	  break;
	default: assert(false,
			"Unrecognised string literal format: " ~ str);
	}
      }
      return value;
    }
    else
      static if(RADIX == 8) { // octal
	value ~= "0";
	foreach(char digit; v) {
	  switch(digit) {
	  case
	    '0','1','2','3','4','5','6','7':
	    static if(isA) value ~= digit;
	    else           value ~= '0';
	    break;
	  case 'Z','z':
	    static if(isA) value ~= '0';
	    else value ~= '7';
	    break;
	  case 'X','x':
	    static if(isA) value ~= '7';
	    else value ~= '7';
	    break;
	  default: assert(false,
			  "Unrecognised string literal format: " ~ str);
	  }
	}
	return value;
      }
  assert(false, "Unrecognised string literal format: " ~ str);
}

// works for binary, octal and hex string literals
// Returns a string with compilable array elements.
private string stringToBits(string value,
			    size_t bytesPerWord,
			    size_t numWords) {
  string v = removeDelimiters(value);
  string code = "";

  if(v[0..2] == "0b" || v[0..2] == "0B") { // binary
    v = v[2..$];
    code ~= "[";
    for(size_t i = 0; i != numWords; ++i) {
      // If the string is shorter than numWords, fill in zeros
      if(v.length == 0) {	// all processed
	code ~= "0";
      }
      else if(v.length >= 8*bytesPerWord) {
	code ~= "cast(store_t) 0b" ~ v[$-8*bytesPerWord..$];
	v = v[0..$-8*bytesPerWord];
      }
      else {
	code ~= "cast(store_t) 0b" ~ v;
	v = "";
      }
      if(i != numWords - 1) {	// not the last word
	code ~= ", ";
      }
      else {			// last word
	code ~= "]";
      }
    }
    return code;
  }
  else if(v[0..2] == "0x" || v[0..2] == "0X") { // hexadecimal
    v = v[2..$];
    code ~= "[";
    for(size_t i = 0; i != numWords; ++i) {
      if(v.length == 0) {	// all processed
	code ~= "0";
      }
      else if(v.length >= 2*bytesPerWord) {
	code ~= "cast(store_t) 0x" ~ v[$-2*bytesPerWord..$];
	v = v[0..$-2*bytesPerWord];
      }
      else {
	code ~= "cast(store_t) 0x" ~ v;
	v = "";
      }
      if(i != numWords - 1) {	// not the last word
	code ~= ", ";
      }
      else {			// last word
	code ~= "]";
      }
    }
    return code;
  }
  else if(v[0..1] == "0") {	// octal
    return stringToBits(octalToLogic(v), bytesPerWord, numWords);
  }
  assert(false, "Unrecognised string literal format: " ~ value);
}


private size_t stringBitSize(string value, size_t RADIX) {
  string v = removeDelimiters(value);
  return cast(size_t)(_log2(RADIX) * v.length);
}

private ubyte _log2(size_t n) {
  if(n == 1) return 0;
  else return cast(ubyte)(1 + _log2(n/2));
}

private template VecParams(size_t SIZE, bool S=true) {
  static if(SIZE <= 8) {
    static if(S) {
      private alias StoreT = byte;
      private alias ValueT = byte;
    }
    else {
      private alias StoreT = ubyte;
      private alias ValueT = ubyte;
    }
  }
  else static if(SIZE <= 16) {
    static if(S) {
      private alias StoreT = short;
      private alias ValueT = short;
    }
    else {
      private alias StoreT = ushort;
      private alias ValueT = ushort;
    }
  }
  else static if(SIZE <= 32) {
    static if(S) {
      private alias StoreT = int;
      private alias ValueT = int;
    }
    else {
      private alias StoreT = uint;
      private alias ValueT = uint;
    }
  }
  else {
    static if(S) {
      private alias StoreT = int;
      private alias ValueT = long;
    }
    else {
      private alias StoreT = uint;
      private alias ValueT = ulong;
    }
  }
  // else static if(SIZE <= 32 || size_t.sizeof*8 == 32) {
  //   static if(SIZE <= 32) {
  //     static if(S) {
  // 	private alias StoreT = int;
  // 	private alias ValueT = int;
  //     }
  //     else {
  // 	private alias StoreT = uint;
  // 	private alias ValueT = uint;
  //     }
  //   }
  //   else {
  //     static if(S) {
  // 	private alias StoreT = int;
  // 	private alias ValueT = long;
  //     }
  //     else {
  // 	private alias StoreT = uint;
  // 	private alias ValueT = ulong;
  //     }
  //   }
  // }
  // else {
  //   static if(S) {
  //     private alias StoreT = long;
  //     private alias ValueT = long;
  //   }
  //   else {
  //     private alias StoreT = ulong;
  //     private alias ValueT = ulong;
  //   }
  // }

  // Word Size -- bits in a word
  private enum size_t WORDSIZE = 8*StoreT.sizeof;
  // _aval size(in words)
  private enum size_t STORESIZE = (8*StoreT.sizeof + SIZE - 1)/(8*StoreT.sizeof);
  // Word size of the Most Significant word
  // Make sure that MSWSIZE is never 0(is equal to WORDSIZE instead)
  private enum size_t MSWSIZE = ((SIZE-1) % WORDSIZE) + 1;
  static if(MSWSIZE == WORDSIZE)	// All ones
    // Shift by WORDSIZE is erroneous -- D gives compile time error
    {
      private enum StoreT UMASK = (cast(StoreT) -1);
      private enum StoreT SMASK = 0;
    }
  else {
    static if (StoreT.sizeof >= 4) {
      private enum StoreT UMASK = ((cast(StoreT) 1) << MSWSIZE) - 1;
      private enum StoreT SMASK = cast(StoreT) (~UMASK);
    }
    else {
      private enum StoreT UMASK = cast(StoreT) ((1 << MSWSIZE) - 1);
      private enum StoreT SMASK = cast(StoreT) ~((1 << MSWSIZE) - 1);
    }
  }
}

// Make sure that all the parameters are of type size_t
template ConvVecParams(N...) {
  static if(N.length > 1) {
    static assert(!is(typeof(N[$-1]) == bool) && // do not confuse bool as size_t
		  is(typeof(N[$-1]): size_t));
    static assert(N[$-1] >= 0, "Can not have vectors with non-positive dimension");
    enum ConvVecParams = ConvVecParams!(N[0..$-1]) ~ cast(size_t) (N[$-1]);
  }
  else {
    static assert(N.length == 1);
    enum ConvVecParams = cast(size_t) (N[$-1]);
  }
}

// Make sure that all the parameters are of type size_t
template CheckVecParams(N...) {
  static if(N.length > 0) {
    import std.traits;
    static if(!is(typeof(N[0]) == bool) && // do not confuse bool as size_t
	      is(typeof(N[0]) == size_t)) {
      static assert(N[0] != 0, "Can not have vectors with size 0");
      enum bool CheckVecParams = CheckVecParams!(N[1..$]);
    }
    else {
      enum bool CheckVecParams = false;
    }
  }
  else {
    enum bool CheckVecParams = true;
  }
}

template VecSize(size_t L=1, N...) {
  static if(N.length > 0) {
    import std.traits;
    enum size_t VecSize = VecSize!(L*N[0], N[1..$]);
  }
  else {
    enum size_t VecSize = L;
  }
}

// One of the reasons for creating this function is that D operates
// A.opCmp(B) as well as B.opCmp(A) in case both are defined. We want
// to avoid that situation.
template _vecCmpT(T, U)	// return true if T >= U
  if(isBitVector!T && isBitVector!U) {
  static if     (T.IS4STATE && !U.IS4STATE)  enum bool _vecCmpT = true;
  else static if(!T.IS4STATE && U.IS4STATE)  enum bool _vecCmpT = false;
  else static if(T.ISSIGNED && !U.ISSIGNED)  enum bool _vecCmpT = true;
  else static if(!T.ISSIGNED && U.ISSIGNED)  enum bool _vecCmpT = false;
  else static if(T.SIZE > U.SIZE)            enum bool _vecCmpT = true;
  else static if(T.SIZE < U.SIZE)            enum bool _vecCmpT = false;
  else static if(T.ELEMSIZE > U.ELEMSIZE)    enum bool _vecCmpT = true;
  else static if(T.ELEMSIZE < U.ELEMSIZE)    enum bool _vecCmpT = false;
  else static if(T.MULTIDIM && !U.MULTIDIM)  enum bool _vecCmpT = true;
  else static if(!T.MULTIDIM && U.MULTIDIM)  enum bool _vecCmpT = false;
  else static if(!T.MULTIDIM && !U.MULTIDIM) enum bool _vecCmpT = true;
    else enum bool _vecCmpT = true; // _vecCmpT(T.ELEMTYPE, U.ELEMTYPE);
}

template _bvec(T, U, string OP)
  if((isBitVector!T || isIntegral!T) &&
     (isBitVector!U || isIntegral!U)) {
  static if (isIntegral!U) alias UU = _bvec!U;
  else alias UU = U;
  static if (isIntegral!T) alias TT = _bvec!U;
  else alias TT = T;
  static if(TT.ISSIGNED && UU.ISSIGNED) {enum bool S = true;}
  else                                {enum bool S = false;}
  static if(TT.IS4STATE || UU.IS4STATE) {enum bool L = true;}
  else                                {enum bool L = false;}
  static if(OP == "~") {
    alias _bvec!(TT.ISSIGNED, L, TT.SIZE + UU.SIZE) _bvec;
  }
  else {
    static if(TT.SIZE > UU.SIZE)        {enum size_t N = TT.SIZE;}
    else                              {enum size_t N = UU.SIZE;}
    alias _bvec = _bvec!(TT.ISSIGNED, L, N);
  }
}

// template _bvec(T, U, string OP)
//   if(isBitVector!T && isBitVector!U) {
//     static if(T.ISSIGNED && U.ISSIGNED) {enum bool S = true;}
//     else                                {enum bool S = false;}
//     static if(T.IS4STATE || U.IS4STATE) {enum bool L = true;}
//     else                                {enum bool L = false;}
//     static if(OP == "|" || OP == "&" || OP == "^") {
//       static if(T.SIZE > U.SIZE)        {enum size_t N = T.SIZE;}
//       else                              {enum size_t N = U.SIZE;}
//     }
//     static if(OP == "COMPARE") {	// for operands of opCmp
//       static if(T.SIZE > U.SIZE)        {enum size_t N = T.SIZE;}
//       else                              {enum size_t N = U.SIZE;}
//     }
//     static if(OP == "+" || OP == "-") {
//       static if(T.SIZE > U.SIZE)        {enum size_t N = T.SIZE + 1;}
//       else                              {enum size_t N = U.SIZE + 1;}
//     }
//     static if(OP == "*")                {enum size_t N = T.SIZE + U.SIZE;}
//     static if(OP == "/")                {enum size_t N = T.SIZE;}
//     static if(OP == "~") {
//       alias _bvec!(T.ISSIGNED, L, T.SIZE + U.SIZE) _bvec;
//     }
//     else {
//       alias _bvec!(T.ISSIGNED, L, N) _bvec;
//     }
//   }

struct _bvec(bool S, bool L, string VAL, size_t RADIX) {
  enum size_t SIZE = stringBitSize(VAL, RADIX);

  private alias VecParams!(SIZE,S).StoreT store_t;

  enum size_t   STORESIZE  = VecParams!(SIZE,S).STORESIZE;
  enum size_t   WORDSIZE   = VecParams!(SIZE,S).WORDSIZE;
  enum store_t  UMASK      = VecParams!(SIZE,S).UMASK;
  enum store_t  SMASK      = VecParams!(SIZE,S).SMASK;
  enum bool     IS4STATE   = L;
  enum bool     ISSIGNED   = S;

  private store_t[STORESIZE] _aval = void;

  public bool aValMSB() {
    static if(S) {
      if((this._aval[$-1] &
	  (cast(store_t) 1) << ((SIZE-1) % WORDSIZE)))
	return true;
      else
	return false;
    }
    else
      return false;
  }

  static if(L) {
    private store_t[STORESIZE] _bval = void;
    public bool bValMSB() {
      static if(S) {
	if((this._bval[$-1] &
	    (cast(store_t) 1) << ((SIZE-1) % WORDSIZE)))
	  return true;
	else
	  return false;
      }
      else
	return false;
    }
  }

  // default constructor not allowed for structures
  public this(int dummy) {
    // sign extension
    _aval = mixin(stringToBits(extractBits!(true, RADIX)(VAL),
			       store_t.sizeof, STORESIZE));
    static if(L) {
      _bval = mixin(stringToBits(extractBits!(false, RADIX)(VAL),
				 store_t.sizeof, STORESIZE));
      if(this.aValMSB) {
	_aval[$-1] |= SMASK;
      }
      else {
	_aval[$-1] &= UMASK;
      }
      if(this.bValMSB) {
	_bval[$-1] |= SMASK;
      }
      else {
	_bval[$-1] &= UMASK;
      }
    }
    else {
      foreach(i, n;(mixin(stringToBits(extractBits!(false, RADIX)(VAL),
				       store_t.sizeof, STORESIZE)))) {
	_aval[i] &= ~n;
      }
      if(this.aValMSB) {
	_aval[$-1] |= SMASK;
      }
      else {
	_aval[$-1] &= UMASK;
      }
    }
  }

  public T opCast(T)() const
    if(isBitVector!T) {
      enum bool _L = T.IS4STATE;
      enum bool _S = T.ISSIGNED;
      T result;
      static if(T.STORESIZE <= STORESIZE) {
	for(size_t i=0; i != T.STORESIZE; ++i) {
	  result._aval[i] = cast(T.store_t) this._aval[i];
	  static if(_L) {
	    static if(L) result._bval[i] =
			   cast(T.store_t) this._bval[i];
	    else          result._bval[i] = 0;
	  }
	  else {
	    // X and Z values reduce to 0
	    static if(L) result._aval[i] &=
			   ~(cast(T.store_t) this._bval[i]);
	  }
	}
	// sign extension
	if(result.aValMSB) result._aval[$-1] |= T.SMASK;
	else                  result._aval[$-1] &= T.UMASK;
	static if(_L) {
	  if(result.bValMSB) result._bval[$-1] |= T.SMASK;
	  else                  result._bval[$-1] &= T.UMASK;
	}
      }
      static if(T.STORESIZE > STORESIZE) {
	for(size_t i=0; i != STORESIZE; ++i) {
	  result._aval[i] = cast(T.store_t) this._aval[i];
	  static if(_L) {
	    static if(L) result._bval[i] =
			   cast(T.store_t) this._bval[i];
	    else          result._bval[i] = 0;
	  }
	  else {
	    // X and Z values reduce to 0
	    static if(L) result._aval[i] &=
			   ~(cast(T.store_t) this._bval[i]);
	  }
	}
	for(size_t i=STORESIZE; i != T.STORESIZE; ++i) {
	  // if RHS is signed, extend its sign
	  if(this.aValMSB) result._aval[i] = -1;
	  else                 result._aval[i] = 0;
	  static if(_L) {
	    static if(L) {
	      if(this.bValMSB) result._bval[i] = -1;
	      else                 result._bval[i] = 0;
	    }
	    else {
	      result._bval[i] = 0;
	    }
	  }
	  else {
	    static if(L) // X/Z reduce to 0
	      if(this.bValMSB) result._aval[i] = 0;
	  }
	}
	static if(!_S) {	// If result is not signed
	  result._aval[$-1] &= T.UMASK;
	  static if(_L) {
	    result._bval[$-1] &= T.UMASK;
	  }
	}
      }
      return result;
    }

  static size_t length() {
    return SIZE;
  }
}

template ToBitSize(alias N) if (isIntegral!(typeof(N)) && N >= 0) {
  static if (N == 0 || N == 1) enum ToBitSize = 1;
  else enum ToBitSize = ToBitSize!(N/2) + 1;
}

template ToBitSize(alias N) if (isIntegral!(typeof(N)) && N < 0) {
  static if (N == 0) enum ToBitSize = 1;
  static if (N == -1) enum ToBitSize = 2;
  else enum ToBitSize = ToBitSize!(N/2) + 1;
}

auto toBit(alias N)() if (isIntegral!(typeof(N))) {
  static if (N >= 0) {
    UBit!(ToBitSize!N) val;
    val._from(N);
    return val;
  }
  else {
    Bit!(ToBitSize!N) val;
    val._from(N);
    return val;
  }
}

enum UBit!1 BIT_0   = UBit!1(0);
enum UBit!1 BIT_1   = UBit!1(1);
alias _0 = BIT_0;
alias _1 = BIT_1;

enum ULogic!1 LOGIC_0 = ULogic!1(0);
enum ULogic!1 LOGIC_1 = ULogic!1(1);
enum ULogic!1 LOGIC_X = cast(ULogic!1)bin!"X";
enum ULogic!1 LOGIC_Z = cast(ULogic!1)bin!"Z";

alias _X = LOGIC_X;
alias _Z = LOGIC_Z;

alias _x = LOGIC_X;
alias _z = LOGIC_Z;

public auto bin(string VAL)() {
  enum bool L = isStr4State(VAL);
  alias vector_t = _bvec!(true, L, stringBitSize(VAL, 2));
  vector_t result = vector_t(_bvec!(true, L, VAL, 2)(0));
  return result;
}

public auto oct(string VAL)() {
  enum bool L = isStr4State(VAL);
  alias vector_t = _bvec!(true, L, stringBitSize(VAL, 8));
  vector_t result = vector_t(_bvec!(true, L, VAL, 8)(0));
  return result;
}

public auto hex(string VAL)() {
  enum bool L = isStr4State(VAL);
  alias vector_t = _bvec!(true, L, stringBitSize(VAL, 16));
  vector_t result = vector_t(_bvec!(true, L, VAL, 16)(0));
  return result;
}

template _bvec(T) if(is(T == bool)) {
  alias _bvec = _bvec!(false, false, 1);
}

template _bvec(T) if(isIntegral!T) {
  alias _bvec = _bvec!(isSigned!T, false, T.sizeof*8);
}

template _bvec(T) if(isBitVector!T) {
  alias _bvec = T;
}

template BitVec(N...) {
  alias  BitVec = _bvec!(true, false, ConvVecParams!N);
}

template UBitVec(N...) {
  alias  UBitVec = _bvec!(false, false, ConvVecParams!N);
}

template LogicVec(N...) {
  alias  LogicVec = _bvec!(true, true, ConvVecParams!N);
}

template ULogicVec(N...) {
  alias  ULogicVec = _bvec!(false, true, ConvVecParams!N);
}


private alias makeMutable(V) = _bvec!(V.ISSIGNED, V.IS4STATE, V.DIMENSIONS);

// A tightly packed fixed width vector of bits
struct _bvec(bool S, bool L, N...) if(CheckVecParams!N)
  {
    import esdl.data.time;

    enum size_t SIZE = VecSize!(1,N);
    private alias store_t = VecParams!(SIZE,S).StoreT;

    enum size_t  STORESIZE  = VecParams!(SIZE,S).STORESIZE;
    enum size_t  WORDSIZE   = VecParams!(SIZE,S).WORDSIZE;
    enum store_t UMASK      = VecParams!(SIZE,S).UMASK;
    enum store_t SMASK      = VecParams!(SIZE,S).SMASK;
    enum bool    IS4STATE   = L;
    enum bool    ISSIGNED   = S;
    enum         DIMENSIONS = N;

    alias opDollar = SIZE;

    alias T = _bvec!(S, L, N);

    alias this_type = typeof(this);
    
    enum size_t ELEMSIZE = N[$-1];

    template isAssignableBitVec(Q) {
      static if (isIntegral!Q && Q.sizeof*8 <= SIZE) {
	enum bool isAssignableBitVec = true;
      }
      else static if (isBitVector!Q && Q.SIZE <= SIZE) {
	static if (IS4STATE || (! Q.IS4STATE)) {
	  enum bool isAssignableBitVec = true;
	}
	else {
	  enum bool isAssignableBitVec = false;
	}
      }
      else {
	  enum bool isAssignableBitVec = true;
      }
    }
    
    static if(N.length > 1) {
      enum bool MULTIDIM = true;
      alias ELEMTYPE = _bvec!(S, L, N[0..$-1]);
    }
    else {
      enum bool MULTIDIM = false;
      alias ELEMTYPE = _bvec!(S, L, cast(size_t) 1);
    }

    // enum MIN = min();
    
    public static auto min() {
      alias _bvec!(S, L, N) _type;
      _type retval;
      static if(S) {
	retval = cast(_type) 1;
	return retval << (_type.SIZE - 1);
      }
      else {
	return retval;
      }
    }

    // enum MAX = max();
    
    public static auto max() {
      alias _bvec!(S, L, N) _type;
      _type retval;
      static if(S) {
	retval = 1;
	retval <<= (_type.SIZE - 1);
	return ~retval;
      }
      else {
	retval = 0;
	return ~retval;
      }
    }

    public static auto ones(size_t msb, size_t lsb=0) {
      import std.conv: to;

      assert(msb <= SIZE && lsb <= SIZE, "MSB is: " ~ msb.to!string);
      alias _bvec!(false, false, N) _type;
      _type a =(cast(_type) 1) << std.algorithm.max(msb, lsb);
      _type b =(cast(_type) 1) << std.algorithm.min(lsb, msb);
      a -= b;
      return a;
    }

    public static auto zeroes(size_t msb, size_t lsb=0) {
      return ~ones(msb, lsb);
    }

    static if(SIZE <= 64) {	// 32-bit size_t
      alias value_t = VecParams!(SIZE,S).ValueT;
      // enum min        = VecParams!(SIZE,S).MAX;
      // enum max        = VecParams!(SIZE,S).MIN;
    }

    // Value bits
    private store_t[STORESIZE] _aval;
    // Control bits
    static if(L) {
      private store_t[STORESIZE] _bval;
    }
    else {
      private enum store_t[STORESIZE] _bval = 0;
    }

    public ubyte getByte(size_t index) const {
      return (cast(ubyte*) _aval.ptr)[0..STORESIZE*store_t.sizeof][index];
    }
    
    public void setByte(size_t index, ubyte val) {
      (cast(ubyte*) _aval.ptr)[0..STORESIZE*store_t.sizeof][index] = val;
    }

    public auto aVal() {
      // http://d.puremagic.com/issues/show_bug.cgi?id=9143
      // _bvec!(S, false, N) retVal;
      _bvec!(S, false, N) retVal;
      retVal._aval[] = this._aval[];
      return retVal;
    }

    public auto bVal() {
      _bvec!(S, false, N) retVal;
      retVal._aval[] = this._bval[];
      return retVal;
    }

    // Primarily for the ease of constraint solver to set value
    void _setNthWord(T)(T v, int word = 0) if(isIntegral!T) {
      // make sure that we are not going over the boundary
      assert(word <= (SIZE-1)/(T.sizeof*8));
      static if (T.sizeof * 8 >= WORDSIZE) {
	enum scale = T.sizeof * 8 / WORDSIZE;
	for (size_t i=0; i != scale; ++i) {
	  if (word * scale + i < STORESIZE) {
	    _aval[word * scale + i] = cast(store_t) v;
	    _bval[word] = 0;
	    v >>= WORDSIZE;
	  }
	}
      }
      else {
	enum scale = WORDSIZE / (T.sizeof * 8);
	auto n = word / scale;
	auto m = word % scale;
	auto mask = 1LU << ((m+1) * WORDSIZE) - (1LU << m * WORDSIZE);
	ulong w = v;
	w <<= (1LU << m * WORDSIZE);
	_aval[n] &= ~mask;
	_aval[n] |= w;
	// bval
	_bval[n] = 0;
      }
      // if MSB word
      if(word == (SIZE-1)/(T.sizeof*8)) {
	if(aValMSB) this._aval[$-1] |= SMASK;
	else           this._aval[$-1] &= UMASK;
      }
    }

    public void setAval(V)(V t)
      if(isBoolean!V ||
	 (isIntegral!V && V.sizeof*8 <= SIZE) ||
	 (isBitVector!V && V.SIZE <= SIZE && (! V.IS4STATE))) {
	static if(isBoolean!V) enum bool _S = false;
	else static if(isBitVector!V) enum bool _S = V.ISSIGNED;
	  else enum bool _S = isSigned!V;
	_bvec!(_S, false, N) v = t;
	// http://d.puremagic.com/issues/show_bug.cgi?id=9143
	// _bvec!(S, false, N) retVal;
	this._aval = v._aval;
      }

    static if(L) {
      public void setBval(V)(V t)
	if(isBoolean!V ||
	   (isIntegral!V && V.sizeof*8 <= SIZE) ||
	   (isBitVector!V && V.SIZE <= SIZE && (! V.IS4STATE))) {
	  static if(isBoolean!V) enum bool _S = false;
	  else static if(isBitVector!V) enum bool _S = V.ISSIGNED;
	    else enum bool _S = isSigned!V;
	  _bvec!(_S, false, N) v = t;
	  // http://d.puremagic.com/issues/show_bug.cgi?id=9143
	  // _bvec!(S, false, N) retVal;
	  this._bval = v._aval;
	}
    }

    // some bits are X or Z
    alias isUnkown = isX;
    public bool isX() const {
      static if(L) {
	for (size_t i=0; i!=_bval.length-1; ++i) {
	  if(_bval[i] != 0) return true;
	}
	if((_bval[$-1] & UMASK) != 0) return true;
	return false;
      }
      else return false;
    }

    // returns true if all the logic bits are carrying Z
    @property public bool isZ() const {
     static if(L) {
       for (size_t i=0; i!= _bval.length-1; ++i) {
	 if(cast(store_t) (_bval[i]+1) != 0) return false;
	 if(_aval[i] != 0) return false;
       }
       if(cast(store_t) ((_bval[$-1] | SMASK)+1) != 0) return false;
       if((_aval[$-1] & UMASK) != 0) return false;
       return true;
     }
     else return false;
   }

    static if(SIZE >= 64) {
      public this(long other) {
    	this._from(other);
      }
      public void opAssign(long  other) {
    	this._from(other);
      }
    }

    else static if(SIZE >= 32) {
      public this(int other) {
    	this._from(other);
      }
      public void opAssign(int  other) {
    	this._from(other);
      }
    }

    else static if(SIZE >= 16) {
      public this(short other) {
    	this._from(other);
      }
      public void opAssign(short other) {
    	this._from(other);
      }
    }

    else static if(SIZE >= 8) {
      public this(byte other) {
	this._from(other);
      }
      public void opAssign(byte other) {
	this._from(other);
      }
    }


    public void opAssign(V)(V other)
      if(isIntegral!V && (NO_CHECK_SIZE || SIZE >= V.sizeof*8)) {
	this._from(other);
      }

    public void opAssign(V)(V other)
      if((isBitVector!V ||
	  is(V == _bvec!(_S, _L, _VAL, _RADIX),
	     bool _S, bool _L, string _VAL, size_t _RADIX))
	 && (NO_CHECK_SIZE || SIZE >= V.SIZE)
	 &&(IS4STATE || !V.IS4STATE)) {
	this._from(other);
      }

    public void opAssign(V)(V other)
      if((is(V: SignalObj!VV, VV) || is(V: HdlSignal!VV, VV) ||
	  is(V: HdlSignalObj!VV, VV) || is(V: Signal!VV, VV)) &&
	 isAssignable!(typeof(this), V.VAL_TYPE)) {
	this._from(other.read());
      }

    public this(V)(V other)
      if((isBitVector!V ||
	  is(V == _bvec!(S_, L_, _VAL, _RADIX),
	     bool S_, bool L_, string _VAL, size_t _RADIX)) &&
	 (NO_CHECK_SIZE || SIZE >= V.SIZE)) {
	this._from(other);
      }

    public this(bool other) {
      this._from(other);
    }

    public  this(V)(V other)
      if(isIntegral!V && (NO_CHECK_SIZE || SIZE >= V.sizeof*8)) {
	this._from(other);
      }

    // TBD
    // public BitVec!N toBitVec(size_t N)() {
    // }
    
    // public this(V)(V other)
    //   if(isFloatingPoint!V &&
    // 	 SIZE >= V.sizeof*8) {
    // 	this._from(other);
    //   }

    // public this(V)(V other)
    //   if(is(V == SimTime)) {
    // 	this._from(other);
    //   }

    // public this(V)(V other)
    //   if(is(V == SimTime)) {
    // 	this._from(other);
    //   }

    public this(V)(V ba) if(is(V == barray)) {
      this = ba;
    }

    public this(V)(V [] bits) if(isBoolean!V) {
      this = bits;
    }

    // declare this aliases -- only if SIZE <= 64
    static if(SIZE <= 64 && !L) {
      static if(SIZE <= WORDSIZE) { // 32-bit size_t
    	static assert(STORESIZE == 1);
      }
      else {
    	static assert(STORESIZE == 2);
      }
      static if(SIZE == 1) {
    	public bool getValue() const {
    	  bool value =(this._aval[0] & 1);
    	  static if(L) {
    	    value &= cast(bool) ~(this._bval[0] & 1); // makes X/Z as 0
    	  }
    	  return value;
    	}
      }
      else {
    	public value_t getValue() const {
    	  value_t value = this._aval[0];
    	  // static if(L) {
    	  //   value &= ~(this._bval[0]); // makes X/Z as 0
    	  // }
    	  static if(SIZE > WORDSIZE) { // 32-bit machines
    	    value_t value32 = this._aval[1];
    	    // static if(L) {
    	    //   value32 &= ~(this._bval[1]);
    	    // }
    	    value |= (value32 << WORDSIZE);
    	  }
    	  // asserts to make sure that sign extension is proper
    	  // static if(S && SIZE < value_t.sizeof*8) {
    	  //   if((value >> (SIZE-1)) & 1) { // negative
    	  //     // make sure that the returned value is sign extended
    	  //     import std.string;
    	  //     assert(isSigned!value_t);
    	  //     assert((value >> SIZE) == -1,
    	  // 	     format("value is %d, %b, %s", value, value, typeid(value_t))); // ">>" is sign-extending shift
    	  //   }
    	  // }
    	  // else
    	  //   static if(SIZE < value_t.sizeof*8) {
    	  //     assert((value >> SIZE) == 0);
    	  //   }
    	  return value;
    	}
      }
      alias getValue this;
    }
    // else {
    //   static if(ISSIGNED) {
    // 	_bvec!(false, IS4STATE, SIZE) getSigned() {
    // 	  auto val = cast(_bvec!(false, IS4STATE, SIZE)) this;
    // 	  return val;
    // 	}
    // 	alias getSigned this;
    //   }
    //   static if(! ISSIGNED) {
    // 	_bvec!(true, IS4STATE, SIZE) getSigned() {
    // 	  auto val = cast(_bvec!(true, IS4STATE, SIZE)) this;
    // 	  return val;
    // 	}
    // 	alias getSigned this;
    //   }
    // }

    // declare this aliases -- only if SIZE <= 64
    // static if(SIZE <= 64 && !L) {
    //   static if(SIZE <= size_t.sizeof*8) { // 32-bit size_t
    // 	static assert(STORESIZE == 1);
    //   }
    //   else {
    // 	static assert(STORESIZE == 2);
    //   }
    //   static if(SIZE == 1) {
    // 	public bool getValue() {
    // 	  bool value =(this._aval[0] & 1);
    // 	  static if(L) {
    // 	    value &= cast(bool) ~(this._bval[0] & 1); // makes X/Z as 0
    // 	  }
    // 	  return value;
    // 	}
    //   }
    //   else {
    // 	public value_t getValue() {
    // 	  value_t value = this._aval[0];
    // 	  static if(L) {
    // 	    value &= ~(this._bval[0]); // makes X/Z as 0
    // 	  }
    // 	  static if(SIZE > size_t.sizeof*8) { // 32-bit machines
    // 	    value_t value32 = this._aval[1];
    // 	    static if(L) {
    // 	      value32 &= ~(this._bval[1]);
    // 	    }
    // 	    value |= (value32 << 32);
    // 	  }
    // 	  // asserts to make sure that sign extension is proper
    // 	  // static if(S && SIZE < value_t.sizeof*8) {
    // 	  //   if((value >> (SIZE-1)) & 1) { // negative
    // 	  //     // make sure that the returned value is sign extended
    // 	  //     import std.string;
    // 	  //     assert(isSigned!value_t);
    // 	  //     assert((value >> SIZE) == -1,
    // 	  // 	     format("value is %d, %b, %s", value, value, typeid(value_t))); // ">>" is sign-extending shift
    // 	  //   }
    // 	  // }
    // 	  // else
    // 	  //   static if(SIZE < value_t.sizeof*8) {
    // 	  //     assert((value >> SIZE) == 0);
    // 	  //   }
    // 	  return value;
    // 	}
    //   }
    //   alias getValue this;
    // }

    public void randomize() {
      import std.random;
      for(size_t i=0; i!=STORESIZE; ++i) {
	this._aval[i] = uniform!store_t();
	static if(L) this._bval[i] = 0;
      }
      if(aValMSB) this._aval[$-1] |= SMASK;
      else           this._aval[$-1] &= UMASK;
      static if(L) {
	if(bValMSB) this._bval[$-1] |= SMASK;
	else           this._bval[$-1] &= UMASK;
      }
    }

    public void randomize(URNG)(ref URNG urng) {
      import std.random;
      for(size_t i=0; i!=STORESIZE; ++i) {
	this._aval[i] = uniform!store_t(urng);
	static if(L) this._bval[i] = 0;
      }
      if(aValMSB) this._aval[$-1] |= SMASK;
      else           this._aval[$-1] &= UMASK;
      static if(L) {
	if(bValMSB) this._bval[$-1] |= SMASK;
	else           this._bval[$-1] &= UMASK;
      }
    }

    public bool aValMSB() const {
      static if(S) {
	if((this._aval[$-1] &
	    (cast(store_t) 1) << ((SIZE-1) % WORDSIZE)))
	  return true;
	else
	  return false;
      }
      else
	return false;
    }

    static if(L) {
      public bool bValMSB() const {
	static if(S) {
	  if((this._bval[$-1] &
	      (cast(store_t) 1) << ((SIZE-1) % WORDSIZE)))
	    return true;
	  else
	    return false;
	}
	else
	  return false;
      }
    }


    public void storeString(V)(V other)
      if(is(V == string)) {
	foreach(ref a; _aval) a = 0;
	static if(L) foreach(ref b; _bval) b = 0;
	foreach(size_t i, char c; other) {
	  auto j = i / store_t.sizeof;
	  auto k = i % store_t.sizeof;
	  if(j < STORESIZE) {
	    import std.traits;
	    _aval[j] |=(cast(Unsigned!store_t) c) << k*8;
	  }
	}
	if(aValMSB) this._aval[$-1] |= SMASK;
	else           this._aval[$-1] &= UMASK;
	static if(L) {
	  if(bValMSB) this._bval[$-1] |= SMASK;
	  else           this._bval[$-1] &= UMASK;
	}
      }


    private void _from(V)(V other)
      if(isIntegral!V) {
	static if(isSigned!V) long rhs = other;
	else                  ulong rhs = other;
	_aval[0] = cast(store_t) rhs;
	static if(L) _bval[0] = 0;
	static if(STORESIZE > 1) {
	  for(size_t i=1; i != STORESIZE; ++i) {
	    rhs >>= store_t.sizeof*8; // '>>' is sign-extending shift
	    _aval[i] = cast(store_t) rhs;
	    static if(L) _bval[i] = 0;
	  }
	}
	// In case the vector is not signed, mask the extended sign bits if eny
	static if(!S && STORESIZE*store_t.sizeof*8 > SIZE) {
	  _aval[$-1] &= UMASK;
	  static if(L) _bval[$-1] &= UMASK;
	}
      }

    // public void opAssign(V)(V other)
    //   if(isBoolean!V)
    //	{
    //	  this._from(other);
    //	}

    public void opAssign(bool other) {
      this._from(other);
    }

    private void _from(V)(V other)
      if(isBoolean!V) {
	_aval[0] = cast(store_t) other;
	static if(L) _bval[0] = 0;
	static if(STORESIZE > 1) {
	  for(size_t i=1; i != STORESIZE; ++i) {
	    _aval[i] = 0;
	    static if(L) _bval[i] = 0;
	  }
	}
      }

    // public void opAssign(V)(V other)
    //   if(isFloatingPoint!V &&
    // 	 SIZE >= V.sizeof*8) {
    // 	this._from(other);
    //   }

    // public void opAssign(V)(V other)
    //   if(is(V == SimTime) &&
    // 	 SIZE >= 72) {
    // 	this._from(other);
    //   }

    // public void opAssign(V)(V other)
    //   if(is(V == SimTime) &&
    // 	 SIZE >= 64) {
    // 	this._from(other);
    //   }

    // private void _from(V)(V other)
    //   if(is(V == SimTime) &&
    // 	 SIZE >= 72) {
    // 	for(size_t i=0; i!=STORESIZE; ++i) {
    // 	  _aval[i] = 0;
    // 	  static if(L) _bval[i] = 0;
    // 	}

    // 	this._aval[0] = other._value;
    // 	this._aval[1] = other._unit;
    //   }

    // private void _from(V)(V other)
    //   if(is(V == SimTime) &&
    // 	 SIZE >= 64) {
    // 	for(size_t i=0; i!=STORESIZE; ++i) {
    // 	  _aval[i] = 0;
    // 	  static if(L) _bval[i] = 0;
    // 	}

    // 	this._aval[0] = other.getVal();
    //   }

    private void _from(V)(V other)
      if(isBitVector!V ||
	 is(V == _bvec!(_S, _L, _VAL, _RADIX), bool _S, bool _L, string _VAL, size_t _RADIX)) {
	static assert(NO_CHECK_SIZE || SIZE >= V.SIZE);
	static assert(IS4STATE || !V.IS4STATE,
		      "Can not implicitly convert LogicVec to BitVec");
	enum bool _L = V.IS4STATE;
	for(size_t i=0; i != V.STORESIZE; ++i) {
	  this._aval[i] = cast(store_t) other._aval[i];
	  static if(L) {
	    static if(_L) this._bval[i] =
			    cast(store_t) other._bval[i];
	    else           this._bval[i] = 0;
	  }
	}
	for(size_t i=V.STORESIZE; i != STORESIZE; ++i) {
	  // if RHS is signed, extend its sign
	  if(other.aValMSB && ISSIGNED) this._aval[i] = cast(store_t) -1;
	  else                  this._aval[i] = 0;
	  static if(L) {
	    static if(_L) {
	      if(other.bValMSB && ISSIGNED) this._bval[i] = cast(store_t) -1;
	      else                  this._bval[i] = 0;
	    }
	    else {
	      this._bval[i] = 0;
	    }
	  }
	}
	if(aValMSB && ISSIGNED) this._aval[$-1] |= SMASK;
	else           this._aval[$-1] &= UMASK;
	static if(L) {
	  if(bValMSB && ISSIGNED) this._bval[$-1] |= SMASK;
	  else           this._bval[$-1] &= UMASK;
	}
      }

    public void opAssign(s_vpi_vecval[] other) {
      this._from(other);
    }

    private void _from() (s_vpi_vecval[] other) {
      // static if(WORDSIZE is 64) {
      // 	for (size_t i=0; i!=(SIZE+31)/32; ++i) {
      // 	  if(i < other.length) {
      // 	    ulong word = other[i].aval;
      // 	    if(i%2 == 0) this._aval[i/2] = word;
      // 	    else this._aval[i/2] |= word << 32;
      // 	  }
      // 	  else {
      // 	    if(i%2 == 0) this._aval[i/2] = 0;
      // 	  }
      // 	  static if(IS4STATE) {
      // 	    if(i < other.length) {
      // 	      ulong cword = other[i].bval;
      // 	      if(i%2 == 0) this._bval[i/2] = cword;
      // 	      else this._bval[i/2] |= cword << 32;
      // 	    }
      // 	    else {
      // 	      if(i%2 == 0) this._bval[i/2] = 0;
      // 	    }
      // 	  }
      // 	}
      // }
      static if(WORDSIZE is 32) {
	for (size_t i=0; i!=(SIZE+31)/32; ++i) {
	  this._aval[i] = other[i].aval;
	  static if(IS4STATE) {
	    this._bval[i] = other[i].bval;
	  }
	}
      }
      else {
	this._aval[0] = cast(store_t) other[0].aval;
	static if(IS4STATE) {
	  this._bval[0] = cast(store_t) other[0].bval;
	}
      }
    }

    // It is the responsibility of the caller to make sure that
    // there is enough space available at other to write down the
    // required bits
    public void toVpiVecValue(s_vpi_vecval[] other) {
      this._to(other);
    }
      
    private void _to() (s_vpi_vecval[] other) {
      assert(other.length >= (SIZE+31)/32);
      // static if(WORDSIZE is 64) {
      // 	for (size_t i=0; i!=(SIZE+31)/32; ++i) {
      // 	  if(i%2 == 0) other[i].aval = cast(uint) this._aval[i/2];
      // 	  else other[i].aval = cast(uint) (this._aval[i/2] >>> 32);
      // 	  static if(IS4STATE) {
      // 	    if(i%2 == 0) other[i].bval = cast(uint) this._bval[i/2];
      // 	    else other[i].bval = cast(uint) (this._bval[i/2] >>> 32);
      // 	  }
      // 	}
      // }
      // else
      static if(WORDSIZE is 32) {
	for (size_t i=0; i!=(SIZE+31)/32; ++i) {
	  other[i].aval = this._aval[i];
	  static if(IS4STATE) {
	    other[i].bval = this._bval[i];
	  }
	}
      }
      else {
	other[0].aval = this._aval[0];
	static if(IS4STATE) {
	  other[0].bval = this._bval[0];
	}
      }
    }

    public void opAssign(V)(V ba) if(is(V == barray)) {
      auto numBits = ba.length;
      if(numBits > SIZE) {
	writeln("Warning: truncating barray to fit into BitVec");
      }
      auto bavoid = cast(void[]) ba;
      // number of bytes to be copied from barray
      // auto numBytes =(ba.length + ubyte.sizeof - 1)/ubyte.sizeof;
      auto baptr = cast(ubyte*) bavoid.ptr;
      auto babytes = baptr[0..(bavoid.length * void.sizeof)];
      // auto babytes = baptr[0..(numBytes * void.sizeof)];

      auto bvptr = cast(ubyte*) _aval.ptr;
      auto bvbytes = bvptr[0..STORESIZE*store_t.sizeof/ubyte.sizeof];
      for(size_t i = 0; i != bvbytes.length; ++i) {
	if(i < babytes.length) bvbytes[i] = babytes[i];
	else bvbytes[i] = 0;
      }
    }

    public void opAssign(V)(V [] bits) if(isBoolean!V) {
      static if(bits.length > SIZE) {
	writeln("Warning: truncating array of bool to fit into BitVec");
      }
      for(size_t i=0; i != STORESIZE; ++i) {
	if(i < bits.length) {
	  this[i] = bits[i];
	}
	else {
	  this[i] = false;
	}
      }
    }

    V to(V, size_t RADIX = 2)() if((is(V == string) ||
				    is(V == char[]))
				   &&(RADIX == 2 ||
				      RADIX == 8 ||
				      RADIX == 16)) {
      static if(RADIX == 8) {
	return logicToOctal(this.to!(V, 2));
      }
      else {
	return toCharString!(V, RADIX);
      }
    }

    string toString()() {
      return this.to!(string, 2);
    }

    void toString(scope void delegate(const(char)[]) sink, FormatSpec!char f) {
      char[] buff;
      switch(f.spec) {
      case 'd'     : buff = this.toDecimalString(); break;
      case 's'     :		// should print as hex when %s
      case 'h'     :		// should print as hex for %h too
      case 'x'     : buff = toLower(this.to!(char[], 16)); break;
      case 'H'     :		// should print as HEX for %H
      case 'X'     : buff = this.to!(char[], 16); break;
      case 'o'     : buff = this.to!(char[], 8); break;
      case 'b'     : buff = this.to!(char[], 2); break;
      default      :
	throw new FormatException("Format specifier not understood: %" ~ f.spec);
      }

      assert(buff.length > 0);

      sink(buff);
    }

    private V toCharString(V, size_t RADIX)() {
      char[] str;
      if(STORESIZE > 1) {
	for(size_t i = 0; i != STORESIZE-1; ++i) {
	  import std.string;
	  static if(RADIX == 2)  string fmtstr = "%b";
	  static if(RADIX == 8)  string fmtstr = "%o";
	  static if(RADIX == 16) string fmtstr = "%X";
	  char[] wstr;
	  string astr =
	    rightJustify(format(fmtstr, _aval[i]),
			 cast(int)((_log2(RADIX) - 1) +
				   8*store_t.sizeof)/_log2(RADIX), '0');
	  static if(L) {
	    string zstr =
	      rightJustify(format(fmtstr, _bval[i]),
			   cast(int)((_log2(RADIX) - 1) +
				     8*store_t.sizeof)/_log2(RADIX), '0');
	    string xstr =
	      rightJustify(format(fmtstr,(cast(store_t)
					  (_aval[i] & _bval[i]))),
			   cast(int)((_log2(RADIX) - 1) +
				     8*store_t.sizeof)/_log2(RADIX), '0');
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
      auto foo = cast(store_t)(_aval[$-1] & UMASK);
      static if(RADIX == 16) string fmtstr = "%X";
      static if(RADIX == 8)  string fmtstr = "%o";
      static if(RADIX == 2)  string fmtstr = "%b";

      import std.string;
      string astr =
	rightJustify(format(fmtstr, cast(store_t)(_aval[$-1] & UMASK)),
		     cast(int)((_log2(RADIX) - 1) +
			       ((SIZE-1)%(8*store_t.sizeof) + 1))
		     /_log2(RADIX), '0');
      static if(L) {
	string zstr =
	  rightJustify(format(fmtstr, cast(store_t)(_bval[$-1] & UMASK)),
		       cast(int)((_log2(RADIX) - 1) +
				 ((SIZE-1)%(8*store_t.sizeof) + 1))
		       /_log2(RADIX), '0');
	string xstr =
	  rightJustify(format(fmtstr, cast(store_t)(_aval[$-1] &
						    _bval[$-1] & UMASK)),
		       cast(int)((_log2(RADIX) - 1) +
				 ((SIZE-1)%(8*store_t.sizeof) + 1))
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
      return cast(V) str;
    }

    char [] toDecimalString() const {
      static if(STORESIZE == 1) {
	auto val = this._aval[0];
	string str = format("%d", val);
	char[] buff;
	foreach(c; str) buff ~= c;
	return buff;
      }
      else {
	uint[] data =(cast(uint[]) this._aval).dup;
	auto predictlength = 20+20*(data.length/2); // just over 19
	char [] buff = new char[predictlength];
	size_t sofar = biguintToDecimal(buff, data.dup);
	return buff[sofar..$];
      }
    }

    auto opIndex(size_t i) const
      in {
	assert(i < SIZE);
      }
    body {
      _bvec!(false, L, cast(size_t) 1) retval;
      static if(STORESIZE == 1) {
	retval._aval[0] = cast(ubyte)((this._aval[0] >>> i) & 1LU);
	static if(L) {
	  retval._bval[0] = cast(ubyte)((this._bval[0] >>> i) & 1LU);
	}
      }
      else {
	retval._aval[0] = cast(ubyte)((this._aval[i/WORDSIZE] >>> (i % WORDSIZE)) & 1U);
	static if(L) {
	  retval._bval[0] = cast(ubyte)((this._bval[i/WORDSIZE] >>> (i % WORDSIZE)) & 1U);
	}
      }
      // else {
      // 	retval._aval[0] = cast(ubyte) bt(cast(const(size_t*)) this._aval.ptr, i);
      // 	static if(L) {
      // 	  retval._bval[0] = cast(ubyte) bt(cast(const(size_t*)) this._bval.ptr, i);
      // 	}
      // }
      return retval;
    }

    unittest {
      void Fun(const BitVec!3 arr) {
	auto x = arr[0];
	assert(x == 1);
      }
      BitVec!3 a;
      a[0] = 1;
      Fun(a);
    }

    bool opIndexAssign(bool b, size_t i)
      in {
	assert(i < SIZE);
      }
    body {
      static if(STORESIZE == 1) {
	if(b) this._aval[0] |= (1LU << i);
	else   this._aval[0] &= ~(1LU << i);
	static if(L) {
	  this._bval[0] &= ~(1LU << i);
	}
      }
      else {
	if(b) this._aval[i/WORDSIZE] |= (1LU << (i % WORDSIZE));
	else   this._aval[i/WORDSIZE] &= ~(1LU << (i % WORDSIZE));
	static if(L) {
	  this._bval[i/WORDSIZE] &= ~(1LU << (i % WORDSIZE));
	}
      }
      // else {
      // 	if(b) bts((cast(size_t*) _aval.ptr), i);
      // 	else   btr((cast(size_t*) _aval.ptr), i);
      // 	static if(L) {
      // 	  btr((cast(size_t*) _bval.ptr), i);
      // 	}
      // }
      return b;
    }

    auto opIndexAssign(V)(V other, size_t i)
      if(isBitVector!V && V.SIZE == 1)
	in {
	  assert(i < SIZE);
	}
    body {
      static if(STORESIZE == 1) {
	static if(other.IS4STATE) {
	  static if(L) {
	    if(other.aVal) this._aval[0] |=(1L << i);
	    else this._aval[0] &= ~(1L << i);
	    if(other.bVal) this._bval[0] |=(1L << i);
	    else this._bval[0] &= ~(1L << i);
	  }
	  else {
	    if(other.aVal && !(other.bVal)) this._aval[0] |=(1L << i);
	    else this._aval[0] &= ~(1L << i);
	  }
	}
	else {
	  if(other.aVal)
	    this._aval[0] |=(1L << i);
	  else this._aval[0] &= ~(1L << i);
	  static if(L) {
	    this._bval[0] &= ~(1L << i);
	  }
	}
      }
      else {
	auto i_ = i % WORDSIZE;
	auto j_ = i / WORDSIZE;
	static if(other.IS4STATE) {
	  static if(L) {
	    if(other.aVal) this._aval[j_] |=(1L << i_);
	    else this._aval[j_] &= ~(1L << i_);
	    if(other.bVal) this._bval[j_] |=(1L << i_);
	    else this._bval[j_] &= ~(1L << i_);
	  }
	  else {
	    if(other.aVal && !(other.bVal)) this._aval[j_] |=(1L << i_);
	    else this._aval[j_] &= ~(1L << i_);
	  }
	}
	else {
	  if(other.aVal)
	    this._aval[j_] |=(1L << i_);
	  else this._aval[j_] &= ~(1L << i_);
	  static if(L) {
	    this._bval[j_] &= ~(1L << i_);
	  }
	}
      }
      // else {
      // 	static if(other.IS4STATE) {
      // 	  static if(L) {
      // 	    if(other.aVal) bts((cast(size_t*) _aval.ptr), i);
      // 	    else btr((cast(size_t*) _aval.ptr), i);
      // 	    if(other.bVal) bts((cast(size_t*) _bval.ptr), i);
      // 	    else btr((cast(size_t*) _bval.ptr), i);
      // 	  }
      // 	  else {
      // 	    if(other.aVal && !(other.bVal)) bts((cast(size_t*) _aval.ptr), i);
      // 	    else btr((cast(size_t*) _aval.ptr), i);
      // 	  }
      // 	}
      // 	else {
      // 	  if(other.aVal) bts((cast(size_t*) _aval.ptr), i);
      // 	  else btr((cast(size_t*) _aval.ptr), i);
      // 	  static if(L) {
      // 	    btr((cast(size_t*) _bval.ptr), i);
      // 	  }
      // 	}
      // }
      return other;
    }

    public auto opBinary(string op, V)(V other) const if(isIntegral!V) {
      return this.opBinary!op(other.toBitVec());
    }

    // public auto opBinaryRight(string op, V)(V other) const if(isIntegral!V) {
    //   return this.opBinaryRight!op(other.toBitVec());
    // }

    // And/Or/Xor
    public auto opBinary(string op, V)(V other) const if(isBitVector!V &&
						   (op == "&" ||
						    op == "|" ||
						    op == "^")) {
	_bvec!(typeof(this), V, op) result = this;
	result.opOpAssign!op(other);
	return result;
      }

    // And/Or/Xor Assign
    public void opOpAssign(string op, V)(V other)
      if(isIntegral!V &&
	 (op == "&" || op == "|" || op == "^")) {
	_bvec!V rhs = other;
	this.opOpAssign!op(rhs);
      }

    public void opOpAssign(string op, V)(V other)
      if(isBitVector!V &&
	 (op == "&" || op == "|" || op == "^")) {
	enum bool _S = V.ISSIGNED;
	enum bool _L = V.IS4STATE;
	auto rhs = cast(_bvec!(_S, _L, SIZE)) other;
	for(size_t i=0; i!=STORESIZE; ++i) {
	  static if(L) {
	    static if(_L) {
	      static if(op == "|") {
		auto a =
		  this._aval[i] | rhs._aval[i] |
		  rhs._bval[i] | this._bval[i];
		auto b =
		  (~rhs._aval[i] &  this._bval[i]) |
		  ( rhs._bval[i] & ~this._aval[i]) |
		  ( rhs._bval[i] &  this._bval[i]);
		this._aval[i] = cast(store_t) a;
		this._bval[i] = cast(store_t) b;
	      }
	      static if(op == "&") {
		auto a =
		  ( rhs._aval[i] | rhs._bval[i]) &
		  (  this._aval[i] |  this._bval[i]);
		auto b =
		  (this._aval[i] | this._bval[i]) &
		  (rhs._aval[i] | rhs._bval[i]) &
		  (this._bval[i] | rhs._bval[i]);
		this._aval[i] = cast(store_t) a;
		this._bval[i] = cast(store_t) b;
	      }
	      static if(op == "^") {
		auto a =
		  this._bval[i] | rhs._bval[i];
		auto b =
		  (this._aval[i] ^ rhs._aval[i]) |
		  this._bval[i];
		this._aval[i] = cast(store_t) a;
		this._bval[i] = cast(store_t) b;
	      }
	    }
	    else {
	      static if(op == "|") {
		auto a =
		  this._aval[i] | rhs._aval[i] | this._bval[i];
		auto b =
		  (~rhs._aval[i] &  this._bval[i]);
		this._aval[i] = cast(store_t) a;
		this._bval[i] = cast(store_t) b;
	      }
	      static if(op == "&") {
		auto a =
		  rhs._aval[i] & (this._aval[i] |  this._bval[i]);
		auto b =
		  this._aval[i] & this._bval[i];
		this._aval[i] = cast(store_t) a;
		this._bval[i] = cast(store_t) b;
	      }
	      static if(op == "^") {
		auto a =
		  (this._aval[i] ^ rhs._aval[i]) |
		  this._bval[i];
		this._aval[i] = cast(store_t) a;
	      }
	    }
	  }
	  else {			// L is false
	    static if(_L) {
	      static if(op == "|") {
		auto a = 
		  (this._aval[i] | (rhs._aval[i] & ~rhs._bval[i]));
		this._aval[i] = cast(store_t) a;
	      }
	      static if(op == "&") {
		auto a =
		  (rhs._aval[i] & this._aval[i] & ~rhs._bval[i]);
		this._aval[i] = cast(store_t) a;
	      }
	      static if(op == "^") {
		auto a =
		((this._aval[i] ^ rhs._aval[i]) & ~rhs._bval[i]);
		this._aval[i] = cast(store_t) a;
	      }
	    }
	    else {
	      static if(op == "|") {
		auto a =
		  (this._aval[i] | rhs._aval[i]);
		this._aval[i] = cast(store_t) a;
	      }
	      static if(op == "&") {
		auto a =
		  (rhs._aval[i] & this._aval[i]);
		this._aval[i] = cast(store_t) a;
	      }
	      static if(op == "^") {
		auto a =
		  (this._aval[i] ^ rhs._aval[i]);
		this._aval[i] = cast(store_t) a;
	      }
	    }
	  }
	  if(this.aValMSB) this._aval[$-1] |= SMASK;
	  else                this._aval[$-1] &= UMASK;
	  static if(L) {
	    if(this.bValMSB) this._bval[$-1] |= SMASK;
	    else                this._bval[$-1] &= UMASK;
	  }
	}
      }


    // mask out(make 0) the bits that are 1 in the argument
    public void maskOut(V)(V other)
      if(isBitVector!V
	 && !V.IS4STATE && !V.ISSIGNED) {
	auto rhs = cast(UBitVec!SIZE) other;
	for(size_t i=0; i!=STORESIZE; ++i) {
	  this._aval[i] &= ~rhs._aval[i];
	  static if(L) {
	    this._bval[i] &= ~rhs._aval[i];
	  }
	  if(this.aValMSB) this._aval[$-1] |= SMASK;
	  else                this._aval[$-1] &= UMASK;
	  static if(L) {
	    if(this.bValMSB) this._bval[$-1] |= SMASK;
	    else                this._bval[$-1] &= UMASK;
	  }
	}
      }

    // Copy all the bits that are not 0 in the argument -- assume that the
    // mask out has already taken place
    public void maskIn(V)(V other)
      if(isBitVector!V && (!V.IS4STATE ||(V.IS4STATE && IS4STATE))) {
	auto rhs = cast(_bvec!(false, V.IS4STATE, SIZE)) other;
	for(size_t i=0; i!=STORESIZE; ++i) {
	  this._aval[i] |= rhs._aval[i];
	  static if(V.IS4STATE && IS4STATE) {
	    this._bval[i] |= rhs._bval[i];
	  }
	  if(this.aValMSB) this._aval[$-1] |= SMASK;
	  else                this._aval[$-1] &= UMASK;
	  static if(L) {
	    if(this.bValMSB) this._bval[$-1] |= SMASK;
	    else                this._bval[$-1] &= UMASK;
	  }
	}
      }

    void opSliceAssign(V)(V other, size_t i, size_t j)
      if(isBitVector!V ||
	 isIntegral!V)
        {
	  import std.algorithm;
	  import std.exception;
	  static if(isIntegral!V)
	    {
	      alias _bvec!V _type;
	      _type rhs = other;
	    }
	  else
	    {
	      alias V _type;
	      alias other rhs;
	    }

	  enforce(i <= SIZE && j <= SIZE,
		  "Slice operands may not be negative");
	  enforce(std.algorithm.max(i,j) -
		  std.algorithm.min(i,j) == _type.SIZE,
		  "Slice size does not match with the RHS");
	  if(i < j)		// bigendian
	    {
	      this.put(i, j, rhs);
	    }
	  else
	    {
	      this.put(j, i, rhs.reverse);
	    }
        }

    V opCast(V)() if(is(V == barray)) {
      barray ba;

      // Since dup method creates a dynamic array, hopefully the
      // memory is allocate on the heap
      // store_t[STORESIZE] bav = _aval.dup;

      // for(size_t i=0; i != STORESIZE; ++i) {
      //	writeln("dup: ", bav[i], ":", _aval[i]);
      // }

      ba.init(_aval.dup, SIZE);
      return ba;
    }

    public V opCast(V)() const if(isIntegral!V || isBoolean!V) {
      static if(L) {
	static if (store_t.sizeof >= 4) {
	  V value = cast(V)(this._aval[0] & ~this._bval[0]);
	}
	else {
	  V value = cast(V)(this._aval[0] & ~(cast(int) this._bval[0]));
	}
      }
      else {
	V value = cast(V) this._aval[0];
      }
      return value;
    }

    // public V opCast(V)()
    //   if(is(V == SimTime) &&
    // 	 SIZE >= 72) {
    // 	SimTime retval;
    // 	retval._value = _aval[0];
    // 	retval._unit  = cast(TimeUnit) _aval[1];
    // 	return retval;
    //   }

    // public V opCast(V)()
    //   if(is(V == SimTime) &&
    // 	 SIZE >= 64) {
    // 	SimTime retval = _aval[0];
    // 	return retval;
    //   }

    // public V opCast(V)()
    //   if(isFloatingPoint!V &&
    // 	 V.sizeof*8 <= SIZE) {
    // 	static if(is(V == real)) {
    // 	  enum WSIZE =(V.sizeof+7)/8;
    // 	  alias ulong ftype;
    // 	}
    // 	static if(is(V == double)) {
    // 	  enum WSIZE = 1;
    // 	  alias ulong ftype;
    // 	}
    // 	static if(is(V == float)) {
    // 	  enum WSIZE = 1;
    // 	  alias uint ftype;
    // 	}

    // 	union utype {
    // 	  ftype[WSIZE] b;
    // 	  V f;
    // 	}

    // 	utype u;

    // 	for(size_t i=0; i!=WSIZE; ++i) {
    // 	  u.b[i] = cast(ftype) _aval[i];
    // 	}

    // 	return	u.f;
    //   }

    public auto opCast(V)() const
      if(isBitVector!V) {
	enum bool _L = V.IS4STATE;
	enum bool _S = V.ISSIGNED;
	alias R = makeMutable!V;
	R result;
	static if(V.STORESIZE <= STORESIZE) {
	  for(size_t i=0; i != V.STORESIZE; ++i) {
	    result._aval[i] = cast(V.store_t) this._aval[i];
	    static if(_L) {
	      static if(L) result._bval[i] =
			     cast(V.store_t) this._bval[i];
	      else          result._bval[i] = 0;
	    }
	    else {
	      // X and Z values reduce to 0
	      static if (V.store_t.sizeof >= 4) {
		static if(L) result._aval[i] &=
			       ~(cast(V.store_t) this._bval[i]);
	      }
	      else {
		static if(L) result._aval[i] &=
			       cast(V.store_t) ~(cast(int) this._bval[i]);
	      }
	    }
	  }
	  // sign extension
	  if(result.aValMSB) result._aval[$-1] |= V.SMASK;
	  else                  result._aval[$-1] &= V.UMASK;
	  static if(_L) {
	    if(result.bValMSB) result._bval[$-1] |= V.SMASK;
	    else                  result._bval[$-1] &= V.UMASK;
	  }
	}
	static if(V.STORESIZE > STORESIZE) {
	  for(size_t i=0; i != STORESIZE; ++i) {
	    result._aval[i] = cast(V.store_t) this._aval[i];
	    static if(_L) {
	      static if(L) result._bval[i] =
			     cast(V.store_t) this._bval[i];
	      else          result._bval[i] = 0;
	    }
	    else {
	      // X and Z values reduce to 0
	      static if(L) result._aval[i] &=
			     ~(cast(V.store_t) this._bval[i]);
	    }
	  }
	  for(size_t i=STORESIZE; i != V.STORESIZE; ++i) {
	    // if RHS is signed, extend its sign
	    if(this.aValMSB) result._aval[i] = -1;
	    else                 result._aval[i] = 0;
	    static if(_L) {
	      static if(L) {
		if(this.bValMSB) result._bval[i] = -1;
		else                 result._bval[i] = 0;
	      }
	      else {
		result._bval[i] = 0;
	      }
	    }
	    else {
	      static if(L)		// X/Z reduce to 0
		if(this.bValMSB) result._aval[i] = 0;
	    }
	  }
	  static if(!_S) {		// If result is not signed
	    result._aval[$-1] &= V.UMASK;
	    static if(_L) {
	      result._bval[$-1] &= V.UMASK;
	    }
	  }
	}
	return result;
      }

    public string retrieveString() {
      string retval;
      foreach(w; _aval) {
	for(size_t i = 0; i != store_t.sizeof; ++i) {
	  if(w == 0) goto done;
	  retval ~= cast(char) w;
	  w >>= 8;
	}
      }
    done: return retval;
    }

    size_t length() const {
      return SIZE;
    }

    // V opCast(V)() if(isIntegral!V) {
    //   V res = cast(V) _aval[0];
    //   return res;
    // }


    // string toString()
    //   {
    //     static if(STORESIZE == 1 && isIntegral!(typeof(_aval[0])))
    //	{
    //	  // We need to use the global to!string, and therefor the '.'
    //	  return .to!string(_aval[0], 2);
    //	}
    //     else
    //	{
    //	  static assert(false, Format!("Can not convert BitVec of size %s"
    //				       ~ " to %s", SIZE, "string"));
    //	}
    //   }

    public T opSlice(size_t i, size_t j) const
      in {
        assert(i < SIZE && i >= 0 && j <= SIZE && j >= 0);
        assert(i < j);
      }
    body {
      T result = this >>> i;
      result &= ones(j - i);
      return result;
    }

    // operator []
    // public barray opSlice() {
    //   return this.to!barray;
    // }

    // place the bits available from the given rhs and place into the
    // specified location
    public void put(V)(size_t i, size_t j, V other)
      if(isBitVector!V || isIntegral!V) {
	auto mask = ones(i, j);
	this.maskOut(mask);

	auto rhs = ones(0, j - i) & other;
	
	this.maskIn(rhs << i);
      }

    public auto get(int COUNT)(size_t i) const
      if(COUNT <= SIZE) {
	assert(i + COUNT <= SIZE);
	_bvec!(S,L,N) retval = cast(typeof(this)) this;
	retval >>= i;
	return cast(_bvec!(S,L,COUNT)) retval;
      }

    // public BitVec!(I, J) slice(size_t I, size_t J=0)() {
    //   static assert(I < SIZE && I >= 0 && J < SIZE && J >= 0);
    //   static assert(I != J);
    //   BitVec!(I, J) bv;
    //   static if(I > J) {
    //     for(size_t k=J; k!=I; ++k) {
    //	bv[k] = this[k];
    //     }
    //   } else {			// J > I
    //     for(size_t k=I; k!=J; ++k) {
    //	bv[k] = this[k];
    //     }
    //   }
    //   return bv;
    // }

    public auto reverse() {
      typeof(this) retval;
      for(size_t i=0; i != SIZE; ++i) {
	retval[SIZE-i-1] = this[i];
      }
      return retval;
    }

    private void reportX(string file = __FILE__,
			 size_t line = __LINE__, V)(const V other) const
      if(isBitVector!V) {
	static if(this.IS4STATE || other.IS4STATE) {
	  if(this.isX || other.isX) {
	    throw new LogicError(format("Logic value of one of the " ~
					"operands is X, %s, %s",
					this, other), file, line);
	  }
	}
      }

    private void reportX(string file = __FILE__,
			 size_t line = __LINE__, V)(const V other) const
      if(isIntegral!V || isBoolean!V) {
	static if(this.IS4STATE) {
	  if(this.isX) {
	    throw new LogicError(format("Logic value of " ~
					"operand is X, %s",
					this), file, line);
	  }
	}
      }


    public int opCmp(string file = __FILE__,
		     size_t line = __LINE__, V)(const V other) const
      if(isBitVector!V &&
	 _vecCmpT!(typeof(this), V)) {
	reportX!(file, line)(other);
	alias P = _bvec!(typeof(this), V, "COMPARE");
	P lhs = this;
	P rhs = other;
	return lhs.compare(rhs);
      }

    public int opCmp(string file = __FILE__,
		     size_t line = __LINE__, V)(const V other) const
      if(isIntegral!V) {
	reportX!(file, line)(other);
	alias P = _bvec!(typeof(this), _bvec!V, "COMPARE");
	P lhs = this;
	P rhs = other;
	return lhs.compare(rhs);
      }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__, V)(const V other)
      if(isBitVector!V) {
	reportX!(file, line)(other);
	alias _bvec!(typeof(this), V, "COMPARE") P;
	P lhs = this;
	P rhs = other;
	return lhs.isEqual(rhs);
      }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const bool other) const {
      alias P = _bvec!(typeof(this), bool, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const byte other) const {
      alias P = _bvec!(typeof(this), byte, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const short other) const {
      alias P = _bvec!(typeof(this), short, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const int other) const {
      alias P = _bvec!(typeof(this), int, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const long other) const {
      alias P = _bvec!(typeof(this), long, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const ubyte other) const {
      alias P = _bvec!(typeof(this), ubyte, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const ushort other) const {
      alias P = _bvec!(typeof(this), ushort, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const uint other) const {
      alias P = _bvec!(typeof(this), uint, "COMPARE");
      P lhs = this;
      P rhs = other;
      return lhs.isEqual(rhs);
    }

    public bool opEquals(string file = __FILE__,
			 size_t line = __LINE__)(const ulong other) const {
	alias P = _bvec!(typeof(this), ulong, "COMPARE");
	P lhs = this;
	P rhs = other;
	return lhs.isEqual(rhs);
      }

    public bool opEquals(ref const T other) const {
	for(size_t i=1; i!=STORESIZE; ++i) {
	  if(this._aval[$-1-i] != other._aval[$-1-i]) return false;
	}
	if((this._aval[$-1] & UMASK) != (other._aval[$-1] & T.UMASK)) return false;
	return true;
    }

    public size_t toHash() const nothrow @safe {
      size_t hash;
      for (size_t i=0; i!=STORESIZE; ++i) {
	hash ^= _aval[i];
      }
      static if(this.IS4STATE) {
	for (size_t i=0; i!=STORESIZE; ++i) {
	  hash ^= _bval[i];
	}
      }
      return hash;
    }

    public bool isSame(string file = __FILE__,
		       size_t line = __LINE__, V)(V other)
      if(isIntegral!V || isBoolean!V) {
	alias _bvec!(typeof(this), _bvec!V, "COMPARE") P;
	P lhs = this;
	P rhs = other;
	return lhs.isLogicEqual(rhs);
      }

    public bool isSame(string file = __FILE__,
		       size_t line = __LINE__, V)(V other)
      if(isBitVector!V) {
	alias _bvec!(typeof(this), V, "COMPARE") P;
	P lhs = this;
	P rhs = other;
	return lhs.isLogicEqual(rhs);
      }

    public int compare(V)(V other) // V shall have the same type as typeof(this)
      if(is(V == typeof(this))) {
	for(size_t i=1; i!=STORESIZE; ++i) {
	  if(this._aval[$-1-i] < other._aval[$-1-i]) return -1;
	  if(this._aval[$-1-i] > other._aval[$-1-i]) return 1;
	}

	if((this._aval[$-1] & UMASK) < (other._aval[$-1] & V.UMASK)) return -1;
	if((this._aval[$-1] & UMASK) > (other._aval[$-1] & V.UMASK)) return 1;

	return 0;
      }


    public bool isEqual(V)(V other)
      if(is(V == typeof(this))) {
	for(size_t i=1; i!=STORESIZE; ++i) {
	  if(this._aval[$-1-i] != other._aval[$-1-i]) return false;
	}
	if((this._aval[$-1] & UMASK) != (other._aval[$-1] & V.UMASK)) return false;
	return true;
      }

    public bool isLogicEqual(V)(V other)
      if(is(V == typeof(this))) {
	for(size_t i=1; i!=STORESIZE; ++i) {
	  if(this._aval[$-1-i] != other._aval[$-1-i]) return false;
	  static if(IS4STATE) {
	    if(this._bval[$-1-i] != other._bval[$-1-i]) return false;
	  }
	}
	if((this._aval[$-1] & UMASK) != (other._aval[$-1] & V.UMASK)) return false;
	static if(IS4STATE) {
	  if((this._bval[$-1] & UMASK) != (other._bval[$-1] & V.UMASK)) return false;
	}
	return true;
      }

    // Bitwise Compliment
    public auto opUnary(string op)() if(op == "~") {
      // compliment every bit
      _bvec!(S,L,SIZE) result = this;
      for(size_t i; i != STORESIZE; ++i) {
	static if (store_t.sizeof >= 4) {
	  result._aval[i] = ~_aval[i];
	}
	else {
	  result._aval[i] = cast(store_t) ~(cast(int) _aval[i]);
	}
      }
      // UMASK out the unused bits
      result._aval[$-1] &= UMASK;
      return result;
    }


    public void opOpAssign(string op, string file = __FILE__,
			   size_t line = __LINE__, V)(V other)
      if(isIntegral!V &&	(op == "+" || op == "-")) {
	reportX!(file, line)(other);
	_bvec!V rhs = other;
	this.opOpAssign!op(rhs);
      }

    public void opOpAssign(string op, string file = __FILE__,
			   size_t line = __LINE__, V)(V other)
      if(isBitVector!V && (op == "+" || op == "-")) {
	reportX!(file, line)(other);

	auto rhs = cast(typeof(this)) other;
	static if(this.SIZE <= WORDSIZE) {
	  static if(op == "+") _aval[0] += rhs._aval[0];
	  else                 _aval[0] -= rhs._aval[0];
	  return;
	}
	else {
	  uint[] a = cast(uint[]) this._aval;
	  uint[] b = cast(uint[]) rhs._aval;
	  long carry = 0;
	  for(size_t i=0; i != a.length; ++i) {
	    static if(op == "+") {
	      long _r = carry + a[i] + b[i];
	      a[i] = cast(typeof(a[i])) _r;
	      carry = _r >> WORDSIZE;
	    }
	    static if(op == "-") {
	      long _r = carry + a[i] - b[i];
	      a[i] = cast(typeof(a[i])) _r;
	      carry = _r >> WORDSIZE;
	    }
	  }
	  if(this.aValMSB) {
	    _aval[$-1] |= SMASK;
	  }
	  else {
	    _aval[$-1] &= UMASK;
	  }
	}
      }

    public auto opUnary(string op)() if (op == "++")
      {
	this += 1;
	return this;
      }

    public auto opUnary(string op)() if (op == "--")
      {
	this -= 1;
	return this;
      }

    public auto opUnary(string op)() const
      if(op == "-") {
	typeof(this) result = 0;
	result -= this;
	return result;
      }

    public auto opBinaryRight(string op, V)(V other)
      if(isIntegral!V &&
	 (op == "+" || op == "-")) {
	_bvec!V rhs = other;
	return rhs.opBinary!op(this);
      }

    // Addition and Substraction with other BitVec
    public auto opBinary(string op, V)(V other) const
      if(isBitVector!V && (op == "+" || op == "-")) {
	// static if(SIZE >= V.SIZE) {
	// typeof(this) result = this;
	_bvec!(this_type, V, "+") result = this;
	static if(op == "+") result += other;
	else result -= other;
	return result;
	// }
	// else {
	//   static if(op == "+") {
	//     _bvec!(V.ISSIGNED, V.IS4STATE, V.SIZE+1) result = other;
	//   }
	//   else {
	//     _bvec!(V.IS4STATE, V.IS4STATE, V.SIZE+1) result = -other;
	//   }
	//   result += this;
	//   return result;
	// }
      }

    public auto opBinary(string op)(size_t shift) const
      if(op == "<<" || op == ">>" || op == ">>>") {
	T result = this;
	result.opOpAssign!(op)(shift);
	return result;
      }

    public auto opBinary(string op, string file= __FILE__,
			 size_t line = __LINE__, V)(V other) const
      if(isBitVector!V && (op == "*")) {
	reportX!(file, line)(other);
	alias R = _bvec!(this_type, V, "*");
	R result = 0;

	static if(result.SIZE <= 32) {
	  result._aval[0] = cast(R.store_t) (_aval[0] * other._aval[0]);
	}
	else {
	  uint[] r = cast(uint[]) result._aval;
	  uint[] a = cast(uint[]) this._aval;
	  uint[] b = cast(uint[]) other._aval;

	  bool aNegative = this.aValMSB();
	  bool bNegative = other.aValMSB();

	  uint _a = void;
	  uint _b = void;
	  for(size_t i=0; i!=r.length; ++i) {
	    uint carry = 0;
	    if(i < a.length) {	     // initialize and sign extend if required
	      _a = a[i];
	      if(aNegative) {
		if(i == a.length - 1) _a |= ~(cast(uint) UMASK);
	      }
	    }
	    else {
	      if(aNegative) _a = uint.max;
	      else if(carry == 0) break;
	      else _a = 0;
	    }
	    for(size_t j=0; j!=r.length-i; ++j) {
	      if(j < b.length) {     // initialize and sign extend if required
		_b = b[j];
		if(bNegative) {
		  if(j == b.length - 1) _b |= ~(cast(uint) V.UMASK);
		}
	      }
	      else {
		if(bNegative) _b = uint.max;
		else if(carry == 0) break;
		else _b = 0;
	      }

	      ulong t = cast(ulong) carry + cast(ulong) r[i+j] + cast(ulong)_a * cast(ulong)_b;
	      // writefln("i: %d, j: %d, carry: %X, r[i+j]: %X, _a: %X, _b: %X",
	      //	       i, j, carry, r[i+j], _a, _b);
	      r[i+j] = cast(uint) t;
	      carry = cast(uint)(t >>> 32);
	    }
	  }
	}
	result._aval[$-1] &= result.UMASK;
	if (result.aValMSB) result._aval[$-1] |= result.SMASK;
	return result;
      }

    public auto opBinary(string op, string file= __FILE__,
			 size_t line = __LINE__, V)(V other) const
      if(isBitVector!V && (op == "/")) {
	reportX!(file, line)(other);
	alias R = _bvec!(this_type, V, "/");
	R result = 0;
	static if(R.SIZE <= 64) {
	  result = getValue() / other.getValue();
	}
	else {
	  pragma(msg, "Not implemented yet -- TBD (use std.internal.math.biguintcore");
	}

	if (result.aValMSB) result._aval[$-1] |= result.SMASK;
	return result;
      }


    // Left Shift Assign
    public void opOpAssign(string op)(size_t shift)
      if(op == "<<") {
	auto wordShift = shift / WORDSIZE;
	auto bitShift = shift % WORDSIZE;
	if(wordShift > 0) {
	  for(size_t i=STORESIZE; i!=0; --i) {
	    if(i > wordShift) _aval[i-1] = _aval[(i-1)-wordShift];
	    else _aval[i-1] = 0;
	    static if(L) {
	      if(i > wordShift) _bval[i-1] = _bval[(i-1)-wordShift];
	      else _bval[i-1] = 0;
	    }
	  }
	}
	if(bitShift != 0) {
	  for(size_t i=STORESIZE; i!=0; --i) {
	    _aval[i-1] <<= bitShift;
	    if(i > 1) {
	      _aval[i-1] |= _aval[i-2] >>>(WORDSIZE - bitShift);
	    }
	    static if(L) {
	      _bval[i-1] <<= bitShift;
	      if(i > 1) {
		_bval[i-1] |= _bval[i-2] >>>(WORDSIZE - bitShift);
	      }
	    }
	  }
	}
	// UMASK out the unused bits
	if(this.aValMSB) _aval[$-1] |= SMASK;
	else		     _aval[$-1] &= UMASK;
	static if(L) {
	  if(this.bValMSB) _bval[$-1] |= SMASK;
	  else		     _bval[$-1] &= UMASK;
	}
      }

    // Right Shift Assign
    public void opOpAssign(string op)(size_t shift)
      if(op == ">>" ||		// sign extended
	 op == ">>>") {		// normal
	auto wordShift = shift / WORDSIZE;
	auto bitShift = shift % WORDSIZE;
	if(wordShift > 0) {
	  for(size_t i=0; i!=STORESIZE; ++i) {
	    if(i+wordShift < STORESIZE) _aval[i] = _aval[i+wordShift];
	    else {
	      static if(op == ">>") {
		if(this.aValMSB) _aval[i] = cast(store_t) -1;
		else             _aval[i] = 0;
	      }
	      static if(op == ">>>") {
		_aval[i] = 0;
	      }
	    }
	    static if(L) {
	      if(i+wordShift < STORESIZE) _bval[i] = _bval[i+wordShift];
	      else {
		static if(op == ">>") {
		  if(this.bValMSB) _bval[i] = ~0;
		  else                 _bval[i] = 0;
		}
		static if(op == ">>>") {
		  _bval[i] = 0;
		}
	      }
	    }
	  }
	}
	if(bitShift != 0) {
	  for(size_t i=0; i!=STORESIZE; ++i) {
	    if(i < STORESIZE-1) {
	      _aval[i] >>>= bitShift;
	      _aval[i] |= _aval[i+1] <<(WORDSIZE - bitShift);
	      static if(L) {
		_bval[i] >>>= bitShift;
		_bval[i] |= _bval[i+1] <<(WORDSIZE - bitShift);
	      }
	    }
	    else {
	      static if(op == ">>") _aval[i] >>= bitShift;
	      static if(op == ">>>") _aval[i] >>>= bitShift;
	      if(this.aValMSB) _aval[$-1] |= SMASK;
	      else                 _aval[$-1] &= UMASK;
	      static if(L) {
		static if(op == ">>") _bval[i] >>= bitShift;
		static if(op == ">>>") _bval[i] >>>= bitShift;
		if(this.bValMSB) _bval[$-1] |= SMASK;
		else                 _bval[$-1] &= UMASK;
	      }
	    }
	  }
	}
      }


    // Concatenation
    public auto opBinary(string op, V)(V other) const
      if(isBitVector!V && (op == "~")) {
	_bvec!(T, V, "~") result = this;
	result <<= V.SIZE;
	result[0..V.SIZE] = other;
	return result;
      }

    // int opApply(scope int delegate(ref bool) dg)
    // int opApply(scope int delegate(ref bit) dg) {
    //   int result = 0;
    //   for(size_t i = 0; i < SIZE; i++) {
    //     bit b = this.opIndex(i);
    //     result = dg(b);
    //     this[i] = b;
    //     if(result) break;
    //   }
    //   return result;
    // }

    /** ditto */
    // int opApply(scope int delegate(ref size_t, ref bool) dg)
    // int opApply(int delegate(ref size_t, ref bit) dg) {
    //   int result = 0;
    //   for(size_t i = 0; i < SIZE; i++) {
    //     bit b = this.opIndex(i);
    //     result = dg(i, b);
    //     this[i] = b;
    //     if(result) break;
    //   }
    //   return result;
    // }
}

public auto toBitVec(T)(T t) if(isIntegral!T) {
  static if(isSigned!T) {
    alias R = BitVec!(8*T.sizeof);
  }
  else {
    alias R = UBitVec!(8*T.sizeof);
  }
  R res = t;
  return res;
 }

// Utility functions
private uint multibyteDivAssign(uint [] dest, uint divisor, uint overflow) {
  ulong c = cast(ulong)overflow;
  for(ptrdiff_t i = dest.length-1; i>= 0; --i) {
    c =(c<<32) + cast(ulong)(dest[i]);
    uint q = cast(uint)(c/divisor);
    c -= divisor * q;
    dest[i] = q;
  }
  return cast(uint)c;
}

private void itoaZeroPadded(char[] output, uint value, int radix = 10) {
  ptrdiff_t x = output.length - 1;
  for( ; x >= 0; --x) {
    output[x]= cast(char)(value % radix + '0');
    value /= radix;
  }
}

package size_t biguintToDecimal(char [] buff, uint [] data) {
  ptrdiff_t sofar = buff.length;
  // Might be better to divide by(10^38/2^32) since that gives 38 digits for
  // the price of 3 divisions and a shr; this version only gives 27 digits
  // for 3 divisions.
  while(data.length>1) {
    uint rem = multibyteDivAssign(data, 10_0000_0000, 0);
    itoaZeroPadded(buff[sofar-9 .. sofar], rem);
    sofar -= 9;
    if(data[$-1] == 0 && data.length > 1) {
      data.length = data.length - 1;
    }
  }
  itoaZeroPadded(buff[sofar-10 .. sofar], data[0]);
  sofar -= 10;
  // and strip off the leading zeros
  while(sofar!= buff.length-1 && buff[sofar] == '0')
    sofar++;
  return sofar;
}

private void toHexZeroPadded(char[] output, uint value) {
  ptrdiff_t x = output.length - 1;
  static immutable string hexDigits = "0123456789ABCDEF";
  for( ; x>=0; --x) {
    output[x] = hexDigits[value & 0xF];
    value >>= 4;
  }
}

public auto toBits(T)(T val) {
  // static if(size_t.sizeof == 8 && T.sizeof >= 8) {
  //   enum WSIZE = (T.sizeof+7)/8;
  //   alias ulong U;
  // }
  // else
  static if(T.sizeof >= 4) {
    enum WSIZE = (T.sizeof+3)/4;
    alias uint U;
  }
  else static if(T.sizeof >= 2) {
      enum WSIZE = (T.sizeof+1)/2;
      alias ushort U;
    }
  else static if(T.sizeof == 1) {
      enum WSIZE = T.sizeof;
      alias ubyte U;
    }

  union utype {
    U[WSIZE] b;
    T f;
  }

  utype u;
  u.f = val;

  alias UBitVec!(8*T.sizeof) V;
  V retval;

  for(size_t i=0; i!=V.STORESIZE; ++i) {
    retval._aval[i] = u.b[i];
  }
  return retval;
}

public void fromBits(T, B)(ref T val, B bv)
  if(isBitVector!B && 8*T.sizeof == B.SIZE) {
    static if(B.IS4STATE) {
      assert(bv.bVal == 0);
    }
    // static if(T.sizeof >= 8) {
    //   enum WSIZE = (T.sizeof+7)/8;
    //   alias ulong U;
    // }
    // else
      static if(T.sizeof >= 4) {
	enum WSIZE = (T.sizeof+3)/4;
	alias uint U;
      }
    else static if(T.sizeof >= 2) {
	enum WSIZE = (T.sizeof+1)/2;
	alias ushort U;
      }
    else static if(T.sizeof == 1) {
	enum WSIZE = T.sizeof;
	alias ubyte U;
      }

    union utype {
      U[WSIZE] b;
      T f;
    }

    utype u;

    for(size_t i=0; i!=B.STORESIZE; ++i) {
      u.b[i] = bv._aval[i];
    }

    val = u.f;
  }


alias BitVec Bit;
alias UBitVec UBit;
alias LogicVec Logic;
alias ULogicVec ULogic;




/*    */
unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k < 64 ; ++k){
    static UBit!64     a ; 
    static UBit!64     b ;  
    for(uint i = 0 ; i < 1000 ; ++i){
      auto a_1 = uniform(0, (pow(2,k)-1)); 
      auto b_1 = uniform(0, (pow(2,k)-1)); 
      a = a_1 ;
      b = b_1 ;
      auto y = cast(UBit!64) (a + b) ;
      assert(y == (a_1 + b_1));
    }
  }

}

unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k < 64 ; ++k){
    static UBit!64     a ; 
    static UBit!64     b ;  
    for(uint i = 0 ; i < 1000 ; ++i){
      auto a_1 = uniform(0, (pow(2,k)-1)); 
      auto b_1 = uniform(0, (pow(2,k)-1)); 
      a = a_1 ;
      b = b_1 ;
      auto y = cast(UBit!64) (a + b) ;
      assert(y == (a_1 + b_1));
    }
  }

}


unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k < 64 ; ++k){
    static UBit!64     a ; 
    static UBit!64     b ;  
    for(uint i = 0 ; i < 1000 ; ++i){
      auto a_1 = uniform(0, (pow(2,k)-1)); 
      auto b_1 = uniform(0, (pow(2,k)-1)); 
      a = a_1 ;
      b = b_1 ;
      auto y = cast(UBit!64) (a - b);
      assert(y == (a_1 - b_1));
    }
  }

  UBit!8  a = cast(byte) 0xff ;
  UBit!8  b = cast(byte) 0xff ;
  UBit!8  y = a + b;
  assert(y == 254) ;

  y = cast(UBit!8)(a + b) ;
  assert(y == 254) ;

}


unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k != 33 ; ++k){
    static UBit!64     a ; 
    static UBit!64     b ;  
    // static UBit!64     y ;
    for(uint i = 0 ; i != 1000; ++i){
      auto a_1 = uniform(0, (pow(2,k)-1)); 
      auto b_1 = uniform(0, (pow(2,k)-1)); 
      a = a_1 ;
      b = b_1 ;
      auto y = cast(UBit!64) (a * b) ;
      assert(y == (a_1 * b_1));
    }
  }

}

unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;

  UBit!63[]   mUBit ;
  UBit!63[]   nUBit ;
  UBit!63[16] pUBit ;
  mUBit.length = 16 ;
  nUBit.length = 16 ;
}


unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k < 15 ; ++k){
    static Bit!64     a ; 
    static Bit!64     b ;  
    for(uint i = 0 ; i < 1000 ; ++i){
      auto a_1 = uniform(-1000, 1000); 
      auto b_1 = uniform(-1000, 1000); 
      a = a_1 ;
      b = b_1 ;
      auto y = a + b ;
      assert(y == (a_1 + b_1));
    }
  }

}




unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k < 15 ; ++k){
    static Bit!63     a ; 
    static Bit!63     b ;  
    for(uint i = 0 ; i < 1000 ; ++i){
      auto a_1 = uniform(-1000, 1000); 
      auto b_1 = uniform(-1000, 1000); 
      a = a_1 ;
      b = b_1 ;
      auto y = a - b ;
      assert(y == (a_1 - b_1));
    }
  }

  Bit!8  a = cast(byte) 0xff ;
  Bit!8  b = cast(byte) 0xff ;
  auto z = cast(Bit!9)a + cast(Bit!9)b;
  Bit!9  y = a + b;
  assert(y == -2) ;

  y = cast(Bit!9)(a + b) ;
  assert(y == -2) ;

}

unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k != 4 ; ++k){
    static Bit!63     a ; 
    static Bit!63     b ;  
    // static Bit!64     y ;
    for(uint i = 0 ; i != 4; ++i){
      auto a_1 = uniform(-1000, 1000); 
      auto b_1 = uniform(-1000, 1000); 
      a = a_1 ;
      b = b_1 ;
      auto y = a * b ;
      assert(y == (a_1 * b_1));
    }
  }

}


unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;

  UBit!64[]   mUBit ;
  UBit!64[]   nUBit ;
  UBit!64[16] pUBit ;
  mUBit.length = 16 ;
  nUBit.length = 16 ;

  for(uint i = 0 ; i < 16 ; ++i){
    auto a_1 = uniform(0, 10000); 
    auto b_1 = uniform(0, 10000); 
    mUBit[i] = a_1 ;
    nUBit[i] = b_1 ;
    pUBit[i] = cast(UBit!64) (mUBit[i] + nUBit[i]);
    assert(pUBit[i] == (a_1 + b_1));
  }

  for(uint i = 0 ; i < 16 ; ++i){
    auto a_1 = uniform(0, 10000); 
    auto b_1 = uniform(0, 10000); 
    mUBit[i] = a_1 ;
    nUBit[i] = b_1 ;
    pUBit[i] = cast(UBit!64) (mUBit[i] - nUBit[i]);
    assert(pUBit[i] == (a_1 - b_1));
  }


  for(uint i = 0 ; i < 16 ; ++i){
    auto a_1 = uniform(0, 1000); 
    auto b_1 = uniform(0, 1000); 
    mUBit[i] = a_1 ;
    nUBit[i] = b_1 ;
    pUBit[i] = cast(UBit!64) (mUBit[i] * nUBit[i]);
    assert(pUBit[i] == (a_1 * b_1));
  }
}


unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k < 15 ; ++k){
    static Bit!63     a ; 
    static Bit!63     b ;  
    for(uint i = 0 ; i < 1000 ; ++i){
      auto a_1 = uniform(-1000, 1000); 
      auto b_1 = uniform(-1000, 1000); 
      a = a_1 ;
      b = b_1 ;
      auto y = a + b ;
      assert(y == (a_1 + b_1));
    }
  }

  Bit!8  a = cast(byte) 0xff ;
  Bit!8  b = cast(byte) 0xff ;
  Bit!9  y = a + b;
  assert(y == -2) ;

  y = a + b;

  assert(y == -2) ;

}

unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k < 15 ; ++k){
    static Bit!63     a ; 
    static Bit!63     b ;  
    for(uint i = 0 ; i < 1000 ; ++i){
      auto a_1 = uniform(-1000, 1000); 
      auto b_1 = uniform(-1000, 1000); 
      a = a_1 ;
      b = b_1 ;
      auto y = a - b ;
      assert(y == (a_1 - b_1));
    }
  }

}



unittest {
  import std.random ;
  import std.math ;
  import std.stdio ;
  for(ulong k = 1 ; k != 15 ; ++k){
    static Bit!63     a ; 
    static Bit!63     b ;  
    // static Bit!64     y ;
    for(uint i = 0 ; i != 10; ++i){
      auto a_1 = uniform(-1000, 1000); 
      auto b_1 = uniform(-1000, 1000); 
      a = a_1 ;
      b = b_1 ;
      auto y = a * b ;
      assert(y == (a_1 * b_1));
    }
  }

}

unittest {
   import std.stdio ;

   ULogic!8 a1  = bin!q{11111111} ; 
   ULogic!8 a2  = hex!q{ff} ;  

   ubyte a1_s = 0b11111111 ;
   ubyte a2_s = 0b11111111 ;

   assert(cast(ubyte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(ubyte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(ubyte)(a1_s * a1_s) == cast(ubyte)(a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{00000000} ; 
   a2 = hex!q{0} ;  
   a1_s = 0b00000000 ;
   a2_s = 0b00000000 ;

   assert(cast(ubyte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(ubyte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(ubyte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{10101010} ; 
   a2 = bin!q{10101010} ;  
   a1_s = 0b10101010 ;
   a2_s = 0b10101010 ;

   assert(cast(ubyte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(ubyte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(ubyte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);
}


unittest {
   import std.stdio ;

   Logic!8 a1 = bin!q{11111111} ; 
   Logic!8 a2 = hex!q{ff} ;  

   byte a1_s = cast(byte)0b11111111 ;
   byte a2_s = cast(byte)0b11111111 ;

   assert((a1_s + a1_s) == (a1 + a2));
   assert((a1_s - a1_s) == (a1 - a2));
   assert((a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{00000000} ; 
   a2 = bin!q{00000000} ;  
   a1_s = cast(byte)0b00000000 ;
   a2_s = cast(byte)0b00000000 ;

   assert((a1_s + a1_s) == (a1 + a2));
   assert((a1_s - a1_s) == (a1 - a2));
   assert((a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{10101010} ; 
   a2 = bin!q{10101010} ;  
   a1_s = cast(byte)0b10101010 ;
   a2_s = cast(byte)0b10101010 ;

   assert(cast(byte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(byte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(byte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);
}



unittest {
   import std.stdio ;

   UBit!8 a1 = bin!q{11111111} ; 
   UBit!8 a2 = hex!q{ff} ;  

   ubyte a1_s = 0b11111111 ;
   ubyte a2_s = 0b11111111 ;

   assert(cast(ubyte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(ubyte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(ubyte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{00000000} ; 
   a2 = bin!q{00000000} ;  
   a1_s = 0b00000000 ;
   a2_s = 0b00000000 ;

   assert(cast(ubyte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(ubyte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(ubyte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{10101010} ; 
   a2 = bin!q{10101010} ;  
   a1_s = 0b10101010 ;
   a2_s = 0b10101010 ;

   assert(cast(ubyte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(ubyte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(ubyte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{1} ; 
   UBit!1 a2_ = cast(UBit!1)a1[0] ;
   Bit!1 a3 = cast(Bit!1)a2_ ;
   assert(a1[0] == a3);

}

unittest {
   import std.stdio ;

   Bit!8 a1 = bin!q{11111111} ; 
   Bit!8 a2 = hex!q{ff} ;  

   byte a1_s = cast(byte)0b11111111 ;
   byte a2_s = cast(byte)0b11111111 ;

   assert(cast(byte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(byte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(byte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{00000000} ; 
   a2 = bin!q{00000000} ;  
   a1_s = cast(byte)0b00000000 ;
   a2_s = cast(byte)0b00000000 ;

   assert(cast(byte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(byte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(byte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{10101010} ; 
   a2 = bin!q{10101010} ;  
   a1_s = cast(byte)0b10101010 ;
   a2_s = cast(byte)0b10101010 ;

   assert(cast(byte)(a1_s + a1_s) == (a1 + a2));
   assert(cast(byte)(a1_s - a1_s) == (a1 - a2));
   assert(cast(byte)(a1_s * a1_s) == (a1 * a2));
   assert((a1_s | a1_s) == (a1 | a2));
   assert((a1_s || a1_s) == (a1 || a2));
   assert((a1_s & a1_s) == (a1 & a2));
   assert((a1_s && a1_s) == (a1 && a2));
   assert((a1_s ^ a1_s) == (a1 ^ a2));
   assert(!a1_s == !a1);
   assert(~a1_s == ~a1);

   a1 = bin!q{1} ; 
   Bit!1 a2_ = cast(Bit!1)a1[0] ;
   UBit!1 a3 = cast(UBit!1)a2_ ;
   assert(a1[0] == a3);


}


unittest {

   import std.stdio ;

   Logic!8 a1 = bin!q{1} ; 
   assert(a1 == LOGIC_1);   

   a1 = bin!q{0};
   assert(a1 == LOGIC_0);   

   a1 = bin!q{X};
   assert(a1.isX());   

   a1 = hex!q{ZZ};
   assert(a1.isZ());   

   a1 = LOGIC_X ;
   assert(a1.isX());   

   a1 = LOGIC_Z ;
   assert(!a1.isZ());   


}

unittest {

   import std.stdio ;

   ULogic!8 a1 = bin!q{1} ; 
   assert(a1 == LOGIC_1);   

   a1 = bin!q{0};
   assert(a1 == LOGIC_0);   

   a1 = bin!q{X};
   assert(a1.isX());   

   a1 = bin!q{zzzzzzzz};
   writefln("%b", a1);
   assert(a1.isZ());   

   a1 = LOGIC_X ;
   assert(a1.isX());   

   a1 = LOGIC_Z ;
   assert(!a1.isZ());

   a1 = bin!q{1} ; 
   Logic!1 a2 = a1[0] ;
   ULogic!1 a3 = a2 ;
   assert(a1[0] == a3);
}

unittest {

    assert(isStr4State("X"));
    assert(isStr4State("Z"));
    assert(!isStr4State("1"));
    assert(!isStr4State("0"));

    Bit!8  x1 ; x1.randomize(); x1.reverse();
    UBit!8 x2 ; x2.randomize(); x2.reverse();
    Logic!8  x3 ; x3.randomize(); x3.reverse();
    ULogic!8 x4 ; x4.randomize(); x4.reverse();


}

unittest {

    import std.stdio ;

    Bit!8 x1 = hex!q{5} ;
    Bit!9 x2 = cast(Bit!9)x1 ;

    UBit!8 x3 = hex!q{5} ;
    UBit!9 x4 = cast(UBit!9)x3 ;

    x2 = cast(Bit!9) x4 ;

    writefln("%d",x1);
    writefln("%s",x1);
    writefln("%x",x1);
    writefln("%o",x1);
    writefln("%b",x1);

    writefln("%d",x3);
    writefln("%s",x3);
    writefln("%x",x3);
    writefln("%o",x3);
    writefln("%b",x3);

}

unittest {

    import std.stdio ;

    Logic!8 x1 = hex!q{5} ;
    Logic!9 x2 = cast(Logic!9)x1 ;

    ULogic!8 x3 = hex!q{5} ;
    ULogic!9 x4 = cast(ULogic!9)x3 ;

    x2 = cast(Logic!9) x4 ;

    writefln("%d",x1);
    writefln("%s",x1);
    writefln("%x",x1);
    writefln("%o",x1);
    writefln("%b",x1);

    writefln("%d",x3);
    writefln("%s",x3);
    writefln("%x",x3);
    writefln("%o",x3);
    writefln("%b",x3);

    ULogic!4 x5 ;
    x5[0] = LOGIC_0 ;
    x5[1] = LOGIC_1 ;
    x5[2] = LOGIC_X ;
    x5[3] = LOGIC_Z ;

    assert(x5[0] == LOGIC_0);
    assert(x5[1] == LOGIC_1);
    assert(x5[2].isX());
    assert(x5[3].isZ());

    Logic!4 x6 ;
    x6[0] = LOGIC_0 ;
    x6[1] = LOGIC_1 ;
    x6[2] = LOGIC_X ;
    x6[3] = LOGIC_Z ;

    assert(x6[0] == LOGIC_0);
    assert(x6[1] == LOGIC_1);
    assert(x6[2].isX());
    assert(x6[3].isZ());

}

unittest {

    Bit!65 [] x1 ;
    Bit!65 [] x2 ;

    Bit!130 [16] y ; 
    x1.length = 16 ;
    x2.length = 16 ;
 
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] + x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] - x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] * x2[i] ;
}

unittest {

    UBit!8 [] x1 ;
    UBit!8 [] x2 ;

    UBit!16 [16] y ; 
    x1.length = 16 ;
    x2.length = 16 ;
 
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] + x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] - x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] * x2[i] ;

}

unittest {

    Logic!65 [] x1 ;
    Logic!65 [] x2 ;

    Logic!130 [16] y ; 
    x1.length = 16 ;
    x2.length = 16 ;
 
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] + x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] - x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] * x2[i] ;
}

unittest {

    ULogic!65 [] x1 ;
    ULogic!65 [] x2 ;

    ULogic!130 [16] y ; 
    x1.length = 16 ;
    x2.length = 16 ;
 
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] + x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] - x2[i] ;
    for(uint i = 0 ; i < 16 ; ++i) y[i] = x1[i] * x2[i] ;
}



// ----- Following has Failed Test 

unittest {

   Bit!8 x1 = bin!q{11111111} ;
   assert(cast(byte)x1 != 0) ;
   assert(cast(byte)x1 == bin!q{11111111}) ;
   assert(cast(byte)x1 == hex!q{ff}) ;
   //assert(cast(byte)x1 > hex!q{f}) ;

   UBit!8 x2 = bin!q{11111111} ;
   assert(cast(byte)x2 != 0) ;
   assert(cast(byte)x2 == bin!q{11111111}) ;
   assert(cast(byte)x2 == hex!q{ff}) ;
   //assert(cast(byte)x2 > hex!q{f}) ;

   Logic!8 x3 = bin!q{11111111} ;
   assert(cast(byte)x3 != 0) ;
   assert(cast(byte)x3 == bin!q{11111111}) ;
   assert(cast(byte)x3 == hex!q{ff}) ;
   //assert(cast(byte)x3 > hex!q{f}) ;

   ULogic!8 x4 = bin!q{11111111} ;
   assert(cast(byte)x4 != 0) ;
   assert(cast(byte)x4 == bin!q{11111111}) ;
   assert(cast(byte)x4 == hex!q{ff}) ;
   //assert(cast(byte)x4 > hex!q{f}) ;

   Bit!8 x5 = x1 >> bin!q{1} ;
   assert(x5 == bin!q{1111111});

   x5 = x1 << bin!q{1} ;
   assert(x5 == bin!q{11111110});
   x5 = x1 << hex!q{1} ;
   assert(x5 == bin!q{11111110});

   UBit!8 x6 = x2 >>> bin!q{1} ;
   //assert(x6 == bin!q{111111});

   Logic!8 x7 = x3 >> bin!q{1} ;
   assert(x7 == bin!q{111111});

   x7 = x3 <<  bin!q{1} ;
   assert(x7 == bin!q{1111110});
   x7 = x3 <<  hex!q{1} ;
   assert(x7 == bin!q{1111110});

   ULogic!8 x8 = x4 >>> bin!q{1} ;

}

unittest {

   UBit!1025 mfunc(UBit!1024 p_, UBit!1024 n_){
      UBit!1025 temp  = (p_ + n_);
      return(temp);
   }

   UBit!1025 x = mfunc(cast(UBit!1024)1024,cast(UBit!1024)100) ;

}


unittest {
    import std.random ;
    import std.stdio ;
    immutable uint N = 65 ;
    Logic!65 wow ;
    for(uint i = 0 ; i < N ; ++i){
      int tmp = uniform(0, 4); 
         
      if      (tmp == 0) wow[i] = LOGIC_X ;
      else if (tmp == 1) wow[i] = LOGIC_Z ;
      else if (tmp == 2) wow[i] = LOGIC_1 ;
      else if (tmp == 3) wow[i] = LOGIC_0 ;
      else   assert(0);

    }

    writefln("binary : %b\n",wow)        ;
    writefln("string : %s\n",wow)        ;
    writefln("hexadecimal : %x\n",wow)   ;
    writefln("octal : %o\n",wow)         ;
    writefln("decimal : %d\n",wow)       ;

}

unittest {
    import std.random ;
    import std.stdio ;
    immutable uint N = 65 ;
    ULogic!65 wow ;
    for(uint i = 0 ; i < N ; ++i){
      int tmp = uniform(0, 4); 
         
      if      (tmp == 0) wow[i] = LOGIC_X ;
      else if (tmp == 1) wow[i] = LOGIC_Z ;
      else if (tmp == 2) wow[i] = LOGIC_1 ;
      else if (tmp == 3) wow[i] = LOGIC_0 ;
      else   assert(0);

    }

    writefln("binary : %b\n",wow)        ;
    writefln("string : %s\n",wow)        ;
    writefln("hexadecimal : %x\n",wow)   ;
    writefln("octal : %o\n",wow)         ;
    writefln("decimal : %d\n",wow)       ;


}

unittest {

   import std.stdio ;

   Logic!1024 a ; 
   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_Z ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i].isZ()) ;

   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_X ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i].isX()) ;

   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_1 ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i] == LOGIC_1) ;

   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_0 ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i] == LOGIC_0) ;

}

unittest {

   import std.stdio ;

   ULogic!1024 a ; 
   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_Z ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i].isZ()) ;

   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_X ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i].isX()) ;

   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_1 ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i] == LOGIC_1) ;

   for(uint i = 0 ; i < 1024 ; ++i) a[i] = LOGIC_0 ;
   for(uint i = 0 ; i < 1024 ; ++i) assert(a[i] == LOGIC_0) ;

}


unittest {

   import std.stdio ;
   Logic!1 a = bin!q{Z} ;
   assert(a.isZ());
   assert(a.isX());

   // FIXME
   // assert(a != LOGIC_1);
   // assert(a != LOGIC_0);
}

unittest {

   alias Bit!8 array ;

   array[]  mem ;

   mem.length = 1024 ;
   mem.length = 2048 ;
   mem.length = 1024 ;

   Bit!8[string][]  hash ;

}

unittest {

   import std.stdio ;

   Bit!8 lsb = bin!q{00000000} ;
   Bit!8 msb = bin!q{11111111} ;
   Bit!16 concat = msb ~ lsb ;
   assert(concat == bin!q{1111111100000000});
   assert(concat >  bin!q{1000000001111111});
   assert(concat >= bin!q{1000000001111111});
   assert(concat != bin!q{1000000001111111});

   auto concat_1 = msb ~ lsb ;
   assert(concat_1 == bin!q{1111111100000000});
   assert(concat_1 >  bin!q{1000000001111111});
   assert(concat_1 >= bin!q{1000000001111111});
   assert(concat_1 != bin!q{1000000001111111});

   auto a = bin!q{10110011};
   auto b = bin!q{10011100};

   assert(a ~ b == bin!q{10110011_10011100});

}

unittest {

   UBit!8 lsb = bin!q{00000000} ;
   UBit!8 msb = bin!q{11111111} ;
   UBit!16 concat = msb ~ lsb ;
   assert(concat == bin!q{1111111100000000});
   assert(concat >  bin!q{1000000001111111});
   assert(concat >= bin!q{1000000001111111});
   assert(concat != bin!q{1000000001111111});

   auto concat_1 = msb ~ lsb ;
   assert(concat_1 == bin!q{1111111100000000});
   assert(concat_1 >  bin!q{1000000001111111});
   assert(concat_1 >= bin!q{1000000001111111});
   assert(concat_1 != bin!q{1000000001111111});
}

// concat ~ does not work for Logic/ULogic 

unittest {

   Logic!8 lsb = bin!q{11111111} ;
   Logic!8 msb = bin!q{11111111} ;
   auto concat = msb ~ lsb ;

}
 
unittest {

   ULogic!8 lsb = bin!q{11111111} ;
   ULogic!8 msb = bin!q{11111111} ;
   auto concat = msb ~ lsb ;

}

unittest {

   UBit!16 mBit    = bin!q{1111111111111111};

   UBit!8  mBit_8      = cast(UBit!8) mBit ;
   UBit!16 mBit_16     = cast(UBit!16) mBit ;
   ubyte    mBit_ubyte  = cast(ubyte) mBit ;
   uint     mBit_uint   = cast(uint) mBit ;
   ushort   mBit_ushort = cast(ushort) mBit ;
   ulong    mBit_ulong  = cast(ulong) mBit ;

   byte     mBit_byte   = cast(byte) mBit ;
   int      mBit_int    = cast(int) mBit ;
   short    mBit_short  = cast(short) mBit ;
   long     mBit_long   = cast(long) mBit ;
/*
   float    mBit_float  = cast(float)  mBit ;
   double   mBit_double = cast(double)  mBit ;
   real     mBit_real   = cast(double)  mBit ;
*/
}

unittest {

   Bit!16 mBit    = bin!q{1111111111111111};

   Bit!8  mBit_8      = cast(Bit!8) mBit ;
   Bit!16 mBit_16     = cast(Bit!16) mBit ;
   ubyte    mBit_ubyte  = cast(ubyte) mBit ;
   uint     mBit_uint   = cast(uint) mBit ;
   ushort   mBit_ushort = cast(ushort) mBit ;
   ulong    mBit_ulong  = cast(ulong) mBit ;

   byte     mBit_byte   = cast(byte) mBit ;
   int      mBit_int    = cast(int) mBit ;
   short    mBit_short  = cast(short) mBit ;
   long     mBit_long   = cast(long) mBit ;

}


unittest {

   Logic!16 mLogic    = bin!q{1111111111111111};

   Logic!8  mLogic_8      = cast(Logic!8) mLogic ;
   Logic!16 mLogic_16     = cast(Logic!16) mLogic ;
   ubyte    mLogic_ubyte  = cast(ubyte) mLogic ;
   uint     mLogic_uint   = cast(uint) mLogic ;
   ushort   mLogic_ushort = cast(ushort) mLogic ;
   ulong    mLogic_ulong  = cast(ulong) mLogic ;

   byte     mLogic_byte   = cast(byte) mLogic ;
   int      mLogic_int    = cast(int) mLogic ;
   short    mLogic_short  = cast(short) mLogic ;
   long     mLogic_long   = cast(long) mLogic ;

}

unittest {

   ULogic!16 mLogic    = bin!q{1111111111111111};

   ULogic!8  mLogic_8      = cast(ULogic!8) mLogic ;
   ULogic!16 mLogic_16     = cast(ULogic!16) mLogic ;
   ubyte    mLogic_ubyte  = cast(ubyte) mLogic ;
   uint     mLogic_uint   = cast(uint) mLogic ;
   ushort   mLogic_ushort = cast(ushort) mLogic ;
   ulong    mLogic_ulong  = cast(ulong) mLogic ;

   byte     mLogic_byte   = cast(byte) mLogic ;
   int      mLogic_int    = cast(int) mLogic ;
   short    mLogic_short  = cast(short) mLogic ;
   long     mLogic_long   = cast(long) mLogic ;

}


unittest {

   import std.complex ;
   import std.stdio ;

   alias  Bit!16 mtype ;

   mtype rBit_1 = hex!q{5} ;
   mtype iBit_1 = hex!q{5} ;
   auto c_1 = complex!(mtype) (rBit_1,iBit_1);

   mtype rBit_2 = hex!q{5} ;
   mtype iBit_2 = hex!q{5} ;
   auto c_2 = complex!(mtype) (rBit_2,iBit_2);

   { 
      auto c_3 = c_1 + c_2 ; 
      writefln("%f",c_3);
      writefln("%e",c_3);
      writefln("%s",c_3);
   }

   { 
      auto c_3 = c_1 - c_2 ; 
      writefln("%f",c_3);
      writefln("%e",c_3);
      writefln("%s",c_3);
   }

   { 
      auto c_3 = c_1 * c_2 ; 
      writefln("%f",c_3);
      writefln("%e",c_3);
      writefln("%s",c_3);
   }

   { 
      auto c_3 = c_1 / c_2 ; 
      writefln("%f",c_3);
      writefln("%s",c_3);
   }


}

unittest {

   import std.complex ;
   import std.stdio ;

   alias  UBit!16 mtype ;

   mtype rBit_1 = hex!q{5} ;
   mtype iBit_1 = hex!q{5} ;
   auto c_1 = complex!(mtype) (rBit_1,iBit_1);

   mtype rBit_2 = hex!q{5} ;
   mtype iBit_2 = hex!q{5} ;
   auto c_2 = complex!(mtype) (rBit_2,iBit_2);

   { 
      auto c_3 = c_1 + c_2 ; 
      writefln("%f",c_3);
      writefln("%e",c_3);
      writefln("%s",c_3);
   }

   { 
      auto c_3 = c_1 - c_2 ; 
      writefln("%f",c_3);
      writefln("%e",c_3);
      writefln("%s",c_3);
   }

   { 
      auto c_3 = c_1 * c_2 ; 
      writefln("%f",c_3);
      writefln("%e",c_3);
      writefln("%s",c_3);
   }

   { 
      auto c_3 = c_1 / c_2 ; 
      writefln("%f",c_3);
      writefln("%e",c_3);
      writefln("%s",c_3);
   }


}




unittest {

   import std.stdio ;

   Bit!8 msb = bin!q{11111111} ;
   Bit!72 concat = msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ;

   assert(concat == hex!q{ffffffffffffffffff});
   //assert(concat >  hex!q{ffff});
   //assert(concat >= hex!q{ffff});
   //assert(concat != hex!q{ffff});

   Bit!73  concat_1 = concat + concat ;
   Bit!144 concat_2 = concat * concat ;
            concat_2 = concat - concat ;
            concat_2 = concat | concat ;
            concat_2 = concat || concat ;
            concat_2 = concat & concat ;
            concat_2 = concat && concat ;
            concat_2 = concat ^ concat ;
            concat_2 = !concat ;
            concat_2 = ~concat ;
}

unittest {

   import std.stdio ;

   UBit!8 msb = bin!q{11111111} ;
   UBit!72 concat = msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ;

   assert(concat == hex!q{ffffffffffffffffff});
   //assert(concat >  hex!q{ffff});
   //assert(concat >= hex!q{ffff});
   //assert(concat != hex!q{ffff});

   UBit!73  concat_1 = concat + concat ;
   UBit!144 concat_2 = concat * concat ;
             concat_2 = concat - concat ;
             concat_2 = concat | concat ;
             concat_2 = concat || concat ;
             concat_2 = concat & concat ;
             concat_2 = concat && concat ;
             concat_2 = concat ^ concat ;
             concat_2 = !concat ;
             concat_2 = ~concat ;
}

unittest {

   import std.stdio ;

   Logic!8 msb = bin!q{11111111} ;
   Logic!72 concat = msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ;

   assert(concat == hex!q{ffffffffffffffffff});
   //assert(concat >  hex!q{ffff});
   //assert(concat >= hex!q{ffff});
   //assert(concat != hex!q{ffff});

   Logic!73  concat_1 = concat + concat ;
   Logic!144 concat_2 = concat * concat ;
            concat_2 = concat - concat ;
            concat_2 = concat | concat ;
            concat_2 = concat || concat ;
            concat_2 = concat & concat ;
            concat_2 = concat && concat ;
            concat_2 = concat ^ concat ;
            concat_2 = !concat ;
            concat_2 = ~concat ;
}

unittest {

   import std.stdio ;

   ULogic!8 msb = bin!q{11111111} ;
   ULogic!72 concat = msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ~ msb ;

   assert(concat == hex!q{ffffffffffffffffff});
   //assert(concat >  hex!q{ffff});
   //assert(concat >= hex!q{ffff});
   //assert(concat != hex!q{ffff});

   ULogic!73  concat_1 = concat + concat ;
   ULogic!144 concat_2 = concat * concat ;
             concat_2 = concat - concat ;
             concat_2 = concat | concat ;
             concat_2 = concat || concat ;
             concat_2 = concat & concat ;
             concat_2 = concat && concat ;
             concat_2 = concat ^ concat ;
             concat_2 = !concat ;
             concat_2 = ~concat ;
}

unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 16 ;
   static enum M = N*2 ;

   static UBit!N[] nBit ;
   static UBit!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(UBit!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   //for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   //for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  



} 

unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 65 ;
   static enum M = N*2 ;

   static UBit!N[] nBit ;
   static UBit!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(UBit!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  

} 

unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 16 ;
   static enum M = N*2 ;

   static Bit!N[] nBit ;
   static Bit!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(Bit!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  

} 

unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 65 ;
   static enum M = N*2 ;

   static Bit!N[] nBit ;
   static Bit!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(Bit!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  

} 

unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 16 ;
   static enum M = N*2 ;

   static ULogic!N[] nBit ;
   static ULogic!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(ULogic!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   //for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   //for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  

} 

unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 65 ;
   static enum M = N*2 ;

   static ULogic!N[] nBit ;
   static ULogic!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(ULogic!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  

} 


unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 16 ;
   static enum M = N*2 ;

   static Logic!N[] nBit ;
   static Logic!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(Logic!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  

} 

unittest {

   import std.random ;
   import std.math ;
   import std.stdio ;

   static enum N = 65 ;
   static enum M = N*2 ;

   static Logic!N[] nBit ;
   static Logic!M[] mBit ;

   nBit.length = 1024 ; 
   mBit.length = nBit.length ; 

   for(uint i = 0 ; i < 1024 ; ++i){
      nBit[i] = cast(Logic!N)(cast(ushort)uniform(0, 65535)) ;
   } 

   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] + nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] - nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] * nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] | nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] || nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] & nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] && nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] ^ nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = !nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = ~nBit[i] ;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >> 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] << 1;  
   for(uint i = 0 ; i < 1024 ; ++i) mBit[i] = nBit[i] >>> 1;  

} 



unittest {

   Bit!16 [1024] a ;
   Bit!16 [1024] b ;
   Bit!17 [1024] y ;

   foreach(ushort i ; a){
      a[i] = i ;
      b[i] = i ;
      y[i] = a[i] + b[i] ;
      y[i] = a[i] - b[i] ;  
      y[i] = a[i] | b[i] ;  
      y[i] = a[i] || b[i] ;  
      y[i] = a[i] & b[i] ;  
      y[i] = a[i] && b[i] ;  
      y[i] = a[i] ^ b[i] ;  
      y[i] = !b[i] ;  
      y[i] = ~b[i] ;  
      y[i] = b[i] >> 1;  
      y[i] = b[i] << 1;  
      y[i] = b[i] >>> 1;  
   }

}

unittest {

   UBit!16 [1024] a ;
   UBit!16 [1024] b ;
   UBit!17 [1024] y ;

   foreach(ushort i ; a){
      a[i] = i ;
      b[i] = i ;
      y[i] = a[i] + b[i] ;
      y[i] = a[i] - b[i] ;  
      y[i] = a[i] | b[i] ;  
      y[i] = a[i] || b[i] ;  
      y[i] = a[i] & b[i] ;  
      y[i] = a[i] && b[i] ;  
      y[i] = a[i] ^ b[i] ;  
      y[i] = !b[i] ;  
      y[i] = ~b[i] ;  
      y[i] = b[i] << 1;  
      y[i] = b[i] >>> 1;  
   }

}

unittest {

   Logic!16 [1024] a ;
   Logic!16 [1024] b ;
   Logic!17 [1024] y ;

   foreach(Logic!16 i ; a){
      a[cast(ulong)i] = i ;
      b[cast(ulong)i] = i ;
      y[cast(ulong)i] = a[cast(ulong)i] + b[cast(ulong)i] ;
      y[cast(ulong)i] = a[cast(ulong)i] - b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] | b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] || b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] & b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] && b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] ^ b[cast(ulong)i] ;  
      y[cast(ulong)i] = !b[cast(ulong)i] ;  
      y[cast(ulong)i] = ~b[cast(ulong)i] ;  
      y[cast(ulong)i] = b[cast(ulong)i] >> 1;  
      y[cast(ulong)i] = b[cast(ulong)i] << 1;  
   }

}

unittest {

   ULogic!16 [1024] a ;
   ULogic!16 [1024] b ;
   ULogic!17 [1024] y ;

   foreach(ULogic!16 i ; a){
      a[cast(ulong)i] = i ;
      b[cast(ulong)i] = i ;
      y[cast(ulong)i] = a[cast(ulong)i] + b[cast(ulong)i] ;
      y[cast(ulong)i] = a[cast(ulong)i] - b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] | b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] || b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] & b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] && b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] ^ b[cast(ulong)i] ;  
      y[cast(ulong)i] = !b[cast(ulong)i] ;  
      y[cast(ulong)i] = ~b[cast(ulong)i] ;  
      y[cast(ulong)i] = b[cast(ulong)i] << 1;  
      y[cast(ulong)i] = b[cast(ulong)i] >>> 1;  
   }

}

unittest {


}


////////////////////////////////
unittest {

   Bit!64 [1024] a ;
   Bit!64 [1024] b ;
   Bit!65 [1024] y ;

   foreach(ulong i ; a){
      a[i] = i ;
      b[i] = i ;
      y[i] = a[i] + b[i] ;
      y[i] = a[i] - b[i] ;  
      y[i] = a[i] | b[i] ;  
      y[i] = a[i] || b[i] ;  
      y[i] = a[i] & b[i] ;  
      y[i] = a[i] && b[i] ;  
      y[i] = a[i] ^ b[i] ;  
      y[i] = !b[i] ;  
      y[i] = ~b[i] ;  
      y[i] = b[i] >> 1;  
      y[i] = b[i] << 1;  
      y[i] = b[i] >>> 1;  
   }

}

unittest {

   UBit!64 [1024] a ;
   UBit!64 [1024] b ;
   UBit!65 [1024] y ;

   foreach(ulong i ; a){
      a[i] = i ;
      b[i] = i ;
      y[i] = a[i] + b[i] ;
      y[i] = a[i] - b[i] ;  
      y[i] = a[i] | b[i] ;  
      y[i] = a[i] || b[i] ;  
      y[i] = a[i] & b[i] ;  
      y[i] = a[i] && b[i] ;  
      y[i] = a[i] ^ b[i] ;  
      y[i] = !b[i] ;  
      y[i] = ~b[i] ;  
      y[i] = b[i] << 1;  
      y[i] = b[i] >>> 1;  
   }

}

unittest {

   Logic!64 [1024] a ;
   Logic!64 [1024] b ;
   Logic!65 [1024] y ;

   foreach(Logic!64 i ; a){
      a[cast(ulong)i] = i ;
      b[cast(ulong)i] = i ;
      y[cast(ulong)i] = a[cast(ulong)i] + b[cast(ulong)i] ;
      y[cast(ulong)i] = a[cast(ulong)i] - b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] | b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] || b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] & b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] && b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] ^ b[cast(ulong)i] ;  
      y[cast(ulong)i] = !b[cast(ulong)i] ;  
      y[cast(ulong)i] = ~b[cast(ulong)i] ;  
      y[cast(ulong)i] = b[cast(ulong)i] >> 1;  
      y[cast(ulong)i] = b[cast(ulong)i] << 1;  
   }

}

unittest {

   ULogic!64 [1024] a ;
   ULogic!64 [1024] b ;
   ULogic!65 [1024] y ;

   foreach(ULogic!64 i ; a){
      a[cast(ulong)i] = i ;
      b[cast(ulong)i] = i ;
      y[cast(ulong)i] = a[cast(ulong)i] + b[cast(ulong)i] ;
      y[cast(ulong)i] = a[cast(ulong)i] - b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] | b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] || b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] & b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] && b[cast(ulong)i] ;  
      y[cast(ulong)i] = a[cast(ulong)i] ^ b[cast(ulong)i] ;  
      y[cast(ulong)i] = !b[cast(ulong)i] ;  
      y[cast(ulong)i] = ~b[cast(ulong)i] ;  
      y[cast(ulong)i] = b[cast(ulong)i] << 1;  
      y[cast(ulong)i] = b[cast(ulong)i] >>> 1;  
   }

}

unittest {

   import std.stdio ;

   {
      scope     Bit!65 p = hex!q{ffff};
      scope     Bit!65 q = hex!q{ffff};
      scope     Bit!66 y = p + q ;
   }
   
   {
      scope     Bit!16 p = hex!q{ffff};
      scope     Bit!16 q = hex!q{ffff};
      scope     Bit!17 y = p + q ;
   }
   
   {
      scope     UBit!65 p = hex!q{ffff};
      scope     UBit!65 q = hex!q{ffff};
      scope     UBit!66 y = p + q ;
   }
   
   {
      scope     UBit!16 p = hex!q{ffff};
      scope     UBit!16 q = hex!q{ffff};
      scope     UBit!17 y = p + q ;
   }
   
   {
      scope     Logic!65 p = hex!q{ffff};
      scope     Logic!65 q = hex!q{ffff};
      scope     Logic!66 y = p + q ;
   }
   
   {
      scope     Logic!16 p = hex!q{ffff};
      scope     Logic!16 q = hex!q{ffff};
      scope     Logic!17 y = p + q ;
   }
   
   {
      scope     ULogic!65 p = hex!q{ffff};
      scope     ULogic!65 q = hex!q{ffff};
      scope     ULogic!66 y = p + q ;
   }
   
   {
      scope     ULogic!16 p = hex!q{ffff};
      scope     ULogic!16 q = hex!q{ffff};
      scope     ULogic!17 y = p + q ;
   }



}

/*

unittest {

   import std.stdio ;

   {
      immutable Bit!65 p ;
      immutable Bit!65 q ;
      immutable Bit!66 y = p + q ;
   }
   
   {
      immutable Bit!16 p ;
      immutable Bit!16 q ;
      immutable Bit!17 y = p + q ;
   }
   
   {
      immutable UBit!65 p ;
      immutable UBit!65 q ;
      immutable UBit!66 y = p + q ;
   }
   
   {
      immutable UBit!16 p ;
      immutable UBit!16 q ;
      immutable UBit!17 y = p + q ;
   }
   
   {
      immutable Logic!65 p ;
      immutable Logic!65 q ;
      immutable Logic!66 y = p + q ;
   }
   
   {
      immutable Logic!16 p ;
      immutable Logic!16 q ;
      immutable Logic!17 y = p + q ;
   }
   
   {
      immutable ULogic!65 p ;
      immutable ULogic!65 q ;
      immutable ULogic!66 y = p + q ;
   }
   
   {
      immutable ULogic!16 p ;
      immutable ULogic!16 q ;
      immutable ULogic!17 y = p + q ;
   }



}
*/


unittest {

   import std.stdio;
   import std.algorithm;

   size_t a = 100 ;
   size_t b = 200 ;

   size_t y1 = max(a,b) ;
   size_t y2 = min(a,b) ;

   writefln("%d",y1);
   writefln("%d",y2);
   writefln("%s",y1);
   writefln("%s",y2);
   writefln("%x",y1);
   writefln("%x",y2);
   writefln("%b",y1);
   writefln("%b",y2);
   writefln("%o",y1);
   writefln("%o",y2);

}

 unittest {
 
    import std.stdio ;
 
    Logic!4 x = bin!q{1101};
    x.reverse();
 
    Logic!4 y = bin!q{1011};
    assert(x.reverse() == y);
 
 }

 unittest {
 
    import std.stdio ;
 
    ULogic!4 x = bin!q{1101};
    x.reverse();
 
    Logic!4 y = bin!q{1011};
    assert(x.reverse == y);
 }

 unittest {
 
    import std.stdio ;
 
    Bit!4 x = bin!q{1101};
    x.reverse();
 
    Logic!4 y = bin!q{1011};
    assert(x.reverse == y);
 
 }

 unittest {
 
    import std.stdio ;
 
    UBit!4 x = bin!q{1101};
    auto z = x.reverse();
 
    Logic!4 y = bin!q{1011};
    // FIXME
    assert(z == y);
 
 }

unittest {

   import std.stdio ;

   Bit!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   writefln("%d",x);
   writefln("%s",x);
   writefln("%x",x);
   writefln("%b",x);
   writefln("%o",x);

   x.reverse();
   x.randomize();

}

unittest {

   import std.stdio ;

   UBit!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   writefln("%d",x);
   writefln("%s",x);
   writefln("%x",x);
   writefln("%b",x);
   writefln("%o",x);

   x.reverse();
   x.randomize();

}

unittest {

   import std.stdio ;

   Logic!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   writefln("%d",x);
   writefln("%s",x);
   writefln("%x",x);
   writefln("%b",x);
   writefln("%o",x);

   x.reverse();
   x.randomize();

}

unittest {

   import std.stdio ;

   ULogic!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   writefln("%d",x);
   writefln("%s",x);
   writefln("%x",x);
   writefln("%b",x);
   writefln("%o",x);

   x.reverse();
   x.randomize();

}

unittest {

   import std.stdio ;

   Bit!1 x = bin!q{1};
   Bit!1 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   UBit!1 x = bin!q{1};
   UBit!1 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   Logic!1 x = bin!q{1};
   Logic!1 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   ULogic!1 x = bin!q{1};
   ULogic!1 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}



////////////

unittest {

   import std.stdio ;

   Bit!16 x = hex!q{aaaa};
   Bit!16 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   UBit!16 x = hex!q{aaaa};
   UBit!16 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   Logic!16 x = hex!q{aaaa};
   Logic!16 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   ULogic!16 x = hex!q{aaaa};
   ULogic!16 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

////////

unittest {

   import std.stdio ;

   Bit!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   Bit!128 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   UBit!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   UBit!128 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   Logic!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   Logic!128 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

unittest {

   import std.stdio ;

   ULogic!128 x = hex!q{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa};
   ULogic!128 y ;
   y += x ;
   y -= x ;
   //y *= x ;
   //y /= x ;

}

///////

unittest {

   import std.stdio ;

{
   uint a = hex!q{aa} ;
   a = bin!q{11111111};

   writefln("%d",a);
   writefln("%s",a);
   writefln("%x",a);
   writefln("%b",a);
   writefln("%o",a);

   Bit!32 b = hex!q{aa} ;

   Bit!33 y1 = a + b ; 
           y1 = a - b ; 
           y1 = a | b ; 
           y1 = a || b ; 
           y1 = a & b ; 
           y1 = a && b ; 
}

{
   //ubyte a = hex!q{aa} ;
   ubyte a = 0xaa ;
   //a = hex!q{11111111};

   writefln("%d",a);
   writefln("%s",a);
   writefln("%x",a);
   writefln("%b",a);
   writefln("%o",a);

   Bit!32 b = hex!q{a} ;

   Bit!33 y1 = a + b ; 
           y1 = a - b ; 
           y1 = a | b ; 
           y1 = a || b ; 
           y1 = a & b ; 
           y1 = a && b ; 
}

{
   //ubyte a = hex!q{aa} ;
   ushort a = 0xaa ;
   //a = hex!q{11111111};

   writefln("%d",a);
   writefln("%s",a);
   writefln("%x",a);
   writefln("%b",a);
   writefln("%o",a);

   Bit!32 b = hex!q{a} ;

   Bit!33 y1 = a + b ; 
           y1 = a - b ; 
           y1 = a | b ; 
           y1 = a || b ; 
           y1 = a & b ; 
           y1 = a && b ; 
}



}

///////////////////
unittest {

   import std.stdio ;

{
   uint a = hex!q{aa} ;
   a = bin!q{11111111};

   writefln("%d",a);
   writefln("%s",a);
   writefln("%x",a);
   writefln("%b",a);
   writefln("%o",a);

   UBit!32 b = hex!q{aa} ;

   UBit!33 y1 = a + b ; 
           y1 = a - b ; 
           y1 = a | b ; 
           y1 = a || b ; 
           y1 = a & b ; 
           y1 = a && b ; 
}

{
   //ubyte a = hex!q{aa} ;
   ubyte a = 0xaa ;
   //a = hex!q{11111111};

   writefln("%d",a);
   writefln("%s",a);
   writefln("%x",a);
   writefln("%b",a);
   writefln("%o",a);

   UBit!32 b = hex!q{a} ;

   UBit!33 y1 = a + b ; 
           y1 = a - b ; 
           y1 = a | b ; 
           y1 = a || b ; 
           y1 = a & b ; 
           y1 = a && b ; 
}

{
   //ubyte a = hex!q{aa} ;
   ushort a = 0xaa ;
   //a = hex!q{11111111};

   writefln("%d",a);
   writefln("%s",a);
   writefln("%x",a);
   writefln("%b",a);
   writefln("%o",a);

   UBit!32 b = hex!q{a} ;

   UBit!33 y1 = a + b ; 
           y1 = a - b ; 
           y1 = a | b ; 
           y1 = a || b ; 
           y1 = a & b ; 
           y1 = a && b ; 
}



}

///////////////////////

unittest {

   import std.stdio ;

   {
      uint a = hex!q{aa} ;
      a = bin!q{11111111};
   
      writefln("%d",a);
      writefln("%s",a);
      writefln("%x",a);
      writefln("%b",a);
      writefln("%o",a);
   
      Logic!32 b = hex!q{aa} ;
   
      Logic!33 y1 = a + b ; 
              y1 = a - b ; 
              //y1 = a | b ; 
              y1 = a || b ; 
              //y1 = a & b ; 
              y1 = a && b ; 
   }
   
   {
      //ubyte a = hex!q{aa} ;
      ubyte a = 0xaa ;
      //a = hex!q{11111111};
   
      writefln("%d",a);
      writefln("%s",a);
      writefln("%x",a);
      writefln("%b",a);
      writefln("%o",a);
   
      Logic!32 b = hex!q{a} ;
   
      Logic!33 y1 = a + b ; 
              y1 = a - b ; 
              //y1 = a | b ; 
              y1 = a || b ; 
              //y1 = a & b ; 
              y1 = a && b ; 
   }
   
   {
      //ubyte a = hex!q{aa} ;
      ushort a = 0xaa ;
      //a = hex!q{11111111};
   
      writefln("%d",a);
      writefln("%s",a);
      writefln("%x",a);
      writefln("%b",a);
      writefln("%o",a);
   
      Logic!32 b = hex!q{a} ;
   
      Logic!33 y1 = a + b ; 
              y1 = a - b ; 
              //y1 = a | b ; 
              y1 = a || b ; 
              //y1 = a & b ; 
              y1 = a && b ; 
   }



}

///////////////////
unittest {

   import std.stdio ;

   {
      uint a = hex!q{aa} ;
      a = bin!q{11111111};
   
      writefln("%d",a);
      writefln("%s",a);
      writefln("%x",a);
      writefln("%b",a);
      writefln("%o",a);
   
      ULogic!32 b = hex!q{aa} ;
   
      ULogic!33 y1 = a + b ; 
              y1 = a - b ; 
              //y1 = a | b ; 
              y1 = a || b ; 
              //y1 = a & b ; 
              y1 = a && b ; 
   }
   
   {
      //ubyte a = hex!q{aa} ;
      ubyte a = 0xaa ;
      //a = hex!q{11111111};
   
      writefln("%d",a);
      writefln("%s",a);
      writefln("%x",a);
      writefln("%b",a);
      writefln("%o",a);
   
      ULogic!32 b = hex!q{a} ;
   
      ULogic!33 y1 = a + b ; 
              y1 = a - b ; 
              //y1 = a | b ; 
              y1 = a || b ; 
              //y1 = a & b ; 
              y1 = a && b ; 
   }
   
   {
      //ubyte a = hex!q{aa} ;
      ushort a = 0xaa ;
      //a = hex!q{11111111};
   
      writefln("%d",a);
      writefln("%s",a);
      writefln("%x",a);
      writefln("%b",a);
      writefln("%o",a);
   
      ULogic!32 b = hex!q{a} ;
   
      ULogic!33 y1 = a + b ; 
              y1 = a - b ; 
              //y1 = a | b ; 
              y1 = a || b ; 
              //y1 = a & b ; 
              y1 = a && b ; 
   }



}

///////////////////////


unittest {

   {
   
      Bit!16 x = hex!q{100} ;
      
      Bit!32 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{300});
   }
   
   {
   
      Bit!65 x = hex!q{1} ;
      
      Bit!128 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{200});
   }
   
   {
   
      UBit!16 x = hex!q{100} ;
      
      UBit!32 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{300});
   }
   
   {
   
      UBit!65 x = hex!q{1} ;
      
      UBit!128 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{200});
   }
   
   
   {
   
      Logic!16 x = hex!q{100} ;
      
      Logic!32 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{300});
   }
   
   {
   
      Logic!65 x = hex!q{1} ;
      
      Logic!128 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{200});
   }
   
   {
   
      ULogic!16 x = hex!q{100} ;
      
      ULogic!32 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{300});
   }
   
   {
   
      ULogic!65 x = hex!q{1} ;
      
      ULogic!128 y = ( x == hex!q{1}) ? hex!q{200} : hex!q{300} ;
      assert(y == hex!q{200});
   }

}

////////////////////////

unittest {

   import std.stdio ;

   Logic!1 a = true  ;
   Logic!1 b = false ;
   Logic!1 y = false ;

   assert(a);
   assert(!b);
   assert(!y);
   
   assert(!(a & b));

   assert(a & ~b);

}

// unittest {
// 
//    import std.stdio ;
// 
//    bit a = true  ;
//    bit b = false ;
//    bit y = false ;
// 
//    assert(a);
//    assert(!b);
//    assert(!y);
//    
//    assert(!(a & b));
// 
//    writefln(" Err :: There is a bug for compound boolean (logic) operations");
// 
//    assert((a & (!b)));
// 
// }



unittest {

   import std.stdio ;

   Bit!16[]  b = new Bit!16[20] ; 
   Bit!128[] c = new Bit!128[20] ; 
   delete(b) ;
   delete(c) ;

// Associative arrays :
   UBit!32 [string]  address_map = [ "reset_ctl_reg" : cast(UBit!32)0x0,
                                      "clock_ctl_reg" : cast(UBit!32)0x1,
                                      "modem_ctl_reg" : cast(UBit!32)0x2,
                                      "moden_ctl_reg" : cast(UBit!32)0x3,
                                      "modeo_ctl_reg" : cast(UBit!32)0x4,
                                      "modep_ctl_reg" : cast(UBit!32)0x5,
                                      "modeq_ctl_reg" : cast(UBit!32)0x6,
                                      "moder_ctl_reg" : cast(UBit!32)0x7,
                                      "modes_ctl_reg" : cast(UBit!32)0x8
                                    ];

   
   writefln("%s",address_map);

   address_map["data1_val_reg"] = cast(UBit!32)0x9  ;
   address_map["data2_val_reg"] = cast(UBit!32)0xa  ;
   address_map["data3_val_reg"] = cast(UBit!32)0xb  ;
   address_map["data4_val_reg"] = cast(UBit!32)0xc  ;
   address_map["data5_val_reg"] = cast(UBit!32)0xd  ;
   address_map["data6_val_reg"] = cast(UBit!32)0xe  ;
   address_map["data7_val_reg"] = cast(UBit!32)0xf  ;
   address_map["data8_val_reg"] = cast(UBit!32)0x10 ;
   
   writefln("%s",address_map);

   UBit!32 [string]  address_map_temp = address_map ;

   writefln("%s",address_map_temp);

}


