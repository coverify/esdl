module esdl.cover.wild;
import esdl.data.bvec;
import std.traits: isIntegral;

struct Wildcard(T)
{

  static if (isIntegral!T) enum size_t BITNUM = T.sizeof * 8;
  static if (isBitVector!T) enum size_t BITNUM = T.SIZE;
  
  T _aval = 0;		// bits to match
  T _bval = 0;		// do not care bits are 0

  
  bool checkHit(T val) {
    return ((val & _bval) == _aval);
  }
  
  this(string str) {
    T bitval = (cast(T) 1) << (BITNUM-1);
    uint n = 0;
    foreach (c; str) {
      n += 1;
      if (c == '_') {n -= 1; continue;}
      else {
	if (n > BITNUM) {
	  import std.format: format;
	  assert (false, format("Given value %s is not of size %d", str, BITNUM));
	}
	if (c == '0') {
	  _bval |= bitval;
	}
	else if (c == '1') {
	  _aval |= bitval;
	  _bval |= bitval;
	}
	else if (!(c == '?' ||
		   c == 'X' || c == 'x' ||
		   c == 'Z' || c == 'z')) {
	  assert (false, "Illegal Wild pattern: " ~ str);
	}
      }
      bitval >>>= 1;
    }
    if (n != BITNUM) {
      import std.format: format;
      assert (false, format("Given value %s is not of size %d", str, BITNUM));
    }
  }

  this(ulvec!BITNUM vec) {

    if (isBitVector!T) {
      _aval = vec.getValueVec();
      _bval = vec.getMetaVec();
    }

    else {
      _aval = vec.getValueVec()[0];
      _bval = vec.getMetaVec()[0];
    }
  }
  
  // string toString() {
  //   char[] str;
  //   str.length = LEN;
  //   for (uint n=0; n != LEN; n += 1) {
  //     uint byten = n/8;
  //     uint bitn = n%8;

  //     bool abit = (((_aval[byten] >> bitn) % 2) == 1);
  //     bool bbit = (((_bval[byten] >> bitn) % 2) == 1);

  //     if (bbit is false) {
  // 	if (abit) assert (false, "Illegal Value of the Wildcard");
  // 	else str[$-1-n] = '?';
  //     }
  //     else if (abit) {
  // 	str[$-1-n] = '1';
  //     }
  //     else str[$-1-n] = '0';
  //   }
  //   return cast(string) str;
  // }

  // bool opEquals(T)(T other) if (isBitVector!T) {
  //   static if (T.SIZE != LEN) return false;
  //   else {
  //     const (ubyte)[] otherb = other.aValBytes();
  //     assert (otherb.length == _aval.length);
  //     for (uint n = 0; N != BYTES; n += 1) {
  // 	if ((otherb[n] & _bval[n]) == _aval[n]) continue;
  // 	else return false;
  //     }
  //     return true;
  //   }
  // }

  // bool opEquals(T)(T other) if (isIntegral!T) { // Assume little-endian
  //   static if (T.sizeof * 8 != LEN) return false;
  //   else {
  //     union U {
  // 	T val;
  // 	ubyte[T.sizeof] otherb;
  //     }
  //     U uu;
  //     uu.val = other;
  //     assert (uu.otherb.length == _aval.length);
  //     for (uint n = 0; n != BYTES; n += 1) {
  // 	if ((uu.otherb[n] & _bval[n]) == _aval[n]) continue;
  // 	else return false;
  //     }
  //     return true;
  //   }
  // }


}
