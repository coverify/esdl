module esdl.cover.wild;
import esdl.data.bvec;
import std.traits: isIntegral;

struct Wildcard(uint LEN) if (LEN > 0)
{
  enum uint BITLEN = LEN;
  enum uint BYTES = (LEN + 7)/8;

  ubyte[BYTES] _aval;		// bits to match
  ubyte[BYTES] _bval;		// do not care bits are 0

  this(string str) {
    uint n = 0;
    foreach (c; str) {
      n += 1;
      uint byten = (LEN - n)/8;
      if (c == '_') {n -= 1; continue;}
      else {
	if (n > LEN) {
	  import std.format: format;
	  assert (false, format("Given value %s is not of size %d", str, LEN));
	}
	_aval[byten] *= 2;
	_bval[byten] *= 2;
	if (c == '?' ||
	    c == 'X' || c == 'x' ||
	    c == 'Z' || c == 'z') continue;
	else if (c == '0') {
	  _aval[byten] += 0;
	  _bval[byten] += 1;
	}
	else if (c == '1') {
	  _aval[byten] += 1;
	  _bval[byten] += 1;
	}
	else assert (false, "Illegal Wild pattern: " ~ str);
      }
    }
    if (n != LEN) {
      import std.format: format;
      assert (false, format("Given value %s is not of size %d", str, LEN));
    }
  }

  this(ulvec!LEN vec) {
    for (uint n; n!= BYTES; n += 1) {
      _bval[n] = cast(ubyte) ~(vec.bvalBytes()[n]);
      _aval[n] = vec.avalBytes()[n] & _bval[n];
    }
  }
  
  string toString() {
    char[] str;
    str.length = LEN;
    for (uint n=0; n != LEN; n += 1) {
      uint byten = n/8;
      uint bitn = n%8;

      bool abit = (((_aval[byten] >> bitn) % 2) == 1);
      bool bbit = (((_bval[byten] >> bitn) % 2) == 1);

      if (bbit is false) {
	if (abit) assert (false, "Illegal Value of the Wildcard");
	else str[$-1-n] = '?';
      }
      else if (abit) {
	str[$-1-n] = '1';
      }
      else str[$-1-n] = '0';
    }
    return cast(string) str;
  }

  bool opEquals(T)(T other) if (isBitVector!T) {
    static if (T.SIZE != LEN) return false;
    else {
      const (ubyte)[] otherb = other.aValBytes();
      assert (otherb.length == _aval.length);
      for (uint n = 0; N != BYTES; n += 1) {
	if ((otherb[n] & _bval[n]) == _aval[n]) continue;
	else return false;
      }
      return true;
    }
  }

  bool opEquals(T)(T other) if (isIntegral!T) { // Assume little-endian
    static if (T.sizeof * 8 != LEN) return false;
    else {
      union U {
	T val;
	ubyte[T.sizeof] otherb;
      }
      U uu;
      uu.val = other;
      assert (uu.otherb.length == _aval.length);
      for (uint n = 0; n != BYTES; n += 1) {
	if ((uu.otherb[n] & _bval[n]) == _aval[n]) continue;
	else return false;
      }
      return true;
    }
  }


}
