// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2019
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.data.packer;

import esdl.data.bvec;
import esdl.base.core: SimTime;
import core.bitop: bt, bts, btr;
import std.range: ElementType;

import std.traits;

struct Packer
{
  template BitCount(T) {
    static if (isBitVector!T)
      static if (T.IS4STATE)
	enum size_t BitCount = T.SIZE * 2;
      else
	enum size_t BitCount = T.SIZE;
    else static if (is (T: bool))
      enum size_t BitCount = 1;
    else
      enum size_t BitCount = 8 * T.sizeof;
  }
  
  private size_t _unpackIter;
  size_t unpackIter() {
    return _unpackIter;
  }

  private size_t _packIter;
  size_t packIter() {
    return _packIter;
  }

  alias _packIter opDollar;

  size_t* ptr;

  enum bitsPerSizeT = ulong.sizeof * 8;

  const size_t dim() {
    return (_packIter + (bitsPerSizeT-1)) / bitsPerSizeT;
  }

  const size_t length() {
    return _packIter;
  }

  size_t length(size_t newIter) {
    if (newIter != _packIter) {
      size_t olddim = dim;
      size_t newdim = (newIter + (bitsPerSizeT-1)) / bitsPerSizeT;
      if (newdim != olddim) {
        auto a = ptr[0 .. olddim];
        a.length = newdim;
        ptr = a.ptr;
        if (newIter & (bitsPerSizeT-1)) {
          ptr[newdim - 1] &= ~(~0L << (newIter & (bitsPerSizeT-1)));
        }
      }
      _packIter = newIter;
    }
    return _packIter;
  }

  T get(T)(size_t i) const {
    static assert(BitCount!T*(64/BitCount!T) == 64);
    static if (isBoolean!T) {
      return opIndex(i);
    }
    else {
      assert(i * BitCount!T < _packIter);
      size_t d = (i * BitCount!T)/64; // which word
      size_t r = (i * BitCount!T)%64; // which part of the word
      ulong word = ptr[d];
      static if (isIntegral!T)
	return cast(T) (word >> r);
      else
	return (word >> r).toBitVec!T;
    }
  }

  bool opIndex(size_t i) const {
    assert(i < _packIter);
    if (bt(ptr, i)) return true;
    else             return false;
  }

  bool opIndexAssign()(bool b, size_t i) {
    assert(i < _packIter);
    if (b)       bts(ptr, i);
    else         btr(ptr, i);
    return b;
  }

  auto dup() const {
    Packer p;
    auto pp = ptr[0 .. dim].dup;
    p.ptr = pp.ptr;
    p._packIter = _packIter;
    p._unpackIter = _unpackIter;
    return p;
  }

  auto opCatAssign(bool BIGENDIAN=false, T)(T t, size_t count = -1)
    if (isBoolean!T || isIntegral!T || isBitVector!T || isSomeChar!T) {
      static if (isBoolean!T) {
	alias UBit!(1) V;
	V v = t;
      }
      else static if(isIntegral!T || isSomeChar!T) {
	alias V = UBit!(BitCount!T);
	V v = t;
      }
      else {
        alias V = T;
        alias v = t;
      }
      size_t bits;
      if(count == -1) {
	bits = V.SIZE;
      }
      else {
	assert(count <= V.SIZE);
	bits = count;
      }
      length = _packIter + bits;
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

  T read(T)(size_t count = -1, bool bigEndian=false)
    if(isBoolean!T || isIntegral!T || isBitVector!T || isSomeChar!T) {
      static if(isBoolean!T)     alias UBit!(1) V;
      else static if(isIntegral!T || isSomeChar!T) alias UBit!(BitCount!T) V;
      else alias T V;
      size_t bitCount;
      if(count == -1) {
	bitCount = V.SIZE;
      }
      else {
	assert(count <= V.SIZE);
	bitCount = count;
      }
      assert(_packIter-_unpackIter >= bitCount);
      V v;
      if(bigEndian) {
        for (size_t i=0; i != bitCount; ++i) {
          v[$-i-1] = this[_unpackIter+i];
        }
      }
      else {
        for (size_t i=0; i != bitCount; ++i) {
          v[i] = this[_unpackIter+i];
        }
      }
      return cast(T) v;
    }
  
  void skip(size_t count) {
    if (_unpackIter > _packIter - count)
      assert(false);
    _unpackIter += count;
  }

  void pack_(T)(T t, size_t count, bool bigEndian)
    if(isBoolean!T || isIntegral!T ||
       (isBitVector!T && !T.IS4STATE) || isSomeChar!T) {
      if(bigEndian) {
        this.opCatAssign!true(t, count);
      }
      else {
        this.opCatAssign(t, count);
      }
    }

  void pack_(T)(T t, size_t count, bool bigEndian)
    if(isBitVector!T && T.IS4STATE) {
      this.pack_(t.aVal, count, bigEndian);
      this.pack_(t.bVal, count, bigEndian);
    }
  
  void unpack_(T)(ref T t, size_t count, bool bigEndian)
    if(isBoolean!T || isIntegral!T ||
       (isBitVector!T && !T.IS4STATE) || isSomeChar!T) {
      size_t bitCount = BitCount!T;
      t = read!T(count, bigEndian);
      _unpackIter += bitCount;
    }

  void unpack_(T)(ref T t, size_t count, bool bigEndian)
    if(isBitVector!T && T.IS4STATE) {
      _bvec!(T.ISSIGNED, false, T.SIZE) aval;
      _bvec!(T.ISSIGNED, false, T.SIZE) bval;
      this.unpack(aval, count, bigEndian);
      t.setAval(aval);
      this.unpack(bval, count, bigEndian);
      t.setBval(bval);
    }

  public void pack_(T)(T arr, size_t count = -1, bool bigEndian=false)
    if (isArray!T) {
      alias E = ElementType!T;
      if (count == -1) {
	foreach (e; arr) {
	  pack_!E(e, -1, bigEndian);
	}
      }
      else {
	if (arr.length < (count + BitCount!E - 1)/BitCount!E)
	  assert(false);
	for (size_t i=0; count != 0; ++i) {
	  if (count >= BitCount!E) {
	    pack_!E(arr[i], -1, bigEndian);
	    count -= BitCount!E;
	  }
	  else {
	    pack_!E(arr[i], count, bigEndian);
	    count = 0;
	  }
	}
      }
    }

  public void unpack_(T)(ref T arr, size_t count = -1, bool bigEndian=false)
    if (isArray!T) {
      alias E = ElementType!T;
      if (count == -1) {
	foreach (ref e; arr) {
	  unpack_!E(e, -1, bigEndian);
	}
      }
      else {
	if (arr.length < (count + BitCount!E - 1)/BitCount!E)
	  assert(false);
	for (size_t i=0; count != 0; ++i) {
	  if (count >= BitCount!E) {
	    unpack_!E(arr[i], -1, bigEndian);
	    count -= BitCount!E;
	  }
	  else {
	    unpack_!E(arr[i], count, bigEndian);
	    count = 0;
	  }
	}
      }
    }
  
  void pack(T)(T t, bool bigEndian, size_t count=-1) if (! isArray!T) {
    this.pack_(t, count, bigEndian);
  }

  void unpack(T)(ref T t, bool bigEndian, size_t count=-1) if (! isArray!T) {
    this.unpack_(t, count, bigEndian);
  }
  
  void pack(T)(T t, size_t count=-1) if (! isArray!T){
    this.pack_(t, count, false);
  }

  void unpack(T)(ref T t, size_t count=-1) if (! isArray!T) {
    this.unpack_(t, count, false);
  }
  
  void pack(T)(T t, bool bigEndian, size_t count=-1) if (isArray!T) {
    this.pack_(t, count, bigEndian);
  }

  void unpack(T)(ref T t, bool bigEndian, size_t count=-1) if (isArray!T) {
    this.unpack_(t, count, bigEndian);
  }
  
  void pack(T)(T t, size_t count=-1) if (isArray!T) {
    this.pack_(t, count, false);
  }

  void unpack(T)(ref T t, size_t count=-1) if (isArray!T) {
    this.unpack_(t, count, false);
  }
  
  public void clear() {
    this._packIter = 0;
    this._unpackIter = 0;
  }

  public bool isEmpty() {
    if(_packIter == _unpackIter) return true;
    else return false;
  }

  void pack(T)(T t, bool bigEndian=false)
    if(is(T == SimTime) || is(T == SimTime) || isFloatingPoint!T) {
      alias _bvec!(false, false, BitCount!T) V;
      V v = t.toBits();
      this.pack(v, bigEndian);
    }

  void unpack(T)(ref T t, bool bigEndian=false)
    if(is(T == SimTime) || is(T == SimTime) || isFloatingPoint!T) {
      alias _bvec!(false, false, BitCount!T) V;
      V v;
      this.unpack(v, bigEndian);
      t.fromBits(v);
    }

  void getPacked(T)(ref T[] stream)
    if (isIntegral!T || isBoolean!T || isBitVector!T)
      {
	static if (isBoolean!T)
	  {
	    UBit!64 iter = (cast(ulong) _unpackIter << 32) + _packIter;
	    stream.length = _packIter + 64;
	    for (size_t i=0; i != stream.length; ++i) {
	      if (i < 64)
		stream[i] = iter[i];
	      else
		stream[i] = opIndex(i-64);
	    }
	  }
	else static if (isIntegral!T)
	  {
	    enum BC = BitCount!T;
	    ulong iter = (cast(ulong) _unpackIter << 32) + _packIter;
	    stream.length = (64 + _packIter + BC - 1)/BC;
	    for (size_t i=0; i != stream.length; ++i) {
	      if (i < 64/BC)
		stream[i] = cast(T) (iter >> (i * BC));
	      else
		stream[i] = get!T(i-(64/BC));
	    }
	  }
	else
	  {
	    enum BC = BitCount!T;
	    ulong iter = (cast(ulong) _unpackIter << 32) + _packIter;
	    stream.length = (64 + _packIter + BC - 1)/BC;
	    for (size_t i=0; i != stream.length; ++i) {
	      if (i < 64/BC)
		stream[i] = (iter >> (i * BC)).toBitVec!T;
	      else
		stream[i] = get!T(i-(64/BC));
	    }
	  }
      }
  
  void setPacked(T)(ref T[] stream)
    if (isIntegral!T || isBoolean!T || isBitVector!T)
      {
	ulong packIter, unpackIter;
	static if (isBoolean!T)
	  {
	    UBit!32 pi;
	    UBit!32 ui;
	    if (stream.length < 64)
	      assert(false);
	    for (size_t i=0; i != 32; ++i)
	      pi[i] = stream[i];
	    for (size_t i=0; i != 32; ++i)
	      ui[i] = stream[i+32];
	    packIter = pi;
	    unpackIter = ui;
	    if (packIter < unpackIter)
	      assert(false);
	    if (stream.length < (64 + packIter))
	      assert(false);
	    length = cast(size_t) packIter;
	    _unpackIter = cast(size_t) unpackIter;
	    for (size_t i=0; i != _packIter; ++i)
	      opIndexAssign(stream[i+64], i);
	  }
	else
	  {
	    ulong iters;
	    import std.stdio;
	    enum BC = BitCount!T;
	    length = 0;
	    for (size_t i=0; i != 64/BC; ++i)
	      iters += ((cast(ulong) stream[i]) << (i * BC));
	    packIter = iters & 0xFFFFFFFF;
	    unpackIter = iters >> 32;
	    if (packIter < unpackIter)
	      assert(false);
	    if (stream.length < (64 + packIter)/BC)
	      assert(false);
	    length = cast(size_t) packIter;
	    _unpackIter = cast(size_t) unpackIter;
	    for (size_t i=0; i != (_packIter + BC - 1)/BC; ++i)
	      ptr[(i*BC)/64] +=
		(cast(ulong) stream[64/BC + i]) << ((i*BC)%64);
	  }
      }
  
  void packReset() {
    clear();
  }

  void unpackReset() {
    _unpackIter = 0;
  }
}
