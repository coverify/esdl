// Written in the D programming language.

// Like container.array but very basic and efficient

// Copyright: Copyright Coverify Systems Technology 2018
// License:   $(WEB www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
// Authors:   puneet@coverify.com

//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
module esdl.data.folder;

import core.stdc.string : memcpy, memmove, memset;
import core.memory: pureMalloc, pureRealloc, pureFree, GC;
alias malloc = pureMalloc;
alias free = pureFree;
alias realloc = pureRealloc;

enum MINCAP = 4;

struct Folder(T) if (is (T == class))
{
  // total capacity of memory allocate
  size_t _capacity;
  // current size
  size_t _size;

  T *_load;

  ~this() {
    GC.removeRange(_load);
    free(_load);
  }

  @disable this(this);
  

  void swop(ref Folder!T other) {
    ubyte[(Folder!T).sizeof] temp;
    
    memcpy(cast(void*) temp.ptr, cast(void*) &other, (Folder!T).sizeof);
    memcpy(cast(void*) &other, cast(void*) &this, (Folder!T).sizeof);
    memcpy(cast(void*) &this, cast(void*) temp.ptr, (Folder!T).sizeof);
  }

  // grow minimum to size
  void growCapacity(size_t cap) {
    import core.checkedint : mulu;

    size_t newcap = cap;
    if (newcap < MINCAP) newcap = MINCAP;
    else if (newcap < _capacity * 2) newcap = _capacity * 2;
    
    bool overflow;
    const nbytes = mulu(newcap, T.sizeof, overflow);
    if (overflow) assert(0);

    if (_capacity == 0) {
      _load = cast(T*) malloc(nbytes);
      memset(_load, 0, newcap * T.sizeof);
      GC.addRange(_load, nbytes);
    }
    else {
      auto newload = cast(T*) malloc(nbytes);
      memcpy(newload, _load, _capacity * T.sizeof);
      memset(newload + _capacity, 0,
	     (newcap - _capacity) * T.sizeof);
      GC.addRange(newload, nbytes);
      GC.removeRange(_load);
      free(_load);
      _load = newload;
    }
    
    _capacity = newcap;
  }
  
  void opOpAssign(string op)(T elem) if (op == "~") {
    if (_size + 1 >= _capacity) {
      growCapacity(_size + 1);
    }
    _load[_size] = elem;
    _size += 1;
  }

  void opOpAssign(string op)(T[] elems) if (op == "~") {
    if (_size + elems.length >= _capacity) {
      growCapacity(_size + elems.length);
    }

    foreach (ref elem; elems) {
      _load[_size] = elem;
      _size += 1;
    }
  }

  ref T opIndex(size_t index) {
    return _load[index];
  }

  T[] opSlice(size_t i, size_t j) {
    return _load[i..j];
  }

  T[] opSlice() {
    return _load[0.._size];
  }

  size_t opDollar() const @safe nothrow {
    return this._size;
  }

  int opApply(int delegate(ref size_t, ref const T) dg) const {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(i, this._load[i])) {
	return r;
      }
    }
    return 0;
  }

  int opApply(int delegate(ref size_t, ref T) dg) {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(i, this._load[i])) {
	return r;
      }
    }
    return 0;
  }

  int opApply(int delegate(ref const T) dg) const {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(this._load[i])) {
	return r;
      }
    }
    return 0;
  }

  int opApply(int delegate(ref T) dg) {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(this._load[i])) {
	return r;
      }
    }
    return 0;
  }

  void clear() {
    for (size_t i=0; i != _size; ++i) {
      _load[i] = T.init;
    }
    _size = 0;
  }

  void reset() {
    _size = 0;
  }

  size_t size() {
    return _size;
  }

  void size(size_t newsize) {
    if (newsize > _capacity) {
      growCapacity(newsize);
    }

    if (newsize > _size) {
      for (size_t i=_size; i!=newsize; ++i) {
	_load[i] = T.init;
      }
    }

    _size = newsize;
  }

  alias length = size;

  V to(V)() if(is(V == string) || is(V == char[])) {
    V v = cast(V) this.opSlice.to!string;
    return v;
  }

  string toString() {
    import std.conv: to;
    return this.opSlice().to!string;
  }

  size_t capacity() {
    return _capacity;
  }

  void reserve(size_t cap) {
    growCapacity(cap);
  }
}
