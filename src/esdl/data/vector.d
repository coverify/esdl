// Written in the D programming language.

// Like container.array but very basic and efficient

// Copyright: Copyright Coverify Systems Technology 2018
// License:   $(WEB www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
// Authors:   puneet@coverify.com

//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
module esdl.data.vector;

import core.stdc.string : memcpy, memmove, memset;
import core.memory: pureMalloc, pureRealloc, pureFree, GC;
import std.traits: isSomeChar, isBoolean, isIntegral;

alias malloc = pureMalloc;
alias free = pureFree;
alias realloc = pureRealloc;

enum MINCAP = 4;

struct Vector(T, string NAME, uint MAXCAP=100)
     if (is (T == class) || is (T == interface) || is (T ==  struct) ||
	 is (T == P*, P) || isSomeChar!T || isBoolean!T || isIntegral!T)
{
  // total capacity of memory allocate
  size_t _capacity;
  // current size
  size_t _size;

  static if (is (T == struct) || is (T == P*, P)) {
    T[] _load;
  }
  else {
    T* _load;
  }

  ~this() {
    static if (is (T == class) || is (T == interface)) {
      GC.removeRange(_load);
    }
    static if (! (is (T == struct) || is (T == P*, P))) {
      free(_load);
    }
  }

  this(this) {
    static if (is (T == struct) || is (T == P*, P)) {
      _load = _load.dup;
    }
    else {
      import core.checkedint : mulu;
      T* newLoad;

      bool overflow;
      const nbytes = mulu(_capacity, T.sizeof, overflow);
      if (overflow) assert(0);

      newLoad = cast(T*) malloc(nbytes);
      memcpy(newLoad, _load, _capacity * T.sizeof);
      static if (is (T == class) || is (T == interface)) {
	GC.addRange(newLoad, nbytes);
      }
      _load = newLoad;
    }
    debug (CHECK_VECTOR_SIZE) {
      static if (NAME == "stackLoad" || NAME == "rangeLoad"
		 || NAME == "termLoad") {
	import std.stdio;
	import std.conv: to;
	writeln ("POSTBLIT size: " ~ NAME ~ " Size: " ~ _capacity.to!string());
      }
    }
  }
  

  void swap(F)(ref F other) if (is (F: Vector!(T, S), string S)) {
    enum SIZE = Vector!(T, "Temp").sizeof;
    ubyte[SIZE] temp;
    
    memcpy(cast(void*) temp.ptr, cast(void*) &other, SIZE);
    memcpy(cast(void*) &other, cast(void*) &this, SIZE);
    memcpy(cast(void*) &this, cast(void*) temp.ptr, SIZE);
  }

  // grow minimum to size
  void growCapacity(size_t cap) {
    import std.conv: to;
    debug (CHECK_VECTOR_SIZE) {
      static if (NAME == "stackLoad" || NAME == "rangeLoad"
		 || NAME == "termLoad") {
	assert (cap <= MAXCAP || MAXCAP == 0,
		"Large size: " ~ NAME ~ " Size: " ~ cap.to!string());
	import std.stdio;
	writeln ("New size: " ~ NAME ~ " Size: " ~ cap.to!string());
      }
    }
    static if (is (T == struct) || is (T == P*, P)) {
      _load.reserve(cap);
      _load.length = cap;
      _capacity = cap;
    }
    else {
      import core.checkedint : mulu;

      // import std.stdio;
      // if (cap > 1000) {
      //   writeln("Vector ", NAME, ": ", cap);
      // }

      size_t newcap = cap;
      if (newcap < MINCAP) newcap = MINCAP;
      else if (newcap < _capacity * 2) newcap = _capacity * 2;
    
      bool overflow;
      const nbytes = mulu(newcap, T.sizeof, overflow);
      if (overflow) assert(0);

      if (_capacity == 0) {
	_load = cast(T*) malloc(nbytes);
	memset(_load, 0, newcap * T.sizeof);
	static if (is (T == class) || is (T == interface)) {
	  GC.addRange(_load, nbytes);
	}
      }
      else {
	auto newload = cast(T*) malloc(nbytes);
	memcpy(newload, _load, _capacity * T.sizeof);
	memset(newload + _capacity, 0,
	       (newcap - _capacity) * T.sizeof);
	static if (is (T == class) || is (T == interface)) {
	  GC.addRange(newload, nbytes);
	  GC.removeRange(_load);
	}
	free(_load);
	_load = newload;
      }
    
      _capacity = newcap;
    }
  }
  
  void opOpAssign(string op)(T elem) if (op == "~") {
    if (_size + 1 >= _capacity) {
      growCapacity((_size + 1) * 2);
    }
    _load[_size] = elem;
    _size += 1;
  }

  static if (is (T == char)) {
    void opOpAssign(string op)(string elems) if (op == "~") {
	if (_size + elems.length >= _capacity) {
	  growCapacity((_size + elems.length) * 2);
	}
	_load[_size.._size+elems.length] = elems[];
	_size += elems.length;
      }
  }

  void opOpAssign(string op)(T[] elems) if (op == "~") {
    if (_size + elems.length >= _capacity) {
      growCapacity((_size + elems.length) * 2);
    }
    _load[_size.._size+elems.length] = elems[];
    _size += elems.length;
  }

  ref T opIndex(size_t index) {
    if (_size <= index) {
      growCapacity((index + 1) * 2);
      for (size_t i=_size; i<=index; ++i) {
	T l = T.init;
	_load[i] = l;
      }
    }
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

  void reset() {
    _size = 0;
  }

  void clear() {
    _size = 0;
  }

  void scrub() {		// scrub and make length zero
    for (size_t i=0; i != _size; ++i) {
      T l = T.init;
      _load[i] = l;
    }
    _size = 0;
  }

  size_t size() {
    return _size;
  }

  void size(size_t newsize) {
    if (newsize > _capacity) {
      growCapacity(newsize * 2);
    }

    if (newsize > _size) {
      for (size_t i=_size; i!=newsize; ++i) {
	T l = T.init;
	_load[i] = l;
      }
    }

    _size = newsize;
  }

  alias length = size;

  static if (is (T == char)) {
    // this function should only be used in combination with reserve
    // Its only purpose is to allow calling format with string directly getting
    // written to vectors memory locations
    void addReserve(size_t sz) {
      if (_capacity < _size + sz) growCapacity((_size + sz) * 2);
    }

    T[] getReserved() {
      return _load[_size.._capacity];
    }

    T* getReservedPtr() {
      return &(_load[_size]);
    }

    // assume that there is sufficient reserved space
    char[] writef(alias fmt, Args...)(Args args) {
      import std.format: sformat;
      return sformat!(fmt)(_load[_size.._capacity], args);
    }

    char[] writef(Args...)(scope const(char)[] fmt, Args args) {
      import std.format: sformat;
      return sformat!(fmt)(_load[_size.._capacity], fmt, args);
    }
  }

  V to(V)() if (is (V == string)) {
    import std.conv: to;
    return this.opSlice().to!string();
  }

  string toString() {
    import std.conv: to;
    return this.opSlice().to!string();
  }

  size_t capacity() {
    return _capacity;
  }

  void reserve(size_t cap) {
    growCapacity(cap);
  }
}

alias Charbuf(string NAME, uint MAXCAP=1024) = Vector!(char, NAME, MAXCAP);
