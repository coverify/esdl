/**
 * This module provides an `Array` type with deterministic memory usage not
 * reliant on the GC, as an alternative to the built-in arrays.
 *
 * This module is a submodule of $(MREF std, container).
 *
 * Source: $(PHOBOSSRC std/container/array.d)
 *
 * Copyright: 2010- Andrei Alexandrescu. All rights reserved by the respective holders.
 *
 * License: Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at $(HTTP
 * boost.org/LICENSE_1_0.txt)).
 *
 * Authors: $(HTTP erdani.com, Andrei Alexandrescu)
 *
 * $(SCRIPT inhibitQuickIndex = 1;)
 */
module esdl.data.vector;

// Modified from the original array to allow some debug on the array
// allocations

import core.exception : RangeError;
import std.range.primitives;
import std.traits: hasElaborateDestructor, isMutable, hasIndirections, isImplicitlyConvertible;

// public import std.container.util;

// import esdl.data.deck: Deck;

// version (DECK) {
//   alias Vector = Deck;
//  }
//  else {
   


pure @system unittest
{
  // We test multiple array lengths in order to ensure that the "a1.capacity == a0.length" test is meaningful
  // for the version in which the constructor uses insertBack
  // (because for some lengths, the test passes even without reserve).
  for (size_t n = 0; n < 100; ++n)
    {
      float[] a0;
      {
	import std.range : iota;
	import std.array;
	import std.algorithm.iteration : map;
	a0 = iota (0, n).map!(i => i * 1.1f).array;
      }

      auto a1 = Vector!(float, "dummy")(a0);

      // We check that a1 has the same length and contents as a0:
      {
	assert(a1.length == a0.length);

	// I wish that I could write "assert(a1[] == a0[]);",
	// but the compiler complains: "Error: incompatible types for `(a1.opSlice()) == (a0[])`: `RangeT!(Vector!(float, "dummy"))` and `float[]`".
	import std.algorithm.comparison : equal;
	assert(equal(a1[], a0[]));
      }

      // We check that a1's constructor has called reserve (to maintain good performance):
      assert(a1.capacity == a0.length);
    }
}

pure @system unittest
{
  // To avoid bad performance, we check that a Vector constructed from an empty range
  // does not initialize its RefCountedStore object, even after a call to "reserve(0)".

  {
    Vector!(float, "dummy") a1;
    assert(! a1._data.refCountedStore.isInitialized);
    a1.reserve(0);
    assert(! a1._data.refCountedStore.isInitialized);
  }

  {
    float[] a0 = [];
    Vector!(float, "dummy") a1 = a0;
    // [2021-09-26] TODO: Investigate RefCounted.
    //assert(! a1._data.refCountedStore.isInitialized);
    a1.reserve(0);
    // [2021-09-26] TODO: Investigate RefCounted.
    //assert(! a1._data.refCountedStore.isInitialized);
  }
}

///
pure @system unittest
{
  auto arr = Vector!(int, "dummy")(0, 2, 3);
  assert(arr[0] == 0);
  assert(arr.front == 0);
  assert(arr.back == 3);

  // reserve space
  arr.reserve(1000);
  assert(arr.length == 3);
  assert(arr.capacity >= 1000);

  // insertion
  arr.insertBefore(arr[1..$], 1);
  assert(arr.front == 0);
  assert(arr.length == 4);

  arr.insertBack(4);
  assert(arr.back == 4);
  assert(arr.length == 5);

  // set elements
  arr[1] *= 42;
  assert(arr[1] == 42);
}

///
pure @system unittest
{
  import std.algorithm.comparison : equal;
  auto arr = Vector!(int, "dummy")(1, 2, 3);

  // concat
  auto b = Vector!(int, "dummy")(11, 12, 13);
  arr ~= b;
  assert(arr.length == 6);

  // slicing
  assert(arr[1 .. 3].equal([2, 3]));

  // remove
  arr.linearRemove(arr[1 .. 3]);
  assert(arr[0 .. 2].equal([1, 11]));
}

/// `Vector!(bool, "dummy")` packs together values efficiently by allocating one bit per element
pure @system unittest
{
  auto arr = Vector!(bool, "dummy")([true, true, false, true, false]);
  assert(arr.length == 5);
}

private struct RangeT(A)
{
  /* Workaround for https://issues.dlang.org/show_bug.cgi?id=13629
     See also: http://forum.dlang.org/post/vbmwhzvawhnkoxrhbnyb@forum.dlang.org
  */
  private A[1] _outer_;
  private @property ref inout(A) _outer() inout { return _outer_[0]; }

  private size_t _a, _b;

  /* E is different from T when A is more restrictively qualified than T:
     immutable(Vector!(int, "dummy")) => T == int, E = immutable(int) */
  alias E = typeof(_outer_[0]._data._payload[0]);

  private this(ref A data, size_t a, size_t b)
  {
    _outer_ = data;
    _a = a;
    _b = b;
  }

  @property RangeT save()
  {
    return this;
  }

  @property bool empty() @safe pure nothrow const
  {
    return _a >= _b;
  }

  @property size_t length() @safe pure nothrow const
  {
    return _b - _a;
  }
  alias opDollar = length;

  @property ref inout(E) front() inout
  {
    assert(!empty, "Attempting to access the front of an empty Vector");
    return _outer[_a];
  }
  @property ref inout(E) back() inout
  {
    assert(!empty, "Attempting to access the back of an empty Vector");
    return _outer[_b - 1];
  }

  void popFront() @safe @nogc pure nothrow
  {
    assert(!empty, "Attempting to popFront an empty Vector");
    ++_a;
  }

  void popBack() @safe @nogc pure nothrow
  {
    assert(!empty, "Attempting to popBack an empty Vector");
    --_b;
  }

  // static if (isMutable!A)
  // {
  //     import std.algorithm.mutation : move;

  //     E moveFront()
  //     {
  //         assert(!empty, "Attempting to moveFront an empty Vector");
  //         assert(_a < _outer.length,
  //             "Attempting to moveFront using an out of bounds low index on a Vector");
  //         return move(_outer._data._payload[_a]);
  //     }

  //     E moveBack()
  //     {
  //         assert(!empty, "Attempting to moveBack an empty Vector");
  //         assert(_b - 1 < _outer.length,
  //             "Attempting to moveBack using an out of bounds high index on a Vector");
  //         return move(_outer._data._payload[_b - 1]);
  //     }

  //     E moveAt(size_t i)
  //     {
  //         assert(_a + i < _b,
  //             "Attempting to moveAt using an out of bounds index on a Vector");
  //         assert(_a + i < _outer.length,
  //             "Cannot move past the end of the array");
  //         return move(_outer._data._payload[_a + i]);
  //     }
  // }

  ref inout(E) opIndex(size_t i) inout
  {
    assert(_a + i < _b,
	   "Attempting to fetch using an out of bounds index on a Vector");
    return _outer[_a + i];
  }

  RangeT opSlice()
  {
    return typeof(return)(_outer, _a, _b);
  }

  RangeT opSlice(size_t i, size_t j)
  {
    assert(i <= j && _a + j <= _b,
	   "Attempting to slice using an out of bounds indices on a Vector");
    return typeof(return)(_outer, _a + i, _a + j);
  }

  RangeT!(const(A)) opSlice() const
  {
    return typeof(return)(_outer, _a, _b);
  }

  RangeT!(const(A)) opSlice(size_t i, size_t j) const
  {
    assert(i <= j && _a + j <= _b,
	   "Attempting to slice using an out of bounds indices on a Vector");
    return typeof(return)(_outer, _a + i, _a + j);
  }

  static if (isMutable!A)
    {
      void opSliceAssign(E value)
      {
	assert(_b <= _outer.length,
	       "Attempting to assign using an out of bounds indices on a Vector");
	_outer[_a .. _b] = value;
      }

      void opSliceAssign(E value, size_t i, size_t j)
      {
	assert(_a + j <= _b,
	       "Attempting to slice assign using an out of bounds indices on a Vector");
	_outer[_a + i .. _a + j] = value;
      }

      void opSliceUnary(string op)()
        if (op == "++" || op == "--")
	  {
            assert(_b <= _outer.length,
		   "Attempting to slice using an out of bounds indices on a Vector");
            mixin(op~"_outer[_a .. _b];");
	  }

      void opSliceUnary(string op)(size_t i, size_t j)
        if (op == "++" || op == "--")
	  {
            assert(_a + j <= _b,
		   "Attempting to slice using an out of bounds indices on a Vector");
            mixin(op~"_outer[_a + i .. _a + j];");
	  }

      void opSliceOpAssign(string op)(E value)
      {
	assert(_b <= _outer.length,
	       "Attempting to slice using an out of bounds indices on a Vector");
	mixin("_outer[_a .. _b] "~op~"= value;");
      }

      void opSliceOpAssign(string op)(E value, size_t i, size_t j)
      {
	assert(_a + j <= _b,
	       "Attempting to slice using an out of bounds indices on a Vector");
	mixin("_outer[_a + i .. _a + j] "~op~"= value;");
      }
    }
}

@system unittest
{
  enum : bool { display = false }
  static if (display)
    {
      import std.stdio;
      enum { nDigitsForPointer = 2 * size_t.sizeof, nDigitsForNObjects = 4 }
    }

  static struct S
  {
    static size_t s_nConstructed;
    static size_t s_nDestroyed;
    static void throwIfTooMany()
    {
      if (s_nConstructed >= 7) throw new Exception ("Ka-boom !");
    }

    uint _i;

    ~this()
    {
      static if (display) writefln("@%*Xh: Destroying.", nDigitsForPointer, &this);
      ++s_nDestroyed;
    }

    this(uint i)
    {
      static if (display) writefln("@%*Xh: Constructing.", nDigitsForPointer, &this);
      _i = i;
      ++s_nConstructed;
      throwIfTooMany();
    }

    this(this)
    {
      static if (display) writefln("@%*Xh: Copying.", nDigitsForPointer, &this);
      ++s_nConstructed;
      throwIfTooMany();
    }
  }

  try
    {
      auto a = Vector!(S, "dummy") (S(0), S(1), S(2), S(3));
      static if (display) writefln("@%*Xh: This is where the array elements are.", nDigitsForPointer, &a [0]);
    }
  catch (Exception e)
    {
      static if (display) writefln("Exception caught !");
    }

  static if (display)
    {
      writefln("s_nConstructed %*Xh.", nDigitsForNObjects, S.s_nConstructed);
      writefln("s_nDestroyed   %*Xh.", nDigitsForNObjects, S.s_nDestroyed);
      writefln("s_nConstructed should be equal to s_nDestroyed.");
      writefln("");
    }

  assert(S.s_nDestroyed == S.s_nConstructed);
}


/**
 * _Vector type with deterministic control of memory. The memory allocated
 * for the array is reclaimed as soon as possible; there is no reliance
 * on the garbage collector. `Vector` uses `malloc`, `realloc` and `free`
 * for managing its own memory.
 *
 * This means that pointers to elements of an `Vector` will become
 * dangling as soon as the element is removed from the `Vector`. On the other hand
 * the memory allocated by an `Vector` will be scanned by the GC and
 * GC managed objects referenced from an `Vector` will be kept alive.
 *
 * Note:
 *
 * When using `Vector` with range-based functions like those in `std.algorithm`,
 * `Vector` must be sliced to get a range (for example, use `array[].map!`
 * instead of `array.map!`). The container itself is not a range.
 */
struct Vector(T, string NAME, size_t MINCAP=8, bool SCRATCH=false)
// if (is(T == class))
{
  // import std.internal.memory : malloc, realloc;
  import core.stdc.string : memcpy, memmove, memset;
  import core.memory: malloc = pureMalloc, realloc = pureRealloc, free = pureFree;

  import core.memory : GC;

  import std.exception : enforce;
  import std.typecons : RefCounted, RefCountedAutoInitialize;

  private size_t _capacity;
  private T[] _payload;
  private size_t _size;

  ~this()
  {
    // import std.stdio;

    // // Warning: destroy would destroy also class instances.
    // // The hasElaborateDestructor protects us here.
    // static if (!SCRATCH && is (T == struct) && hasElaborateDestructor!T)
    //   foreach (ref e; _payload[0.._size])
    // 	.destroy(e);

    // static if (!SCRATCH && 
    // 	       (is (T == class) || hasIndirections!T))
    //   GC.removeRange(cast(void*) _payload);

    // writeln ("Free: ", _capacity, " ptr: ", cast(void*) _payload);
    // if (_payload) free(cast(void*) _payload);
  }

  void reset() {
    // static if (!SCRATCH && is (T == struct) && hasElaborateDestructor!T)
    //   foreach (ref e; _payload[0.._size])
    // 	.destroy(e);
    _size = 0;
    return;
  }

  
  /**
   * Removes all the elements from the array and releases allocated memory.
   *
   * Postcondition: `empty == true && capacity == 0`
   *
   * Complexity: $(BIGOH length)
   */
  void clear()
  {
    // static if (!SCRATCH && is (T == struct) && hasElaborateDestructor!T)
    //   foreach (ref e; _payload[0.._size])
    // 	.destroy(e);

    // static if (!SCRATCH && 
    // 	       (is (T == class) || hasIndirections!T))
    //   GC.removeRange(cast(void*) _payload);
    // free(cast(void*) _payload);
    _payload = null;
    _capacity = 0;
    _size = 0;
  }

  /**
   * Disable postblit
   */

  // @disable this(this);

  /**
   * Constructor taking a number of items.
   */
  this(U)(U[] values...) if (isImplicitlyConvertible!(U, T))
    {
      // [2021-07-17] Checking to see whether *always* calling ensureInitialized works-around-and/or-is-related-to https://issues.dlang.org/show_bug.cgihttps://issues.dlang.org/show_bug.cgi...
      //if (values.length)
      {
	reserve(values.length);
	foreach (ref value; values)
	  {
	    // We do not simply write "insertBack(value);"
	    // because that might perform, on each iteration, a now-redundant check of length vs capacity.
	    // Thanks to @dkorpel (https://github.com/dlang/phobos/pull/8162#discussion_r667479090).

	    import core.lifetime : emplace;
	    emplace(_payload.ptr + _size, value);

	    // We increment the length after each iteration (as opposed to adjusting it just once, after the loop)
	    // in order to improve error-safety (in case one of the calls to emplace throws).
	    _size += 1;
	  }
      }

      assert(_size == values.length);   // We check that all values have been inserted.
      assert(_capacity == values.length); // We check that reserve has been called before the loop.
    }

  /**
   * Constructor taking an $(REF_ALTTEXT input range, isInputRange, std,range,primitives)
   */
  this(Range)(Range r)
       if (isInputRange!Range && isImplicitlyConvertible!(ElementType!Range, T) && !is(Range == T[]))
	 {
	   insertBack(r);
	 }

  /**
   * Comparison for equality.
   */
  bool opEquals(const Vector rhs) const
  {
    return opEquals(rhs);
  }

  // fix https://issues.dlang.org/show_bug.cgi?23140
  private alias Unshared(T) = T;
  private alias Unshared(T: shared U, U) = U;

  /// ditto
  bool opEquals(ref const Vector rhs) const
  {
    if (empty) return rhs.empty;
    if (rhs.empty) return false;

    return cast(Unshared!(T)[]) _payload[0.._size] ==
      cast(Unshared!(T)[]) rhs._payload[0..rhs._size];
  }

  /**
   *  Defines the array's primary range, which is a random-access range.
   *
   *  `ConstRange` is a variant with `const` elements.
   *  `ImmutableRange` is a variant with `immutable` elements.
   */
  // alias Range = RangeT!Vector;

  // /// ditto
  // alias ConstRange = RangeT!(const Vector);

  // /// ditto
  // alias ImmutableRange = RangeT!(immutable Vector);

  /**
   * Duplicates the array. The elements themselves are not transitively
   * duplicated.
   *
   * Complexity: $(BIGOH length).
   */
  @property Vector dup()
  {
    return Vector(_payload[0.._size]);
  }

  /**
   * Returns: `true` if and only if the array has no elements.
   *
   * Complexity: $(BIGOH 1)
   */
  @property bool empty() const
  {
    return _size == 0;
  }

  /**
   * Returns: The number of elements in the array.
   *
   * Complexity: $(BIGOH 1).
   */
  @property size_t length() const
  {
    return _size;
  }

  /// ditto
  size_t opDollar() const
  {
    return _size;
  }

  /**
   * Returns: The maximum number of elements the array can store without
   * reallocating memory and invalidating iterators upon insertion.
   *
   * Complexity: $(BIGOH 1)
   */
  @property size_t capacity() const
  {
    return _capacity;
  }

  /**
   * Returns: the internal representation of the array.
   *
   * Complexity: $(BIGOH 1).
   */

  inout(T)[] data() inout @system
  {
    return _payload[0.._size];
  }

  /**
   * Ensures sufficient capacity to accommodate `e` _elements.
   * If `e < capacity`, this method does nothing.
   *
   * Postcondition: `capacity >= e`
   *
   * Note: If the capacity is increased, one should assume that all
   * iterators to the elements are invalidated.
   *
   * Complexity: at most $(BIGOH length) if `e > capacity`, otherwise $(BIGOH 1).
   */
  void reserve(size_t elements)
  {
    if (elements <= capacity) return;
    growCapacity(elements);
  }

  private void growCapacity(size_t elements) {
    assert (elements >= _capacity);
    // static if (T.sizeof == 1)
    //   {
    // 	const sz = elements;
    //   }
    // else
    //   {
    // 	import core.checkedint : mulu;
    // 	bool overflow;
    // 	const sz = mulu(elements, T.sizeof, overflow);
    // 	if (overflow)
    // 	  assert(false, "Overflow");
    //   }
    // // import std.stdio;
    // // writeln("Allocated -- ", sz, " -- ", NAME);
    // static if (is (T == class) || hasIndirections!T)
    //   {
    // 	/* Because of the transactional nature of this
    // 	 * relative to the garbage collector, ensure no
    // 	 * threading bugs by using malloc/copy/free rather
    // 	 * than realloc.
    // 	 */

    // 	auto newPayload = cast(T*) malloc(sz);

    // 	// copy old data over to new array
    // 	memcpy(cast(void*) newPayload, cast(void*) _payload, T.sizeof * _size);
    // 	// Zero out unused capacity to prevent gc from seeing false pointers
    // 	static if (!SCRATCH) {
    // 	  memset( cast(void*) (newPayload + _size),
    // 		  0,
    // 		  (elements - _size) * T.sizeof);
    // 	  GC.addRange(cast(void*) newPayload, sz);
    // 	  GC.removeRange(cast(void*) _payload);
    // 	}
    // 	free(cast(void*) _payload);
    // 	_payload = newPayload;
    //   }
    // else
    //   {
    // 	import std.stdio;
    // 	// These can't have pointers, so no need to zero unused region
    // 	auto newPayload = cast(T*) malloc(sz);
    // 	// copy old data over to new array
    // 	memcpy(cast(void*) newPayload, cast(void*) _payload, T.sizeof * _size);

    // 	free(cast(void*) _payload);
    // 	// auto newPayload = cast(T*) realloc(_payload, sz);
    // 	// auto newPayload = cast(T*) malloc(sz);
    // 	// free(cast(void*) _payload);
    // 	writeln ("Free: ", _capacity, " ptr: ", cast(void*) _payload);
    // 	writeln ("Malloc: ", elements, " ptr: ", cast(void*) newPayload);
    // 	_payload = newPayload;
    //   }
    _payload.reserve(elements);
    _payload.length = elements;
    _capacity = elements;
  }

  /**
   * Returns: A range that iterates over elements of the array in
   * forward order.
   *
   * Complexity: $(BIGOH 1)
   */
  // Range opSlice()
  // {
  //     return typeof(return)(this, 0, length);
  // }

  // ConstRange opSlice() const
  // {
  //     return typeof(return)(this, 0, length);
  // }

  // ImmutableRange opSlice() immutable
  // {
  //     return typeof(return)(this, 0, length);
  // }

  /**
   * Returns: A range that iterates over elements of the array from
   * index `i` up to (excluding) index `j`.
   *
   * Precondition: `i <= j && j <= length`
   *
   * Complexity: $(BIGOH 1)
   */
  // Range opSlice(size_t i, size_t j)
  // {
  //     assert(i <= j && j <= length, "Invalid slice bounds");
  //     return typeof(return)(this, i, j);
  // }

  // ConstRange opSlice(size_t i, size_t j) const
  // {
  //     assert(i <= j && j <= length, "Invalid slice bounds");
  //     return typeof(return)(this, i, j);
  // }

  // ImmutableRange opSlice(size_t i, size_t j) immutable
  // {
  //     assert(i <= j && j <= length, "Invalid slice bounds");
  //     return typeof(return)(this, i, j);
  // }

  /**
   * Returns: The first element of the array.
   *
   * Precondition: `empty == false`
   *
   * Complexity: $(BIGOH 1)
   */
  @property ref inout(T) front() inout
  {
    return _payload[0];
  }

  /**
   * Returns: The last element of the array.
   *
   * Precondition: `empty == false`
   *
   * Complexity: $(BIGOH 1)
   */
  @property ref inout(T) back() inout
  {
    return _payload[_size - 1];
  }

  /**
   * Returns: The element or a reference to the element at the specified index.
   *
   * Precondition: `i < length`
   *
   * Complexity: $(BIGOH 1)
   */
  ref inout(T) opIndex(size_t i) inout
  {
    return _payload[i];
  }

  /**
   * Slicing operators executing the specified operation on the entire slice.
   *
   * Precondition: `i < j && j < length`
   *
   * Complexity: $(BIGOH slice.length)
   */
  void opSliceAssign(T value)
  {
    _payload[0.._size] = value;
  }

  /// ditto
  void opSliceAssign(T value, size_t i, size_t j)
  {
    _payload[i .. j] = value;
  }

  /// ditto
  void opSliceUnary(string op)()
       if (op == "++" || op == "--")
	 {
	   mixin(op~"_payload[0.._size];");
	 }

  /// ditto
  void opSliceUnary(string op)(size_t i, size_t j)
       if (op == "++" || op == "--")
	 {
	   mixin(op~"_payload[i .. j];");
	 }

  /// ditto
  void opSliceOpAssign(string op)(T value)
  {
    mixin("_payload[0.._size] "~op~"= value;");
  }

  /// ditto
  void opSliceOpAssign(string op)(T value, size_t i, size_t j)
  {
    mixin("_payload[i .. j] "~op~"= value;");
  }

  private enum hasSliceWithLength(T) = is(typeof({ T t = T.init; t[].length; }));

  /**
   * Returns: A new array which is a concatenation of `this` and its argument.
   *
   * Complexity:
   * $(BIGOH length + m), where `m` is the number of elements in `stuff`.
   */
  Vector opBinary(string op, Stuff)(Stuff stuff)
       if (op == "~")
	 {
	   Vector result;

	   static if (hasLength!Stuff || isNarrowString!Stuff)
	     result.reserve(_size + stuff.length);
	   else static if (hasSliceWithLength!Stuff)
	     result.reserve(_size + stuff[].length);
	   else static if (isImplicitlyConvertible!(Stuff, T))
	     result.reserve(_size + 1);

	   result.insertBack(this[]);
	   result ~= stuff;
	   return result;
	 }

  /**
   * Forwards to `insertBack`.
   */
  void opOpAssign(string op, Stuff)(auto ref Stuff stuff)
       if (op == "~")
	 {
	   static if (isImplicitlyConvertible!(typeof(stuff), T)) {
	     insertBack(stuff);
	   }
	   else static if (is(typeof(stuff[])) && isImplicitlyConvertible!(typeof(stuff[][0]), T))
	     {
	       insertBack(stuff[]);
	     }
	   else
	     {
	       insertBack(stuff);
	     }
	 }

  /**
   * Sets the number of elements in the array to `newLength`. If `newLength`
   * is greater than `length`, the new elements are added to the end of the
   * array and initialized with `T.init`. If `T` is a `struct` whose default
   * constructor is annotated with `@disable`, `newLength` must be lower than
   * or equal to `length`.
   *
   * Complexity:
   * Guaranteed $(BIGOH abs(length - newLength)) if `capacity >= newLength`.
   * If `capacity < newLength` the worst case is $(BIGOH newLength).
   *
   * Precondition: `__traits(compiles, { static T _; }) || newLength <= length`
   *
   * Postcondition: `length == newLength`
   */
  @property void length(size_t newLength)
  {
    if (_size >= newLength)
      {
	// shorten
	static if (!SCRATCH && is (T == struct) && hasElaborateDestructor!T)
	  foreach (ref e; _payload[newLength .. _size]) {
	    T init_;
	    e = init_;
	  }
	    // .destroy(e);
	_size = newLength;
	return;
      }
    // static if (!SCRATCH) 
    //     assert (false, "Incrementing length is not allowed for Scratch Vector");
    else {
      static if (__traits(compiles, { static T _; }))
	{
	  import std.algorithm.mutation : initializeAll;

	  immutable startEmplace = _size;
	  reserve(newLength);
	  initializeAll(_payload[startEmplace .. newLength]);
	  _size = newLength;
	}
      else
	{
	  assert(0, "Cannot add elements to array because `" ~
		 fullyQualifiedName!T ~ ".this()` is annotated with " ~
		 "`@disable`.");
	}
    }
  }


  static if (is (T == char)) {
    // increment length without initializing
    // useful for charbuf functionality
    @property package T[] _acquire(size_t len) {
      size_t oldSize = _size;
      _size += len;
      return _payload[oldSize.._size];
    }

    package T[] _reserved() {
      return _payload[_size.._capacity];
    }
  }

  /**
   * Removes the last element from the array and returns it.
   * Both stable and non-stable versions behave the same and guarantee
   * that ranges iterating over the array are never invalidated.
   *
   * Precondition: `empty == false`
   *
   * Returns: The element removed.
   *
   * Complexity: $(BIGOH 1).
   *
   * Throws: `Exception` if the array is empty.
   */
  T removeAny()
  {
    auto result = back;
    removeBack();
    return result;
  }

  /// ditto
  alias stableRemoveAny = removeAny;

  /**
   * Inserts the specified elements at the back of the array. `stuff` can be
   * a value convertible to `T` or a range of objects convertible to `T`.
   *
   * Returns: The number of elements inserted.
   *
   * Complexity:
   * $(BIGOH length + m) if reallocation takes place, otherwise $(BIGOH m),
   * where `m` is the number of elements in `stuff`.
   */
  // Insert one item
  size_t insertBack(Elem)(Elem elem) if (isImplicitlyConvertible!(Elem, T))
    {
      import core.lifetime : emplace;
      assert(_capacity >= _size);
      if (_capacity == _size) {
	auto cap = (_capacity + 1) * 2;
	if (cap < MINCAP) cap = MINCAP;
	growCapacity(cap);
      }
      assert(_capacity > _size && _payload,
	     "Failed to reserve memory");
      // static if (SCRATCH || !is (T == struct)) {
      _payload[_size] = elem;
      // }
      // else {
      // 	emplace(_payload + _size, elem);
      // }
      _size += 1;
      return 1;
    }

  // Insert a range of items
  size_t insertBack(Range)(Range r)
       if (isInputRange!Range && isImplicitlyConvertible!(ElementType!Range, T))
	 {
	   immutable size_t oldLength = _size;

	   static if (hasLength!Range)
	     {
	       immutable size_t rLength = r.length;
	       if (_capacity <= _size + rLength) {
		 growCapacity((_size + rLength) * 2);
	       }
	     }

	   static if (isRandomAccessRange!Range &&
		      (SCRATCH || !is (T == struct))) {
	     // use memcpy
	     _payload[_size.._size+r.length] = r[];
	     _size += r.length;
	     return r.length;
	   }
	   else {
	     size_t result;
	     foreach (item; r)
	       {
		 insertBack(item);
		 ++result;
	       }

	     static if (hasLength!Range)
	       assert(result == rLength, "insertBack: range might have changed length");

	     assert(_size == oldLength + result,
		    "Failed to insertBack range");

	     return result;
	   }
	 }

  size_t insertBack(T[] r)
  {
    immutable size_t rLength = r.length;
    if (rLength > 0) {
      if (_capacity <= _size + rLength) {
	growCapacity((_size + rLength) * 2);
      }
      _payload[_size.._size+rLength] = r;
      _size += rLength;
      return rLength;
    }
    else return 0;
  }

  /// ditto
  alias insert = insertBack;

  /**
   * Removes the value from the back of the array. Both stable and non-stable
   * versions behave the same and guarantee that ranges iterating over the
   * array are never invalidated.
   *
   * Precondition: `empty == false`
   *
   * Complexity: $(BIGOH 1).
   *
   * Throws: `Exception` if the array is empty.
   */
  void removeBack()
  {
    enforce(!empty);
    static if (is (T == struct) && hasElaborateDestructor!T) {
      T init_;
      _payload[_size - 1] = init_;
    }
    // .destroy(_payload[_size - 1]);

    _size -= 1;
  }

  /// ditto
  alias stableRemoveBack = removeBack;

  /**
   * Removes `howMany` values from the back of the array.
   * Unlike the unparameterized versions above, these functions
   * do not throw if they could not remove `howMany` elements. Instead,
   * if `howMany > n`, all elements are removed. The returned value is
   * the effective number of elements removed. Both stable and non-stable
   * versions behave the same and guarantee that ranges iterating over
   * the array are never invalidated.
   *
   * Returns: The number of elements removed.
   *
   * Complexity: $(BIGOH howMany).
   */
  size_t removeBack(size_t howMany)
  {
    if (howMany > _size) howMany = _size;
    static if (is (T == struct) && hasElaborateDestructor!T)
      foreach (ref e; _payload[_size - howMany .. _size]) {
	T init_;
	_payload[_size - 1] = init_;
        // .destroy(e);
      }

    _size = _size - howMany;
    return howMany;
  }

  /// ditto
  alias stableRemoveBack = removeBack;

  /**
   * Inserts `stuff` before, after, or instead range `r`, which must
   * be a valid range previously extracted from this array. `stuff`
   * can be a value convertible to `T` or a range of objects convertible
   * to `T`. Both stable and non-stable version behave the same and
   * guarantee that ranges iterating over the array are never invalidated.
   *
   * Returns: The number of values inserted.
   *
   * Complexity: $(BIGOH length + m), where `m` is the length of `stuff`.
   *
   * Throws: `Exception` if `r` is not a range extracted from this array.
   */
  size_t insertBefore(Stuff)(Range r, Stuff stuff)
       if (isImplicitlyConvertible!(Stuff, T))
	 {
	   import core.lifetime : emplace;
	   enforce(r._outer._data is _data && r._a <= _size);
	   reserve(_size + 1);
	   // Move elements over by one slot
	   memmove(_payload.ptr + r._a + 1,
		   _payload.ptr + r._a,
		   T.sizeof * (_size - r._a));
	   emplace(_payload.ptr + r._a, stuff);
	   _size += 1;
	   return 1;
	 }

  /// ditto
  size_t insertBefore(Stuff)(Range r, Stuff stuff)
       if (isInputRange!Stuff && isImplicitlyConvertible!(ElementType!Stuff, T))
	 {
	   import core.lifetime : emplace;
	   enforce(r._outer._data is _data && r._a <= _size);
	   static if (isForwardRange!Stuff)
	     {
	       // Can find the length in advance
	       auto extra = walkLength(stuff);
	       if (!extra) return 0;
	       reserve(_size + extra);
	       // Move elements over by extra slots
	       memmove(_payload.ptr + r._a + extra,
		       _payload.ptr + r._a,
		       T.sizeof * (_size - r._a));
	       foreach (p; _payload.ptr + r._a ..
			_payload.ptr + r._a + extra)
		 {
		   emplace(p, stuff.front);
		   stuff.popFront();
		 }
	       _size += extra;
	       return extra;
	     }
	   else
	     {
	       import std.algorithm.mutation : bringToFront;
	       enforce(_data);
	       immutable offset = r._a;
	       enforce(offset <= _size);
	       auto result = insertBack(stuff);
	       bringToFront(this[offset .. _size - result],
			    this[_size - result .. _size]);
	       return result;
	     }
	 }

  /// ditto
  alias stableInsertBefore = insertBefore;

  /// ditto
  size_t insertAfter(Stuff)(Range r, Stuff stuff)
       if (isImplicitlyConvertible!(Stuff, T) ||
	   isInputRange!Stuff && isImplicitlyConvertible!(ElementType!Stuff, T))
	 {
	   import std.algorithm.mutation : bringToFront;
	   enforce(r._outer._data is _data);
	   // TODO: optimize
	   immutable offset = r._b;
	   enforce(offset <= _size);
	   auto result = insertBack(stuff);
	   bringToFront(this[offset .. _size - result],
			this[_size - result .. _size]);
	   return result;
	 }

  /// ditto
  size_t replace(Stuff)(Range r, Stuff stuff)
       if (isInputRange!Stuff && isImplicitlyConvertible!(ElementType!Stuff, T))
	 {
	   enforce(r._outer._data is _data);
	   size_t result;
	   for (; !stuff.empty; stuff.popFront())
	     {
	       if (r.empty)
		 {
		   // insert the rest
		   return result + insertBefore(r, stuff);
		 }
	       r.front = stuff.front;
	       r.popFront();
	       ++result;
	     }
	   // Remove remaining stuff in r
	   linearRemove(r);
	   return result;
	 }

  /// ditto
  size_t replace(Stuff)(Range r, Stuff stuff)
       if (isImplicitlyConvertible!(Stuff, T))
	 {
	   enforce(r._outer._data is _data);
	   if (r.empty)
	     {
	       insertBefore(r, stuff);
	     }
	   else
	     {
	       r.front = stuff;
	       r.popFront();
	       linearRemove(r);
	     }
	   return 1;
	 }

  /**
   * Removes all elements belonging to `r`, which must be a range
   * obtained originally from this array.
   *
   * Returns: A range spanning the remaining elements in the array that
   * initially were right after `r`.
   *
   * Complexity: $(BIGOH length)
   *
   * Throws: `Exception` if `r` is not a valid range extracted from this array.
   */
  // Range linearRemove(Range r)
  // {
  //     import std.algorithm.mutation : copy;

  //     enforce(r._outer._data is _data);
  //     enforce(r._a <= r._b && r._b <= _size);
  //     immutable offset1 = r._a;
  //     immutable offset2 = r._b;
  //     immutable tailLength = _size - offset2;
  //     // Use copy here, not a[] = b[] because the ranges may overlap
  //     copy(this[offset2 .. _size], this[offset1 .. offset1 + tailLength]);
  //     _size = offset1 + tailLength;
  //     return this[_size - tailLength .. _size];
  // }

  int opApply(int delegate(ref size_t, ref const T) dg) const {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(i, this[i])) {
	return r;
      }
    }
    return 0;
  }

  int opApply(int delegate(ref size_t, ref T) dg) {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(i, this[i])) {
	return r;
      }
    }
    return 0;
  }

  int opApply(int delegate(ref const T) dg) const {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(this[i])) {
	return r;
      }
    }
    return 0;
  }

  int opApply(int delegate(ref T) dg) {
    for (size_t i = 0; i < this._size; ++i) {
      if (int r = dg(this[i])) {
	return r;
      }
    }
    return 0;
  }

  T[] opSlice(size_t i, size_t j) {
    return data[i..j];
  }

  T[] opSlice() {
    return data;
  }

  package T[] _getPayload() {
    return _payload;
  }

  void swap(F)(ref F other) if (is (F: Vector!(T, S), string S)) {
    enum SIZE = Vector!(T, "Temp").sizeof;
    ubyte[SIZE] temp;
    
    memcpy(cast(void*) temp.ptr, cast(void*) &other, SIZE);
    memcpy(cast(void*) &other, cast(void*) &this, SIZE);
    memcpy(cast(void*) &this, cast(void*) temp.ptr, SIZE);
  }
}

alias Scratch(T, string NAME, size_t MINCAP=8) =
  Vector!(T, NAME, MINCAP, true);

@system unittest
{
  Vector!(int, "dummy") a;
  assert(a.empty);
}

@system unittest
{
  Vector!(int, "dummy") a;
  a.length = 10;
  assert(a.length == 10);
  assert(a.capacity >= a.length);
}

@system unittest
{
  struct Dumb { int x = 5; }
  Vector!(Dumb, "dummy") a;
  a.length = 10;
  assert(a.length == 10);
  assert(a.capacity >= a.length);
  immutable cap = a.capacity;
  foreach (ref e; a)
    e.x = 10;
  a.length = 5;
  assert(a.length == 5);
  // do not realloc if length decreases
  assert(a.capacity == cap);
  foreach (ref e; a)
    assert(e.x == 10);

  a.length = 8;
  assert(a.length == 8);
  // do not realloc if capacity sufficient
  assert(a.capacity == cap);
  assert(Dumb.init.x == 5);
  foreach (i; 0 .. 5)
    assert(a[i].x == 10);
  foreach (i; 5 .. a.length)
    assert(a[i].x == Dumb.init.x);

  // realloc required, check if values properly copied
  a[] = Dumb(1);
  a.length = 20;
  assert(a.capacity >= 20);
  foreach (i; 0 .. 8)
    assert(a[i].x == 1);
  foreach (i; 8 .. a.length)
    assert(a[i].x == Dumb.init.x);

  // check if overlapping elements properly initialized
  a.length = 1;
  a.length = 20;
  assert(a[0].x == 1);
  foreach (e; a[1 .. $])
    assert(e.x == Dumb.init.x);
}

@system unittest
{
  Vector!(int, "dummy") a = Vector!(int, "dummy")(1, 2, 3);
  //a._data._refCountedDebug = true;
  auto b = a.dup;
  assert(b == Vector!(int, "dummy")(1, 2, 3));
  b.front = 42;
  assert(b == Vector!(int, "dummy")(42, 2, 3));
  assert(a == Vector!(int, "dummy")(1, 2, 3));
}

@system unittest
{
  auto a = Vector!(int, "dummy")(1, 2, 3);
  assert(a.length == 3);
}

@system unittest
{
  const Vector!(int, "dummy") a = [1, 2];

  assert(a[0] == 1);
  assert(a.front == 1);
  assert(a.back == 2);

  static assert(!__traits(compiles, { a[0] = 1; }));
  static assert(!__traits(compiles, { a.front = 1; }));
  static assert(!__traits(compiles, { a.back = 1; }));

  auto r = a[];
  size_t i;
  foreach (e; r)
    {
      assert(e == i + 1);
      i++;
    }
}

@safe unittest
{
  // https://issues.dlang.org/show_bug.cgi?id=13621
  import std.container : Vector, BinaryHeap;
  alias Heap = BinaryHeap!(Vector!(int, "dummy"));
}

@system unittest
{
  // https://issues.dlang.org/show_bug.cgi?id=18800
  static struct S { void* p; }
  Vector!(S, "dummy") a;
  a.length = 10;
}

@system unittest
{
  Vector!(int, "dummy") a;
  a.reserve(1000);
  assert(a.length == 0);
  assert(a.empty);
  assert(a.capacity >= 1000);
  auto p = a._data._payload.ptr;
  foreach (i; 0 .. 1000)
    {
      a.insertBack(i);
    }
  assert(p == a._data._payload.ptr);
}

@system unittest
{
  auto a = Vector!(int, "dummy")(1, 2, 3);
  a[1] *= 42;
  assert(a[1] == 84);
}

@system unittest
{
  auto a = Vector!(int, "dummy")(1, 2, 3);
  auto b = Vector!(int, "dummy")(11, 12, 13);
  auto c = a ~ b;
  assert(c == Vector!(int, "dummy")(1, 2, 3, 11, 12, 13));
  assert(a ~ b[] == Vector!(int, "dummy")(1, 2, 3, 11, 12, 13));
  assert(a ~ [4,5] == Vector!(int, "dummy")(1,2,3,4,5));
}

@system unittest
{
  auto a = Vector!(int, "dummy")(1, 2, 3);
  auto b = Vector!(int, "dummy")(11, 12, 13);
  a ~= b;
  assert(a == Vector!(int, "dummy")(1, 2, 3, 11, 12, 13));
}

@system unittest
{
  auto a = Vector!(int, "dummy")(1, 2, 3, 4);
  assert(a.removeAny() == 4);
  assert(a == Vector!(int, "dummy")(1, 2, 3));
}

@system unittest
{
  auto a = Vector!(int, "dummy")(1, 2, 3, 4, 5);
  auto r = a[2 .. a.length];
  assert(a.insertBefore(r, 42) == 1);
  assert(a == Vector!(int, "dummy")(1, 2, 42, 3, 4, 5));
  r = a[2 .. 2];
  assert(a.insertBefore(r, [8, 9]) == 2);
  assert(a == Vector!(int, "dummy")(1, 2, 8, 9, 42, 3, 4, 5));
}

@system unittest
{
  auto a = Vector!(int, "dummy")(0, 1, 2, 3, 4, 5, 6, 7, 8);
  a.linearRemove(a[4 .. 6]);
  assert(a == Vector!(int, "dummy")(0, 1, 2, 3, 6, 7, 8));
}

// Give the Range object some testing.
@system unittest
{
  import std.algorithm.comparison : equal;
  import std.range : retro;
  auto a = Vector!(int, "dummy")(0, 1, 2, 3, 4, 5, 6)[];
  auto b = Vector!(int, "dummy")(6, 5, 4, 3, 2, 1, 0)[];
  alias A = typeof(a);

  static assert(isRandomAccessRange!A);
  static assert(hasSlicing!A);
  static assert(hasAssignableElements!A);
  static assert(hasMobileElements!A);

  assert(equal(retro(b), a));
  assert(a.length == 7);
  assert(equal(a[1 .. 4], [1, 2, 3]));
}

// https://issues.dlang.org/show_bug.cgi?id=5920
@system unittest
{
  struct structBug5920
  {
    int order;
    uint* pDestructionMask;
    ~this()
    {
      if (pDestructionMask)
	*pDestructionMask += 1 << order;
    }
  }

  alias S = structBug5920;
  uint dMask;

  auto arr = Vector!(S, "dummy")(cast(S[])[]);
  foreach (i; 0 .. 8)
    arr.insertBack(S(i, &dMask));
  // don't check dMask now as S may be copied multiple times (it's ok?)
  {
    assert(arr.length == 8);
    dMask = 0;
    arr.length = 6;
    assert(arr.length == 6);    // make sure shrinking calls the d'tor
    assert(dMask == 0b1100_0000);
    arr.removeBack();
    assert(arr.length == 5);    // make sure removeBack() calls the d'tor
    assert(dMask == 0b1110_0000);
    arr.removeBack(3);
    assert(arr.length == 2);    // ditto
    assert(dMask == 0b1111_1100);
    arr.clear();
    assert(arr.length == 0);    // make sure clear() calls the d'tor
    assert(dMask == 0b1111_1111);
  }
  assert(dMask == 0b1111_1111);   // make sure the d'tor is called once only.
}

// Test for https://issues.dlang.org/show_bug.cgi?id=5792
// (mainly just to check if this piece of code is compilable)
@system unittest
{
  auto a = Vector!(int[], "dummy")([[1,2],[3,4]]);
  a.reserve(4);
  assert(a.capacity >= 4);
  assert(a.length == 2);
  assert(a[0] == [1,2]);
  assert(a[1] == [3,4]);
  a.reserve(16);
  assert(a.capacity >= 16);
  assert(a.length == 2);
  assert(a[0] == [1,2]);
  assert(a[1] == [3,4]);
}

// test replace!Stuff with range Stuff
@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(int, "dummy")([1, 42, 5]);
  a.replace(a[1 .. 2], [2, 3, 4]);
  assert(equal(a[], [1, 2, 3, 4, 5]));
}

// test insertBefore and replace with empty Vectors
@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(int, "dummy")();
  a.insertBefore(a[], 1);
  assert(equal(a[], [1]));
}
@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(int, "dummy")();
  a.insertBefore(a[], [1, 2]);
  assert(equal(a[], [1, 2]));
}
@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(int, "dummy")();
  a.replace(a[], [1, 2]);
  assert(equal(a[], [1, 2]));
}
@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(int, "dummy")();
  a.replace(a[], 1);
  assert(equal(a[], [1]));
}
// make sure that Vector instances refuse ranges that don't belong to them
@system unittest
{
  import std.exception : assertThrown;

  Vector!(int, "dummy") a = [1, 2, 3];
  auto r = a.dup[];
  assertThrown(a.insertBefore(r, 42));
  assertThrown(a.insertBefore(r, [42]));
  assertThrown(a.insertAfter(r, 42));
  assertThrown(a.replace(r, 42));
  assertThrown(a.replace(r, [42]));
  assertThrown(a.linearRemove(r));
}
@system unittest
{
  auto a = Vector!(int, "dummy")([1, 1]);
  a[1]  = 0; //Check Vector.opIndexAssign
  assert(a[1] == 0);
  a[1] += 1; //Check Vector.opIndexOpAssign
  assert(a[1] == 1);

  //Check Vector.opIndexUnary
  ++a[0];
  //a[0]++ //op++ doesn't return, so this shouldn't work, even with 5044 fixed
  assert(a[0] == 2);
  assert(+a[0] == +2);
  assert(-a[0] == -2);
  assert(~a[0] == ~2);

  auto r = a[];
  r[1]  = 0; //Check Vector.Range.opIndexAssign
  assert(r[1] == 0);
  r[1] += 1; //Check Vector.Range.opIndexOpAssign
  assert(r[1] == 1);

  //Check Vector.Range.opIndexUnary
  ++r[0];
  //r[0]++ //op++ doesn't return, so this shouldn't work, even with 5044 fixed
  assert(r[0] == 3);
  assert(+r[0] == +3);
  assert(-r[0] == -3);
  assert(~r[0] == ~3);
}

@system unittest
{
  import std.algorithm.comparison : equal;

  //Test "array-wide" operations
  auto a = Vector!(int, "dummy")([0, 1, 2]); //Vector
  a[] += 5;
  assert(a[].equal([5, 6, 7]));
  ++a[];
  assert(a[].equal([6, 7, 8]));
  a[1 .. 3] *= 5;
  assert(a[].equal([6, 35, 40]));
  a[0 .. 2] = 0;
  assert(a[].equal([0, 0, 40]));

  //Test empty array
  auto a2 = Vector!(int, "dummy").init;
  ++a2[];
  ++a2[0 .. 0];
  a2[] = 0;
  a2[0 .. 0] = 0;
  a2[] += 0;
  a2[0 .. 0] += 0;

  //Test "range-wide" operations
  auto r = Vector!(int, "dummy")([0, 1, 2])[]; //Vector.Range
  r[] += 5;
  assert(r.equal([5, 6, 7]));
  ++r[];
  assert(r.equal([6, 7, 8]));
  r[1 .. 3] *= 5;
  assert(r.equal([6, 35, 40]));
  r[0 .. 2] = 0;
  assert(r.equal([0, 0, 40]));

  //Test empty Range
  auto r2 = Vector!(int, "dummy").init[];
  ++r2[];
  ++r2[0 .. 0];
  r2[] = 0;
  r2[0 .. 0] = 0;
  r2[] += 0;
  r2[0 .. 0] += 0;
}

// Test issue 11194
@system unittest
{
  static struct S {
    int i = 1337;
    void* p;
    this(this) { assert(i == 1337); }
    ~this() { assert(i == 1337); }
  }
  Vector!(S, "dummy") arr;
  S s;
  arr ~= s;
  arr ~= s;
}

// https://issues.dlang.org/show_bug.cgi?id=11459
@safe unittest
{
  static struct S
  {
    bool b;
    alias b this;
  }
  alias A = Vector!(S, "dummy");
  alias B = Vector!(shared bool, "dummy")(shared bool);
}

// https://issues.dlang.org/show_bug.cgi?id=11884
@system unittest
{
  import std.algorithm.iteration : filter;
  auto a = Vector!(int, "dummy")([1, 2, 2].filter!"true"());
}

// https://issues.dlang.org/show_bug.cgi?id=8282
@safe unittest
{
  auto arr = new Vector!(int, "dummy");
}

// https://issues.dlang.org/show_bug.cgi?id=6998
@system unittest
{
  static int i = 0;
  class C
  {
    int dummy = 1;
    this(){++i;}
    ~this(){--i;}
  }

  assert(i == 0);
  auto c = new C();
  assert(i == 1);

  //scope
  {
    auto arr = Vector!(C, "dummy")(c);
    assert(i == 1);
  }
  //Vector should not have destroyed the class instance
  assert(i == 1);

  //Just to make sure the GC doesn't collect before the above test.
  assert(c.dummy == 1);
}

//https://issues.dlang.org/show_bug.cgi?id=6998 (2)
@system unittest
{
  static class C {int i;}
  auto c = new C;
  c.i = 42;
  Vector!(C, "dummy") a;
  a ~= c;
  a.clear;
  assert(c.i == 42); //fails
}

@safe unittest
{
  static assert(is(Vector!(int, "dummy").Range));
  static assert(is(Vector!(int, "dummy").ConstRange));
}

@system unittest // const/immutable Vector and Ranges
{
  static void test(A, R, E, S)()
  {
    A a;
    R r = a[];
    assert(r.empty);
    assert(r.length == 0);
    static assert(is(typeof(r.front) == E));
    static assert(is(typeof(r.back) == E));
    static assert(is(typeof(r[0]) == E));
    static assert(is(typeof(r[]) == S));
    static assert(is(typeof(r[0 .. 0]) == S));
  }

  alias A = Vector!(int, "dummy");

  test!(A, A.Range, int, A.Range);
  test!(A, const A.Range, const int, A.ConstRange);

  test!(const A, A.ConstRange, const int, A.ConstRange);
  test!(const A, const A.ConstRange, const int, A.ConstRange);

  test!(immutable A, A.ImmutableRange, immutable int, A.ImmutableRange);
  test!(immutable A, const A.ImmutableRange, immutable int, A.ImmutableRange);
  test!(immutable A, immutable A.ImmutableRange, immutable int,
        A.ImmutableRange);
}

// ensure @nogc
@nogc @system unittest
{
  Vector!(int, "dummy") ai;
  ai ~= 1;
  assert(ai.front == 1);

  ai.reserve(10);
  assert(ai.capacity == 10);

  static immutable arr = [1, 2, 3];
  ai.insertBack(arr);
}

/*
 * typeof may give wrong result in case of classes defining `opCall` operator
 * https://issues.dlang.org/show_bug.cgi?id=20589
 *
 * destructor std.container.array.Vector!(MyClass).Vector.~this is @system
 * so the unittest is @system too
 */
@system unittest
{
  class MyClass
  {
    T opCall(T)(T p)
    {
      return p;
    }
  }

  Vector!(MyClass, "dummy") arr;
}

@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(int, "dummy")([1,2,3,4,5]);
  assert(a.length == 5);

  assert(a.insertAfter(a[0 .. 5], [7, 8]) == 2);
  assert(equal(a[], [1,2,3,4,5,7,8]));

  assert(a.insertAfter(a[0 .. 5], 6) == 1);
  assert(equal(a[], [1,2,3,4,5,6,7,8]));
}

// https://issues.dlang.org/show_bug.cgi?id=22105
@system unittest
{
  import core.exception : AssertError;
  import std.exception : assertThrown, assertNotThrown;

  struct NoDefaultCtor
  {
    int i;
    @disable this();
    this(int j) { i = j; }
  }

  auto array = Vector!(NoDefaultCtor, "dummy")([NoDefaultCtor(1), NoDefaultCtor(2)]);
  assertNotThrown!AssertError(array.length = 1);
  assertThrown!AssertError(array.length = 5);
}

// https://issues.dlang.org/show_bug.cgi?id=23140
@system unittest
{
  shared class C
  {
  }

  Vector!(C, "dummy") ac;
  ac = Vector!(C, "dummy")([new C]);
}
////////////////////////////////////////////////////////////////////////////////
// Vector!(bool, "dummy")
////////////////////////////////////////////////////////////////////////////////

/**
 * _Vector specialized for `bool`. Packs together values efficiently by
 * allocating one bit per element.
 */
// struct Vector(T, string NAME)
// if (is(immutable T == immutable bool))
// {
//     import std.exception : enforce;
//     import std.typecons : RefCounted, RefCountedAutoInitialize;

//     static immutable uint bitsPerWord = size_t.sizeof * 8;
//     private static struct Data
//     {
//         Vector!(size_t, NAME).Payload _backend;
//         size_t _length;
//     }
//     private RefCounted!(Data, RefCountedAutoInitialize.no) _store;

//     private @property ref size_t[] data()
//     {
//         assert(_store.refCountedStore.isInitialized,
//             "Cannot get data of uninitialized Vector");
//         return _store._backend._payload;
//     }

//     /**
//      * Defines the array's primary range.
//      */
//     struct Range
//     {
//         private Vector _outer;
//         private size_t _a, _b;
//         /// Range primitives
//         @property Range save()
//         {
//             version (bug4437)
//             {
//                 return this;
//             }
//             else
//             {
//                 auto copy = this;
//                 return copy;
//             }
//         }
//         /// Ditto
//         @property bool empty()
//         {
//             return _a >= _b || _outer.length < _b;
//         }
//         /// Ditto
//         @property T front()
//         {
//             enforce(!empty, "Attempting to access the front of an empty Vector");
//             return _outer[_a];
//         }
//         /// Ditto
//         @property void front(bool value)
//         {
//             enforce(!empty, "Attempting to set the front of an empty Vector");
//             _outer[_a] = value;
//         }
//         /// Ditto
//         T moveFront()
//         {
//             enforce(!empty, "Attempting to move the front of an empty Vector");
//             return _outer.moveAt(_a);
//         }
//         /// Ditto
//         void popFront()
//         {
//             enforce(!empty, "Attempting to popFront an empty Vector");
//             ++_a;
//         }
//         /// Ditto
//         @property T back()
//         {
//             enforce(!empty, "Attempting to access the back of an empty Vector");
//             return _outer[_b - 1];
//         }
//         /// Ditto
//         @property void back(bool value)
//         {
//             enforce(!empty, "Attempting to set the back of an empty Vector");
//             _outer[_b - 1] = value;
//         }
//         /// Ditto
//         T moveBack()
//         {
//             enforce(!empty, "Attempting to move the back of an empty Vector");
//             return _outer.moveAt(_b - 1);
//         }
//         /// Ditto
//         void popBack()
//         {
//             enforce(!empty, "Attempting to popBack an empty Vector");
//             --_b;
//         }
//         /// Ditto
//         T opIndex(size_t i)
//         {
//             return _outer[_a + i];
//         }
//         /// Ditto
//         void opIndexAssign(T value, size_t i)
//         {
//             _outer[_a + i] = value;
//         }
//         /// Ditto
//         T moveAt(size_t i)
//         {
//             return _outer.moveAt(_a + i);
//         }
//         /// Ditto
//         @property size_t length() const
//         {
//             assert(_a <= _b, "Invalid bounds");
//             return _b - _a;
//         }
//         alias opDollar = length;
//         /// ditto
//         Range opSlice(size_t low, size_t high)
//         {
//             // Note: indexes start at 0, which is equivalent to _a
//             assert(
//                 low <= high && high <= (_b - _a),
//                 "Using out of bounds indexes on a Vector"
//             );
//             return Range(_outer, _a + low, _a + high);
//         }
//     }

//     /**
//      * Constructor taking a number of items.
//      */
//     this(U)(U[] values...)
//     if (isImplicitlyConvertible!(U, T))
//     {
//         reserve(values.length);
//         foreach (i, v; values)
//         {
//             auto rem = i % bitsPerWord;
//             if (rem)
//             {
//                 // Fits within the current array
//                 if (v)
//                 {
//                     data[$ - 1] |= (cast(size_t) 1 << rem);
//                 }
//                 else
//                 {
//                     data[$ - 1] &= ~(cast(size_t) 1 << rem);
//                 }
//             }
//             else
//             {
//                 // Need to add more data
//                 _store._backend.insertBack(v);
//             }
//         }
//         _store._length = values.length;
//     }

//     /**
//      * Constructor taking an $(REF_ALTTEXT input range, isInputRange, std,range,primitives)
//      */
//     this(Range)(Range r)
//     if (isInputRange!Range && isImplicitlyConvertible!(ElementType!Range, T) && !is(Range == T[]))
//     {
//         insertBack(r);
//     }

//     /**
//      * Comparison for equality.
//      */
//     bool opEquals(const Vector rhs) const
//     {
//         return opEquals(rhs);
//     }

//     // fix https://issues.dlang.org/show_bug.cgi?23140
//     private alias Unshared(T) = T;
//     private alias Unshared(T: shared U, U) = U;

//     /// ditto
//     bool opEquals(string RHS)(ref const Vector!(T, RHS) rhs) const
//     {
//         if (empty) return rhs.empty;
//         if (rhs.empty) return false;

//         return cast(Unshared!(T)[]) _store._backend._payload ==  cast(Unshared!(T)[]) rhs._store._backend._payload;
//     }

//     /**
//      * Property returning `true` if and only if the array has
//      * no elements.
//      *
//      * Complexity: $(BIGOH 1)
//      */
//     @property bool empty() const
//     {
//         return !length;
//     }

//     /**
//      * Returns: A duplicate of the array.
//      *
//      * Complexity: $(BIGOH length).
//      */
//     @property Vector dup()
//     {
//         Vector result;
//         result.insertBack(this[]);
//         return result;
//     }

//     /**
//      * Returns the number of elements in the array.
//      *
//      * Complexity: $(BIGOH 1).
//      */
//     @property size_t length() const
//     {
//         return _store.refCountedStore.isInitialized ? _store._length : 0;
//     }
//     alias opDollar = length;

//     /**
//      * Returns: The maximum number of elements the array can store without
//      * reallocating memory and invalidating iterators upon insertion.
//      *
//      * Complexity: $(BIGOH 1).
//      */
//     @property size_t capacity()
//     {
//         return _store.refCountedStore.isInitialized
//             ? cast(size_t) bitsPerWord * _store._backend.capacity
//             : 0;
//     }

//     /**
//      * Ensures sufficient capacity to accommodate `e` _elements.
//      * If `e < capacity`, this method does nothing.
//      *
//      * Postcondition: `capacity >= e`
//      *
//      * Note: If the capacity is increased, one should assume that all
//      * iterators to the elements are invalidated.
//      *
//      * Complexity: at most $(BIGOH length) if `e > capacity`, otherwise $(BIGOH 1).
//      */
//     void reserve(size_t e)
//     {
//         import std.conv : to;
//         _store.refCountedStore.ensureInitialized();
//         _store._backend.reserve(to!size_t((e + bitsPerWord - 1) / bitsPerWord));
//     }

//     /**
//      * Returns: A range that iterates over all elements of the array in forward order.
//      *
//      * Complexity: $(BIGOH 1)
//      */
//     Range opSlice()
//     {
//         return Range(this, 0, length);
//     }


//     /**
//      * Returns: A range that iterates the array between two specified positions.
//      *
//      * Complexity: $(BIGOH 1)
//      */
//     Range opSlice(size_t a, size_t b)
//     {
//         enforce(a <= b && b <= length);
//         return Range(this, a, b);
//     }

//     /**
//      * Returns: The first element of the array.
//      *
//      * Precondition: `empty == false`
//      *
//      * Complexity: $(BIGOH 1)
//      *
//      * Throws: `Exception` if the array is empty.
//      */
//     @property bool front()
//     {
//         enforce(!empty);
//         return data.ptr[0] & 1;
//     }

//     /// Ditto
//     @property void front(bool value)
//     {
//         enforce(!empty);
//         if (value) data.ptr[0] |= 1;
//         else data.ptr[0] &= ~cast(size_t) 1;
//     }

//     /**
//      * Returns: The last element of the array.
//      *
//      * Precondition: `empty == false`
//      *
//      * Complexity: $(BIGOH 1)
//      *
//      * Throws: `Exception` if the array is empty.
//      */
//     @property bool back()
//     {
//         enforce(!empty);
//         return cast(bool)(data.back & (cast(size_t) 1 << ((_store._length - 1) % bitsPerWord)));
//     }

//     /// Ditto
//     @property void back(bool value)
//     {
//         enforce(!empty);
//         if (value)
//         {
//             data.back |= (cast(size_t) 1 << ((_store._length - 1) % bitsPerWord));
//         }
//         else
//         {
//             data.back &=
//                 ~(cast(size_t) 1 << ((_store._length - 1) % bitsPerWord));
//         }
//     }

//     /**
//      * Indexing operators yielding or modifyng the value at the specified index.
//      *
//      * Precondition: `i < length`
//      *
//      * Complexity: $(BIGOH 1)
//      */
//     bool opIndex(size_t i)
//     {
//         auto div = cast(size_t) (i / bitsPerWord);
//         auto rem = i % bitsPerWord;
//         enforce(div < data.length);
//         return cast(bool)(data.ptr[div] & (cast(size_t) 1 << rem));
//     }

//     /// ditto
//     void opIndexAssign(bool value, size_t i)
//     {
//         auto div = cast(size_t) (i / bitsPerWord);
//         auto rem = i % bitsPerWord;
//         enforce(div < data.length);
//         if (value) data.ptr[div] |= (cast(size_t) 1 << rem);
//         else data.ptr[div] &= ~(cast(size_t) 1 << rem);
//     }

//     /// ditto
//     void opIndexOpAssign(string op)(bool value, size_t i)
//     {
//         auto div = cast(size_t) (i / bitsPerWord);
//         auto rem = i % bitsPerWord;
//         enforce(div < data.length);
//         auto oldValue = cast(bool) (data.ptr[div] & (cast(size_t) 1 << rem));
//         // Do the deed
//         auto newValue = mixin("oldValue "~op~" value");
//         // Write back the value
//         if (newValue != oldValue)
//         {
//             if (newValue) data.ptr[div] |= (cast(size_t) 1 << rem);
//             else data.ptr[div] &= ~(cast(size_t) 1 << rem);
//         }
//     }

//     /// Ditto
//     T moveAt(size_t i)
//     {
//         return this[i];
//     }

//     /**
//      * Returns: A new array which is a concatenation of `this` and its argument.
//      *
//      * Complexity:
//      * $(BIGOH length + m), where `m` is the number of elements in `stuff`.
//      */
//     Vector!(bool, NAME) opBinary(string op, Stuff)(Stuff rhs)
//     if (op == "~")
//     {
//         Vector!(bool, NAME) result;

//         static if (hasLength!Stuff)
//             result.reserve(length + rhs.length);
//         else static if (is(typeof(rhs[])) && hasLength!(typeof(rhs[])))
//             result.reserve(length + rhs[].length);
//         else static if (isImplicitlyConvertible!(Stuff, bool))
//             result.reserve(length + 1);

//         result.insertBack(this[]);
//         result ~= rhs;
//         return result;
//     }

//     /**
//      * Forwards to `insertBack`.
//      */
//     Vector!(bool, NAME) opOpAssign(string op, Stuff)(Stuff stuff)
//     if (op == "~")
//     {
//         static if (is(typeof(stuff[]))) insertBack(stuff[]);
//         else insertBack(stuff);
//         return this;
//     }

//     /**
//      * Removes all the elements from the array and releases allocated memory.
//      *
//      * Postcondition: `empty == true && capacity == 0`
//      *
//      * Complexity: $(BIGOH length)
//      */
//     void clear()
//     {
//         this = Vector();
//     }

//     /**
//      * Sets the number of elements in the array to `newLength`. If `newLength`
//      * is greater than `length`, the new elements are added to the end of the
//      * array and initialized with `false`.
//      *
//      * Complexity:
//      * Guaranteed $(BIGOH abs(length - newLength)) if `capacity >= newLength`.
//      * If `capacity < newLength` the worst case is $(BIGOH newLength).
//      *
//      * Postcondition: `length == newLength`
//      */
//     @property void length(size_t newLength)
//     {
//         import std.conv : to;
//         _store.refCountedStore.ensureInitialized();
//         auto newDataLength =
//             to!size_t((newLength + bitsPerWord - 1) / bitsPerWord);
//         _store._backend.length = newDataLength;
//         _store._length = newLength;
//     }

//     /**
//      * Removes the last element from the array and returns it.
//      * Both stable and non-stable versions behave the same and guarantee
//      * that ranges iterating over the array are never invalidated.
//      *
//      * Precondition: `empty == false`
//      *
//      * Returns: The element removed.
//      *
//      * Complexity: $(BIGOH 1).
//      *
//      * Throws: `Exception` if the array is empty.
//      */
//     T removeAny()
//     {
//         auto result = back;
//         removeBack();
//         return result;
//     }

//     /// ditto
//     alias stableRemoveAny = removeAny;

//     /**
//      * Inserts the specified elements at the back of the array. `stuff` can be
//      * a value convertible to `bool` or a range of objects convertible to `bool`.
//      *
//      * Returns: The number of elements inserted.
//      *
//      * Complexity:
//      * $(BIGOH length + m) if reallocation takes place, otherwise $(BIGOH m),
//      * where `m` is the number of elements in `stuff`.
//      */
//     size_t insertBack(Stuff)(Stuff stuff)
//     if (is(Stuff : bool))
//     {
//         _store.refCountedStore.ensureInitialized();
//         auto rem = _store._length % bitsPerWord;
//         if (rem)
//         {
//             // Fits within the current array
//             if (stuff)
//             {
//                 data[$ - 1] |= (cast(size_t) 1 << rem);
//             }
//             else
//             {
//                 data[$ - 1] &= ~(cast(size_t) 1 << rem);
//             }
//         }
//         else
//         {
//             // Need to add more data
//             _store._backend.insertBack(stuff);
//         }
//         ++_store._length;
//         return 1;
//     }

//     /// ditto
//     size_t insertBack(Stuff)(Stuff stuff)
//     if (isInputRange!Stuff && is(ElementType!Stuff : bool))
//     {
//         size_t result;
//         static if (hasLength!Stuff)
//             result = stuff.length;

//         for (; !stuff.empty; stuff.popFront())
//         {
//             insertBack(stuff.front);
//             static if (!hasLength!Stuff) ++result;
//         }

//         return result;
//     }

//     /// ditto
//     alias stableInsertBack = insertBack;

//     /// ditto
//     alias insert = insertBack;

//     /// ditto
//     alias stableInsert = insertBack;

//     /// ditto
//     alias linearInsert = insertBack;

//     /// ditto
//     alias stableLinearInsert = insertBack;

//     /**
//      * Removes the value from the back of the array. Both stable and non-stable
//      * versions behave the same and guarantee that ranges iterating over the
//      * array are never invalidated.
//      *
//      * Precondition: `empty == false`
//      *
//      * Complexity: $(BIGOH 1).
//      *
//      * Throws: `Exception` if the array is empty.
//      */
//     void removeBack()
//     {
//         enforce(_store._length);
//         if (_store._length % bitsPerWord)
//         {
//             // Cool, just decrease the length
//             --_store._length;
//         }
//         else
//         {
//             // Reduce the allocated space
//             --_store._length;
//             _store._backend.length = _store._backend.length - 1;
//         }
//     }

//     /// ditto
//     alias stableRemoveBack = removeBack;

//     /**
//      * Removes `howMany` values from the back of the array. Unlike the
//      * unparameterized versions above, these functions do not throw if
//      * they could not remove `howMany` elements. Instead, if `howMany > n`,
//      * all elements are removed. The returned value is the effective number
//      * of elements removed. Both stable and non-stable versions behave the same
//      * and guarantee that ranges iterating over the array are never invalidated.
//      *
//      * Returns: The number of elements removed.
//      *
//      * Complexity: $(BIGOH howMany).
//      */
//     size_t removeBack(size_t howMany)
//     {
//         if (howMany >= length)
//         {
//             howMany = length;
//             clear();
//         }
//         else
//         {
//             length = length - howMany;
//         }
//         return howMany;
//     }

//     /// ditto
//     alias stableRemoveBack = removeBack;

//     /**
//      * Inserts `stuff` before, after, or instead range `r`, which must
//      * be a valid range previously extracted from this array. `stuff`
//      * can be a value convertible to `bool` or a range of objects convertible
//      * to `bool`. Both stable and non-stable version behave the same and
//      * guarantee that ranges iterating over the array are never invalidated.
//      *
//      * Returns: The number of values inserted.
//      *
//      * Complexity: $(BIGOH length + m), where `m` is the length of `stuff`.
//      */
//     size_t insertBefore(Stuff)(Range r, Stuff stuff)
//     {
//         import std.algorithm.mutation : bringToFront;
//         // TODO: make this faster, it moves one bit at a time
//         immutable inserted = stableInsertBack(stuff);
//         immutable tailLength = length - inserted;
//         bringToFront(
//             this[r._a .. tailLength],
//             this[tailLength .. length]);
//         return inserted;
//     }

//     /// ditto
//     alias stableInsertBefore = insertBefore;

//     /// ditto
//     size_t insertAfter(Stuff)(Range r, Stuff stuff)
//     if (isImplicitlyConvertible!(Stuff, T) ||
//             isInputRange!Stuff && isImplicitlyConvertible!(ElementType!Stuff, T))
//     {
//         import std.algorithm.mutation : bringToFront;
//         // TODO: make this faster, it moves one bit at a time
//         immutable inserted = stableInsertBack(stuff);
//         immutable tailLength = length - inserted;
//         bringToFront(
//             this[r._b .. tailLength],
//             this[tailLength .. length]);
//         return inserted;
//     }

//     /// ditto
//     alias stableInsertAfter = insertAfter;

//     /// ditto
//     size_t replace(Stuff)(Range r, Stuff stuff)
//     if (is(Stuff : bool))
//     {
//         if (!r.empty)
//         {
//             // There is room
//             r.front = stuff;
//             r.popFront();
//             linearRemove(r);
//         }
//         else
//         {
//             // No room, must insert
//             insertBefore(r, stuff);
//         }
//         return 1;
//     }

//     /// ditto
//     alias stableReplace = replace;

//     /**
//      * Removes all elements belonging to `r`, which must be a range
//      * obtained originally from this array.
//      *
//      * Returns: A range spanning the remaining elements in the array that
//      * initially were right after `r`.
//      *
//      * Complexity: $(BIGOH length)
//      */
//     Range linearRemove(Range r)
//     {
//         import std.algorithm.mutation : copy;
//         copy(this[r._b .. length], this[r._a .. length]);
//         length = length - r.length;
//         return this[r._a .. length];
//     }
// }

@system unittest
{
  import std.algorithm.comparison : equal;

  auto a = Vector!(bool, "dummy")([true, true, false, false, true, false]);
  assert(equal(a[], [true, true, false, false, true, false]));
}

// using Ranges
@system unittest
{
  import std.algorithm.comparison : equal;
  import std.range : retro;
  bool[] arr = [true, true, false, false, true, false];

  auto a = Vector!(bool, "dummy")(retro(arr));
  assert(equal(a[], retro(arr)));
}

@system unittest
{
  Vector!(bool, "dummy") a;
  assert(a.empty);
}

@system unittest
{
  auto arr = Vector!(bool, "dummy")([false, false, false, false]);
  assert(arr.front == false);
  assert(arr.back == false);
  assert(arr[1] == false);
  auto slice = arr[];
  slice = arr[0 .. $];
  slice = slice[1 .. $];
  slice.front = true;
  slice.back = true;
  slice[1] = true;
  slice = slice[0 .. $]; // https://issues.dlang.org/show_bug.cgi?id=19171
  assert(slice.front == true);
  assert(slice.back == true);
  assert(slice[1] == true);
  assert(slice.moveFront == true);
  assert(slice.moveBack == true);
  assert(slice.moveAt(1) == true);
}

// uncomparable values are valid values for an array
// https://issues.dlang.org/show_bug.cgi?id=16331
@system unittest
{
  double[] values = [double.nan, double.nan];
  auto arr = Vector!(double, "dummy")(values);
}

@nogc @system unittest
{
  auto a = Vector!(int, "dummy")(0, 1, 2);
  int[3] b = [3, 4, 5];
  short[3] ci = [0, 1, 0];
  auto c = Vector!(short, "dummy")(ci);
  assert(Vector!(int, "dummy")(0, 1, 2, 0, 1, 2) == a ~ a);
  assert(Vector!(int, "dummy")(0, 1, 2, 3, 4, 5) == a ~ b);
  assert(Vector!(int, "dummy")(0, 1, 2, 3) == a ~ 3);
  assert(Vector!(int, "dummy")(0, 1, 2, 0, 1, 0) == a ~ c);
}

@nogc @system unittest
{
  auto a = Vector!(char, "dummy")('a', 'b');
  assert(Vector!(char, "dummy")("abc") == a ~ 'c');
  import std.utf : byCodeUnit;
  assert(Vector!(char, "dummy")("abcd") == a ~ "cd".byCodeUnit);
}

@nogc @system unittest
{
  auto a = Vector!(dchar, "dummy")("ąćę"d);
  assert(Vector!(dchar, "dummy")("ąćęϢϖ"d) == a ~ "Ϣϖ"d);
  wchar x = 'Ϣ';
  assert(Vector!(dchar, "dummy")("ąćęϢz"d) == a ~ x ~ 'z');
}

@system unittest
{
  Vector!(bool, "dummy") a;
  assert(a.empty);
  a.insertBack(false);
  assert(!a.empty);
}

@system unittest
{
  Vector!(bool, "dummy") a;
  assert(a.empty);
  auto b = a.dup;
  assert(b.empty);
  a.insertBack(true);
  assert(b.empty);
}

@system unittest
{
  import std.conv : to;
  Vector!(bool, "dummy") a;
  assert(a.length == 0);
  a.insert(true);
  assert(a.length == 1, to!string(a.length));
}

@system unittest
{
  import std.conv : to;
  Vector!(bool, "dummy") a;
  assert(a.capacity == 0);
  foreach (i; 0 .. 100)
    {
      a.insert(true);
      assert(a.capacity >= a.length, to!string(a.capacity));
    }
}

@system unittest
{
  Vector!(bool, "dummy") a;
  assert(a.capacity == 0);
  a.reserve(15657);
  assert(a.capacity >= 15657);
  a.reserve(100);
  assert(a.capacity >= 15657);
}

@system unittest
{
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  assert(a[0 .. 2].length == 2);
}

@system unittest
{
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  assert(a[].length == 4);
}

@system unittest
{
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  assert(a.front);
  a.front = false;
  assert(!a.front);
}

@system unittest
{
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  assert(a[].length == 4);
}

@system unittest
{
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  assert(a.back);
  a.back = false;
  assert(!a.back);
}

@system unittest
{
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  assert(a[0] && !a[1]);
  a[0] &= a[1];
  assert(!a[0]);
}

@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  auto b = Vector!(bool, "dummy")([true, true, false, true]);
  assert(equal((a ~ b)[],
	       [true, false, true, true, true, true, false, true]));
  assert((a ~ [true, false])[].equal([true, false, true, true, true, false]));
  Vector!(bool, "dummy") c;
  c.insertBack(true);
  assert((c ~ false)[].equal([true, false]));
}
@system unittest
{
  import std.algorithm.comparison : equal;
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  auto b = Vector!(bool, "dummy")([false, true, false, true, true]);
  a ~= b;
  assert(equal(
	       a[],
	       [true, false, true, true, false, true, false, true, true]));
}

@system unittest
{
  auto a = Vector!(bool, "dummy")([true, false, true, true]);
  a.clear();
  assert(a.capacity == 0);
}

@system unittest
{
  Vector!(bool, "dummy") a;
  a.length = 1057;
  assert(a.length == 1057);
  assert(a.capacity >= a.length);
  foreach (e; a)
    {
      assert(!e);
    }
  immutable cap = a.capacity;
  a.length = 100;
  assert(a.length == 100);
  // do not realloc if length decreases
  assert(a.capacity == cap);
}

@system unittest
{
  Vector!(bool, "dummy") a;
  a.length = 1057;
  assert(!a.removeAny());
  assert(a.length == 1056);
  foreach (e; a)
    {
      assert(!e);
    }
}

@system unittest
{
  Vector!(bool, "dummy") a;
  for (int i = 0; i < 100; ++i)
    a.insertBack(true);
  foreach (e; a)
    assert(e);
}

@system unittest
{
  Vector!(bool, "dummy") a;
  a.length = 1057;
  assert(a.removeBack(1000) == 1000);
  assert(a.length == 57);
  foreach (e; a)
    {
      assert(!e);
    }
}

@system unittest
{
  import std.conv : to;
  Vector!(bool, "dummy") a;
  version (bugxxxx)
    {
      a._store.refCountedDebug = true;
    }
  a.insertBefore(a[], true);
  assert(a.length == 1, to!string(a.length));
  a.insertBefore(a[], false);
  assert(a.length == 2, to!string(a.length));
  a.insertBefore(a[1 .. $], true);
  import std.algorithm.comparison : equal;
  assert(a[].equal([false, true, true]));
}

// https://issues.dlang.org/show_bug.cgi?id=21555
@system unittest
{
  import std.algorithm.comparison : equal;
  Vector!(bool, "dummy") arr;
  size_t len = arr.insertBack([false, true]);
  assert(len == 2);
}

// https://issues.dlang.org/show_bug.cgi?id=21556
@system unittest
{
  import std.algorithm.comparison : equal;
  Vector!(bool, "dummy") a;
  a.insertBack([true, true, false, false, true]);
  assert(a.length == 5);

  assert(a.insertAfter(a[0 .. 5], [false, false]) == 2);
  assert(equal(a[], [true, true, false, false, true, false, false]));

  assert(a.insertAfter(a[0 .. 5], true) == 1);
  assert(equal(a[], [true, true, false, false, true, true, false, false]));
}

@system unittest
{
  import std.conv : to;
  Vector!(bool, "dummy") a;
  a.length = 10;
  a.insertAfter(a[0 .. 5], true);
  assert(a.length == 11, to!string(a.length));
  assert(a[5]);
}
@system unittest
{
  alias V3 = int[3];
  V3 v = [1, 2, 3];
  Vector!(V3, "dummy") arr;
  arr ~= v;
  assert(arr[0] == [1, 2, 3]);
}
@system unittest
{
  alias V3 = int[3];
  V3[2] v = [[1, 2, 3], [4, 5, 6]];
  Vector!(V3, "dummy") arr;
  arr ~= v;
  assert(arr[0] == [1, 2, 3]);
  assert(arr[1] == [4, 5, 6]);
}

// Change of length reallocates without calling GC.
// https://issues.dlang.org/show_bug.cgi?id=13642
@system unittest
{
  import core.memory;
  class ABC { void func() { int x = 5; } }

  Vector!(ABC, "dummy") arr;
  // Length only allocates if capacity is too low.
  arr.reserve(4);
  assert(arr.capacity == 4);

  void func() @nogc
  {
    arr.length = 5;
  }
  func();

  foreach (ref b; arr) b = new ABC;
  GC.collect();
  arr[1].func();
}

@system unittest
{

  Vector!(int, "dummy") arr = [1, 2, 4, 5];
  int[] data = arr.data();

  const Vector!(int, "dummy") arr2 = [8, 9];
  assert(arr2.data() == [8, 9]);

  data[0] = 0;
  assert(arr[0] == 0);

  arr.length = 0;
  assert(arr.data == []);

  Vector!(int, "dummy") empty;
  assert(empty.data == []);
}

// }
