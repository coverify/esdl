// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

// This file is part of esdl.

module esdl.data.queue;
import std.format: FormatSpec, FormatException;
import std.conv: to;
import std.range: ElementType;


/** The Queue class provides a random access container where appending and
    removing takes amortized O(1) for both ends. Internally it is a array with
    a base pointer in form of a long and a size value in form of a size_t.

    Authors: Robert "burner" Schadek, rburners@gmail.com
*/
public struct Queue(T) {
  import std.traits: isIterable, isArray;
  import std.string: format;

  private T[] data; /// the actual stored data
  private size_t head = 0; /// insert first than move
  private size_t size = 0; /// move first than insert

  /** Through this constructor a Queue is constructed from a array.

      Params:
      arr = The array the Queue will be constructed from.
  */
  // we do not cover arrays in isIterable, because empty array "[]" is not iteratble
  public this(R)(R values) @safe
    if(isIterable!R && is(ElementType!R: T) && !(isArray!R)) {
      this.pushBack(values);
    }

  // public this()(T[] values) @safe {
  //   this.pushBack(values);
  // }

  public this()(const T[] values) @safe {
    this.pushBack(values);
  }

  public this()(T[] values) @safe {
    this.pushBack(values);
  }

  /** This can be considered the copy constructor of the Queue. A deep copy
      of the array as well as any other internal data is created.

      Params:
      toCopy = The deque to copy.

      Examples:
      ----------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      Queue!(int) copy = new Queue!(int)(de);
      de.removeFront();
		
      // the copy should still hold all elements
      foreach(ptrdiff_t idx, int it; copy) {
      assert(copy[idx] == it);
      }
      ---------------
  */

  public this(this) @safe  { // postblit
    this.data = this.data.dup;
  }

  public Queue!T opAssign(R)(R values) @safe
    if(isIterable!R && is(ElementType!R: T) && !(isArray!R)) {
      this.clear;
      this.pushBack(values);
      return this;
    }

  // we do not cover arrays in isIterable, because empty array "[]" is not iteratble
  public Queue!T opAssign()(T[] values) @safe {
    this.clear;
    this.pushBack(values);
    return this;
  }
    
  public Queue!T opAssign()(const T[] values) @safe {
    this.clear;
    this.pushBack(values);
    return this;
  }
    
  // Unlike underlying dlang array assignment, data is duplicated
  // data can not be shared between the two queues anyways
  public Queue!T opAssign()(Queue!T q) @safe {
    this.data = q.data.dup;
    this.head = q.head;
    this.size = q.size;
    return this;
  }

  public Queue!T opAssign()(const Queue!T q) @safe {
    this.data = q.data.dup;
    this.head = q.head;
    this.size = q.size;
    return this;
  }

  public Queue!T clone() const {
    Queue!T q;
    q.data = (cast(T[]) this.data).dup;
    q.head = head;
    q.size = size;
    return q;
  }

  public Queue!T clone() {
    Queue!T q;
    q.data ~= this.data.dup;
    q.head = head;
    q.size = size;
    return q;
  }

  alias dup = clone;
  
  unittest {
    int[] arr = [1,2,3,4,5];
    Queue!(int) de = arr;

    // the copy should still hold all elements
    foreach(size_t idx, int it; de) {
      assert(arr[idx] == it, format("%d[%d]", idx, it));
    }
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    Queue!(int) copy = de;
    de.removeFront();
		
    // the copy should still hold all elements
    foreach(size_t idx, int it; copy) {
      assert(copy[idx] == it);
    }
  }

  /** We need a way traversal the Queue. These Range struct gives us this
      possibility. To facility the use of ranges in D, this Range struct
      complies to the forwardrange, inputrange, bidirectionalrange and
      randomaccessrange specifications.
  */
  struct Range(U,S) {
    private U* deque;
    private size_t idx;
    private size_t size;

    package this(ref U _deque, const size_t idx,
		 const size_t highIdx) @trusted {
      this.deque = &_deque;
      this.idx = idx;
      this.size = highIdx;
    }

    /** The member function front returns the first element of the range
	iterable by this Range.
	 
	Returns:
	The first element the range points to.
	 
	Examples:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
	auto it = de[];
	assert(it.front() == 1);
	---------------
    */
    public @property ref S front() @safe {
      return (*deque)[this.idx];
    }

    unittest {
      Queue!(int) de;
      de = [1,2,3,4,5];
      auto it = de[];
      assert(it.front() ==  1); // holds true1);
      it.front = 666;
      assert(it.front() ==  666); // holds true1);
    }

    /** The member function back returns the last element of the range
	iterable by this Range.
	 
	Returns:
	The last element the range points to.
	 
	Examples:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
	auto it = de[];
	assert(it.back() == 5);
	---------------
    */
    public @property ref S back() @safe {
      return (*deque)[this.idx+this.size-1];
    }

    unittest {
      Queue!int de;
      de = [1,2,3,4,5];
      auto it = de[];
      int b;
      assert((b = it.back()) == 5// , to!(string)(b)
    	     ); // holds true
    }

    /** If no elements are in the range this functions tell you this.

	Returns:
	True if the range is empty, false otherwise.

	Examples:
	----------------
	Queue!(int) de = new Queue!(int)();
	auto it = de[];
	assert(it.empty()); // holds true

	de = new Queue!(int)([1,2,3,4]);
	it = de[];
	assert(!it.empty()); // holds true
	---------------
    */
    public @property bool empty() const @safe {
      return this.size == 0;
    }

    unittest {
      Queue!(int) de;
      auto it = de[];
      assert(it.empty// , to!(string)(it.length)
    	     ); // holds true

      de = [1,2,3,4];
      it = de[];
      assert(!it.empty); // holds true
    }

    /** Save can be used to create a copy of the range. This is required by
	the forward range specification.

	Examples:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4]);
	auto it = de[];
	assert(it.front() == 1);

	auto jt = it.save();
	assert(jt.front() == 1);

	it.popFront();
	assert(it.front() == 2);
	assert(jt.front() == 1);
	----------------
    */
    public @property Range!(U,S) save() @safe {
      return Range!(U,S)(*deque, this.idx, this.size);
    }

    unittest {
      Queue!int de = [1,2,3,4];
      auto it = de[];
      assert(it.front() == 1);
		
      auto jt = it.save();
      assert(jt.front() == 1);
		
      it.popFront();
      assert(it.front() == 2);
      assert(jt.front() == 1);
    }

    /** Steps the front of the range to the next element.

	Example:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4]);
	auto it = de[];
	assert(it.front() == 1);

	it.popFront();
	assert(it.front() == 2);
	----------------
    */
    public void popFront() @safe {
      ++this.idx;
      --this.size;
    }
	
    /** Steps the back of the range to the next element.

	Example:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4]);
	auto it = de[];
	assert(it.back() == 4);

	it.popBack();
	assert(it.back() == 3);
	----------------
    */
    public void popBack() @safe {
      --this.size;
    }

    unittest {
      Queue!(int) de =[1,2,3,4];
      auto it = de[];
      assert(it.back() == 4);
		
      it.popBack();
      assert(it.back() == 3);
    }

    /** Interestingly the length member functions returns the length of the
	range.

	Returns:
	The length of the range

	Example:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4]);
	auto it = de[];
	assert(it.length == 4); // holds true
	----------------
    */
    public @property size_t length() const @safe nothrow {
      return this.size;
    }

    unittest {
      Queue!(int) de = [1,2,3,4];
      auto it = de[];
      assert(it.length == 4); // holds true

      de = [];
      it = de[];
      assert(it.length == 0); // holds true
    }

    /** This is needed to allow slicing the range. 

	Example:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4]);
	auto it = de[][1,3];
	assert(it.length == 2); // holds true
	----------------
    */
    public Range!(U,S) opSlice(size_t l, size_t h) @safe {
      return Range!(U,S)(*deque, this.idx+l, this.idx+h);
    }

    unittest {
      Queue!(int) de = [1,2,3,4];
      auto it = de[][1 .. 3];
      assert(it.length == 3); // holds true
      assert(it.back() == 4);
    }

    /** For random access this function is needed.

	Params:
	i = The index of the element to access

	Returns:
	The element pointed to by i

	Example:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4]);
	auto it = de[];

	assert(it[0] == 1);
	assert(it[2] == 3);
	assert(it[3] == 4);
	----------------
    */
    public ref S opIndex(size_t i) @safe {
      return (*deque)[this.idx+i];
    }

    unittest {
      Queue!(int) de = [1,2,3,4];
      auto it = de[];
		
      assert(it[0] == 1);
      assert(it[2] == 3);
      assert(it[3] == 4);
    }

    /** Returns the index into the deque. With other words the offset 
	from the beginning of the range in relation to index 0 of the Queue.

	Returns:
	The offset of the beginning of the range in relation index 0 of the
	Queue.

	Example:
	----------------
	Queue!(int) de = new Queue!(int)([1,2,3,4]);
	auto it = de.range(1);
	it.popFront();
	assert(it.getIndex() == 2);
	----------------
    */
    public size_t getIndex() const @safe nothrow {
      return this.idx;
    }

    unittest {
      Queue!(int) de = [1,2,3,4];
      auto it = de.range(1);
      it.popFront();
      assert(it.getIndex() == 2);
    }

  }

  unittest { // check range for iterator properties
    import std.range;
    static assert(isInputRange!(Range!(Queue!(int), int)));
    static assert(isForwardRange!(Range!(Queue!(int), int)));
    static assert(isRandomAccessRange!(Range!(Queue!(int), int)));
    static assert(isInputRange!(Range!(Queue!(int), int)));
  }

  /+public this(S)(S range)  if(isInputRange!(S)
   && !is(S == T[])) {
   this(32);
   foreach(it; range) {
   this.pushBack(it);
   }
   }
	
   // unittest {
   // auto rs = uniq([1,2,3,4,4,5,5,6]);
   // Queue!(int) de = new Queue!(int)(rs);
   // for(int i = 1; i < 7; ++i) {
   // assert(de[i-1] == i);
   // }
   // }
   +/

  /** Sometimes you want to convert the Queue into an dynamic Array. This
      function accomplishes this tales.

      Returns:
      A array containing the elements of the Queue.

      Examples:
      -------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de.toArray() == [1,2,3,4,5]);
      -------------
  */

  public T[] toArray() @trusted {
    T[] ret = new T[this.length()];
    foreach(idx, it; this) {
      ret[idx] = it;
    }
    return ret;
  }

  V to(V)() if(is(V == string) || is(V == char[])) {
    V v = cast(V) this.toArray.to!string;
    return v;
  }

  string toString() {
    return this.to!(string);
  }

  void toString(scope void delegate(const(char)[]) sink,
  		ref FormatSpec!char f) {
    char[] buff;
    switch(f.spec) {
    case 's':
      buff = cast(char[]) this.toArray.to!string;
      break;
    default :
      throw new FormatException("Format specifier not understood: %" ~ f.spec);
    }
    assert(buff.length > 0);
    sink(buff);
  }

  // public const(T)[] toArray() const @trusted {
  //   T[] ret = new T[this.length()];
  //   foreach(idx, it; this) {
  //     ret[idx] = it;
  //   }
  //   return ret;
  // }

  // http://d.puremagic.com/issues/show_bug.cgi?id=10727
  // alias toArray this;

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    assert(de.toArray() == [1,2,3,4,5]);
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    int[] deA = de.toArray;
    assert(deA == [1,2,3,4,5]);
  }


  /** Grows the array and places by a factor of 2
   */
  private void growCapacity() @trusted {
    T[] ndata;
    if(data.length == 0) {
      ndata = new T[8];
    } else {
      ndata = new T[this.data.length*2];
    }
    assert(ndata !is null);

    size_t idx = 0;
    for(size_t i = 0; i < this.length; ++i) {
      ndata[idx++] = this.data[(this.head+i)%this.data.length];
    }

    this.data = ndata;
    this.head = 0;
    this.size = idx;
  }

  /** This member function can be used to insert data before the data
      pointed to be idx. That means you can not use insert to append an
      element at the back. To do that use the pushBack member function.

      Params:
      idx = The index of where to insert the data. The index can range from 
      -(deque.length+1) < idx < deque.length.
      data = The data to insert

      Examples:
      -------------
      Queue!(int) de = new Queue!(int)([1,2,4,5,6]);
      de.insert(2,3);
      foreach(ptrdiff_t idx, int it; [1,2,3,4,5,6]) {
      assert(de[idx] == it, format("de[%u](%d) == it", idx, de[idx], 
      it));
      }
      de.insert(5,7);
      assert(de.removeBack() == 6);
      assert(de.removeBack() == 7);

      de.insert(0, -1);
      assert(de.front == -1);
      -------------

      Returns:
      The Queue for furthor processing.
  */
  public Queue!(T) insert(S...)(ptrdiff_t idx, S data) @safe {
    foreach(dataElem; data) {
      if(idx < 0) {
	idx = this.size + idx;
      }
      assert(idx >= 0);

      if(idx == 0) {
	this.pushFront(data);
      } else if(idx == this.size) {
	this.pushBack(data);
      } else if(idx < (this.size / 2)) {
	if(this.size+1 >= this.data.length) {
	  this.growCapacity();
	}

	// move stuff front
	size_t fix = this.head == 0 ? this.data.length-1 : this.head-1;

	for(size_t i = 0; i < idx; ++i) {
	  size_t low = (fix + i) % this.data.length;
	  size_t up = (fix + i + 1) % this.data.length;
	  this.data[low] = this.data[up];
	}
				
	this.head = this.head == 0 ? this.data.length-1 : this.head-1;

	++this.size;

	this.data[(this.head + idx)%this.data.length] =
	  dataElem;
      } else {
	if(this.size+1 >= this.data.length) {
	  this.growCapacity();
	}

	T tmp = this.data[(this.head+idx)%this.data.length];
	for(size_t i = idx+1; i < this.size; ++i) {
	  T lTmp = this.data[(this.head + i) % this.data.length];	
	  this.data[(this.head + i) % this.data.length] = tmp;

	  tmp = lTmp;
	}
	this.data[(this.head + this.size) % this.data.length] = tmp;
	this.data[(this.head + idx) % this.data.length] = dataElem;

	++this.size;

      }

      if(idx >= 0) { 
	++idx;
      } else {
	--idx;
      }
    }

    return this;
  }

  public Queue!(T) insert(R)(ptrdiff_t idx, R range) @safe
    if(isIterable!R && is(ElementType!R: T)) {
      foreach(it; range) {
	this.insert(idx, it);
	if(idx >= 0) {
	  ++idx;
	} else {
	  --idx;
	}
      }
      return this;
    }

  unittest {
    import std.range;
    Take!(int[]) t = take([0,1,2,3,4,5,6], 4);
    Queue!(int) de = [-1,4,5,6];
    de.insert(1, t);
    int idx = -1;
    foreach(it; de) {
      assert(it == idx++);
    }
  }

  unittest {
    import std.range;
    Take!(int[]) t = take([6,5,4,3,2], 4);
    Queue!(int) de = [1,2,7];
    de.insert(-1, t);
    int idx = 1;
    foreach(it; de) {
      assert(it == idx++);
    }
  }

  unittest {
    Queue!(int) de = [1,2,4,5,6];
    de.insert(2,3);
    foreach(size_t idx, int it; [1,2,3,4,5,6]) {
      assert(de[idx] == it, format("de[%u](%d) == it", idx, de[idx], 
  				   it));
    }
    de.insert(5,7);
    de.removeBack();
    de.removeBack();

    de.insert(0, -1);
    assert(de.front == -1);
  }

  unittest { // test nIdx == 0 part
    Queue!(int) de = [2,3,4,5,6];
    de.insert(0, 1);
    assert(de.front == 1);
    int[] a = [1,2,3,4,5,6];
    foreach(size_t idx, int it; a) {
      assert(de[idx] == it, 
  	     format("de[%d](%d) != %d", idx, de[idx], it));
    }
    de.insert(0, 0);
    assert(de.front == 0);
    a = [0,1,2,3,4,5,6];
    foreach(size_t idx, int it; a) {
      assert(de[idx] == it,
  	     format("de[%d](%d) != %d", idx, de[idx], it));
    }
  }

  unittest { // test nIdx == length part
    Queue!(int) de = [1,2,3,4,5];
    de.insert(de.length, 6);
    assert(de.back == 6);
    int[] a = [1,2,3,4,5,6];
    foreach(size_t idx, int it; a) {
      assert(de[idx] == it, 
  	     format("de[%d](%d) != %d", idx, de[idx], it));
    }
    de.insert(de.length, 7);
    assert(de.back == 7);
    a = [1,2,3,4,5,6,7];
    foreach(size_t idx, int it; a) {
      assert(de[idx] == it,
  	     format("de[%d](%d) != %d", idx, de[idx], it));
    }
  }

  unittest {
    Queue!(int) de = [1,2,4,5,6];
    de.insert(2,3);
    foreach(size_t idx, int it; [1,2,3,4,5,6]) {
      assert(de[idx] == it, format("de[%u](%d) == it(%d)", idx, 
  				   de[idx], it));
    }
    de.insert(5,7);
    de.removeBack();
    de.removeBack();

    de.insert(0, -1);
    assert(de.front == -1);
  }

  unittest {
    Queue!(int) de = [2,4,5,6];
    de.pushFront(1);
    de.insert(2,3);
    foreach(size_t idx, int it; [1,2,3,4,5,6]) {
      assert(de[idx] == it, format("de[%u](%d) == it(%d)", idx, 
  				   de[idx], it));
    }
    de.insert(5,7);
    de.removeBack();
    de.removeBack();

    de.insert(0, -1);
    assert(de.front == -1);
  }

  unittest {
    Queue!(int) de = [1,2,3,4,7];
    de.insert(4,5);
    foreach(size_t idx, int it; [1,2,3,4,5,7]) {
      assert(de[idx] == it, format("de[%u](%d) == it(%d)", idx, 
  				   de[idx], it));
    }
    de.insert(5,6);
    foreach(size_t idx, int it; [1,2,3,4,5,6,7]) {
      assert(de[idx] == it, format("de[%u](%d) == it(%d)", idx, 
  				   de[idx], it));
    }
  }

  /** This member function can be used to remove a element at the given
      index. If the index is in bound it is removed and returned.

      Params:
      idx = The index of the element to remove. The index can be of range
      -(deque.length+1) < idx < deque.length.

      Returns:
      The removed element is returned

      Examples:
      -------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      assert(de.remove(5) == 6);
      assert(de.remove(-5) == 1);
      assert(de.remove(0) == 2);
      assert(de.length == 3);
      assert(de.remove(1) == 4);
      assert(de.remove(0) == 3);
      assert(de.remove(0) == 5);
      assert(de.length == 0);
      -------------
  */
  public void remove(const size_t idx, size_t cnt = 1) @trusted {
    cnt = 1;			// not working yet
    size_t nIdx = idx;
    if(idx < 0) {
      nIdx = this.size+idx;
    }
    assert(nIdx >= 0);
    assert(nIdx+cnt <= this.size);
    if(nIdx == 0) {
      this.removeFront(cnt);
      return;
    } else if(nIdx == this.size-1) {
      this.removeBack(cnt);
      return;
    } else if(nIdx < (this.size / 2)) {
      for(size_t i = nIdx; i > 0; --i) {
	this.data[(this.head + i) % this.data.length] = 
	  this.data[(this.head + i - cnt) % 
		    this.data.length];	
      }
      this.head = (this.head + cnt) % this.data.length;
      --this.size;
      return;
    } else {
      for(size_t i = nIdx; i < this.size+cnt; ++i) {
	this.data[(this.head + i) % this.data.length] = 
	  this.data[(this.head + i + cnt) % 
		    this.data.length];
      }
      --this.size;
      return;
    }

    assert(false);
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5,6];
    de.remove(5);
    de.remove(-5);
    de.remove(0);
    assert(de.length == 3, format("%u", de.length));
    int b;
    de.remove(1);
    de.remove(0);
    de.remove(0);
    assert(de.length == 0);

  }

  version(none) {
    unittest {
      Queue!(int) de = [1,2,3,4,5,6];
      de.remove(1,3);
      size_t idx = 0;
      foreach(it; [1,5,6]) {
    	assert(de[idx] == it);
      }
    }
  }

  /** The member function front returns a reference to the first element in
      the Queue. If the Queue is empty it throws an OutOfBoundException.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de.front == 1); // Holds true 
      de.front = 99;
      assert(de.front == 99); // Holds true
      --------------

      Returns:
      A reference to the first element in the Queue.

      See_Also: back
  */
  public ref T front() @safe {
    assert(!this.empty);
    return this.data[head];
  }

  public void popFront(ref T pop) {
    pop = this.front();
    this.removeFront();
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    assert(de.front == 1); // Holds true 
    de.front = 99;
    assert(de.front == 99); // Holds true
  }

  /** The member function const(front) returns a const reference to the first
      element in the Queue. If the Queue is empty it throws an 
      OutOfBoundException.

      Examples:
      --------------
      const Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de.front == 1); // Holds true 
      de.front = 99; // Does not compile, because ref is const
      --------------

      Returns:
      A const reference to the first element in the Queue.	

      See_Also: back
  */
  public ref const(T) front() const @safe {
    assert(!this.empty);
    return this.data[head];
  }

  unittest {
    const Queue!(int) de = [1,2,3,4,5];
    assert(de.front == 1); // Holds true 
  }

  /** The member function const(back) returns a const reference to the last
      element in the Queue. If the Queue is empty it throws an 
      OutOfBoundException.

      Examples:
      --------------
      const Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de.back == 5); // Holds true 
      de.back = 99; // Does not compile, because ref is const
      --------------

      Returns:
      A const reference to the last element in the Queue.	

      See_Also: front
  */
  public ref const(T) back() const @safe {
    assert(!this.empty);
    return this.data[(this.head+this.size-1)%this.data.length];
  }
	
  public void popBack(ref T pop) {
    pop = this.back();
    this.removeBack();
  }

  unittest {
    const Queue!(int) de = [1,2,3,4,5];
    assert(de.back == 5); // Holds true 
  }
  
  /** The member function back returns a reference to the last element in
      the Queue. If the Queue is empty it throws an OutOfBoundException.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de.back == 5); // Holds true 
      de.back = 99;
      assert(de.back == 99); // Holds true
      --------------

      Returns:
      A reference to the last element in the Queue.

      See_Also: front
  */
  public ref T back() @safe {
    assert(!this.empty);
    return this.data[(this.head+this.size-1)%this.data.length];
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    assert(de.back == 5); // Holds true 
    de.back = 99;
    assert(de.back == 99); // Holds true
  }

  /** The removeFront member function removes the first n element of the
      Queue. This reduces the length of the Queue by one.

      Params:
      numToPop = The number of elements to remove from the front of the
      Queue.

      Returns:
      The previously first element of the Queue.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de.removeFront() == 1); // Holds true
      assert(de.front == 2); // Holds true
      --------------
  */
	
  public void removeFront(const size_t numToPop = 1) @safe {
    // debug assert(numToPop <= this.size, to!(string) ~ numToPop.to!string ~ " " 
    // 		 ~ to!(string) ~ " " ~ this.size.to!string);
    this.head = (this.head+numToPop) % this.data.length;
    this.size -= numToPop;
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    de.removeFront();
    assert(de.front == 2); // Holds true
    assert(de.length == 4);
  }

  unittest {
    Queue!(int) de;
    de.pushBack(1);
    de.removeFront();
    de.pushBack(2);
    de.removeFront();
    de.pushBack(3);
    de.removeFront();
    de.pushBack(4);
    de.removeFront();
    de.pushBack(5);
    de.removeFront();
    de.pushBack(6);
    de.removeFront();
    assert(de.empty);
    de.pushBack(1);
    assert(de.front == 1);
    assert(de.back == 1);
    de.pushBack(2);
    assert(de.front == 1);
    assert(de.back == 2);
    de.pushBack(3);
    assert(de.front == 1);
    assert(de.back == 3);
    int b;
    de.removeFront(2);
    assert(de.length == 1);
    assert(!de.empty);
  }

  /** The removeBack member function removes the last element of the Queue.
      This reduces the length of the Queue by one.

      Returns:
      The previously last element of the Queue.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      de.removeBack();
      assert(de.back == 4); // holds true
      --------------
  */
  public void removeBack(const size_t numToPop = 1) @safe {
    import std.exception;
    enforce(numToPop <= this.size,
	    "Queue is not long enough for removeBack operation");
    this.size = this.size - numToPop;
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    de.removeBack();
    int b;
    assert((b = de.back) == 4, format("%d", b)); // holds true
    assert(de.length == 4);
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    int b;
    de.removeBack(2);
    assert(de.back == 3, format("%d", de.back)); // holds true
    assert(de.length == 3);
  }

  unittest {
    Queue!(int) de;
    foreach(int it; [4,3,2,1]) {
      de.pushFront(it);
      assert(de.front == it);
    }

    assert(de.length == 4);

    foreach(size_t idx, int it; [1,2,3,4]) {
      assert(de[idx] == it, format("%d[%d] != %d", idx, de[idx], it));
    }

    de.removeBack();
    de.removeBack();
    de.removeBack();
    de.removeBack();
    assert(de.length == 0);
    assert(de.empty);
  }

  /** Use the pushFront member function to append a element at the front of
      the Queue. Appending a element at the front takes amorized O(1) time.

      Params:
      toPush = The element to append at the front.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      de.pushFront(0);
      assert(de.front == 0); // holds true
      --------------
  */
  public void pushFront(T...)(T values) @safe {
    foreach(it; values) {
      if(this.size+1 >= this.data.length) {
	this.growCapacity();
      }
      this.head = this.head == 0 ? this.data.length-1 : this.head-1;

      ++this.size;
      this.data[this.head] = it;
    }
  }

  public void pushFront(R)(R values) @safe
    if(isIterable!R && is(ElementType!R: T)) {
    foreach(it; values) {
      this.pushFront(it);
    }
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    de.pushFront(0);
    assert(de.front == 0); // holds true
    int[] a = [0,1,2,3,4,5];
    foreach(idx, it; a) {
      assert(de[idx] == it, format("%d[%d]", idx, de[idx]));
    }
  }

  unittest {
    Queue!(int) de;
    de.pushFront(0);
    assert(de.front == 0); // holds true
  }

  unittest {
    Queue!(int) de;
    de.pushFront([6,5,4,3,2,1]);

    int[6] a = [1,2,3,4,5,6];
    foreach_reverse(idx, it; a) {
      assert(de[idx] == it);
    }
  }

  unittest {
    import std.range;
    Take!(int[]) t = take([0,1,2,3,4,5,6], 4);
    Queue!(int) de;
    de.pushFront(t);
    foreach(idx, it; de) {
      assert(3-idx == it, format("%d %d", 7-idx, it));
    }
  }

  unittest {
    Queue!(int) de;
    de.pushFront(6,5,4,3,2,1);

    int[6] a = [1,2,3,4,5,6];
    foreach_reverse(idx, it; a) {
      assert(de[idx] == it);
    }
  }

  /** Use the pushBack member function to append a element at the back of
      the Queue. Appending a element at the back takes amorized O(1) time.

      Params:
      toPush = The element to append at the back.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      de.pushBack(6);
      assert(de.back == 6); // holds true
      --------------
  */
  public void pushBack(R...)(R values) @trusted {
    foreach(it; values) {
      if(this.size+1 >= this.data.length) {
	this.growCapacity();
      }

      this.data[(this.head + this.size) % this.data.length] 
	= it;

      ++this.size;
    }
  }

  public void pushBack(R)(R values) @trusted
    if(isIterable!R && is(ElementType!R: T) && !(isArray!R)) {
      foreach(it; values) {
	this.pushBack(it);
      }
    }

  public void pushBack()(T[] values) @trusted {
    foreach(it; values) {
      this.pushBack(it);
    }
  }

  public void opOpAssign(string op, R)(R values) @trusted
    if(op == "~" && isIterable!R && is(ElementType!R: T)) {
      foreach(it; values) {
	this.pushBack(it);
      }
    }

  public void opOpAssign(string op, R)(R other) @safe
    if(op == "~" && is(R unused: T)) {
      this.pushBack(other);
    }

  public Queue!T opBinary(string op, R)(R values) @safe
    if(op == "~" && isIterable!R && is(ElementType!R: T)) {
      Queue!T ret = this;
      ret ~= values;
      return ret;
    }

  public Queue!T opBinary(string op, R)(R other) @safe
    if(op == "~" && is(R unused: T)) {
      Queue!T ret = this;
      ret ~= other;
      return ret;
    }

  public Queue!T opBinaryRight(string op, R)(R values) @safe
    if(op == "~" && isIterable!R && is(ElementType!R: T)) {
      Queue!T ret;
      ret ~= values;
      ret ~= this;
      return ret;
    }

  public Queue!T opBinaryRight(string op, R)(R other) @safe
    if(op == "~" && is(R unused: T)) {
      Queue!T ret;
      ret ~= other;
      ret ~= this;
      return ret;
    }

  unittest {
    import std.range;
    Take!(int[]) t = take([0,1,2,3,4,5,6,7], 4);
    Queue!(int) de;
    de.pushBack(t);
    foreach(idx, it; de) {
      assert(idx == it);
    }
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    de ~= 6;
    assert(de.back == 6); // holds true
    assert(de.length == 6); // holds true
    int[] a = [1,2,3,4,5,6];
    foreach(idx, it; a) {
      assert(de[idx] == it, format("%u[%d]", idx, de[idx]));
    }
  }

  unittest {
    Queue!(int) de;
    de ~= [1,2,3,4,5,6];

    int[6] a = [1,2,3,4,5,6];
    foreach(idx, it; a) {
      assert(de[idx] == it);
    }
  }

  unittest {
    Queue!(int) de;
    de.pushBack(1,2,3,4,5,6);

    int[6] a = [1,2,3,4,5,6];
    foreach(idx, it; a) {
      assert(de[idx] == it);
    }
  }

  /** This functions returns a reference pointed to by the index.

      Params:
      idx = The index of the element you want to access. The index to check. 
      The index range goes from -(deque.length+1) < idx < deque.length.

      Returns:
      A reference to the value pointed to by the index.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de[-1] == 6); 	// holds true 
      assert(de[-5] == 1); 	// holds true 
      assert(de[0] == 1); 	// holds true 
      assert(de[4] == 5); 	// holds true 

      de[-1] = 99;			// please assign your value here
      assert(de[-1] == 99); 	// holds true 

      de[0] = 1337; 			// holds true 
      assert(de[0] == 1337); 	// holds true 
      --------------
  */
  public ref T opIndex(const ptrdiff_t idx) @trusted {
    if(idx >= 0) {	
      assert(idx <= this.size, 
	     format("idx(%d) size(%d)", idx, this.size));
      return this.data[(this.head+idx)%this.data.length];
    } else {
      ptrdiff_t nIdx = this.size+idx;
      assert(nIdx <= (this.size+1) && nIdx >= 0, 
	     format("out of bound index %d for Queue of length %u", idx,
		    this.length));
      return this.data[(this.head + nIdx) % this.data.length];
    }
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    assert(de[-1] == 5); // holds true 
    assert(de[-5] == 1); // holds true 
    assert(de[0] == 1); // holds true 
    assert(de[4] == 5); // holds true 

    de[-1] = 99;
    assert(de[-1] == 99); // holds true 

    de[0] = 1337; // holds true 
    assert(de[0] == 1337); // holds true 
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    int b;
    assert((b = de[-1]) == 5, format("%d", b)); // holds true 
    assert((b = de[-5]) == 1, format("%d", b)); // holds true 
  }
	
  unittest {
    Queue!(int) de = [1,2,3,4,5];
    de[-1] = 99;
    assert(de[-1] == 99); // holds true 

    de[0] = 1337; // holds true 
    assert(de[0] == 1337); // holds true 
  }

  /** This functions returns a const reference pointed to by the index.

      Params:
      idx = The index of the element you want to access. The index to check. 
      The index range goes from -(deque.length+1) < idx < deque.length.

      Returns:
      A const reference to the value pointed to by the index.

      Examples:
      --------------
      const Queue!(int) de = new Queue!(int)([1,2,3,4,5]);
      assert(de[-1] == 6); // holds true 
      assert(de[-5] == 1); // holds true 
      assert(de[-6] == 1); // will throw a OutOfBoundException 
      assert(de[0] == 1); // holds true 
      assert(de[4] == 5); // holds true 
      assert(de[5] == 5); // will throw a OutOfBoundException 
      --------------
  */
  public ref const(T) opIndex(const ptrdiff_t idx) const @trusted {
    if(idx >= 0) {	
      assert(idx <= this.size);
      return this.data[(this.head+idx)%this.data.length];
    } else {
      ptrdiff_t nIdx = this.size+idx;
      assert(nIdx <= (this.size+1) && nIdx >= 0, 
	     format("out of bound index %d for Queue of length %u", idx,
		    this.length));
      return this.data[(this.head + nIdx) % this.data.length];
    }
  }

  unittest {
    const Queue!(int) de = [1,2,3,4,5];
    assert(de[-1] == 5); // holds true 
    assert(de[-5] == 1); // holds true 
  }

  /** Tells you if the deque is empty.

      Returns:
      If the deque is empty, true is returned otherwise false.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)();
      assert(de.empty); // holds true
      --------------
  */
  @property public bool empty() const @safe nothrow {
    return this.size == 0;
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5];
    for(int i = 0; i < 5; ++i) {
      de.removeFront();
    }
    assert(de.empty);
  }

  /** Traversals the deque in reverse order. The deque is const.

      Params:
      dg = The delegate created by the compiler from the foreach_reverse
      loop. The first parameter is the index of the value reference by
      the second parameter of type T.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      foreach_reverse(ref const ptrdiff_t idx, ref const int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// not allowed, it is const
      }
      --------------
  */
  public int opApplyReverse(int delegate(ref size_t, ref const T) dg) const {
    for(size_t idx = this.size-1; idx < ptrdiff_t.max; --idx) {
      if(int r = dg(idx, this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApplyReverse
    const Queue!(int) de = [1,2,3,4,5,6];
    foreach_reverse(ref size_t idx, ref const int it; de) {
      assert(de[idx] == it);	// holds true
    }
  }

  /** Traversals the deque in reverse order. The deque is const.

      Params:
      dg = The delegate created by the compiler from the foreach_reverse
      loop.

      Examples:
      --------------
      const Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      ptrdiff_t idx = 0;
      foreach_reverse(ref const int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// not allowed, it is const
      ++idx;
      }
      --------------
  */
  public int opApplyReverse(int delegate(const ref T) dg) const {
    for(size_t idx = this.size-1; idx < ptrdiff_t.max; --idx) {
      if(int r = dg(this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApplyReverse
    const Queue!(int) de = [1,2,3,4,5,6];
    ptrdiff_t idx = 0;
    foreach_reverse(ref const int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      ++idx;
    }
    assert(idx == de.length);
  }

  /** Traversals the deque in reverse order.

      Params:
      dg = The delegate created by the compiler from the foreach_reverse
      loop. The first parameter is the index of the value reference by
      the second parameter of type T.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      foreach_reverse(ptrdiff_t idx, int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// works
      }
      --------------
  */
  public int opApplyReverse(int delegate(ref size_t, ref T) dg) {
    for(size_t idx = this.size-1; idx < ptrdiff_t.max; --idx) {
      if(int r = dg(idx, this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApplyReverse
    Queue!(int) de = [1,2,3,4,5,6];
    foreach_reverse(ref size_t idx, ref int it; de) {
      assert(de[idx] == it);	// holds true
      it = 666;					// works
    }

    foreach(it;de) {
      assert(it == 666);
    }
  }

  /** Traversals the deque in reverse order.

      Params:
      dg = The delegate created by the compiler from the foreach_reverse
      loop.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      ptrdiff_t idx = 0;
      foreach_reverse(ref int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// works
      ++idx;
      }
      --------------
  */
  public int opApplyReverse(int delegate(ref T) dg) {
    for(size_t idx = this.size-1; idx < ptrdiff_t.max; --idx) {
      if(int r = dg(this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApplyReverse
    Queue!(int) de = [1,2,3,4,5,6];
    ptrdiff_t idx = 0;
    foreach_reverse(ref int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// works
      ++idx;
    }
    assert(idx == de.length);

    foreach(it;de) {
      assert(it == 666);
    }
  }

  /** Traversals the deque in order. The deque is marked as const.

      Params:
      dg = The delegate created by the compiler from the foreach loop.

      Examples:
      --------------
      const Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      ptrdiff_t idx = 0;
      foreach(ref const ptrdiff_t idx, ref const int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// works
      ++idx;
      }
      --------------
  */
  public int opApply(int delegate(ref size_t, ref const T) dg) const {
    for(size_t idx = 0; idx < this.size; ++idx) {
      if(int r = dg(idx, this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApply
    const Queue!(int) de = [1,2,3,4,5,6];
    foreach(ref size_t idx, ref const int it; de) {
      assert(de[idx] == it, format("de[idx](%d) != it(%d)", 
  				   de[idx], it));	// holds true
    }
  }

  /** Traversals the deque in order.

      Params:
      dg = The delegate created by the compiler from the foreach loop.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      ptrdiff_t idx = 0;
      foreach(ref ptrdiff_t idx, ref int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// works
      ++idx;
      }
      --------------
  */
  public int opApply(int delegate(ref size_t, ref T) dg) {
    for(size_t idx = 0; idx < this.size; ++idx) {
      if(int r = dg(idx, this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApply
    Queue!(int) de = [1,2,3,4,5,6];
    foreach(ref size_t idx, ref int it; de) {
      assert(de[idx] == it, format("de[idx](%d) != it(%d)", 
  				   de[idx], it));	// holds true
      it = 666;
    }

    foreach(it; de) {
      assert(it == 666);
    }
  }
	
  /** Traversals the deque in order. The deque is marked as const

      Params:
      dg = The delegate created by the compiler from the foreach loop.

      Examples:
      --------------
      const Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      ptrdiff_t idx = 0;
      foreach(ref const int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      ++idx;
      }
      --------------
  */
  public int opApply(int delegate(const ref T) dg) const {
    for(size_t idx = 0; idx < this.size; ++idx) {
      if(int r = dg(this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApply
    const Queue!(int) de = [1,2,3,4,5,6];
    ptrdiff_t idx = 0;
    foreach(ref const int it; de) {
      assert(de[idx] == it, format("de[idx](%d) != it(%d)", 
  				   de[idx], it));	// holds true
      ++idx;
    }
    assert(idx == de.length);
  }

  /** Traversals the deque in order.

      Params:
      dg = The delegate created by the compiler from the foreach loop.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5,6]);
      ptrdiff_t idx = 0;
      foreach(ref const int it; de) {
      assert(de[-(idx+1)] == it);	// holds true
      it = 666;					// works 
      ++idx;
      }
      --------------
  */
  public int opApply(int delegate(ref T) dg) {
    for(size_t idx = 0; idx < this.size; ++idx) {
      if(int r = dg(this.data[(this.head+idx)%this.data.length])) {
	return r;
      }
    }
    return 0;
  }

  unittest { // unittest for the previous opApply
    Queue!(int) de = [1,2,3,4,5,6];
    ptrdiff_t idx = 0;
    foreach(ref int it; de) {
      assert(de[idx] == it, format("de[idx](%d) != it(%d)", 
  				   de[idx], it));	// holds true
      it = 666;
      ++idx;
    }
    assert(idx == de.length);

    foreach(it; de) {
      assert(it == 666);
    }
  }

  /** This function can be used to return an range of the Queue.

      Params:
      start = The head index of the range. On default it is set to 0.

      Returns:
      RandomAccessRange to the Queue

      Examples:
      ----------------
      int[] arr = [1,2,3,4,5,6];
      Queue!(int) de = new Queue!(int)(arr);
      Range!(Queue!(int),int) it = de[];
      size_t idx = 0;
      foreach(ref iter;it) {
      assert(iter == arr[idx++]);
      iter = 1337;
      }

      foreach(jt; de) {
      assert(jt == 1337);
      }
      ----------------
  */
  public Range!(Queue!(T), T) range(size_t start = 0) @safe {
    assert(start <= this.size);
    return Range!(Queue!(T), T)(this, start, this.size-start);
  }

  public Range!(Queue!(T), T) range(size_t start, size_t till) @safe {
    assert(start <= this.size);
    assert(start+till <= this.size);
    return Range!(Queue!(T), T)(this, start, till);
  }

  unittest {
    int[] arr = [1,2,3,4,5,6];
    Queue!(int) de = arr;
    Range!(Queue!(int),int) it = de.range(1,1);
    size_t idx = 2;
    foreach(iter;it) {
      assert(iter == idx++);
    }
    assert(idx == 3, format("%u", idx));
  }

  unittest {
    int[] arr = [1,2,3,4,5,6];
    Queue!(int) de;
    auto it = de[];
    size_t idx = 0;
    foreach(ref iter;it) {
      assert(iter == arr[idx++]);
      iter = 1337;
      assert(de[idx-1] == 1337);
    }

    foreach(jt; de) {
      assert(jt == 1337, format("%d", jt));
    }
  }

  unittest {
    int[] arr = [1,2,3,4,5,6];
    Queue!(int) de = arr;
    auto it = de.range(2);
    size_t idx = 3;
    foreach(jt; it) {
      assert(jt == idx++);
    }
  }

  /** This function can be used to return an range a constant the Queue. 
      That means you cannot change the content of the Queue through this 
      range.

      Returns:
      RandomAccessRange to the Queue

      Examples:
      ----------------
      int[] arr = [1,2,3,4,5,6];
      const Queue!(int) de = new Queue!(int)(arr);
      Range!(const Queue!(int), const int) it = de[];
      size_t idx = 0;
      foreach(iter;it) {
      assert(iter == arr[idx++]);
      }	 
      ----------------
  */
  public Range!(const Queue!(T), const(T)) range(size_t start = 0) const {
    assert(start < this.size);
    return Range!(const Queue!(T), const T)(this, start, this.size-start);
  }

  public Range!(const Queue!(T), const(T)) range(size_t start, 
						 size_t till) @safe const {
    assert(start <= this.size);
    assert(start+till <= this.size);
    return Range!(const Queue!(T), const(T))(this, start, till);
  }

  unittest {
    int[] arr = [1,2,3,4,5,6];
    const Queue!(int) de = arr;
    auto it = de[];
    size_t idx = 0;
    foreach(iter;it) {
      assert(iter == arr[idx++]);
    }	 
  }

  /** The opDollar member functions returns the number of elements placed 
      in this Queue.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]); 
      de[$-1] = 666;
      assert(de[$-1] == 666);
      --------------

      Returns:
      The number of elements T placed in the in Queue.
  */
  public size_t opDollar() const @safe nothrow {
    return this.length();
  }

  unittest {
    Queue!(int) de = [1,2,3,4];
    de[$-1] = 666;
    assert(de[$-1] == 666);
  }

  /** The length property returns the number of elements placed in this
      Queue.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5]); 
      assert(de.length == 5);
      --------------

      Returns:
      The number of elements T placed in the in Queue.
  */
  @property public size_t length() const @safe nothrow { 
    return this.size;
  }

  /** The size of the internal array -1 is returned by this function. This
      is the capacity of the array.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)(21);
      assert(de.getCapacity() == 20);
      --------------

      Returns: The capacity of the deque.
  */
  public size_t getCapacity() const @safe nothrow {
    return this.data.length-1;
  }

  unittest {
    Queue!(int) de;
    assert(de.getCapacity() == -1);
  }

  /** This member function clears the content of the deque by reseting the
      head and the size index to their init position. This does not change
      the capacity of the deque, it only set the length to 0.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)(32);
      foreach(it; [1,2,3,4,5,6]) {
      de.pushBack(it);
      }
      de.clear();
      assert(de.empty);
      assert(de.getCapacity() == 31);
      --------------

      See_Also: empty, length
  */
  public void clear() @safe nothrow {
    this.head = this.size = 0;
  }

  unittest {
    Queue!(int) de;
    foreach(it; [1,2,3,4,5,6]) {
      de.pushBack(it);
    }
    de.clear();
    assert(de.empty);
    assert(de.getCapacity() == 7);
  }

  /** Compares the two Queues if all elements they share are equal.
	 	
      Params:
      o = The Queue to compare this one to.

      Examples:
      --------------
      Queue!(int) de = new Queue!(int)([1,2,3,4,5,6,7]);
      assert(de == de);
      Queue!(int) de2 = new Queue!(int)([1,2,3,4,5,6]);
      assert(de != de2);
      Queue!(int) de3 = new Queue!(int)(de);
      assert(de !is de3);
      assert(de == de3);
      --------------

      Returns:
      The value of true is returned if the Queue contain the same elements,
      false otherwise.
  */

  public bool opEquals(Queue!T d) @trusted {
    if(this.length() != d.length()) {
      return false;
    }
    foreach(idx, it; d) {
      // check is both null
      static if(is(T == class)) {
  	if(this[idx] is null && d[idx] is null) {
  	  continue;
  	}
  	// one of the two is null
  	if(this[idx] is null || d[idx] is null) {
  	  return false;
  	}
      }
      if(this[idx] != it) {
  	return false;
      }
    }
    return true;
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5,6,7];
    assert(de == de);
    Queue!(int) de2 = [1,2,3,4,5,6];
    assert(de != de2);
    Queue!(int) de3 = de;
    assert(de !is de3);
    assert(de == de3);
  }

  /** Creating a deep copy when slicing the deque is to heavy and therefor a
      iterator is returned that representing the slice. 
      The element indexed by the high value is not included, hence 
      [low .. high$(RPAREN).
	 
      Returns:
      An iterator that represents the slice.
  */
  public Queue!(T) opSlice(size_t low, size_t high) @safe {
    assert(high <= this.length);
    Queue!(T) ret = this;
    size_t numPopBack = this.length - high;
    ret.removeFront(low);
    ret.removeBack(numPopBack);
		
    return ret;
  }

  unittest {
    Queue!(int) de = [1,2,3,4,5,6];
    Queue!(int) slice = de[1 .. 4];
    //foreach(it; slice) { writef("%d ", it); } writeln();
    int value = 2;
    foreach(it;slice) {
      assert(it == value, format("it(%d) != value(%d)", it, value));
      ++value;
    }
    assert(value == 5);

    slice = de[3 .. de.length];
    Queue!(int) rSlice = slice;
    value = 4;
    foreach(it;slice) {
      assert(it == value, format("it(%d) != value(%d)", it, value));
      ++value;
    }
    assert(value == 7);

    value = 6;
    foreach_reverse(it;rSlice) {
      assert(it == value, format("it(%d) != value(%d)", it, value));
      --value;
    }
    assert(value == 3);
  }

  public Range!(Queue!(T), T) opSlice() @safe {
    return Range!(Queue!(T), T)(this, 0, this.size);
  }

  public Range!(const Queue!(T), const(T)) opSlice() const {
    return Range!(const Queue!(T), const T)(this, 0, this.size);
  }


  unittest {
    Queue!(int) original = [1,2,3,4,5,6];
    auto copy = original[];
    // assert(original == copy);
  }

  // unittest { // random insert and remove
  //   import std.random;
  //   import std.container;
  //   import std.stdio;

  //   for(int k = 0; k < 11; ++k) {
  //     bool set[30000];

  //     Queue!(int) de;

  //     for(int i = 0; i < 250; ++i) {
  // 	int t = cast(int) uniform(0, set.length);
  // 	t = t < 0 ? -t : t;
  // 	assert(t < set.length, format("%d >= %d", t, set.length));
  // 	if(set[t]) {
  // 	  continue;
  // 	}

  // 	set[t] = true;
  // 	ptrdiff_t idx = uniform(0, de.length == 0 ? 1 : de.length);
  // 	/*writefln("NEW %d at %d size(%u) i(%d) round %d", t, idx,
  // 	  de.length, i, k);*/
  // 	de.insert(idx, t);

  // 	bool found = true;
  //     inner: for(int j = 0; j < set.length; ++j) {
  // 	  if(set[j]) {
  // 	    foreach(it; de) {
  // 	      if(it == j) {
  // 		continue inner;
  // 	      }
  // 	    }
  // 	    writefln("did not found %d", j);
  // 	    found = false;
  // 	    break;
  // 	  }
  // 	}
  // 	if(!found) { foreach(it; de) write(it, ' '); writeln(); }
  // 	assert(found);
  //     }

  //     while(!de.empty) {
  // 	ptrdiff_t idx = uniform(0, de.length == 0 ? 1 : de.length);
  // 	int re = de.remove(idx);
  // 	/*writefln("REMOVE %d idx %d size %u round %d", re, idx,
  // 	  de.length, k);*/
  // 	set[re] = false;
  // 	bool found = true;
  //     inner2: for(int j = 0; j < set.length; ++j) {
  // 	  if(set[j]) {
  // 	    foreach(it; de) {
  // 	      if(it == j) {
  // 		continue inner2;
  // 	      }
  // 	    }
  // 	    writefln("did not found %d", j);
  // 	    found = false;
  // 	    break;
  // 	  }
  // 	}
  // 	if(!found) { foreach(it; de) write(it, ' '); writeln(); }
  // 	assert(found);
  //     }

  //     foreach(idx, it; set) {
  // 	assert(!it, to!(string)(idx));
  //     }
  //   }
  // }

  unittest { // pushFront removeBack
    for(int s = 1; s < 10; ++s) {
      Queue!(int) de;
      int count = 1000;
      for(int i = 0; i < count; ++i) {
  	de.pushFront(i);
  	assert(de.front() == i);
  	assert(de.length == i+1, format("i(%u) head(%d) size(%d) data[%u]"
  					, de.length, de.head, de.size, de.data.length));
  	int j = i;
  	foreach(idx, it; de) {
  	  assert(it == j, format("de[%u](%d) != j(%d)", idx, it, j));
  	  --j;
  	}
      }


      for(int i = 0; i < count; ++i) {
  	int b;
  	de.removeBack();
  	assert(de.length == count-i-1);
      }
    }
  }

  unittest { // pushFront removeFront
    for(int s = 1; s < 10; ++s) {
      Queue!(int) de;
      int count = 1000;
      for(int i = 0; i < count; ++i) {
  	de.pushFront(i);
  	assert(de.front() == i);
  	assert(de.length == i+1, format("i(%u) head(%d) size(%d) data[%u]"
  					, de.length, de.head, de.size, de.data.length));
  	int j = i;
  	foreach(idx, it; de) {
  	  assert(it == j, format("de[%u](%d) != j(%d)", idx, it, j));
  	  --j;
  	}
      }


      for(int i = count-1; i >= 0; --i) {
  	int b;
  	de.removeFront();
  	assert(de.length == i, format("%d %d", de.length, i));
      }
    }
  }

  unittest { // pushBack removeBack
    for(int s = 1; s < 10; ++s) {
      Queue!(int) de;
      int count = 1000;
      for(int i = 0; i < count; ++i) {
  	de.pushBack(i);
  	assert(de.back() == i);
  	assert(de.length == i+1, format("i(%u) head(%d) size(%d) data[%u]"
  					, de.length, de.head, de.size, de.data.length));
      }

      for(int i = count-1; i >= 0; --i) {
  	int b;
  	de.removeBack();
  	assert(de.length == i);
      }
    }
  }

  unittest { // pushBack removeFront
    for(int s = 1; s < 10; ++s) {
      Queue!(int) de;
      int count = 1000;
      for(int i = 0; i < count; ++i) {
  	de.pushBack(i);
  	assert(de.back() == i);
  	assert(de.front() == 0);
  	assert(de.length == i+1, format("i(%u) head(%d) size(%d) data[%u]"
  					, de.length, de.head, de.size, de.data.length));
  	int j = 0;
  	foreach(idx, it; de) {
  	  assert(it == j, format("de[%u](%d) != j(%d)", idx, it, j));
  	  ++j;
  	}
      }


      for(int i = 0; i < count; ++i) {
  	int b;
  	de.removeFront();
  	assert(de.length == count-i-1, format("%d %d", de.length,
  					      count-i-1));
      }
    }
  }


}


// array init foreach and simple iterator test
unittest {
  import std.conv: to;
  import std.string: format;
  Queue!(int) de1 = [1,2,3,4,5,6];
  foreach(idx, it; [1,2,3,4,5,6]) {
    assert(de1[idx] == it);
  }

  foreach_reverse(idx, it; [6,5,4,3,2,1]) {
    assert(de1[de1.length-idx-1] == it, format("de1[%u] == %d it(%d)", 
					       idx, de1[de1.length-idx-1], it)
	   );
  }

  auto jt = de1[];
  assert(jt.back() == 6, to!string(jt));
  assert(de1.back() == 6, to!string(de1.back()));
  assert(de1.front() == 1, to!string(de1.front()));

  const Queue!(int) d1const = de1;
  auto it2 = d1const[];
  assert(d1const.back() == 6, to!string(d1const.back()));
  assert(d1const.front() == 1, to!string(d1const.front()));
}

unittest { // insert unittest
  Queue!(int) de1 = [1,2,3,5,6];
  de1.insert(3, 4);
  foreach(idx, it; [1,2,3,4,5,6]) {
    de1[idx] = it;
  }
  de1.insert(0,0);
  foreach(idx, it; [0,1,2,3,4,5,6]) {
    de1[idx] = it;
  }
  de1.insert(6,8);
  foreach(idx, it; [0,1,2,3,4,5,6]) {
    de1[idx] = it;
  }
}

unittest { // simple iterator unittest
  import std.string: format;
  int[] arr = [1,2,3,4,5,6];
  Queue!(int) de1 = arr;
  auto it = de1[];
  auto tt = it.save();
  int idx = 0;
  foreach(jt; it) {
    assert(jt == arr[idx++], format("%d == %d", jt, arr[idx]));
  }
  assert(idx == arr.length, 
	 format("idx(%u) arr.length(%u)", idx, arr.length));
  idx = 0;
  foreach(jt; tt) {
    assert(jt == arr[idx], format("%d == %d", jt, arr[idx]));
    ++idx;
  }

  it = de1[];
  idx = 5;
  foreach_reverse(jt; it) {
    assert(jt == arr[idx], format("%d == %d idx(%u)", jt, arr[idx], idx));
    --idx;
  }
  assert(idx == -1, format("idx(%u)", idx));
}


unittest { 	// benchmark against appender, slist, dlist for appending at the
  // end
  import std.datetime;
  import std.conv: to;
  import std.container;
  import std.string: format;
  import std.array: appender;
  import std.stdio;
  void fillAppender() {
    auto app = appender!(int[])();
    foreach(it; 1..2049) {
      app.put(it);	
    }
	
    for(int i = 2049; i < 4098; i+=3) {
      app.put([i, i+1, i+2]);
    }
	
    for(int i = 1; i < 4098; ++i) {
      assert(app.data[i-1] == i);
    }
  }
	
  void fillDList() {
    auto dl = DList!(int)();
    foreach(it; 1..2049) {
      dl.insertBack(it);	
    }
	
    for(int i = 2049; i < 4098; i+=3) {
      dl.insertBack([i, i+1, i+2]);
    }
	
    int j = 1;
    foreach(it; dl) {
      assert(it == j++);
    }
  }
	
  void fillSList() {
    auto sl = SList!(int)();
    foreach(it; 1..2049) {
      sl.insertAfter(sl[], it);	
    }
	
    for(int i = 2049; i < 4098; i+=3) {
      sl.insertAfter(sl[], [i, i+1, i+2]);
    }
	
    int j = 1;
    foreach(it; sl) {
      assert(it == j++);
    }
  }
	
  void fillQueue() {
    Queue!(int) de;
    foreach(it; 1..2049) {
      de.pushBack(it);	
    }
	
    for(int i = 2049; i < 4098; i+=3) {
      de.pushBack([i, i+1, i+2]);
    }
	
    for(int i = 1; i < 4098; ++i) {
      assert(de[i-1] == i);
    }
  }

  void fillArray() {
    int[] a = new int[0];
    foreach(it; 1..2049) {
      a = a ~ [it];
    }

    for(int i = 2049; i < 4098; i+=3) {
      a = a ~ [i, i+1, i+2];
    }

    int j = 1;
    foreach(it; a) {
      assert(it == j++, format("it(%d) j(%d)", it, j));
    }
  }

  // enum numIterations = 300;
  // auto r = benchmark!(fillAppender, fillSList, fillDList, fillQueue,
  // 		      fillArray)(numIterations);	
  // writeln("Append 4097 elements at the end at run foreach once");
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "Appender", "put",
  // 	   numIterations, r[0].to!("msecs",int),
  // 	   r[0].to!("msecs",int)/to!float(numIterations));
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "SList", "insertBack",
  // 	   numIterations, r[1].to!("msecs",int),
  // 	   r[1].to!("msecs",int)/to!float(numIterations));
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "DList", "insertBack",
  // 	   numIterations, r[2].to!("msecs",int),
  // 	   r[2].to!("msecs",int)/to!float(numIterations));
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "Queue", "pushBack",
  // 	   numIterations, r[3].to!("msecs",int),
  // 	   r[3].to!("msecs",int)/to!float(numIterations));
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "int[]", "a ~ []",
  // 	   numIterations, r[4].to!("msecs",int),
  // 	   r[4].to!("msecs",int)/to!float(numIterations));
}

unittest {
  import std.datetime;
  import std.conv: to;
  import std.container;
  import std.string: format;
  import std.stdio;
  void fillDList() {
    auto sl = DList!(int)();
    foreach(it; 1..2049) {
      sl.insertFront(it);	
    }
	
    for(int i = 2049; i < 4098; i+=3) {
      sl.insertFront([i+2, i+1, i]);
    }
	
    int j = 4097;
    foreach(it; sl) {
      assert(it == j--);
    }
  }

  void fillSList() {
    auto sl = SList!(int)();
    foreach(it; 1..2049) {
      sl.insertFront(it);	
    }
	
    for(int i = 2049; i < 4098; i+=3) {
      sl.insertFront([i+2, i+1, i]);
    }
	
    int j = 4097;
    foreach(it; sl) {
      assert(it == j--, format("it(%d) j(%d)", it, j));
    }
  }
	
  void fillQueue() {
    Queue!(int) de;
    foreach(it; 1..2049) {
      de.pushFront(it);	
    }
	
    for(int i = 2049; i < 4098; i+=3) {
      de.pushFront([i, i+1, i+2]);
    }

    //foreach(it; de) {write(it, ' '); } writeln();

    int j = 4097;
    foreach(it; de) {
      assert(it == j--, format("it(%d) j(%d)", it, j));
    }
  }

  void fillArray() {
    int[] a = new int[0];
    foreach(it; 1..2049) {
      a = [it] ~ a;	
    }

    for(int i = 2049; i < 4098; i+=3) {
      a = [i+2, i+1, i] ~ a;
    }

    int j = 4097;
    foreach(it; a) {
      assert(it == j--, format("it(%d) j(%d)", it, j));
    }
  }

  // enum numIterations = 300;
  // auto r = benchmark!(fillSList, fillDList, fillQueue,fillArray)(numIterations);	
  // writeln();
  // writeln("Append 4097 elements at the begining at run foreach once");
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "SList",
  // 	   "insertFront", numIterations, r[0].to!("msecs",int),
  // 	   r[0].to!("msecs",int)/to!float(numIterations));
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "DList",
  // 	   "insertFront", numIterations, r[1].to!("msecs",int),
  // 	   r[1].to!("msecs",int)/to!float(numIterations));
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "Queue",
  // 	   "pushFront", numIterations, r[2].to!("msecs",int),
  // 	   r[2].to!("msecs",int)/to!float(numIterations));
  // writefln("Milliseconds to call %8s %11s %d times: %5s average: %7.3f", "int[]",
  // 	   "[] ~ a", numIterations, r[3].to!("msecs",int),
  // 	   r[3].to!("msecs",int)/to!float(numIterations));
}

unittest { // sort test
  import std.algorithm;
  Queue!(int) de = [4,5,7,3,2,1,0];
  Queue!(int) deS = [4,5,7,3,2,1,0];
  Queue!(int) de2 = [4,5,7,3,2,1,0];
  auto r = de[];
  std.algorithm.sort!("a < b")(r);
  //sort!("a < b")(r);
  for(size_t i = 0; i < de.length-1; ++i) {
    assert(de[i] <= de[i+1]);
  }
}

