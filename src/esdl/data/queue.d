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
import std.range: RangeElementType = ElementType;
import std.array: array;


template isQueue(T)
{
  static if (is (T: Queue!L, L))
    enum bool isQueue = true;
  else
    enum bool isQueue = false;
}

template QueueElementType(T) if (isQueue!T)
{
  static if (is (T: Queue!L, L))
    alias QueueElementType = L;
  else
    static assert (false);
}

struct Queue(T) {
  import std.traits: isIterable, isArray;
  import std.range: hasLength;
  import std.string: format;

  import core.stdc.string: memmove, memset;

  alias ElementType = T;

  private T[] _array;

  private size_t _head;
  private size_t _size;

  final private void _assimilateArray(T[] arr) @safe {
    _array = arr;
    _head = 0;
    _size = arr.length;
  }

  final private void _move(size_t didx, size_t sidx, size_t count) {
    memmove(_array.ptr+didx, _array.ptr+sidx, (count)*T.sizeof);
  }

  final private void _clear(size_t idx, size_t count) {
    memset(_array.ptr+idx, 0, (count)*T.sizeof);
  }

  final public size_t getCapacity() const @safe nothrow { return _array.length; }

  unittest {
    Queue!(int) q;
    assert (q.getCapacity() == 0);
    q ~= 0;
    assert (q.getCapacity() != 0);
  }

  public this(T[] arr, size_t head, size_t size) {
    _array = arr;
    _head = head;
    _size = size;
  }
  
  public this(this) @safe  { }

  public this(R)(R values) @safe
  if (isIterable!R && is(RangeElementType!R: T) && !(isArray!R)) {
    T[] arr = array(values);
    this._assimilateArray(arr);
  }

  public this(const T[] values) @safe {
    this._assimilateArray(values.dup);
  }

  public this(T[] values) @safe {
    this._assimilateArray(values);
  }

  public Queue!T opAssign(R)(R values) @safe
  if (isIterable!R && is(RangeElementType!R: T) && !(isArray!R)) {
    T[] arr = array(values);
    this._assimilateArray(arr);
    return this;
  }

  public Queue!T opAssign(const T[] values) @safe {
    this._assimilateArray(values.dup);
    return this;
  }
    
  public Queue!T opAssign(Queue!T q) @safe {
    this._head = q._head;
    this._size = q._size;
    this._array = q._array;
    return this;
  }

  unittest {
    int[] a = [0, 1, 2, 3, 4, 5];
    Queue!(int) q = a;

    assert (a.length = q.length);
    foreach (size_t i, int e; q) {
      assert (a[i] == e, format("%d[%d]", i, e));
    }
  }

  public Queue!T clone() const @safe {
    Queue!T q;
    q._array = this._array.dup;
    q._head = this._head;
    q._size = this._size;
    return q;
  }

  public Queue!T clone() @safe {
    Queue!T q;
    q._array = this._array.dup;
    q._head = this._head;
    q._size = this._size;
    return q;
  }

  alias dup = clone;

  public bool opEquals(R)(R r) const @trusted
    if (isIterable!R && is (RangeElementType!R: T) && hasLength!R)
  {
    if (this.length() != r.length) {
      return false;
    }
    foreach (idx, it; r) {
      static if (is (T == class)) {
  	if (this[idx] is null && it is null) continue;
  	if (this[idx] is null || it is null) return false;
      }
      if (this[idx] != it) return false;
    }
    return true;
  }

  public T[] toArray() const @trusted {
    T[] ret = new T[_size];
    if (_head == 0) ret[] = _array[0.._size];
    else {
      if (_size + _head > _array.length) {
	ret[0.._array.length-_head] = _array[_head..$];
	ret[_array.length-_head.._size] = _array[0.._size+_head-_array.length];
      }
      else {
	ret[0.._size] = _array[_head.._head+_size];
      }
    }
    return ret;
  }

  string toString() {
    return this.to!(string);
  }

  void toString(void delegate(scope const(char)[]) sink,
		const FormatSpec!char f) {
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

  public size_t length() const @safe nothrow { return _size; }
  public void length(size_t nsize) { 
    if (nsize > _size) while (nsize >= _array.length) _growCapacity();
    _size = nsize;
  }
  public size_t opDollar() const @safe nothrow { return this.length(); }

  public void growCapacity() @safe {
    _growCapacity();
  }

  private void _growCapacity() @trusted { // does not change _size
    T[] arr;
    if (_array.length == 0) {
      arr = new T[8];
    }
    else {
      arr = new T[this._array.length*2];
    }
    assert(arr !is null);

    if (_head + _size <= _array.length) {
      arr[0.._size] = _array[_head.._head+_size];
    }
    else {
      size_t chunk0 = _array.length-_head;
      size_t chunk1 = _size-chunk0;
      arr[0..chunk0] = _array[_head..$];
      arr[chunk0.._size] = _array[0..chunk1];
    }
    this._array = arr;
    this._head = 0;
  }

  private size_t _tail() {
    assert (_size <= _array.length);
    return (_head + _size) % _array.length;
  }
  
  public void opOpAssign(string op)(size_t shift) @trusted
    if (op == "<<")
  {				// shift the circular buffer left
    assert (shift < _size);
    assert (_size <= _array.length);
    if (_size == _array.length) {
      _head = (_head + shift) % _size;
    }
    else {
      auto tail = _tail;
      auto len = _array.length;
      if (_head < tail) {
	if (tail + shift <= len) {
	  // _array[tail..tail+shift] = _array[_head.._head+shift];
	  _move(tail, _head, shift);
	}
	else {
	  // _array[tail..len] = _array[_head.._head+len-tail];
	  _move(tail, _head, len-tail);
	  // _array[0..shift+tail-len] = _array[_head+len-tail.._head+shift];
	  _move(0, _head+len-tail, shift+tail-len);
	}
	_head = _head + shift;
      }
      else {
	if (_head + shift <= len) {
	  // _array[tail..tail+shift] = _array[_head.._head+shift];
	  _move(tail, _head, shift);
	}
	else {
	  // _array[tail..tail+len-_head] = _array[_head.._head+len-_head];
	  _move(tail, _head, len-_head);
	  // _array[tail+len-_head..tail+shift] = _array[0..shift+_head-len];
	  _move(tail+len-_head, 0, shift+_head-len);
	}
	_head = (_head + shift) % len;
      }
    }
  }
  
  public void opOpAssign(string op)(size_t shift) @trusted
    if (op == ">>")
  {				// shift the circular buffer left
    assert (shift < _size);
    assert (_size <= _array.length);
    if (_size == _array.length) {
      _head = (_size + _head - shift) % _size;
    }
    else {
      auto tail = _tail;
      auto len = _array.length;
      if (_head < tail) {
	if (_head >= shift) {
	  // _array[_head-shift..head] = _array[tail-shift..tail];
	  _move(_head-shift, tail-shift, shift);
	}
	else {
	  // _array[0.._head] = _array[tail-_head..tail];
	  _move(0, tail-_head, _head);
	  // _array[len+_head-shift..len] = _array[tail-shift..tail-_head]
	  _move(len+_head-shift, tail-shift, shift-_head);
	}
	_head = (len + _head - shift) % len;
      }
      else {
	if (tail >= shift) {
	  // _array[_head-shift.._head] = _array[tail-shift..tail];
	  _move(_head-shift, tail-shift, shift);
	}
	else {
	  // _array[_head-tail.._head] = _array[0..tail]
	  _move(_head-tail, 0, tail);
	  // _array[_head-shift.._head-tail] = _array[len+tail-shift..len];
	  _move(_head-shift, len+tail-shift, shift-tail);
	}
	_head = _head - shift;
      }
    }
  }
  
  public void _insert(ptrdiff_t idx, size_t count) @trusted {
    while (count + _size >= _array.length) growCapacity();

    if (idx < 0) idx = this._size + idx;
    assert (idx >= 0);
    
    auto len = _array.length;
    size_t fidx = (idx + _head) % len;
    auto tail = _tail;

    if (idx >= _size / 2) {
      if (fidx < tail) {
	if (tail + count <= len || fidx + count >= len) {
	  _move((fidx+count)%len, fidx, tail-fidx);
	}
	else if (fidx + count < len && tail + count > len) {
	  _move(0, len-count, tail+count-len);
	  _move(fidx+count, fidx, len-(fidx+count));
	}
	else {
	  assert (false);
	}
      }
      else {
	if (fidx + count <= len) {
	  _move(count, 0, tail);
	  _move(0, len-count, count);
	  _move(fidx+count, fidx, len-(fidx+count));
	}
	else {
	  _move(count, 0, tail);
	  _move((fidx+count)%len, fidx, len-fidx);
	}
      }
    }
    else {
      if (_head < fidx) {
	if (_head >= count || fidx <= count) {
	  _move((len+_head-count)%len, _head, idx);
	}
	else if (_head < count && fidx > count) {
	  _move(len+_head-count, _head, count-_head);
	  _move(0, count, fidx-count);
	}
	else {
	  assert (false);
	}
      }
      else {
	if (fidx > count) {
	  _move(_head-count, _head, len-_head);
	  _move(len-count, 0, count);
	  _move(0, count, fidx-count);
	}
	else {
	  _move(_head-count, _head, len-_head);
	  _move(len-count, 0, fidx);
	}
      }
      _head = (len + _head - count) % len;
    }
    _size = _size + count;
  }


  public void _remove(ptrdiff_t idx, size_t count)  {
    if (idx < 0) idx = this._size + idx;
    assert (idx >= 0);
    
    auto len = _array.length;
    auto tail = _tail;

    if (idx >= (_size - count) / 2) {
      size_t fidx = (idx + _head + count) % len;
      if (fidx < tail) {
	if (tail <= count || fidx >= count) {
	  _move((len+fidx-count)%len, fidx, tail-fidx);
	}
	else if (fidx < count && tail > count) {
	  _move(len+fidx-count, fidx, count-fidx);
	  _move(0, count, tail-count);
	}
	else {
	  assert (false);
	}
      }
      else {
	if (tail > count) {
	  _move(fidx-count, fidx, len-fidx);
	  _move(len-count, 0, count);
	  _move(0, count, tail-count);
	}
	else {
	  _move(fidx-count, fidx, len-fidx);
	  _move(len-count, 0, tail);
	}
      }
    }
    else {
      size_t fidx = (idx + _head) % len;
      if (_head < fidx) {
	if (fidx + count <= len || _head + count >= len) {
	  _move((_head+count)%len, _head, idx);
	}
	else if (fidx + count > len || _head + count < len) {
	  _move(0, len-count, fidx+count-len);
	  _move(_head+count, _head, len-_head-count);
	}
	else {
	  assert (false);
	}
      }
      else {
	if (_head + count < len) {
	  _move(count, 0, fidx);
	  _move(0, len-count, count);
	  _move(_head+count, _head, len-_head-count);
	}
	else {
	  _move(count, 0, fidx);
	  _move((_head+count)%len, _head, len-_head);
	}
      }
      _head = (_head + count) % len;
    }
    _size = _size - count;
  }

  public Queue!(T) opSlice(size_t low, size_t high) @safe {
    assert(high <= this.length);
    Queue!(T) slice = this;	// postblit
    size_t numPopBack = this.length - high;
    slice.removeFront(low);
    slice.removeBack(numPopBack);
    return slice;
  }

  public Range!(Queue!T, T) opSlice() @safe {
    return Range!(Queue!T, T)(this, 0, this.length());
  }

  public Range!(const Queue!T, const(T)) opSlice() const @safe {
    return Range!(const Queue!T, const T)(this, 0, this.length());
  }

  struct Range(Q, E) {
    private Q* _queue;

    private size_t _head;	// offset from _queue._head
    private size_t _size;

    package this(ref Q queue,
		 const size_t head,
		 const size_t size) @trusted {
      assert (head + size <= queue.length);
      _queue = &queue;
      _head = head;
      _size = size;
    }

    public size_t length() const @safe nothrow { return _size; }
    public size_t opDollar() const @safe nothrow { return _size; }
    public ref E opIndex(const size_t i) @safe { return (*_queue)[_head+i]; }
    public ref const(E) opIndex(const size_t i) const @safe { return (*_queue)[_head+i]; }
    public Range!(Q, E) opSlice(size_t head, size_t tail) @safe {
      assert (head >= 0 && tail > head && tail <= _size);
      return Range!(Q, E)(*_queue, _head+head, tail-head);
    }

    public ref E front() @safe { return (*_queue)[_head]; }
    public ref E back() @safe { return (*_queue)[_head+_size-1]; }
    public bool empty() const @safe nothrow { return _size == 0; }
    public Range!(Q, E) save() @safe nothrow {
      return Range!(Q, E)(*_queue, _head, _size);
    }
    public void popFront() @safe nothrow {
      assert (! empty());
      _head += 1;
      _size -= 1;
    }
    public void popBack() @safe nothrow {
      assert (! empty());
      _size -= 1;
    }
    public void opAssign(R)(R values)
      if (isIterable!R && is (RangeElementType!R: T) && hasLength!R)
    {
      import std.stdio;
      static if (isArray!R) {
	size_t head = (_head + _queue._head) % _queue._array.length;
	if (head + values.length <= _queue._array.length) {
	  _queue._array[head..head+values.length] = values;
	}
	else {
	  size_t len0 = _queue._array.length-head;
	  _queue._array[head..$] = values[0..len0];
	  _queue._array[0..values.length-len0] = values[len0..$];
	}
      }
      else {	    // handle queues and queue ranges more efficiently
	foreach (i, val; values) {
	  this[i] = val;
	}
      }
    }
      
  }

  public ref T opIndex(const ptrdiff_t idx) @trusted {
    if (idx >= 0) {	
      assert (idx <= _size);
      return _array[(_head+idx) % _array.length];
    }
    else {
      ptrdiff_t nIdx = _size + idx;
      assert (nIdx <= (_size+1) && nIdx >= 0, 
	      format ("out of bound index %d for Queue of length %u",
		      idx, this.length()));
      return _array[(_head+nIdx) % _array.length];
    }
  }

  public ref const(T) opIndex(const ptrdiff_t idx) const @trusted {
    if (idx >= 0) {	
      assert (idx <= _size);
      return _array[(_head+idx) % _array.length];
    }
    else {
      ptrdiff_t nIdx = _size + idx;
      assert (nIdx <= (_size+1) && nIdx >= 0, 
	      format ("out of bound index %d for Queue of length %u",
		      idx, this.length()));
      return _array[(_head+nIdx) % _array.length];
    }
  }

  public void removeFront(const size_t count = 1) @safe {
    assert (count <= _size);
    _head = (_head + count) % _array.length;
    _size -= count;
  }

  public void removeBack(const size_t count = 1) @safe {
    assert (count <= _size);
    _size -= count;
  }
  
  public void pushFront(T value) @safe {
    if (_size+1 >= _array.length) _growCapacity();
    _head = _head == 0 ? _array.length-1 : _head-1;
    _size += 1;
    _array[_head] = value;
  }

  public void pushFront(R)(R values) @safe
    if (isIterable!R && is (RangeElementType!R: T))
  {
    static if (hasLength!R) {
      size_t len = values.length;
      while (_size+len >= _array.length) _growCapacity();
      _head = (_array.length + _head - len) % _array.len;
      _size += len;
      this[][0..len] = values;
    }
    else {
      foreach (val; values) this.pushFront(val);
    }
  }

  public void pushBack(T value) @safe {
    if (_size+1 >= _array.length) _growCapacity();
    _size += 1;
    _array[_tail] = value;
  }

  public void pushBack(R)(R values) @safe
    if (isIterable!R && is (RangeElementType!R: T))
  {
    static if (hasLength!R) {
      size_t len = values.length;
      while (_size+len >= _array.length) _growCapacity();
      _size += len;
      this[][$-len..$] = values;
    }
    else {
      foreach (val; values) this.pushBack(val);
    }
  }

  public void opOpAssign(string op, R)(R values) @trusted
       if (op == "~" && isIterable!R && is (RangeElementType!R: T))
  {
    this.pushBack(values);
  }

  public void opOpAssign(string op, R)(R value) @safe
    if (op == "~" && is (R unused: T))
  {
    this.pushBack(value);
  }

  public Queue!T opBinary(string op, R)(R values) @safe
    if (op == "~" && isIterable!R && is(RangeElementType!R: T))
  {
    Queue!T ret = this;
    ret ~= values;
    return ret;
  }

  public Queue!T opBinary(string op, R)(R value) @safe
    if (op == "~" && is(R unused: T))
  {
    Queue!T ret = this;
    ret ~= value;
    return ret;
  }

  public Queue!T opBinaryRight(string op, R)(R values) @safe
    if (op == "~" && isIterable!R && is(RangeElementType!R: T))
  {
    Queue!T ret;
    ret ~= values;
    ret ~= this;
    return ret;
  }

  public Queue!T opBinaryRight(string op, R)(R value) @safe
    if (op == "~" && is(R unused: T))
  {
    Queue!T ret;
    ret ~= value;
    ret ~= this;
    return ret;
  }

  public void insert(size_t idx, T value) @safe {
    _insert(idx, 1);
    this[idx] = value;
  }

  public void insert(R)(size_t idx, R values) @safe
    if (isIterable!R && is (RangeElementType!R: T))
  {
    static if (hasLength!R) {
      size_t len = values.length;
      _insert(idx, len);
      this[][idx..idx+len] = values;
    }
    else {
      foreach (i, val; values) this.insert(idx+i, val);
    }
  }

  public int opApply(int delegate(ref size_t, ref const T) dg) const {
    for (size_t idx = 0; idx < this._size; ++idx) {
      if (int r = dg(idx, this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public int opApplyReverse(int delegate(ref size_t, ref const T) dg) const {
    for (size_t idx = this._size-1; idx < ptrdiff_t.max; --idx) {
      if (int r = dg(idx, this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public int opApply(int delegate(ref size_t, ref T) dg) {
    for (size_t idx = 0; idx < this._size; ++idx) {
      if (int r = dg(idx, this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public int opApplyReverse(int delegate(ref size_t, ref T) dg) {
    for (size_t idx = this._size-1; idx < ptrdiff_t.max; --idx) {
      if (int r = dg(idx, this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public int opApply(int delegate(const ref T) dg) const {
    for (size_t idx = 0; idx < this._size; ++idx) {
      if (int r = dg(this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public int opApplyReverse(int delegate(const ref T) dg) const {
    for (size_t idx = this._size-1; idx < ptrdiff_t.max; --idx) {
      if (int r = dg(this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public int opApply(int delegate(ref T) dg) {
    for (size_t idx = 0; idx < this._size; ++idx) {
      if (int r = dg(this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public int opApplyReverse(int delegate(ref T) dg) {
    for (size_t idx = this._size-1; idx < ptrdiff_t.max; --idx) {
      if (int r = dg(this._array[(this._head+idx)%this._array.length])) {
	return r;
      }
    }
    return 0;
  }

  public bool empty() const @safe nothrow {
    return _size == 0;
  }

  public ref T front() @safe {
    assert (! this.empty);
    return _array[_head];
  }

  public ref const(T) front() const @safe {
    assert (! this.empty);
    return _array[_head];
  }

  public void popFront(ref T f) {
    f = front();
    removeFront();
  }
  
  public ref T back() @safe {
    assert (! this.empty);
    return _array[(_head+_size-1)%_array.length];
  }
	
  public ref const(T) back() const @safe {
    assert (! this.empty);
    return _array[(_head+_size-1)%_array.length];
  }
	
  public void popBack(ref T f) {
    f = this.back();
    this.removeBack();
  }

}
