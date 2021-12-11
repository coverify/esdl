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
  
  public this(const Queue!T q, size_t head, size_t tail) const {
    _array = q._array;
    _head = head;
    _size = tail - head;
  }
  
 public this(this) @safe { }	// postblit

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

  unittest {
    int[] a = [0, 1, 2, 3, 4, 5];
    Queue!(int) tmp = a;
    Queue!(int) q = tmp.dup;

    assert (a.length = q.length);
    foreach (size_t i, int e; q) {
      assert (a[i] == e, format("%d[%d]", i, e));
    }
  }

  public bool opEquals(R)(R r) const @trusted
    if (isIterable!R && is (RangeElementType!R: T) && hasLength!R)
  {
    if (this.length() != r.length) return false;

    foreach (idx, it; r) {
      static if (is (T == class)) {
  	if (this[idx] is null && it is null) continue;
  	if (this[idx] is null || it is null) return false;
      }
      if (this[idx] != it) return false;
    }
    return true;
  }

  unittest {
    int[] a = [0, 1, 2, 3, 4, 5];
    Queue!(int) tmp = a;
    Queue!(int) q = tmp.dup;

    assert (q == a);
    assert (q == tmp);

    q ~= 42;

    assert (q != a);
    assert (q != tmp);
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

  unittest {
    int[] a = [0, 1, 2, 3, 4, 5];
    Queue!(int) q = a;
    int[] arr = q.toArray;

    assert (arr == a);
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

  unittest {
    Queue!(int) q = [0, 1, 2, 3, 4, 5];
    assert (q.to!string == "[0, 1, 2, 3, 4, 5]", q.to!string);
  }

  public size_t length() const @safe nothrow { return _size; }
  public void length(size_t nsize) { 
    if (nsize > _size) while (nsize >= _array.length) _growCapacity();
    _size = nsize;
  }
  public size_t opDollar() const @safe nothrow { return this.length(); }

  unittest {
    Queue!(int) q;
    assert (q.length == 0);
    q = [0, 1, 2, 3, 4, 5];
    assert (q.length == 6);
    for (size_t i=0; i!=10; ++i) q._growCapacity();
    assert (q.length == 6);
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

  unittest {
    Queue!(int) q = [0, 1, 2, 3, 4, 5];
    Queue!(int) p = q.dup;

    p <<= 4;
    p >>= 2;
    p >>= 2;

    assert(q == p);
  }

  
  
  private void _insert(ptrdiff_t idx, size_t count) @trusted {
    while (count + _size >= _array.length) _growCapacity();

    if (idx < 0) idx = this._size + idx;
    assert (idx >= 0);
    
    auto len = _array.length;
    size_t fidx = (idx + _head) % len;
    auto tail = _tail;

    if (idx >= _size / 2) {
      if (fidx <= tail) {
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
      if (_head <= fidx) {
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


  private void _remove(ptrdiff_t idx, size_t count) {
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
      if (_head <= fidx) {
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

  public const (Queue!(T)) opSlice(size_t low, size_t high) const @safe {
    assert(high <= this.length);
    const (Queue!(T)) slice = const (Queue!(T)) (this, low, high);

    return slice;
  }

  unittest {
    Queue!(int) q = [0, 1, 2, 3, 4, 5];
    immutable Queue!(int) r = [0, 1, 2, 3, 4, 5];
    q._growCapacity();

    assert (q[0..2] == [0, 1]);
    assert (r[0..2] == [0, 1]);
    q <<= 3;
    assert (q[0..2] == [3, 4]);
  }

  public Range!(Queue!T, T) opSlice() @safe {
    return Range!(Queue!T, T)(this, 0, this.length());
  }

  unittest {
    Queue!(int) q = [0, 1, 2, 3, 4, 5];
    q._growCapacity();

    assert (q[] == [0, 1, 2, 3, 4, 5]);
  }

  public const(Range!(Queue!T, T)) opSlice() const @safe {
    return const(Range!(Queue!T, T))(this, 0, this.length());
  }

  struct Range(Q, E) {
    private Q* _queue;

    private size_t _head;	// offset from _queue._head
    private size_t _size;

    private E[] _array() {
      return _queue._array;
    }

    private const(E[]) _array() const {
      return _queue._array;
    }

    package this(ref Q queue,
		 const size_t head,
		 const size_t size) @trusted {
      assert (head + size <= queue.length);
      _queue = &queue;
      _head = head;
      _size = size;
    }

    package this(ref const(Q) queue,
		 const size_t head,
		 const size_t size) const @trusted {
      assert (head + size <= queue.length);
      _queue = &queue;
      _head = head;
      _size = size;
    }

    public size_t length() const @safe nothrow { return _size; }

    unittest {
      Queue!(int) q = [0, 1, 2, 3, 4, 5];
      q._growCapacity();

      assert (q[].length == 6);
      assert (q.length == 6);

      q ~= 42;
      
      assert (q[].length == 7);
      assert (q.length == 7);

      auto r = q[].save();
      q ~= [42, 100];

      assert (r.length == 7);
      assert (q.length == 9);
    }

    public size_t opDollar() const @safe nothrow { return _size; }

    public ref E opIndex(const size_t i) @safe { return (*_queue)[_head+i]; }

    public ref const(E) opIndex(const size_t i) const @safe {
      return (*_queue)[_head+i];
    }

    public const(Range!(Q, E)) opSlice(size_t head, size_t tail) const @safe {
      assert (head >= 0 && tail > head && tail <= _size);
      return const(Range!(Q, E))(*_queue, _head+head, tail-head);
    }

    public Range!(Q, E) opSlice(size_t head, size_t tail) @safe {
      assert (head >= 0 && tail > head && tail <= _size);
      return Range!(Q, E)(*_queue, _head+head, tail-head);
    }

    unittest {
      Queue!(int) q = [0, 1, 2, 3, 4, 5];
      immutable Queue!(int) r = [0, 1, 2, 3, 4, 5];
      q._growCapacity();

      assert (q[][2] == 2);
      assert (q[][$-1] == 5);
      assert (q[][0..2] == [0, 1]);

      assert (r[][0] == 0);
      assert (r[][0..2] == [0, 1]);
    }
    
    public ref E front() @safe { return (*_queue)[_head]; }
    public ref E back() @safe { return (*_queue)[_head+_size-1]; }
    public bool empty() const @safe nothrow { return _size == 0; }
    unittest {
      Queue!(int) q = [0, 1, 2, 3, 4, 5];
      immutable Queue!(int) r = [0, 1, 2, 3, 4, 5];

      assert (q.front() == 0);
      assert (r.front() == 0);

      assert (q.back() == 5);
      assert (r.back() == 5);

      assert (! q.empty());
      assert (! r.empty());

      assert (Queue!int([]).empty());
      q.length = 0;
      assert (q.empty());
    }

    public Range!(Q, E) save() @safe nothrow {
      return Range!(Q, E)(*_queue, _head, _size);
    }

    unittest {
      Queue!int q = [0, 1, 2, 3, 4, 5];
      auto r = q[].save();

      assert (r == q[]);
    }
    
    public void popFront() @safe nothrow {
      assert (! empty());
      _head += 1;
      _size -= 1;
    }
    unittest {
      Queue!int q = [0, 1, 2, 3, 4, 5];
      auto r = q[].save();
      r.popFront();

      assert (r == [1, 2, 3, 4, 5]);
    }
    

    public void popBack() @safe nothrow {
      assert (! empty());
      _size -= 1;
    }
    unittest {
      Queue!int q = [0, 1, 2, 3, 4, 5];
      auto r = q[].save();
      r.popBack();

      assert (r == [0, 1, 2, 3, 4]);
    }
    

    public void opAssign(R)(R values) @trusted
      if (isIterable!R && is (RangeElementType!R: T) && hasLength!R)
    {
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
      
    unittest {
      Queue!int q = [0, 1, 2, 3, 4, 5];
      auto r = q[].save();
      r = [42, 43, 44, 45, 46, 47];

      assert (r == [42, 43, 44, 45, 46, 47]);
      assert (q == [42, 43, 44, 45, 46, 47]);
    }
    
    public bool opEquals(R)(R r) const @trusted
      if (isIterable!R && is (RangeElementType!R: T) && hasLength!R)
    {
      if (this.length() != r.length) return false;

      foreach (idx, it; r) {
	static if (is (T == class)) {
	  if (this[idx] is null && it is null) continue;
	  if (this[idx] is null || it is null) return false;
	}
	if (this[idx] != it) return false;
      }
      return true;
    }


    public int opApply(int delegate(ref size_t, ref const T) dg) const {
      for (size_t idx = 0; idx < this._size; ++idx) {
	if (int r = dg(idx, this._array[(this._head+idx)%this._array.length])) {
	  return r;
	}
      }
      return 0;
    }

    public int opApplyReverse(int delegate(ref const size_t, ref const T) dg) const {
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

  } // struct Range ends here

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

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5];

    for (size_t i=0; i != q.length; ++i)  {
      assert (q[i] == i);
    }

    for (ptrdiff_t i=1; i != q.length; ++i)  {
      assert (q[-i] == 5 - i + 1);
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
  
  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5];
    q.removeFront(2);

    assert (q == [2, 3, 4, 5]);

    q = [0, 1, 2, 3, 4, 5];
    q.removeBack(2);

    assert (q == [0, 1, 2, 3]);
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
      _head = (_array.length + _head - len) % _array.length;
      _size += len;
      this[][0..len] = values;
    }
    else {
      foreach (val; values) this.pushFront(val);
    }
  }

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5];
    q.removeFront(2);
    q.pushFront([42, 41, 40, 39, 38]);

    assert (q == [42, 41, 40, 39, 38, 2, 3, 4, 5]);
    q.pushFront(42);
    assert (q == [42, 42, 41, 40, 39, 38, 2, 3, 4, 5]);
  }
  
  public void pushBack(T value) @safe {
    if (_size+1 >= _array.length) _growCapacity();
    _size += 1;
    _array[_tail-1] = value;
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

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5];
    q.removeBack(2);
    q.pushBack([42, 41, 40, 39, 38]);

    assert (q == [0, 1, 2, 3, 42, 41, 40, 39, 38]);
    q.pushBack(42);
    assert (q == [0, 1, 2, 3, 42, 41, 40, 39, 38, 42], q.to!string);
  }
  
  public void opOpAssign(string op, R)(R values) @trusted
       if (op == "~" && isIterable!R && is (RangeElementType!R: T))
  {
    this.pushBack(values);
  }

  public void opOpAssign(string op, V)(V value) @safe
    if (op == "~" && is (V unused: T))
  {
    this.pushBack(value);
  }

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5];
    q.removeBack(2);
    q ~= [42, 41, 40, 39, 38];

    assert (q == [0, 1, 2, 3, 42, 41, 40, 39, 38]);
    q ~= 42;
    assert (q == [0, 1, 2, 3, 42, 41, 40, 39, 38, 42], q.to!string);
  }

  public Queue!T opBinary(string op, R)(R values) @safe
    if (op == "~" && isIterable!R && is(RangeElementType!R: T))
  {
    Queue!T ret = this;
    ret ~= values;
    return ret;
  }

  public Queue!T opBinary(string op, V)(V value) @safe
    if (op == "~" && is(V unused: T))
  {
    Queue!T ret = this;
    ret ~= value;
    return ret;
  }

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5];
    Queue!int r = q ~ [42, 43, 44, 45, 46];

    assert (r == [0, 1, 2, 3, 4, 5, 42, 43, 44, 45, 46]);
  }
  
  public Queue!T opBinaryRight(string op, R)(R values) @safe
    if (op == "~" && isIterable!R && is(RangeElementType!R: T))
  {
    Queue!T ret;
    ret ~= values;
    ret ~= this;
    return ret;
  }

  public Queue!T opBinaryRight(string op, V)(V value) @safe
    if (op == "~" && is(V unused: T))
  {
    Queue!T ret;
    ret ~= value;
    ret ~= this;
    return ret;
  }

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5];
    Queue!int r = [42, 43, 44, 45, 46] ~ q;

    assert (r == [42, 43, 44, 45, 46, 0, 1, 2, 3, 4, 5]);
  }
  
  public void remove(ptrdiff_t idx, size_t count) {
    _remove(idx, count);
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

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    q.remove(4, 4);
    assert (q == [0, 1, 2, 3, 8, 9]);
    q.remove(0, 2);
    assert (q == [2, 3, 8, 9], q.to!string);
    q.insert(0, [0, 1]);
    assert (q == [0, 1, 2, 3, 8, 9], q.to!string);
    q.insert(6, [0, 1]);
    assert (q == [0, 1, 2, 3, 8, 9, 0, 1], q.to!string);
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

  unittest {
    Queue!int q = [];
    assert (q.empty());
    q = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert (! q.empty());
  }
  
  public ref T front() @safe {
    assert (! this.empty);
    return _array[_head];
  }

  public ref const(T) front() const @safe {
    assert (! this.empty);
    return _array[_head];
  }

  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert (q.front() == 0);
  }
  
  public void popFront(ref T f) {
    f = front();
    removeFront();
  }
  
  public void popFront() {
    removeFront();
  }
  
  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    int foo;
    q.popFront(foo);
    assert (foo == 0);
    q.popFront(foo);
    assert (foo == 1);
    q.popFront();
    q.popFront(foo);
    assert (foo == 3);
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

  public void popBack() {
    removeBack();
  }
  
  unittest {
    Queue!int q = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    int foo;
    q.popBack(foo);
    assert (foo == 9);
    q.popBack(foo);
    assert (foo == 8);
    q.popBack();
    q.popBack(foo);
    assert (foo == 6);
  }
}
