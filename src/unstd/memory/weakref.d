/** Weak reference implementation.

Copyright: Denis Shelomovskij 2013

License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).

Authors: Denis Shelomovskij
*/
module unstd.memory.weakref;


import core.exception;
import core.memory;
import core.atomic;

import unstd.array;
import unstd.casts;
import unstd.memory.allocation;


/**
Detect whether a weak reference to type $(D T) can be created.

A weak reference can be created for a $(D class), $(D interface), or $(D delegate).

Warning:
$(D delegate) context must be a class instance.
I.e. creating a weak reference for a $(D delegate) created from a $(D struct)
member function will result in undefined behavior.

$(RED Weak reference will not work for closures) unless enhancement $(DBUGZILLA 9601)
is implemented as now regular D objects aren't created on closures.
*/
enum isWeakReferenceable(T) = is(T == class) || is(T == interface) || is(T == delegate);

/**
Implements weak reference.

Note: The class contains a pointer to a target object thus it behaves as
a normal reference if placed in GC block without $(D NO_SCAN) attribute.

Tip: This behaves like C#'s short weak reference or Java's weak reference.
*/
final @trusted class WeakReference(T)
if(isWeakReferenceable!T)
{
	/* Create weak reference for $(D target).

	Preconditions:
	$(D target !is null)
	*/
	this(T target)
	in { assert(target); }
	body
	{
		_data.target = target;
		rt_attachDisposeEvent(_targetToObj(target), &onTargetDisposed);
	}

	/// Determines whether referenced object is finalized.
	@property bool alive() const pure nothrow @nogc
	{ return !!atomicLoad(_data.ptr); }

	/**
	Returns referenced object if it isn't finalized
	thus creating a strong reference to it.
	Returns null otherwise.
	*/
	@property inout(T) target() inout nothrow
	{
		return _data.getTarget();
	}

	~this()
	{
		if(T t = target)
		{
			rt_detachDisposeEvent(_targetToObj(t), &onTargetDisposed);
		}
	}

private:
	shared ubyte[T.sizeof] _dataStore;

	@property ref inout(_WeakData!T) _data() inout pure nothrow @nogc
	{
		return _dataStore.viewAs!(_WeakData!T);
	}

	void onTargetDisposed(Object) pure nothrow @nogc
	{
		atomicStore(_data.ptr, cast(shared void*) null);
	}
}

/// Convenience function that returns a $(D WeakReference!T) object for $(D target).
@safe WeakReference!T weakReference(T)(T target)
if(isWeakReferenceable!T)
{
	return new WeakReference!T(target);
}

///
unittest
{
	auto weak = weakReference(new Object());
	// ...
	if(auto obj = weak.target)
	{
		// Still alive! Let's kill it by hands.
		destroy(obj);
		assert(!weak.alive && !weak.target);
	}
}

///
unittest
{
	auto weak = weakReference(&(new Object()).toString);
	// ...
	if(auto del = weak.target)
	{
		// It's alive! Let's check and kill it by hands.
		assert(del() == "object.Object");
		destroy(cast(Object) del.ptr);
		assert(!weak.alive && !weak.target);
	}
}

@safe unittest
{
	void destroy(T)(T t) @trusted { .destroy(t); } // to make unittest `@safe`

	{
		auto o = new Object();
		auto w = weakReference(o);
		assert(w.alive && w.target is o);
		destroy(o);
		assert(!w.alive && !w.target);
	}

	interface I { }
	class C: I { void f() {} }
	{
		I i = new C();
		auto w = weakReference(i);
		assert(w.alive && w.target is i);
		destroy(i);
		assert(!w.alive && !w.target);
	}
	{
		auto c = new C();
		auto w = weakReference(&c.f);
		assert(w.alive && w.target is &c.f);
		destroy(c);
		assert(!w.alive && !w.target);
	}
}

/**
Implements weak reference array.

It gives better performance when working with
multiple weak references at once.
*/
final @trusted class WeakReferenceArray(T)
if(isWeakReferenceable!T)
{
	/**
	Create weak reference array with initial capacity $(D initialCapacity).

	Preconditions:
	$(D initialCapacity != 0)
	*/
	this(in size_t initialCapacity)
	in { assert(initialCapacity); }
	body
	{
		_data = cast(_WeakData!T*) heap.allocate!T(initialCapacity, false, false).ptr;
		_capacity = initialCapacity;
	}

	/// Total _count of (possibly dead) weak references.
	@property size_t count() const @safe pure nothrow @nogc
	{ return _count; }

	/// Total count of alive weak references.
	@property size_t aliveCount() const pure nothrow @nogc
	{ return atomicLoad(_aliveCount); }

	/// Returns the _capacity of the array.
	@property size_t capacity() const @safe pure nothrow @nogc
	{ return _capacity; }

	/**
	Determines whether array behaves as a _hard reference.
	$(D false) by default.
	*/
	@property bool hard() const @safe pure nothrow @nogc
	{ return _hard; }

	/**
	Return array internal buffer which can be safely used while
	the array behaves as a hard reference.

	The array contains $(D aliveCount) non-null references.
	Use $(D removeDead) before retrieveing the array to
	get array of only alive objects.
	
	Note:
	Retrieved buffer may become invalid after addition of an object
	into the array if $(D capacity == count) or after $(D reserve) or
	$(D removeDead) call.

	Preconditions:
	$(D hard)
	*/
	@property inout(T)[] buff() inout pure nothrow @nogc
	in { assert(hard); }
	body
	{ return (cast(inout T*) _data)[0 .. _count]; }

	/**
	Appends new weak reference to $(D target) to the array.
	*/
	void opOpAssign(string op : "~")(T target)
	{
		if(_count == _capacity)
		{
			if(_capacity * 2 < _capacity)
				onOutOfMemoryError();
			reserve(_capacity * 2);
		}
		_data[_count++].target = target;
		if(!target)
			return;
		atomicOp!`+=`(_aliveCount, 1);
		rt_attachDisposeEvent(_targetToObj(target), &onTargetDisposed);
	}

	/**
	Returns $(D i)-th referenced object if it isn't finalized
	thus creating a strong reference to it.
	Returns null otherwise.
	*/
	inout(T) opIndex(in size_t i) inout nothrow
	{
		version(D_NoBoundsChecks) { }
		else if(i >= _count)
			onRangeError();

		if(_hard)
			return _data[i].target;

		return _data[i].getTarget();
	}

	/// Changes $(D i)-th referenced object.
	void opIndexAssign(T target, in size_t i)
	{
		version(D_NoBoundsChecks) { }
		else if(i >= _count)
			onRangeError();

		const wasHard = hard;
		if(!wasHard) makeHard();
		scope(exit) if(!wasHard) makeWeak();

		if(_data[i].target is target)
			return;

		auto prevObject = _data[i].ptr ? _targetToObj(_data[i].target) : null;
		auto object = target ? _targetToObj(target) : null;
		_data[i].target = target;

		if(!prevObject || !object)
			(cast() _aliveCount) += object ? 1 : -1;

		if(prevObject is object)
			return; // no need to attach/detach dispose events

		if(prevObject)
		{
			bool foundPrev = false;
			foreach(j, t; buff) if(t && j != i)
			{
				foundPrev |= _targetToObj(t) is prevObject;
				if(foundPrev)
					break;
			}
			if(!foundPrev)
				rt_detachDisposeEvent(prevObject, &onTargetDisposed);
		}
		if(object)
			rt_attachDisposeEvent(object, &onTargetDisposed);
	}

	/// Reserve at least $(D newCapacity) elements for appending.
	void reserve(in size_t newCapacity)
	{
		if(newCapacity <= _capacity)
			return;

		const wasHard = hard;
		if(!wasHard) makeHard();
		scope(exit) if(!wasHard) makeWeak();

		_capacity = newCapacity;
		T[] arr = buff;
		heap.reallocate(arr, _capacity, false, false);
		_data = cast(_WeakData!T*) arr.ptr;
	}

	/// Remove dead weak references from the array. This may decrease $(D count).
	void removeDead() nothrow
	{
		const wasHard = hard;
		if(!wasHard) makeHard();

		for(size_t i = 0; i < count; )
		{
			// NOTE: This may be optimized but we assume small arrays for now.
			if(!_data[i].ptr)
				rawCopy(_data + i + 1, _data + i, --_count - i);
			else
				++i;
		}

		if(!wasHard) makeWeak();
	}

	/// Force the array to behave as a weak reference.
	void makeWeak() nothrow
	{
		if(!_hard)
			return;
		_hard = false;
		GC.removeRange(cast(void*) _data);
	}

	/// Force the array to behave as a hard reference.
	void makeHard() nothrow
	{
		if(_hard)
			return;
		_hard = true;
		GC.addRange(cast(void*) _data, T.sizeof * _count);
	}

	~this()
	{
		makeHard();

		foreach(t; buff) if(t)
			rt_detachDisposeEvent(_targetToObj(t), &onTargetDisposed);

		heap.free(cast(T*) _data, false);
	}

private:
	size_t _capacity, _count = 0;
	bool _hard = false;
	shared size_t _aliveCount = 0;
	_WeakData!T* _data;

	void onTargetDisposed(Object obj) pure nothrow @nogc
	{
		version(assert) size_t repeatCount = 0;
		foreach(ref d; _data[0 .. _count]) if(d.ptr && _targetToObj(d.target) is obj)
		{
			atomicOp!`-=`(_aliveCount, 1);
			atomicStore(d.ptr, cast(shared void*) null);
			static if(is(T == delegate))
				d.funcptr = null;
			version(assert) ++repeatCount;
		}
		version(assert) assert(repeatCount);
	}
}


/**
Convenience function that returns a $(D WeakReferenceArray!T)
with initial capacity $(D initialCapacity).
*/
@safe WeakReferenceArray!T weakReferenceArray(T)(in size_t initialCapacity = 64)
if(isWeakReferenceable!T)
{
	return new WeakReferenceArray!T(initialCapacity);
}

@safe unittest
{
	void destroy(T)(T t) @trusted { .destroy(t); } // to make unittest `@safe`

	{
		auto o = new Object();
		auto w = weakReferenceArray!Object(1);
		w ~= o;
		assert(w.aliveCount == 1 && w[0] is o);
		destroy(o);
		assert(!w.aliveCount && !w[0]);

		auto o1 = new Object(), o2 = new Object(), o3 = new Object();
		w ~= o1;
		w ~= o2;
		w ~= o3;
		assert(!w.hard && w.aliveCount == 3 && w[1] is o1 && w[2] is o2 && w[3] is o3);
		w.makeHard();
		assert(w.hard && w.aliveCount == 3 && w.buff == [null, o1, o2, o3]);
		destroy(o2);
		assert(w.aliveCount == 2 && w.buff == [null, o1, null, o3]);
		w.removeDead();
		assert(w.aliveCount == 2 && w.buff == [o1, o3]);
		w.makeWeak();
		assert(!w.hard);
		destroy(o1);
		destroy(o3);
		assert(!w.aliveCount);
		assert(w.count == 2);
		w.removeDead();
		assert(!w.count);
	}

	{
		auto o = new Object(), o1 = new Object(), o2 = new Object();
		auto w = weakReferenceArray!Object(1);
		w ~= o;
		w ~= o1;
		w[0] = o2;
		assert(w.aliveCount == 2 && w[0] is o2 && w[1] is o1);
		destroy(o);
		assert(w.aliveCount == 2 && w[0] is o2 && w[1] is o1);
		destroy(o2);
		assert(w.aliveCount == 1 && !w[0] && w[1] is o1);
		w[0] = o1;
		assert(w.aliveCount == 2 && w[0] is o1 && w[1] is o1);
		destroy(o1);
		assert(w.aliveCount == 0 && !w[0] && !w[1]);
	}

	interface I { }
	class C: I { void f() {} void f1() {} }
	{
		I i = new C(), i1 = new C();
		auto w = weakReferenceArray!I(1);
		w ~= i;
		w ~= i;
		w ~= i;
		w ~= i1;
		assert(w.aliveCount == 4 && w[0] is i && w[1] is i && w[2] is i && w[3] is i1);
		destroy(i);
		assert(w.aliveCount == 1 && !w[0] && !w[1] && !w[2] && w[3] is i1);
		destroy(i1);
		assert(!w.aliveCount && !w[0] && !w[1] && !w[2] && !w[3]);
	}
	{
		auto c = new C(), c1 = new C();
		auto w = weakReferenceArray!(void delegate())(1);
		w ~= &c.f;
		w ~= &c1.f;
		w ~= &c.f1;
		assert(w.aliveCount == 3 && w[0] is &c.f && w[1] is &c1.f && w[2] is &c.f1);
		destroy(c1);
		assert(w.aliveCount == 2 && w[0] is &c.f && !w[1] && w[2] is &c.f1);
		destroy(c);
		assert(!w.aliveCount && !w[0] && !w[1] && !w[2]);
	}
}


private:

alias DisposeEvt = void delegate(Object);

extern(C)
{
	Object _d_toObject(void* p) pure nothrow @nogc;
	void rt_attachDisposeEvent(Object obj, DisposeEvt evt);
	void rt_detachDisposeEvent(Object obj, DisposeEvt evt);
}

union _WeakData(T)
if(isWeakReferenceable!T)
{
	T target;
	struct
	{
		shared void* ptr; // delegate also has ptr at offset 0
		static if(is(T == delegate))
			void* funcptr;
	}

	// Returns referenced object if it isn't finalized.
	@property inout(T) getTarget() inout nothrow
	{
		auto ptr = cast(inout shared void*) atomicLoad(/*de-inout*/(cast(const) this).ptr);
		if(!ptr)
			return null;

		// Note: this is an implementation dependent GC fence as there
		// is no guarantee `addrOf` will really lock GC mutex.
		GC.addrOf(cast(void*) -1);

		// We have strong reference to ptr here so just test
		// whether we are still alive:
		if(!atomicLoad(/*de-inout*/(cast(const) this).ptr))
			return null;

		// We have to use obtained reference to ptr in result:
		static if(is(T == delegate))
			inout _WeakData res = { ptr: ptr, funcptr: funcptr };
		else
			inout _WeakData res = { ptr: ptr };
		return res.target;
	}
}

Object _targetToObj(T)(T t) pure nothrow @nogc
if(is(T == delegate))
{ return _d_toObject(t.ptr); }

inout(Object) _targetToObj(T)(inout T t) @trusted pure nothrow @nogc
if(is(T == class) || is(T == interface))
{ return t.upcast!Object; }
