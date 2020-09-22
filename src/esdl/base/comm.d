// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.base.comm;

private import esdl.base.core;
import std.traits;
import std.stdio;
import core.memory: GC;

import esdl.data.bvec: isBitVector;

// Given a type (class or interface), this template function finds out
// whether the type has a member function by name event that
// returns an Event when called with no arguments
package template hasEventMethod(T, string NAME) {
  static if(__traits(hasMember, T, NAME)) {
    static if(isEventMethod!(MemberFunctionsTuple!(T, NAME))) {
      enum bool hasEventMethod = true;
    } else {
      enum bool hasEventMethod = false;
    }
  } else {
    enum bool hasEventMethod = false;
  }
}

// Auxilliary function used by hasEventMethod
private template isEventMethod(ML...) {
  static if(ML.length == 0) {
    enum bool isEventMethod = false;
  } else {
    static if((is(ReturnType!(ML[0]) == Event) ||
	       is(ReturnType!(ML[0]) : EventObj))) {
      enum bool isEventMethod = true;
    } else {
      enum bool isEventMethod = isEventMethod!(ML[1..$]);
    }
  }
}

package template hasRegisterMethod(T, string NAME, P=void) {
  static if(__traits(hasMember, T, NAME)) {
    static if(hasRegisterMethod!(MemberFunctionsTuple!(T, NAME))) {
      enum bool hasRegisterMethod = true;
    } else {
      enum bool hasRegisterMethod = false;
    }
  }
}

// Auxilliary function used by hasRegisterMethod
private template hasRegisterMethod(ML...) {
  static if(ML.length == 0) {
    enum bool hasRegisterMethod = false;
  } else {
    static if(isCallable!(ML[0]) && ParameterTypeTuple!(ML[0]).length == 0) {
      enum bool hasRegisterMethod = true;
    } else {
      enum bool hasRegisterMethod = hasRegisterMethod!(ML[1..$]);
    }
  }
}

// public string declareProxyEvents(IF)() {
//   // declare a channel -- would be useful to run __traits(compiles)
//   IF channel;
//   string result = "";

//   foreach(f; __traits(allMembers, IF)) {
//     if(__traits(compiles, mixin("channel." ~ f ~ "()"))) {
//       if(hasEventMethod!(IF, f)) {
//	result ~= "public Event " ~ f ~ ";";
//       }
//     }
//   }
//   return result;
// }

// public string bindProxyEvents(IF, string channel)() {
//   // declare a channel -- would be useful to run __traits(compiles)
//   // IF channel;
//   string result = "";

//   foreach(string f; __traits(allMembers, IF)) {
//     if(__traits(compiles, mixin("channel." ~ f ~ "()"))) {
//       if(hasEventMethod!(IF, f)) {
//	result ~= "this." ~ f ~ " = " ~ channel ~ "." ~ f ~ "().proxy();";
//       }
//     }
//   }

//   return result;
// }

string declareWait(IF, string E, string CHANNEL)() {
  IF channel;
  string result = "// Interface does not define event()";
  static if((__traits(hasMember, IF, E)) &&
	    (__traits(compiles, mixin("channel." ~ E ~ "()")))) {
    foreach(M;(MemberFunctionsTuple!(IF, E)))
      if(is(ReturnType!M == Event) ||
	 is(ReturnType!M : EventObj)) {
	result = "
	  void wait() {
	    // wait for default Event
	    " ~ CHANNEL ~ ".event().wait();
	  }";
      }
  }
  return result;
}

@_esdl__component struct Port(IF, size_t N=1, size_t M=N)
{
  // enum bool _thisIsPort = true;
  public PortObj!(IF,N,M) _portObj = void;

  package ref PortObj!(IF,N,M) _esdl__objRef() {
    return _portObj;
  }

  public PortObj!(IF,N,M) _esdl__obj() {
    if(this._portObj is null) {
      synchronized(typeid(Port!(IF,N,M))) {
	if(this._portObj is null) {
	  this._portObj = new PortObj!(IF,N,M)();
	}
      }
    }
    return this._portObj;
  }

  alias _esdl__obj this;
  alias _esdl__obj get;

  // void opCall(IF channel) {
  //   _esdl__obj.bind(channel);
  // }

  // void opAssign(IF channel) {
  //   _esdl__obj.bind(channel);
  // }

  // Disallow Port assignment
  @disable private void opAssign(Port e);

  // Special case of Signals
  static if(is(IF unused == SignalOutIF!T, T)) {
    import std.traits: isAssignable, isIntegral;
    import esdl.data.bvec: isBitVector;
    
    public final void opAssign(T val) {
      this._portObj.channel.write(val);
    }

    public final void opAssign(V) (V val)
      if(isAssignable!(T, V) &&
	 !is(T == V) &&
	 !(isBitVector!T && (isIntegral!V || is(V == bool)))) {
	this._portObj.channel.write(cast(T) val);
      }

    static if(isBitVector!T) {
      static if(T.SIZE >= 1) {
	public void opAssign(bool val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 8 && T.ISSIGNED) {
	public void opAssign(byte val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 8 && !T.ISSIGNED) {
	public void opAssign(ubyte val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 16 && T.ISSIGNED) {
	public void opAssign(short val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 16 && !T.ISSIGNED) {
	public void opAssign(ushort val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 32 && T.ISSIGNED) {
	public void opAssign(int val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 32 && !T.ISSIGNED) {
	public void opAssign(uint val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 64 && T.ISSIGNED) {
	public void opAssign(long val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
      static if(T.SIZE >= 64 && !T.ISSIGNED) {
	public void opAssign(ulong val) {
	  this._portObj.channel.write(cast(T) val);
	}
      }
    }

    S to(S)() if(is(S == string)) {
      return this._portObj.channel.read.to!S();
    }

    public string toString() {
      import std.conv;
      return to!string(this._portObj.channel.read);
    }

  }

  public final void initialize() {
    if(_portObj is null) {
      _portObj = new PortObj!(IF,N,M);
      // writeln("Building Port");
    }
  }

  static void _esdl__inst(size_t I=0, T, L)(T t, ref L l) {
    l._esdl__objRef._esdl__inst!I(t, l._esdl__objRef);
  }

  static void _esdl__elab(size_t I, T, L)(T t, ref L l, uint[] indices=null)
  {
    l._esdl__inst!I(t, l);
    static assert(is(T unused: ElabContext),
		  "Only ElabContext components are allowed to have ports");
    synchronized(l.get) {
      l._esdl__nomenclate!I(t, indices);
      t._esdl__addPort(l.get);
      l._esdl__setParent(t);
    }
  }
}

public class ExePortObj(IF, size_t N=1, size_t M=N)
  if(N == 1) : BaseExePort
{
  static assert(N == 0 || N >= M);
  public IF _channel = void;

  // disable auto instantiation of the channel during the elaboration
  @disable package ref IF _esdl__objRef() {
    return _channel;
  }

  public IF _esdl__obj() {
    return _channel;
  }

  alias _esdl__obj this;

  public void _esdl__exeportIsBound() {
    if(M != 0 && _channel is null) {
      writeln("Error: ExePort '" ~ this.getFullName ~
	      "' is not bound to any channel");
      this.getRoot._esdl__unboundExePorts();
    }
  }

  // Events associated with this exeport
  static if(hasEventMethod!(IF, "defaultEvent")) {
    // static sensitivity lists will get bound to this Event by default
    // and this event will in turn get bound to the channels event when
    // the channel is bound to this exeport
    // public Event event;

    // define a wait method that gets called if a user waits for this exeport
    final void wait() {
      import esdl.base.core;
      wait(_channel.defaultEvent());
    }
  }

  // If the corresponding channel provides methods(by any name) that
  // does not take any arguments and returns an Event or an EventObj
  //(or its derived class object), create ProxyEvents by the same
  // name on the exeport. These events would then be bound to the events
  // returned by the corresponding channel at the time of the channel
  // itself getting bound to the exeport
  // mixin(declareProxyEvents!IF());

  // This should get simplified one DMD bug 9618 is taken care of
  // http://d.puremagic.com/issues/show_bug.cgi?id=9618
  static if(is(IF unused: SignalInIF!S, S) ||
	    is(IF unused: SignalOutIF!S, S) ||
	    is(IF unused: SignalWriteIF!S, S) ||
	    is(IF unused: SignalInOutIF!S, S))
    {
      // bind method for signals
      final void bind(U)(U channel)
	if(is(U unused == Signal!(S, M), S, bool M)) {
	  if(simPhase == SimPhase.BINDEXEPORTS) {
	    import std.exception;
	    enforce(_channel is null, "Re-binding a exeport if not allowed: " ~
		    this.getFullName);
	    this._channel = channel._esdl__objRef;
	    // Bind all Proxy Events
	    //    mixin(bindProxyEvents!(IF, "_channel")());
	    // static if(hasRegisterMethod!(IF, "registerExePort")) {
	    static if(__traits(compiles, _channel.registerExePort(this))) {
	      _channel.registerExePort(this);
	    }
	    // static if(hasRegisterMethod!(IF, "registerExePort", ExePort!(IF, N))) {
	    //   channel.registerExePort();
	    // }
	  }
	}

      final void opCall(U)(U channel)
	if(is(U unused == Signal!(S, M), S, bool M)) {
	  this.bind(channel);
	}
    }
  else
  {
    final void bind(IF channel) {
      if(simPhase == SimPhase.BINDEXEPORTS) {
	import std.exception;
	enforce(_channel is null, "Re-binding a exeport if not allowed: " ~
		this.getFullName);
	this._channel = channel;
	// Bind all Proxy Events
	//    mixin(bindProxyEvents!(IF, "_channel")());
	// static if(hasRegisterMethod!(IF, "registerExePort")) {
	static if(__traits(compiles, _channel.registerExePort(this))) {
	  _channel.registerExePort(this);
	}
	// static if(hasRegisterMethod!(IF, "registerExePort", ExePort!(IF, N))) {
	//   channel.registerExePort();
	// }
      }
    }

    final void opCall(IF channel) {
      this.bind(channel);
    }
  }

  // Hierarchy
  mixin NamedMixin;

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l)
  {
    synchronized(u) {
      if(l is null) l = new L();
    }
  }

  static void _esdl__elab(size_t I, T, L)(T t, ref L l, uint[] indices=null)
  {
    l._esdl__inst!I(t, l);
    static assert(is(T unused: ElabContext),
		  "Only ElabContext components are allowed to have ports");
    synchronized(l.get) {
      l._esdl__nomenclate!I(t, indices);
      t._esdl__addExePort(l.get);
      l._esdl__setParent(t);
    }
  }

}

@_esdl__component struct ExePort(IF, size_t N=1, size_t M=N) if(N == 1)
  {
    // enum bool _thisIsExePort = true;
    public ExePortObj!(IF) _exeportObj = void;

    package ref ExePortObj!(IF) _esdl__objRef() {
      return _exeportObj;
    }

    public ExePortObj!(IF) _esdl__obj() {
      return _exeportObj;
    }

    alias _esdl__obj this;
    alias _esdl__obj get;

    final void opCall(IF channel) {
      _esdl__obj.bind(channel);
    }

    // Disallow ExePort assignment
    @disable private void opAssign(ExePort e);

    // public final void initialize() {
    //   if(_exeportObj is null) {
    //     _exeportObj = new ExePortObj!(IF);
    //     // writeln("Building ExePort");
    //   }
    // }

    static void _esdl__inst(size_t I=0, T, L)(T t, ref L l) {
      l._esdl__objRef._esdl__inst!I(t, l._esdl__objRef);
    }
}

alias ExePort ExPort;

public interface BasePort: NamedComp {
  public void _esdl__portIsBound();
}

public interface BaseExePort: NamedComp {
  public void _esdl__exeportIsBound();
}

// N is the number of channels that can connect
// M represents the minimum number of channels that must connect
public class PortObj(IF, size_t N=1, size_t M=N) if(N == 1) : BasePort
{
  static assert(N == 0 || N >= M);
  public IF _channel = void;

  // disable auto instatiation during the elaboration process
  @disable package ref IF _esdl__objRef() {
    return _channel;
  }

  public IF channel() {
    synchronized(this) {
      return _channel;
    }
  }

  alias channel this;
  alias channel _esdl__obj;

  public void _esdl__portIsBound() {
    synchronized(this) {
      if(M != 0 && _channel is null) {
	writeln("Error: port '" ~ this.getFullName ~
		"' is not bound to any channel");
	this.getRoot._esdl__unboundPorts();
      }
    }
  }

  // Events associated with this port
  static if(hasEventMethod!(IF, "defaultEvent")) {
    // static sensitivity lists will get bound to this Event by default
    // and this event will in turn get bound to the channels event when
    // the channel is bound to this port
    // public Event event;

    // define a wait method that gets called if a user waits for this port
    final void wait() {
      import esdl.base.core;
      wait(channel.defaultEvent());
    }
  }

  // If the corresponding channel provides methods(by any name) that
  // does not take any arguments and returns an Event or an EventObj
  //(or its derived class object), create ProxyEvents by the same
  // name on the port. These events would then be bound to the events
  // returned by the corresponding channel at the time of the channel
  // itself getting bound to the port
  // mixin(declareProxyEvents!IF());

  // This should get simplified one DMD bug 9618 is taken care of
  // http://d.puremagic.com/issues/show_bug.cgi?id=9618
  static if(is(IF unused: SignalInIF!S, S) ||
	    is(IF unused: SignalOutIF!S, S) ||
	    is(IF unused: SignalWriteIF!S, S) ||
	    is(IF unused: SignalInOutIF!S, S))
    {
      // bind method for signals
      void bind(U)(U channel)
	if(is(U unused == Signal!(S, M), S, bool M)) {
	  if(simPhase == SimPhase.BINDPORTS) {
	    import std.exception;
	    enforce(this._channel is null, "Re-binding a port if not allowed: " ~
		    this.getFullName);
	    synchronized(this) {
	      this._channel = channel._esdl__objRef;
	    }
	    // Bind all Proxy Events
	    //    mixin(bindProxyEvents!(IF, "_channel")());
	    // static if(hasRegisterMethod!(IF, "registerPort")) {
	    static if(__traits(compiles, _channel.registerPort(this))) {
	      _channel.registerPort(this);
	    }
	    // static if(hasRegisterMethod!(IF, "registerPort", Port!(IF, N))) {
	    //   _channel.registerPort();
	    // }
	  }
	}
      void opCall(U)(U channel)
	if(is(U unused == Signal!(S, M), S, bool M)) {
	  this.bind(channel);
	}
    }
  else
  {
    // bind method
    final void bind(IF channel) {
      if(simPhase == SimPhase.BINDPORTS) {
	import std.exception;
	enforce(this._channel is null, "Re-binding a port if not allowed: " ~
		this.getFullName);
	synchronized(this) {
	  this._channel = channel;
	}
	// Bind all Proxy Events
	//    mixin(bindProxyEvents!(IF, "_channel")());
	// static if(hasRegisterMethod!(IF, "registerPort")) {
	static if(__traits(compiles, _channel.registerPort(this))) {
	  _channel.registerPort(this);
	}
	// static if(hasRegisterMethod!(IF, "registerPort", Port!(IF, N))) {
	//   _channel.registerPort();
	// }
      }
    }


    final void opCall(IF channel) {
      this.bind(channel);
    }
  }

  // Hierarchy
  mixin NamedMixin;

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l)
  {
    synchronized(u) {
      if(l is null) l = new L();
    }
  }
}

// public class PortObj(IF, size_t N=1, size_t M=N) if(N != 1) : BasePort
// {
//   static assert(N == 0 || N >= M);
//   static if(N == 0) {
//     public IF[] _channel;
//   }
//   else {
//     public IF [N] _channel;
//   }

//   // points to the array index for the next bind
//   private size_t index = 0;

//   public size_t size() {
//     return index;
//   }

//   alias size length;

//   // disable auto instatiation during the elaboration process
//   @disable package ref IF _esdl__objRef() {
//     return _channel;
//   }

//   public IF _esdl__obj() {
//     return _channel;
//   }

//   alias _esdl__obj this;

//   public IF opIndex(size_t n) {
//     import std.exception;
//     enforce(n < index, "Can not access port index " ~ n.to!string);
//   }

//   public void _esdl__portIsBound() {
//     if(M != 0 && index < M) {
//       writeln("Error: port '" ~ this.getFullName ~
// 	       "' is not bound to sufficient number of channels");
//       this.getRoot._esdl__unboundPorts();
//     }
//   }

//   // // Events associated with this port
//   // static if(hasEventMethod!(IF, "defaultEvent")) {
//   //   // static sensitivity lists will get bound to this Event by default
//   //   // and this event will in turn get bound to the channels event when
//   //   // the channel is bound to this port
//   //   // public Event event;

//   //   // define a wait method that gets called if a user waits for this port
//   //   // void wait() {
//   //   //   // wait for default Event
//   //   //   wait(_channel.defaultEvent());
//   //   // }
//   // }

//   // If the corresponding channel provides methods(by any name) that
//   // does not take any arguments and returns an Event or an EventObj
//   //(or its derived class object), create ProxyEvents by the same
//   // name on the port. These events would then be bound to the events
//   // returned by the corresponding channel at the time of the channel
//   // itself getting bound to the port
//   // mixin(declareProxyEvents!IF());

//   // bind method
//   void bind(IF channel) {
//     if(simPhase == SimPhase.BINDPORTS) {
//       static if(N == 0) {
// 	this._channel ~= channel;
// 	index += 1;
//       }
//       else {
// 	import std.exception;
// 	enforce(index < N,
// 		"Can not bind any more channels; exceeded max allowed: " ~
// 		N.to!stting);
// 	this._channel[index] = channel;
// 	++index;
//       }
//       // Bind all Proxy Events
//       //    mixin(bindProxyEvents!(IF, "_channel")());
//       // static if(hasRegisterMethod!(IF, "registerPort")) {
//       static if(__traits(compiles, _channel.registerPort(this))) {
// 	_channel[index-1].registerPort(this);
//       }
//       // static if(hasRegisterMethod!(IF, "registerPort", Port!(IF, N))) {
//       //   channel.registerPort();
//       // }
//     }
//   }

//   void opCall(IF channel) {
//     this.bind(channel);
//   }

//   // Hierarchy
//   mixin NamedMixin;

// }



// public void wait(T)(T port)
//   if(is(T unused: esdl.base.comm.Port!(IF, N), IF == interface, int N))
//     {
//       static if(hasEventMethod!(IF, "event")) {
//	port.wait();
//       }
//       else {
//	static assert("Error: No 'event' method for cahnnel type");
//       }
//     }

interface MutexIF
{
  void lock();
  bool tryLock();
  bool unlock();
}

class MutexObj: MutexIF, NamedComp
{
  static import core.sync.mutex;

  Event _event;
  core.sync.mutex.Mutex _mutex;

  @_esdl__ignore Process _owner;

  // Fixme -- why is a parent required here
  this(NamedComp parent=null) {
    synchronized(this) {
      if(parent is null) {
	parent = Process.self;
      }
      if(parent !is null) this._esdl__parent = parent;
      _mutex = new core.sync.mutex.Mutex();
      _event.initialize("_event", this);
    }
  }

  final bool unlock() {
    Process _caller = Process.self;
    synchronized(this) {
      if(_owner is _caller) {
	_mutex.unlock();
	_event.notify();
	_owner = null;
	return true;
      }
      else
	return false;
    }
  }

  final bool tryLock() {
    Process _caller = Process.self;
    synchronized(this) {
      if(_owner is null) {
	_owner = _caller;
	_mutex.lock();
	return true;
      }
      else
	if(_owner is _caller) {
	  return true;
	}
      return false;
    }
  }

  final void lock() {
    Process _caller = Process.self;
    while(true) {
      synchronized(this) {
	if(_owner is null) {
	  _owner = _caller;
	  _mutex.lock();
	  return;
	}
	else
	  if(_owner is _caller) {
	    return;
	  }
      }
      // wait statement can not be put inside a synchronized block
      _event.wait();
    }
  }

  final Process whoIsCalling() {
    return Process.self;
    // SimThread thread =
    //   staticCast!SimThread(core.thread.Thread.getThis());
    // if(thread.isTaskThread()) {
    //   return staticCast!Process(thread);
    // }
    // assert(false, "Mutexes can be locked only from Tasks");
  }

  // Hierarchy
  mixin NamedMixin;

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l)
  {
    synchronized(u) {
      if(l is null) l = new L();
    }
  }
}

@_esdl__component struct Mutex
{
  // enum bool _thisIsMutex = true;
  public MutexObj _mutexObj = void;

  package final ref MutexObj _esdl__objRef() return {
    return _mutexObj;
  }

  public final MutexObj _esdl__obj() {
    if(this._mutexObj is null) {
      synchronized(typeid(Mutex)) {
	if(this._mutexObj is null) {
	  this._mutexObj = new MutexObj();
	}
      }
    }
    return this._mutexObj;
  }

  alias _esdl__obj this;

  // Disallow Mutex assignment
  @disable private void opAssign(Mutex e);
  @disable private this(this);

  // static public Mutex opCall() {
  //   Mutex mutex;
  //   mutex.initialize();
  //   return mutex;
  // }

  static public Mutex[] opIndex(size_t n) {
    Mutex[] mutexs = new Mutex[n];
    foreach(ref mutex;mutexs) {
      synchronized {
	mutex.initialize();
      }
    }
    return mutexs;
  }

  public final void initialize(NamedComp parent=null) {
    initialize(null, parent);
  }

  public final void initialize(string name, NamedComp parent=null) {
    synchronized {
      if(RootThread.self !is null && parent is null) {
	assert(false, "Must provide parent for MutexObj being " ~
	       "\"initialize\" during elaboration");
      }
      if(_mutexObj is null) {
	_mutexObj = new MutexObj(parent);
      }
      if(name !is null) {
	_mutexObj._esdl__nomenclate_inst(name);
      }
    }
  }

  final void lock() {
    initialize();
    _mutexObj.lock();
  }
  final bool tryLock() {
    initialize();
    return _mutexObj.tryLock();
  }
  final bool unlock() {
    initialize();
    return _mutexObj.unlock();
  }

  static void _esdl__inst(size_t I=0, T, L)(T t, ref L l) {
    l._esdl__objRef._esdl__inst!I(t, l._esdl__objRef);
  }

  static void _esdl__elab(size_t I, U, L)(U u, ref L l, uint[] indices=null) {
    l._esdl__inst!I(u, l);
    synchronized(l._esdl__objRef) {
      static if(is(U unused: ElabContext)) {
	u._esdl__addChildObj(l);
      }
      l._esdl__objRef._esdl__nomenclate!I(u, indices);
      l._esdl__objRef._esdl__setParent(u);
      _esdl__elabMems(l._esdl__objRef);
    }
  }
}

interface SemaphoreIF
{
  void wait();
  bool tryWait();
  void post();
  ptrdiff_t getValue();
}

class SemaphoreObj: SemaphoreIF, NamedComp
{
  Event _event;
  ptrdiff_t   _value;

  this(ptrdiff_t n=1, NamedComp parent=null) {
    synchronized(this) {
      this._esdl__setParent(parent);
      _event.initialize("_event", this);
      _value = n;
    }
  }

  final ptrdiff_t getValue() {
    synchronized(this) {
      return _value;
    }
  }

  final void post() {
    synchronized(this) {
      ++_value;
      if(_value > 0) {
	_event.notify();
      }
    }
  }

  final bool tryWait() {
    synchronized(this) {
      if(_value > 0) {
	--_value;
	return true;
      }
      else {
	return false;
      }
    }
  }

  final void wait() {
    while(true) {
      synchronized(this) {
	if(_value > 0) {
	  --_value;
	  return;
	}
      }
      // wait statement can not be put inside a synchronized bwait
      _event.wait();
    }
  }
  // Hierarchy
  mixin NamedMixin;

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l)
  {
    synchronized(u) {
      if(l is null) l = new L();
    }
  }
}

@_esdl__component struct Semaphore
{
  // enum bool _thisIsSemaphore = true;
  public SemaphoreObj _semaphoreObj = void;

  package ref SemaphoreObj _esdl__objRef() return {
    return _semaphoreObj;
  }

  public SemaphoreObj _esdl__obj() {
    if(this._semaphoreObj is null) {
      synchronized(typeid(Semaphore)) {
	if(this._semaphoreObj is null) {
	  this._semaphoreObj = new SemaphoreObj();
	}
      }
    }
    return this._semaphoreObj;
  }

  alias _esdl__obj this;

  // Disallow Semaphore assignment
  @disable private void opAssign(Semaphore e);
  @disable private this(this);

  public final void initialize() {
    if(_semaphoreObj is null) {
      synchronized(typeid(Semaphore)) {
	if(_semaphoreObj is null) {
	  _semaphoreObj = new SemaphoreObj;
	}
      }
    }
  }

  this(size_t n) {
    synchronized(typeid(Semaphore)) {
      if(_semaphoreObj is null) {
	_semaphoreObj = new SemaphoreObj(n);
      }
    }
  }
  
  void wait() {
    initialize();
    _semaphoreObj.wait();
  }

  bool tryWait() {
    initialize();
    return _semaphoreObj.tryWait();
  }

  void post() {
    initialize();
    _semaphoreObj.post();
  }

  ptrdiff_t getValue() {
    initialize();
    return _semaphoreObj.getValue();
  }

  static void _esdl__inst(size_t I=0, T, L)(T t, ref L l) {
    l._esdl__objRef._esdl__inst!I(t, l._esdl__objRef);
  }

  static void _esdl__elab(size_t I, U, L)(U u, ref L l, uint[] indices=null) {
    l._esdl__inst!I(u, l);
    synchronized(l._esdl__objRef) {
      static if(is(U unused: ElabContext)) {
	u._esdl__addChildObj(l);
      }
      l._esdl__objRef._esdl__nomenclate!I(u, indices);
      l._esdl__objRef._esdl__setParent(u);
      _esdl__elabMems(l._esdl__objRef);
    }
  }
}

// Fifo

// non-blocking interface
interface FifoInNBIF(T)
{
  alias Port!(FifoInNBIF!T) port_t;
  public bool nbRead(ref T);
  public Event writeEvent();
  public void registerPort(BasePort port);
}
// Blocking interface
interface FifoInBIF(T)
{
  alias PortObj!(FifoInBIF!T) port_t;
  public void read(ref T);
  public T read();
  public void registerPort(BasePort port);
}

interface FifoInIF(T): FifoInBIF!T, FifoInNBIF!T
{
  size_t numFilled();
}

// non-blocking interface
interface FifoOutNBIF(T)
{
  alias Port!(FifoOutNBIF!T) port_t;
  public bool nbWrite(T);
  public Event readEvent();
  public void registerPort(BasePort port);
}
// Blocking interface
interface FifoOutBIF(T)
{
  alias Port!(FifoOutBIF!T) port_t;
  public void write(T t);
  public void registerPort(BasePort port);
}

interface FifoOutIF(T): FifoOutBIF!T, FifoOutNBIF!T
{
  size_t numFree();
}

class FifoObj(T, size_t N=0): Channel, FifoInIF!T, FifoOutIF!T
{
  alias Port!(FifoInNBIF!T) port_inb_t;
  alias Port!(FifoInBIF!T) port_ib_t;
  alias Port!(FifoOutNBIF!T) port_onb_t;
  alias Port!(FifoOutBIF!T) port_ob_t;

 protected:
  static if(N == 0) {
    T [] _buffer;
  }
  else {
    T [N] _buffer;
  }
  size_t _free;
  size_t _readIndex;
  size_t _writeIndex;

  // For book-keeping whether ports have been attached to the Fifo
  bool _readerp = false;
  bool _writerp = false;

  size_t _numReadable = 0;
  size_t _numRead = 0;
  size_t _numWritten = 0;

  Event _readEvent;
  Event _writeEvent;

  static if(N == 0) {
    final void GrowBuffer() {
      synchronized(this) {
	size_t S = _buffer.length;
	_buffer.length *= 2;
	_free += S;
	import std.exception;
	import std.string;
	// enforce(_readIndex == _writeIndex+1 ||
	// 	(_readIndex == 0 && _writeIndex == _buffer.length-1),
	// 	format("_readIndex, %d, _writeIndex %d", _readIndex, _writeIndex));
	for(size_t i = 0; i != _writeIndex; ++i) {
	  _buffer[S+i] = _buffer[i];
	}
	_writeIndex += S;
      }
    }
  }

 public:
  this(string name="", NamedComp parent=null) {
    synchronized(this) {
      _readEvent.initialize("_readEvent", this);
      _writeEvent.initialize("_writeEvent", this);
      static if(N == 0) {_buffer.length = 4;}
      _free = _buffer.length;
      _esdl__setName(name);
      _esdl__setParent(parent);
    }
  }

  // void registerPort(IF)(PortObj!IF p)

  final void registerPort(BasePort p) {
    synchronized(this) {
      if(cast(PortObj!(FifoInNBIF!T)) p ||
	 cast(PortObj!(FifoInBIF!T)) p) {
	if(_readerp == true) {
	  assert(false, "Only one input port can be connected to Fifo");
	}
	else _readerp = true;
      }
      else if(cast(PortObj!(FifoOutNBIF!T)) p ||
	      cast(PortObj!(FifoOutBIF!T)) p) {
	if(_writerp == true) {
	  assert(false, "Only one input port can be connected to Fifo");
	}
	else _writerp = true;
      }
      else assert(false, "Incompatible port");
    }
  }

  final void registerPort(Port!(FifoInNBIF!T) p) {
    synchronized(this) {
      if(_readerp == true)
	assert(false, "Only one input port can be connected to Fifo");
      else
	_readerp = true;
    }
  }
  
  final void registerPort(port_ib_t p) {
    synchronized(this) {
      if(_readerp == true)
	assert(false, "Only one input port can be connected to Fifo");
      else
	_readerp = true;
    }
  }

  final void registerPort(port_onb_t p) {
    synchronized(this) {
      if(_writerp == true)
	assert(false, "Only one output port can be connected to Fifo");
      else
	_writerp = true;
    }
  }

  final void registerPort(port_ob_t p) {
    synchronized(this) {
      if(_writerp == true)
	assert(false, "Only one output port can be connected to Fifo");
      else
	_writerp = true;
    }
  }
  
  final size_t numFilled() {
    synchronized(this) {
      return _numReadable - _numRead;
    }
  }

  // static if(N != 0) {
  final size_t numFree() {
    synchronized(this) {
      return _buffer.length - _numReadable - _numWritten;
    }
  }
  // }

  final Event writeEvent() {
    return _writeEvent;
  }

  final Event readEvent() {
    return _readEvent;
  }

  // void _esdl__elaborate()
  // {
  //   alias typeof(this) T;
  //   alias typeof(_readEvent) L;

  //   _esdl__elab!0(this, _readEvent , "_readEvent", null);
  //   _esdl__elab!0(this, _writeEvent, "_writeEvent", null);
  // }

  final bool readBuffer(ref T val) {
    synchronized(this) {
      if(_free == _buffer.length) return false;
      val = _buffer[_readIndex];
      _free += 1;
      _readIndex =(1 + _readIndex) % _buffer.length;
      return true;
    }
  }

  final bool writeBuffer(T val) {
    synchronized(this) {
      if(_free == 0) return false;
      _buffer[_writeIndex] = val;
      _free -= 1;
      _writeIndex =(1 + _writeIndex) % _buffer.length;
      return true;
    }
  }

  final void read(ref T val) {
    bool _done = false;
    while(!_done) {
      if(numFilled() == 0) {
	_writeEvent.wait();
      }
      synchronized(this) {
	if(numFilled() != 0) {
	  _done = true;
	  _numRead++;
	  readBuffer(val);
	  requestUpdate();
	}
      }
    }
  }

  final T read() {
    T tmp;
    this.read(tmp);
    return tmp;
  }

  final bool nbRead(ref T val) {
    synchronized(this) {
      if(numFilled() == 0) return false;
      _numRead++;
      readBuffer(val);
      requestUpdate();
      return true;
    }
  }

  final void write(T val) {
    bool _done = false;
    while(!_done) {
      static if(N == 0) {
	synchronized(this) {
	  if(numFree() == 0) {
	    GrowBuffer();
	  }
	}
      }
      else {
	if(numFree() == 0) {
	  _readEvent.wait();
	}
      }
      synchronized(this) {
	if(numFree() != 0) {
	  _done = true;
	  _numWritten++;
	  writeBuffer(val);
	  requestUpdate();
	}
      }
    }
  }

  final bool nbWrite(T val) {
    synchronized(this) {
      static if(N == 0) {
	if(numFree() == 0) {
	  GrowBuffer();
	}
      }
      else {
	if(numFree() == 0) {
	  return false;
	}
      }
      _numWritten++;
      writeBuffer(val);
      requestUpdate();
      return true;
    }
  }

  // no need for synchronized here -- this functions is called only
  // during scheduler phase
  final override protected void update() {
    if(_numRead > 0) {
      // writeln("Notifying Read");
      _readEvent.notify(0);
    }
    if(_numWritten > 0) {
      // writeln("Notifying Write");
      _writeEvent.notify(0);
    }
    _numRead = 0;
    _numWritten = 0;
    _numReadable = _buffer.length - _free;
  }

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l)
  {
    synchronized(u) {
      if(l is null) l = new L();
    }
  }
}

@_esdl__component struct Fifo(T, size_t N = 0)
{
  // enum bool _thisIsFifo = true;
  public FifoObj!(T, N) _fifoObj = void;

  package ref FifoObj!(T, N) _esdl__objRef() {
    return _fifoObj;
  }

  public FifoObj!(T,N) _esdl__obj() {
    if(this._fifoObj is null) {
      synchronized(typeid(Fifo!(T,N))) {
	if(this._fifoObj is null) {
	  this._fifoObj = new FifoObj!(T,N)();
	}
      }
    }
    return this._fifoObj;
  }

  alias _esdl__obj this;

  // Disallow Fifo assignment
  @disable private void opAssign(Fifo e);
  @disable private this(this);

  public final void initialize() {
    if(this._fifoObj is null) {
      synchronized(typeid(Fifo!(T,N))) {
	if(_fifoObj is null) {
	  _fifoObj = new FifoObj!(T, N);
	}
      }
    }
  }

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l) {
    l._esdl__objRef._esdl__inst!I(u, l._esdl__objRef);
  }

  static void _esdl__elab(size_t I, U, L)(U u, ref L l, uint[] indices=null) {
    l._esdl__inst!I(u, l);
    synchronized(l._esdl__objRef) {
      static if(is(U unused: ElabContext)) {
	u._esdl__addChildObj(l);
      }
      l._esdl__objRef._esdl__nomenclate!I(u, indices);
      l._esdl__objRef._esdl__setParent(u);
      _esdl__elabMems(l._esdl__objRef);
    }
  }
}

interface SignalInIF(T)
{
  import esdl.data.bvec;

  public Event defaultEvent();
  public bool valueChanged();
  public Event event();
  public T read();

  alias read this;

  static if((isBitVector!T && T.SIZE == 1) || is(T == bool)) {
    public Event posedge();
    public Event negedge();
    public bool valueChangedPos();
    public bool valueChangedNeg();
  }
}

interface SignalWriteIF(T)
{
  void write(T data);
}

interface SignalInOutIF(T): SignalInIF!T, SignalWriteIF!T
{}

alias SignalInOutIF SignalOutIF;

class SignalObj(T, bool MULTI_DRIVER = false): Channel, SignalInOutIF!T
{
  import esdl.data.bvec;

  alias VAL_TYPE = T;

  protected Notification!T _changeEvent;
  protected T _curVal;
  protected T _newVal;

  alias read this;
  // FIXME -- http://d.puremagic.com/issues/show_bug.cgi?id=9249
  // S opCast(S)() if(is(S == string)) {
  //   synchronized(this)
  //     {
  //	return _curVal.to!S();
  //     }
  // }

  public this() {
    synchronized(this) {
      static if(is(T == bool) || (isBitVector!T && T.SIZE == 1)) {
	_posedgeEvent.initialize("_posedgeEvent", this);
	_negedgeEvent.initialize("_negedgeEvent", this);
      }
      _changeEvent.initialize("_changeEvent", this);
    }
  }

  public final override string toString() {
    synchronized(this) {
      import std.conv;
      return to!string(_curVal);
    }
  }

  static if(MULTI_DRIVER == false) {
    protected bool _writePortBound = false;
  }

  final Event defaultEvent() {
    Event e = _changeEvent;
    return e;
  }

  final Event event() {
    return defaultEvent();
  }

  final Notification!T defaultNotification() {
    return _changeEvent;
  }

  final Notification!T notification() {
    return defaultNotification();
  }

  public final T read() {
    synchronized(this) {
      return _curVal;
    }
  }

  public final bool valueChanged() {
    return _changeEvent.triggered();
  }

  public final void write(T val) {
    synchronized(this) {
      if(_curVal != val) {
	_newVal = val;
	requestUpdate();
      }
    }
  }

  public final void opAssign(T val) {
    this.write(val);
  }

  public final void opAssign(V) (V val)
    if(isAssignable!(T, V) &&
       !is(T == V) &&
       !(isBitVector!T && (isIntegral!V || is(V == bool)))) {
      this.write(cast(T) val);
    }

  static if(isBitVector!T) {
    static if(T.SIZE >= 1) {
      public final void opAssign(bool val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 8 && T.ISSIGNED) {
      public final void opAssign(byte val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 8 && !T.ISSIGNED) {
      public final void opAssign(ubyte val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 16 && T.ISSIGNED) {
      public final void opAssign(short val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 16 && !T.ISSIGNED) {
      public final void opAssign(ushort val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 32 && T.ISSIGNED) {
      public final void opAssign(int val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 32 && !T.ISSIGNED) {
      public final void opAssign(uint val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 64 && T.ISSIGNED) {
      public final void opAssign(long val) {
	this.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 64 && !T.ISSIGNED) {
      public final void opAssign(ulong val) {
	this.write(cast(T) val);
      }
    }
  }

  final void registerPort(BasePort p) {
    synchronized(this) {
      static if(MULTI_DRIVER == false) {
	if(cast(PortObj!(SignalWriteIF!T)) p) {
	  import std.exception;
	  enforce(! _writePortBound, "Signal " ~ this.getName ~
		  " can be bound to only a single write port");
	  _writePortBound = true;
	}
      }
    }
  }

  public void updateBindings() {}

  // no need for synchronized
  public final override void update() {
    // if(_newVal != _curVal) {
    _curVal = _newVal;
    _changeEvent.post(0, _curVal);
    updateBindings();
    static if(is(T == bool) || (isBitVector!T && T.SIZE == 1)) {
      // if(_posedgeEvent._eventObj !is null) {
      if(_newVal == 1) {
	_posedgeEvent.notify(0);
      }
      // }
      // if(_negedgeEvent._eventObj !is null) {
      if(_newVal == 0) {
	_negedgeEvent.notify(0);
      }
      // }
    }
    // }
  }

  static if(is(T == bool) || (isBitVector!T && T.SIZE == 1)) {
    protected Event _posedgeEvent;
    protected Event _negedgeEvent;

    final bool valueChangedPos() {
      return _posedgeEvent.triggered();
    }

    final bool valueChangedNeg() {
      return _negedgeEvent.triggered();
    }

    final Event posedge() {
      return _posedgeEvent;
    }

    final Event negedge() {
      return _negedgeEvent;
    }
  }

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l)
  {
    synchronized(u) {
      if(l is null) l = new L();
    }
  }

  public final void opOpAssign(string op, T)(T other) {
    synchronized(this) {
      static if(op == "+")  _newVal = _curVal +  other;
      static if(op == "-")  _newVal = _curVal -  other;
      static if(op == "*")  _newVal = _curVal *  other;
      static if(op == "/")  _newVal = _curVal /  other;
      static if(op == "^^") _newVal = _curVal ^^ other;
      static if(op == "%")  _newVal = _curVal %  other;
      static if(op == "~")  _newVal = _curVal ~  other;
      static if(op == "|")  _newVal = _curVal ^  other;
      static if(op == "&")  _newVal = _curVal %  other;
      static if(op == "^")  _newVal = _curVal ~  other;
      this.requestUpdate();
    }
  }

}

template Signal(uint WIDTH) {
  import esdl.data.bvec;
  alias Signal=Signal!(UBit!WIDTH);
}

@_esdl__component struct Signal(T, bool MULTI_DRIVER = false)
{
  // enum bool _thisIsSignal = true;
  alias VAL_TYPE = T;

  public SignalObj!(T, MULTI_DRIVER) _signalObj = void;

  public ref SignalObj!(T, MULTI_DRIVER) _esdl__objRef() {
    return _signalObj;
  }

  public SignalObj!(T, MULTI_DRIVER) _esdl__obj() {
    if(this._signalObj is null) {
      synchronized(typeid(Signal!(T, MULTI_DRIVER))) { //(this)
	if(_signalObj is null) {
	  _signalObj = new SignalObj!(T, MULTI_DRIVER);

	  // Construct these event objects here
	  // otherwise these get autoconstructed in the update phase
	  // where the parent object is not visible
	
	  _signalObj._changeEvent.initialize();

	  import esdl.data.bvec;

	  static if(is(T == bool) || (isBitVector!T && T.SIZE == 1)) {
	    _signalObj._posedgeEvent.initialize("_posedgeEvent");
	    _signalObj._negedgeEvent.initialize("_negedgeEvent");
	  }
	}
      }
    }
    return this._signalObj;
  }

  alias _esdl__obj this;

  private auto opAssign(S)(S e)
    if(is(S unused: SignalObj!(T, M), bool M))
      {
	auto ret = e.read();
	this.write(ret);
	return ret;
      }

  // Disallow Signal assignment
  // @disable private this(this);

  public void opAssign()(T val) {
    _esdl__obj.write(val);
  }

  public final void opAssign(V) (V val)
    if(isAssignable!(T, V) &&
       !is(T == V) &&
       !(isBitVector!T && (isIntegral!V || is(V == bool)))) {
      _esdl__obj.write(cast(T) val);
    }

  static if(isBitVector!T) {
    static if(T.SIZE >= 1) {
      public void opAssign(bool val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 8 && T.ISSIGNED) {
      public void opAssign(byte val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 8 && !T.ISSIGNED) {
      public void opAssign(ubyte val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 16 && T.ISSIGNED) {
      public void opAssign(short val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 16 && !T.ISSIGNED) {
      public void opAssign(ushort val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 32 && T.ISSIGNED) {
      public void opAssign(int val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 32 && !T.ISSIGNED) {
      public void opAssign(uint val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 64 && T.ISSIGNED) {
      public void opAssign(long val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 64 && !T.ISSIGNED) {
      public void opAssign(ulong val) {
	_esdl__obj.write(cast(T) val);
      }
    }
  }

  public void opOpAssign(string op, T)(T other) {
    _esdl__obj.opOpAssign!op(other);
  }

  public final void initialize() {
    synchronized(typeid(Signal!(T, MULTI_DRIVER))) {
      if(_signalObj is null) {
	_signalObj = new SignalObj!(T, MULTI_DRIVER);
      }
    }
  }

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l) {
    l._esdl__objRef._esdl__inst!I(u, l._esdl__objRef);
  }

  static void _esdl__elab(size_t I, U, L)(U u, ref L l, uint[] indices=null) {
    l._esdl__inst!I(u, l);
    synchronized(l._esdl__objRef) {
      static if(is(U unused: ElabContext)) {
	u._esdl__addChildObj(l._esdl__objRef);
      }
      l._esdl__objRef._esdl__nomenclate!I(u, indices);
      l._esdl__objRef._esdl__setParent(u);
      _esdl__elabMems(l._esdl__objRef);
    }
  }
}

class HdlSignalObj(T, bool MULTI_DRIVER = false): SignalObj!(T, MULTI_DRIVER)
{
  import esdl.intf.vpi;

  alias VAL_TYPE = T;

  alias read this;

  public final T read() {
    return super.read();
  }

  vpiHandle vpiNetHandle = null;

  override final void updateBindings() {
    if(vpiNetHandle) {	// only if the signal is bound to a Verilog net
      if(this._updateReason !is UpdateReason.VERILOG) {
	this.hdlPut();
      }
    }
  }
  
  public int opCmp(string file = __FILE__,
		   size_t line = __LINE__, V)(const V other) const
    if(isIntegral!V || isBitVector!V || isBoolean!V) {
      return this.read().opCmp(other);
    }

  public bool opEquals(string file = __FILE__,
		       size_t line = __LINE__, V)(const V other)
    if(isIntegral!V || isBitVector!V || isBoolean!V) {
      return this.read().opEquals(other);
    }

  final private void hdlPut() {
    assert(vpiIsUsable);
    synchronized(this) {
      s_vpi_value v;
      v.format = vpiVectorVal;
      static if(isBitVector!T) {
	enum size_t NWORDS = (T.SIZE+31)/32;
      }
      else {
	enum size_t NWORDS = (8*T.sizeof + 31)/32;
      }
      s_vpi_vecval[NWORDS+1] vector;

      static if(isBitVector!T) {
	_curVal.toVpiVecValue(vector);
      }
      else {
	enum size_t size = 8 * T.sizeof;
	// special handling for long/ulong for others simply copy
	static if(size > 32) {
	  vector[0].aval = cast(uint) _curVal;
	  vector[1].aval = cast(uint) (_curVal >>> 32);
	  vector[0].bval = 0;
	  vector[1].bval = 0;
	}
	else {
	  vector[0].aval = _curVal;
	  vector[0].bval = 0;
	}
      }

      v.value.vector = vector.ptr;
      vpi_put_value(vpiNetHandle, &v, null, vpiNoDelay);

    }
  }
  
  private static int _hdlConnect(p_cb_data cb) {
    auto t = cast(HdlSignalObj!(T, MULTI_DRIVER)) (*cb).user_data;
    t.hdlGet();
    return 0;
  }

  private final void hdlGet() {
    synchronized(this) {
      // for now, get the value and display it
      s_vpi_value v;
      v.format = vpiVectorVal;
      vpi_get_value(vpiNetHandle, &v);
      // at the time of binding we already checked that the size of
      // the signal at the two sides match.

      static if(isBitVector!T) {
	enum WS = (T.SIZE+31)/32;
	_newVal = v.value.vector[0..WS];
      }
      else {
	enum size_t size = 8 * T.sizeof;
	// special handling for long/ulong for others simply copy
	static if(size > 32) {
	  ulong lsw = v.value.vector[0].aval;
	  ulong msw = v.value.vector[1].aval;
	  lsw |= (msw << 32);
	  _newVal = cast(T) lsw;
	}
	else {
	  _newVal = cast(T) v.value.vector[0].aval;
	}
      }
      requestUpdate(UpdateReason.VERILOG);
      // writeln(*(v.value.vector));
    }
  }

  public final void hdlBind(string net) {
    synchronized(this) {
      if(vpiNetHandle !is null) {
	assert(false, "Signal is already bound: " ~ this.getFullName());
      }
	
      vpiNetHandle = vpiGetHandleByName(net, null);

      if(vpiNetHandle is null) {
	assert(false, "Can not find \"" ~ net ~ "\" in the verilog design");
      }
    
      auto handleType = vpi_get(vpiType, vpiNetHandle);
      if(handleType !is vpiNet && handleType !is vpiReg) {
	assert(false, "\"" ~ net ~ "\"" ~ " is not of reg or wire type");
      }

      auto size = vpi_get(vpiSize, vpiNetHandle);
      static if(isBitVector!T) {
	if(size !is T.SIZE) {
	  assert(false, "hdlBind: Signal size does not match with the size " ~
		 "of the net " ~ net);
	}
      }
      else static if(isBoolean!T) {
	if(size !is 1) {
	  assert(false, "hdlBind: Signal size does not match with the size " ~
		 "of the net" ~ net);
	}
      }
      else {
	if(size !is 8 * T.sizeof) {
	  assert(false, "hdlBind: Signal size does not match with the size " ~
		 "of the net" ~ net);
	}
      }

      // Reflect the HDL signal value here
      hdlGet();

      auto p_cb = new s_cb_data();	  
      p_cb.reason = vpiCbValueChange;
      p_cb.cb_rtn = &_hdlConnect;
      p_cb.obj = vpiNetHandle;
      // cb.time = null;
      // cb.value = null;

      Object obj = this;
      p_cb.user_data = cast(void*) obj;

      vpi_register_cb(p_cb);
    }
  }

  public final void opAssign(V) (V val)
    if(isAssignable!(T, V) &&
       !is(T == V) &&
       !(isBitVector!T && (isIntegral!V || is(V == bool)))) {
      this.write(cast(T) val);
    }

  
  public final void opOpAssign(string op, T)(T other) {
    synchronized(this) {
      static if(op == "+")  _newVal = _curVal +  other;
      static if(op == "-")  _newVal = _curVal -  other;
      static if(op == "*")  _newVal = _curVal *  other;
      static if(op == "/")  _newVal = _curVal /  other;
      static if(op == "^^") _newVal = _curVal ^^ other;
      static if(op == "%")  _newVal = _curVal %  other;
      static if(op == "~")  _newVal = _curVal ~  other;
      static if(op == "|")  _newVal = _curVal ^  other;
      static if(op == "&")  _newVal = _curVal %  other;
      static if(op == "^")  _newVal = _curVal ~  other;
      this.requestUpdate();
    }
  }

}

template HdlSignal(uint WIDTH) {
  import esdl.data.bvec;
  alias HdlSignal=HdlSignal!(ULogic!WIDTH);
}

@_esdl__component struct HdlSignal(T, bool MULTI_DRIVER = false)
{
  // enum bool _thisIsSignal = true;
  alias VAL_TYPE = T;
  public HdlSignalObj!(T, MULTI_DRIVER) _signalObj = void;

  public ref HdlSignalObj!(T, MULTI_DRIVER) _esdl__objRef() {
    return _signalObj;
  }

  public HdlSignalObj!(T, MULTI_DRIVER) _esdl__obj() {
    if(this._signalObj is null) {
      synchronized(typeid(HdlSignal!(T, MULTI_DRIVER))) { //(this)
	if(_signalObj is null) {
	  _signalObj = new HdlSignalObj!(T, MULTI_DRIVER);

	  // Construct these event objects here
	  // otherwise these get autoconstructed in the update phase
	  // where the parent object is not visible
	
	  _signalObj._changeEvent.initialize();

	  import esdl.data.bvec;

	  static if(is(T == bool) || (isBitVector!T && T.SIZE == 1)) {
	    _signalObj._posedgeEvent.initialize("_posedgeEvent");
	    _signalObj._negedgeEvent.initialize("_posedgeEvent");
	  }
	}
      }
    }
    return this._signalObj;
  }

  alias _esdl__obj this;

  private auto opAssign(S)(S e)
    if(is(S unused: HdlSignalObj!(T, M), bool M))
      {
	auto ret = e.read();
	this.write(ret);
	return ret;
      }

  // Disallow Signal assignment
  // @disable private this(this);

  public void opAssign()(T val) {
    _esdl__obj.write(val);
  }

  public final void opAssign(V) (V val)
    if(isAssignable!(T, V) &&
       !is(T == V) &&
       !(isBitVector!T && (isIntegral!V || is(V == bool)))) {
      _esdl__obj.write(cast(T) val);
    }

  static if(isBitVector!T) {
    static if(T.SIZE >= 1) {
      public void opAssign(bool val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 8 && T.ISSIGNED) {
      public void opAssign(byte val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 8 && !T.ISSIGNED) {
      public void opAssign(ubyte val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 16 && T.ISSIGNED) {
      public void opAssign(short val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 16 && !T.ISSIGNED) {
      public void opAssign(ushort val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 32 && T.ISSIGNED) {
      public void opAssign(int val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 32 && !T.ISSIGNED) {
      public void opAssign(uint val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 64 && T.ISSIGNED) {
      public void opAssign(long val) {
	_esdl__obj.write(cast(T) val);
      }
    }
    static if(T.SIZE >= 64 && !T.ISSIGNED) {
      public void opAssign(ulong val) {
	_esdl__obj.write(cast(T) val);
      }
    }
  }

  public void opOpAssign(string op, T)(T other) {
    _esdl__obj.opOpAssign!op(other);
  }

  public final void initialize() {
    synchronized(typeid(HdlSignal!(T, MULTI_DRIVER))) {
      if(_signalObj is null) {
	_signalObj = new HdlSignalObj!(T, MULTI_DRIVER);
      }
    }
  }

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l) {
    l._esdl__objRef._esdl__inst!I(u, l._esdl__objRef);
  }

  static void _esdl__elab(size_t I, U, L)(U u, ref L l, uint[] indices=null) {
    l._esdl__inst!I(u, l);
    synchronized(l._esdl__objRef) {
      static if(is(U unused: ElabContext)) {
	u._esdl__addChildObj(l._esdl__objRef);
      }
      l._esdl__objRef._esdl__nomenclate!I(u, indices);
      l._esdl__objRef._esdl__setParent(u);
      _esdl__elabMems(l._esdl__objRef);
    }
  }
}

template Input(T)
{
  alias Port!(SignalInIF!T,1,1) Input;
}

template Output(T)
{
  alias Port!(SignalOutIF!T,1,1) Output;
}

template InOut(T)
{
  alias Port!(SignalInOutIF!T,1,1) InOut;
}


template Wire(size_t W)
  if(W > 0) {
  import esdl.data.bvec;
  alias Signal!(Logic!W) Wire;
}

template WireIn(size_t W)
  if(W > 0) {
  import esdl.data.bvec;
  alias Input!(Logic!W) Wire;
}

template WireOut(size_t W)
  if(W > 0) {
  import esdl.data.bvec;
  alias Output!(Logic!W) Wire;
}
