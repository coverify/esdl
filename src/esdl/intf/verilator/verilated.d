module esdl.intf.verilator.verilated;

import esdl.base.core: _esdl__component, NamedComp, _esdl__ignore,
  HierComp, RootEntity, EsdlSimulator, Time, Process, SimPhase,
  getRootEntity, EntityIntf, ElabContext, BaseExport, Entity,
  BasePort;
import std.traits: isIntegral, isBoolean;
import esdl.data.bvec: isBitVector, ubvec;

public class VlExportObj(IF)
     if (is (IF == VlSignal!T, T)) : BaseExport
{
  static if (is (IF == VlSignal!VV, VV)) {
    alias VAL_TYPE = VV;

    final VV read() {
      return _channel.read();
    }

  }

  public IF _channel = void;

  // disable auto instantiation of the channel during the elaboration
  @disable package ref IF _esdl__objRef() {
    return _channel;
  }

  public IF _esdl__obj() {
    return _channel;
  }

  alias _esdl__obj this;

  public void _esdl__exportIsBound() {
    if (_channel.isNull()) {
      import std.stdio: writeln;
      writeln("Error: VlExport '" ~ this.getFullName ~
	      "' is not bound to any channel");
      this.getRoot._esdl__unboundExports();
    }
  }

  // If the corresponding channel provides methods(by any name) that
  // does not take any arguments and returns an Event or an EventObj
  //(or its derived class object), create ProxyEvents by the same
  // name on the export. These events would then be bound to the events
  // returned by the corresponding channel at the time of the channel
  // itself getting bound to the export
  // mixin(declareProxyEvents!IF ());

  // This should get simplified one DMD bug 9618 is taken care of
  // http://d.puremagic.com/issues/show_bug.cgi?id=9618
  final void bind(ref IF channel) {
    // if (simPhase == SimPhase.BINDEXPORTS) {
    import std.exception;
    enforce(_channel.isNull, "Re-binding a export if not allowed: " ~
	    this.getFullName);
    this._channel = channel;
    // Bind all Proxy Events
    //    mixin(bindProxyEvents!(IF, "_channel")());
    // static if (hasRegisterMethod!(IF, "registerVlExport")) {
    static if (__traits(compiles, _channel.registerExport(this))) {
      _channel.registerExport(this);
    }
  }

  final void opCall(IF channel) {
    this.bind(channel);
  }

  // Hierarchy
  mixin NamedMixin;

  static void _esdl__inst(size_t I=0, U, L)(U u, ref L l)
  {
    synchronized(u) {
      if (l is null) l = new L();
    }
  }

  static void _esdl__elab(size_t I, T, L)(T t, ref L l, uint[] indices=null)
  {
    l._esdl__inst!I(t, l);
    static assert(is(T unused: ElabContext),
		  "Only ElabContext components are allowed to have ports");
    synchronized(l.get) {
      l._esdl__nomenclate!I(t, indices);
      t._esdl__addExport(l.get);
      l._esdl__setParent(t);
    }
  }

}

@_esdl__component struct VlExport(IF)
     if (is (IF == VlSignal!T, T))
  {
    static if (is (IF == VlSignal!VV, VV)) {
      import std.traits: isAssignable;
      alias VAL_TYPE = VV;
      
      final void opCall(VV* val) {
	VlSignal!VV sig = val;
	_esdl__obj.bind(sig);
      }
      final void opAssign(V)(V val) if (isAssignable!(IF, V)) {
	_exportObj._channel = val;
      }

      final VV read() {
	return _exportObj._channel.read();
      }

      final bool opCast(C)() if (isBoolean!C) {
	return this.read != 0;
      }
    }
    // enum bool _thisIsVlExport = true;
    public VlExportObj!(IF) _exportObj = void;

    package ref VlExportObj!(IF) _esdl__objRef() {
      return _exportObj;
    }

    public VlExportObj!(IF) _esdl__obj() {
      return _exportObj;
    }

    alias _esdl__obj this;
    alias _esdl__obj get;

    final void opCall(IF channel) {
      _esdl__obj.bind(channel);
    }


    // Disallow VlExport assignment
    @disable private void opAssign(typeof(this) e);

    // public final void initialize() {
    //   if (_exportObj is null) {
    //     _exportObj = new VlExportObj!(IF);
    //     // writeln("Building VlExport");
    //   }
    // }

    static void _esdl__inst(size_t I=0, T, L)(T t, ref L l) {
      l._esdl__objRef._esdl__inst!I(t, l._esdl__objRef);
    }
}

template VlExport(int N)
{
  alias VlExport = VlExport!(VlSignal!N);
}

template VlPort(int N)
{
  alias VlPort = VlPort!(VlSignal!N);
}

@_esdl__component struct VlPort(IF)
     if (is (IF == VlSignal!T, T))  
{
  static if (is (IF == VlSignal!VV, VV)) {
    import std.traits: isAssignable;
    alias VAL_TYPE = VV;

    // final void opAssign(VV val) {
    //   _portObj._channel = val;
    // }
    final void opAssign(V)(V val) if (isAssignable!(IF, V)) {
      _portObj._channel = val;
    }

    final VV read() {
      return _portObj._channel.read();
    }

    final bool opCast(C)() if (isBoolean!C) {
      return this.read != 0;
    }
  }

  
  // enum bool _thisIsPort = true;
  public VlPortObj!(IF) _portObj = void;

  package ref VlPortObj!(IF) _esdl__objRef() {
    return _portObj;
  }

  public VlPortObj!(IF) _esdl__obj() {
    if (this._portObj is null) {
      // synchronized(typeid(VlPort!(IF))) {
      if (this._portObj is null) {
	this._portObj = new VlPortObj!(IF)();
      }
      // }
    }
    return this._portObj;
  }

  alias _esdl__obj this;
  alias _esdl__obj get;

  T opCast(T:bool)() {
    return this.read() != 0;
  }  

  // Disallow VlPort assignment
  // @disable private void opAssign(typeof(this) e);

  // Special case of Signals
  public final void initialize() {
    if(_portObj is null) {
      _portObj = new VlPortObj!(IF);
      // writeln("Building VlPort");
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

public class VlPortObj(IF)
     if (is (IF == VlSignal!T, T)) : BasePort
{
  static if (is (IF == VlSignal!VV, VV)) {
    alias VAL_TYPE = VV;

    final VV read() {
      return _channel.read();
    }

  }

  public IF _channel = void;

  // disable auto instatiation during the elaboration process
  @disable package ref IF _esdl__objRef() {
    return _channel;
  }

  package ref IF _esdl__obj() {
    return _channel;
  }

  public IF channel() {
    // synchronized(this) {
    return _channel;
    // }
  }

  alias channel this;
  alias channel _esdl__obj;

  public void _esdl__portIsBound() {
    synchronized(this) {
      if (_channel.isNull()) {
	import std.stdio: writeln;
	writeln("Error: VlPort '" ~ this.getFullName ~
		"' is not bound to any channel");
	this.getRoot._esdl__unboundPorts();
      }
    }
  }

  final bool opCast(C)() if (isBoolean!C) {
    return this.read != 0;
  }

  public int opCmp(string file = __FILE__,
		   size_t line = __LINE__, V)(const V other) const
       if (isIntegral!V || isBitVector!V || isBoolean!V) {
	 return this._channel.opCmp(other);
       }

  public bool opEquals(string file = __FILE__,
		       size_t line = __LINE__, V)(const V other)
       if (isIntegral!V || isBitVector!V || isBoolean!V) {
	 return this._channel.opEquals(other);
       }

  V opAssign(V)(V val)
       if (isIntegral!V || isBitVector!V || isBoolean!V) {
	 _channel = val;
	 return val;
       }

  // If the corresponding channel provides methods(by any name) that
  // does not take any arguments and returns an Event or an EventObj
  //(or its derived class object), create ProxyEvents by the same
  // name on the port. These events would then be bound to the events
  // returned by the corresponding channel at the time of the channel
  // itself getting bound to the port
  // mixin(declareProxyEvents!IF());

  // This should get simplified once DMD bug 9618 is taken care of
  // http://d.puremagic.com/issues/show_bug.cgi?id=9618
  // bind method
  final void bind(IF channel) {
    // if (simPhase == SimPhase.BINDPORTS) {
    import std.exception;
    enforce(this._channel.isNull(), "Re-binding a port if not allowed: " ~
	    this.getFullName);
    synchronized(this) {
      this._channel = channel;
    }
    // Bind all Proxy Events
    //    mixin(bindProxyEvents!(IF, "_channel")());
    // static if(hasRegisterMethod!(IF, "registerPort")) {
    static if (__traits(compiles, _channel.registerPort(this))) {
      _channel.registerPort(this);
    }
  }


  final void opCall(IF channel) {
    this.bind(channel);
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
    synchronized(l) {
      l._esdl__nomenclate!I(t, indices);
      t._esdl__addPort(l);
      l._esdl__setParent(t);
    }
  }

}



abstract class VlInterface: Entity { }

template VlSignal(int N)
{
  alias VlSignal = VlSignal!(ubvec!N);
}

struct VlSignal(T)
{
  import std.traits: isAssignable, isPointer;
  
  T* _sig;

  alias get this;
  
  ref T get() { return *_sig; }

  void write(T val) { *_sig = val; }

  T read() { return *_sig; }

  void read(ref T val) { val = *_sig; }

  void opAssign(V)(V val) if (isAssignable!(T, V) && (! isPointer!V)) {
    *_sig = val;
  }

  void opAssign(ref VlSignal!T t) {
    _sig = t._sig;
  }

  void opAssign(T* sig) { _sig = sig; }

  this(T* sig) {
    _sig = sig;
  }

  void bind(T* sig) { _sig = sig; }

  final bool isNull() { return _sig is null; }

  public int opCmp(string file = __FILE__,
		   size_t line = __LINE__, V)(const V other) const
       if(isIntegral!V || isBitVector!V || isBoolean!V) {
	 if (*_sig > other) return 1;
	 else if (*_sig == other) return 0;
	 else return -1;
       }

  public bool opEquals(string file = __FILE__,
		       size_t line = __LINE__, V)(const V other)
       if(isIntegral!V || isBitVector!V || isBoolean!V) {
	 return *_sig == other;
       }
}

