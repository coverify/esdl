module esdl.intf.verilator.verilated;

import esdl.base.core: _esdl__component, NamedComp, _esdl__ignore,
  HierComp, RootEntity, EsdlSimulator, Time, Process, SimPhase,
  getRootEntity, EntityIntf, ElabContext, BaseExport, Entity,
  BasePort;
import std.traits: isIntegral, isBoolean;
import esdl.data.bvec: isBitVector;

extern (C++) {
  import core.stdcpp.string: basic_string;

  class VerilatedVcdFile {
  private:
    int m_fd = 0;  // File descriptor we're writing to
    @disable this();
  public:
    // METHODS
    /// Construct a (as yet) closed file
    // VerilatedVcdFile() = default;
    /// Close and destruct

    // virtual ~VerilatedVcdFile() = default;
    ~this();
    /// Open a file with given filename
    bool open(ref const(basic_string!char) name);
    /// Close object's file
    void close();
    /// Write data to file (if it is open)
    ulong write(const(char*) bufp, long len);
    // final ulong write(string bufp, long len) {
    //   import std.string: toStringz;
    //   return this.write(bufp.toStringz(), len);
    // }
  }

  // blind struct
  struct VerilatedContext {
    final void traceEverOn(bool flag);
  };
  class VerilatedVcdC;
  
  class ESDLVerilatedVcdD {
    private @disable this();

    VerilatedVcdC m_vcd_c;
    
    ~this();
    final bool isOpen() const;
    /// Open a new VCD file
    /// This includes a complete header dump each time it is called,
    /// just as if this object was deleted and reconstructed.
    void open(const(char) *filename);
    // final void open(string filename) {
    //   import std.string: toStringz;
    //   this.open(filename.toStringz());
    // }
    
    /// Continue a VCD dump by rotating to a new file name
    /// The header is only in the first file created, this allows
    /// "cat" to be used to combine the header plus any number of data files.
    final void openNext(bool incFilename = true);
    /// Set size in megabytes after which new file should be created
    final void rolloverMB(size_t rMB);
    /// Close dump
    final void close();
    /// Flush dump
    final void flush();
    /// Write one cycle of dump data
    /// Call with the current context's time just after eval'ed,
    /// e.g. ->dump(contextp->time())
    final void dump(ulong timeui);
    /// Write one cycle of dump data - backward compatible and to reduce
    /// conversion warnings.  It's better to use a vluint64_t time instead.
    final void dump(double timestamp);
    final void dump(uint timestamp);
    final void dump(int timestamp);

    // METHODS - Internal/backward compatible
    // \protectedsection

    // Set time units (s/ms, defaults to ns)
    // Users should not need to call this, as for Verilated models, these
    // propage from the Verilated default timeunit
    final void set_time_unit(const(char*) unit);
    // final void set_time_unit(string unit) {
    //   import std.string: toStringz;
    //   this.set_time_unit(unit.toStringz());
    // }
    final void set_time_unit(ref const(basic_string!char) unit);

    // Set time resolution (s/ms, defaults to ns)
    // Users should not need to call this, as for Verilated models, these
    // propage from the Verilated default timeprecision
    final void set_time_resolution(const(char*) unit);
    // final void set_time_resolution(string unit) {
    //   import std.string: toStringz;
    //   this.set_time_resolution(unit.toStringz());
    // }

    final void set_time_resolution(ref const(basic_string!char) unit);

    final VerilatedVcdC getVcdC();
  }

  VerilatedVcdFile createVcdFile();

  ESDLVerilatedVcdD createVcdD(VerilatedVcdFile filep = null);

}

public class VlExportObj(IF, size_t N=1, size_t M=N)
     if (N == 1 && is (IF == VlSignal!T, T)) : BaseExport
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

  public void _esdl__exportIsBound() {
    if (M != 0 && _channel.isNull()) {
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
  final void bind(IF channel) {
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
    // static if (hasRegisterMethod!(IF, "registerVlExport", VlExport!(IF, N))) {
    //   channel.registerVlExport();
    // }
    // }
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

@_esdl__component struct VlExport(IF, size_t N=1, size_t M=N)
     if (N == 1 && is (IF == VlSignal!T, T))
  {
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

    static if (is (IF == VlSignal!T, T) && isIntegral!T) {
      final void opCall(T* val) {
	_esdl__obj.bind(VlSignal!T(val));
      }
      final void opAssign(T val) {
	_exportObj._channel = val;
      }
      final T read() {
	return _exportObj._channel;
      }

      final bool opCast(C)() if (isBoolean!C) {
	return this.read != 0;
      }
    }
      

    // Disallow VlExport assignment
    @disable private void opAssign(VlExport e);

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

template VlExport(T) if (isIntegral!T)
{
  alias VlExport = VlExport!(VlSignal!T);
}

template VlPort(T) if (isIntegral!T)
{
  alias VlPort = VlPort!(VlSignal!T);
}

@_esdl__component struct VlPort(IF, size_t N=1, size_t M=N)
{
  // enum bool _thisIsPort = true;
  public VlPortObj!(IF,N,M) _portObj = void;

  package ref VlPortObj!(IF,N,M) _esdl__objRef() {
    return _portObj;
  }

  public VlPortObj!(IF,N,M) _esdl__obj() {
    if(this._portObj is null) {
      synchronized(typeid(VlPort!(IF,N,M))) {
	if(this._portObj is null) {
	  this._portObj = new VlPortObj!(IF,N,M)();
	}
      }
    }
    return this._portObj;
  }

  alias _esdl__obj this;
  alias _esdl__obj get;

  T opCast(T:bool)() {
    return this.read() != 0;
  }  

  // Disallow VlPort assignment
  @disable private void opAssign(VlPort e);

  // Special case of Signals
  public final void initialize() {
    if(_portObj is null) {
      _portObj = new VlPortObj!(IF,N,M);
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

// N is the number of channels that can connect
// M represents the minimum number of channels that must connect
public class VlPortObj(IF, size_t N=1, size_t M=N)
     if (N == 1 && is (IF == VlSignal!T, T)) : BasePort
{
  static assert(N == 0 || N >= M);
  public IF _channel = void;

  // disable auto instatiation during the elaboration process
  @disable package ref IF _esdl__objRef() {
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
      if (M != 0 && _channel.isNull()) {
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
    // static if(hasRegisterMethod!(IF, "registerPort", VlPort!(IF, N))) {
    //   _channel.registerPort();
    // }
    // }
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

struct VlSignal(T)
{
  T* _sig;

  alias get this;
  
  ref T get() { return *_sig; }

  void write(T val) { *_sig = val; }

  T read() { return *_sig; }

  void read(ref T val) { val = *_sig; }

  ref T opAssign(T val) {
    *_sig = val;
    return *_sig;
  }

  void opAssign(T* sig) { _sig = sig; }

  this(T* sig) { _sig = sig; }

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

class VerilatedVcdD {
  ESDLVerilatedVcdD _vcd_d;

  this(VerilatedVcdFile filep = null) {
    _vcd_d = createVcdD(filep);
  }
  
  final bool isOpen() const { return _vcd_d.isOpen(); }

  final void open(const(char) *filename) { _vcd_d.open(filename); }
  final void open(string filename) {
    import std.string: toStringz;
    _vcd_d.open(filename.toStringz());
  }

  final void openNext(bool incFilename = true) { _vcd_d.openNext(incFilename); }
  final void rolloverMB(size_t rMB) { _vcd_d.rolloverMB(rMB); }
  final void close() { _vcd_d.close(); }
  final void flush() { _vcd_d.flush(); }
  final void dump(ulong timeui) { _vcd_d.dump(timeui); }
  final void dump(double timestamp) { _vcd_d.dump(timestamp); }
  final void dump(uint timestamp) { _vcd_d.dump(timestamp); }
  final void dump(int timestamp) { _vcd_d.dump(timestamp); }

  final void set_time_unit(const(char*) unit) { _vcd_d.set_time_unit(unit); }
  final void set_time_unit(string unit) {
    import std.string: toStringz;
    _vcd_d.set_time_unit(unit.toStringz());
  }
  final void set_time_unit(ref const(basic_string!char) unit) { _vcd_d.set_time_unit(unit); }
  final void set_time_resolution(const(char*) unit) { _vcd_d.set_time_resolution(unit); }
  final void set_time_resolution(string resolution) {
    import std.string: toStringz;
    _vcd_d.set_time_resolution(resolution.toStringz());
  }
  final void set_time_resolution(ref const(basic_string!char) unit) { _vcd_d.set_time_resolution(unit); }

  final VerilatedVcdC getVcdC() { return _vcd_d.getVcdC(); }

}

class VerilatedVcdFileD {
  VerilatedVcdFile _file;

  this() {
    _file = createVcdFile();
  }
  
  final bool open(ref const(basic_string!char) name) { return _file.open(name); }
  final void close() { _file.close(); }
  final ulong write(const(char*) bufp, long len) { return _file.write(bufp, len); }
  final ulong write(string bufp, long len) {
    import std.string: toStringz;
    return _file.write(bufp.toStringz(), len);
  }
}

