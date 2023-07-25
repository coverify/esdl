module esdl.intf.verilator.verilated;

import esdl.base.core: _esdl__component, NamedComp, _esdl__ignore,
  HierComp, RootEntity, EsdlSimulator, Time, Process, SimPhase,
  getRootEntity, EntityIntf, ElabContext, BaseExport, Entity,
  BasePort;
import std.traits: isIntegral, isBoolean;
import esdl.data.bvec: isBitVector, ubvec;
import esdl.rand.misc: rand;

extern (C++, verilated) {
  /// Enable debug of internal verilated code
  void debugLevel(int level);
  int debugLevel();

  /// Set the last VerilatedContext accessed
  /// Generally threadContextp(value) should be called instead

  // void lastContextp(VerilatedContext* contextp);
  /// Return the last VerilatedContext accessed
  /// Generally threadContextp() should be called instead

  // VerilatedContext* lastContextp();
  /// Set the VerilatedContext used by the current thread

  /// If using multiple contexts, and threads are created by the user's
  /// wrapper (not Verilator itself) then this must be called to set the
  /// context that applies to each thread
  // void threadContextp(VerilatedContext* contextp);

  /// Return the VerilatedContext for the current thread
  // VerilatedContext* threadContextp();

  /// Return the global VerilatedContext, used if none created by user
  // VerilatedContext* defaultContextp();

  /// Call VerilatedContext::assertOn using current thread's VerilatedContext
  void assertOn(bool flag);
  
  /// Return VerilatedContext::assertOn() using current thread's VerilatedContext
  bool assertOn();

  /// Call VerilatedContext::calcUnusedSigs using current thread's VerilatedContext
  void calcUnusedSigs(bool flag);

  /// Return VerilatedContext::calcUnusedSigs using current thread's VerilatedContext
  bool calcUnusedSigs();
  
  /// Call VerilatedContext::commandArgs using current thread's VerilatedContext
  void commandArgs(int argc, const char** argv);
  
  void commandArgs(int argc, char** argv);
  
  /// Call VerilatedContext::commandArgsAdd using current thread's VerilatedContext
  void commandArgsAdd(int argc, const char** argv);
  
  /// Return VerilatedContext::commandArgsPlusMatch using current thread's VerilatedContext
  const (char*) commandArgsPlusMatch(const (char*) prefixp);
  
  /// Call VerilatedContext::errorLimit using current thread's VerilatedContext
  void errorLimit(int val);
  
  /// Return VerilatedContext::errorLimit using current thread's VerilatedContext
  int errorLimit();
  
  /// Call VerilatedContext::fatalOnError using current thread's VerilatedContext
  void fatalOnError(bool flag);
  
  /// Return VerilatedContext::fatalOnError using current thread's VerilatedContext
  bool fatalOnError();
  
  /// Call VerilatedContext::fatalOnVpiError using current thread's VerilatedContext
  void fatalOnVpiError(bool flag);
  
  /// Return VerilatedContext::fatalOnVpiError using current thread's VerilatedContext
  bool fatalOnVpiError();
  
  /// Call VerilatedContext::gotError using current thread's VerilatedContext
  void gotError(bool flag);
  
  /// Return VerilatedContext::gotError using current thread's VerilatedContext
  bool gotError();
  
  /// Call VerilatedContext::gotFinish using current thread's VerilatedContext
  void gotFinish(bool flag);
  
  /// Return VerilatedContext::gotFinish using current thread's VerilatedContext
  bool gotFinish();
  
  /// Call VerilatedContext::randReset using current thread's VerilatedContext
  void randReset(int val);
  
  /// Return VerilatedContext::randReset using current thread's VerilatedContext
  int randReset();
  
  /// Call VerilatedContext::randSeed using current thread's VerilatedContext
  void randSeed(int val);
  
  /// Return VerilatedContext::randSeed using current thread's VerilatedContext
  int randSeed();
  
  /// Call VerilatedContext::time using current thread's VerilatedContext
  void time(ulong val);
  
  /// Return VerilatedContext::time using current thread's VerilatedContext
  ulong time();
  
  /// Call VerilatedContext::timeInc using current thread's VerilatedContext
  void timeInc(ulong add);
  
  // Deprecated
  int timeunit();
  
  int timeprecision();
  
  /// Call VerilatedContext::tracesEverOn using current thread's VerilatedContext
  void traceEverOn(bool flag);

  //   /// Callback typedef for addFlushCb, addExitCb
  //   using VoidPCb = void (*)(void*);
  //   /// Add callback to run on global flush
  //   void addFlushCb(VoidPCb cb, void* datap) VL_MT_SAFE;
  //   /// Remove callback to run on global flush
  //   void removeFlushCb(VoidPCb cb, void* datap) VL_MT_SAFE;
  //   /// Run flush callbacks registered with addFlushCb
  //   void runFlushCallbacks() VL_MT_SAFE;
  // #ifndef VL_NO_LEGACY
  //   void flushCall() VL_MT_SAFE { runFlushCallbacks(); }  // Deprecated
  // #endif
  //   /// Add callback to run prior to exit termination
  //   void addExitCb(VoidPCb cb, void* datap) VL_MT_SAFE;
  //   /// Remove callback to run prior to exit termination
  //   void removeExitCb(VoidPCb cb, void* datap) VL_MT_SAFE;
  //   /// Run exit callbacks registered with addExitCb
  //   void runExitCallbacks() VL_MT_SAFE;

  /// Return product name for (at least) VPI
  const (char*) productName();
  
  /// Return product version for (at least) VPI
  const (char*) productVersion();

  /// Call OS to make a directory
  void mkdir(const (char*) dirname);

  /// When multithreaded, quiesce the model to prepare for trace/saves/coverage
  /// This may only be called when no locks are held.
  void quiesce();

  /// For debugging, print much of the Verilator internal state.
  /// The output of this function may change in future
  /// releases - contact the authors before production use.
  void internalsDump();
  
  /// For debugging, print text list of all scope names with
  /// dpiImport/Export context.  This function may change in future
  /// releases - contact the authors before production use.
  void scopesDump();

  // Internal: Find scope
  // const VerilatedScope* scopeFind(const char* namep);
  
  // const VerilatedScopeNameMap* scopeNameMap();

  // METHODS - INTERNAL USE ONLY (but public due to what uses it)
  // Internal: Create a new module name by concatenating two strings
  // Returns pointer to thread-local data (overwritten on next call)
  const (char*) catName(const (char*) n1, const (char*) n2,
			       const (char*) delimiter = ".");

  // Internal: Throw signal assertion
  void nullPointerError(const (char*) filename, int linenum);
  
  void overWidthError(const (char*) signame);
  void scTimePrecisionError(int sc_prec, int vl_prec);
  void scTraceBeforeElaborationError();

  // Internal: Get and set DPI context
  // const VerilatedScope* dpiScope();
  // void dpiScope(const VerilatedScope* scopep);
  // void dpiContext(const VerilatedScope* scopep, const char* filenamep,
  // 			 int lineno);
  
  void dpiClearContext();
  bool dpiInContext();
  const (char*) dpiFilenamep();
  int dpiLineno();
  int exportFuncNum(const char* namep);

  // Internal: Set the mtaskId, called when an mtask starts
  // Per thread, so no need to be in VerilatedContext
  void mtaskId(uint id);
  uint mtaskId();
  void endOfEvalReqdInc();
  void endOfEvalReqdDec();

  // Internal: Called at end of each thread mtask, before finishing eval
  // void endOfThreadMTask(VerilatedEvalMsgQueue* evalMsgQp);
  // Internal: Called at end of eval loop
  // void endOfEval(VerilatedEvalMsgQueue* evalMsgQp);
}

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



abstract class VlInterface: Entity, rand.disable { }

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


struct VpiSignalBinder
{
  VpiSignalBinderObj _binder;

  alias binder this;

  VpiSignalBinderObj binder() {
    if (_binder is null) _binder = new VpiSignalBinderObj();
    return _binder;
  }
}

class VpiSignalBinderObj
{
  VpiBindSignalBase[] _signals;

  void add(T)(ref T val, string net) {
    _signals ~= new VpiBindSignal!(T)(val, net);
  }

  void add(T)(ref T val, size_t index, string net) {
    _signals ~= new VpiBindSignalIndexed!(T)(val, index, net);
  }

  void put() {
    foreach (sig; _signals) {
      sig.hdlPut();
    }
  }

  void get() {
    foreach (sig; _signals) {
      sig.hdlGet();
    }
  }
}

abstract class VpiBindSignalBase
{
  abstract void hdlPut();
  abstract void hdlGet();
}

class VpiBindSignal(T): VpiBindSignalBase
{
  import esdl.intf.vpi;

  immutable (T*) _vptr;

  vpiHandle _vpiHandle = null;

  this(ref T val, string net) {
    _vptr = & val;
    this.hdlBind(net);
  }

  public final void hdlBind(string net) {
    synchronized(this) {
      if(_vpiHandle !is null) {
	assert(false, "Signal is already bound: " ~ net);
      }
	
      _vpiHandle = vpiGetHandleByName(net, null);

      if(_vpiHandle is null) {
	assert(false, "Can not find \"" ~ net ~ "\" in the verilog design");
      }
    
      auto handleType = vpi_get(vpiType, _vpiHandle);
      if(handleType !is vpiNet && handleType !is vpiReg) {
	assert(false, "\"" ~ net ~ "\"" ~ " is not of reg or wire type");
      }

      auto size = vpi_get(vpiSize, _vpiHandle);
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
      // hdlGet();

      // auto p_cb = new s_cb_data();	  
      // p_cb.reason = vpiCbValueChange;
      // p_cb.cb_rtn = &_hdlConnect;
      // p_cb.obj = _vpiHandle;
      // // cb.time = null;
      // // cb.value = null;

      // Object obj = this;
      // p_cb.user_data = cast(void*) obj;

      // vpi_register_cb(p_cb);
    }
  }
  
  final override void hdlPut() {
    assert (vpiIsUsable);
    synchronized (this) {
      s_vpi_value v;
      v.format = vpiVectorVal;
      static if (isBitVector!T) {
	enum size_t NWORDS = (T.SIZE+31)/32;
      }
      else {
	enum size_t NWORDS = (8*T.sizeof + 31)/32;
      }
      s_vpi_vecval[NWORDS+1] vector;

      static if(isBitVector!T) {
	(*_vptr).toVpiVecValue(vector);
      }
      else {
	enum size_t size = 8 * T.sizeof;
	// special handling for long/ulong for others simply copy
	static if(size > 32) {
	  vector[0].aval = cast(uint) (*_vptr);
	  vector[1].aval = cast(uint) ((*_vptr) >>> 32);
	  vector[0].bval = 0;
	  vector[1].bval = 0;
	}
	else {
	  vector[0].aval = (*_vptr);
	  vector[0].bval = 0;
	}
      }

      v.value.vector = vector.ptr;
      vpi_put_value(_vpiHandle, &v, null, vpiNoDelay);

    }
  }
  
  final override void hdlGet() {
    synchronized (this) {
      // for now, get the value and display it
      s_vpi_value v;
      v.format = vpiVectorVal;
      vpi_get_value(_vpiHandle, &v);
      // at the time of binding we already checked that the size of
      // the signal at the two sides match.

      static if(isBitVector!T) {
	enum WS = (T.SIZE+31)/32;
	(*_vptr) = v.value.vector[0..WS];
      }
      else {
	enum size_t size = 8 * T.sizeof;
	// special handling for long/ulong for others simply copy
	static if (size > 32) {
	  ulong lsw = v.value.vector[0].aval;
	  ulong msw = v.value.vector[1].aval;
	  lsw |= (msw << 32);
	  (*_vptr) = cast(T) lsw;
	}
	else {
	  (*_vptr) = cast(T) v.value.vector[0].aval;
	}
      }
    }
  }
}

class VpiBindSignalIndexed(T): VpiBindSignalBase
{
  import esdl.intf.vpi;

  immutable (T*) _vptr;

  immutable size_t _index;

  vpiHandle _vpiHandle = null;

  this(ref T val, size_t index, string net) {
    _vptr = & val;
    _index = index;
    this.hdlBind(net);
  }

  public final void hdlBind(string net) {
    synchronized(this) {
      if(_vpiHandle !is null) {
	assert(false, "Signal is already bound: " ~ net);
      }
	
      _vpiHandle = vpiGetHandleByName(net, null);

      if(_vpiHandle is null) {
	assert(false, "Can not find \"" ~ net ~ "\" in the verilog design");
      }
    
      auto handleType = vpi_get(vpiType, _vpiHandle);
      if(handleType !is vpiNet && handleType !is vpiReg) {
	assert(false, "\"" ~ net ~ "\"" ~ " is not of reg or wire type");
      }

      auto size = vpi_get(vpiSize, _vpiHandle);
      if(size !is 1) {
	assert(false, "hdlBind: signal size for VpiBindSignalIndexed has to be 1");
      }

      // Reflect the HDL signal value here
      // hdlGet();

      // auto p_cb = new s_cb_data();	  
      // p_cb.reason = vpiCbValueChange;
      // p_cb.cb_rtn = &_hdlConnect;
      // p_cb.obj = _vpiHandle;
      // // cb.time = null;
      // // cb.value = null;

      // Object obj = this;
      // p_cb.user_data = cast(void*) obj;

      // vpi_register_cb(p_cb);
    }
  }
  
  final override void hdlPut() {
    s_vpi_value v;
    v.format = vpiScalarVal;
    v.value.scalar = (*_vptr)[_index];
    vpi_put_value(_vpiHandle, &v, null, vpiNoDelay);
  }
  
  final override void hdlGet() {
    // for now, get the value and display it
    s_vpi_value v;
    v.format = vpiScalarVal;
    vpi_get_value(_vpiHandle, &v);
    // at the time of binding we already checked that the size of
    // the signal at the two sides match.
    (*_vptr)[_index] = cast(bool) v.value.scalar;
  }
  
}




struct VpiSignal(T)
{
  import esdl.intf.vpi;

  alias VAL_TYPE = T;

  T _value;

  alias read this;

  vpiHandle vpiNetHandle = null;

  public int opCmp(string file = __FILE__,
		   size_t line = __LINE__, V)(const V other) const
       if (isIntegral!V || isBitVector!V || isBoolean!V) {
	 return this._value.opCmp(other);
       }

  public bool opEquals(string file = __FILE__,
		       size_t line = __LINE__, V)(const V other)
       if (isIntegral!V || isBitVector!V || isBoolean!V) {
	 return this._value.opEquals(other);
       }

  public final void opAssign(V) (V val)
       if (isAssignable!(T, V)) {
	 _value = other;
	 this.hdlPut();
       }
  
  public final void opOpAssign(string op, T)(T other) {
    synchronized(this) {
      _value.opOpAssign!op(other);
      this.hdlPut();
    }
  }

  T read() {
    hdlGet();
    return _value;
  }

  // private static int _hdlConnect(p_cb_data cb) {
  //   auto t = cast(VpiSignal!T*) (*cb).user_data;
  //   t.hdlGet();
  //   return 0;
  // }

  this(string net) {
    this.hdlBind(net);
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

      // auto p_cb = new s_cb_data();	  
      // p_cb.reason = vpiCbValueChange;
      // p_cb.cb_rtn = &_hdlConnect;
      // p_cb.obj = vpiNetHandle;
      // // cb.time = null;
      // // cb.value = null;

      // Object obj = this;
      // p_cb.user_data = cast(void*) obj;

      // vpi_register_cb(p_cb);
    }
  }
  
  final private void hdlPut() {
    assert (vpiIsUsable);
    synchronized (this) {
      s_vpi_value v;
      v.format = vpiVectorVal;
      static if (isBitVector!T) {
	enum size_t NWORDS = (T.SIZE+31)/32;
      }
      else {
	enum size_t NWORDS = (8*T.sizeof + 31)/32;
      }
      s_vpi_vecval[NWORDS+1] vector;

      static if(isBitVector!T) {
	_value.toVpiVecValue(vector);
      }
      else {
	enum size_t size = 8 * T.sizeof;
	// special handling for long/ulong for others simply copy
	static if(size > 32) {
	  vector[0].aval = cast(uint) _value;
	  vector[1].aval = cast(uint) (_value >>> 32);
	  vector[0].bval = 0;
	  vector[1].bval = 0;
	}
	else {
	  vector[0].aval = _value;
	  vector[0].bval = 0;
	}
      }

      v.value.vector = vector.ptr;
      vpi_put_value(vpiNetHandle, &v, null, vpiNoDelay);

    }
  }
  
  private final void hdlGet() {
    synchronized (this) {
      // for now, get the value and display it
      s_vpi_value v;
      v.format = vpiVectorVal;
      vpi_get_value(vpiNetHandle, &v);
      // at the time of binding we already checked that the size of
      // the signal at the two sides match.

      static if(isBitVector!T) {
	enum WS = (T.SIZE+31)/32;
	_value = v.value.vector[0..WS];
      }
      else {
	enum size_t size = 8 * T.sizeof;
	// special handling for long/ulong for others simply copy
	static if (size > 32) {
	  ulong lsw = v.value.vector[0].aval;
	  ulong msw = v.value.vector[1].aval;
	  lsw |= (msw << 32);
	  _value = cast(T) lsw;
	}
	else {
	  _value = cast(T) v.value.vector[0].aval;
	}
      }
    }
  }



}

