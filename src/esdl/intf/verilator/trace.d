module esdl.intf.verilator.trace;

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

