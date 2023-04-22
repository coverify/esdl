#include <verilated_vcd_c.h>

class ESDLVerilatedVcdD {
public:
  VerilatedVcdC* m_vcd_c;

  explicit ESDLVerilatedVcdD(VerilatedVcdFile* filep = nullptr)
  {
    m_vcd_c = new VerilatedVcdC(filep);
  }

  virtual ~ESDLVerilatedVcdD();

  bool isOpen() const  VL_MT_SAFE;
  /// Open a new VCD file
  /// This includes a complete header dump each time it is called,
  /// just as if this object was deleted and reconstructed.
  virtual void open(const char* filename) VL_MT_SAFE;
  /// Continue a VCD dump by rotating to a new file name
  /// The header is only in the first file created, this allows
  /// "cat" to be used to combine the header plus any number of data files.
  void openNext(bool incFilename = true) VL_MT_SAFE;
  /// Set size in megabytes after which new file should be created
  void rolloverSize(size_t rolloverSize) VL_MT_SAFE;
  /// Close dump
  void close() VL_MT_SAFE;
  /// Flush dump
  void flush() VL_MT_SAFE;
  /// Write one cycle of dump data
  /// Call with the current context's time just after eval'ed,
  /// e.g. ->dump(contextp->time())
  void dump(vluint64_t timeui) VL_MT_SAFE;
  /// Write one cycle of dump data - backward compatible and to reduce
  /// conversion warnings.  It's better to use a vluint64_t time instead.
  void dump(double timestamp);
  void dump(vluint32_t timestamp);
  void dump(int timestamp);

  // METHODS - Internal/backward compatible
  // \protectedsection

  // Set time units (s/ms, defaults to ns)
  // Users should not need to call this, as for Verilated models, these
  // propage from the Verilated default timeunit
  void set_time_unit(const char* unit) VL_MT_SAFE;

  void set_time_unit(const std::string& unit) VL_MT_SAFE;

  // Set time resolution (s/ms, defaults to ns)
  // Users should not need to call this, as for Verilated models, these
  // propage from the Verilated default timeprecision
  void set_time_resolution(const char* unit) VL_MT_SAFE;

  void set_time_resolution(const std::string& unit) VL_MT_SAFE;

  VerilatedVcdC* getVcdC();
  // Internal class access
  // inline VerilatedVcd* spTrace() { return m_vcd_c->spTrace(); }

};

ESDLVerilatedVcdD* createVcdD(VerilatedVcdFile* filep = nullptr) {
  return new ESDLVerilatedVcdD();
}
  
VerilatedVcdFile* createVcdFile() {
  return new VerilatedVcdFile();
}

ESDLVerilatedVcdD::~ESDLVerilatedVcdD() { delete m_vcd_c; }
bool ESDLVerilatedVcdD::isOpen() const VL_MT_SAFE  { return m_vcd_c->isOpen(); }
void ESDLVerilatedVcdD::open(const char* filename) VL_MT_SAFE { m_vcd_c->open(filename); }
void ESDLVerilatedVcdD::openNext(bool incFilename) VL_MT_SAFE { m_vcd_c->openNext(incFilename); }
void ESDLVerilatedVcdD::rolloverSize(size_t rolloverSize) VL_MT_SAFE { m_vcd_c->rolloverSize(rolloverSize); }
void ESDLVerilatedVcdD::close() VL_MT_SAFE { m_vcd_c->close(); }
/// Flush dump
void ESDLVerilatedVcdD::flush() VL_MT_SAFE { m_vcd_c->flush(); }
/// Write one cycle of dump data
/// Call with the current context's time just after eval'ed,
/// e.g. ->dump(contextp->time())
void ESDLVerilatedVcdD::dump(vluint64_t timeui) VL_MT_SAFE { m_vcd_c->dump(timeui); }
/// Write one cycle of dump data - backward compatible and to reduce
/// conversion warnings.  It's better to use a vluint64_t time instead.
void ESDLVerilatedVcdD::dump(double timestamp) { m_vcd_c->dump(timestamp); }
void ESDLVerilatedVcdD::dump(vluint32_t timestamp) { m_vcd_c->dump(timestamp); }
void ESDLVerilatedVcdD::dump(int timestamp) { m_vcd_c->dump(timestamp); }

// METHODS - Internal/backward compatible
// \protectedsection

// Set time units (s/ms, defaults to ns)
// Users should not need to call this, as for Verilated models, these
// propage from the Verilated default timeunit
void ESDLVerilatedVcdD::set_time_unit(const char* unit) VL_MT_SAFE { m_vcd_c->set_time_unit(unit); }

void ESDLVerilatedVcdD::set_time_unit(const std::string& unit) VL_MT_SAFE { m_vcd_c->set_time_unit(unit); }

// Set time resolution (s/ms, defaults to ns)
// Users should not need to call this, as for Verilated models, these
// propage from the Verilated default timeprecision
void ESDLVerilatedVcdD::set_time_resolution(const char* unit) VL_MT_SAFE { m_vcd_c->set_time_resolution(unit); }

void ESDLVerilatedVcdD::set_time_resolution(const std::string& unit) VL_MT_SAFE {
  m_vcd_c->set_time_resolution(unit);
}

VerilatedVcdC* ESDLVerilatedVcdD::getVcdC() {
  return m_vcd_c;
}

