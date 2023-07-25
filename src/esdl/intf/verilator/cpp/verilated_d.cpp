#include <verilated.h>

namespace verilated
{
  /// Enable debug of internal verilated code
  void debugLevel(int level) VL_MT_SAFE {
    Verilated::debug(level);
  }
  int debugLevel() VL_MT_SAFE { return Verilated::debug(); }
  /// Set the last VerilatedContext accessed
  /// Generally threadContextp(value) should be called instead
  void lastContextp(VerilatedContext* contextp) VL_MT_SAFE {
    Verilated::lastContextp(contextp);
  }
  /// Return the last VerilatedContext accessed
  /// Generally threadContextp() should be called instead
  VerilatedContext* lastContextp() VL_MT_SAFE {
    return Verilated::lastContextp();
  }
  /// Set the VerilatedContext used by the current thread

  /// If using multiple contexts, and threads are created by the user's
  /// wrapper (not Verilator itself) then this must be called to set the
  /// context that applies to each thread
  void threadContextp(VerilatedContext* contextp) VL_MT_SAFE {
    Verilated::threadContextp(contextp);
  }
  /// Return the VerilatedContext for the current thread
  VerilatedContext* threadContextp() VL_MT_SAFE {
    return Verilated::threadContextp();
  }
  /// Return the global VerilatedContext, used if none created by user
  VerilatedContext* defaultContextp() VL_MT_SAFE {
    return Verilated::defaultContextp();
  }

  /// Call VerilatedContext::assertOn using current thread's VerilatedContext
  void assertOn(bool flag) VL_MT_SAFE {
    Verilated::assertOn(flag);
  }
  /// Return VerilatedContext::assertOn() using current thread's VerilatedContext
  bool assertOn() VL_MT_SAFE {
    return Verilated::assertOn();
  }
  /// Call VerilatedContext::calcUnusedSigs using current thread's VerilatedContext
  void calcUnusedSigs(bool flag) VL_MT_SAFE {
    Verilated::calcUnusedSigs(flag);
  }
  /// Return VerilatedContext::calcUnusedSigs using current thread's VerilatedContext
  bool calcUnusedSigs() VL_MT_SAFE {
    return Verilated::calcUnusedSigs();
  }
  /// Call VerilatedContext::commandArgs using current thread's VerilatedContext
  void commandArgs(int argc, const char** argv) VL_MT_SAFE {
    Verilated::commandArgs(argc, argv);
  }
  void commandArgs(int argc, char** argv) VL_MT_SAFE {
    Verilated::commandArgs(argc, argv);
  }
  /// Call VerilatedContext::commandArgsAdd using current thread's VerilatedContext
  void commandArgsAdd(int argc, const char** argv) {
    Verilated::commandArgsAdd(argc, argv);
  }
  /// Return VerilatedContext::commandArgsPlusMatch using current thread's VerilatedContext
  const char* commandArgsPlusMatch(const char* prefixp) VL_MT_SAFE {
    return Verilated::commandArgsPlusMatch(prefixp);
  }
  /// Call VerilatedContext::errorLimit using current thread's VerilatedContext
  void errorLimit(int val) VL_MT_SAFE {
    Verilated::errorLimit(val);
  }
  /// Return VerilatedContext::errorLimit using current thread's VerilatedContext
  int errorLimit() VL_MT_SAFE {
    return Verilated::errorLimit();
  }
  /// Call VerilatedContext::fatalOnError using current thread's VerilatedContext
  void fatalOnError(bool flag) VL_MT_SAFE {
    Verilated::fatalOnError(flag);
  }
  /// Return VerilatedContext::fatalOnError using current thread's VerilatedContext
  bool fatalOnError() VL_MT_SAFE {
    return Verilated::fatalOnError();
  }
  /// Call VerilatedContext::fatalOnVpiError using current thread's VerilatedContext
  void fatalOnVpiError(bool flag) VL_MT_SAFE {
    Verilated::fatalOnVpiError(flag);
  }
  /// Return VerilatedContext::fatalOnVpiError using current thread's VerilatedContext
  bool fatalOnVpiError() VL_MT_SAFE {
    return Verilated::fatalOnVpiError();
  }
  /// Call VerilatedContext::gotError using current thread's VerilatedContext
  void gotError(bool flag) VL_MT_SAFE {
    Verilated::gotError(flag);
  }
  /// Return VerilatedContext::gotError using current thread's VerilatedContext
  bool gotError() VL_MT_SAFE {
    return Verilated::gotError();
  }
  /// Call VerilatedContext::gotFinish using current thread's VerilatedContext
  void gotFinish(bool flag) VL_MT_SAFE {
    Verilated::gotFinish(flag);
  }
  /// Return VerilatedContext::gotFinish using current thread's VerilatedContext
  bool gotFinish() VL_MT_SAFE {
    return Verilated::gotFinish();
  }
  /// Call VerilatedContext::randReset using current thread's VerilatedContext
  void randReset(int val) VL_MT_SAFE {
    Verilated::randReset(val);
  }
  /// Return VerilatedContext::randReset using current thread's VerilatedContext
  int randReset() VL_MT_SAFE {
    return Verilated::randReset();
  }
  /// Call VerilatedContext::randSeed using current thread's VerilatedContext
  void randSeed(int val) VL_MT_SAFE {
    Verilated::randSeed(val);
  }
  /// Return VerilatedContext::randSeed using current thread's VerilatedContext
  int randSeed() VL_MT_SAFE {
    return Verilated::randSeed();
  }
  /// Call VerilatedContext::time using current thread's VerilatedContext
  void time(uint64_t val) VL_MT_SAFE {
    Verilated::time(val);
  }
  /// Return VerilatedContext::time using current thread's VerilatedContext
  uint64_t time() VL_MT_SAFE {
    return Verilated::time();
  }
  /// Call VerilatedContext::timeInc using current thread's VerilatedContext
  void timeInc(uint64_t add) VL_MT_UNSAFE {
    Verilated::timeInc(add);
  }
  // Deprecated
  int timeunit() VL_MT_SAFE {
    return Verilated::timeunit();
  }
  int timeprecision() VL_MT_SAFE {
    return Verilated::timeprecision();
  }
  /// Call VerilatedContext::tracesEverOn using current thread's VerilatedContext
  void traceEverOn(bool flag) VL_MT_SAFE {
    Verilated::traceEverOn(flag);
  }

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
  const char* productName() VL_PURE {
    return Verilated::productName();
  }
  /// Return product version for (at least) VPI
  const char* productVersion() VL_PURE {
    return Verilated::productVersion();
  }

  /// Call OS to make a directory
  void mkdir(const char* dirname) VL_MT_UNSAFE {
    Verilated::mkdir(dirname);
  }

  /// When multithreaded, quiesce the model to prepare for trace/saves/coverage
  /// This may only be called when no locks are held.
  void quiesce() VL_MT_SAFE {
    Verilated::quiesce();
  }

  /// For debugging, print much of the Verilator internal state.
  /// The output of this function may change in future
  /// releases - contact the authors before production use.
  void internalsDump() VL_MT_SAFE {
    Verilated::internalsDump();
  }
  /// For debugging, print text list of all scope names with
  /// dpiImport/Export context.  This function may change in future
  /// releases - contact the authors before production use.
  void scopesDump() VL_MT_SAFE {
    Verilated::scopesDump();
  }
  // Internal: Find scope
  const VerilatedScope* scopeFind(const char* namep) VL_MT_SAFE {
    return Verilated::scopeFind(namep);
  }
  const VerilatedScopeNameMap* scopeNameMap() VL_MT_SAFE {
    return Verilated::scopeNameMap();
  }

  // METHODS - INTERNAL USE ONLY (but public due to what uses it)
  // Internal: Create a new module name by concatenating two strings
  // Returns pointer to thread-local data (overwritten on next call)
  const char* catName(const char* n1, const char* n2,
			     const char* delimiter = ".") VL_MT_SAFE {
    return Verilated::catName(n1, n2, delimiter);
  };

  // Internal: Throw signal assertion
  void nullPointerError(const char* filename, int linenum)  VL_MT_SAFE {
    Verilated::nullPointerError(filename, linenum);
  }
  void overWidthError(const char* signame)  VL_MT_SAFE {
    Verilated::overWidthError(signame);
  }
  void scTimePrecisionError(int sc_prec, int vl_prec)  VL_MT_SAFE {
    Verilated::scTimePrecisionError(sc_prec, vl_prec);
  }
  void scTraceBeforeElaborationError()  VL_MT_SAFE {
    Verilated::scTraceBeforeElaborationError();
  }

  // Internal: Get and set DPI context
  const VerilatedScope* dpiScope() VL_MT_SAFE {
    return Verilated::dpiScope();
  }
  void dpiScope(const VerilatedScope* scopep) VL_MT_SAFE {
    Verilated::dpiScope(scopep);
  }
  void dpiContext(const VerilatedScope* scopep, const char* filenamep,
			 int lineno) VL_MT_SAFE {
    Verilated::dpiContext(scopep, filenamep, lineno);
  }
  void dpiClearContext() VL_MT_SAFE {
    Verilated::dpiClearContext();
  }
  bool dpiInContext() VL_MT_SAFE {
    return Verilated::dpiInContext();
  }
  const char* dpiFilenamep() VL_MT_SAFE {
    return Verilated::dpiFilenamep();
  }
  int dpiLineno() VL_MT_SAFE {
    return Verilated::dpiLineno();
  }
  int exportFuncNum(const char* namep) VL_MT_SAFE {
    return Verilated::exportFuncNum(namep);
  }

  // Internal: Set the mtaskId, called when an mtask starts
  // Per thread, so no need to be in VerilatedContext
  void mtaskId(uint32_t id) VL_MT_SAFE {
    Verilated::mtaskId(id);
  }
  uint32_t mtaskId() VL_MT_SAFE {
    return Verilated::mtaskId();
  }
  void endOfEvalReqdInc() VL_MT_SAFE {
    Verilated::endOfEvalReqdInc();
  }
  void endOfEvalReqdDec() VL_MT_SAFE {
    Verilated::endOfEvalReqdDec();
  }

  // Internal: Called at end of each thread mtask, before finishing eval
  void endOfThreadMTask(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE {
    Verilated::endOfThreadMTask(evalMsgQp);
  }
  // Internal: Called at end of eval loop
  void endOfEval(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE {
    Verilated::endOfEval(evalMsgQp);
  }
}
