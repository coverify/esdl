module esdl.rand.agent;

import esdl.data.folder: Folder;

import esdl.solver.base;
import esdl.solver.mono: CstMonoSolver;
import esdl.solver.z3: CstZ3Solver;
import esdl.solver.buddy: CstBuddySolver;

import esdl.rand.misc: _esdl__Sigbuf, CstVectorOp;
import esdl.rand.proxy: _esdl__Proxy;
import esdl.rand.pred: CstPredicate, Hash;
import esdl.rand.base: CstDomBase, CstDomSet, CstIterCallback,
  CstDepCallback, CstScope, CstIterator, CstVecNodeIntf,
  CstVecTerm, CstLogicTerm, CstDepIntf;
import esdl.rand.base: CstValue, CstVarNodeIntf;


class CstSolverAgent			// agent of related predicates
{
  CstMonoSolver!int intMono;
  CstMonoSolver!uint uintMono;
  CstMonoSolver!long longMono;
  CstMonoSolver!ulong ulongMono;

  uint _softPredicateCount;
  bool _hasVectorConstraints;
  bool _hasUniqueConstraints;
  bool _hasDistConstraints;

  // bool _isMono;
  // CstDomBase _monoDom;

  uint softPredicateCount() {
    return _softPredicateCount;
  }

  bool hasVectorConstraints() {
    return _hasVectorConstraints;
  }
  
  bool hasUniqueConstraints() {
    return _hasUniqueConstraints;
  }
  
  bool hasDistConstraints() {
    return _hasDistConstraints;
  }

  void markDist() {
    _hasDistConstraints = true;
  }

  void initialize(_esdl__Proxy proxy) {
    _proxy = proxy;
    _preds.reset();
    _predList.reset();

    _annotatedDoms.reset();
    _annotatedDomArrs.reset();
    _annotatedVars.reset();
    _annotatedVarArrs.reset();

    _softPredicateCount = 0;
    _hasVectorConstraints = false;
    _hasUniqueConstraints = false;
    _hasDistConstraints = false;

    _distPred = null;
    _solver = null;
    _state = State.INIT;

  }
  
  Folder!(CstPredicate, "preds") _preds;

  CstPredicate _distPred;

  Folder!(CstPredicate, "predList") _predList;

  CstPredicate[] predicates() {
    return _preds[];
  }

  _esdl__Proxy _proxy;

  this () {
    intMono = new CstMonoSolver!int("");
    uintMono = new CstMonoSolver!uint("");
    longMono = new CstMonoSolver!long("");
    ulongMono = new CstMonoSolver!ulong("");
  }

  _esdl__Proxy getProxy() {
    return _proxy;
  }

  void addPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln(pred.describe());
    _predList ~= pred;
  }

  Folder!(CstDomBase, "annotatedDoms") _annotatedDoms;
  uint addAnnotatedDom(CstDomBase dom) {
    // import std.stdio;
    // writeln(annotatedDom.describe());
    uint index = cast (uint) _annotatedDoms.length;
    _annotatedDoms ~= dom;
    return index;
  }

  CstDomBase[] annotatedDoms() {
    return _annotatedDoms[];
  }
  
  Folder!(CstDomSet, "annotatedDomArrs") _annotatedDomArrs;
  uint addAnnotatedDomArr(CstDomSet domArr) {
    uint index = cast (uint) _annotatedDomArrs.length;
    _annotatedDomArrs ~= domArr;
    return index;
  }

  CstDomSet[] annotatedDomArrs() {
    return _annotatedDomArrs[];
  }
  
  Folder!(CstDomBase, "annotatedVars") _annotatedVars;
  uint addAnnotatedVar(CstDomBase var) {
    uint index = cast (uint) _annotatedVars.length;
    _annotatedVars ~= var;
    return index;
  }

  CstDomBase[] annotatedVars() {
    return _annotatedVars[];
  }

  Folder!(CstDomSet, "annotatedVarArrs") _annotatedVarArrs;
  uint addAnnotatedVarArr(CstDomSet varArr) {
    uint index = cast (uint) _annotatedVarArrs.length;
    _annotatedVarArrs ~= varArr;
    return index;
  }

  CstDomSet[] annotatedVarArrs() {
    return _annotatedVarArrs[];
  }

  void setSolverContext(CstPredicate solvablePred, uint level) {
    solvablePred.setSolverContext(this, level);

    setOrderAndBools();
  }

  void setOrderAndBools() {
    
    import std.algorithm.sorting: sort; 
    
    _softPredicateCount = 0;
    _hasVectorConstraints = false;
    _hasUniqueConstraints = false;
    _hasDistConstraints = false;

    // foreach (pred; _preds) pred._agent = null;
    _preds.reset();
    foreach (pred; sort!((x, y) => x.hashValue() < y.hashValue())(_predList[])) {
      if (pred.isDistPredicate()) this.markDist();
      // pred._agent = this;
      if (pred._soft != 0) _softPredicateCount += 1;
      if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
      if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
      _preds ~= pred;

    }

    // for the next cycle
    _predList.reset();
  }

  void annotate() {
    foreach (pred; _preds) {
      // import std.stdio;
      // writeln("Annotating: ", pred.fullName());
      assert (! pred.isBlocked());
      if (! hasDistConstraints)
	pred.annotate(this);
    }
  }

  _esdl__Sigbuf _sig;
  
  char[] signature() {
    _sig.reset();
    _sig ~= "HANDLER:\n";
    foreach (pred; _preds) {
      assert (! pred.isBlocked());
      if (! hasDistConstraints)
	pred.writeSignature(_sig, this);
    }
    return _sig[];
  }

  override size_t toHash() @trusted nothrow {
    import std.exception:assumeWontThrow;
    return assumeWontThrow(getHash());
  }
  
  bool _hasHashBeenCalculated = false;
  
  Hash _hash;
  
  ulong getHash(){
    if (_hasHashBeenCalculated){
      return _hash.hash;
    }
    _hash = Hash(cast(uint) _preds.length);
    foreach (pred; _preds){
      assert (! pred.isBlocked());
      if (! hasDistConstraints)
	pred.calcHash(_hash);
    }
    return _hash.hash;
  }

  public enum State: ubyte
    {   INIT,
	SOLVED
    }

  State _state;
  
  void reset() {
    _state = State.INIT;

    if (_distPred !is null) {
      // _distPred.reset;
      _distPred = null;
    }

    // Now handled in proxy
    // foreach (pred; _preds) pred.reset();
  }

  void markSolved() {
    _state = State.SOLVED;
  }

  bool isSolved() {
    return _state == State.SOLVED;
  }

  CstSolver _solver;

  void solve() {
    // import std.stdio;
    // writeln("Solving: ", this.describe());
    if (_proxy._esdl__debugSolver()) {
      import std.stdio;
      writeln(describe());
    }

    assert (_distPred is null || (! _distPred.distDomain().isRand()));
    annotate();
    bool monoFlag = false;
    if (!(_softPredicateCount != 0 || _hasVectorConstraints)) {
      if (_preds.length == 1 && _preds[0].isVisitor()) {
	_preds[0]._state = CstPredicate.State.SOLVED;
	_proxy.addSolvedDomain(_preds[0]._domain);
	monoFlag = true;
      }
      else if (_annotatedDoms.length == 1 && (! _annotatedDoms[0].isBool())) {
	// else if (_isMono && (! _monoDom.isBool())) {
	if (_annotatedDoms[0].bitcount() < 32) {
	  _solver = intMono;
	}
	else if (_annotatedDoms[0].bitcount == 32) {
	  if(_annotatedDoms[0].signed()) {
	    _solver = intMono;
	  }
	  else{
	    _solver = uintMono;
	  }
	}
	else if (_annotatedDoms[0].bitcount < 64) {
	  _solver = longMono;
	}
	else if (_annotatedDoms[0].bitcount == 64) {
	  if(_annotatedDoms[0].signed()) {
	    _solver = longMono;
	  }
	  else {
	    _solver = ulongMono;
	  }
	}
	if ( _solver !is null ) {
	  // import std.stdio;
	  monoFlag = _solver.solve(this);
	  // writeln("here mono. ", monoFlag);
	}
      }
    }
    if (!monoFlag){
      char[] mutableSig = signature();
      // assert(sig1 == mutableSig);

      if (_proxy._esdl__debugSolver()) {
	import std.stdio;
	writeln(mutableSig);
      }
      // do not use mutableSig.to!string since we do not want to allocate mem
      // for now
      CstSolver* solverp = (cast(string) mutableSig) in _proxy._solvers;
      // _hasHashBeenCalculated = false;
      // CstSolver* solverp = this in _proxy._solvers;

      if (solverp !is null) {
	_solver = *solverp;
	_solver.solve(this);
      }
      else {
	import std.conv: to;
	// do not use cast(string) mutableSig since it will
	// cast and use the same char buffer memory
	string immutableSig = mutableSig.to!string();
	if (_softPredicateCount != 0 || _hasVectorConstraints) {
	  if (_proxy._esdl__debugSolver()) {
	    import std.stdio;
	    writeln("Invoking Z3 because of Soft/Vector Constraints");
	    writeln("_preds: ", _preds[]);
	    foreach (pred; _preds) {
	      writeln(pred.describe());
	    }
	    writeln(describe());
	  }
	  _solver = new CstZ3Solver(immutableSig, this);
	  _solver.solve(this);
	}
	else {
	  uint totalBits;
	  uint domBits;
	  foreach (dom; _annotatedDoms) {
	    // assert (! dom.isProperDist());
	    uint domBC = dom.bitcount();
	    totalBits += domBC;
	    domBits += domBC;
	  }
	  foreach (var; _annotatedVars) totalBits += var.bitcount();
	  if (totalBits > 32 || _hasUniqueConstraints) {
	    if (_proxy._esdl__debugSolver()) {
	      import std.stdio;
	      writeln("Invoking Z3 because of > 32 bits");
	      writeln(describe());
	    }
	    _solver = new CstZ3Solver(immutableSig, this);
	    _solver.solve(this);
	  }
	  else {
	    _solver = new CstBuddySolver(immutableSig, this);
	    _solver.solve(this);
	  }
	}
	// _hasHashBeenCalculated = true;
	// if (_solver !is null) _proxy._solvers[this] = _solver;
	if (_solver !is null) _proxy._solvers[immutableSig] = _solver;
      }
    }
    // import std.stdio;
    // writeln(_solver.describe());
    // _solver.solve(this);
    foreach (pred; _preds) {
      // import std.stdio;
      // writeln("Marking Solved: ", pred.name());
      pred.markPredSolved();
    }

    this.markSolved();

    foreach (dom; _annotatedDoms) dom.setAnnotation(uint.max);
    foreach (dom; _annotatedVars) dom.setAnnotation(uint.max);
    foreach (dom; _annotatedDomArrs) dom.setAnnotation(uint.max);
    foreach (dom; _annotatedVarArrs) dom.setAnnotation(uint.max);
    
  }
      

  string describe() {
    import std.conv: to;
    string description = "CstSolverAgent -- \n";
    if (_preds.length > 0) {
      description ~= "  Predicates:\n";
      foreach (pred; _preds) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_softPredicateCount != 0) {
      description ~= "  Soft Predicates Count: " ~
	_softPredicateCount.to!string() ~ "\n";
    }
    return description;
  }
}
