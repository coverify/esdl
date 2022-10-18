module esdl.rand.agent;

import esdl.data.vector: Vector;

import esdl.solver.base;
import esdl.solver.mono: CstMonoSolver;
import esdl.solver.z3: CstZ3Solver;
import esdl.solver.buddy: CstBuddySolver;

import esdl.rand.misc: _esdl__Sigbuf, CstVectorOp;
import esdl.rand.proxy: _esdl__CstProcessor;
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

  void initialize(_esdl__CstProcessor proc) {
    _preds.reset();
    _predGroup.reset();

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
  
  Vector!(CstPredicate, "preds") _preds;

  CstPredicate _distPred;

  Vector!(CstPredicate, "predGroup") _predGroup;

  CstPredicate[] predicates() {
    return _preds[];
  }

  this () {
    intMono = new CstMonoSolver!int("");
    uintMono = new CstMonoSolver!uint("");
    longMono = new CstMonoSolver!long("");
    ulongMono = new CstMonoSolver!ulong("");
  }

  void addPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln(pred.describe());
    _predGroup ~= pred;
  }

  Vector!(CstDomBase, "annotatedDoms") _annotatedDoms;
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
  
  Vector!(CstDomSet, "annotatedDomArrs") _annotatedDomArrs;
  uint addAnnotatedDomArr(CstDomSet domArr) {
    uint index = cast (uint) _annotatedDomArrs.length;
    _annotatedDomArrs ~= domArr;
    return index;
  }

  CstDomSet[] annotatedDomArrs() {
    return _annotatedDomArrs[];
  }
  
  Vector!(CstDomBase, "annotatedVars") _annotatedVars;
  uint addAnnotatedVar(CstDomBase var) {
    uint index = cast (uint) _annotatedVars.length;
    _annotatedVars ~= var;
    return index;
  }

  CstDomBase[] annotatedVars() {
    return _annotatedVars[];
  }

  Vector!(CstDomSet, "annotatedVarArrs") _annotatedVarArrs;
  uint addAnnotatedVarArr(CstDomSet varArr) {
    uint index = cast (uint) _annotatedVarArrs.length;
    _annotatedVarArrs ~= varArr;
    return index;
  }

  CstDomSet[] annotatedVarArrs() {
    return _annotatedVarArrs[];
  }

  uint _annotationIndex;

  uint getAnnotationIndex() {
    return _annotationIndex++;
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
    foreach (pred; sort!((x, y) => x.hashValue() < y.hashValue())(_predGroup[])) {
      if (pred.isDistPredicate()) this.markDist();
      // pred._agent = this;
      if (pred._soft != 0) _softPredicateCount += 1;
      if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
      if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
      _preds ~= pred;

    }

    // for the next cycle
    _predGroup.reset();
  }

  void annotate(_esdl__CstProcessor proc) {
    foreach (pred; _preds) {
      // import std.stdio;
      // writeln("Annotating: ", pred._esdl__getFullName());
      assert (! pred.isBlocked());
      if (! hasDistConstraints)
	pred.annotate(this, proc);
    }
  }

  _esdl__Sigbuf _sig;
  
  char[] signature(_esdl__CstProcessor proc) {
    _sig.reset();
    _sig ~= "HANDLER:\n";
    foreach (pred; _preds) {
      assert (! pred.isBlocked());
      if (! hasDistConstraints)
	pred.writeSignature(proc, _sig, this);
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

  CstSolver[string] _solvers;

  CstSolver _solver;

  void solve(_esdl__CstProcessor proc) {
    // import std.stdio;
    // writeln("Solving: ", this.describe());
    if (proc.debugSolver()) {
      import std.stdio;
      writeln(describe());
    }

    assert (_distPred is null || (! _distPred.distDomain()._esdl__isRand()));
    annotate(proc);
    bool monoFlag = false;
    if (!(_softPredicateCount != 0 || _hasVectorConstraints)) {
      if (_preds.length == 1 && _preds[0].isVisitor()) {
	_preds[0]._state = CstPredicate.State.SOLVED;
	proc.addSolvedDomain(_preds[0]._domain);
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
	  monoFlag = _solver.solve(this, proc);
	  // writeln("here mono. ", monoFlag);
	}
      }
    }
    if (!monoFlag) {
      
      char[] mutableSig = signature(proc);
      // assert(sig1 == mutableSig);

      if (proc.debugSolver()) {
	import std.stdio;
	writeln(mutableSig);
      }
      // do not use mutableSig.to!string since we do not want to allocate mem
      // for now
      CstSolver* solverp = (cast(string) mutableSig) in _solvers;
      // _hasHashBeenCalculated = false;
      // CstSolver* solverp = this in _solvers;

      if (solverp !is null) {
	_solver = *solverp;
	_solver.solve(this, proc);
      }
      else {
	import std.conv: to;
	// do not use cast(string) mutableSig since it will
	// cast and use the same char buffer memory
	string immutableSig = mutableSig.to!string();
	if (_softPredicateCount != 0 || _hasVectorConstraints) {
	  if (proc.debugSolver()) {
	    import std.stdio;
	    writeln("Invoking Z3 because of Soft/Vector Constraints");
	    writeln("_preds: ", _preds[]);
	    foreach (pred; _preds) {
	      writeln(pred.describe());
	    }
	    writeln(describe());
	  }
	  _solver = new CstZ3Solver(immutableSig, this, proc);
	  _solver.solve(this, proc);
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
	    if (proc.debugSolver()) {
	      import std.stdio;
	      writeln("Invoking Z3 because of > 32 bits");
	      writeln(describe());
	    }
	    _solver = new CstZ3Solver(immutableSig, this, proc);
	    _solver.solve(this, proc);
	  }
	  else {
	    _solver = new CstBuddySolver(immutableSig, this, proc);
	    _solver.solve(this, proc);
	  }
	}
	// _hasHashBeenCalculated = true;
	// if (_solver !is null) _solvers[this] = _solver;
	if (_solver !is null) _solvers[immutableSig] = _solver;
      }
    }
    // import std.stdio;
    // writeln(_solver.describe());
    // _solver.solve(this, proc);
    foreach (pred; _preds) {
      // import std.stdio;
      // writeln("Marking Solved: ", pred._esdl__getName());
      pred.markPredSolved(proc);
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
	description ~= "    " ~ pred._esdl__getName() ~ '\n';
      }
    }
    if (_softPredicateCount != 0) {
      description ~= "  Soft Predicates Count: " ~
	_softPredicateCount.to!string() ~ "\n";
    }
    return description;
  }
}
