module esdl.rand.pred;

import std.algorithm.sorting: sort;
import std.algorithm.searching: canFind, countUntil;
import std.algorithm: map, filter;
import std.array;
import std.container.array;

import esdl.data.folder;
import esdl.rand.proxy: _esdl__Proxy, _esdl__ConstraintBase;
import esdl.rand.misc;
import esdl.rand.base: CstDomBase, CstDomSet, CstIterCallback,
  CstDepCallback, CstScope, CstIterator, CstVecNodeIntf,
  CstVecTerm, CstLogicTerm, CstDepIntf;
import esdl.rand.base: CstValue, CstVarNodeIntf;

import esdl.solver.base;
import esdl.solver.mono: CstMonoSolver;
import esdl.solver.z3: CstZ3Solver;
import esdl.solver.buddy: CstBuddySolver;
import esdl.rand.vecx: CstVector, CstVecArr;
import esdl.rand.domain: CstArrLength;

struct Hash
{
  ulong hash;
  
  this (ulong h) nothrow {
    hash = h;
  }
  
  enum uint m = 0x5bd1e995;
  enum uint r = 24;

  void modify (ulong c){
    ulong k = c * m;
    k ^= k >> r;
    hash = (hash * m) ^ (k * m);
  }
  void modify (string s){
    modify(calcHash(s));
  }

  uint calcHash(scope const(char)[] data) @nogc nothrow pure @safe
  {
    return calcHash(cast(const(ubyte)[])data);
  }
  
  uint calcHash(scope const(ubyte)[] data) @nogc nothrow pure @safe
  {
    uint h = cast(uint) data.length;
    while (data.length >= 4)
      {
        uint k = data[3] << 24 | data[2] << 16 | data[1] << 8 | data[0];
        k *= m;
        k ^= k >> r;
        h = (h * m) ^ (k * m);
        data = data[4..$];
      }
    switch (data.length & 3)
      {
      case 3:
        h ^= data[2] << 16;
        goto case;
      case 2:
        h ^= data[1] << 8;
        goto case;
      case 1:
        h ^= data[0];
        h *= m;
        goto default;
      default:
        break;
      }
    h ^= h >> 13;
    h *= m;
    h ^= h >> 15;
    return h;
  }
}

// hash map number keys

// tried to use ascii where possible

// ! -> 33
// : -> 58
// >> -> > -> 62
// ( -> 40
// ) -> 41
//   -> 32
// .. -> . -> 46
// DIST -> d -> 100
// [ -> 91
// ] -> 93
// NOT -> N -> 78
// NEG -> ~ -> 126
// ! INSIDE -> \ -> 92
// INSIDE -> / -> 47
// UNIQUE -> u -> 117
// Visitor: -> v -> 118
// := -> @ -> 64
// :/ -> * -> 42
// V -> 86
// R -> 82
// # -> 35
// U -> 85
// S -> 83
// bool -> 0

class CstPredHandler			// handler of related predicates
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

  void setBatchContext(CstPredicate solvablePred, uint level) {
    solvablePred.setBatchContext(this, level);

    setOrderAndBools();
  }

  void setOrderAndBools() {
    
    import std.algorithm.sorting: sort; 
    
    _softPredicateCount = 0;
    _hasVectorConstraints = false;
    _hasUniqueConstraints = false;
    _hasDistConstraints = false;

    // foreach (pred; _preds) pred._handler = null;
    _preds.reset();
    foreach (pred; sort!((x, y) => x.hashValue() < y.hashValue())(_predList[])) {
      if (pred.isDistPredicate()) this.markDist();
      // pred._handler = this;
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
    string description = "CstPredHandler -- \n";
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

class CstDistPredHandler	// handler of dist and related predicates
{
  void initialize(_esdl__Proxy proxy) {
    _proxy = proxy;
    _preds.reset();

    _distPred = null;
    _state = State.INIT;
  }
  
  Folder!(CstPredicate, "preds") _preds;
  CstPredicate _distPred;

  CstPredicate[] predicates() {
    return _preds[];
  }

  _esdl__Proxy _proxy;

  _esdl__Proxy getProxy() {
    return _proxy;
  }

  void distPred(CstPredicate pred) {
    pred._state = CstPredicate.State.GROUPED;
    _distPred = pred;
  }

  void addPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln(pred.describe());
    pred._state = CstPredicate.State.GROUPED;
    _preds ~= pred;
  }

  public enum State: ubyte
  {   INIT,
      SOLVED
      }

  State _state;
  
  void reset() {
    _state = State.INIT;
    if (_distPred !is null) {
      _distPred = null;
    }
  }

  void markSolved() {
    _state = State.SOLVED;
  }

  bool isSolved() {
    return _state == State.SOLVED;
  }

  void solve() {
    if (_proxy._esdl__debugSolver()) {
      import std.stdio;
      writeln(describe());
    }

    assert (_distPred.isGuardEnabled());
    CstDistSolverBase dist = _distPred._expr.getDist();
    CstDomBase distDomain = _distPred.distDomain();
    dist.reset();
    foreach (wp; _preds) {
      assert (wp.isGuardEnabled());
      if (wp.isGuardEnabled()) {
	// import std.stdio;
	// writeln(wp.describe());
	bool compat = wp._expr.isCompatWithDist(distDomain);
	if (compat is false)
	  assert (false, "can only use != or !inside operator on distributed domains");
	wp._expr.visit(dist);
	wp.markPredSolved();
      }
      else {
	wp.markPredSolved();
      }
    }
    dist.uniform(distDomain, _proxy._esdl__getRandGen());
    _proxy.addSolvedDomain(distDomain);
    _distPred.markPredSolved();


    this.markSolved();

  }
      

  string describe() {
    import std.conv: to;
    string description = "CstDistPredHandler -- \n";
    if (_preds.length > 0) {
      description ~= "  Predicates:\n";
      foreach (pred; _preds) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_distPred !is null) {
      description ~= "  Dist Predicate:\n";
      description ~= "    " ~ _distPred.name() ~ '\n';
    }
    return description;
  }
}

class CstPredicate: CstIterCallback, CstDepCallback, CstDepIntf
{
  string name() {
    import std.conv;
    if (_parent is null) {
      return _constraint.fullName() ~ '/' ~
	(_isGuard ? "guard_" : "pred_") ~
	_statement.to!string() ~ '%' ~ _id.to!string();
    }
    else {
      return _parent.name() ~
	'[' ~ _unrollIterVal.to!string() ~ ']' ~'%' ~ _id.to!string();
    }
  }
  
  string fullName() {
    return name();
  }

  bool isVisitor() {
    return false;
  }

  bool visit(CstSolver solver, bool inv=false) {
    // import std.stdio;
    // writeln ("Visiting: ", fullName());
    assert (_state !is State.BLOCKED);
    if (_guard is null) {
      if (this.isGuard() && _state == State.SOLVED) {
	assert (inv ^ _exprVal, this.fullName());
	return false;
	// import std.stdio;
	// writeln (_exprVal, ": ", inv);
      }
      else {
	_expr.visit(solver);
	if (inv) solver.processEvalStack(CstLogicOp.LOGICNOT);
	return true;
      }
    }
    else {
      assert (this.isGuard() || inv is false);
      bool implication = _guard.visit(solver, _guardInv);
      if (this.isGuard()) {
	if (_state == State.SOLVED) {
	  assert (inv ^ _exprVal);
	  return implication;
	}
	else {
	  _expr.visit(solver);
	  if (inv) solver.processEvalStack(CstLogicOp.LOGICNOT);
	  solver.processEvalStack(CstLogicOp.LOGICAND);
	  return true;
	}
      }
      else {
	_expr.visit(solver);
	if (implication) solver.processEvalStack(CstLogicOp.LOGICIMP);
	return true;
      }
    }
  }
  // alias _expr this;

  enum State: byte { NONE, INIT, RESOLVED, UNROLLED, BLOCKED, COLLATED, GROUPED, SOLVED }

  bool isResolved() {
    return _state == State.RESOLVED;
  }

  void markResolved() {
    import std.conv: to;
    assert (_state == State.BLOCKED || _state == State.UNROLLED ||
	    _state == State.INIT, _state.to!string());
    if (_state == State.INIT) {
      _state = State.RESOLVED;
    }
  }

  final bool isUnrolled() {
    return _state == State.UNROLLED;
  }
  
  final bool isGrouped() {
    return _state == State.GROUPED;
  }
  
  // returns true if the only domain for this predicate
  // is a dist domain
  bool hasOnlyDistDomain() {
    return _distDomain !is null || (_domain !is null && _domain.getDistPred() !is null);
  }

  bool isCompatWithDist(CstDomBase distDom) {
    if (isBlocked()) return false;
    foreach (rnd; _resolvedRnds) {
      if (rnd.isSolved() || rnd is distDom) continue;
      else return false;
    }
    foreach (rndArr; _resolvedRndArrs) {
      foreach (rnd; rndArr[]) {
	if (rnd.isSolved()) continue;
	else return false;
      }
    }
    return _expr.isCompatWithDist(distDom);
  }
  
  _esdl__ConstraintBase _constraint;
  uint _statement;
  bool _domainContextSet;

  immutable bool _isLambdaPred = false;
  immutable bool _isVisitorPred = false;

  final bool isLambdaPred() { return _isLambdaPred; }
  final bool isVisitorPred() { return _isVisitorPred; }

  _esdl__Proxy _proxy;
  CstScope _scope;
  CstLogicTerm _expr;
  CstPredicate _parent;
  CstPredicate _guard;

  bool _isGuard;

  bool isGuard() { return _isGuard; }

  bool _guardInv;
  bool guardInv() { return _guardInv; }

  
  // List of dependent predicates that this guard may block
  // This can be set once in the setDomainContext
  Folder!(CstPredicate, "depPreds") _depPreds;

  void addDepPred(CstPredicate dep) {
    _depPreds ~= dep;
  }
    
  bool isGuardEnabled() {
    if (_guard is null) return true;
    else {
      assert (_guard._state == State.SOLVED);
      return _guard._exprVal ^ _guardInv;
    }
  }
  
  // When urolling, disable the previously unrolled constraints
  // if not required -- if the length is less now
  bool _isInRange = true;

  bool isEnabled() {
    if (_parent is null)
      return _constraint.isEnabled() && isInRange() && _proxy.isRand();
    else return _constraint.isEnabled() && isInRange() && _proxy.isRand() && _parent.isEnabled();
  }

  bool isInRange() {
    if (_parent is null) return _isInRange;
    else return _isInRange && _parent.isInRange();
  }

  bool isCollated() {
    return _state == State.COLLATED;
  }
  
  bool isBlocked() {
    return _state == State.BLOCKED;
  }
  
  uint _level;
  uint _unrollCycle;
  bool _markResolve = true;

  CstVectorOp _vectorOp = CstVectorOp.NONE;
  bool _uniqueFlag = false;
  void setUniqueFlag() { _uniqueFlag = true; }
  uint _soft = 0;

  uint getSoftWeight() { return _soft; }

  State _state = State.INIT;

  void reset() {
    _state = State.INIT;
  }

  void initialize() {
    _state = State.INIT;
    _depCbs.reset();
    _resolvedDepsCount = 0;
  }

  Folder!(CstPredicate, "uwPreds") _uwPreds;
  size_t _uwLength;
  
  __gshared uint _count;
  immutable uint _id;

  this(_esdl__ConstraintBase cst, CstPredicate guard, bool guardInv,
       uint stmt, _esdl__Proxy proxy, uint soft, CstLogicTerm expr,
       bool isGuard, CstPredicate parent=null,
       CstIterator unrollIter=null, uint unrollIterVal=0 // ,
       // CstIterator[] iters ...
       ) {
    _isLambdaPred = cst.isLambdaConstraint();
    _isVisitorPred = cst.isVisitorConstraint();
    synchronized (typeid(CstPredicate)) {
      _id = _count++;
    }
    assert(proxy !is null);
    _constraint = cst;
    _guard = guard;
    _guardInv = guardInv,
    _soft = soft;
    _statement = stmt;
    _proxy = proxy;
    _unrollIterVal = unrollIterVal;
    _isInRange = true;
    if (parent is null) {
      _scope = _proxy.currentScope();
      _level = 0;
    }
    else {
      _scope = parent._scope;
      _level = parent._level + 1;
    }
    assert(_scope !is null);
    _expr = expr;

    _isGuard = isGuard;

    _parent = parent;
    
    if (_parent is null) {
      _scope.getIterators(_parsedIters, _level);
    }
    else {
      _parsedIters.reset();
      foreach (iter; _parent._iters[1..$].map!(tr =>
					       tr.unrollIterator(unrollIter,
								 unrollIterVal))) {
	_parsedIters ~= iter;
      }
    }
      
    _expr.setDistPredContext(this);
    
    // doDetDomainContext is now being called on the newly unrolled predicates
    // using procUnrolledNewPredicates method in the proxy
    // if (parent !is null) this.doSetDomainContext(this); // unrolled
    makeHash();
    // import std.stdio;
    // writeln(this.describe());
    debug(CSTPREDS) {
      import std.stdio;
      stdout.writeln(this.describe());
    }
  }

  _esdl__Proxy getProxy()() {
    assert(_proxy !is null);
    return _proxy;
  }

  void doResolve() {
    if (_iters.length == 0) {
      _resolvedDepsCount += 1;
      _markResolve = true;
      checkResolved();
      // if (this.isGuard() && this.checkResolved())
      // 	this.procResolvedGuard();
    }
  }

  void doUnroll() {
    if (_state == State.BLOCKED) return;
    import std.conv: to;
    bool guardUnrolled = false;
    if (_unrollCycle == _proxy._cycle) { // already executed
      return;
    }

    // _proxy.registerUnrolled(this);
    assert (_state != State.UNROLLED,
	    "Predicate: " ~ fullName() ~ " in unexpected state: " ~ _state.to!string());
    _state = State.UNROLLED;
    // check if all the dependencies are resolved
    // foreach (dep; _deps) {
    //   if (! dep.isSolved()) {
    // 	return;
    //   }
    // }
    CstIterator iter = _iters[0];

    if (_guard !is null && _guard._iters.length > 0 &&
	_guard._iters[0] is iter) {
      _guard.doUnroll();
      guardUnrolled = true;
    }
    
    if (iter.getLenVec().isSolved()) {
      this.unroll(iter, guardUnrolled);
      _unrollCycle = _proxy._cycle;
    }

    _proxy.procUnrolledNewPredicates();
  }

  uint _currLen;
  
  void unroll(CstIterator iter, bool guardUnrolled) {
    assert (iter is _iters[0]);

    if (! iter.isUnrollable()) {
      assert(false, "CstIterator is not unrollabe yet: "
	     ~ this.describe());
    }

    auto prevLen = _currLen;
    _currLen = cast(uint) iter.size();
    auto builtLen = _uwPreds.length;
    // import std.stdio;
    // writeln("size is ", _currLen);

    if (_uwPreds.length < _currLen) _uwPreds.length = _currLen;
    
    for (uint i=0; i != _uwPreds.length; ++i) {
      if (i < _currLen) {
	if (i >= builtLen) {
	  CstPredicate uwPred = _uwPreds[i];
	  assert (uwPred is null);
	  CstPredicate guard = _guard;
	  if (guardUnrolled) guard = _guard._uwPreds[i];
	  uwPred = new CstPredicate(_constraint, guard, _guardInv, _statement,
				    _proxy, _soft, _expr.unroll(iter, iter.mapIter(i)),
				    _isGuard, this, iter, i// ,
				    // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
				    );
	  uwPred._unrolledIters ~= this._unrolledIters[];
	  uwPred._unrolledIters ~= iter;
	  _uwPreds[i] = uwPred;
	  _proxy.addUnrolledNewPredicate(uwPred);
	}
	else if (i >= prevLen) {
	  _uwPreds[i]._isInRange = true;
	}
	_proxy.addNewPredicate(_uwPreds[i]);
      }
      else {
	_uwPreds[i]._isInRange = false;
      }
    }
  }

  uint _resolvedDepsCount = 0;
  
  final bool checkResolved(bool init_=false) {
    // if (_markResolve || init_) {
    if (_resolvedDepsCount == _deps.length) {
      _markResolve = false;
      bool resolved = true;
      foreach (dep; _deps) {
	if (! dep.isDepResolved()) {
	  resolved = false;
	  break;
	}
      }
      if (resolved) {
	import std.conv: to;
	assert (_resolvedDepsCount == _deps.length, "Predicate: " ~ fullName() ~ " -- " ~
		_resolvedDepsCount.to!string ~ " != " ~ _deps.length.to!string() ~
		" _markResolve: " ~ _markResolve.to!string() ~ " init_: " ~ init_.to!string());
	if (isGuard()) procResolvedGuard();
	else processResolved();
      }
      return resolved;
    }
    return false;
  }

  // Excl. Conds -- The special case of mono and dist preds
  CstDomBase _domain;	    	// would be null if multiple domains
  CstDomBase getDom() {
    return _domain;
  }
  
  Folder!(CstDomBase, "unresolvedRnds") _unresolvedRnds;
  Folder!(CstDomBase, "distRnds") _distRnds;	// temporary folder used in expr.d
  void addUnresolvedRnd(CstDomBase rnd,
	      DomainContextEnum context=DomainContextEnum.DEFAULT) {
    // A guard should on store its own rands as deps
    // should ignore the nested guards
    if (this.isGuard()) {
      if (this._isCurrentContext) this.addDep(rnd);
      return;
    }

    final switch (context) {
    case DomainContextEnum.DEFAULT: if (! _unresolvedRnds[].canFind(rnd)) _unresolvedRnds ~= rnd;
      break;
    case DomainContextEnum.DIST: if (! _distRnds[].canFind(rnd)) _distRnds ~= rnd;
      break;
    case DomainContextEnum.INDEX: if (! _idxs[].canFind(rnd)) _idxs ~= rnd;
      break;
    case DomainContextEnum.BITINDEX: if (! _bitIdxs[].canFind(rnd)) _bitIdxs ~= rnd;
      break;
    }
  }

  Folder!(CstDomBase, "resolvedRnds") _resolvedRnds;
  void addResolvedRnd(CstDomBase rnd) {
    if (! _resolvedRnds[].canFind(rnd)) _resolvedRnds ~= rnd;
  }

  Folder!(CstDomSet, "unrosolvedRndArrs") _unresolvedRndArrs;
  void addUnresolvedRndArr(CstDomSet rndArr,
		 DomainContextEnum context=DomainContextEnum.DEFAULT) {
    if (this.isGuard()) {
      if (this._isCurrentContext) this.addDep(rndArr);
      return;
    }
    assert (context == DomainContextEnum.DEFAULT);
    if (! _unresolvedRndArrs[].canFind(rndArr)) _unresolvedRndArrs ~= rndArr;
  }

  Folder!(CstDomSet, "resolvedRndArrs") _resolvedRndArrs;
  void addResolvedRndArr(CstDomSet rdn) {
    if (! _resolvedRndArrs[].canFind(rdn)) _resolvedRndArrs ~= rdn;
  }

  Folder!(CstDomBase, "unrosolvedVars") _unresolvedVars;
  void addVar(CstDomBase var,
	      DomainContextEnum context=DomainContextEnum.DEFAULT) {
    final switch (context) {
    case DomainContextEnum.DEFAULT, DomainContextEnum.DIST:
      if (! _unresolvedVars[].canFind(var)) _unresolvedVars ~= var;
      break;
    case DomainContextEnum.INDEX: if (! _idxs[].canFind(var)) _idxs ~= var;
      break;
    case DomainContextEnum.BITINDEX: if (! _bitIdxs[].canFind(var)) _bitIdxs ~= var;
      break;
    }
  }

  Folder!(CstDomBase, "resolvedVars") _resolvedVars;
  void addResolvedVar(CstDomBase var) {
    if (! _resolvedVars[].canFind(var)) _resolvedVars ~= var;
  }

  Folder!(CstDomSet, "unresolvedVarArrs") _unresolvedVarArrs;
  void addVarArr(CstDomSet varArr,
		 DomainContextEnum context=DomainContextEnum.DEFAULT) {
    // assert (context == DomainContextEnum.DEFAULT);
    if (! _unresolvedVarArrs[].canFind(varArr)) _unresolvedVarArrs ~= varArr;
  }

  Folder!(CstDomSet, "resolvedVarArrs") _resolvedVarArrs;
  void addResolvedVarArr(CstDomSet rdn) {
    if (! _resolvedVarArrs[].canFind(rdn)) _resolvedVarArrs ~= rdn;
  }

  // all the dist domains that this predicate is associated with
  // There could be multiple such domains
  Folder!(CstDomBase, "dists") _dists;
  void addDist(CstDomBase dist,
	      DomainContextEnum context=DomainContextEnum.DEFAULT) {
    if (! _dists[].canFind(dist)) _dists ~= dist;
  }
  Folder!(CstValue, "vals")  _vals;
  void addVal(CstValue val,
	      DomainContextEnum context=DomainContextEnum.DEFAULT) {
    if (! _vals[].canFind(val)) _vals ~= val;
  }
  Folder!(CstDepIntf, "deps") _deps;
  void addDep(CstDepIntf dep,
	      DomainContextEnum context=DomainContextEnum.DEFAULT) {
    if (! _deps[].canFind(dep)) _deps ~= dep;
  }
  Folder!(CstDepIntf, "idxs") _idxs;
  void addIdx(CstDepIntf idx,
	      DomainContextEnum context=DomainContextEnum.DEFAULT) {
    if (! _idxs[].canFind(idx)) _idxs ~= idx;
  }
  Folder!(CstDomBase, "bitIdxs") _bitIdxs;
  void addBitIdx(CstDomBase bitIdx,
		 DomainContextEnum context=DomainContextEnum.DEFAULT) {
    if (! _bitIdxs[].canFind(bitIdx)) _bitIdxs ~= bitIdx;
  }
  Folder!(CstIterator, "iters") _iters;
  void addIter(CstIterator iter,
	       DomainContextEnum context=DomainContextEnum.DEFAULT) {
    // if (! _iters[].canFind(iter))
    _iters ~= iter;
  }
  Folder!(CstIterator, "parsedIters") _parsedIters;
  void addParsedIter(CstIterator parsedIter,
		     DomainContextEnum context=DomainContextEnum.DEFAULT) {
    // if (! _parsedIters[].canFind(parsedIter))
    _parsedIters ~= parsedIter;
  }
  Folder!(CstIterator, "varIters") _varIters;
  void addVarIter(CstIterator varIter,
		  DomainContextEnum context=DomainContextEnum.DEFAULT) {
    // if (! _varIters[].canFind(varIter))
    _varIters ~= varIter;
  }

  // For the predicates that have been created by unrolling,
  // keep track of the iterators unrolled
  Folder!(CstIterator, "unrolledIters") _unrolledIters;
  
  CstIterator _unrollIter;
  uint _unrollIterVal;

  uint _unresolveLap;

  final CstDomBase[] getUnresolvedRnds() {
    return _unresolvedRnds[];
  }

  final CstDomSet[] getUnresolvedRndArrs(){
    return _unresolvedRndArrs[];
  }

  final CstDomBase[] getUnresolvedVars() {
    return _unresolvedVars[];
  }

  final CstDomSet[] getUnresolvedVarArrs() {
    return _unresolvedVarArrs[];
  }

  final CstValue[] getVals() {
    return _vals[];
  }

  final CstDomBase[] getRnds() {
    return _resolvedRnds[];
  }

  final CstDomSet[] getRndArrs() {
    return _resolvedRndArrs[];
  }

  final CstDomBase[] getVars() {
    return _resolvedVars[];
  }

  final CstDomSet[] getVarArrs() {
    return _resolvedVarArrs[];
  }

  void processResolved() {
    _resolvedRnds.reset();
    _resolvedVars.reset();
    _resolvedRndArrs.reset();
    _resolvedVarArrs.reset();

    foreach (rnd; _unresolvedRnds) {
      CstDomBase resolved = rnd.getResolvedNode();
      if (resolved.isRand()) {
	addResolvedRnd(resolved);
	resolved.addResolvedPred(this);
      }
      else addResolvedVar(resolved);
    }
    
    foreach (rnd; _unresolvedRndArrs) {
      CstDomSet resolved = rnd.getResolvedNode();
      if (resolved.isRand()) {
	addResolvedRndArr(resolved);
	resolved.addResolvedPred(this);
      }
      else addResolvedVarArr(resolved);
    }
    
    foreach (rnd; _unresolvedVars) {
      addResolvedVar(rnd.getResolvedNode());
    }
    
    foreach (rnd; _unresolvedVarArrs) {
      addResolvedVarArr(rnd.getResolvedNode());
    }
    
  }

  final void markAsUnresolved(uint lap) {
    if (_unresolveLap != lap) {	 // already marked -- avoid infinite recursion
      _unresolveLap = lap;
      foreach (rnd; _unresolvedRnds) rnd.markAsUnresolved(lap);
      foreach (rndArr; _unresolvedRndArrs) rndArr.markAsUnresolved(lap, true);
    }
  }

  final bool isMarkedUnresolved(uint lap) {
    if (_parent !is null) {
      if (_parent.isMarkedUnresolved(lap)) {
	return true;
      }
    }
    return (_unresolveLap == lap);
  }

  // final bool markIfUnresolved(uint lap) {
  //   if (_deps.length > 0 || _iter !is null) {
  //     this.markAsUnresolved(lap);
  //     return true;
  //   }
  //   return false;
  // }

  final bool isRolled() {
    if (_unrollCycle != _proxy._cycle && _state != State.BLOCKED) {
      assert (this._iters.length > 0 && _state == State.INIT);
      return true;
    }
    return false;
  }

  // No longer required -- Taken care of by _state (UNROLLED)
  // used by setBatchContext to find if the predicate has been unrolled and
  // therefor it should not be considered for grouping
  // final bool hasUnrolled() {
  //   if (this._iters.length == 0 ||
  // 	_unrollCycle != _proxy._cycle) {
  //     return false;
  //   }
  //   return true;
  // }
  
  final bool hasDeps() {
    return this._deps.length > 0;
  }

  final bool solvable() {
    return _deps.length == 0 && _iters.length == 0;
  }
  
  // A temporary context useful only for setDomainContext
  // it is either null or points to the guard predicate that is
  // currently being processed
  bool _isCurrentContext;

  final void doSetDomainContext(CstPredicate pred) {
    if (pred is this) {
      if (_domainContextSet) return;
      else _domainContextSet = true;
    }

    _isCurrentContext = true;
    scope (exit) _isCurrentContext = false;
    
    // make sure that the doSetDomainContext has already
    // processed the guards, if any
    assert (_guard is null || _guard._domainContextSet is true);

    if (pred is this)
      _expr.setDomainContext(pred, DomainContextEnum.DEFAULT);
    else {
      // When looking at guards of predicates involving dist domains
      // we just need to add the guard in the dependency list
      if (pred.hasOnlyDistDomain()) pred.addDep(this);
      // otherwise for normal predicates, process the guard expression
      // normally
      else _expr.setDomainContext(pred, DomainContextEnum.DEFAULT);
    }

    if (pred._dists.length > 0) {
      if (pred is this && pred._dists.length == 1 &&
	  _unresolvedRnds.length == 0 && _unresolvedRndArrs.length == 0) {
	// we are either dealing with a dist predicate itself or
	// we have ancountered a predicate of the form a != b or a !inside []
	// where a is a dist domain
	assert (pred._dists[0].getDistPred() !is null);
	pred.addUnresolvedRnd(pred._dists[0]);
      }
      else {
	foreach (dist; pred._dists) {
	  pred.addVar(dist);
	  pred.addDep(dist);
	}
      }
      pred._dists.reset();
    }
      

    if (pred is this && _unresolvedRnds.length == 1 &&
	_unresolvedRndArrs.length == 0)
      _domain = _unresolvedRnds[0];

    if (_guard !is null) {
      // guard will enroll the predicate and will block or enable it
      // when triggered
      if (pred is this) _guard.addDepPred(this);
      _guard.doSetDomainContext(pred);
    }

    if (pred is this) {
    
      foreach (rnd; _unresolvedRnds) rnd.registerRndPred(this);
      foreach (rnd; _unresolvedRndArrs) rnd.registerRndPred(this);

      foreach (idx; _idxs) // if (! idx.isSolved())
	addDep(idx);
      foreach (idx; _bitIdxs) // if (! idx.isSolved())
	addDep(idx);
    
      // foreach (dep; _deps) dep.registerDepPred(this);

      // For now treat _idxs as _deps since _idxs are merged with _deps
      // foreach (idx; _idxs) idx.registerIdxPred(this);

      // take only the parsed iterators that are found in the expression
      // as well
      // _iters = pasredIters.filter!(itr =>
      // 				 canFind(varIters, itr)).array;
      _iters.reset();
      if (isVisitor()) {
	_iters.swap(_varIters);
      }
      else {
	foreach (iter; _parsedIters[].filter!(itr =>
					      canFind!((CstIterator a, CstIterator b) => a == b)
					      (_varIters[], itr))) {
	  _iters ~= iter;
	}
      }
    
      // Now being done in proxy.d
      // if (_iters.length != 0) _iters[0].registerRolled(this);
    }
  }

  void procDependency(CstDepIntf dep) {
    // import std.stdio;
    // writeln("Removing dep from rnds: ", dep.name());
    CstDomBase dom = cast (CstDomBase) dep;
    if (dom !is null) {
      auto index = countUntil(_unresolvedRnds[], dep);
      if (index >= 0) {
	_unresolvedRnds[index] = _unresolvedRnds[$-1];
	_unresolvedRnds.length = _unresolvedRnds.length - 1;
	_unresolvedVars ~= dom;
	dom.purgeRndPred(this);
      }
    }
    if (_guard !is null) _guard.procDependency(dep);
  }
  
  void doProcDomainContext() {
    import std.algorithm.searching: canFind;
    foreach (rnd; _unresolvedRnds) {
      foreach (dep; rnd.getDeps()) {
	if (! _deps[].canFind(dep)) _deps ~= dep;
      }
    }
    foreach (rnd; _unresolvedRndArrs) {
      foreach (dep; rnd.getDeps()) {
	if (! _deps[].canFind(dep)) _deps ~= dep;
      }
    }
    if (! isVisitor())
      foreach (dep; _deps) this.procDependency(dep);
  }

  CstLogicTerm getExpr() {
    return _expr;
  }

  bool tryResolveAllDeps(_esdl__Proxy proxy) {
    bool resolved = true;
    // import std.stdio;
    // writeln("pred: ", fullName());
    foreach (dep; _deps) {
      // writeln("dep: ", dep.fullName());
      if (dep.tryResolveDep(proxy)) {
	// writeln("resolved: ", dep.fullName());
	_resolvedDepsCount += 1;
      }
      else {
	// writeln("cb: ", dep.fullName());
	dep.registerDepPred(this);
	resolved = false;
      }
    }
    return resolved;
  }

  bool _exprVal;
  final void procResolvedGuard() {
    assert (this.isGuard());
    _state = State.SOLVED;
    _exprVal = _expr.eval();
    foreach (pred; _depPreds) {
      pred.block(_exprVal);
    }
  }

  void block(bool flag) {
    if (! (flag ^ _guardInv)) block();
  }
  
  void block() {
    // import std.stdio;
    // writeln ("Blocking: ", fullName());
    this._state = State.BLOCKED;
    foreach (pred; _depPreds) pred.block();
  }
  
  bool hasUpdate() {
    foreach (var; _resolvedVars) {
      if (var.hasChanged()) {
	return true;
      }
    }
    foreach (idx; _idxs) {
      if (idx.hasChanged()) {
	return true;
      }
    }
    return false;
  }

  string describe() {
    import std.string:format;
    import std.conv: to;
    string description = "Predicate Name: " ~ name() ~ "\n";
    description ~= "Predicate ID: " ~ _id.to!string() ~ "\n    ";
    description ~= "State: " ~ _state.to!string() ~ "\n    ";
    description ~= "Is In Range? " ~ _isInRange.to!string ~ "\n    ";
    description ~= "Expr: " ~ _expr.describe() ~ "\n    ";
    description ~= "Context Set? " ~ _domainContextSet.to!string() ~ "\n    ";
    description ~= _scope.describe();
    description ~= format("    Level: %s\n", _level);
    if (_iters.length > 0) {
      description ~= "    Iterators: \n";
      foreach (iter; _iters) {
	description ~= "\t" ~ iter.fullName() ~ "\n";
      }
    }
    if (_unrolledIters.length > 0) {
      description ~= "    Unrolled Iterators: \n";
      foreach (iter; _unrolledIters) {
	description ~= "\t" ~ iter.fullName() ~ "\n";
      }
    }
    if (_unresolvedRnds.length > 0) {
      description ~= "    Domains: \n";
      foreach (rnd; _unresolvedRnds) {
	description ~= "\t" ~ rnd.fullName() ~ "\n";
      }
    }
    if (_resolvedRnds.length > 0) {
      description ~= "    Resolved Domains: \n";
      foreach (rnd; _resolvedRnds) {
	description ~= "\t" ~ rnd.fullName() ~ "\n";
      }
    }
    if (_unresolvedVars.length > 0) {
      description ~= "    Variables: \n";
      foreach (var; _unresolvedVars) {
	description ~= "\t" ~ var.fullName() ~ "\n";
      }
    }
    if (_resolvedVars.length > 0) {
      description ~= "    Resolved Variables: \n";
      foreach (var; _resolvedVars) {
	description ~= "\t" ~ var.fullName() ~ "\n";
      }
    }
    if (_vals.length > 0) {
      description ~= "    Values: \n";
      foreach (val; _vals) {
	description ~= "\t" ~ val.describe() ~ "\n";
      }
    }
    if (_idxs.length > 0) {
      description ~= "    Indexes: \n";
      foreach (idx; _idxs) {
	description ~= "\t" ~ idx.fullName() ~ "\n";
      }
    }
    if (_bitIdxs.length > 0) {
      description ~= "    Bit Indexes: \n";
      foreach (idx; _bitIdxs) {
	description ~= "\t" ~ idx.fullName() ~ "\n";
      }
    }
    if (_deps.length > 0) {
      description ~= "    Depends on: \n";
      foreach (dep; _deps) {
	description ~= "\t" ~ dep.fullName() ~ "\n";
      }
    }
    if (_depPreds.length > 0) {
      description ~= "    Gated Predicates: \n";
      foreach (dep; _depPreds) {
	description ~= "\t" ~ dep.fullName() ~ "\n";
      }
    }
    description ~= "\n";
    return description;
  }

  // CstPredHandler _handler;

  // CstPredHandler handler() {
  //   return _handler;
  // }

  void setProxyContext(_esdl__Proxy proxy){
    // import std.stdio;
    // writeln("setProxyContext: ", this.describe());

    foreach (dom; _resolvedRnds) {
      if (! dom.inRange()) {
	// import std.stdio;
	// writeln(this.describe());
	// writeln(_guard.describe());
	if (_guard is null || _guard._expr.eval()) {
	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
	}
	_state = State.BLOCKED;
	return;
      }
    }

    foreach (dom; _resolvedVars) {
      if (! dom.inRange()) {
	// import std.stdio;
	// writeln(this.describe());
	// writeln(_guard.describe());
	if (_guard is null || _guard._expr.eval()) {
	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
	}
	_state = State.BLOCKED;
	return;
      }
    }
    proxy.collatePredicate(this);

    foreach (dom; _resolvedRnds) {
      if (dom._state is CstDomBase.State.INIT && (! dom.isSolved())) {
	dom.setProxyContext(proxy);
      }
    }
    foreach (arr; _resolvedRndArrs) {
      if (arr._state is CstDomSet.State.INIT && arr.isRand()) {
	arr.setProxyContext(proxy);
      }
    }
  }

  void setBatchContext(CstPredHandler handler, uint level) {
    if (this.isBlocked()) return;
    
    assert(getOrderLevel() == level - 1, "unexpected error in solving before constraints");
      
    foreach (dom; _resolvedRnds) {
      assert(dom.getOrderLevel() != level, "unexpected error in solving before constraints");
      if (dom.getOrderLevel < level - 1){
	assert(dom.isSolved(), "unexpected error in solving before constraints");
      }
    } 
    
    sendPredToHandler(handler);
    
    foreach (dom; _resolvedRnds) {
      if (dom._state is CstDomBase.State.COLLATED && (! dom.isSolved())) {
	dom.setBatchContext(handler, level);
      }
    }
    foreach (arr; _resolvedRndArrs) {
      if (arr._state is CstDomSet.State.COLLATED // && (! arr.isSolved())
	  ) {
	arr.setBatchContext(handler, level);
      }
    }
  }

  void sendPredToHandler(CstPredHandler handler){
    _state = State.GROUPED;
    
    if (this.isDistPredicate()) {
      assert (handler.hasDistConstraints());
      if (this.isGuardEnabled()) {
  	if (handler._distPred !is null) {
  	  assert (false,
  		  "It is illegal to have more than one dist predicate active on the same domain");
  	}
  	handler._distPred = this;
      }
      else {
  	handler.addPredicate(this);
      }
    }
    else {
      assert (! this.isGuard());
      handler.addPredicate(this);
    }
    
  }

  void annotate(CstPredHandler handler) {
    if (_guard !is null) {
      if (_guard._state is State.SOLVED) {
	assert (_guard._exprVal ^ _guardInv);
      }
      else {
	_guard.annotate(handler);
      }
    }
    _expr.annotate(handler);
  }

  void writeSignature(ref _esdl__Sigbuf str, CstPredHandler handler) {
    import std.format: sformat;
    if (_soft != 0) {
      char[16] buff;
      str ~= '!';
      str ~=  sformat(buff[], "%d", _soft); // _soft.to!string();
      str ~= ':';
    }
    if (_guard !is null) {
      if (_guard._state is State.SOLVED) {
	assert (_guard._exprVal ^ _guardInv);
      }
      else {
	if (_guardInv) str ~= " ! ";
	_guard.writeSignature(str, handler);
	str ~= " >> ";
      }
    }
    _expr.writeExprString(str);
  }

  void calcHash(ref Hash hash){
    hash.modify(33);
    hash.modify(_soft);
    hash.modify(58);
    if (_guard !is null) {
      _guard.calcHash(hash);
      if (_guardInv) hash.modify(33);
      hash.modify(62);
    }
    _expr.calcHash(hash);
  }
  
  Hash _hash;
  ulong hashValue() {
    return _hash.hash;
  }
  void makeHash(){
    _hash = Hash(0);
    _hash.modify(_soft);
    if (_guard !is null) {
      _guard.makeHash();
      if (_guardInv) _hash.modify(33);
      _hash.modify(_guard.hashValue());
    }
    _expr.makeHash();
    _hash.modify(_expr.hashValue());
  }
  
  bool isDistPredicate() { return _distDomain !is null; }
  CstDomBase _distDomain;
  void distDomain(CstDomBase vec) {
    assert (_distDomain is null);
    _distDomain = vec;
  }
  CstDomBase distDomain() {
    return _distDomain;
  }

  void markPredSolved() {
    import std.conv: to;
    // import std.stdio;
    // writeln("marking predicate solved: ", describe());
    assert (this.isGuard() || this.isVisitor() ||
	    _state == State.GROUPED || _state == State.BLOCKED,
	    "State is: " ~ _state.to!string());
    _state = State.SOLVED;

    this.execDepCbs();
  }

  bool tryResolveFixed(_esdl__Proxy proxy) {
    assert (isGuard());
    if (_unresolvedRnds.length > 0 || _unresolvedVars.length > 0) return false;
    else return tryResolveDep(proxy);
  }
  
  bool tryResolveDep(_esdl__Proxy proxy) {
    assert (isGuard());
    if (_unresolvedVarArrs.length > 0 ||
	_unresolvedRndArrs.length > 0) return false;
    else {
      bool success = true;
      foreach (rnd; _unresolvedRnds) {
	if (! rnd.tryResolveDep(proxy)) {
	  success = false;
	}
      }
      if (success) {
	this.markPredSolved();
	proxy.solvedSome();
      }
      return success;
    }
  }
  
  bool isDepResolved() {
    return isSolved();
  }

  bool isSolved() {
    return (_state == State.SOLVED);
  }

  Folder!(CstDepCallback, "depCbs") _depCbs;

  void registerDepPred(CstDepCallback depCb) {
    // if (! _depCbs[].canFind(depCb))
    _depCbs ~= depCb;
  }

  void registerIdxPred(CstDepCallback depCb) {
    assert (false);
  }

  bool hasChanged() {
    assert (false);
  }

  void execDepCbs() {
    foreach (cb; _depCbs) {
      cb.doResolve();
    }
  }

  CstDomBase getDomain() { return null; }

  uint _orderLevel = 0;

  uint getOrderLevel(){
    return _orderLevel;
  }
  
  void setOrderLevel(uint level){
    _orderLevel = level;
  }
  
}

class CstVisitorPredicate: CstPredicate
{
  this(_esdl__ConstraintBase cst, CstPredicate guard, bool guardInv, uint stmt,
       _esdl__Proxy proxy, uint soft, CstLogicTerm expr, bool isGuard, CstPredicate parent=null,
       CstIterator unrollIter=null, uint unrollIterVal=0// ,
       // CstIterator[] iters ...
       ) {
    assert (guard is null);
    // import std.stdio;
    // writeln("Creating a visitor predicate: ", cst.name());
    super(cst, guard, guardInv, stmt, proxy, soft, expr, isGuard, parent, unrollIter, unrollIterVal);
  }

  override bool isVisitor() {
    return true;
  }

  override void unroll(CstIterator iter, bool guardUnrolled) {
    // import std.stdio;
    // writeln("Unrolling Visitor");
    assert (iter is _iters[0]);

    if (! iter.isUnrollable()) {
      assert (false, "CstIterator is not unrollabe yet: "
	      ~ this.describe());
    }
    auto currLen = iter.size();
    auto prevLen = _uwPreds.length;
    // import std.stdio;
    // writeln("size is ", currLen);

    if (currLen > prevLen) {
      // import std.stdio;
      // writeln("Need to unroll ", currLen - _uwPreds.length, " times");
      for (uint i = cast(uint) _uwPreds.length; i != currLen; ++i) {
	// import std.stdio;
	// writeln("i: ", i, " mapped: ", iter.mapIter(i));
	CstVisitorPredicate uwPred =
	  new CstVisitorPredicate(_constraint, _guard, _guardInv, _statement, _proxy, _soft,
				  _expr.unroll(iter, iter.mapIter(i)), false, this, iter, i// ,
				  // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
				  );
	uwPred._unrolledIters ~= this._unrolledIters[];
	uwPred._unrolledIters ~= iter;
	_uwPreds ~= uwPred;
      }
      for (size_t i=prevLen; i!=currLen; ++i) {
	_uwPreds[i].doSetDomainContext(_uwPreds[i]);
      }
    }

    // Do not use foreach here since we may have more elements in the
    // array than the current value of currLen
    for (size_t i=0; i!=currLen; ++i) {
      if (_uwPreds[i]._iters.length == 0) { // completely unrolled
	_uwPreds[i]._expr.scan();
	// import std.stdio;
	// writeln("Collecting constraints from: ", _uwPreds[i]._expr.describe());
      }
      else {
	_proxy.addNewPredicate(_uwPreds[i]);
      }
    }

    _uwLength = currLen;
  }
}
