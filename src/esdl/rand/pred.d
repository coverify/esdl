module esdl.rand.pred;

import std.algorithm.sorting: sort;
import std.algorithm.searching: canFind, countUntil;
import std.algorithm: map, filter;
import std.array;
import std.container.array;

import esdl.data.folder;
import esdl.data.charbuf;
import esdl.rand.proxy: _esdl__Proxy, _esdl__ConstraintBase;
import esdl.rand.misc;
import esdl.rand.base: CstDomBase, CstDomSet, CstIterCallback, DomType,
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
  size_t hash;
  
  this (size_t h) nothrow {
    hash = h;
  }
  
  enum uint m = 0x5bd1e995;
  enum uint r = 24;

  void modify (size_t c){
    size_t k = c * m;
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



class CstPredGroup			// group of related predicates
{
  CstMonoSolver!int intMono;
  CstMonoSolver!uint uintMono;
  CstMonoSolver!long longMono;
  CstMonoSolver!ulong ulongMono;

  bool _hasSoftConstraints;
  bool _hasVectorConstraints;
  bool _hasUniqueConstraints;
  bool _hasDistConstraints;

  bool hasSoftConstraints() {
    return _hasSoftConstraints;
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
    _guards.reset();
    _predList.reset();
    _guardList.reset();
    _doms.reset();
    _domArrs.reset();
    _vars.reset();
    _varArrs.reset();

    _hasSoftConstraints = false;
    _hasVectorConstraints = false;
    _hasUniqueConstraints = false;
    _hasDistConstraints = false;

    _distPred = null;
    _solver = null;
    _state = State.INIT;
  }
  
  // List of predicates permanently in this group
  Folder!(CstPredicate, "preds") _preds;
  Folder!(CstPredicate, "guards") _guards;

  CstPredicate _distPred;

  Folder!(CstPredicate, "predList") _predList;
  Folder!(CstPredicate, "guardList") _guardList;

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

  // this(_esdl__Proxy proxy) {
  //   _proxy = proxy;
  // }

  _esdl__Proxy getProxy() {
    return _proxy;
  }

  void addPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln(pred.describe());
    _predList ~= pred;
  }

  void addGuard(CstPredicate pred) {
    _guardList ~= pred;
  }

  Folder!(CstDomBase, "doms") _doms;
  uint addDomain(CstDomBase dom) {
    // import std.stdio;
    // writeln(dom.describe());
    uint index = cast (uint) _doms.length;
    _doms ~= dom;
    return index;
  }

  CstDomBase[] domains() {
    return _doms[];
  }
  
  Folder!(CstDomSet, "domArrs") _domArrs;
  void addDomainArr(CstDomSet domArr) {
    _domArrs ~= domArr;
  }

  CstDomSet[] domainArrs() {
    return _domArrs[];
  }
  
  Folder!(CstDomBase, "vars") _vars;
  uint addVariable(CstDomBase var) {
    uint index = cast (uint) _vars.length;
    _vars ~= var;
    return index;
  }

  CstDomBase[] variables() {
    return _vars[];
  }

  Folder!(CstDomSet, "varArrs") _varArrs;
  void addVariableArr(CstDomSet varArr) {
    _varArrs ~= varArr;
  }

  void setGroupContext(CstPredicate solvablePred, uint level) {
    solvablePred.setGroupContext(this, level);

    setOrderAndBools();
  }

  void setOrderAndBools() {
    
    import std.algorithm.sorting: sort; 
    
    _hasSoftConstraints = false;
    _hasVectorConstraints = false;
    _hasUniqueConstraints = false;
    _hasDistConstraints = false;

    // foreach (pred; _preds) pred._group = null;
    _preds.reset();
    foreach (pred; sort!((x, y) => x.hashValue() < y.hashValue())(_predList[])) {
      if (pred.withDist()) this.markDist();
      // pred._group = this;
      if (pred._soft != 0) _hasSoftConstraints = true;
      if (pred._vectorOp != CstVectorOp.NONE) _hasVectorConstraints = true;
      if (pred._uniqueFlag is true) _hasUniqueConstraints = true;
      _preds ~= pred;
    }
    // foreach (pred; _guards) pred._group = null;
    _guards.reset();
    foreach (pred; sort!((x, y) => x.hashValue() < y.hashValue())(_guardList[])) {
      // pred._group = this;
      _guards ~= pred;
    }
    // if (_distPred !is null) _distPred._group = this;
    
    // for the next cycle
    _predList.reset();
    _guardList.reset();
    
  }

  void setAnnotation() {
    foreach (i, dom; _doms) {
      assert (dom !is null);
      dom.setAnnotation(cast(uint) i);
    }
    foreach (i, dom; _vars) {
      assert (dom !is null);
      dom.setAnnotation(cast(uint) i);
    }
  }

  void annotate() {
    _doms.reset();
    _vars.reset();

    if (_distPred !is null) _distPred.annotate(this);
    foreach (pred; _preds) pred.annotate(this);
  }

  static Charbuf _sig;
  
  string signature() {
    _sig.reset();
    _sig ~= "GROUP:\n";
    foreach (pred; _preds) {
      if (! hasDistConstraints || pred.isGuardEnabled())
	pred.writeSignature(_sig);
    }
    return _sig.toString();
  }

  override size_t toHash() @trusted nothrow {
    import std.exception:assumeWontThrow;
    return assumeWontThrow(getHash());
  }
  
  bool _hasHashBeenCalculated = false;
  
  Hash _hash;
  
  size_t getHash(){
    if (_hasHashBeenCalculated){
      return _hash.hash;
    }
    _hash = Hash(cast(uint) _preds.length);
    foreach (pred; _preds){
      if (! hasDistConstraints || pred.isGuardEnabled())
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

    if (_distPred is null || (! _distPred.distDomain().isRand())) {
      annotate();
      // string sig1 = signature();
      bool monoFlag = false;
      if (!(_hasSoftConstraints || _hasVectorConstraints)) {
	if (_preds.length == 1 && _preds[0].isVisitor()) {
	  // _preds[0]._dom.forceResolve(_proxy);
	  _preds[0]._state = CstPredicate.State.SOLVED;
	  _proxy.addSolvedDomain(_preds[0]._dom);
	  monoFlag = true;
	}
	else if (_doms.length == 1 && (! _doms[0].isBool())) {
	  if (_doms[0].bitcount() < 32) {
	    _solver = intMono;
	  }
	  else if (_doms[0].bitcount == 32) {
	    if(_doms[0].signed()) {
	      _solver = intMono;
	    }
	    else{
	      _solver = uintMono;
	    }
	  }
	  else if (_doms[0].bitcount < 64) {
	    _solver = longMono;
	  }
	  else if (_doms[0].bitcount == 64) {
	    if(_doms[0].signed()) {
	      _solver = longMono;
	    }
	    else {
	      _solver = ulongMono;
	    }
	  }
	  if ( _solver !is null ) {
	    monoFlag = _solver.solve(this);
	  }
	}
      }
      if (!monoFlag){
      
	string sig = signature();
	// assert(sig1 == sig);

	if (_proxy._esdl__debugSolver()) {
	  import std.stdio;
	  writeln(sig);
	}

	CstSolver* solverp = sig in _proxy._solvers;
	// _hasHashBeenCalculated = false;
	// CstSolver* solverp = this in _proxy._solvers;

	if (solverp !is null) {
	  _solver = *solverp;
	  _solver.solve(this);
	}
	else {
	  if (_hasSoftConstraints || _hasVectorConstraints) {
	    if (_proxy._esdl__debugSolver()) {
	      import std.stdio;
	      writeln("Invoking Z3 because of Soft/Vector Constraints");
	      writeln("_preds: ", _preds[]);
	      foreach (pred; _preds) {
		writeln(pred.describe());
	      }
	      writeln(describe());
	    }
	    _solver = new CstZ3Solver(sig, this);
	    _solver.solve(this);
	  }
	  else {
	    uint totalBits;
	    uint domBits;
	    foreach (dom; _doms) {
	      // assert (! dom.isProperDist());
	      uint domBC = dom.bitcount();
	      totalBits += domBC;
	      domBits += domBC;
	    }
	    foreach (var; _vars) totalBits += var.bitcount();
	    if (totalBits > 32 || _hasUniqueConstraints) {
	      if (_proxy._esdl__debugSolver()) {
		import std.stdio;
		writeln("Invoking Z3 because of > 32 bits");
		writeln(describe());
	      }
	      _solver = new CstZ3Solver(sig, this);
	      _solver.solve(this);
	    }
	    else {
	      _solver = new CstBuddySolver(sig, this);
	      _solver.solve(this);
	    }
	  }
	  // _hasHashBeenCalculated = true;
	  // if (_solver !is null) _proxy._solvers[this] = _solver;
	  if (_solver !is null) _proxy._solvers[sig] = _solver;
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
    }
    else {
      assert (_distPred.isGuardEnabled());
      CstDistSolverBase dist = _distPred._expr.getDist();
      CstDomBase distDomain = _distPred.distDomain();
      dist.reset();
      foreach (wp; _preds) {
	if (wp.isGuardEnabled()) {
	  // import std.stdio;
	  // writeln(wp.describe());
	  bool compat = wp._expr.isCompatWithDist(distDomain);
	  if (compat is false) assert (false, "can only use != operator on distributed domains");
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
    }


    foreach (guard; _guards) {
      if (! guard.tryResolve(_proxy)) {
	assert (false, "Unresolved Guard: " ~ guard.name());
      }
      // else {
      // 	import std.stdio;
      // 	writeln("Resolved Guard: ", guard.name());
      // }
    }
    this.markSolved();

    foreach (dom; _doms) dom.setAnnotation(uint.max);
    foreach (dom; _vars) dom.setAnnotation(uint.max);
    
  }
      

  string describe() {
    import std.conv: to;
    string description = "CstPredGroup -- \n";
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
    if (_guards.length > 0) {
      description ~= "  Guards:\n";
      foreach (pred; _guards) {
	description ~= "    " ~ pred.name() ~ '\n';
      }
    }
    if (_hasSoftConstraints) {
      description ~= "  Has Soft Constraints: True\n";
    }
    else {
      description ~= "  Has Soft Constraints: False\n";
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

  void visit(CstSolver solver, bool inv=false) {
    if (_guard is null) {
      _expr.visit(solver);
      if (inv) solver.processEvalStack(CstLogicOp.LOGICNOT);
    }
    else {
      assert (this.isGuard() || inv is false);
      _guard.visit(solver, _guardInv);
      _expr.visit(solver);
      if (inv) solver.processEvalStack(CstLogicOp.LOGICNOT);
      if (this.isGuard()) solver.processEvalStack(CstLogicOp.LOGICAND);
      else                solver.processEvalStack(CstLogicOp.LOGICIMP);
    }
  }
  // alias _expr this;

  enum State: byte { NONE, INIT, UNROLLED, COLLATED, DISABLED, GROUPED, SOLVED }

  bool isUnrolled() {
    return _state == State.UNROLLED;
  }
  

  void hasDistDomain(bool v) {
    _hasDistDomain = v;
  }
  bool hasDistDomain() {
    return _hasDistDomain;
  }

  bool withDist() {
    if (getDom() is null) return false;
    // else {
    //   getDom().isProperDist();
    // }
    return _hasDistDomain || isDist();
  }
  
  _esdl__ConstraintBase _constraint;
  uint _statement;
  bool _hasDistDomain;
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
    
  bool isGuardEnabled() {
    if (_guard is null) return true;
    else {
      auto gv = _guard._expr.eval();
      return gv ^ _guardInv;
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
  
  bool isDisabled() {
    return _state == State.DISABLED;
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
      
    this.setDistPredContext();
    
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
      _markResolve = true;
      return;
    }
  }

  void doUnroll() {
    import std.conv: to;
    bool guardUnrolled = false;
    if (_unrollCycle == _proxy._cycle) { // already executed
      return;
    }

    _proxy.registerUnrolled(this);
    assert (_state != State.UNROLLED,
	    "Unexpected State: " ~ _state.to!string());
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
	  CstPredicate _uwPred = _uwPreds[i];
	  assert (_uwPred is null);
	  CstPredicate guard = _guard;
	  if (guardUnrolled) guard = _guard._uwPreds[i];
	  _uwPred = new CstPredicate(_constraint, guard, _guardInv, _statement,
				     _proxy, _soft, _expr.unroll(iter, iter.mapIter(i)),
				     _isGuard, this, iter, i// ,
				     // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
				     );
	  _uwPreds[i] = _uwPred;
	  _proxy.addUnrolledNewPredicate(_uwPred);
	}
	else if (i >= prevLen) {
	  _uwPreds[i]._isInRange = true;
	}
	_proxy.addUnrolledPredicate(_uwPreds[i]);
      }
      else {
	_uwPreds[i]._isInRange = false;
      }
    }
  }

  final bool depsAreResolved(bool force=false) {
    if (_markResolve || force) {
      _markResolve = false;
      foreach (dep; _deps) {
	if (! dep.isResolved()) {
	  return false;
	}
      }
      // All _idxs are rolled into _deps
      // foreach (idx; _idxs) {
      // 	if (! idx.isSolved()) {
      // 	  return false;
      // 	}
      // }
      if (this.isGuard()) {
	tryResolve(_proxy);
      }
      return true;
    }
    return false;
  }

  // Excl. Conds -- The special case of mono and dist preds
  CstDomBase _dom;	    	// would be null if multiple domains
  CstDomBase getDom() {
    return _dom;
  }
  
  Folder!(CstDomBase, "unresolvedRnds") _unresolvedRnds;
  Folder!(CstDomBase, "distRnds") _distRnds;	// temporary folder used in expr.d
  void addUnresolvedRnd(CstDomBase rnd,
	      DomainContextEnum context=DomainContextEnum.DEFAULT) {
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
	resolved._resolvedDomainPreds ~= this;
      }
      else addResolvedVar(resolved);
    }
    
    foreach (rnd; _unresolvedRndArrs) {
      CstDomSet resolved = rnd.getResolvedNode();
      if (resolved.isRand()) {
	addResolvedRndArr(resolved);
	resolved._resolvedDomainPreds ~= this;
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
    if (this._iters.length > 0 &&
	_unrollCycle != _proxy._cycle) {
      return true;
    }
    return false;
  }

  // No longer required -- Taken care of by _state (UNROLLED)
  // used by setGroupContext to find if the predicate has been unrolled and
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
  
  final void setDistPredContext() {
    _expr.setDistPredContext(this);
  }

  final void doSetDomainContext(CstPredicate pred, bool thisPred=true) {
    if (thisPred) {
      if (_domainContextSet) return;
      else _domainContextSet = true;
    }

    _expr.setDomainContext(pred, DomainContextEnum.DEFAULT);

    if (pred._dists.length > 0) {
      if (thisPred is true && pred._dists.length == 1 &&
	  _unresolvedRnds.length == 0 && _unresolvedRndArrs.length == 0) {
	assert (pred._dists[0].isDist());
	pred._unresolvedRnds ~= pred._dists[0];
      }
      else {
	foreach (dist; pred._dists) {
	  pred.addVar(dist);
	  pred.addDep(dist);
	}
      }
      pred._dists.reset();
    }
      

    if (thisPred && _unresolvedRnds.length == 1 && _unresolvedRndArrs.length == 0)
      _dom = _unresolvedRnds[0];

    // if (this is pred && this.isDist()) {
    //   assert (_unresolvedRnds.length == 1 && _unresolvedRndArrs.length == 0);
    // }

    
    if (_guard !is null) {
      if (_distDomain !is null && thisPred is true) { // processing a dist predicate
	// assert (thisPred is true);
	assert (_dom !is null && _dom == _distDomain);
	pred._deps ~= _guard;
      }
      else if (_dom !is null && _dom.isDist()) {
	// assert (thisPred is true);
	pred._deps ~= _guard;
      }
      else {
	_guard.doSetDomainContext(pred, false);
      }
    }

    if (thisPred) {
    
      // foreach (varIter; varIters) {
      //   import std.stdio;
      //   stdout.writeln("Found Iterator: ", varIter.name());
      // }
      // if (_iters.length > 0) {
      //   _len = _iters[0].getLenVec();
      // }
    
      foreach (rnd; _unresolvedRnds) rnd.registerRndPred(this);
      foreach (rnd; _unresolvedRndArrs) rnd.registerRndPred(this);

      // foreach (var; _unresolvedVars) var.registerVarPred(this);

      if ((! this.isVisitor()) && (! this.isGuard()) && _unresolvedRndArrs.length == 0) {
	// assert (_unresolvedRnds.length != 0, this.describe());
	if (_unresolvedRnds.length > 1) {
	  foreach (rnd; _unresolvedRnds) {
	    rnd._type = DomType.MULTI;
	  }
	}
	else if (! this.isDist()) {
	  if (_unresolvedRnds.length == 1) {
	    auto rnd = _unresolvedRnds[0];
	    if (rnd._type == DomType.TRUEMONO) {
	      if (_unresolvedVars.length > 0) {
		rnd._type = DomType.LAZYMONO;
	      }
	      if (_idxs.length > 0) {
		assert(! rnd.isStatic());
		rnd._type = DomType.INDEXEDMONO;
	      }
	    }
	  }
	}
      }

      // When the parent unrolls, its dependencies would already be take care of
      // if (_parent !is null) {
      //   CstDomBase[] _foundDeps = _deps ~ _idxs;
      //   _deps = _foundDeps.filter!(dep => (! canFind(_parent._deps, dep))).array;
      // }

      foreach (idx; _idxs) if (! idx.isResolved()) addDep(idx);
      foreach (idx; _bitIdxs) if (! idx.isSolved()) addDep(idx);
    
      foreach (dep; _deps) dep.registerDepPred(this);

      // if (this.isGuard()) {
      // 	foreach (dep; _unresolvedRnds) dep.registerDepPred(this);
      // }

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
    
      if (_iters.length != 0) _iters[0].registerRolled(this);
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

  void tryResolveDeps(_esdl__Proxy proxy) {
    foreach (dep; _deps) dep.tryResolve(proxy);
    foreach (dep; _idxs) dep.tryResolve(proxy);
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
      description ~= "    Depends: \n";
      foreach (dep; _deps) {
	description ~= "\t" ~ dep.fullName() ~ "\n";
      }
    }
    description ~= "\n";
    return description;
  }

  // CstPredGroup _group;

  // CstPredGroup group() {
  //   return _group;
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
	_state = State.DISABLED;
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
	_state = State.DISABLED;
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

   void setGroupContext(CstPredGroup group, uint level) {
    
    
    assert(getOrderLevel() == level - 1, "unexpected error in solving before constraints");
      
    foreach (dom; _resolvedRnds) {
      assert(dom.getOrderLevel() != level, "unexpected error in solving before constraints");
      if (dom.getOrderLevel < level - 1){
	assert(dom.isSolved(), "unexpected error in solving before constraints");
      }
    } 
    
    addPredicateToGroup(group);
    
    foreach (dom; _resolvedRnds) {
      if (dom._state is CstDomBase.State.COLLATED && (! dom.isSolved())) {
	dom.setGroupContext(group, level);
      }
    }
    foreach (arr; _resolvedRndArrs) {
      if (arr._state is CstDomSet.State.COLLATED // && (! arr.isSolved())
	  ) {
	arr.setGroupContext(group, level);
      }
    }
  }

  void addPredicateToGroup(CstPredGroup group){
    _state = State.GROUPED;
    
    // if (_group !is group) {
    //   assert(_group is null,
    // 	     "A predicate may be added to a group, but group should not change");
    // }
    
    if (this.isDist()) {
      assert (group.hasDistConstraints());
      if (this.isGuardEnabled()) {
  	if (group._distPred !is null) {
  	  assert (false,
  		  "It is illegal to have more than one dist predicate active on the same domain");
  	}
  	group._distPred = this;
      }
      else {
  	group.addPredicate(this);
      }
    }
    else if (this.isGuard()) {
      group.addGuard(this);
    }
    else {
      group.addPredicate(this);
    }
    
  }
  // void setGroupContext(CstPredGroup group) {
  //   // import std.stdio;
  //   // writeln("setGroupContext: ", this.describe());
  //   foreach (dom; _unresolvedRnds) {
  //     if (! dom.inRange()) {
  // 	// import std.stdio;
  // 	// writeln(this.describe());
  // 	// writeln(_guard.describe());
  // 	if (_guard is null || _guard._expr.eval()) {
  // 	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
  // 	}
  // 	return;
  //     }
  //   }

  //   foreach (dom; _unresolvedVars) {
  //     if (! dom.inRange()) {
  // 	// import std.stdio;
  // 	// writeln(this.describe());
  // 	// writeln(_guard.describe());
  // 	if (_guard is null || _guard._expr.eval()) {
  // 	  assert (false, "Predicate " ~ name() ~ " has out of bound domain: " ~ dom.name());
  // 	}
  // 	return;
  //     }
  //   }

  //   _state = State.GROUPED;
  //   if (_group !is group) {
  //     assert(_group is null,
  // 	     "A predicate may be added to a group, but group should not change");
  //   }
  //   if (this.isDist()) {
  //     assert (group.hasDistConstraints());
  //     if (this.isGuardEnabled()) {
  // 	if (group._distPred !is null) {
  // 	  assert (false,
  // 		  "It is illegal to have more than one dist predicate active on the same domain");
  // 	}
  // 	group._distPred = this;
  //     }
  //     else {
  // 	group.addPredicate(this);
  //     }
  //   }
  //   else if (this.isGuard()) {
  //     group.addGuard(this);
  //   }
  //   else {
  //     group.addPredicate(this);
  //   }
  //   foreach (dom; _unresolvedRnds) {
  //     // import std.stdio;
  //     // writeln("setGroupContext: ", dom.name());
  //     // if (dom.group is null && (! dom.isSolved())) {
  //     if (dom._state is CstDomBase.State.INIT && (! dom.isSolved())) {
  // 	dom.setGroupContext(group);
  //     }
  //   }
  //   foreach (arr; _unresolvedRndArrs) {
  //     // import std.stdio;
  //     // writeln("setGroupContext: ", arr.name());
  //     // if (arr.group is null && (! arr.isSolved())) {
  //     if (arr._state is CstDomSet.State.INIT // && (! arr.isSolved())
  // 	  ) {
  // 	arr.setGroupContext(group);
  //     }
  //   }
  // }

  void annotate(CstPredGroup group, bool recurse=false) {
    // import std.stdio;
    // writeln("Annotating: ", this.describe());
    assert ((! this.isGuard()) || recurse);
    if (_guard !is null) _guard.annotate(group, true);

    foreach (rnd; this._resolvedRnds) {
      rnd.annotate(group);
    }
    foreach (rndArr; this._resolvedRndArrs) {
      group.addDomainArr(rndArr);
      foreach (rnd; rndArr[]) {
	rnd.annotate(group);
      }
    }
    foreach (var; this._resolvedVars) {
      var.annotate(group);
    }
    foreach (varArr; this._resolvedVarArrs) {
      group.addVariableArr(varArr);
      foreach (var; varArr[]) {
	var.annotate(group);
      }
    }
  }

  void writeSignature(ref Charbuf str) {
    import std.format: sformat;
    if (_soft != 0) {
      char[16] buff;
      str ~= '!';
      str ~=  sformat(buff[], "%d", _soft); // _soft.to!string();
      str ~= ':';
    }
    if (_guard !is null) {
      if (_guardInv) str ~= " ! ";
      _guard.writeSignature(str);
      str ~= " >> ";
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
  size_t hashValue() {
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
  
  bool isDist() { return _distDomain !is null; }
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
    assert (this.isGuard() || this.isVisitor() || _state == State.GROUPED,
	    "State is: " ~ _state.to!string());
    _state = State.SOLVED;

    this.execDepCbs();
  }

  bool tryResolveFixed(_esdl__Proxy proxy) {
    assert (isGuard());
    if (_unresolvedRnds.length > 0 || _unresolvedVars.length > 0) return false;
    else return tryResolve(proxy);
  }
  
  bool tryResolve(_esdl__Proxy proxy) {
    assert (isGuard());
    if (_unresolvedVarArrs.length > 0 ||
	_unresolvedRndArrs.length > 0) return false;
    else {
      bool success = true;
      foreach (rnd; _unresolvedRnds) {
	if (! rnd.tryResolve(proxy)) {
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
  
  bool isResolved() {
    return isSolved();
  }

  bool isSolved() {
    return (_state == State.SOLVED);
  }

  CstDepCallback[] _depCbs;
  void registerDepPred(CstDepCallback depCb) {
    foreach (cb; _depCbs) {
      if (cb is depCb) {
	return;
      }
    }
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
      for (uint i = cast(uint) _uwPreds.length;
	   i != currLen; ++i) {
	// import std.stdio;
	// writeln("i: ", i, " mapped: ", iter.mapIter(i));
	_uwPreds ~= new CstVisitorPredicate(_constraint, _guard, _guardInv, _statement, _proxy, _soft,
					    _expr.unroll(iter, iter.mapIter(i)), false, this, iter, i// ,
					    // _iters[1..$].map!(tr => tr.unrollIterator(iter, i)).array
					    );
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
	_proxy.addUnrolledPredicate(_uwPreds[i]);
      }
    }

    _uwLength = currLen;
  }
}
