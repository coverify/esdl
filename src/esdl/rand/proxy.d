module esdl.rand.proxy;

import esdl.solver.base: CstSolver, DistRangeSetBase;
import esdl.rand.base: CstVecPrim, CstLogicExpr, CstScope, CstDomBase,
  DomType, CstVecTerm, CstObjectVoid, CstVarNodeIntf, CstObjectIntf,
  CstIterator, CstDomSet, CstVarGlobIntf, CstLogicTerm;
import esdl.rand.pred: CstPredicate, CstPredGroup;
import esdl.rand.misc;
import esdl.data.folder;
import esdl.data.charbuf;

import std.container: Array;
import std.array;
import esdl.rand.cstx: CstParseData, CstParser;


static CstParseData constraintXlate(string PROXY, string CST,
			      string FILE, size_t LINE, string NAME="") {
  CstParser parser = CstParser(CST, FILE, LINE);
  return parser.translate(PROXY, NAME);
}

abstract class _esdl__ConstraintBase: rand.disable
{
  this(_esdl__Proxy proxy, string name, string constraint) {
    _proxy = proxy;
    _name = name;
    _constraint = constraint;
  }
  immutable string _constraint;
  immutable string _name;
  protected bool _enabled = true;
  protected _esdl__Proxy _proxy;

  bool isEnabled() {
    return _enabled;
  }

  void enable() {
    _enabled = true;
  }

  void disable() {
    _enabled = false;
  }

  void constraint_mode(bool mode) {
    if (mode != _enabled) {
      _enabled = mode;
      _proxy.getProxyRoot().setNeedSync();
    }
  }
  bool constraint_mode() { return _enabled; }

  string name() {
    return _name;
  }

  string fullName() {
    return _proxy.fullName() ~ _name;
  }

  final _esdl__Proxy getProxy() {
    return _proxy;
  }

  void _esdl__initCst() { }

  void _esdl__updateCst() { }
  
  abstract void makeConstraints();
  abstract CstPredicate[] getConstraintGuards();
  abstract CstPredicate[] getConstraints();
}

abstract class Constraint(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__)
  : _esdl__ConstraintBase
{
  import esdl.rand.vecx: CstVector;
  
  alias CstBoolVar = CstVector!(bool, rand(true, true), 0);
  
  debug(CSTPARSER) {
    pragma(msg, "/* Constraint Specification STARTS\n");
    pragma(msg, CONSTRAINT);
    pragma(msg, "\nConstraint Specification ENDS */");
    pragma(msg, "// cstDecls STARTS\n");
    pragma(msg, CST_PARSE_DATA.cstDecls);
    pragma(msg, "// cstDecls ENDS\n");
    pragma(msg, "// cstDefines STARTS\n");
    pragma(msg, CST_PARSE_DATA.cstDefines);
    pragma(msg, "// cstDefines! ENDS\n");
    pragma(msg, "// guardDecls STARTS\n");
    pragma(msg, CST_PARSE_DATA.guardDecls);
    pragma(msg, "// guardDecls! ENDS\n");
    pragma(msg, "// guardInits STARTS\n");
    pragma(msg, CST_PARSE_DATA.guardInits);
    pragma(msg, "// guardUpdts! ENDS\n");
    pragma(msg, CST_PARSE_DATA.guardUpdts);
    pragma(msg, "// guardUpdts! ENDS\n");
  }
    
  enum CstParseData CST_PARSE_DATA = constraintXlate("this.outer", CONSTRAINT, FILE, LINE);

  protected CstPredicate[] _preds;
  protected CstPredicate[] _guards;
  
  protected bool _initialized;

  this(_esdl__Proxy eng, string name) {
    super(eng, name, CONSTRAINT);
  }

  final override CstPredicate[] getConstraintGuards() {
    if (! _initialized) makeConstraints();
    return _guards;
  }

  final override CstPredicate[] getConstraints() {
    if (! _initialized) makeConstraints();
    return _preds;
  }

};


// template _esdl__baseHasRandomization(T) {
//   static if(is(T B == super)
// 	    && is(B[0] == class)) {
//     alias U = B[0];
//     static if(__traits(compiles, U._esdl__hasRandomization)) {
//       enum bool _esdl__baseHasRandomization = true;
//     }
//     else {
//       enum bool _esdl__baseHasRandomization = _esdl__baseHasRandomization!U;
//     }
//   }
//   else {
//     enum bool _esdl__baseHasRandomization = false;
//   }
// }
class CstDomBasePair {
  CstDomBase dom1;
  CstDomBase dom2;
  CstDomBase getFirst(){
    return dom1;
  }
  CstDomBase getSecond(){
    return dom2;
  }
  this( CstDomBase d1,  CstDomBase d2){
    dom1 = d1;
    dom2 = d2;
  }
}

abstract class _esdl__Proxy: CstObjectVoid, CstObjectIntf, rand.barrier
{
  // static Buddy _esdl__buddy;

  // CstDomBase[] _cstRndDomains;
  CstDomBase[] _cstValDomains;

  // compositional parent -- not inheritance based
  _esdl__Proxy _parent;
  _esdl__Proxy _root;

  // only the root proxy gets a null name, other component proxies override
  string fullName() {return "";}
  string name() {return "";}
  bool isRand() {return true;}

  _esdl__Proxy getProxyRoot() {
    if (_root is null) {return this;}
    else return _root;
  }

  // CstObjNodeIntf
  final bool _esdl__isObjArray() {return false;}
  final CstIterator _esdl__iter() {return null;}
  final CstVarNodeIntf _esdl__getChild(ulong n) {assert (false);}
  void scan() {}		// when an object is unrolled

  CstSolver[string] _solvers;

  CstVarGlobIntf[string] _globalLookups;

  void addGlobalLookup(CstVarGlobIntf global, string lookup) {
    assert(lookup !in _globalLookups);
    _globalLookups[lookup] = global;
  }

  CstVarGlobIntf getGlobalLookup(string lookup) {
    auto global = lookup in _globalLookups;
    if (global !is null) return *global;
    else return null;
  }

  Folder!(CstPredicate, "newPreds") _newPreds;
  Folder!(CstPredicate, "unrolledPreds") _unrolledPreds;
  
  Folder!(CstPredicate, "rolledPreds") _rolledPreds;
  Folder!(CstPredicate, "toRolledPreds") _toRolledPreds;
  Folder!(CstPredicate, "resolvedPreds") _resolvedPreds;
  Folder!(CstPredicate, "resolvedDynPreds") _resolvedDynPreds;
  // Folder!(CstPredicate, "beforePreds") _beforePreds;
  Folder!(CstDomBasePair, "beforePreds") _beforePreds;
  Folder!(CstPredicate, "toSolvePreds") _toSolvePreds;
  Folder!(CstPredicate, "dependentPreds") _dependentPreds;

  Folder!(CstPredicate, "_solvePreds") _solvePreds;

  Folder!(CstPredicate, "unresolvedPreds") _unresolvedPreds;
  Folder!(CstPredicate, "toResolvedPreds") _toUnresolvedPreds;

  // Folder!(CstPredicate, "resolvedDistPreds") _resolvedDistPreds;
  Folder!(CstPredicate, "resolvedMonoPreds") _resolvedMonoPreds;

  Folder!(CstDomBase, "solvedDomains") _solvedDomains;
  Folder!(CstDomSet, "solvedDomainArrs") _solvedDomainArrs;
  
  Folder!(CstPredGroup, "solvedGroups") _solvedGroups;

  void addSolvedDomain(CstDomBase domain) {
    _solvedDomains ~= domain;
  }

  // the integer variable _lap is incremented everytime a set of @rand
  // variables is made available for constraint solving. This 
  // variable is used for:
  // 1. marking the predicates that have unresolved dependencies
  //    and/or have a relation with such predicates. When some
  //    predicated are resolved it may lead to some of these
  //    predicates becoming available
  uint _lap;
  // _cycle is incremented once everytime randomize function is
  // called. The use of this variable within a @rand variable is to
  // indicate that the variable has been solved. Within a predicate,
  // this variable indicates that the predicate has been solved for
  // the indiated randomization cycle. There are two more places where
  // this variable is used:
  // 1. To indicate that iterator has been unrolled for a vec array in
  //    a given randomization cycle.
  // 2. To indicate that the index expression has been resolved for a
  //    vec/vec-array for the indicated randomization cycle
  uint _cycle;

  void updateValDomains() {
    foreach (dom; _cstValDomains) {
      dom.updateVal();
    }
  }
  
  _esdl__RandGen _esdl__rGen;

  _esdl__RandGen _esdl__getRandGen() {
    assert(_root is this);
    return _root._esdl__rGen;
  }

  uint _esdl__seed;
  uint _esdl__varN;

  uint indexVar() {
    return _esdl__varN++;
  }
  
  bool _esdl__seeded = false;

  uint getRandomSeed() {
    assert(_root is this);
    return _esdl__seed;
  }

  bool isRandomSeeded() {
    assert(_root is this);
    return _esdl__seeded;
  }

  void seedRandom(uint seed) {
    assert(_root is this);
    _esdl__seeded = true;
    _esdl__seed = seed;
    _esdl__rGen.seed(seed);    
  }
  
  
  // void addToUnrolled(CstPredicate pred) {
  //   _toUnrolledPreds ~= pred;
  // }
  
  // Scope for foreach
  CstScope _rootScope;
  CstScope _currentScope;

  void pushScope(CstIterator iter) {
    assert (_currentScope !is null);
    _currentScope = _currentScope.push(iter);
  }

  void popScope() {
    assert (_currentScope !is null);
    assert (_currentScope !is _rootScope);
    _currentScope = _currentScope.pop();
  }

  CstScope currentScope() {
    assert (_currentScope !is null);
    return _currentScope;
  }

  abstract bool _esdl__debugSolver();

  _esdl__Proxy unroll(CstIterator iter, ulong n) {
    return this;
  }

  // the root proxy is always static
  bool isStatic() {
    return true;
  }

  bool isRolled() {
    return false;
  }

  // Keep a list of constraints in the class
  _esdl__ConstraintBase _esdl__cstWith;

  bool _esdl__cstWithChanged = true;
  bool _esdl__needSync = true;

  bool needSync() {
    return _esdl__needSync;
  }

  void setNeedSync() {
    _esdl__needSync = true;
  }

  this(_esdl__Proxy parent, Object outer) {
    this(parent);
  }

  this(_esdl__Proxy parent, void* outer) {
    this(parent);
  }

  this(_esdl__Proxy parent) {
    import std.random: Random, uniform;
    debug(NOCONSTRAINTS) {
      assert(false, "Constraint engine started");
    }
    else {
      import esdl.base.core: Procedure;
      auto proc = Procedure.self;
      if (proc !is null) {
	Random procRgen = proc.getRandGen();
	_esdl__seed = 0; // uniform!(uint)(procRgen);
      }
      else {
	// no active simulation -- use global rand generator
	_esdl__seed = 0; // uniform!(uint)();
      }
    }
    _esdl__rGen = new _esdl__RandGen(_esdl__seed);

    if (parent is null) {
      // if (_esdl__buddy is null) {
      // 	_esdl__buddy = new Buddy(400, 400);
      // }
      _root = this;
    }
    else {
      _parent = parent;
      _root = _parent.getProxyRoot();
      // _esdl__buddy = _root._esdl__buddy;
    }
    // scopes for constraint parsing
    _rootScope = new CstScope(null, null);
    _currentScope = _rootScope;

  }

  // overridden by Randomization mixin -- see meta.d
  abstract void _esdl__doRandomize(_esdl__RandGen randGen);
  abstract void _esdl__doConstrain(_esdl__Proxy proxy);


  void reset() {
    // _solvedDomains is from previous cycle
    foreach (dom; _solvedDomains) {
      dom.reset();
    }
    foreach (domArr; _solvedDomainArrs) {
      domArr.reset();
    }
    // reset all bins
    _newPreds.reset();
    _unrolledPreds.reset();
    _rolledPreds.reset();
    _toRolledPreds.reset();
    _resolvedPreds.reset();
    _resolvedDynPreds.reset();
    _toSolvePreds.reset();
    _dependentPreds.reset();
    _unresolvedPreds.reset();
    _toUnresolvedPreds.reset();
    _beforePreds.reset();
    // _resolvedDistPreds.reset();
    _resolvedMonoPreds.reset();
    _solvedDomains.reset();
    _solvedDomainArrs.reset();
    updateValDomains();
  }
  
  private bool _solvedSome = false;
  void solvedSome() { _solvedSome = true; }
  bool checkContinue(ref CstDomBasePair pred, uint lap){
    if(pred.getSecond.getmarkBefore() == lap){
      return true;
    }
    CstDomBase dom = pred.getFirst;
    if(dom.isSolved()){
      return true;
    }
    foreach(predicate; _beforePreds){
      if(dom == predicate.getSecond && !predicate.getFirst.isSolved){
	return true;
      }
    }
    return false;
  }
  void addpsuedoBeforePreds( CstDomBase dom1, CstDomBase dom2,  ulong beforeLength) {
    for(uint j = 0; j < beforeLength; j++){
      if(_beforePreds[j].getFirst == dom2){
	if(!isInBeforePreds(dom1, _beforePreds[j].getSecond, beforeLength)){
	  _beforePreds ~= new CstDomBasePair(dom1, _beforePreds[j].getSecond);
	  addpsuedoBeforePreds( dom1, _beforePreds[j].getSecond, beforeLength);
	}
      }
    }
  }
  bool isInBeforePreds(CstDomBase dom1, CstDomBase dom2, ulong beforeLength){
    for(uint j = 0; j < beforeLength; j++){
      if(_beforePreds[j].getFirst == dom1 && _beforePreds[j].getSecond == dom2){
	return true;
      }
    }
    return false;
  }
  void solve() {
    if (_esdl__cstWithChanged is true)
      _esdl__needSync = true;
    assert(_root is this);
    this._cycle += 1;
    foreach(pred; _newPreds){
      makeBeforePreds(pred);
    }
    ulong beforeLength = _beforePreds.length;
    for(ulong i = 0; i < beforeLength; i++){
      CstDomBase dom1 = _beforePreds[i].getFirst;
      CstDomBase dom2 = _beforePreds[i].getSecond;
      addpsuedoBeforePreds( dom1, dom2, beforeLength);
    }
    while (_newPreds.length > 0 ||
	   _unrolledPreds.length > 0 ||
	   // _resolvedMonoPreds.length > 0 ||
	   _resolvedDynPreds.length > 0 ||
	   _resolvedPreds.length > 0 ||
	   _unresolvedPreds.length > 0 ||
	   _toRolledPreds.length > 0 ||
	   _dependentPreds.length > 0) {
      _solvedSome = false;
      // import std.stdio;

      // if (_newPreds.length > 0) {
      // 	writeln("Here for _newPreds: ", _newPreds.length);
      // }
      // if (_unrolledPreds.length > 0) {
      // 	writeln("Here for _unrolledPreds: ", _unrolledPreds.length);
      // }
      // if (_resolvedDynPreds.length > 0) {
      // 	writeln("Here for _resolvedDynPreds: ", _resolvedDynPreds.length);
      // }
      // if (_resolvedPreds.length > 0) {
      // 	writeln("Here for _resolvedPreds: ", _resolvedPreds.length);
      // }
      // if (_unresolvedPreds.length > 0) {
      // 	writeln("Here for _unresolvedPreds: ", _unresolvedPreds.length);
      // }
      // if (_toRolledPreds.length > 0) {
      // 	writeln("Here for _toRolledPreds: ", _toRolledPreds.length);
      // }

      // Predicate unrolling across array of objects may result in
      // registration of new constraints (via visitor predicates), so
      // it is important to process unrolled predicates before dealing
      // with new predicates
      foreach (pred; _unrolledPreds) procUnrolledPredicate(pred);
      _unrolledPreds.reset();
      
      foreach (pred; _newPreds) procNewPredicate(pred);
      _newPreds.reset();
      
      // foreach (pred; _resolvedDistPreds) {
      // 	_solvedDomains ~= solveDist(pred);
      // 	_solvedSome = true;
      // }
      // _resolvedDistPreds.reset();

      // _lap, like _cycle starts with 1
      // this is to avoid default values
      _lap += 1;
      // writeln("Lap: ", _lap);

      _rolledPreds.reset();
      _rolledPreds.swap(_toRolledPreds);

      foreach (pred; _rolledPreds) {
	if (pred.isRolled()) {
	  pred.markAsUnresolved(_lap);
	  _toRolledPreds ~= pred;
	}
	else {
	  _solvedSome = true;
	}
      }

      foreach (pred; _unresolvedPreds) {
	if (pred.isResolved()) {
	  procResolved(pred);
	}
	else {
	  _toUnresolvedPreds ~= pred;
	  pred.markAsUnresolved(_lap);
	}
      }

      // _resolvedMonoPreds.swap(_toSolvePreds);

      // foreach (pred; _toSolvePreds) {
      // 	if (_esdl__debugSolver) {
      // 	  import std.stdio;
      // 	  writeln("Solving Mono Predicate: ", pred.describe());
      // 	}
      // 	if (! procMonoDomain(pred)) {
      // 	  // writeln("Mono Unsolved: ", pred.name());
      // 	  _resolvedPreds ~= pred;
      // 	}
      // 	else {
      // 	  _solvedSome = true;
      // 	}
      // }
      // _toSolvePreds.reset();
      
      // first handle _resolvedDynPreds
      _resolvedDynPreds.swap(_toSolvePreds);

      foreach (pred; _toSolvePreds) {
	// if (_esdl__debugSolver) {
	//   import std.stdio;
	//   writeln("Solving Maybe Mono Predicate: ", pred.describe());
	// }
	if (pred.isMarkedUnresolved(_lap)) {
	  _resolvedDynPreds ~= pred;
	}
	else {
	  // if (! procMaybeMonoDomain(pred)) {
	  _solvePreds ~= pred;
	  // }
	  //   else {
	  //     _solvedSome = true;
	  //   }
	}
      }
      _toSolvePreds.reset();

      // now the normal _resolvedPreds
      _resolvedPreds.swap(_toSolvePreds);
      
      foreach (pred; _dependentPreds){
	_toSolvePreds ~= pred;
      }
      _dependentPreds.reset();
      
      foreach (pred; _beforePreds) {
	if(checkContinue(pred, _lap)){
	  continue;
	}
	//CstDomBase [] a = pred.getDomains();
	//assert(a.length == 2);
	pred.getFirst.orderBefore(pred.getSecond, _lap);
      }
      
      foreach (pred; _toSolvePreds) {
	if(pred.getmarkBefore()){
	  _dependentPreds ~= pred;
	  //pred.setmarkBefore(false);
	}
	else if (pred.isMarkedUnresolved(_lap)) {
	  _resolvedPreds ~= pred;
	}
	else {
	  _solvePreds ~= pred;
	}
      }

      _toSolvePreds.reset();

      // Work on _solvePreds
      foreach (pred; _solvePreds) {
	if (! pred.isGuard()) {
	  if (pred.isSolved()) {
	    _solvedSome = true;
	  }
	  else {
	    import std.conv: to;
	    CstPredGroup group = pred.group();
	    if (group is null) {
	      group = new CstPredGroup(this);
	      if (_esdl__debugSolver) {
		import std.stdio;
		writeln("Created new group ", group._id, " for predicate: ", pred.name());
	      }
	    }
	    assert (! group.isSolved(),
		    "Group can not be solved when the predicate is still not solved; group id: " ~
		    group._id.to!string() ~ " predicate id: " ~ pred._id.to!string());
	    group.setGroupContext(pred);
	    group.solve();
	    _solvedGroups ~= group;
	    _solvedSome = true;
	  }
	}
      }
      foreach(pred; _dependentPreds){
	pred.setmarkBefore(false);
      }
      foreach (pred; _beforePreds) {
	CstDomBase a = pred.getFirst;
	if(a.getmarkBefore < _lap && !(a.isSolved())){
	  a.randomizeWithoutConstraints(this);
	}
      }
      if (_solvedSome is false) {
	import std.stdio;
	// if (_resolvedDistPreds.length > 0) {
	//   stderr.writeln("_resolvedDistPreds: ");
	//   foreach (pred; _resolvedDistPreds) stderr.writeln(pred.describe());
	// }
	// if (_resolvedMonoPreds.length > 0) {
	//   stderr.writeln("_resolvedMonoPreds: ");
	//   foreach (pred; _resolvedMonoPreds) stderr.writeln(pred.describe());
	// }
	if (_resolvedDynPreds.length > 0) {
	  stderr.writeln("_resolvedDynPreds: ");
	  foreach (pred; _resolvedDynPreds) stderr.writeln(pred.describe());
	}
	if (_resolvedPreds.length > 0) {
	  stderr.writeln("_resolvedPreds: ");
	  foreach (pred; _resolvedPreds) stderr.writeln(pred.describe());
	}
	if (_unresolvedPreds.length > 0) {
	  stderr.writeln("_unresolvedPreds: ");
	  foreach (pred; _unresolvedPreds) stderr.writeln(pred.describe());
	}
	if (_toRolledPreds.length > 0) {
	  stderr.writeln("_toRolledPreds: ");
	  foreach (pred; _toRolledPreds) stderr.writeln(pred.describe());
	}
	assert (false, "Infinite loop in constraint solver");
      }

      _solvePreds.reset();

      
      _unresolvedPreds.reset();
      _unresolvedPreds.swap(_toUnresolvedPreds);
    }
    foreach (group; _solvedGroups) {
      group.reset();
      _solvedDomains ~= group.domains();
      _solvedDomainArrs ~= group.domainArrs();
    }
    _solvedGroups.reset();
    _esdl__needSync = false;
  }

  CstDomBase solveDist(CstPredicate pred) {
    if (_esdl__debugSolver) {
      import std.stdio;
      writeln("Solving Dist Predicate: ", pred.describe());
    }
    CstDomBase distDom = pred.distDomain();
    CstPredicate[] distPreds = distDom.getRandPreds();
    // long[] toRemove;
    DistRangeSetBase dist = pred._expr.getDist();
    dist.reset();
    foreach (predicate; distPreds){
      CstVecTerm ex = predicate._expr.isNot(distDom);
      // isNot returns rhs if the predicate is of != type,
      // otherwise it returns null
      if (predicate.getRnds().length == 1 && ! predicate.isDist()) {
	if (ex is null) {
	  assert (false, "can only use != operator on distributed domains");
	}
	dist.purge(ex.evaluate());
      }
    }
    dist.uniform(distDom, _esdl__getRandGen());
    return distDom;
  }

  void procResolved(CstPredicate pred) {
    assert (pred._rnds.length > 0 || pred._rndArrs.length > 0 || pred.isGuard(),
	    pred.describe());
    // if (pred.isDist()) {
    //   _resolvedDistPreds ~= pred;
    // }
    // // else if (pred._rnds.length == 1 &&
    // // 	     pred._rndArrs.length == 0 &&
    // // 	     pred._rnds[0]._type <= DomType.LAZYMONO//  &&
    // // 	     // pred._rnds[0]._esdl__parentIsConstrained is false
    // // 	     ) {
    // //   _resolvedMonoPreds ~= pred;
    // //   // procMonoDomain(pred._rnds[0], pred);
    // // }
    // else
    if (pred._dynRnds.length > 0) {
      foreach (rnd; pred._dynRnds) {
	auto dom = rnd.getResolved();
	dom._tempPreds ~= pred;
      }
      _resolvedDynPreds ~= pred;
    }
    else {
      _resolvedPreds ~= pred;
    }
  }

  void addNewPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln("Adding: ", pred.describe());
    _newPreds ~= pred;
  }

  void addUnrolledPredicate(CstPredicate pred) {
    // import std.stdio;
    // writeln("Adding: ", pred.describe());
    _unrolledPreds ~= pred;
  }
  void makeBeforePreds(CstPredicate pred ){
    if(pred.getExpr().isOrderingExpr()){
      _beforePreds ~= new CstDomBasePair(pred.getDomains[0], pred.getDomains[1]);
    }
  }
  void procNewPredicate(CstPredicate pred) {
    pred.randomizeDeps(this);
    if(pred.getExpr().isOrderingExpr()){
      
    }
    else if (pred._iters.length > 0) {
      _toRolledPreds ~= pred;
    }
    else if (pred._deps.length > 0) {
      _unresolvedPreds ~= pred;
    }
    else {
      procResolved(pred);
    }
  }

  void procUnrolledPredicate(CstPredicate pred) {
    pred.randomizeDeps(this);
    if (pred._iters.length == 0) {
      if (pred.isResolved(true)) {
	procResolved(pred);
      }
      else {
	_toUnresolvedPreds ~= pred;
      }
    }
    else {
      _toRolledPreds ~= pred;
    }
  }

}
