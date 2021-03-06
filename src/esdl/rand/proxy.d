module esdl.rand.proxy;
import esdl.solver.base;

import esdl.rand.base: CstVecPrim, CstLogicExpr, CstScope, CstDomain,
  CstPredicate, CstBlock, CstPredGroup, DomType, CstVecExpr, CstObjectVoid,
  CstVarNodeIntf, CstObjectIntf, CstIterator, CstDomSet, CstVarGlobIntf;

import esdl.rand.misc;
import esdl.data.folder;
import esdl.data.charbuf;
import esdl.rand.dist: DistRangeSetBase;

import std.container: Array;
import std.array;

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
  protected CstBlock _cstBlock;

  bool isEnabled() {
    return _enabled;
  }

  void enable() {
    _enabled = true;
  }

  void disable() {
    _enabled = false;
  }

  string name() {
    return _name;
  }

  string fullName() {
    return _proxy.fullName() ~ _name;
  }

  final _esdl__Proxy getProxy() {
    return _proxy;
  }

  final CstBlock getCstBlock() {
    if (_cstBlock is null) {
      _cstBlock = makeCstBlock();
    }
    return _cstBlock;
  }

  abstract CstBlock makeCstBlock();
}

static char[] constraintXlate(string PROXY, string CST,
			      string FILE, size_t LINE, string NAME="") {
  import esdl.rand.cstx;
  CstParser parser = CstParser(CST, FILE, LINE);
  return parser.translate(PROXY, NAME);
}

abstract class Constraint(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__)
  : _esdl__ConstraintBase
{
  this(_esdl__Proxy eng, string name) {
    super(eng, name, CONSTRAINT);
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
class domainPair {
  CstDomain dom1;
  CstDomain dom2;
  CstDomain getFirst(){
    return dom1;
  }
  CstDomain getSecond(){
    return dom2;
  }
  this( CstDomain d1,  CstDomain d2){
    dom1 = d1;
    dom2 = d2;
  }
}

abstract class _esdl__Proxy: CstObjectVoid, CstObjectIntf, rand.barrier
{
  // static Buddy _esdl__buddy;

  // CstDomain[] _cstRndDomains;
  CstDomain[] _cstValDomains;

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
  final CstVarNodeIntf _esdl__getChild(uint n) {assert (false);}
  void visit() {}		// when an object is unrolled

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
  Folder!(domainPair, "beforePreds") _beforePreds;
  Folder!(CstPredicate, "toSolvePreds") _toSolvePreds;
  Folder!(CstPredicate, "dependentPreds") _dependentPreds;

  Folder!(CstPredicate, "_solvePreds") _solvePreds;

  Folder!(CstPredicate, "unresolvedPreds") _unresolvedPreds;
  Folder!(CstPredicate, "toResolvedPreds") _toUnresolvedPreds;

  Folder!(CstPredicate, "resolvedDistPreds") _resolvedDistPreds;
  Folder!(CstPredicate, "resolvedMonoPreds") _resolvedMonoPreds;

  Folder!(CstDomain, "solvedDomains") _solvedDomains;
  Folder!(CstDomSet, "solvedDomainArrs") _solvedDomainArrs;
  
  Folder!(CstPredGroup, "solvedGroups") _solvedGroups;

  void addSolvedDomain(CstDomain domain) {
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

  _esdl__Proxy unroll(CstIterator iter, uint n) {
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

  bool _esdl__cstWithChanged;

  CstBlock _esdl__cstExprs;

  // Array!ulong _solveValue;
  
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

    if(parent is null) {
      // if (_esdl__buddy is null) {
      // 	_esdl__buddy = new Buddy(400, 400);
      // }
      _root = this;
      _esdl__cstExprs = new CstBlock();
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
    _resolvedDistPreds.reset();
    _resolvedMonoPreds.reset();
    _solvedDomains.reset();
    _solvedDomainArrs.reset();
    updateValDomains();
  }
  
  private bool _solvedSome = false;
  void solvedSome() { _solvedSome = true; }
  bool checkContinue(ref domainPair pred, uint lap){
    if(pred.getSecond.getmarkBefore() == lap){
      return true;
    }
    CstDomain dom = pred.getFirst;
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
  void addpsuedoBeforePreds( CstDomain dom1, CstDomain dom2,  ulong beforeLength) {
    for(uint j = 0; j < beforeLength; j++){
      if(_beforePreds[j].getFirst == dom2){
	if(!isInBeforePreds(dom1, _beforePreds[j].getSecond, beforeLength)){
	  _beforePreds ~= new domainPair(dom1, _beforePreds[j].getSecond);
	  addpsuedoBeforePreds( dom1, _beforePreds[j].getSecond, beforeLength);
	}
      }
    }
  }
  bool isInBeforePreds(CstDomain dom1, CstDomain dom2, ulong beforeLength){
    for(uint j = 0; j < beforeLength; j++){
      if(_beforePreds[j].getFirst == dom1 && _beforePreds[j].getSecond == dom2){
	return true;
      }
    }
    return false;
  }
  void solve() {
    assert(_root is this);
    this._cycle += 1;
    foreach(pred; _newPreds){
      makeBeforePreds(pred);
    }
    ulong beforeLength = _beforePreds.length;
    for(ulong i = 0; i < beforeLength; i++){
      CstDomain dom1 = _beforePreds[i].getFirst;
      CstDomain dom2 = _beforePreds[i].getSecond;
      addpsuedoBeforePreds( dom1, dom2, beforeLength);
    }
    while (_newPreds.length > 0 ||
	   _unrolledPreds.length > 0 ||
	   // _resolvedDistPreds.length > 0 ||
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
      
      foreach (pred; _resolvedDistPreds) {
	if (_esdl__debugSolver) {
	  import std.stdio;
	  writeln("Solving Dist Predicate: ", pred.describe());
	}
	CstDomain[] distVars = pred.getRnds();
	assert (distVars.length == 1);
	CstDomain distDom = distVars[0];
	CstPredicate[] distPreds = distDom.getRandPreds();
	// long[] toRemove;
	DistRangeSetBase dist = pred._expr.getDist();
	dist.reset();
	foreach (predicate; distPreds){
	  CstVecExpr ex = predicate._expr.isNot(distDom);
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
	_solvedDomains ~= distDom;
	_solvedSome = true;
      }
      _resolvedDistPreds.reset();

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
	//CstDomain [] a = pred.getDomains();
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
      foreach( pred; _dependentPreds){
	pred.setmarkBefore(false);
      }
      foreach (pred; _beforePreds) {
	CstDomain a = pred.getFirst;
	if(a.getmarkBefore < _lap && !(a.isSolved())){
	  a.randomizeWithoutConstraints(this);
	}
      }
      if (_solvedSome is false) {
	import std.stdio;
	if (_resolvedDistPreds.length > 0) {
	  stderr.writeln("_resolvedDistPreds: ");
	  foreach (pred; _resolvedDistPreds) stderr.writeln(pred.describe());
	}
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
      
  }

  void procResolved(CstPredicate pred) {
    assert (pred._rnds.length > 0 || pred._rndArrs.length > 0,
	    pred.describe());
    if (pred.isDist()) {
      _resolvedDistPreds ~= pred;
    }
    // else if (pred._rnds.length == 1 &&
    // 	     pred._rndArrs.length == 0 &&
    // 	     pred._rnds[0]._type <= DomType.LAZYMONO//  &&
    // 	     // pred._rnds[0]._esdl__parentIsConstrained is false
    // 	     ) {
    //   _resolvedMonoPreds ~= pred;
    //   // procMonoDomain(pred._rnds[0], pred);
    // }
    else if (pred._dynRnds.length > 0) {
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
    _unrolledPreds ~= pred;
  }
  void makeBeforePreds(CstPredicate pred ){
    if(pred.getExpr().isOrderingExpr()){
      _beforePreds ~= new domainPair(pred.getDomains[0], pred.getDomains[1]);
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
