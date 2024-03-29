module esdl.rand.cstr;
import esdl.rand.pred: CstPredicate;
import esdl.rand.parser: CstParseData, CstParser;
import esdl.rand.misc;
import esdl.rand.proxy: _esdl__Proxy, _esdl__CstProcessor;
import esdl.data.vector: Vector;


static CstParseData constraintXlate(string PROXY, string CST,
				    string FILE, size_t LINE, string NAME="") {
  CstParser parser = CstParser(CST, FILE, LINE);
  return parser.translate(PROXY, NAME);
}

abstract class _esdl__ConstraintBase: rand.disable
{
  this(_esdl__Proxy proxy, string name, string constraint) {
    _proxy = proxy;
    _esdl__name = name;
    _constraint = constraint;
  }

  __gshared uint _esdl__lambdaConstraintCount;

  immutable string _constraint;
  immutable string _esdl__name;
  protected bool _overridden = false;
  protected _esdl__Proxy _proxy;

  void markOverridden() {
    _overridden = true;
  }
  
  bool isEnabled() {
    return constraintMode() && ! _overridden;
  }

  void enable() {
    constraintMode(true);
  }

  void disable() {
    constraintMode(false);
  }

  void constraintMode(bool mode) { // overridden in derived class
    assert(false);
  }

  bool constraintMode() { // overridden in derived class
    return true;
  }

  string _esdl__getName() {
    return _esdl__name;
  }

  string _esdl__getFullName() {
    return _proxy._esdl__getFullName() ~ '.' ~ _esdl__name;
  }

  final _esdl__Proxy getProxy() {
    return _proxy;
  }

  void _esdl__initCst() { }

  void _esdl__updateCst() { }
  
  abstract void makeConstraints();
  abstract void doSetDomainContext(_esdl__CstProcessor proc);
  abstract void doProcDomainContext(_esdl__CstProcessor proc);

  abstract CstPredicate[] getConstraintGuards();
  abstract CstPredicate[] getConstraints();
  abstract string getCode();
  abstract bool isLambdaConstraint();
  abstract bool isVisitorConstraint();

}


// struct wrapper for the main user interface
// it has to be a struct, because the user may not wait for a class object to
// constructed before he can call API methods like constraint_mode
alias constraint = Constraint;

enum constraint_override;

struct Constraint(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__)
{
  enum bool _esdl__TypeHasRandBarrier = true;
  alias CstType = _esdl__Constraint!(CONSTRAINT, FILE, LINE);

  bool _mode = true;

  alias constraint_mode = constraintMode;

  void constraintMode(bool mode) {
    _mode = mode;
  }

  bool constraintMode() {
    return _mode;
  }

}


abstract class _esdl__ConstraintLambda(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__):
  _esdl__Constraint!(CONSTRAINT, FILE, LINE) {
  this(_esdl__Proxy eng, string name) {
    super(eng, name);
  }
  __gshared immutable uint _esdl__lambdaConstraintID;

  pragma(crt_constructor)
    extern(C) static void _esdl__setWithConstraintID() {
    _esdl__lambdaConstraintID = _esdl__lambdaConstraintCount++;
  }
  
  static uint _esdl__getLambdaConstraintID() {
    return _esdl__lambdaConstraintID;
  }
  
}


abstract class _esdl__Constraint(string CONSTRAINT, string FILE=__FILE__, size_t LINE=__LINE__)
  : _esdl__ConstraintBase, rand.barrier
{
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

  protected Vector!(CstPredicate, "preds") _preds;
  protected Vector!(CstPredicate, "guards") _guards;
  
  protected bool _initialized;

  this(_esdl__Proxy eng, string name) {
    super(eng, name, CONSTRAINT);
  }

  final override CstPredicate[] getConstraintGuards() {
    assert (_initialized);
    return _guards[];
  }

  final override CstPredicate[] getConstraints() {
    assert (_initialized);
    return _preds[];
  }

  final override void doSetDomainContext(_esdl__CstProcessor proc) {
    // guards should always be processed before the usual predicates
    foreach (pred; _guards) pred.doSetDomainContext(pred, proc);
    foreach (pred; _preds)  pred.doSetDomainContext(pred, proc);
  }

  final override void doProcDomainContext(_esdl__CstProcessor proc) {
    foreach (pred; _guards) pred.doProcDomainContext(proc);
    foreach (pred; _preds)  pred.doProcDomainContext(proc);
  }

  override string getCode() {
    return CONSTRAINT;
  }

}


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
// class CstDomBasePair {
//   CstDomBase dom1;
//   CstDomBase dom2;
//   CstDomBase getFirst(){
//     return dom1;
//   }
//   CstDomBase getSecond(){
//     return dom2;
//   }
//   this( CstDomBase d1,  CstDomBase d2){
//     dom1 = d1;
//     dom2 = d2;
//   }
// }

