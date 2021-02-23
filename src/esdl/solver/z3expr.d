module esdl.solver.z3expr;

import esdl.intf.z3.api;
import esdl.intf.z3.z3;
import std.string: toStringz;
import core.stdc.string: strlen;

import std.traits: isIntegral, isBoolean;
import std.stdio;

alias BvExprVector = AstVectorTpl!BvExpr;
alias BoolExprVector = AstVectorTpl!BoolExpr;

T StaticCast(T, F)(const F from)
  if (is (F == class) && is (T == class)
      // make sure that F is indeed amongst the base classes of T
      && staticIndexOf!(F, BaseClassesTuple!T) != -1
      )
    in {
      // assert statement will not be compiled for production release
      assert((from is null) || cast(T)from !is null);
    }
body {
  return cast(T) cast(void*) from;
 }


struct BvExpr
{
  mixin RvalueRef;
  
  AST _ast;
  bool _signed;

  this(Context c, string name, uint size, bool signed=true) {
    _signed = signed;
    Z3_ast r = Z3_mk_const(c, c.strSymbol(name), c.bvSort(size));
    c.checkError();
    _ast = AST(c, r);
  }
  
  this(Context c, Z3_ast n, bool signed=true) {
    _signed = signed;
    _ast = AST(c, n);
  }

  this(this) { }

  // this(ref return scope BvExpr rhs) {
  //   _signed = rhs._signed;
  //   _ast = rhs._ast;
  // }

  bool isNull() {
    return _ast.isNull();
  }

  BvExpr opAssign(ref return scope BvExpr rhs) {
    _ast = rhs._ast;
    _signed = rhs._signed;
    return this;
  }

  bool isSigned() {
    return _signed;
  }

  void setContext(Context ctx) {
    _ast.setContext(ctx);
  }
  Context context() {
    return _ast.context();
  }
  Z3_error_code checkError()  {
    return _ast.checkError();
  }
  // alias _ast this;

  T opCast(t)() if (is (T == Z3_ast)) {
    return _ast.m_ast;
  }
  Z3_ast getAST() {
    return _ast.m_ast;
  }
  
  alias getAST this;

  Z3_ast_kind kind() {
    return _ast.kind();
  }

  Z3_ast opCast(T)() if (is (T == Z3_ast)) {
    return _ast;
  }
  
  /**
     \brief Return the sort of this expression.
  */
  Sort getSort() {
    Z3_sort s = Z3_get_sort(context(), _ast.m_ast);
    checkError();
    return Sort(context(), s);
  }

  /**
     \brief Return true if this expression is an application.
  */
  bool isApp() {
    return kind() == Z3_ast_kind.Z3_APP_AST || kind() == Z3_ast_kind.Z3_NUMERAL_AST;
  }
  /**
     \brief Return true if this expression is a constant (i.e., an application with 0 arguments).
  */
  bool isConst() {
    return isApp() && numArgs() == 0;
  }
  /**
     \brief Return true if this expression is a lambda expression.
  */
  bool isLambda() {
    return Z3_is_lambda(context(), getAST);
  }
  /**

     \brief Return true if this expression is a variable.
  */
  bool isVar() {
    return kind() == Z3_ast_kind.Z3_VAR_AST;
  }
  /**
     \brief Return true if expression is an algebraic number.
  */
  bool isAlgebraic() {
    return Z3_is_algebraic_number(context(), getAST);
  }

  /**
     \brief Return true if this expression is well sorted (aka type correct).
  */
  bool isWellSorted() {
    bool r = Z3_is_well_sorted(context(), getAST);
    checkError();
    return r;
  }

  /**
     \brief Return string representation of numeral or algebraic number
     This method assumes the expression is numeral or algebraic

     \pre is_numeral() || is_algebraic()
  */
  string get_decimal_string(int precision) {
    auto r = (Z3_get_numeral_decimal_string(context(), getAST, precision));
    return cast(string) r[0..r.strlen];
  }
        

  /**
     \brief retrieve unique identifier for expression.
  */
  uint id() {
    uint r = Z3_get_ast_id(context(), getAST);
    checkError();
    return r;
  }

  /**
     \brief Return true if this expression is a string literal. 
     The string can be accessed using \c get_string() and \c get_escaped_string()
  */
  bool isStringValue() {
    return Z3_is_string(context(), getAST);
  }

  /**
     \brief for a string value expression return an escaped or unescaped string value.
     \pre expression is for a string value.
  */

  string getEscapedString() {            
    assert (isStringValue());
    auto s = Z3_get_string(context(), getAST);
    checkError();
    return cast(string) s[0..s.strlen];
  }

  string getString() {
    assert (isStringValue());
    uint n;
    auto s = Z3_get_lstring(context(), getAST, &n);
    checkError();
    return cast(string) s[0..n];
  }

  T opCast(T)() if (is (T == Z3_app)) {
    assert (isApp());
    return cast (Z3_app) this;
  }
  
  Z3_app getApp() {
    assert (isApp());
    return cast (Z3_app) this;
  }


  /**
     \brief Return the declaration associated with this application.
     This method assumes the expression is an application.

     \pre is_app()
  */
  FuncDecl decl() {
    Z3_func_decl f = Z3_get_app_decl(context(), cast(Z3_app) this);
    checkError();
    return FuncDecl(context(), f);
  }
  /**
     \brief Return the number of arguments in this application.
     This method assumes the expression is an application.

     \pre is_app()
  */
  uint numArgs() {
    uint r = Z3_get_app_num_args(context(), cast(Z3_app) this);
    checkError();
    return r;
  }
  /**
     \brief Return the i-th argument of this application.
     This method assumes the expression is an application.

     \pre is_app()
     \pre i < num_args()
  */
  BvExpr arg(uint i) {
    Z3_ast r = Z3_get_app_arg(context(), cast(Z3_app) this, i);
    checkError();
    return BvExpr(context(), r, _signed);
  }

  // expr rotate_left(uint i) { Z3_ast r = Z3_mk_rotate_left(context(), i, *this); context().checkError(); return expr(context(), r); }
  BvExpr rotateLeft(uint i) {
    Z3_ast r = Z3_mk_rotate_left(context(), i, getAST);
    context().checkError();
    return BvExpr(context(), r, _signed);
  }
  // expr rotate_right(uint i) { Z3_ast r = Z3_mk_rotate_right(context(), i, *this); context().checkError(); return expr(context(), r); }
  BvExpr rotateRight(uint i) {
    Z3_ast r = Z3_mk_rotate_right(context(), i, getAST);
    context().checkError();
    return BvExpr(context(), r, _signed);
  }
  // expr repeat(uint i) { Z3_ast r = Z3_mk_repeat(context(), i, *this); context().checkError(); return expr(context(), r); }
  BvExpr repeat(uint i) {
    Z3_ast r = Z3_mk_repeat(context(), i, getAST);
    context().checkError();
    return BvExpr(context(), r, _signed);
  }

  // expr extract(uint hi, uint lo) { Z3_ast r = Z3_mk_extract(context(), hi, lo, *this); context().checkError(); return expr(context(), r); }
  BvExpr extract(uint hi, uint lo) {
    Z3_ast r = Z3_mk_extract(context(), hi, lo, getAST);
    context().checkError();
    return BvExpr(context(), r, false);
  }
  
  // uint lo() { assert (is_app() && Z3_get_decl_num_parameters(context(), decl()) == 2); return static_cast<uint>(Z3_get_decl_int_parameter(context(), decl(), 1)); }
  uint lo() {
    assert (isApp() && Z3_get_decl_num_parameters(context(), decl()) == 2);
    return cast(uint) Z3_get_decl_int_parameter(context(), decl(), 1);
  }

  // uint hi() { assert (is_app() && Z3_get_decl_num_parameters(context(), decl()) == 2); return static_cast<uint>(Z3_get_decl_int_parameter(context(), decl(), 0)); }
  uint hi() {
    assert (isApp() && Z3_get_decl_num_parameters(context(), decl()) == 2);
    return cast(uint) Z3_get_decl_int_parameter(context(), decl(), 0);
  }

  // friend expr fma(expr const& a, expr const& b, expr const& c, expr const& rm);

  // /**
  //    \brief sequence and regular expression operations.
  //    + is overloaded as sequence concatenation and regular expression union.
  //    concat is overloaded to handle sequences and regular expressions
  // */
  BvExpr extract()(auto ref BvExpr offset, auto ref BvExpr length) {
    checkContext(this, offset); checkContext(offset, length);
    Z3_ast r = Z3_mk_seq_extract(context(), getAST, offset.getAST, length.getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr replace()(auto ref BvExpr src, auto ref BvExpr dst) {
    checkContext(this, src); checkContext(src, dst);
    Z3_ast r = Z3_mk_seq_replace(context(), getAST, src.getAST, dst.getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr unit() {
    Z3_ast r = Z3_mk_seq_unit(context(), getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr contains()(auto ref BvExpr s) {
    checkContext(this, s);
    Z3_ast r = Z3_mk_seq_contains(context(), getAST, s.getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr at()(auto ref BvExpr index) {
    checkContext(this, index);
    Z3_ast r = Z3_mk_seq_at(context(), getAST, index.getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr nth()(auto ref BvExpr index) {
    checkContext(this, index);
    Z3_ast r = Z3_mk_seq_nth(context(), getAST, index.getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr length() {
    Z3_ast r = Z3_mk_seq_length(context(), getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr stoi() {
    Z3_ast r = Z3_mk_str_to_int(context(), getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  BvExpr itos() {
    Z3_ast r = Z3_mk_int_to_str(context(), getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }

  // friend expr range(expr const& lo, expr const& hi);


  /**
     \brief create a looping regular expression.
  */
  BvExpr loop(uint lo) {
    Z3_ast r = Z3_mk_re_loop(context(), getAST, lo, 0);
    checkError();
    return BvExpr(context(), r, _signed);
  }

  BvExpr loop(uint lo, uint hi) {
    Z3_ast r = Z3_mk_re_loop(context(), getAST, lo, hi);
    checkError();
    return BvExpr(context(), r, _signed);
  }

  /**
   * index operator defined on arrays and sequences.
   */
  BvExpr opIndex()(auto ref BvExpr index) {
    assert(isArray() || isSeq());
    if (isArray()) {
      return select(this, index);
    }
    return nth(index);            
  }

  BvExpr opIndex()(auto ref BvExprVector index) {
    return select(this, index);
  }

  /**
     \brief Return a simplified version of this expression.
  */
  BvExpr simplify() {
    Z3_ast r = Z3_simplify(context(), getAST);
    checkError();
    return BvExpr(context(), r, _signed);
  }
  /**
     \brief Return a simplified version of this expression. The parameter \c p is a set of parameters for the Z3 simplifier.
  */
  BvExpr simplify()(auto ref Params p) {
    Z3_ast r = Z3_simplify_ex(context(), getAST, p);
    checkError();
    return BvExpr(context(), r, _signed);
  }

  /**
     \brief Apply substitution. Replace src expressions by dst.
  */

  BvExpr substitute()(auto ref BvExprVector src, auto ref BvExprVector dst) {
    assert (src.size() == dst.size());
    Z3_ast[] _src = new Z3_ast[](src.size());
    Z3_ast[] _dst = new Z3_ast[](dst.size());
    for (uint i = 0; i < src.size(); ++i) {
      _src[i] = src[i].getAST;
      _dst[i] = dst[i].getAST;
    }
    Z3_ast r = Z3_substitute(context(), getAST, src.size(), _src.ptr, _dst.ptr);
    checkError();
    return BvExpr(context(), r, _signed);
  }

  /**
     \brief Apply substitution. Replace bound variables by expressions.
  */

  BvExpr substitute()(auto ref BvExprVector dst) {
    Z3_ast[] _dst = new Z3_ast[](dst.size());
    for (uint i = 0; i < dst.size(); ++i) {
      _dst[i] = dst[i].getAST;
    }
    Z3_ast r = Z3_substitute_vars(context(), getAST, dst.size(), _dst.ptr);
    checkError();
    return BvExpr(context(), r, _signed);
  }

  BvExpr opUnary(string op)() if(op == "~") {
    return BvExpr(context(), Z3_mk_bvnot(this.context, getAST), _signed);
  }

  BvExpr opUnary(string op)() if(op == "-") {
    Z3_ast r = 0;
    r = Z3_mk_bvneg(this.context(), getAST);
    this.checkError();
    return BvExpr(context(), r, _signed);
  }

  BvExpr zext(uint i) {
    return BvExpr(context(), Z3_mk_zero_ext(context(), i, getAST), _signed);
  }

  BvExpr sext(uint i) {
    return BvExpr(context(), Z3_mk_sign_ext(context(), i, getAST), _signed);
  }

  BvExpr extendBy(uint i, bool signed) {
    if (signed) {
      return BvExpr(context(), Z3_mk_sign_ext(context(), i, getAST), signed);
    }
    else {
      return BvExpr(context(), Z3_mk_zero_ext(context(), i, getAST), signed);
    }
  }

  BvExpr extendTo(uint newSize, bool signed) {
    assert (newSize >= size());
    if (signed) {
      return BvExpr(context(), Z3_mk_sign_ext(context(), newSize - size(), getAST), signed);
    }
    else {
      return BvExpr(context(), Z3_mk_zero_ext(context(), newSize - size(), getAST), signed);
    }
  }

  uint size() {
    auto sort = getSort();
    assert (sort.isBv());
    return sort.bvSize();
  }

  BvExpr promote() {
    uint sz = size();
    if (sz < 32) {
      if (_signed) {
	return BvExpr(context(), Z3_mk_sign_ext(context(), 32-sz, getAST), true);
      }
      else {
	return BvExpr(context(), Z3_mk_zero_ext(context(), 32-sz, getAST), true);
      }
    }
    if (sz == 32) return this;
    if (sz < 64) {
      if (_signed) {
	return BvExpr(context(), Z3_mk_sign_ext(context(), 64-sz, getAST), true);
      }
      else {
	return BvExpr(context(), Z3_mk_zero_ext(context(), 64-sz, getAST), true);
      }
    }
    else return this;
  }
  
  /**
     \brief Return true if this is a Bit-vector expression.
  */
  bool isBv() {
    return getSort().isBv();
  }

  BvExpr opBinary(string op)(BvExpr other)
    if (op == "&" || op == "|" || op == "^" || op == "+" ||
	op == "-" || op == "*" || op == "/" || op == "%" ||
	op == "<<" || op == ">>" || op == ">>>") {
      import std.algorithm: min, max;
      checkContext(this, other);

      // BvExpr lhs = this;
      // BvExpr rhs = other;
      BvExpr lhs, rhs;

      bool signed = promoteToCommonType(this, other, lhs, rhs);

      assert (lhs.isBv()); assert(rhs.isBv());
      
      Z3_ast r = null;
      static if(op == "&") {
	r = Z3_mk_bvand(this.context(), lhs, rhs);
      }
      static if(op == "|") {
	r = Z3_mk_bvor(this.context(), lhs, rhs);
      }
      static if(op == "^") {
	r = Z3_mk_bvxor(this.context(), lhs, rhs);
      }
      static if(op == "+") {
	r = Z3_mk_bvadd(this.context(), lhs, rhs);
      }
      static if(op == "-") {
	r = Z3_mk_bvsub(this.context(), lhs, rhs);
      }
      static if(op == "*") {
	r = Z3_mk_bvmul(this.context(), lhs, rhs);
      }
      static if(op == "/") {
	if (signed) r = Z3_mk_bvsdiv(a.context(), lhs, rhs);
	else        r = Z3_mk_bvudiv(a.context(), lhs, rhs);
      }
      static if(op == "%") {
	if (signed) r = Z3_mk_bvsrem(a.context(), lhs, rhs);
	else        r = Z3_mk_bvurem(a.context(), lhs, rhs);
      }
      static if(op == "<<") {
	r = Z3_mk_bvshl(a.context(), lhs, rhs);
      }
      static if(op == ">>") {
	if (signed) r = Z3_mk_bvashr(a.context(), lhs, rhs);
	else        r = Z3_mk_bvlshr(a.context(), lhs, rhs);
      }
      static if(op == ">>>") {
	r = Z3_mk_bvlshr(a.context(), lhs, rhs);
      }
      checkError();
      return BvExpr(this.context(), r, signed);
    }

  static BvExpr castAST(Context c, Z3_ast a) {
    assert (Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_NUMERAL_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_APP_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_QUANTIFIER_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_VAR_AST);
    return BvExpr(c, a);
  }

  int getNumeralInt() {
    int result = 0;
    if (!isNumeralI(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine int");
    }
    return result;
  }

  uint getNumeralUint() {
    uint result = 0;
    if (!isNumeralU(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine uint");
    }
    return result;
  }

  long getNumeralInt64() {
    long result = 0;
    if (!isNumeralI64(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine int64_t");
    }
    return result;
  }

  ulong getNumeralUint64() {
    ulong result = 0;
    if (!isNumeralU64(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine uint64_t");
    }
    return result;
  }

  bool isNumeralI64(ref long i) {
    bool r = Z3_get_numeral_int64(context(), getAST, &i);
    checkError();
    return r;
  }

  bool isNumeralU64(ref ulong i) {
    bool r = Z3_get_numeral_uint64(context(), getAST, &i);
    checkError();
    return r;
  }

  bool isNumeralI(ref int i) {
    bool r = Z3_get_numeral_int(context(), getAST, &i);
    checkError();
    return r;
  }

  bool isNumeralU(ref uint i) {
    bool r = Z3_get_numeral_uint(context(), getAST, &i);
    checkError();
    return r;
  }

  bool isNumeral(ref string s) {
    auto r = Z3_get_numeral_string(context(), getAST);
    s = cast(string) r[0..r.strlen];
    checkError();
    return true;
  }


  BvExpr mapTo(ref Model m, bool model_completion=false) {
    checkContext(this, m);
    Z3_ast r = null;
    bool status = Z3_model_eval(context(), m, this.getAST, model_completion, &r);
    checkError();
    if (status == false && context().enableExceptions())
      throw(new Exception("failed to evaluate expression"));
    return BvExpr(context(), r, _signed);
  }
}

BvExpr bvNumVal(Context c, long n, uint bitcount, bool signed) {
  Sort s = c.bvSort(bitcount);
  Z3_ast r;
  if (bitcount <= 32) {
    if (signed) r = Z3_mk_int(c, cast(int) n, s);
    else r = Z3_mk_unsigned_int(c, cast(uint) n, s);
  }
  else if (bitcount <= 64) {
    if (signed) r = Z3_mk_int64(c, n, s);
    else r = Z3_mk_unsigned_int64(c, cast(ulong) n, s);
  }
  else {
    // use the following API for BV
    // extern(C) Z3_ast Z3_mk_bv_numeral (Z3_context c, uint sz, const(bool)* bits);
    assert (false, "TBD: BitVector needs to be implemented");
  }
  c.checkError();
  return BvExpr(c, r, signed);
}

bool promoteToCommonType(ref BvExpr a, ref BvExpr b,
			 ref BvExpr lhs, ref BvExpr rhs) {

  // lhs = a; rhs = b;
  // return true;
  import std.algorithm: max;

  checkContext(a, b);

  BvExpr lexpr = a.promote();
  BvExpr rexpr = b.promote();
      
  uint lsz = lexpr.size();
  uint rsz = rexpr.size();

  uint size = max(lsz, rsz);
  bool signed = lexpr._signed && rexpr._signed;

  if (lsz != size) {
    auto extended = lexpr.extendTo(size, signed);
    lhs = extended;
  }
  else lhs = lexpr;

  if (rsz != size) {
    auto extended = rexpr.extendTo(size, signed);
    rhs = extended;
  }
  else rhs = rexpr;

  return signed;
}

// friend expr distinct(expr_vector const& args);
BoolExpr distinct()(auto ref BvExprVector args) {
  assert (args.size() > 0);
  Context ctx = args.context();
  Z3_ast[] _args = args.toArray!Z3_ast();
  Z3_ast r = Z3_mk_distinct(args.context(), cast(uint) _args.length, _args.ptr);
  args.checkError();
  return BoolExpr(args.context(), r);
}

// friend expr concat(expr const& a, expr const& b);
BvExpr concat()(auto ref BvExpr a, auto ref BvExpr b) {
  checkContext(a, b);
  Z3_ast r;
  if (Z3_is_seq_sort(a.context(), a.getSort())) {
    Z3_ast[2] _args = [a.getAST, b.getAST];
    r = Z3_mk_seq_concat(a.context(), 2, _args.ptr);
  }
  else if (Z3_is_re_sort(a.context(), a.getSort())) {
    Z3_ast[2] _args = [a.getAST, b.getAST];
    r = Z3_mk_re_concat(a.context(), 2, _args.ptr);
  }
  else {
    r = Z3_mk_concat(a.context(), a.getAST, b.getAST);
  }
  a.checkError();
  return BvExpr(a.context(), r);
}

// friend expr concat(expr_vector const& args);
BvExpr concat()(auto ref BvExprVector args) {
  Z3_ast r;
  assert (args.size() > 0);
  if (args.size() == 1) {
    return args[0];
  }
  Z3_ast[] _args = args.toArray!Z3_ast();
  if (Z3_is_seq_sort(args.context(), args[0].getSort())) {
    r = Z3_mk_seq_concat(args.context(), cast(uint) _args.length, _args.ptr);
  }
  else if (Z3_is_re_sort(args.context(), args[0].getSort())) {
    r = Z3_mk_re_concat(args.context(), cast(uint) _args.length, _args.ptr);
  }
  else {
    r = _args[_args.length-1];
    for (size_t i = _args.length - 1; i > 0; ) {
      --i;
      r = Z3_mk_concat(args.context(), _args[i], r);
      args.checkError();
    }
  }
  args.checkError();
  return BvExpr(args.context(), r);
}

// friend expr operator==(expr & a, expr & b);
BoolExpr eq()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_eq(lhs.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BoolExpr(lhs.context(), r);
}

// // friend expr operator==(expr & a, int b);
// BoolExpr eq()(auto ref BvExpr a, int b) {
//   assert (a.isBv());
//   return eq(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator==(int a, expr & b);
// BoolExpr eq()(int a, auto ref BvExpr b) {
//   assert(b.isBv());
//   return eq(bvNumVal(b.context(), a).byRef, b);
// }



// friend expr operator!=(expr & a, expr & b);
BoolExpr neq()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast[2] args = [lhs.getAST, rhs.getAST];
  Z3_ast r = Z3_mk_distinct(lhs.context(), 2, args.ptr);
  lhs.checkError();
  return BoolExpr(lhs.context(), r);
}

// // friend expr operator!=(expr & a, int b);
// BoolExpr neq()(auto ref BvExpr a, int b) {
//   assert (a.isArith() || a.isBv() || a.isFpa());
//   return neq(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator!=(int a, expr & b);
// BoolExpr neq()(int a, auto ref BvExpr b) {
//   assert(b.isArith() || b.isBv() || b.isFpa());
//   return neq(bvNumVal(b.context(), a).byRef, b);
// }



// friend expr sum(expr_vector const& args);
BvExpr sum()(auto ref BvExprVector args) {
  assert (args.size() > 0);
  Context ctx = args.context();
  Z3_ast[] _args = args.toArray!Z3_ast();
  Z3_ast r = Z3_mk_add(args.context(), cast(uint) _args.length, _args.ptr);
  args.checkError();
  return BvExpr(args.context(), r);
}


// friend expr operator*(expr & a, expr & b);
BvExpr mul()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_bvmul(lhs.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

// // friend expr operator*(expr & a, int b);
// BvExpr mul()(auto ref BvExpr a, int b) {
//   return mul(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator*(int a, expr & b);
// BvExpr mul()(int a, auto ref BvExpr b) {
//   return mul(bvNumVal(b.context(), a).byRef, b);
// }

// /*  \brief Power operator  */
// friend expr pw(expr & a, expr & b);
BvExpr pw()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_power(lhs.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r);
}

// // friend expr pw(expr & a, int b);
// BvExpr pw()(auto ref BvExpr a, int b) {
//   return pw(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr pw(int a, expr & b);
// BvExpr pw()(int a, auto ref BvExpr b) {
//   return pw(bvNumVal(b.context(), a).byRef, b);
// }

// /* \brief mod operator */
// friend expr mod(expr const& a, expr const& b);
BvExpr mod()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_bvsmod(lhs.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r);
}

// // friend expr mod(expr const& a, int b);
// BvExpr mod()(auto ref BvExpr a, int b) {
//   return mod(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr mod(int a, expr const& b);
// BvExpr mod()(int a, auto ref BvExpr b) {
//   return mod(bvNumVal(b.context(), a).byRef, b);
// }


// /* \brief rem operator */
// friend expr rem(expr const& a, expr const& b);
BvExpr rem()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r;
  if (signed) r = Z3_mk_bvsrem(a.context(), lhs.getAST, rhs.getAST);
  else        r = Z3_mk_bvurem(a.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

// // friend expr rem(expr const& a, int b);
// BvExpr rem()(auto ref BvExpr a, int b) {
//   return rem(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr rem(int a, expr const& b);
// BvExpr rem()(int a, auto ref BvExpr b) {
//   return rem(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr operator/(expr & a, expr & b);
BvExpr div()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r;
  if (signed) r = Z3_mk_bvsdiv(a.context(), lhs.getAST, rhs.getAST);
  else        r = Z3_mk_bvudiv(a.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

// // friend expr operator/(expr & a, int b);
// BvExpr div()(auto ref BvExpr a, int b) {
//   return div(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator/(int a, expr & b);
// BvExpr div()(int a, auto ref BvExpr b) {
//   return div(bvNumVal(b.context(), a).byRef, b);
// }

BvExpr compliment()(auto ref BvExpr a) {
  Z3_ast r = Z3_mk_bvnot(a.context(), a.getAST);
  a.checkError();
  return BvExpr(a.context(), r, a._signed);
}

// friend expr operator-(expr & a);
BvExpr neg()(auto ref BvExpr a) {
  Z3_ast r = Z3_mk_bvneg(a.context(), a.getAST);
  a.checkError();
  return BvExpr(a.context(), r, a._signed);
}

// friend expr operator+(expr & a, expr & b);
BvExpr add()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_bvadd(lhs.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

// // friend expr operator+(expr & a, int b);
// BvExpr add()(auto ref BvExpr a, int b) {
//   return add(a, bvNumVal(a.context(), b).byRef);
// }
    
// // friend expr operator+(int a, expr & b);
// BvExpr add()(int a, auto ref BvExpr b) {
//   return add(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr operator-(expr & a, expr & b);
BvExpr sub()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_bvsub(lhs.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

// // friend expr operator-(expr & a, int b);
// BvExpr sub()(auto ref BvExpr a, int b) {
//   return sub(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator-(int a, expr & b);
// BvExpr sub()(int a, auto ref BvExpr b) {
//   return sub(bvNumVal(b.context(), a).byRef, b);
// }


BvExpr lsh()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_bvshl(lhs.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

BvExpr rsh()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r;
  if (signed) r = Z3_mk_bvashr(a.context(), lhs.getAST, rhs.getAST);
  else        r = Z3_mk_bvlshr(a.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

BvExpr lrsh()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = Z3_mk_bvlshr(a.context(), lhs.getAST, rhs.getAST);
  lhs.checkError();
  return BvExpr(lhs.context(), r, signed);
}

// friend expr operator<=(expr & a, expr & b);
BoolExpr le()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = null;
  if (signed) r = Z3_mk_bvsle(a.context(), lhs.getAST, rhs.getAST);
  else        r = Z3_mk_bvule(a.context(), lhs.getAST, rhs.getAST);
  a.checkError();
  return BoolExpr(a.context(), r);
}

// // friend expr operator<=(expr & a, int b);
// BoolExpr le()(auto ref BvExpr a, int b) {
//   return le(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator<=(int a, expr & b);
// BoolExpr le()(int a, auto ref BvExpr b) {
//   return le(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr operator>=(expr & a, expr & b);
BoolExpr ge()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = null;
  if (signed) r = Z3_mk_bvsge(a.context(), lhs.getAST, rhs.getAST);
  else        r = Z3_mk_bvuge(a.context(), lhs.getAST, rhs.getAST);
  a.checkError();
  return BoolExpr(a.context(), r);
}

// // friend expr operator>=(expr & a, int b);
// BoolExpr ge()(auto ref BvExpr a, int b) {
//   return ge(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator>=(int a, expr & b);
// BoolExpr ge()(int a, auto ref BvExpr b) {
//   return ge(bvNumVal(b.context(), a).byRef, b);
// }


// friend expr operator<(expr & a, expr & b);
BoolExpr lt()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = null;
  if (signed) r = Z3_mk_bvslt(a.context(), lhs.getAST, rhs.getAST);
  else        r = Z3_mk_bvult(a.context(), lhs.getAST, rhs.getAST);
  a.checkError();
  return BoolExpr(a.context(), r);
}

// // friend expr operator<(expr & a, int b);
// BoolExpr lt()(auto ref BvExpr a, int b) {
//   return lt(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator<(int a, expr & b);
// BoolExpr lt()(int a, auto ref BvExpr b) {
//   return lt(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr operator>(expr & a, expr & b);
BoolExpr gt()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  Z3_ast r = null;
  if (signed) r = Z3_mk_bvsgt(a.context(), lhs.getAST, rhs.getAST);
  else        r = Z3_mk_bvugt(a.context(), lhs.getAST, rhs.getAST);
  a.checkError();
  return BoolExpr(a.context(), r);
}

// // friend expr operator>(expr & a, int b);
// BoolExpr gt()(auto ref BvExpr a, int b) {
//   return gt(a, bvNumVal(a.context(), b).byRef);
// }

// // friend expr operator>(int a, expr & b);
// BoolExpr gt()(int a, auto ref BvExpr b) {
//   return gt(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr pble(expr_vector const& es, int * coeffs, int bound);
BoolExpr pble()(auto ref BvExprVector es, int* coeffs, int bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_pble(es.context(), cast(uint) _es.length, _es.ptr, coeffs, bound);
  es.context.checkError();
  return BoolExpr(es.context(), r);
}

// friend expr pbge(expr_vector const& es, int * coeffs, int bound);
BoolExpr pbge()(auto ref BvExprVector es, int* coeffs, int bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_pbge(es.context(), cast(uint) _es.length, _es.ptr, coeffs, bound);
  es.context.checkError();
  return BoolExpr(es.context(), r);
}

// friend expr pbeq(expr_vector const& es, int * coeffs, int bound);
BoolExpr pbeq()(auto ref BvExprVector es, int* coeffs, int bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_pbeq(es.context(), cast(uint) _es.length, _es.ptr, coeffs, bound);
  es.context.checkError();
  return BoolExpr(es.context(), r);
}

// friend expr atmost(expr_vector const& es, uint bound);
BoolExpr atmost()(auto ref BvExprVector es, uint bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_atmost(es.context(), cast(uint) _es.length, _es.ptr, bound);
  es.context.checkError();
  return BoolExpr(es.context(), r);
}

// friend expr atleast(expr_vector const& es, uint bound);
BoolExpr atleast()(auto ref BvExprVector es, uint bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_atleast(es.context(), cast(uint) _es.length, _es.ptr, bound);
  es.context.checkError();
  return BoolExpr(es.context(), r);
}

// friend expr operator&(expr & a, expr & b);
BvExpr bvand()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvand(a.context(), lhs, rhs);
  return BvExpr(a.context(), r, signed);
}

// // friend expr operator&(expr & a, int b);
// BvExpr bvand()(auto ref BvExpr a, int b) {
//   return bvand(a, bvNumVal(a.context(), b).byRef);
// }
// // friend expr operator&(int a, expr & b);
// BvExpr bvand()(int a, auto ref BvExpr b) {
//   return bvand(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr operator^(expr & a, expr & b);
BvExpr bvor()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvor(a.context(), lhs, rhs);
  return BvExpr(a.context(), r, signed);
}


// // friend expr operator^(expr & a, int b);
// BvExpr bvxor()(auto ref BvExpr a, int b) {
//   return bvxor(a, bvNumVal(a.context(), b).byRef);
// }
// // friend expr operator^(int a, expr & b);
// BvExpr bvXor()(int a, auto ref BvExpr b) {
//   return bvxor(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr operator|(expr & a, expr & b);
BvExpr bvxor()(auto ref BvExpr a, auto ref BvExpr b) {
  BvExpr lhs, rhs;
  bool signed = promoteToCommonType(a, b, lhs, rhs);
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvxor(a.context(), lhs, rhs);
  return BvExpr(a.context(), r, signed);
}


// // friend expr operator|(expr & a, int b);
// BvExpr bvor()(auto ref BvExpr a, int b) {
//   return bvor(a, bvNumVal(a.context(), b).byRef);
// }
// // friend expr operator|(int a, expr & b);
// BvExpr bvor()(int a, auto ref BvExpr b) {
//   return bvor(bvNumVal(b.context(), a).byRef, b);
// }

// friend expr nand(expr const& a, expr const& b);
BvExpr bvnand()(auto ref BvExpr a, auto ref BvExpr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvnand(a.context(), a.getAST, b.getAST);
  return BvExpr(a.context(), r);
}
// friend expr nor(expr const& a, expr const& b);
BvExpr bvnor()(auto ref BvExpr a, auto ref BvExpr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvnor(a.context(), a.getAST, b.getAST);
  return BvExpr(a.context(), r);
}
// friend expr xnor(expr const& a, expr const& b);
BvExpr bvxnor()(auto ref BvExpr a, auto ref BvExpr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvxnor(a.context(), a.getAST, b.getAST);
  return BvExpr(a.context(), r);
}

// friend expr min(expr const& a, expr const& b);
BvExpr min()(auto ref BvExpr a, auto ref BvExpr b) { 
  checkContext(a, b); 
  Z3_ast r = Z3_mk_ite(a.context(), Z3_mk_bvuge(a.context(), a.getAST, b.getAST), b.getAST, a.getAST);
  return BvExpr(a.context(), r); 
}

// friend expr max(expr const& a, expr const& b);
BvExpr max()(auto ref BvExpr a, auto ref BvExpr b) { 
  checkContext(a, b); 
  Z3_ast r = Z3_mk_ite(a.context(), Z3_mk_bvuge(a.context(), a.getAST, b.getAST), a.getAST, b.getAST);
  return BvExpr(a.context(), r); 
}

struct BoolExpr
{
  mixin RvalueRef;
  
  AST _ast;

  this(Context c) {
    _ast = AST(c);
  }

  this(Context c, string name, bool fresh=false) {
    Z3_ast r;
    if (fresh) r = Z3_mk_fresh_const(c, name.toStringz(), c.boolSort());
    else r = Z3_mk_const(c, c.strSymbol(name), c.boolSort());
    c.checkError();
    _ast = AST(c, r);
  }
  
  this(Context c, Z3_ast n) {
    _ast = AST(c, n);
  }

  this(Context c, bool val) {
      this(c, val ? Z3_mk_true(c) : Z3_mk_false(c));
  }
  
  this(this) { }
  
  // this(ref return scope BoolExpr rhs) {
  //   _ast = AST(rhs._ast);
  // }

  bool isNull() {
    return _ast.isNull();
  }

  BoolExpr opAssign(ref return scope BoolExpr rhs) {
    _ast = rhs._ast;
    return this;
  }


  void setContext(Context ctx) {
    _ast.setContext(ctx);
  }
  Context context() {
    return _ast.context();
  }
  Z3_error_code checkError()  {
    return _ast.checkError();
  }

  T opCast(t)() if (is (T == Z3_ast)) {
    return _ast.m_ast;
  }

  Z3_ast getAST() {
    return _ast.m_ast;
  }
  
  alias getAST this;

  Z3_ast_kind kind() {
    return _ast.kind();
  }

  Z3_ast opCast(T)() if (is (T == Z3_ast)) {
    return _ast.m_ast;
  }
  
  /**
     \brief Return the sort of this expression.
  */
  Sort getSort() {
    Z3_sort s = Z3_get_sort(context(), _ast.m_ast);
    checkError();
    return Sort(context(), s);
  }

  /**
     \brief Return true if this expression is an application.
  */
  bool isApp() {
    return kind() == Z3_ast_kind.Z3_APP_AST || kind() == Z3_ast_kind.Z3_NUMERAL_AST;
  }
  /**
     \brief Return true if this expression is a constant (i.e., an application with 0 arguments).
  */
  bool isConst() {
    return isApp() && numArgs() == 0;
  }
  /**
     \brief Return true if this expression is a quantifier.
  */
  bool isQuantifier() {
    return kind() == Z3_ast_kind.Z3_QUANTIFIER_AST;
  }

  /**
     \brief Return true if this expression is a universal quantifier.
  */
  bool isForall() {
    return Z3_is_quantifier_forall(context(), getAST);
  }
  /**
     \brief Return true if this expression is an existential quantifier.
  */
  bool isExists() {
    return Z3_is_quantifier_exists(context(), getAST);
  }
  /**
     \brief Return true if this expression is a lambda expression.
  */
  bool isLambda() {
    return Z3_is_lambda(context(), getAST);
  }
  /**

     \brief Return true if this expression is a variable.
  */
  bool isVar() {
    return kind() == Z3_ast_kind.Z3_VAR_AST;
  }
  /**
     \brief Return true if this expression is well sorted (aka type correct).
  */
  bool isWellSorted() {
    bool r = Z3_is_well_sorted(context(), getAST);
    checkError();
    return r;
  }

  /**
     \brief retrieve unique identifier for expression.
  */
  uint id() {
    uint r = Z3_get_ast_id(context(), getAST);
    checkError();
    return r;
  }

  Z3_lbool boolValue() {
    return Z3_get_bool_value(context(), getAST);
  }

  T opCast(T)() if (is (T == Z3_app)) {
    assert (isApp());
    return cast (Z3_app) this;
  }
  
  Z3_app getApp() {
    assert (isApp());
    return cast (Z3_app) this;
  }


  /**
     \brief Return the declaration associated with this application.
     This method assumes the expression is an application.

     \pre is_app()
  */
  FuncDecl decl() {
    Z3_func_decl f = Z3_get_app_decl(context(), cast(Z3_app) this);
    checkError();
    return FuncDecl(context(), f);
  }
  /**
     \brief Return the number of arguments in this application.
     This method assumes the expression is an application.

     \pre is_app()
  */
  uint numArgs() {
    uint r = Z3_get_app_num_args(context(), cast(Z3_app) this);
    checkError();
    return r;
  }
  /**
     \brief Return the i-th argument of this application.
     This method assumes the expression is an application.

     \pre is_app()
     \pre i < num_args()
  */
  BoolExpr arg(uint i) {
    Z3_ast r = Z3_get_app_arg(context(), cast(Z3_app) this, i);
    checkError();
    return BoolExpr(context(), r);
  }

  /**
     \brief Return the 'body' of this quantifier.

     \pre is_quantifier()
  */
  BoolExpr body() {
    assert (isQuantifier());
    Z3_ast r = Z3_get_quantifier_body(context(), getAST);
    checkError();
    return BoolExpr(context(), r);
  }

  bool isTrue() {
    return isApp() && Z3_decl_kind.Z3_OP_TRUE == decl().declKind();
  }
  bool isFalse() {
    return isApp() && Z3_decl_kind.Z3_OP_FALSE == decl().declKind();
  }
  bool isNot() {
    return isApp() && Z3_decl_kind.Z3_OP_NOT == decl().declKind();
  }
  bool isAnd() {
    return isApp() && Z3_decl_kind.Z3_OP_AND == decl().declKind();
  }
  bool isOr()  {
    return isApp() && Z3_decl_kind.Z3_OP_OR  == decl().declKind();
  }
  bool isXor() {
    return isApp() && Z3_decl_kind.Z3_OP_XOR  == decl().declKind();
  }
  bool isImplies() {
    return isApp() && Z3_decl_kind.Z3_OP_IMPLIES  == decl().declKind();
  }
  bool isEq() {
    return isApp() && Z3_decl_kind.Z3_OP_EQ == decl().declKind();
  }
  bool isIte() {
    return isApp() && Z3_decl_kind.Z3_OP_ITE == decl().declKind();
  }
  bool isDistinct() {
    return isApp() && Z3_decl_kind.Z3_OP_DISTINCT == decl().declKind();
  }

        
  /**
     \brief Return a simplified version of this expression.
  */
  BoolExpr simplify() {
    Z3_ast r = Z3_simplify(context(), getAST);
    checkError();
    return BoolExpr(context(), r);
  }
  /**
     \brief Return a simplified version of this expression. The parameter \c p is a set of parameters for the Z3 simplifier.
  */
  BoolExpr simplify()(auto ref Params p) {
    Z3_ast r = Z3_simplify_ex(context(), getAST, p);
    checkError();
    return BoolExpr(context(), r);
  }

  /**
     \brief Apply substitution. Replace src expressions by dst.
  */

  BoolExpr substitute()(auto ref BoolExprVector src, auto ref BoolExprVector dst) {
    assert (src.size() == dst.size());
    Z3_ast[] _src = new Z3_ast[](src.size());
    Z3_ast[] _dst = new Z3_ast[](dst.size());
    for (uint i = 0; i < src.size(); ++i) {
      _src[i] = src[i].getAST;
      _dst[i] = dst[i].getAST;
    }
    Z3_ast r = Z3_substitute(context(), getAST, src.size(), _src.ptr, _dst.ptr);
    checkError();
    return BoolExpr(context(), r);
  }

  /**
     \brief Apply substitution. Replace bound variables by expressions.
  */

  BoolExpr substitute()(auto ref BoolExprVector dst) {
    Z3_ast[] _dst = new Z3_ast[](dst.size());
    for (uint i = 0; i < dst.size(); ++i) {
      _dst[i] = dst[i].getAST;
    }
    Z3_ast r = Z3_substitute_vars(context(), getAST, dst.size(), _dst.ptr);
    checkError();
    return BoolExpr(context(), r);
  }

  BoolExpr opUnary(string op)() if(op == "!") {
    Z3_ast r = Z3_mk_not(this.context, getAST);
    this.checkError();
    return BoolExpr(this.context(), r);
  }

  static BoolExpr castAST(Context c, Z3_ast a) {
    assert (Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_NUMERAL_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_APP_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_QUANTIFIER_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_VAR_AST);
    return BoolExpr(c, a);
  }
}

BoolExpr boolVal(Context c, bool val) {
  return BoolExpr(c, val);
}

void addRule()(auto ref Solver solver, auto ref BoolExpr e) {
  Z3_solver_assert(solver.context(), solver, e.getAST);
  solver.checkError();
}

void addRule()(auto ref Solver solver, auto ref BoolExpr e, auto ref BoolExpr p) {
  assert (p.isConst());
  Z3_solver_assert_and_track(context(), solver, e.getAST, p.getAST);
  solver.checkError();
}

void addRule()(auto ref Solver solver, auto ref BoolExpr e, string p) {
  addRule(solver, e, solver.context().boolConst(p).byRef);
}

void addRule()(auto ref Optimize optimize, auto ref BoolExpr e) {
  Z3_optimize_assert(optimize.context(), optimize, e.getAST);
  optimize.checkError();
}

void addRule()(auto ref Optimize optimize, auto ref BoolExpr e, uint weight) {
  import std.conv: to;
  Z3_optimize_assert_soft(optimize.context(), optimize, e.getAST,
			  weight.to!string.toStringz, null);
  optimize.checkError();
}

void addRule()(auto ref Optimize optimize, auto ref BoolExpr e,
	       uint weight, string id) {
  import std.conv: to;
  Z3_optimize_assert_soft(optimize.context(), optimize, e.getAST,
			  weight.to!string.toStringz,
			  optimize.context().strSymbol(id));
  optimize.checkError();
}

void addRule()(auto ref Optimize optimize, auto ref BoolExpr e, auto ref BoolExpr p) {
  assert (p.isConst());
  Z3_optimize_assert_and_track(context(), optimize, e.getAST, p.getAST);
  optimize.checkError();
}

void addRule()(auto ref Optimize optimize, auto ref BoolExpr e, string p) {
  addRule(optimize, e, optimize.context().boolConst(p).byRef);
}

// friend expr ite(expr & c, expr & t, expr & e);
BoolExpr ite()(auto ref BoolExpr c, auto ref BoolExpr t, auto ref BoolExpr e) {
  checkContext(c, t); checkContext(c, e);
  Z3_ast r = Z3_mk_ite(c.context, c.getAST, t.getAST, e.getAST);
  c.checkError();
  return BoolExpr(c.context(), r);
}

BoolExpr and()(auto ref BoolExpr a, auto ref BoolExpr b) {
  checkContext(a, b);
  Z3_ast[2] args = [a.getAST, b.getAST];
  Z3_ast r = Z3_mk_and(a.context(), 2, args.ptr);
  a.checkError();
  return BoolExpr(a.context(), r);
}
  
BoolExpr and(BoolExpr[] arr ...) {
  // checkContext(a, b);
  Z3_ast[] asts;
  foreach (ref a; arr) {
    asts ~= a.getAST;
  }
  Z3_ast r = Z3_mk_and(arr[0].context(), cast(uint) asts.length, asts.ptr);
  arr[0].checkError();
  return BoolExpr(arr[0].context(), r);
}
  
BoolExpr or()(auto ref BoolExpr a, auto ref BoolExpr b) {
  checkContext(a, b);
  Z3_ast[2] args = [a.getAST, b.getAST];
  Z3_ast r = Z3_mk_or(a.context(), 2, args.ptr);
  a.checkError();
  return BoolExpr(a.context(), r);
}
  
BoolExpr or(BoolExpr[] arr ...) {
  // checkContext(a, b);
  Z3_ast[] asts;
  foreach (ref a; arr) {
    asts ~= a.getAST;
  }
  Z3_ast r = Z3_mk_or(arr[0].context(), cast(uint) asts.length, asts.ptr);
  arr[0].checkError();
  return BoolExpr(arr[0].context(), r);
}
  
BoolExpr xor()(auto ref BoolExpr a, auto ref BoolExpr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_xor(a.context(), a.getAST, b.getAST);
  a.checkError();
  return BoolExpr(a.context(), r);
}
  
BoolExpr not()(auto ref BoolExpr a) {
  Z3_ast r = Z3_mk_not(a.context(), a.getAST);
  a.checkError();
  return BoolExpr(a.context(), r);
}

// friend expr implies(expr & a, expr & b);
BoolExpr implies()(auto ref BoolExpr a, auto ref BoolExpr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_implies(a.context(), a.getAST, b.getAST);
  a.checkError();
  return BoolExpr(a.context(), r);
}

BoolExpr z3True(Context c) {
  return BoolExpr(c, Z3_mk_true(c));
}

BoolExpr z3False(Context c) {
  return BoolExpr(c, Z3_mk_false(c));
}


void fullAdder()(auto ref BoolExpr a, auto ref BoolExpr b, auto ref BoolExpr cin,
		 out BoolExpr sum, out BoolExpr cout) {
  BoolExpr cout_ = or(and(a, b), and(a, cin), and(b, cin));
  BoolExpr sum_ = xor(xor(a, b), cin);
  cout = cout_;
  sum = sum_;
}

void adder(Context cxt, BoolExpr[] a, BoolExpr[] b, BoolExpr[] result) {
  BoolExpr cin = z3False(cxt);
  BoolExpr cout;

  assert(a.length == b.length);

  // result is assumed to be of right size
  // result.length = a.length + 1;

  for (size_t i=0; i!=a.length; ++i) {
    fullAdder(a[i], b[i], cin, result[i], cout);
    cin = cout;
  }
  result[$-1] = cout;
}

void addPairs(Context cxt, uint numBits, uint numIns, BoolExpr[] bits,
	      ref uint outNum, BoolExpr[] outBits) {
  uint outNumBits = numBits + 1;
  size_t inCursor = 0;
  size_t outCursor = 0;
  outNum = (numIns + 1) / 2;
  // assert (bits.length == numBits*numIns*2);
  for (uint i=0; i != numIns/2; ++i) {
    adder(cxt,
	  bits[inCursor..inCursor+numBits], bits[inCursor+numBits..inCursor+2*numBits],
	  outBits[outCursor..outCursor+outNumBits]);
    inCursor += 2*numBits;
    outCursor += outNumBits;
  }
  if (numIns % 2 != 0) {
    for (uint i=0; i!=numBits; ++i) {
      outBits[outCursor+i] = bits[inCursor+i];
    }
    BoolExpr false_ = z3False(cxt);
    outBits[outCursor+numBits] = false_;
  }
}

BoolExpr[] countOnes(Context cxt, BoolExpr[] lits) {
  uint numIns = cast(uint) lits.length;
  uint numBits = 1;
  BoolExpr[] aux1;
  BoolExpr[] aux2;
  if (lits.length == 0) return [];

  aux1 = lits.dup();
  aux1.length = lits.length + 1;
  aux2.length = lits.length + 1;

  while (numIns > 1) {
    uint newNumIns;
    addPairs(cxt, numBits, numIns, aux1, newNumIns, aux2);
    numIns = newNumIns;
    numBits += 1;
    debug(MAXSAT) {
      import std.stdio;
      writeln("numBits: ", numBits, " numIns: ", numIns);
      for (size_t i=0; i!=numIns*numBits; ++i) {
	writeln("bit ", i, ": ", aux2[i]._ast.toString()); 
      }
      wrintln("---------------------");
    }
    BoolExpr[] tmp = aux1;
    aux1 = aux2;
    aux2 = tmp;
  }
  
  return aux1[0..numBits];
}

bool getBit(uint val, uint idx) {
  uint mask = 1 << (idx & 31);
  return (val & mask) != 0;
}

bool getBit(ulong val, uint idx) {
  ulong mask = 1 << (idx & 63);
  return (val & mask) != 0;
}

void le(Solver s, BoolExpr[] val, uint k) {
  Context cxt = s.context();
  
  BoolExpr i1, i2, rule;

  BoolExpr notVal = not(val[0]);
  
  BoolExpr true_ = z3True(cxt);
  if (getBit(k, 0)) rule = true_;
  else rule = notVal;

  for (uint idx=0; idx!=val.length; ++idx) {
    BoolExpr notVal_ = not(val[idx]);
    notVal = notVal_;
    if (getBit(k, idx)) {
      i1 = notVal;
      i2 = rule;
    }
    else {
      BoolExpr false1 =  z3False(cxt);
      BoolExpr false2 = z3False(cxt);
      i1 = false1;
      i2 = false2;
    }
    BoolExpr rule_ = or(i1, i2, and(notVal, rule));
    rule = rule_;
  }

  s.addRule(rule);
}

void atMostK(Solver s, BoolExpr[] lits, uint k) {
  if (k >= lits.length || lits.length <= 1) return;
  BoolExpr[] count = countOnes(s.context(), lits);
  le(s, count, k);
}

void atMost1(Solver s, BoolExpr[] lits) {
  atMostK(s, lits, 1);
}

void testAtMost1() {
  import std.stdio;

  Config cfg = new Config();
  cfg.set("MODEL", true);
  Context ctx = new Context(cfg);

  Solver s = Solver(ctx);

  BoolExpr k1 = BoolExpr(ctx, "k1");
  BoolExpr k2 = BoolExpr(ctx, "k2");
  BoolExpr k3 = BoolExpr(ctx, "k3");
  BoolExpr k4 = BoolExpr(ctx, "k4");
  BoolExpr k5 = BoolExpr(ctx, "k5");
  BoolExpr k6 = BoolExpr(ctx, "k6");

  BoolExpr[] args1 = [k1, k2, k3, k4, k5];
  BoolExpr[] args2 = [k4, k5, k6];
  writeln("testing at-most-one constraint");

  atMost1(s, args1);
  atMost1(s, args2);

  writeln("It must be sat...");

  auto result = s.check();
  writeln("result is: ", result);

  auto model = s.getModel();
  writeln("Model: ", model);

  s.addRule(or(k2, k3));
  s.addRule(or(k1, k6));

  writeln("It must be sat...");

  result = s.check();
  writeln("result is: ", result);
  
  auto model2 = s.getModel();
  writeln("Model: ", model2);

  s.addRule(or(k4, k5));

  writeln("It must be unsat...");

  result = s.check();
  writeln("result is: ", result);
}

