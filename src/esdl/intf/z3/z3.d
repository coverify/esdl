module esdl.intf.z3.z3;

import esdl.intf.z3.api;
import std.string: toStringz;
import core.stdc.string: strlen;

import std.traits: isIntegral, isBoolean;
import std.stdio;


mixin template RvalueRef()
{
  alias T = typeof (this); // typeof(this) get us the type we're in
  static assert (is (T == struct));

  @nogc @safe
  ref T byRef() pure nothrow return
  {
    return this;
  }
}

string getParam(string param) {
  char* vala;
  if (Z3_global_param_get(param.toStringz,
			  cast(const(char*)*) (&(vala)))) {
    return cast(string) vala[0..vala.strlen()];
  }
  else {
    return "";
  }
}

void setParam(string param, string value) {
  Z3_global_param_set(param.toStringz, value.toStringz);
}

void setParam(string param, bool value) {
  Z3_global_param_set(param.toStringz, value ? "true" : "false");
}

void setParam(string param, int value) {
  import std.conv: to;
  Z3_global_param_set(param.toStringz, value.to!string.toStringz);
}

void resetParams() {
  Z3_global_param_reset_all();
}

static class Z3Exception: Throwable
{
  this(string err="Unknown Exception") {
    super(err);
  }
}


/**
   \brief Z3 global configuration object.
*/
class Config
{
  Z3_config    _m_cfg;

  alias _m_cfg this;

  this() {
    _m_cfg = Z3_mk_config();
  }

  ~this() {
    Z3_del_config(_m_cfg);
  }
  
  /**
     \brief Set global parameter \c param with string \c value.
  */
  void set(string param, string value) {
    Z3_set_param_value(_m_cfg, param.toStringz, value.toStringz);
  }
  /**
     \brief Set global parameter \c param with Boolean \c value.
  */
  void set(string param, bool value) {
    Z3_set_param_value(_m_cfg, param.toStringz, value ? "true" : "false");
  }
  /**
     \brief Set global parameter \c param with integer \c value.
  */
  void set(string param, int value) {
    import std.conv: to;
    Z3_set_param_value(_m_cfg, param.toStringz, value.to!string.toStringz);
  }
}

enum CheckResult: ubyte { UNSAT, SAT, UNKNOWN }

enum RoundingMode: ubyte { RNA, RNE, RTP, RTN, RTZ }

CheckResult toCheckResult(Z3_lbool l) {
  if (l == Z3_lbool.Z3_L_TRUE) return CheckResult.SAT;
  else if (l == Z3_lbool.Z3_L_FALSE) return CheckResult.UNSAT;
  return CheckResult.UNKNOWN;
}

/**
   \brief A Context manages all other Z3 objects, global configuration options, etc.
*/


class Context
{
  bool       _m_enable_exceptions;
  RoundingMode _m_rounding_mode;
  Z3_context _m_ctx;

  alias _m_ctx this;
  
  private void init(Config c) {
    _m_ctx = Z3_mk_context_rc(c);
    _m_enable_exceptions = true;
    _m_rounding_mode = RoundingMode.RNA;
    Z3_set_error_handler(_m_ctx, null);
    Z3_set_ast_print_mode(_m_ctx, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
  }

  this() {
    Config c = new Config();
    init(c);
  }

  this(Config c) {
    init(c);
  }

  ~this() {
    Z3_del_context(_m_ctx);
  }

  /**
     \brief Auxiliary method used to check for API usage errors.
  */
  Z3_error_code checkError() {
    Z3_error_code e = Z3_get_error_code(_m_ctx);
    if (e != Z3_error_code.Z3_OK && enableExceptions()) {
      auto msg = Z3_get_error_msg(_m_ctx, e);
      throw new Z3Exception(cast(string) msg[0..msg.strlen()]);
    }
    return e;
  }

  void checkParserError() {
    checkError();
  }

  /**
     \brief The C++ API uses by defaults exceptions on errors.
     For applications that don't work well with exceptions (there should be only few)
     you have the ability to turn off exceptions. The tradeoffs are that applications
     have to be very careful about using checkError() after calls that may result in an
     erroneous state.
  */
  void setEnableExceptions(bool f) {
    _m_enable_exceptions = f;
  }

  bool enableExceptions() const {
    return _m_enable_exceptions;
  }

  /**
     \brief Update global parameter \c param with string \c value.
  */
  void set(string param, string value) {
    Z3_update_param_value(_m_ctx, param.toStringz, value.toStringz);
  }
  /**
     \brief Update global parameter \c param with Boolean \c value.
  */
  void set(string param, bool value) {
    Z3_update_param_value(_m_ctx, param.toStringz, value ? "true" : "false"); }
  /**
     \brief Update global parameter \c param with Integer \c value.
  */
  void set(string param, int value) {
    import std.conv: to;
    Z3_update_param_value(_m_ctx, param.toStringz, value.to!string.toStringz);
  }

  /**
     \brief Interrupt the current procedure being executed by any object managed by this context.
     This is a soft interruption: there is no guarantee the object will actually stop.
  */
  void interrupt() {
    Z3_interrupt(_m_ctx);
  }

  // TODO
  /**
     \brief Create a Z3 symbol based on the given string.
  */
  Symbol strSymbol(string s) {
    Z3_symbol r = Z3_mk_string_symbol(_m_ctx, s.toStringz);
    checkError();
    return Symbol(this, r);
  }
  /**
     \brief Create a Z3 symbol based on the given integer.
  */
  Symbol intSymbol(int n) {
    Z3_symbol r = Z3_mk_int_symbol(_m_ctx, n);
    checkError();
    return Symbol(this, r);
  }
  /**
     \brief Return the Boolean sort.
  */
  Sort boolSort() {
    Z3_sort s = Z3_mk_bool_sort(_m_ctx);
    checkError();
    return Sort(this, s);
  }
  /**
     \brief Return the integer sort.
  */
  Sort intSort() {
    Z3_sort s = Z3_mk_int_sort(_m_ctx);
    checkError();
    return Sort(this, s);
  }
  /**
     \brief Return the Real sort.
  */
  Sort realSort() {
    Z3_sort s = Z3_mk_real_sort(_m_ctx);
    checkError();
    return Sort(this, s);
  }
  /**
     \brief Return the Bit-vector sort of size \c sz. That is, the sort for bit-vectors of size \c sz.
  */
  Sort bvSort(uint sz) {
    Z3_sort s = Z3_mk_bv_sort(_m_ctx, sz);
    checkError();
    return Sort(this, s);
  }
  /**
     \brief Return the sort for ASCII strings.
  */
  Sort stringSort() {
    Z3_sort s = Z3_mk_string_sort(_m_ctx);
    checkError();
    return Sort(this, s);
  }
  /**
     \brief Return a sequence sort over base sort \c s.
  */
  Sort seqSort()(auto ref Sort s) {
    Z3_sort r = Z3_mk_seq_sort(_m_ctx, s);
    checkError();
    return Sort(this, r);
  }
  /**
     \brief Return a regular expression sort over sequences \c seq_sort.
  */
  Sort reSort()(auto ref Sort s) {
    Z3_sort r = Z3_mk_re_sort(_m_ctx, s);
    checkError();
    return Sort(this, r);
  }

  /**
     \brief Return an array sort for arrays from \c d to \c r.

     Example: Given a context \c c, <tt>c.array_sort(c.int_sort(), c.bool_sort())</tt> is an array sort from integer to Boolean.
  */

  Sort arraySort(Sort d, Sort r) {
    Z3_sort s = Z3_mk_array_sort(_m_ctx, d, r);
    checkError();
    return Sort(this, s);
  }

  Sort arraySort()(auto ref SortVector d, Sort r) {
    Z3_sort[] dom = d.toArray!Z3_sort();
    Z3_sort s = Z3_mk_array_sort_n(_m_ctx, cast(uint) dom.length, dom.ptr, r);
    checkError();
    return Sort(this, s);
  }

  /**
     \brief Return a floating point sort.
     \c ebits is a number of exponent bits,
     \c sbits	is a number of significand bits,
     \pre where ebits must be larger than 1 and sbits must be larger than 2.
  */
  Sort fpaSort(uint ebits, uint sbits) {
    Z3_sort s = Z3_mk_fpa_sort(_m_ctx, ebits, sbits);
    checkError();
    return Sort(this, s);
  }

  /**
     \brief Return a FloatingPoint sort with given precision bitwidth (16, 32, 64 or 128).
  */
  Sort fpaSort(int N)() {
    static if (N == 16) return fpaSort(5, 11);
    static if (N == 32) return fpaSort(8, 24);
    static if (N == 64) return fpaSort(11, 53);
    static if (N == 80) return fpaSort(15, 65);
    static if (N == 128) return fpaSort(15, 113);
  }

  /**
     \brief Return a RoundingMode sort.
  */

  Sort fpaRoundingMode() {
    switch (_m_rounding_mode) {
    case RoundingMode.RNA: return Sort(this, Z3_mk_fpa_rna(_m_ctx));
    case RoundingMode.RNE: return Sort(this, Z3_mk_fpa_rne(_m_ctx));
    case RoundingMode.RTP: return Sort(this, Z3_mk_fpa_rtp(_m_ctx));
    case RoundingMode.RTN: return Sort(this, Z3_mk_fpa_rtn(_m_ctx));
    case RoundingMode.RTZ: return Sort(this, Z3_mk_fpa_rtz(_m_ctx));
    default: return Sort(this); 
    }
  }
  /**
     \brief Sets RoundingMode of FloatingPoints.
  */
  void setRoundingMode(RoundingMode rm) {
    _m_rounding_mode = rm;
  }
  /**
     \brief Return an enumeration sort: enum_names[0], ..., enum_names[n-1].
     \c cs and \c ts are output parameters. The method stores in \c cs the constants corresponding to the enumerated elements,
     and in \c ts the predicates for testing if terms of the enumeration sort correspond to an enumeration.
  */
  Sort enumerationSort()(string name, string[] enum_names,
		       auto ref FuncDeclVector cs, auto ref FuncDeclVector ts) {
    Z3_symbol[] _enum_names = new Z3_symbol[](enum_names.length);
    for (uint i = 0; i != enum_names.length; ++i) {
      _enum_names[i] = Z3_mk_string_symbol(this, enum_names[i].toStringz);
    }
    Z3_func_decl[] _cs = new Z3_func_decl[](enum_names.length);
    Z3_func_decl[] _ts = new Z3_func_decl[](enum_names.length);
    Z3_symbol _name = Z3_mk_string_symbol(this, name.toStringz);
    Sort s = this.toSort(Z3_mk_enumeration_sort(this, _name, cast(uint) _enum_names.length,
						 _enum_names.ptr, _cs.ptr, _ts.ptr));
    checkError();
    for (uint i = 0; i != enum_names.length; ++i) {
      cs.pushBack(FuncDecl(this, _cs[i]).byRef);
      ts.pushBack(FuncDecl(this, _ts[i]).byRef);
    }
    return s;
  }

  /**
     \brief Return a tuple constructor.
     \c name is the name of the returned constructor,
     \c n are the number of arguments, \c names and \c sorts are their projected sorts.
     \c projs is an output parameter. It contains the set of projection functions.
  */

  FuncDecl tupleSort()(string name, string[] names, Sort[] sorts,
		     auto ref FuncDeclVector projs) {
    assert (sorts.length == names.length);
    Z3_symbol[] _names = new Z3_symbol[](names.length);
    Z3_sort[] _sorts = new Z3_sort[](sorts.length);
    for (uint i = 0; i != names.length; ++i) {
      _names[i] = Z3_mk_string_symbol(this, names[i].toStringz);
      _sorts[i] = sorts[i];
   }
    Z3_func_decl[] _projs = new Z3_func_decl[](_names.length);
    Z3_symbol _name = Z3_mk_string_symbol(this, name.toStringz);
    Z3_func_decl tuple;
    Sort _ignore_s = this.toSort(Z3_mk_tuple_sort(this, _name, cast(uint) _names.length, _names.ptr,
						   _sorts.ptr, &tuple, _projs.ptr));
    checkError();
    for (uint i = 0; i != names.length; ++i) {
      projs.pushBack(FuncDecl(this, _projs[i]).byRef);
    }
    return FuncDecl(this, tuple);
  }

  /**
     \brief create an uninterpreted sort with the name given by the string or symbol.
  */

  Sort uninterpretedSort(string name) {
    Z3_symbol _name = Z3_mk_string_symbol(this, name.toStringz);
    return toSort(this, Z3_mk_uninterpreted_sort(this, _name));
  }

  Sort uninterpretedSort(Symbol name) {
    return toSort(this, Z3_mk_uninterpreted_sort(this, name));
  }

  FuncDecl func()(auto ref Symbol name, Sort[] domain, auto ref Sort range) {
    Z3_sort[] args = new Z3_sort[](domain.length);
    for (uint i = 0; i < domain.length; i++) {
      checkContext(domain[i], range);
      args[i] = domain[i];
    }
    Z3_func_decl f = Z3_mk_func_decl(_m_ctx, name, cast(uint) args.length, args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl func()(string name, Sort[] domain, auto ref Sort range) {
    return func(range.context().strSymbol(name).byRef, domain, range);
  }

  FuncDecl func()(auto ref Symbol name, auto ref SortVector domain, auto ref Sort range) {
    Z3_sort[] args = new Z3_sort[](domain.length);
    for (uint i = 0; i != domain.size(); ++i) {
      checkContext(domain[i], range);
      args[i] = domain[i];
    }
    Z3_func_decl f = Z3_mk_func_decl(_m_ctx, name, domain.size(), args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl func()(string name, auto ref SortVector domain, auto ref Sort range) {
    return func(range.context().strSymbol(name).byRef, domain, range);
  }

  FuncDecl func()(string name, auto ref Sort domain, auto ref Sort range) {
    checkContext(domain, range);
    Z3_sort[1] args = [domain];
    Z3_func_decl f = Z3_mk_func_decl(_m_ctx, strSymbol(name), 1, args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort range) {
    checkContext(d1, range); checkContext(d2, range);
    Z3_sort[2] args = [d1, d2];
    Z3_func_decl f = Z3_mk_func_decl(_m_ctx, strSymbol(name), 2, args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort d3, auto ref Sort range) {
    checkContext(d1, range); checkContext(d2, range); checkContext(d3, range);
    Z3_sort[3] args = [d1, d2, d3];
    Z3_func_decl f = Z3_mk_func_decl(_m_ctx, strSymbol(name), 3, args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort d3, auto ref Sort d4, auto ref Sort range) {
    checkContext(d1, range); checkContext(d2, range); checkContext(d3, range); checkContext(d4, range);
    Z3_sort[4] args = [d1, d2, d3, d4];
    Z3_func_decl f = Z3_mk_func_decl(_m_ctx, strSymbol(name), 4, args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort d3, auto ref Sort d4, auto ref Sort d5, auto ref Sort range) {
    checkContext(d1, range); checkContext(d2, range); checkContext(d3, range); checkContext(d4, range); checkContext(d5, range);
    Z3_sort[5] args = [d1, d2, d3, d4, d5];
    Z3_func_decl f = Z3_mk_func_decl(_m_ctx, strSymbol(name), 5, args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl recfun()(Symbol name, Sort[] domain, auto ref Sort range) {
    Z3_sort[] args = new Z3_sort[](domain.length);
    for (uint i = 0; i < domain.length; i++) {
      checkContext(domain[i], range);
      args[i] = domain[i];
    }
    Z3_func_decl f = Z3_mk_rec_func_decl(_m_ctx, name, cast(uint) args.length, args.ptr, range);
    checkError();
    return FuncDecl(this, f);
  }

  FuncDecl recfun()(string name, Sort[] domain, auto ref Sort range) {
    return recfun(strSymbol(name), domain, range);
  }

  FuncDecl recfun()(string name, auto ref Sort d1, auto ref Sort range) {
    return recfun(strSymbol(name), [d1], range);
  }

  FuncDecl recfun()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort range) {
    Sort[] dom = [d1, d2];
    return recfun(strSymbol(name), dom, range);
  }

  void recdef()(FuncDecl f, auto ref ExprVector args, auto ref Expr body) {
    checkContext(f, args); checkContext(f, body);
    Z3_ast[] vars = args.toArray!Z3_ast;
    Z3_add_rec_def(f.context(), f, cast(uint) vars.length, vars.ptr, body.getAST);
  }

  // void      recdef(func_decl, expr_vector const& args, expr const& body);

  Expr constant()(Symbol name, auto ref Sort s) {
    Z3_ast r = Z3_mk_const(_m_ctx, name, s);
    checkError();
    return Expr(this, r);
  }

  Expr constant()(string name, auto ref Sort s) {
    return constant(strSymbol(name), s);
  }
  Expr boolConst(string name) {
    return constant(name, boolSort().byRef);
  }
  Expr intConst(string name) {
    return constant(name, intSort().byRef);
  }
  Expr realConst(string name) {
    return constant(name, realSort().byRef);
  }
  Expr bvConst(string name, uint sz) {
    return constant(name, bvSort(sz).byRef);
  }
  Expr fpaConst(string name, uint ebits, uint sbits) {
    return constant(name,  fpaSort(ebits, sbits).byRef);
  }
  Expr fpaConst(uint N)(string name) {
    return constant(name, fpaSort!N().byRef);
  }
  Expr boolVal(bool b) {
    return b ? Expr(this, Z3_mk_true(_m_ctx)):
      Expr(this, Z3_mk_false(_m_ctx));
  }
  Expr intVal(int n) {
    Z3_ast r = Z3_mk_int(_m_ctx, n, intSort());
    checkError();
    return Expr(this, r);
  }
  Expr intVal(uint n) {
    Z3_ast r = Z3_mk_unsigned_int(_m_ctx, n, intSort());
    checkError();
    return Expr(this, r);
  }
  Expr intVal(long n) {
    Z3_ast r = Z3_mk_int64(_m_ctx, n, intSort());
    checkError();
    return Expr(this, r);
  }
  Expr intVal(ulong n) {
    Z3_ast r = Z3_mk_unsigned_int64(_m_ctx, n, intSort());
    checkError();
    return Expr(this, r);
  }
  Expr intVal(string n) {
    Z3_ast r = Z3_mk_numeral(_m_ctx, n.toStringz, intSort());
    checkError();
    return Expr(this, r);
  }
  Expr realVal(int n, int d) {
    Z3_ast r = Z3_mk_real(_m_ctx, n, d);
    checkError();
    return Expr(this, r);
  }
  Expr realVal(int n) {
    Z3_ast r = Z3_mk_int(_m_ctx, n, realSort());
    checkError();
    return Expr(this, r);
  }
  Expr realVal(uint n) {
    Z3_ast r = Z3_mk_unsigned_int(_m_ctx, n, realSort());
    checkError();
    return Expr(this, r);
  }
  Expr realVal(long n) {
    Z3_ast r = Z3_mk_int64(_m_ctx, n, realSort());
    checkError();
    return Expr(this, r);
  }
  Expr realVal(ulong n) {
    Z3_ast r = Z3_mk_unsigned_int64(_m_ctx, n, realSort());
    checkError();
    return Expr(this, r);
  }
  Expr realVal(string n) {
    Z3_ast r = Z3_mk_numeral(_m_ctx, n.toStringz, realSort());
    checkError();
    return Expr(this, r);
  }

  Expr bvVal(int n, uint sz) {
    Sort s = bvSort(sz);
    Z3_ast r = Z3_mk_int(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
  }
  Expr bvVal(uint n, uint sz) {
    Sort s = bvSort(sz);
    Z3_ast r = Z3_mk_unsigned_int(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
  }
  Expr bvVal(long n, uint sz) {
    Sort s = bvSort(sz);
    Z3_ast r = Z3_mk_int64(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
  }
  Expr bvVal(ulong n, uint sz) {
    Sort s = bvSort(sz);
    Z3_ast r = Z3_mk_unsigned_int64(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
  }
  Expr bvVal(string n, uint sz) {
    Sort s = bvSort(sz);
    Z3_ast r = Z3_mk_numeral(_m_ctx, n.toStringz, s);
    checkError();
    return Expr(this, r);
  }
  Expr bvVal(bool[] bits) {
    Z3_ast r = Z3_mk_bv_numeral(_m_ctx, cast(uint) bits.length, bits.ptr);
    checkError();
    return Expr(this, r);
  }

  Expr fpaVal(real n) {
    Sort s = fpaSort!80();
    Z3_ast r = Z3_mk_fpa_numeral_double(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
  }
  Expr fpaVal(double n) {
    Sort s = fpaSort!64();
    Z3_ast r = Z3_mk_fpa_numeral_double(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
  }
  Expr fpaVal(float n) {
    Sort s = fpaSort!32();
    Z3_ast r = Z3_mk_fpa_numeral_float(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
  }

  Expr stringVal(string s, uint n) {
    Z3_ast r = Z3_mk_lstring(_m_ctx, n, s.toStringz);
    checkError();
    return Expr(this, r);
  }
  Expr stringVal(string s) {
    Z3_ast r = Z3_mk_string(_m_ctx, s.toStringz);
    checkError();
    return Expr(this, r);
  }
  Expr numVal()(int n, auto ref Sort s) {
    Z3_ast r = Z3_mk_int(_m_ctx, n, s);
    checkError();
    return Expr(this, r);
 }


  // /**
  //    \brief parsing
  // */
  // expr_vector parse_string(char const* s);
  // expr_vector parse_file(char const* file);

  ExprVector parseString(string s) {
    Z3_ast_vector r = Z3_parse_smtlib2_string(this, s.toStringz, 0, null, null, 0, null, null);
    checkError();
    return ExprVector(this, r);
  }
  
  ExprVector parseFile(string s) {
    Z3_ast_vector r = Z3_parse_smtlib2_file(this, s.toStringz, 0, null, null, 0, null, null);
    checkError();
    return ExprVector(this, r);
  }

  ExprVector parseString()(string s, auto ref SortVector sorts, auto ref FuncDeclVector decls) {
    Z3_symbol[] sort_names = new Z3_symbol[](sorts.size());
    Z3_symbol[] decl_names = new Z3_symbol[](decls.size());
    Z3_sort[]   sorts1; sorts1 = sorts.toArray!Z3_sort();
    Z3_func_decl[] decls1 = decls.toArray!Z3_func_decl();
    for (uint i = 0; i < sorts.size(); ++i) {
      sort_names[i] = sorts[i].name();
    }
    for (uint i = 0; i < decls.size(); ++i) {
      decl_names[i] = decls[i].name();
    }

    Z3_ast_vector r = Z3_parse_smtlib2_string(this, s.toStringz, sorts.size(), sort_names.ptr,
					      sorts1.ptr, decls.size(), decl_names.ptr, decls1.ptr);
    checkError();
    return ExprVector(this, r);
  }

  ExprVector parseFile()(string s, ref SortVector sorts, ref FuncDeclVector decls) {
    Z3_symbol[] sort_names = new Z3_symbol[](sorts.size());
    Z3_symbol[] decl_names = new Z3_symbol[](decls.size());
    Z3_sort[]   sorts1; sorts1 = sorts.toArray!Z3_sort();
    Z3_func_decl[] decls1 = decls.toArray!Z3_func_decl();
    for (uint i = 0; i < sorts.size(); ++i) {
      sort_names[i] = sorts[i].name();
    }
    for (uint i = 0; i < decls.size(); ++i) {
      decl_names[i] = decls[i].name();
    }

    Z3_ast_vector r = Z3_parse_smtlib2_file(this, s.toStringz, sorts.size(), sort_names.ptr,
					      sorts1.ptr, decls.size(), decl_names.ptr, decls1.ptr);
    checkError();
    return ExprVector(this, r);
  }
}

mixin template HasContext()
{
  protected Context _m_ctx;
  void setContext(Context ctx) {
    _m_ctx = ctx;
  }
  Context context() {
    return _m_ctx;
  }
  Z3_error_code checkError()  {
    return _m_ctx.checkError();
  }
}

void checkContext(U, V) (U a, V b) {
  // assert (a !is null && b !is null);
  assert (a.context() is b.context());
}

struct AstVectorTpl(T)
{
  mixin HasContext;
  
  Z3_ast_vector _m_vector;
  
  alias _m_vector this;
  
  void init(Z3_ast_vector v) {
    _m_vector = v;
    Z3_ast_vector_inc_ref(context(), _m_vector);
  }

  this(Context c) {
    setContext(c);
    init(Z3_mk_ast_vector(c));
  }

  this(Context c, Z3_ast_vector v) {
    setContext(c);
    init(v);
  }

  this(this) {
    assert (context() !is null);
    Z3_ast_vector_inc_ref(context(), _m_vector);
  }
    
  // this(ref AstVectorTpl!T rhs) {
  //   setContext(rhs.context());
  //   _m_vector = rhs._m_vector;
  //   Z3_ast_vector_inc_ref(context(), _m_vector);
  // }

  ~this() {
    Z3_ast_vector_dec_ref(context(), _m_vector);
  }

  alias length = size;
  
  uint size() {
    return Z3_ast_vector_size(context(), _m_vector);
  }
  
  T opIndex(uint i) {
    Z3_ast r = Z3_ast_vector_get(context(), _m_vector, i);
    checkError();
    return T.castAST(context(), r);
  }

  void pushBack()(auto ref T e) {
    Z3_ast_vector_push(context(), _m_vector, cast(Z3_ast) e);
    checkError();
  }
  
  void resize(uint sz) {
    Z3_ast_vector_resize(context(), _m_vector, sz);
    checkError();
  }

  T back() {
    return opIndex(size() - 1);
  }

  void popBack() {
    assert (size() > 0);
    resize(size() - 1);
  }

  bool empty() {
    return size() == 0;
  }

  ref AstVectorTpl!T opAssign(ref AstVectorTpl!T rhs) {
    Z3_ast_vector_inc_ref(rhs.context(), rhs._m_vector);
    Z3_ast_vector_dec_ref(context(), _m_vector);
    setContext(rhs.context());
    _m_vector = rhs._m_vector;
    return this;
  }

  ref AstVectorTpl!T set()(uint idx, auto ref AST a) {
    Z3_ast_vector_set(context(), _m_vector, idx, a);
    return this;
  }

  alias length = size;

  V[] toArray(V)() {
    V[] arr = new V[](this.length);
    for (uint i = 0; i != size(); ++i) {
      arr[i] = cast(V) this[i];
    }
    return arr;
  }

  /*
    Disabled pending C++98 build upgrade
    bool contains(T const& x) const {
    for (T y : *this) if (eq(x, y)) return true;
    return false;
    }
  */

  // class iterator {
  //   ast_vector_tpl const* _m_vector;
  //   unsigned m_index;
  // public:
  // iterator(ast_vector_tpl const* v, unsigned i): _m_vector(v), m_index(i) {}
  // iterator(iterator const& other): _m_vector(other._m_vector), m_index(other.m_index) {}
  //   iterator operator=(iterator const& other) { _m_vector = other._m_vector; m_index = other.m_index; return *this; }

  //     bool operator==(iterator const& other) const {
  // 	return other.m_index == m_index;
  //     };
  //   bool operator!=(iterator const& other) const {
  //     return other.m_index != m_index;
  //   };
  //   iterator& operator++() {
  //     ++m_index;
  //     return *this;
  //   }
  //   void set(T& arg) {
  //     Z3_ast_vector_set(_m_vector->ctx(), *_m_vector, m_index, arg);
  //   }
  //   iterator operator++(int) { iterator tmp = *this; ++m_index; return tmp; }
  //   T * operator->() const { return &(operator*()); }
  //   T operator*() const { return (*_m_vector)[m_index]; }
  // };
  // iterator begin() const { return iterator(this, 0); }
  // iterator end() const { return iterator(this, size()); }
  // friend std::ostream & operator<<(std::ostream & out, ast_vector_tpl const & v) { out << Z3_ast_vector_to_string(v.ctx(), v); return out; }
  
}

alias AstVector = AstVectorTpl!AST;
alias ExprVector = AstVectorTpl!Expr;
alias SortVector = AstVectorTpl!Sort;
alias FuncDeclVector = AstVectorTpl!FuncDecl;


struct Symbol
{
  mixin HasContext;
  mixin RvalueRef;
  
  Z3_symbol _m_sym;
  Z3_symbol native() {
    return _m_sym;
  }
  alias native this;

  this(Context c, Z3_symbol s) {
    setContext(c);
    _m_sym = s;
  }

  this(this) {
    assert (context() !is null);
  }

  // this(ref return scope Symbol rhs) {
  //   setContext(rhs.context());
  //   _m_sym = rhs._m_sym;
  // }

  Symbol opAssign(ref return scope Symbol rhs) {
    setContext(rhs.context());
    _m_sym = rhs._m_sym;
    return this;
  }
  Z3_symbol_kind kind() {
    return Z3_get_symbol_kind(context(), _m_sym);
  }
  string toString() {
    assert (kind() == Z3_symbol_kind.Z3_STRING_SYMBOL);
    auto cstr = Z3_get_symbol_string(context(), _m_sym);
    return cast(string) cstr[0..cstr.strlen];
  }
  int toInt() {
    assert(kind() == Z3_symbol_kind.Z3_INT_SYMBOL);
    return Z3_get_symbol_int(context(), _m_sym);
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
  V to(V)() if (is(V: int)) {
    return this.toInt();
  }
}

struct ParamDescrs
{
  mixin HasContext;

  Z3_param_descrs _m_descrs;
  this(Context c, Z3_param_descrs d) {
    setContext(c);
    _m_descrs = d;
    Z3_param_descrs_inc_ref(context(), _m_descrs);
  }
  this(this) {
    assert (context() !is null);
    Z3_param_descrs_inc_ref(context(), _m_descrs);
  }
  // this(ref return scope ParamDescrs rhs) {
  //   setContext(rhs.context);
  //   _m_descrs = rhs._m_descrs;
  //   Z3_param_descrs_inc_ref(context(), _m_descrs);
  // }
  ParamDescrs opAssign(ref return scope ParamDescrs rhs) {
    Z3_param_descrs_inc_ref(rhs.context(), rhs._m_descrs);
    Z3_param_descrs_dec_ref(context(), _m_descrs);
    _m_descrs = rhs._m_descrs;
    setContext(rhs.context);
    return this;
  }
  ~this() {
    Z3_param_descrs_dec_ref(context(), _m_descrs);
  }
  static ParamDescrs simplifyParamDescrs(Context c)
  {
    return ParamDescrs(c, Z3_simplify_get_param_descrs(c));
  }
  uint size() {
    return Z3_param_descrs_size(context(), _m_descrs);
  }
  Symbol name(uint i) {
    return Symbol(context(), Z3_param_descrs_get_name(context(), _m_descrs, i));
  }
  Z3_param_kind kind()(auto ref Symbol s) {
    return Z3_param_descrs_get_kind(context(), _m_descrs, s);
  }
  string documentation()(auto ref Symbol s) {
    auto r = Z3_param_descrs_get_documentation(context(), _m_descrs, s);
    checkError();
    return cast(string) r[0..r.strlen];
  }
  string toString() {
    auto r = Z3_param_descrs_to_string(context(), _m_descrs);
    return cast(string) r[0..r.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}

struct Params
{
  mixin HasContext;

  Z3_params _m_params;
  this(Context c) {
    setContext(c);
    _m_params = Z3_mk_params(c);
    Z3_params_inc_ref(context(), _m_params);
  }
  this(this) {
    assert (context() !is null);
    Z3_params_inc_ref(context(), _m_params);    
  }

  // this(ref return scope Params rhs) {
  //   setContext(rhs.context());
  //   _m_params = rhs._m_params;
  //   Z3_params_inc_ref(context(), _m_params);
  // }
  Params opAssign(ref return scope Params rhs) {
    Z3_params_inc_ref(rhs.context(), rhs._m_params);
    Z3_params_dec_ref(context(), _m_params);
    setContext(rhs.context());
    _m_params = rhs._m_params;
    return this;
  }
  ~this() {
    Z3_params_dec_ref(context(), _m_params);
  }
  Z3_params native() {
    return _m_params;
  }
  alias native this;
  T opCast(T)() if (is (T == Z3_params)) {
      return _m_params;
  }

  void set(string k, bool b) {
    Z3_params_set_bool(context(), _m_params, context().strSymbol(k), b);
  }
  void set(string k, uint n) {
    Z3_params_set_uint(context(), _m_params, context().strSymbol(k), n);
  }
  void set(string k, double n) {
    Z3_params_set_double(context(), _m_params, context().strSymbol(k), n);
  }
  void set()(string k, auto ref Symbol s) {
    Z3_params_set_symbol(context(), _m_params, context().strSymbol(k), s);
  }
  void set()(string k, auto ref string s) {
    Z3_params_set_symbol(context(), _m_params, context().strSymbol(k), context().strSymbol(s));
  }
  string toString() {
    auto r =  Z3_params_to_string(context(), this);
    return cast(string) r[0..r.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}

struct AST
{
  mixin HasContext;

  protected Z3_ast _m_ast;

  bool isNull() {
    return _m_ast is null;
  }

  Z3_ast m_ast() {
    return _m_ast;
  }
  
  this(Context c) {
    setContext(c);
    _m_ast = null;
  }
  this(Context c, Z3_ast n) {
    setContext(c);
    _m_ast = n;
    Z3_inc_ref(context(), _m_ast);
  }
  this(this) {
    if (context() !is null) {
      Z3_inc_ref(context(), _m_ast);
    }
  }
  // this(ref scope return AST rhs) {
  //   setContext(rhs.context());
  //   _m_ast = rhs._m_ast;
  //   Z3_inc_ref(context(), _m_ast);
  // }
  ref AST opAssign(ref scope return AST rhs) {
    if (_m_ast !is null) Z3_dec_ref(context(), _m_ast);
    setContext(rhs.context());
    _m_ast = rhs._m_ast;
    Z3_inc_ref(context(), _m_ast);
    return this;
  }
  ~this() {
    if (context !is null) Z3_dec_ref(context, _m_ast);
  }
  Z3_ast native() {
    return _m_ast;
  }
  T opCast(T)() if (is (T == Z3_ast)) {
    return _m_ast;
  }
  alias native this;

  T opCast(T)() if(isBoolean!T) {
    return _m_ast !is null;
  }
  
  Z3_ast_kind kind() {
    Z3_ast_kind r = Z3_get_ast_kind(context(), _m_ast);
    checkError();
    return r;
  }
  uint hash() {
    uint r = Z3_get_ast_hash(context(), _m_ast);
    checkError();
    return r;
  }
  string toString() {
    auto r =  Z3_ast_to_string(context(), _m_ast);
    return cast(string) r[0..r.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }

  /**
     \brief Return true if the ASTs are structurally identical.
  */
  bool opEquals()(auto ref AST other) {
    return Z3_is_eq_ast(context(), this, other);
  }

  bool eq()(auto ref AST other) {
    return Z3_is_eq_ast(context(), this, other);
  }

  static AST castAST(Context c, Z3_ast a) {
    return AST(c, a);
  }

}

/**
   \brief A Z3 sort (aka type). Every expression (i.e., formula or term) in Z3 has a sort.
*/
struct Sort
{
  mixin RvalueRef;

  AST _ast;
  this(Context c) {
    _ast = AST(c);
  }
  this(Context c, Z3_sort s) {
    _ast = AST(c, cast(Z3_ast) s);
  }
  this(Context c, Z3_ast a) {
    _ast = AST(c, a);
  }
  this(this) { }
  // this(ref return scope Sort rhs) {
  //   _ast = rhs._ast;
  // }
  Sort opAssign(ref return scope Sort rhs) {
    _ast = rhs._ast;
    return this;
  }
  T opCast(T)() if (is (T == Z3_sort)) {
      return cast(Z3_sort) _ast._m_ast;
  }
  T opCast(T)() if (is (T == Z3_ast)) {
      return _ast._m_ast;
  }
  Z3_sort native() {
    return cast(Z3_sort) _ast._m_ast;
  }
  alias native this;

  Context context() {
    return _ast.context();
  }
  Z3_error_code checkError() {
    return _ast.checkError();
  }
  // alias _ast this;
  /**
     \brief retrieve unique identifier for func_decl.
  */
  uint id() {
    uint r = Z3_get_sort_id(context(), this);
    checkError();
    return r;
  }

  /**
     \brief Return the internal sort kind.
  */
  Z3_sort_kind sortKind() {
    return Z3_get_sort_kind(context(), cast(Z3_sort) this);
  }
  /**
     \brief Return name of sort.
  */
  Symbol name() {
    Z3_symbol s = Z3_get_sort_name(context(), cast(Z3_sort) this);
    checkError();
    return Symbol(context(), s);
  }
  /**
     \brief Return true if this sort is the Boolean sort.
  */
  bool isBool() {
    return sortKind() == Z3_sort_kind.Z3_BOOL_SORT;
  }
  /**
     \brief Return true if this sort is the Integer sort.
  */
  bool isInt() {
    return sortKind() == Z3_sort_kind.Z3_INT_SORT;
  }
  /**
     \brief Return true if this sort is the Real sort.
  */
  bool isReal() {
    return sortKind() == Z3_sort_kind.Z3_REAL_SORT;
  }
  /**
     \brief Return true if this sort is the Integer or Real sort.
  */
  bool isArith() {
    return isInt() || isReal();
  }
  /**
     \brief Return true if this sort is a Bit-vector sort.
  */
  bool isBv() {
    return sortKind() == Z3_sort_kind.Z3_BV_SORT;
  }
  /**
     \brief Return true if this sort is a Array sort.
  */
  bool isArray() {
    return sortKind() == Z3_sort_kind.Z3_ARRAY_SORT;
  }
  /**
     \brief Return true if this sort is a Datatype sort.
  */
  bool isDatatype() {
    return sortKind() == Z3_sort_kind.Z3_DATATYPE_SORT;
  }
  /**
     \brief Return true if this sort is a Relation sort.
  */
  bool isRelation() {
    return sortKind() == Z3_sort_kind.Z3_RELATION_SORT;
  }
  /**
     \brief Return true if this sort is a Sequence sort.
  */
  bool isSeq() {
    return sortKind() == Z3_sort_kind.Z3_SEQ_SORT;
  }
  /**
     \brief Return true if this sort is a regular expression sort.
  */
  bool isRe() {
    return sortKind() == Z3_sort_kind.Z3_RE_SORT;
  }
  /**
     \brief Return true if this sort is a Finite domain sort.
  */
  bool isFiniteDomain() {
    return sortKind() == Z3_sort_kind.Z3_FINITE_DOMAIN_SORT;
  }
  /**
     \brief Return true if this sort is a Floating point sort.
  */
  bool isFpa() {
    return sortKind() == Z3_sort_kind.Z3_FLOATING_POINT_SORT;
  }

  /**
     \brief Return the size of this Bit-vector sort.

     \pre is_bv()
  */
  uint bvSize() {
    assert (isBv());
    uint r = Z3_get_bv_sort_size(context(), cast(Z3_sort) this);
    checkError();
    return r;
  }

  uint fpaEbits() {
    assert (isFpa());
    uint r = Z3_fpa_get_ebits(context(),  cast(Z3_sort) this);
    checkError();
    return r;
  }

  uint fpaSbits() {
    assert (isFpa());
    uint r = Z3_fpa_get_sbits(context(),  cast(Z3_sort) this);
    checkError();
    return r;
  }
  /**
     \brief Return the domain of this Array sort.

     \pre is_array()
  */
  Sort arrayDomain() {
    assert (isArray());
    Z3_sort s = Z3_get_array_sort_domain(context(), cast(Z3_sort) this);
    checkError();
    return Sort(context(), s);
  }
  /**
     \brief Return the range of this Array sort.

     \pre is_array()
  */
  Sort arrayRange() {
    assert (isArray());
    Z3_sort s = Z3_get_array_sort_range(context(), cast(Z3_sort) this);
    checkError();
    return Sort(context(), s);
  }

  static Sort castAST(Context c, Z3_ast a) {
    assert (Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_SORT_AST);
    return Sort(c, cast(Z3_sort) a);
  }

}

/**
   \brief Function declaration (aka function definition). It is the signature of interpreted and uninterpreted functions in Z3.
   The basic building block in Z3 is the function application.
*/
struct FuncDecl
{
  mixin RvalueRef;

  AST _ast;
  this(Context c) {
    _ast = AST(c);
  }
  this(Context c, Z3_func_decl n) {
    _ast = AST(c, cast(Z3_ast) n);
  }
  this(this) { }    
  // this(ref return scope FuncDecl rhs) {
  //   _ast = rhs._ast;
  // }
  FuncDecl opAssign(ref return scope FuncDecl rhs) {
    _ast = rhs._ast;
    return this;
  }
  T opCast(T)() if (is (T == Z3_func_decl)) {
    return cast(Z3_func_decl) _ast._m_ast;
  }
  T opCast(T)() if (is (T == Z3_ast)) {
      return _ast._m_ast;
  }
  Z3_func_decl native() {
    return cast(Z3_func_decl) _ast._m_ast;
  }

  alias native this;

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
  /**
     \brief retrieve unique identifier for FuncDecl.
  */
  uint id() {
    uint r = Z3_get_func_decl_id(context(), this);
    checkError();
    return r;
  }

  uint arity() {
    return Z3_get_arity(context(), this);
  }

  Sort domain(uint i) {
    assert (i < arity());
    Z3_sort r = Z3_get_domain(context(), this, i);
    checkError();
    return Sort(context(), r);
  }
  Sort range() {
    Z3_sort r = Z3_get_range(context(), this);
    checkError();
    return Sort(context(), r);
  }
  Symbol name() {
    Z3_symbol s = Z3_get_decl_name(context(), this);
    checkError();
    return Symbol(context(), s);
  }
  Z3_decl_kind declKind() {
    return Z3_get_decl_kind(context(), this);
  }

  FuncDecl transitiveClosure()(auto ref FuncDecl foo) {
    Z3_func_decl tc = Z3_mk_transitive_closure(context(), this);
    checkError();
    return FuncDecl(context(), tc); 
  }

  bool isConst() {
    return arity() == 0;
  }

  // expr operator()() const;
  Expr opCall() {
    Z3_ast r = Z3_mk_app(context(), this, 0, null);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(uint n, expr const * args) const;
  Expr opCall(Expr[] args) {
    Z3_ast[] _args = new Z3_ast[](args.length);
    for (uint i = 0; i != args.length; ++i) {
      checkContext(this, args[i]);
      _args[i] = args[i].getAST;
    }
    Z3_ast r = Z3_mk_app(context(), this, cast(uint) _args.length, _args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(expr_vector const& v) const;
  Expr opCall()(auto ref ExprVector args) {
    Z3_ast[] _args = new Z3_ast[](args.size());
    for (uint i = 0; i != args.length; ++i) {
      checkContext(this, args[i]);
      _args[i] = args[i].getAST;
    }
    Z3_ast r = Z3_mk_app(context(), this, args.size(), _args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(expr const & a) const;
  Expr opCall()(auto ref Expr a) {
    checkContext(this, a);
    Z3_ast[1] args = [a.getAST];
    Z3_ast r = Z3_mk_app(context(), this, 1, args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(int a) const;
  Expr opCall(int a) {
    auto dom = domain(0);
    Z3_ast[1] args = [context().numVal(a, dom).getAST];
    Z3_ast r = Z3_mk_app(context(), this, 1, args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(expr const & a1, expr const & a2) const;
  Expr opCall()(auto ref Expr a1, auto ref Expr a2) {
    checkContext(this, a1); checkContext(this, a2);
    Z3_ast[2] args = [a1.getAST, a2.getAST];
    Z3_ast r = Z3_mk_app(context(), this, 2, args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(expr const & a1, int a2) const;
  Expr opCall()(auto ref Expr a1, int a2) {
    checkContext(this, a1);
    auto dom = domain(1);
    Z3_ast[2] args = [a1.getAST, context().numVal(a2, dom).getAST];
    Z3_ast r = Z3_mk_app(context(), this, 2, args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(int a1, expr const & a2) const;
  Expr opCall()(int a1, auto ref Expr a2) {
    checkContext(this, a2);
    auto dom = domain(0);
    Z3_ast[2] args = [context().numVal(a1, dom).getAST, a2.getAST];
    Z3_ast r = Z3_mk_app(context(), this, 2, args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
  Expr opCall()(auto ref Expr a1, auto ref Expr a2, auto ref Expr a3) {
    checkContext(this, a1); checkContext(this, a2); checkContext(this, a3);
    Z3_ast[3] args = [a1.getAST, a2.getAST, a3.getAST];
    Z3_ast r = Z3_mk_app(context(), this, 3, args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
  Expr opCall()(auto ref Expr a1, auto ref Expr a2, auto ref Expr a3, auto ref Expr a4) {
    checkContext(this, a1); checkContext(this, a2);
    checkContext(this, a3); checkContext(this, a4);
    Z3_ast[4] args = [a1.getAST, a2.getAST, a3.getAST, a4.getAST];
    Z3_ast r = Z3_mk_app(context(), this, 4, args.ptr);
    checkError();
    return Expr(context(), r);
  }
  // expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;
  Expr opCall()(auto ref Expr a1, auto ref Expr a2, auto ref Expr a3, auto ref Expr a4, auto ref Expr a5) {
    checkContext(this, a1); checkContext(this, a2);
    checkContext(this, a3); checkContext(this, a4); checkContext(this, a5);
    Z3_ast[5] args = [a1.getAST, a2.getAST, a3.getAST, a4.getAST, a5.getAST];
    Z3_ast r = Z3_mk_app(context(), this, 5, args.ptr);
    checkError();
    return Expr(context(), r);
  }

  static FuncDecl castAST(Context c, Z3_ast a) {
    assert (Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_FUNC_DECL_AST);
    return FuncDecl(c, cast(Z3_func_decl) a);
  }
}

struct Expr
{
  mixin RvalueRef;
  
  AST _ast;

  this(Context c) {
    _ast = AST(c);
  }

  this(Context c, string name, uint size) {
    Z3_ast r = Z3_mk_const(c, c.strSymbol(name), c.bvSort(size));
    c.checkError();
    _ast = AST(c, r);
  }
  
  this(Context c, Z3_ast n) {
    _ast = AST(c, n);
  }

  this(this) { }
  // this(ref return scope Expr rhs) {
  //   _ast = AST(rhs._ast);
  // }

  Expr opAssign(ref return scope Expr rhs) {
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
  // alias _ast this;

  T opCast(t)() if (is (T == Z3_ast)) {
    return _ast._m_ast;
  }
  Z3_ast getAST() {
    return _ast._m_ast;
  }
  
  alias getAST this;

  Z3_ast_kind kind() {
    return _ast.kind();
  }

  Z3_ast opCast(T)() if (is (T == Z3_ast)) {
    return _ast._m_ast;
  }
  
  /**
     \brief Return the sort of this expression.
  */
  Sort getSort() {
    Z3_sort s = Z3_get_sort(context(), _ast._m_ast);
    checkError();
    return Sort(context(), s);
  }

  /**
     \brief Return true if this is a Boolean expression.
  */
  bool isBool() {
    return getSort().isBool();
  }
  /**
     \brief Return true if this is an integer expression.
  */
  bool isInt() {
    return getSort().isInt();
  }
  /**
     \brief Return true if this is a real expression.
  */
  bool isReal() {
    return getSort().isReal();
  }
  /**
     \brief Return true if this is an integer or real expression.
  */
  bool isArith() {
    return getSort().isArith();
  }
  /**
     \brief Return true if this is a Bit-vector expression.
  */
  bool isBv() {
    return getSort().isBv();
  }
  /**
     \brief Return true if this is a Array expression.
  */
  bool isArray() {
    return getSort().isArray();
  }
  /**
     \brief Return true if this is a Datatype expression.
  */
  bool isDatatype() {
    return getSort().isDatatype();
  }
  /**
     \brief Return true if this is a Relation expression.
  */
  bool isRelation() {
    return getSort().isRelation();
  }
  /**
     \brief Return true if this is a sequence expression.
  */
  bool isSeq() {
    return getSort().isSeq();
  }
  /**
     \brief Return true if this is a regular expression.
  */
  bool isRe() {
    return getSort().isRe();
  }

  /**
     \brief Return true if this is a Finite-domain expression.

     \remark Finite-domain is special kind of interpreted sort:
     isBool(), isBv() and isFiniteDomain() are mutually
     exclusive.

  */
  bool isFiniteDomain() {
    return getSort().isFiniteDomain();
  }
  /**
     \brief Return true if this is a FloatingPoint expression. .
  */
  bool isFpa() {
    return getSort().isFpa();
  }

  /**
     \brief Return true if this expression is a numeral.
     Specialized functions also return representations for the numerals as
     small integers, 64 bit integers or rational or decimal strings.
  */
  bool isNumeral() {
    return kind() == Z3_ast_kind.Z3_NUMERAL_AST;
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
    if (!isNumeral()) return false;
    auto r = Z3_get_numeral_string(context(), getAST);
    s = cast(string) r[0..r.strlen];
    checkError();
    return true;
  }
  bool isNumeral(ref string s, uint precision) {
    if (!isNumeral()) return false;
    auto r = Z3_get_numeral_decimal_string(context(), getAST, precision);
    s = cast(string) r[0..r.strlen];
    checkError();
    return true;
  }
  bool isNumeral(ref double d) {
    if (!isNumeral()) return false;
    d = Z3_get_numeral_double(context(), getAST);
    checkError();
    return true;
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
    assert (isNumeral() || isAlgebraic());
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
     \brief Return int value of numeral, throw if result cannot fit in
     machine int

     It only makes sense to use this function if the caller can ensure that
     the result is an integer or if exceptions are enabled.
     If exceptions are disabled, then use the is_numeral_i function.

     \pre is_numeral()
  */
  int getNumeralInt() {
    int result = 0;
    if (!isNumeralI(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine int");
    }
    return result;
  }

  /**
     \brief Return uint value of numeral, throw if result cannot fit in
     machine uint

     It only makes sense to use this function if the caller can ensure that
     the result is an integer or if exceptions are enabled.
     If exceptions are disabled, then use the is_numeral_u function.
     \pre is_numeral()
  */
  uint getNumeralUint() {
    assert(isNumeral());
    uint result = 0;
    if (!isNumeralU(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine uint");
    }
    return result;
  }

  /**
     \brief Return \c int64_t value of numeral, throw if result cannot fit in
     \c int64_t.

     \pre is_numeral()
  */
  long getNumeralInt64() {
    assert (isNumeral());
    long result = 0;
    if (!isNumeralI64(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine int64_t");
    }
    return result;
  }

  /**
     \brief Return \c uint64_t value of numeral, throw if result cannot fit in
     \c uint64_t.

     \pre is_numeral()
  */
  ulong getNumeralUint64() {
    assert(isNumeral());
    ulong result = 0;
    if (!isNumeralU64(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine uint64_t");
    }
    return result;
  }

  double getNumeralDouble() {
    assert(isNumeral());
    double result = 0;
    if (!isNumeral(result)) {
      assert (context().enableExceptions());
      if (!context().enableExceptions()) return 0;
      throw new Z3Exception("numeral does not fit in machine double");
    }
    return result;
  }

  Z3_lbool boolValue() {
    return Z3_get_bool_value(context(), getAST);
  }

  Expr numerator() {
    assert (isNumeral());
    Z3_ast r = Z3_get_numerator(context(), getAST);
    checkError();
    return Expr(context(),r);
  }


  Expr denominator() {
    assert (isNumeral());
    Z3_ast r = Z3_get_denominator(context(), getAST);
    checkError();
    return Expr(context(),r);
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
     \brief Return a RoundingMode sort.
  */
  Sort fpaRoundingMode() {
    assert (isFpa());
    Z3_sort s = context().fpaRoundingMode();
    checkError();
    return Sort(context(), s);
  }


  /**
     \brief Return the declaration associated with this application.
     This method assumes the expression is an application.

     \pre is_app()
  */
  FuncDecl decl() {
    Z3_func_decl f = Z3_get_app_decl(context(), Z3_to_app(context(), this.getAST));
    checkError();
    return FuncDecl(context(), f);
  }
  /**
     \brief Return the number of arguments in this application.
     This method assumes the expression is an application.

     \pre is_app()
  */
  uint numArgs() {
    uint r = Z3_get_app_num_args(context(), Z3_to_app(context(), this.getAST));
    checkError();
    return r;
  }
  /**
     \brief Return the i-th argument of this application.
     This method assumes the expression is an application.

     \pre is_app()
     \pre i < num_args()
  */
  Expr arg(uint i) {
    Z3_ast r = Z3_get_app_arg(context(), Z3_to_app(context(), this.getAST), i);
    checkError();
    return Expr(context(), r);
  }

  /**
     \brief Return the 'body' of this quantifier.

     \pre is_quantifier()
  */
  Expr body() {
    assert (isQuantifier());
    Z3_ast r = Z3_get_quantifier_body(context(), getAST);
    checkError();
    return Expr(context(), r);
  }

  // friend expr operator!(expr const & a); // not
  // friend expr operator&&(expr const & a, expr const & b); // and
  // friend expr operator&&(expr const & a, bool b); // and
  // friend expr operator&&(bool a, expr const & b); // and
  // friend expr operator||(expr const & a, expr const & b); // or
  // friend expr operator||(expr const & a, bool b); // or
  // friend expr operator||(bool a, expr const & b); // or
  // friend expr implies(expr const & a, expr const & b);
  // friend expr implies(expr const & a, bool b);
  // friend expr implies(bool a, expr const & b);
  // friend expr mk_or(expr_vector const& args);
  // friend expr mk_and(expr_vector const& args);
  // friend expr ite(expr const & c, expr const & t, expr const & e);

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
  bool isAdd() {
    return isApp() && Z3_decl_kind.Z3_OP_ADD == decl().declKind();
  }
  bool isSub() {
    return isApp() && Z3_decl_kind.Z3_OP_SUB == decl().declKind();
  }
  bool isLe() {
    return isApp() && Z3_decl_kind.Z3_OP_LE == decl().declKind();
  }
  bool isGe() {
    return isApp() && Z3_decl_kind.Z3_OP_GE == decl().declKind();
  }
  bool isLt() {
    return isApp() && Z3_decl_kind.Z3_OP_LT == decl().declKind();
  }
  bool isGt() {
    return isApp() && Z3_decl_kind.Z3_OP_GT == decl().declKind();
  }
  bool isMul() {
    return isApp() && Z3_decl_kind.Z3_OP_MUL == decl().declKind();
  }
  bool isDiv() {
    return isApp() && Z3_decl_kind.Z3_OP_DIV == decl().declKind();
  }
  bool isIDiv() {
    return isApp() && Z3_decl_kind.Z3_OP_IDIV == decl().declKind();
  }
  bool isRem() {
    return isApp() && Z3_decl_kind.Z3_OP_REM == decl().declKind();
  }
  bool isMod() {
    return isApp() && Z3_decl_kind.Z3_OP_MOD == decl().declKind();
  }
  bool isPower() {
    return isApp() && Z3_decl_kind.Z3_OP_POWER == decl().declKind();
  }


  // friend expr distinct(expr_vector const& args);
  // friend expr concat(expr const& a, expr const& b);
  // friend expr concat(expr_vector const& args);

  // friend expr operator==(expr const & a, expr const & b);
  // friend expr operator==(expr const & a, int b);
  // friend expr operator==(int a, expr const & b);

  // friend expr operator!=(expr const & a, expr const & b);
  // friend expr operator!=(expr const & a, int b);
  // friend expr operator!=(int a, expr const & b);

  // friend expr operator+(expr const & a, expr const & b);
  // friend expr operator+(expr const & a, int b);
  // friend expr operator+(int a, expr const & b);
  // friend expr sum(expr_vector const& args);

  // friend expr operator*(expr const & a, expr const & b);
  // friend expr operator*(expr const & a, int b);
  // friend expr operator*(int a, expr const & b);

  // /*  \brief Power operator  */
  // friend expr pw(expr & a, expr & b);
  // friend expr pw(expr & a, int b);
  // friend expr pw(int a, expr & b);

  // /* \brief mod operator */
  // friend expr mod(expr const& a, expr const& b);
  // friend expr mod(expr const& a, int b);
  // friend expr mod(int a, expr const& b);

  // /* \brief rem operator */
  // friend expr rem(expr const& a, expr const& b);
  // friend expr rem(expr const& a, int b);
  // friend expr rem(int a, expr const& b);

  // friend expr is_int(expr const& e);

  // friend expr operator/(expr & a, expr & b);
  // friend expr operator/(expr & a, int b);
  // friend expr operator/(int a, expr & b);

  // friend expr operator-(expr & a);

  // friend expr operator-(expr & a, expr & b);
  // friend expr operator-(expr & a, int b);
  // friend expr operator-(int a, expr & b);

  // friend expr operator<=(expr & a, expr & b);
  // friend expr operator<=(expr & a, int b);
  // friend expr operator<=(int a, expr & b);


  // friend expr operator>=(expr & a, expr & b);
  // friend expr operator>=(expr & a, int b);
  // friend expr operator>=(int a, expr & b);

  // friend expr operator<(expr & a, expr & b);
  // friend expr operator<(expr & a, int b);
  // friend expr operator<(int a, expr & b);

  // friend expr operator>(expr & a, expr & b);
  // friend expr operator>(expr & a, int b);
  // friend expr operator>(int a, expr & b);

  // friend expr pble(expr_vector const& es, int * coeffs, int bound);
  // friend expr pbge(expr_vector const& es, int * coeffs, int bound);
  // friend expr pbeq(expr_vector const& es, int * coeffs, int bound);
  // friend expr atmost(expr_vector const& es, uint bound);
  // friend expr atleast(expr_vector const& es, uint bound);

  // friend expr operator&(expr & a, expr & b);
  // friend expr operator&(expr & a, int b);
  // friend expr operator&(int a, expr & b);

  // friend expr operator^(expr & a, expr & b);
  // friend expr operator^(expr & a, int b);
  // friend expr operator^(int a, expr & b);

  // friend expr operator|(expr & a, expr & b);
  // friend expr operator|(expr & a, int b);
  // friend expr operator|(int a, expr & b);
  // friend expr nand(expr const& a, expr const& b);
  // friend expr nor(expr const& a, expr const& b);
  // friend expr xnor(expr const& a, expr const& b);

  // friend expr min(expr const& a, expr const& b);
  // friend expr max(expr const& a, expr const& b);

  // friend expr bv2int(expr const& a, bool is_signed); 
  // friend expr int2bv(uint n, expr const& a);
  // friend expr bvadd_no_overflow(expr const& a, expr const& b, bool is_signed);
  // friend expr bvadd_no_underflow(expr const& a, expr const& b);
  // friend expr bvsub_no_overflow(expr const& a, expr const& b);
  // friend expr bvsub_no_underflow(expr const& a, expr const& b, bool is_signed);
  // friend expr bvsdiv_no_overflow(expr const& a, expr const& b);
  // friend expr bvneg_no_overflow(expr const& a);
  // friend expr bvmul_no_overflow(expr const& a, expr const& b, bool is_signed);
  // friend expr bvmul_no_underflow(expr const& a, expr const& b);
        
  // expr rotate_left(uint i) { Z3_ast r = Z3_mk_rotate_left(context(), i, *this); context().checkError(); return expr(context(), r); }
  Expr rotateLeft(uint i) {
    Z3_ast r = Z3_mk_rotate_left(context(), i, getAST);
    context().checkError();
    return Expr(context(), r);
  }
  // expr rotate_right(uint i) { Z3_ast r = Z3_mk_rotate_right(context(), i, *this); context().checkError(); return expr(context(), r); }
  Expr rotateRight(uint i) {
    Z3_ast r = Z3_mk_rotate_right(context(), i, getAST);
    context().checkError();
    return Expr(context(), r);
  }
  // expr repeat(uint i) { Z3_ast r = Z3_mk_repeat(context(), i, *this); context().checkError(); return expr(context(), r); }
  Expr repeat(uint i) {
    Z3_ast r = Z3_mk_repeat(context(), i, getAST);
    context().checkError();
    return Expr(context(), r);
  }

  // friend expr abs(expr & a);
  // friend expr sqrt(expr & a, expr & rm);
  // friend expr operator~(expr & a);

  // expr extract(uint hi, uint lo) { Z3_ast r = Z3_mk_extract(context(), hi, lo, *this); context().checkError(); return expr(context(), r); }
  Expr extract(uint hi, uint lo) {
    Z3_ast r = Z3_mk_extract(context(), hi, lo, getAST);
    context().checkError();
    return Expr(context(), r);
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
  Expr extract()(auto ref Expr offset, auto ref Expr length) {
    checkContext(this, offset); checkContext(offset, length);
    Z3_ast r = Z3_mk_seq_extract(context(), getAST, offset.getAST, length.getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr replace()(auto ref Expr src, auto ref Expr dst) {
    checkContext(this, src); checkContext(src, dst);
    Z3_ast r = Z3_mk_seq_replace(context(), getAST, src.getAST, dst.getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr unit() {
    Z3_ast r = Z3_mk_seq_unit(context(), getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr contains()(auto ref Expr s) {
    checkContext(this, s);
    Z3_ast r = Z3_mk_seq_contains(context(), getAST, s.getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr at()(auto ref Expr index) {
    checkContext(this, index);
    Z3_ast r = Z3_mk_seq_at(context(), getAST, index.getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr nth()(auto ref Expr index) {
    checkContext(this, index);
    Z3_ast r = Z3_mk_seq_nth(context(), getAST, index.getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr length() {
    Z3_ast r = Z3_mk_seq_length(context(), getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr stoi() {
    Z3_ast r = Z3_mk_str_to_int(context(), getAST);
    checkError();
    return Expr(context(), r);
  }
  Expr itos() {
    Z3_ast r = Z3_mk_int_to_str(context(), getAST);
    checkError();
    return Expr(context(), r);
  }

  // friend expr range(expr const& lo, expr const& hi);


  /**
     \brief create a looping regular expression.
  */
  Expr loop(uint lo) {
    Z3_ast r = Z3_mk_re_loop(context(), getAST, lo, 0);
    checkError();
    return Expr(context(), r);
  }

  Expr loop(uint lo, uint hi) {
    Z3_ast r = Z3_mk_re_loop(context(), getAST, lo, hi);
    checkError();
    return Expr(context(), r);
  }

  /**
   * index operator defined on arrays and sequences.
   */
  Expr opIndex()(auto ref Expr index) {
    assert(isArray() || isSeq());
    if (isArray()) {
      return select(this, index);
    }
    return nth(index);            
  }

  Expr opIndex()(auto ref ExprVector index) {
    return select(this, index);
  }

  /**
     \brief Return a simplified version of this expression.
  */
  Expr simplify() {
    Z3_ast r = Z3_simplify(context(), getAST);
    checkError();
    return Expr(context(), r);
  }
  /**
     \brief Return a simplified version of this expression. The parameter \c p is a set of parameters for the Z3 simplifier.
  */
  Expr simplify()(auto ref Params p) {
     Z3_ast r = Z3_simplify_ex(context(), getAST, p);
     checkError();
     return Expr(context(), r);
   }

  /**
     \brief Apply substitution. Replace src expressions by dst.
  */

  Expr substitute()(auto ref ExprVector src, auto ref ExprVector dst) {
    assert (src.size() == dst.size());
    Z3_ast[] _src = new Z3_ast[](src.size());
    Z3_ast[] _dst = new Z3_ast[](dst.size());
    for (uint i = 0; i < src.size(); ++i) {
      _src[i] = src[i].getAST;
      _dst[i] = dst[i].getAST;
    }
    Z3_ast r = Z3_substitute(context(), getAST, src.size(), _src.ptr, _dst.ptr);
    checkError();
    return Expr(context(), r);
  }

  /**
     \brief Apply substitution. Replace bound variables by expressions.
  */

  Expr substitute()(auto ref ExprVector dst) {
    Z3_ast[] _dst = new Z3_ast[](dst.size());
    for (uint i = 0; i < dst.size(); ++i) {
      _dst[i] = dst[i].getAST;
    }
    Z3_ast r = Z3_substitute_vars(context(), getAST, dst.size(), _dst.ptr);
    checkError();
    return Expr(context(), r);
  }

  Expr opUnary(string op)() if(op == "~") {
    return Expr(this.context(), Z3_mk_bvnot(this.context, getAST));
  }

  Expr opUnary(string op)() if(op == "-") {
    Z3_ast r = 0;
    // if (this.is_bv()) {
    r = Z3_mk_bvneg(this.context(), getAST);
    // }
    this.checkError();
    return Expr(this.context(), r);
  }

  Expr opBinary(string op)(Expr other)
    if (op == "&" || op == "|" || op == "^" || op == "+" ||
	op == "-" || op == "*" || op == "/" || op == "%" ||
	op == "<<" || op == ">>" || op == ">>>") {
      checkContext(this, other);
      assert (! (this.isBool() || other.isBool()));
      Z3_ast r = null;
      static if(op == "&") {
	r = Z3_mk_bvand(this.context(), getAST, other);
      }
      static if(op == "|") {
	r = Z3_mk_bvor(this.context(), getAST, other);
      }
      static if(op == "^") {
	r = Z3_mk_bvxor(this.context(), getAST, other);
      }
      static if(op == "+") {
	r = Z3_mk_bvadd(this.context(), getAST, other);
      }
      static if(op == "-") {
	r = Z3_mk_bvsub(this.context(), getAST, other);
      }
      static if(op == "*") {
	r = Z3_mk_bvmul(this.context(), getAST, other);
      }
      static if(op == "/") {
	r = Z3_mk_bvsdiv(this.context(), getAST, other);
      }
      static if(op == "%") {
	r = Z3_mk_bvsrem(this.context(), getAST, other);
      }
      static if(op == "<<") {
	r = Z3_mk_bvshl(this.context(), getAST, other);
      }
      static if(op == ">>") {
	r = Z3_mk_bvashr(this.context(), getAST, other);
      }
      static if(op == ">>>") {
	r = Z3_mk_bvlshr(this.context(), getAST, other);
      }
      checkError();
      return Expr(this.context(), r);
    }

  static Expr castAST(Context c, Z3_ast a) {
    assert (Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_NUMERAL_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_APP_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_QUANTIFIER_AST ||
	    Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_VAR_AST);
    return Expr(c, a);
  }
}

struct FuncEntry
{
  mixin HasContext;
  
  Z3_func_entry _m_entry;

  private void init(Z3_func_entry e) {
    _m_entry = e;
    Z3_func_entry_inc_ref(context(), _m_entry);
  }

  this(Context c, Z3_func_entry e) {
    setContext(c);
    _m_entry = e;
    Z3_func_entry_inc_ref(context(), _m_entry);
  }

  this(this) {
    assert (context() !is null);
    Z3_func_entry_inc_ref(context(), _m_entry);
  }

  // this(ref FuncEntry s) {
  //   setContext(s.context());
  //   init(s._m_entry);
  // }

  ~this() {
    Z3_func_entry_dec_ref(context(), _m_entry);
  }

  Z3_func_entry native() {
    return _m_entry;
  }

  alias native this;
  //operator Z3_func_entry() const { return _m_entry; }

  ref FuncEntry opAssign(ref FuncEntry s) return {
    Z3_func_entry_inc_ref(s.context(), s._m_entry);
    Z3_func_entry_dec_ref(context(), _m_entry);
    setContext(s.context());
    _m_entry = s._m_entry;
    return this;
  }
  
  Expr value() {
    Z3_ast r = Z3_func_entry_get_value(context(), _m_entry);
    checkError();
    return Expr(context(), r);
  }
  uint numArgs() {
    uint r = Z3_func_entry_get_num_args(context(), _m_entry);
    checkError();
    return r;
  }
  Expr arg(uint i) {
    Z3_ast r = Z3_func_entry_get_arg(context(), _m_entry, i);
    checkError();
    return Expr(context(), r);
  }
}

struct FuncInterp
{
  mixin HasContext;

  Z3_func_interp _m_interp;
  private void init(Z3_func_interp e) {
    _m_interp = e;
    Z3_func_interp_inc_ref(context(), _m_interp);
  }

  this(Context c, Z3_func_interp e) {
    setContext(c);
    _m_interp = e;
    Z3_func_interp_inc_ref(context(), _m_interp);
  }

  this(this) {
    assert (context() !is null);
    Z3_func_interp_inc_ref(context(), _m_interp);
  }

  // this(ref FuncInterp s) {
  //   setContext(s.context());
  //   init(s._m_interp);
  // }

  ~this() {
    Z3_func_interp_dec_ref(context(), _m_interp);
  }
  Z3_func_interp native() {
    return _m_interp;
  }
  alias native this;

  ref FuncInterp opAssign(ref FuncInterp s) return {
    Z3_func_interp_inc_ref(s.context(), s._m_interp);
    Z3_func_interp_dec_ref(context(), _m_interp);
    setContext(s.context());
    _m_interp = s._m_interp;
    return this;
  }

  Expr elseValue() {
    Z3_ast r = Z3_func_interp_get_else(context(), _m_interp);
    checkError();
    return Expr(context(), r);
  }
  
  uint numEntries() {
    uint r = Z3_func_interp_get_num_entries(context(), _m_interp);
    checkError();
    return r;
  }

  FuncEntry entry(uint i) {
    Z3_func_entry e = Z3_func_interp_get_entry(context(), _m_interp, i);
    checkError();
    return FuncEntry(context(), e);
  }

  void addEntry()(auto ref ExprVector args, auto ref Expr value) {
    Z3_func_interp_add_entry(context(), _m_interp, args, value.getAST);
    checkError();
  }

  void setElse()(auto ref Expr value) {
    Z3_func_interp_set_else(context(), _m_interp, value.getAST);
    checkError();
  }
}

struct Model
{
  mixin HasContext;

  Z3_model _m_model;
  private void init(Z3_model m) {
    _m_model = m;
    Z3_model_inc_ref(context(), _m_model);
  }

  struct translate {};

  this(Context c) {
    setContext(c);
    init(Z3_mk_model(c));
  }

  this(Context c, Z3_model m) {
    setContext(c);
    _m_model = m;
    Z3_model_inc_ref(context(), _m_model);
  }

  this(this) {
    assert (context() !is null);
    Z3_model_inc_ref(context(), _m_model);
  }

  // this(ref Model s) {
  //   setContext(s.context());
  //   init(s._m_model);
  // }
  
  this(ref Model src, Context dst, translate) {
    setContext(dst);
    _m_model = Z3_model_translate(src.context(), src, dst);
    Z3_model_inc_ref(context(), _m_model);
    // init(Z3_model_translate(src.context(), src, dst));
  }

  ~this() {
    Z3_model_dec_ref(context(), _m_model);
  }

  Z3_model native() {
    return _m_model;
  }
  alias native this;

  ref Model opAssign(ref Model s) return {
    Z3_model_inc_ref(s.context(), s._m_model);
    Z3_model_dec_ref(context(), _m_model);
    setContext(s.context());
    _m_model = s._m_model;
    return this;
  }

  Expr eval()(auto ref Expr n, bool model_completion=false) {
    checkContext(this, n);
    Z3_ast r = null;
    bool status = Z3_model_eval(context(), _m_model, n.getAST, model_completion, &r);
    checkError();
    if (status == false && context().enableExceptions())
      throw(new Exception("failed to evaluate expression"));
    return Expr(context(), r);
  }

  uint numConsts() {
    return Z3_model_get_num_consts(context(), _m_model);
  }

  uint numFuncs() {
    return Z3_model_get_num_funcs(context(), _m_model);
  }

  FuncDecl getConstDecl(uint i) {
    Z3_func_decl r = Z3_model_get_const_decl(context(), _m_model, i);
    checkError();
    return FuncDecl(context(), r);
  }

  FuncDecl getFuncDecl(uint i) {
    Z3_func_decl r = Z3_model_get_func_decl(context(), _m_model, i);
    checkError();
    return FuncDecl(context(), r);
  }
  uint size() {
    return numConsts() + numFuncs();
  }

  FuncDecl opIndex(int i) {
    assert(0 <= i);
    return (cast(uint) (i) < numConsts()) ? getConstDecl(i) : getFuncDecl(i - numConsts());
  }

  // returns interpretation of constant declaration c.
  // If c is not assigned any value in the Model it returns
  // an expression with a null ast reference.
  Expr getConstInterp(FuncDecl c) {
    checkContext(this, c);
    Z3_ast r = Z3_model_get_const_interp(context(), _m_model, c);
    checkError();
    return Expr(context(), r);
  }
  
  FuncInterp getFuncInterp(FuncDecl f) {
    checkContext(this, f);
    Z3_func_interp r = Z3_model_get_func_interp(context(), _m_model, f);
    checkError();
    return FuncInterp(context(), r);
  }

  // returns true iff the Model contains an interpretation
  // for function f.
  bool hasInterp(FuncDecl f) {
    checkContext(this, f);
    return Z3_model_has_interp(context(), _m_model, f);
  }

  FuncInterp addFuncInterp()(auto ref FuncDecl f, auto ref Expr else_val) {
    Z3_func_interp r = Z3_add_func_interp(context(), _m_model, f, else_val.getAST);
    checkError();
    return FuncInterp(context(), r);
  }

  void add_const_interp()(auto ref FuncDecl f, auto ref Expr value) {
    Z3_add_const_interp(context(), _m_model, f, value.getAST);
    checkError();
  }

  // friend std::ostream & operator<<(std::ostream & out, Model const & m);
  string toString() {
    auto str = Z3_model_to_string(context(), this);
    return cast(string) str[0..str.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}


struct Stats
{
  mixin HasContext;
  
  Z3_stats _m_stats;
  private void init(Z3_stats e) {
    _m_stats = e;
    Z3_stats_inc_ref(context(), _m_stats);
  }
  this(Context c) {
    setContext(c);
    _m_stats = null;
  }

  this(Context c, Z3_stats e) {
    setContext(c);
    _m_stats = e;
    Z3_stats_inc_ref(context(), _m_stats);
  }

  this(this) {
    assert (context() !is null);
    Z3_stats_inc_ref(context(), _m_stats);
  }

  // this(ref Stats s) {
  //   setContext(s.context());
  //   init(s._m_stats);
  // }

  ~this() {
    if (_m_stats) Z3_stats_dec_ref(context(), _m_stats);
  }

  Z3_stats native() {
    return _m_stats;
  }
  alias native this;
  
  ref Stats opAssign(ref Stats s) return {
    Z3_stats_inc_ref(s.context(), s._m_stats);
    if (_m_stats) Z3_stats_dec_ref(context(), _m_stats);
    setContext(s.context());
    _m_stats = s._m_stats;
    return this;
  }

  uint size() {
    return Z3_stats_size(context(), _m_stats);
  }

  string key(uint i) {
    auto s = Z3_stats_get_key(context(), _m_stats, i);
    checkError();
    return cast(string) s[0..s.strlen()];
  }

  bool isUint(uint i) {
    bool r = Z3_stats_is_uint(context(), _m_stats, i);
    checkError();
    return r;
  }

  bool isDouble(uint i) {
    bool r = Z3_stats_is_double(context(), _m_stats, i);
    checkError();
    return r;
  }

  uint uintValue(uint i) {
    uint r = Z3_stats_get_uint_value(context(), _m_stats, i);
    checkError();
    return r;
  }

  double doubleValue(uint i) {
    double r = Z3_stats_get_double_value(context(), _m_stats, i);
    checkError();
    return r;
  }

  // friend std::ostream & operator<<(std::ostream & out, Stats const & s);
  string toString() {
    auto str = Z3_stats_to_string(context(), this);
    return cast(string) str[0..str.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}

struct Solver {
  mixin HasContext;
  
  Z3_solver _m_solver;
  private void init(Z3_solver s) {
    _m_solver = s;
    Z3_solver_inc_ref(context(), _m_solver);
  }
  struct simple {};
  struct translate {};
  this(Context c) {
    setContext(c);
    init(Z3_mk_solver(c));
  }
  this(Context c, simple) {
    setContext(c);
    init(Z3_mk_simple_solver(c));
  }
  this(Context c, Z3_solver s) {
    setContext(c);
    init(s);
  }
  this(Context c, string logic) {
    setContext(c);
    init(Z3_mk_solver_for_logic(c, c.strSymbol(logic)));
  }
  this(Context c, ref Solver src, translate) {
    setContext(c);
    init(Z3_solver_translate(src.context(), src, c));
  }
  this(this) {
    assert (context() !is null);
    Z3_solver_inc_ref(context(), _m_solver);
  }
  // this(ref Solver s) {
  //   setContext(s.context());
  //   init(s._m_solver);
  // }
  ~this() {
    Z3_solver_dec_ref(context(), _m_solver);
  }
  Z3_solver native() {
    return _m_solver;
  }

  alias native this;
  
  ref Solver opAssign(ref Solver s) return {
    Z3_solver_inc_ref(s.context(), s._m_solver);
    Z3_solver_dec_ref(context(), _m_solver);
    setContext(s.context());
    _m_solver = s._m_solver;
    return this;
  }

  void set()(auto ref Params p) {
    Z3_solver_set_params(context(), _m_solver, p);
    checkError();
  }

  void set(string k, bool v) {
    Params p = Params(context());
    p.set(k, v);
    set(p);
  }

  void set(string k, uint v) {
    Params p = Params(context());
    p.set(k, v);
    set(p);
  }

  void set(string k, double v) {
    Params p = Params(context());
    p.set(k, v);
    set(p);
  }

  void set()(string k, auto ref Symbol v) {
    Params p = Params(context());
    p.set(k, v);
    set(p);
  }

  void set(string k, string v) {
    Params p = Params(context());
    p.set(k, v);
    set(p);
  }

  void push() {
    Z3_solver_push(context(), _m_solver);
    checkError();
  }

  void pop(uint n = 1) {
    Z3_solver_pop(context(), _m_solver, n);
    checkError();
  }

  void reset() {
    Z3_solver_reset(context(), _m_solver);
    checkError();
  }

  void add()(auto ref Expr e) {
    assert (e.isBool());
    Z3_solver_assert(context(), _m_solver, e.getAST);
    checkError();
  }

  void add()(auto ref Expr e, auto ref Expr p) {
    assert (e.isBool()); assert (p.isBool()); assert (p.isConst());
    Z3_solver_assert_and_track(context(), _m_solver, e.getAST, p.getAST);
    checkError();
  }

  void add()(auto ref Expr e, string p) {
    add(e, context().boolConst(p).byRef);
  }

  // fails for some compilers:
        // void add(expr_vector const& v) { check_context(*this, v); for (expr e : v) add(e); }
  void fromFile(string file) {
    Z3_solver_from_file(context(), _m_solver, file.toStringz);
    context().checkParserError();
  }

  void fromString(string s) {
    Z3_solver_from_string(context(), _m_solver, s.toStringz);
    context().checkParserError();
  }

  CheckResult check() {
    Z3_lbool r = Z3_solver_check(context(), _m_solver);
    checkError();
    return toCheckResult(r);
  }

  CheckResult check(Expr[] assumptions) {
    Z3_ast[] _assumptions = new Z3_ast[](assumptions.length);
    for (uint i = 0; i < assumptions.length; i++) {
      checkContext(this, assumptions[i]);
      _assumptions[i] = assumptions[i].getAST;
    }
    Z3_lbool r = Z3_solver_check_assumptions(context(), _m_solver,
					     cast(uint) _assumptions.length, _assumptions.ptr);
    checkError();
    return toCheckResult(r);
  }

  CheckResult check()(auto ref ExprVector assumptions) {
    uint n = assumptions.size();
    Z3_ast[] _assumptions = new Z3_ast[](n);
    for (uint i = 0; i < n; i++) {
      checkContext(this, assumptions[i]);
      _assumptions[i] = assumptions[i].getAST;
    }

    Z3_lbool r = Z3_solver_check_assumptions(context(), _m_solver,
					     cast(uint) _assumptions.length, _assumptions.ptr);
    checkError();
    return toCheckResult(r);
  }

  Model getModel() {
    Z3_model m = Z3_solver_get_model(context(), _m_solver);
    checkError();
    return Model(context(), m);
  }

  CheckResult consequences()(auto ref ExprVector assumptions, auto ref ExprVector vars, auto ref ExprVector conseq) {
    Z3_lbool r = Z3_solver_get_consequences(context(), _m_solver, assumptions, vars, conseq);
    checkError();
    return toCheckResult(r);
  }

  string reasonUnknown() {
    Z3_string r = Z3_solver_get_reason_unknown(context(), _m_solver);
    checkError();
    return cast(string) r[0..r.strlen()];
  }

  Stats statistics() {
    Z3_stats r = Z3_solver_get_statistics(context(), _m_solver);
    checkError();
    return Stats(context(), r);
  }

  ExprVector unsatCore() {
    Z3_ast_vector r = Z3_solver_get_unsat_core(context(), _m_solver);
    checkError();
    return ExprVector(context(), r);
  }

  ExprVector assertions() {
    Z3_ast_vector r = Z3_solver_get_assertions(context(), _m_solver);
    checkError();
    return ExprVector(context(), r);
  }

  ExprVector nonUnits() {
    Z3_ast_vector r = Z3_solver_get_non_units(context(), _m_solver);
    checkError();
    return ExprVector(context(), r);
  }

  ExprVector units() {
    Z3_ast_vector r = Z3_solver_get_units(context(), _m_solver);
    checkError();
    return ExprVector(context(), r);
  }

  ExprVector trail() {
    Z3_ast_vector r = Z3_solver_get_trail(context(), _m_solver);
    checkError();
    return ExprVector(context(), r);
  }

  ExprVector trail()(auto ref uint[] levels) { 
    Z3_ast_vector r = Z3_solver_get_trail(context(), _m_solver); 
    checkError(); 
    ExprVector result = ExprVector(context(), r);
    uint sz = result.size();
    levels.length  = sz;
    Z3_solver_get_levels(context(), _m_solver, r, sz, levels.ptr);
    checkError(); 
    return result; 
  }

  Expr proof() {
    Z3_ast r = Z3_solver_get_proof(context(), _m_solver);
    checkError();
    return Expr(context(), r);
  }

  string toSmt2(string status = "unknown") {
    Z3_ast[] es = assertions().toArray!Z3_ast();
    Z3_ast* fmls = es.ptr;
    Z3_ast fml = null;
    uint sz = cast(uint) es.length;
    if (sz > 0) {
      --sz;
      fml = fmls[sz];
    }
    else {
      fml = context().boolVal(true).getAST;
    }
    auto str = Z3_benchmark_to_smtlib_string(context(),"".toStringz, "".toStringz,
					     status.toStringz, "".toStringz, sz, fmls, fml);
    return cast(string) str[0..str.strlen];
  }

  string dimacs() {
    auto str = Z3_solver_to_dimacs_string(context(), _m_solver);
    return cast(string) str[0..str.strlen];
  }

  ParamDescrs getParamDescrs() {
    return ParamDescrs(context(), Z3_solver_get_param_descrs(context(), _m_solver));
  }


  ExprVector cube()(auto ref ExprVector vars, uint cutoff) {
    Z3_ast_vector r = Z3_solver_cube(context(), _m_solver, vars, cutoff);
    checkError();
    return ExprVector(context(), r);
  }

  // class cube_iterator {
  //     Solver&      _m_solver;
  //     uint&    m_cutoff;
  //     expr_vector& m_vars;
  //     expr_vector  m_cube;
  //     bool         m_end;
  //     bool         m_empty;

  //     void inc() {
  //         assert(!m_end && !m_empty);
  //         m_cube = _m_solver.cube(m_vars, m_cutoff);
  //         m_cutoff = 0xFFFFFFFF;
  //         if (m_cube.size() == 1 && m_cube[0].is_false()) {
  //             m_cube = z3::expr_vector(_m_solver.context());
  //             m_end = true;
  //         }
  //         else if (m_cube.empty()) {
  //             m_empty = true;
  //         }
  //     }
  // public:
  //     cube_iterator(Solver& s, expr_vector& vars, uint& cutoff, bool end):
  //         _m_solver(s),
  //         m_cutoff(cutoff),
  //         m_vars(vars),
  //         m_cube(s.context()),
  //         m_end(end),
  //         m_empty(false) {
  //         if (!m_end) {
  //             inc();
  //         }
  //     }

  //     cube_iterator& operator++() {
  //         assert(!m_end);
  //         if (m_empty) {
  //             m_end = true;
  //         }
  //         else {
  //             inc();
  //         }
  //         return *this;
  //     }
  //     cube_iterator operator++(int) { assert(false); return *this; }
  //     expr_vector const * operator->() const { return &(operator*()); }
  //     expr_vector const& operator*() const { return m_cube; }

  //     bool operator==(cube_iterator const& other) {
  //         return other.m_end == m_end;
  //     };
  //     bool operator!=(cube_iterator const& other) {
  //         return other.m_end != m_end;
  //     };

  // };

  // class cube_generator {
  //     Solver&      _m_solver;
  //     uint     m_cutoff;
  //     expr_vector  m_default_vars;
  //     expr_vector& m_vars;
  // public:
  //     cube_generator(Solver& s):
  //         _m_solver(s),
  //         m_cutoff(0xFFFFFFFF),
  //         m_default_vars(s.context()),
  //         m_vars(m_default_vars)
  //     {}

  //     cube_generator(Solver& s, expr_vector& vars):
  //         _m_solver(s),
  //         m_cutoff(0xFFFFFFFF),
  //         m_default_vars(s.context()),
  //         m_vars(vars)
  //     {}

  //     cube_iterator begin() { return cube_iterator(_m_solver, m_vars, m_cutoff, false); }
  //     cube_iterator end() { return cube_iterator(_m_solver, m_vars, m_cutoff, true); }
  //     void set_cutoff(uint c) { m_cutoff = c; }
  // };

  // cube_generator cubes() { return cube_generator(*this); }
  // cube_generator cubes(expr_vector& vars) { return cube_generator(*this, vars); }

  string toString() {
    auto str = Z3_solver_to_string(context(), this);
    return cast(string) str[0..str.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}

struct Goal
{
  mixin HasContext;

  Z3_goal _m_goal;

  private void init(Z3_goal s) {
    _m_goal = s;
    Z3_goal_inc_ref(context(), _m_goal);
  }

  this(Context c, bool models=true, bool unsat_cores=false, bool proofs=false) {
    setContext(c);
    init(Z3_mk_goal(c, models, unsat_cores, proofs));
  }
  
  this(Context c, Z3_goal s) {
    setContext(c);
    init(s);
  }

  this(this) {
    assert (context() !is null);
    Z3_goal_inc_ref(context(), _m_goal);
  }

  // this(ref Goal s) {
  //   setContext(s.context());
  //   init(s._m_goal);
  // }

  ~this() {
    Z3_goal_dec_ref(context(), _m_goal);
  }

  Z3_goal native() {
    return _m_goal;
  }
  alias native this;

  ref Goal opAssign(ref Goal s) return {
    Z3_goal_inc_ref(s.context(), s._m_goal);
    Z3_goal_dec_ref(context(), _m_goal);
    setContext(s.context());
    _m_goal = s._m_goal;
    return this;
  }

  void add()(auto ref Expr f) {
    checkContext(this, f);
    Z3_goal_assert(context(), _m_goal, f.getAST);
    checkError();
  }

  void add()(auto ref ExprVector v) {
    checkContext(this, v);
    for (uint i = 0; i < v.size(); ++i) {
      auto ie = v[i];
      add(ie);
    }
  }
  uint size() { return Z3_goal_size(context(), _m_goal); }

  Expr opIndex(int i) {
    assert(0 <= i);
    Z3_ast r = Z3_goal_formula(context(), _m_goal, i);
    checkError();
    return Expr(context(), r);
  }
  
  Z3_goal_prec precision() {
    return Z3_goal_precision(context(), _m_goal);
  }
  bool inconsistent() {
    return Z3_goal_inconsistent(context(), _m_goal);
  }
  uint depth() {
    return Z3_goal_depth(context(), _m_goal);
  }
  void reset() {
    Z3_goal_reset(context(), _m_goal);
  }
  uint numExprs() {
    return Z3_goal_num_exprs(context(), _m_goal);
  }
  bool isDecidedSat() {
    return Z3_goal_is_decided_sat(context(), _m_goal);
  }
  bool isDecidedUnsat() {
    return Z3_goal_is_decided_unsat(context(), _m_goal);
  }
  Model convertModel()(auto ref Model m) {
    checkContext(this, m);
    Z3_model new_m = Z3_goal_convert_model(context(), _m_goal, m);
    checkError();
    return Model(context(), new_m);
  }
  Model getModel() {
    Z3_model new_m = Z3_goal_convert_model(context(), _m_goal, null);
    checkError();
    return Model(context(), new_m);
  }

  Expr asExpr() {
    uint n = size();
    if (n == 0)
      return context().boolVal(true);
    else if (n == 1)
      return opIndex(0);
    else {
      Z3_ast[] args = new Z3_ast[](n);
      for (uint i = 0; i < n; i++)
	args[i] = opIndex(i).getAST;
      return Expr(context(), Z3_mk_and(context(), n, args.ptr));
    }
  }
  string dimacs() {
    auto str = Z3_goal_to_dimacs_string(context(), _m_goal);
    return cast(string) str[0..str.strlen()];
  }

  string toString() {
    auto str = Z3_goal_to_string(context(), this);
    return cast(string) str[0..str.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}

struct ApplyResult
{
  mixin HasContext;
  
  Z3_apply_result _m_apply_result;
  private void init(Z3_apply_result s) {
    _m_apply_result = s;
    Z3_apply_result_inc_ref(context(), _m_apply_result);
  }

  this(Context c, Z3_apply_result s) {
    setContext(c);
    init(s);
  }

  this(this) {
    assert (context() !is null);
    Z3_apply_result_inc_ref(context(), _m_apply_result);
  }

  // this(ref ApplyResult s) {
  //   setContext(s.context);
  //   init(s._m_apply_result);
  // }
  ~this() {
    Z3_apply_result_dec_ref(context(), _m_apply_result);
  }
  Z3_apply_result native() {
    return _m_apply_result;
  }
  alias native this;
  ref ApplyResult opAssign(ref ApplyResult s) return {
    Z3_apply_result_inc_ref(s.context(), s._m_apply_result);
    Z3_apply_result_dec_ref(context(), _m_apply_result);
    setContext(s.context());
    _m_apply_result = s._m_apply_result;
    return this;
  }
  uint size() {
    return Z3_apply_result_get_num_subgoals(context(), _m_apply_result);
  }
  Goal opIndex(int i) {
    assert(0 <= i);
    Z3_goal r = Z3_apply_result_get_subgoal(context(), _m_apply_result, i);
    checkError();
    return Goal(context(), r);
  }
  string toString() {
    auto str = Z3_apply_result_to_string(context(), this);
    return cast(string) str[0..str.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}


struct Tactic
{
  mixin HasContext;
  
  Z3_tactic _m_tactic;
  private void init(Z3_tactic s) {
    _m_tactic = s;
    Z3_tactic_inc_ref(context(), _m_tactic);
  }
  this(Context c, string name) {
    setContext(c);
    Z3_tactic r = Z3_mk_tactic(c, name.toStringz);
    checkError(); init(r);
  }
  this(Context c, Z3_tactic s) {
    setContext(c);
    init(s);
  }
  this(this) {
    assert (context() !is null);
    Z3_tactic_inc_ref(context(), _m_tactic);
  }
  // this(ref Tactic s) {
  //   setContext(s.context());
  //   init(s._m_tactic);
  // }
  ~this() {
    Z3_tactic_dec_ref(context(), _m_tactic);
  }
  Z3_tactic native() {
    return _m_tactic;
  }
  alias native this;
  ref Tactic opAssign(ref Tactic s) return {
    Z3_tactic_inc_ref(s.context(), s._m_tactic);
    Z3_tactic_dec_ref(context(), _m_tactic);
    setContext(s.context());
    _m_tactic = s._m_tactic;
    return this;
  }
  Solver mkSolver() {
    Z3_solver r = Z3_mk_solver_from_tactic(context(), _m_tactic);
    checkError();
    return Solver(context(), r);
  }

  ApplyResult apply()(auto ref Goal g) {
    checkContext(this, g);
    Z3_apply_result r = Z3_tactic_apply(context(), _m_tactic, g);
    checkError();
    return ApplyResult(context(), r);
  }
  
  ApplyResult opCall()(auto ref Goal g)  {
    return apply(g);
  }

  string help() {
    auto r = Z3_tactic_get_help(context(), _m_tactic);
    checkError();
    return cast(string) r[0..r.strlen()];
  }
  
  ParamDescrs getParamDescrs() {
    return ParamDescrs(context(), Z3_tactic_get_param_descrs(context(), _m_tactic));
  }
}

Tactic and()(auto ref Tactic t1, auto ref Tactic t2) {
  checkContext(t1, t2);
  Z3_tactic r = Z3_tactic_and_then(t1.context(), t1, t2);
  t1.checkError();
  return Tactic(t1.context(), r);
}

Tactic or()(auto ref Tactic t1, auto ref Tactic t2) {
  checkContext(t1, t2);
  Z3_tactic r = Z3_tactic_or_else(t1.context(), t1, t2);
  t1.checkError();
  return Tactic(t1.context(), r);
}

Tactic repeat()(auto ref Tactic t, uint max=uint.max) {
  Z3_tactic r = Z3_tactic_repeat(t.context(), t, max);
  t.checkError();
  return Tactic(t.context(), r);
}

Tactic withParam()(auto ref Tactic t, auto ref Params p) {
  Z3_tactic r = Z3_tactic_using_params(t.context(), t, p);
  t.checkError();
  return Tactic(t.context(), r);
}

Tactic tryFor()(auto ref Tactic t, uint ms) {
  Z3_tactic r = Z3_tactic_try_for(t.context(), t, ms);
  t.checkError();
  return Tactic(t.context(), r);
}

Tactic parOr(Tactic[] tactics) {
  if (tactics.length == 0) {
    throw (new Exception("a non-zero number of tactics need to be passed to par_or"));
  }
  Z3_tactic[] buffer = new Z3_tactic[](tactics.length);
  for (uint i = 0; i < tactics.length; ++i) buffer[i] = tactics[i];
  return Tactic(tactics[0].context(), Z3_tactic_par_or(tactics[0].context(),
						       cast(uint) buffer.length, buffer.ptr));
}

Tactic parAndThen()(auto ref Tactic t1, auto ref Tactic t2) {
  checkContext(t1, t2);
  Z3_tactic r = Z3_tactic_par_and_then(t1.context(), t1, t2);
  t1.checkError();
  return Tactic(t1.context(), r);
}

struct Probe
{
  mixin HasContext;
  mixin RvalueRef;
  
  Z3_probe _m_probe;

  private void init(Z3_probe s) {
    _m_probe = s;
    Z3_probe_inc_ref(context(), _m_probe);
  }

  this(Context c, string name) {
    setContext(c);
    Z3_probe r = Z3_mk_probe(c, name.toStringz);
    checkError();
    init(r);
  }
  this(Context c, double val) {
    setContext(c);
    Z3_probe r = Z3_probe_const(c, val);
    checkError();
    init(r);
  }
  this(Context c, Z3_probe s) {
    setContext(c);
    init(s);
  }
  this(this) {
    assert (context() !is null);
    Z3_probe_inc_ref(context(), _m_probe);
  }
  // this(ref Probe s) {
  //   setContext(s.context());
  //   init(s._m_probe);
  // }
  ~this() {
    Z3_probe_dec_ref(context(), _m_probe);
  }
  Z3_probe native() {
    return _m_probe;
  }
  alias native this;
  
  ref Probe opAssign(ref Probe s) return {
    Z3_probe_inc_ref(s.context(), s._m_probe);
    Z3_probe_dec_ref(context(), _m_probe);
    setContext(s.context());
    _m_probe = s._m_probe;
    return this;
  }

  double apply()(auto ref Goal g) {
    double r = Z3_probe_apply(context(), _m_probe, g);
    checkError();
    return r;
  }
  double opCall()(auto ref Goal g) {
    return apply(g);
  }

  // friend Probe operator<=(ref Probe p1, ref Probe p2);
  // friend Probe operator<=(ref Probe p1, double p2);
  // friend Probe operator<=(double p1, ref Probe p2);
  // friend Probe operator>=(ref Probe p1, ref Probe p2);
  // friend Probe operator>=(ref Probe p1, double p2);
  // friend Probe operator>=(double p1, ref Probe p2);
  // friend Probe operator<(ref Probe p1, ref Probe p2);
  // friend Probe operator<(ref Probe p1, double p2);
  // friend Probe operator<(double p1, ref Probe p2);
  // friend Probe operator>(ref Probe p1, ref Probe p2);
  // friend Probe operator>(ref Probe p1, double p2);
  // friend Probe operator>(double p1, ref Probe p2);
  // friend Probe operator==(ref Probe p1, ref Probe p2);
  // friend Probe operator==(ref Probe p1, double p2);
  // friend Probe operator==(double p1, ref Probe p2);
  // friend Probe operator&&(ref Probe p1, ref Probe p2);
  // friend Probe operator||(ref Probe p1, ref Probe p2);
  // friend Probe operator!(ref Probe p);
}

Probe le()(auto ref Probe p1, auto ref Probe p2) {
  checkContext(p1, p2);
  Z3_probe r = Z3_probe_le(p1.context(), p1, p2);
  p1.checkError();
  return Probe(p1.context(), r);
}
Probe le()(auto ref Probe p1, double p2) {
  return le(p1, Probe(p1.context(), p2).byRef());
}
Probe le()(double p1, auto ref Probe p2) {
  return le(Probe(p2.context(), p1).byRef, p2);
}
Probe ge()(auto ref Probe p1, auto ref Probe p2) {
  checkContext(p1, p2);
  Z3_probe r = Z3_probe_ge(p1.context(), p1, p2);
  p1.checkError();
  return Probe(p1.context(), r);
}
Probe ge()(auto ref Probe p1, double p2) {
  return ge(p1, Probe(p1.context(), p1).byRef);
}
Probe ge()(double p1, auto ref Probe p2) {
  return ge(Probe(p2.context(), p1).byRef, p2);
}
Probe lt()(auto ref Probe p1, auto ref Probe p2) {
  checkContext(p1, p2);
  Z3_probe r = Z3_probe_lt(p1.context(), p1, p2);
  p1.checkError();
  return Probe(p1.context(), r);
}
Probe lt()(auto ref Probe p1, double p2) {
  return lt(p1, Probe(p1.context(), p1).byRef);
}
Probe lt()(double p1, auto ref Probe p2) {
  return lt(Probe(p2.context(), p1).byRef, p2);
}
Probe gt()(auto ref Probe p1, auto ref Probe p2) {
  checkContext(p1, p2);
  Z3_probe r = Z3_probe_gt(p1.context(), p1, p2);
  p1.checkError();
  return Probe(p1.context(), r);
}
Probe gt()(auto ref Probe p1, double p2) {
  return gt(p1, Probe(p1.context(), p1).byRef);
}
Probe gt()(double p1, auto ref Probe p2) {
  return gt(Probe(p2.context(), p1).byRef, p2);
}
Probe eq()(auto ref Probe p1, auto ref Probe p2) {
  checkContext(p1, p2);
  Z3_probe r = Z3_probe_eq(p1.context(), p1, p2);
  p1.checkError();
  return Probe(p1.context(), r);
}
Probe eq()(auto ref Probe p1, double p2) {
  return eq(p1, Probe(p1.context(), p1).byRef);
}
Probe eq()(double p1, auto ref Probe p2) {
  return eq(Probe(p2.context(), p1).byRef, p2);
}
Probe and()(auto ref Probe p1, auto ref Probe p2) {
  checkContext(p1, p2);
  Z3_probe r = Z3_probe_and(p1.context(), p1, p2);
  p1.checkError();
  return Probe(p1.context(), r);
}
Probe or()(auto ref Probe p1, auto ref Probe p2) {
  checkContext(p1, p2);
  Z3_probe r = Z3_probe_or(p1.context(), p1, p2);
  p1.checkError();
  return Probe(p1.context(), r);
}
Probe not()(auto ref Probe p) {
  Z3_probe r = Z3_probe_not(p.context(), p);
  p.checkError();
  return Probe(p.context(), r);
}

struct Optimize
{
  mixin HasContext;
  Z3_optimize _m_opt;

  struct handle {
    uint _m_h;
    this(uint h) {_m_h = h;}
    uint h() { return _m_h; }
  }

  this(Context c) {
    setContext(c);
    _m_opt = Z3_mk_optimize(c);
    Z3_optimize_inc_ref(c, _m_opt);
  }

  this(this) {
    assert (context() !is null);
    Z3_optimize_inc_ref(context(), _m_opt);
  }

  // this(ref Optimize o)  {
  //   setContext(o.context);
  //   Z3_optimize_inc_ref(o.context(), o._m_opt);
  //   _m_opt = o._m_opt;
  // }

  ref Optimize opAssign(ref Optimize o) return {
    Z3_optimize_inc_ref(o.context(), o._m_opt);
    Z3_optimize_dec_ref(context(), _m_opt);
    _m_opt = o._m_opt;
    setContext(o.context());
    return this;
  }

  ~this() {
    Z3_optimize_dec_ref(context(), _m_opt);
  }
  
  Z3_optimize native() {
    return _m_opt;
  }
  alias native this;

  void add()(auto ref Expr e) {
    assert (e.isBool());
    Z3_optimize_assert(context(), _m_opt, e.getAST);
  }

  handle add()(auto ref Expr e, uint weight) {
    import std.conv: to;
    assert (e.isBool());
    return handle(Z3_optimize_assert_soft(context(), _m_opt, e.getAST,
					  weight.to!string.toStringz, null));
  }

  handle add()(auto ref Expr e, uint weight, string id) {
    import std.conv: to;
    assert (e.isBool());
    return handle(Z3_optimize_assert_soft(context(), _m_opt, e.getAST,
					  weight.to!string.toStringz,
					  context().strSymbol(id)));
  }

  void add()(auto ref Expr e, auto ref Expr t) {
    assert (e.isBool());
    Z3_optimize_assert_and_track(context(), _m_opt, e.getAST, t.getAST);
  }

  handle add()(auto ref Expr e, string weight) {
    assert (e.isBool());
    return handle(Z3_optimize_assert_soft(context(), _m_opt, e.getAST, weight.toStringz, null));
  }

  handle maximize()(auto ref Expr e) {
    return handle(Z3_optimize_maximize(context(), _m_opt, e.getAST));
  }

  handle minimize()(auto ref Expr e) {
    return handle(Z3_optimize_minimize(context(), _m_opt, e.getAST));
  }

  void push() {
    Z3_optimize_push(context(), _m_opt);

  }
  void pop() {
    Z3_optimize_pop(context(), _m_opt);
  }

  CheckResult check() {
    Z3_lbool r = Z3_optimize_check(context(), _m_opt, 0, null);
    checkError();
    return toCheckResult(r);
  }
  
  CheckResult check()(auto ref ExprVector asms) {
    uint n = asms.size();
    Z3_ast[] _asms = new Z3_ast[](n);
    for (uint i = 0; i < n; i++) {
      checkContext(this, asms[i]);
      _asms[i] = asms[i].getAST;
    }
    Z3_lbool r = Z3_optimize_check(context(), _m_opt, n, _asms.ptr);
    checkError();
    return toCheckResult(r);
  }

  Model getModel() {
    Z3_model m = Z3_optimize_get_model(context(), _m_opt);
    checkError();
    return Model(context(), m);
  }

  ExprVector unsatCore() {
    Z3_ast_vector r = Z3_optimize_get_unsat_core(context(), _m_opt);
    checkError();
    return ExprVector(context(), r);
  }

  void set()(auto ref Params p) {
    Z3_optimize_set_params(context(), _m_opt, p);
    checkError();
  }

  Expr lower()(auto ref handle h) {
    Z3_ast r = Z3_optimize_get_lower(context(), _m_opt, h.h());
    checkError();
    return Expr(context(), r);
  }
  Expr upper()(auto ref handle h) {
    Z3_ast r = Z3_optimize_get_upper(context(), _m_opt, h.h());
    checkError();
    return Expr(context(), r);
  }

  ExprVector assertions() {
    Z3_ast_vector r = Z3_optimize_get_assertions(context(), _m_opt);
    checkError();
    return ExprVector(context(), r);
  }

  ExprVector objectives() {
    Z3_ast_vector r = Z3_optimize_get_objectives(context(), _m_opt);
    checkError();
    return ExprVector(context(), r);
  }

  Stats statistics() {
    Z3_stats r = Z3_optimize_get_statistics(context(), _m_opt);
    checkError();
    return Stats(context(), r);
  }
  void fromFile(string filename) {
    Z3_optimize_from_file(context(), _m_opt, filename.toStringz);
    checkError();
  }
  void fromString(string constraints) {
    Z3_optimize_from_string(context(), _m_opt, constraints.toStringz);
    checkError();
  }
  
  string help() {
    auto r = Z3_optimize_get_help(context(), _m_opt);
    checkError();
    return cast(string) r[0..r.strlen()];
  }

  string toString() {
    auto str = Z3_optimize_to_string(context(), this);
    return cast(string) str[0..str.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
}

struct Fixedpoint
{
  mixin HasContext;
  
  Z3_fixedpoint _m_fp;
  this(Context c) {
    setContext(c);
    _m_fp = Z3_mk_fixedpoint(c);
    Z3_fixedpoint_inc_ref(c, _m_fp);
  }
  ~this() {
    Z3_fixedpoint_dec_ref(context(), _m_fp);
  }
  Z3_fixedpoint native() {
    return _m_fp;
  }
  alias native this;
  
  void fromString(string s) {
    Z3_fixedpoint_from_string(context(), _m_fp, s.toStringz);
    checkError();
  }
  void fromFile(string s) {
    Z3_fixedpoint_from_file(context(), _m_fp, s.toStringz);
    checkError();
  }
  void addRule()(auto ref Expr rule, auto ref Symbol name) {
    Z3_fixedpoint_add_rule(context(), _m_fp, rule.getAST, name);
    checkError();
  }
  void addFact()(auto ref FuncDecl f, uint[] args) {
    Z3_fixedpoint_add_fact(context(), _m_fp, f, f.arity(), args.ptr);
    checkError();
  }
  CheckResult query()(auto ref Expr q) {
    Z3_lbool r = Z3_fixedpoint_query(context(), _m_fp, q.getAST);
    checkError();
    return toCheckResult(r);
  }
  CheckResult query()(auto ref FuncDeclVector relations) {
    Z3_func_decl[] rs = relations.toArray!Z3_func_decl();
    Z3_lbool r = Z3_fixedpoint_query_relations(context(), _m_fp, cast(uint) rs.length, rs.ptr);
    checkError();
    return toCheckResult(r);
  }
  Expr getAnswer() {
    Z3_ast r = Z3_fixedpoint_get_answer(context(), _m_fp);
    checkError();
    return Expr(context(), r);
  }
  string reasonUnknown() {
    auto r = Z3_fixedpoint_get_reason_unknown(context(), _m_fp);
    return cast(string) r[0..r.strlen()];
  }
  void updateRule()(auto ref Expr rule, auto ref Symbol name) {
    Z3_fixedpoint_update_rule(context(), _m_fp, rule.getAST, name);
    checkError();
  }
  uint getNumLevels()(auto ref FuncDecl p) {
    uint r = Z3_fixedpoint_get_num_levels(context(), _m_fp, p);
    checkError();
    return r;
  }
  Expr getCoverDelta(int level, FuncDecl p) {
    Z3_ast r = Z3_fixedpoint_get_cover_delta(context(), _m_fp, level, p);
    checkError();
    return Expr(context(), r);
  }
  void addCover()(int level, auto ref FuncDecl p, auto ref Expr property) {
    Z3_fixedpoint_add_cover(context(), _m_fp, level, p, property.getAST);
    checkError();
  }
  Stats statistics() {
    Z3_stats r = Z3_fixedpoint_get_statistics(context(), _m_fp);
    checkError();
    return Stats(context(), r);
  }
  void registerRelation()(auto ref FuncDecl p) {
    Z3_fixedpoint_register_relation(context(), _m_fp, p);
  }
  ExprVector assertions() {
    Z3_ast_vector r = Z3_fixedpoint_get_assertions(context(), _m_fp);
    checkError();
    return ExprVector(context(), r);
  }
  ExprVector rules() {
    Z3_ast_vector r = Z3_fixedpoint_get_rules(context(), _m_fp);
    checkError();
    return ExprVector(context(), r);
  }
  void set()(auto ref Params p) {
    Z3_fixedpoint_set_params(context(), _m_fp, p);
    checkError();
  }
  string help() {
    auto r = Z3_fixedpoint_get_help(context(), _m_fp);
    return cast(string) r[0..r.strlen()];
  }
  ParamDescrs getParamDescrs() {
    return ParamDescrs(context(), Z3_fixedpoint_get_param_descrs(context(), _m_fp));
  }
  string toString() {
    auto str = Z3_fixedpoint_to_string(context(), this, 0, null);
    return cast(string) str[0..str.strlen];
  }
  V to(V)() if (is(V == string)) {
    return this.toString();
  }
  string toString()(auto ref ExprVector queries) {
    Z3_ast[] qs = queries.toArray!Z3_ast();
    auto str = Z3_fixedpoint_to_string(context(), _m_fp, cast(uint) qs.length, qs.ptr);
    return cast(string) str[0..str.strlen];
  }
}

/**
   \brief Return an expression representing <tt>not(a)</tt>.

   \pre a.is_bool()
*/
// friend expr operator!(expr & a);
Expr not()(auto ref Expr a) {
  assert(a.isBool());
  // _Z3_MK_UN_(a, Z3_mk_not);
  Z3_ast r = Z3_mk_not(a.context(), a.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
  

/**
   \brief Return an expression representing <tt>a and b</tt>.

   \pre a.is_bool()
   \pre b.is_bool()
*/
// friend expr operator&&(expr & a, expr & b);

Expr and()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  assert (a.isBool() && b.isBool());
  Z3_ast[2] args = [a.getAST, b.getAST];
  Z3_ast r = Z3_mk_and(a.context(), 2, args.ptr);
  a.checkError();
  return Expr(a.context(), r);
}
  

/**
   \brief Return an expression representing <tt>a and b</tt>.
   The C++ Boolean value \c b is automatically converted into a Z3 Boolean constant.

   \pre a.is_bool()
*/
// friend expr operator&&(expr & a, bool b);

Expr and()(auto ref Expr a, bool b) {
  return and(a, a.context().boolVal(b).byRef);
}
  
/**
   \brief Return an expression representing <tt>a and b</tt>.
   The C++ Boolean value \c a is automatically converted into a Z3 Boolean constant.

   \pre b.is_bool()
*/
// friend expr operator&&(bool a, expr & b);
  
Expr and()(bool a, auto ref Expr b) {
  return and(b.context().boolVal(a).byRef, b);
}
  
/**
   \brief Return an expression representing <tt>a or b</tt>.

   \pre a.is_bool()
   \pre b.is_bool()
*/
// friend expr operator||(expr & a, expr & b);

Expr or()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  assert (a.isBool() && b.isBool());
  Z3_ast[2] args = [a.getAST, b.getAST];
  Z3_ast r = Z3_mk_or(a.context(), 2, args.ptr);
  a.checkError();
  return Expr(a.context(), r);
}
  
/**
   \brief Return an expression representing <tt>a or b</tt>.
   The C++ Boolean value \c b is automatically converted into a Z3 Boolean constant.

   \pre a.is_bool()
*/
// friend expr operator||(expr & a, bool b);

Expr or()(auto ref Expr a, bool b) {
  return or(a, a.context().boolVal(b).byRef);
}

/**
   \brief Return an expression representing <tt>a or b</tt>.
   The C++ Boolean value \c a is automatically converted into a Z3 Boolean constant.

   \pre b.is_bool()
*/
// friend expr operator||(bool a, expr const & b);

Expr or()(bool a, auto ref Expr b) {
  return or(b.context().boolVal(a).byRef, b);
}
  

Tactic fail_if()(auto ref Probe p) {
  Z3_tactic r = Z3_tactic_fail_if(p.context(), p);
  p.checkError();
  return Tactic(p.context(), r);
}
Tactic when()(auto ref Probe p, auto ref Tactic t) {
  checkContext(p, t);
  Z3_tactic r = Z3_tactic_when(t.context(), p, t);
  t.checkError();
  return Tactic(t.context(), r);
}

Tactic cond()(auto ref Probe p, auto ref Tactic t1, auto ref Tactic t2) {
  checkContext(p, t1); checkContext(p, t2);
  Z3_tactic r = Z3_tactic_cond(t1.context(), p, t1, t2);
  t1.checkError();
  return Tactic(t1.context(), r);
}

// friend expr implies(expr & a, expr & b);
Expr implies()(auto ref Expr a, auto ref Expr b) {
  assert (a.isBool() && b.isBool());
  checkContext(a, b);
  Z3_ast r = Z3_mk_implies(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr implies(expr & a, bool b);
Expr implies()(auto ref Expr a, bool b) {
  return implies(a, a.context().boolVal(b).byRef);
}

// friend expr implies(bool a, expr & b);
Expr implies()(bool a, auto ref Expr b) {
  return implies(b.context().boolVal(a).byRef, b);
}

// /**
//    \brief Return an expression representing <tt>a or b</tt>.
//    The C++ Boolean value \c a is automatically converted into a Z3 Boolean constant.

//    \pre b.is_bool()
// */
// friend expr operator||(bool a, expr & b);

// friend expr mk_or(expr_vector const& args);
Expr mkOr()(auto ref ExprVector args) {
  Z3_ast[] _args = args.toArray!Z3_ast();
  Z3_ast r = Z3_mk_or(args.context(), cast(uint) _args.length, _args.ptr);
  args.checkError();
  return Expr(args.context(), r);
}

// friend expr mk_and(expr_vector const& args);
Expr mkAnd()(auto ref ExprVector args) {
  Z3_ast[] _args = args.toArray!Z3_ast();
  Z3_ast r = Z3_mk_and(args.context(), cast(uint) _args.length, _args.ptr);
  args.checkError();
  return Expr(args.context(), r);
}

// friend expr ite(expr & c, expr & t, expr & e);
Expr ite()(auto ref Expr c, auto ref Expr t, auto ref Expr e) {
  checkContext(c, t); checkContext(c, e);
  assert(c.isBool());
  Z3_ast r = Z3_mk_ite(c.context, c.getAST, t.getAST, e.getAST);
  c.checkError();
  return Expr(c.context(), r);
}

// friend expr distinct(expr_vector const& args);
Expr distinct()(auto ref ExprVector args) {
  assert (args.size() > 0);
  Context ctx = args.context();
  Z3_ast[] _args = args.toArray!Z3_ast();
  Z3_ast r = Z3_mk_distinct(args.context(), cast(uint) _args.length, _args.ptr);
  args.checkError();
  return Expr(args.context(), r);
}

// friend expr concat(expr const& a, expr const& b);
Expr concat()(auto ref Expr a, auto ref Expr b) {
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
  return Expr(a.context(), r);
}

// friend expr concat(expr_vector const& args);
Expr concat()(auto ref ExprVector args) {
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
  return Expr(args.context(), r);
}

// friend expr operator==(expr & a, expr & b);
Expr eq()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_eq(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator==(expr & a, int b);
Expr eq()(auto ref Expr a, int b) {
  assert (a.isArith() || a.isBv() || a.isFpa());
  return eq(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator==(int a, expr & b);
Expr eq()(int a, auto ref Expr b) {
  assert(b.isArith() || b.isBv() || b.isFpa());
  return eq(b.context().numVal(a, b.getSort().byRef).byRef, b);
}



// friend expr operator!=(expr & a, expr & b);
Expr neq()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast[2] args = [a.getAST, b.getAST];
  Z3_ast r = Z3_mk_distinct(a.context(), 2, args.ptr);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator!=(expr & a, int b);
Expr neq()(auto ref Expr a, int b) {
  assert (a.isArith() || a.isBv() || a.isFpa());
  return neq(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator!=(int a, expr & b);
Expr neq()(int a, auto ref Expr b) {
  assert(b.isArith() || b.isBv() || b.isFpa());
  return neq(b.context().numVal(a, b.getSort().byRef).byRef, b);
}


// friend expr operator+(expr & a, expr & b);
Expr add()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    Z3_ast[2] args = [a.getAST, b.getAST];
    r = Z3_mk_add(a.context(), 2, args.ptr);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvadd(a.context(), a.getAST, b.getAST);
  }
  else if (a.isSeq() && b.isSeq()) {
    return concat(a, b);
  }
  else if (a.isRe() && b.isRe()) {
    Z3_ast[2] _args = [a.getAST, b.getAST];
    r = Z3_mk_re_union(a.context(), 2, _args.ptr);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_add(a.context(), cast(Z3_ast) a.context().fpaRoundingMode(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert (false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator+(expr & a, int b);
Expr add()(auto ref Expr a, int b) {
  return add(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
    
// friend expr operator+(int a, expr & b);
Expr add()(int a, auto ref Expr b) {
  return add(b.context().numVal(a, b.getSort().byRef).byRef, b);
}


// friend expr sum(expr_vector const& args);
Expr sum()(auto ref ExprVector args) {
  assert (args.size() > 0);
  Context ctx = args.context();
  Z3_ast[] _args = args.toArray!Z3_ast();
  Z3_ast r = Z3_mk_add(args.context(), cast(uint) _args.length, _args.ptr);
  args.checkError();
  return Expr(args.context(), r);
}


// friend expr operator*(expr & a, expr & b);
Expr mul()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    Z3_ast[2] args = [a.getAST, b.getAST];
    r = Z3_mk_mul(a.context(), 2, args.ptr);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvmul(a.context(), a.getAST, b.getAST);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_mul(a.context(), cast(Z3_ast) a.context().fpaRoundingMode(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert (false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator*(expr & a, int b);
Expr mul()(auto ref Expr a, int b) {
  return mul(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator*(int a, expr & b);
Expr mul()(int a, auto ref Expr b) {
  return mul(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// /*  \brief Power operator  */
// friend expr pw(expr & a, expr & b);
Expr pw()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_power(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr pw(expr & a, int b);
Expr pw()(auto ref Expr a, int b) {
  return pw(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr pw(int a, expr & b);
Expr pw()(int a, auto ref Expr b) {
  return pw(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// /* \brief mod operator */
// friend expr mod(expr const& a, expr const& b);
Expr mod()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r;
  if (a.isBv()) {
    r = Z3_mk_bvsmod(a.context(), a.getAST, b.getAST);
  }
  else {
    r = Z3_mk_mod(a.context(), a.getAST, b.getAST);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr mod(expr const& a, int b);
Expr mod()(auto ref Expr a, int b) {
  return mod(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr mod(int a, expr const& b);
Expr mod()(int a, auto ref Expr b) {
  return mod(b.context().numVal(a, b.getSort().byRef).byRef, b);
}


// /* \brief rem operator */
// friend expr rem(expr const& a, expr const& b);
Expr rem()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r;
  if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_rem(a.context(), a.getAST, b.getAST);
  }
  else {
    r = Z3_mk_rem(a.context(), a.getAST, b.getAST);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr rem(expr const& a, int b);
Expr rem()(auto ref Expr a, int b) {
  return rem(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr rem(int a, expr const& b);
Expr rem()(int a, auto ref Expr b) {
  return rem(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr is_int(expr const& e);

Expr isInt()(auto ref Expr e) {
  Z3_ast r = Z3_mk_is_int(e.context(), e.getAST);
  e.checkError();
  return Expr(e.context(), r);
}


// friend expr operator/(expr & a, expr & b);
Expr div()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    r = Z3_mk_div(a.context(), a.getAST, b.getAST);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvsdiv(a.context(), a.getAST, b.getAST);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_div(a.context(), cast(Z3_ast) a.context().fpaRoundingMode(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert (false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator/(expr & a, int b);
Expr div()(auto ref Expr a, int b) {
  return div(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator/(int a, expr & b);
Expr div()(int a, auto ref Expr b) {
  return div(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr operator-(expr & a);
Expr neg()(auto ref Expr a) {
  Z3_ast r = null;
  if (a.isArith()) {
    r = Z3_mk_unary_minus(a.context(), a.getAST);
  }
  else if (a.isBv()) {
    r = Z3_mk_bvneg(a.context(), a.getAST);
  }
  else if (a.isFpa()) {
    r = Z3_mk_fpa_neg(a.context(), a.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert(false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator-(expr & a, expr & b);
Expr sub()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    Z3_ast[2] args = [a.getAST, b.getAST];
    r = Z3_mk_sub(a.context(), 2, args.ptr);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvsub(a.context(), a.getAST, b.getAST);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_sub(a.context(), cast(Z3_ast) a.context().fpaRoundingMode(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert(false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator-(expr & a, int b);
Expr sub()(auto ref Expr a, int b) {
  return sub(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator-(int a, expr & b);
Expr sub()(int a, auto ref Expr b) {
  return sub(b.context().numVal(a, b.getSort().byRef).byRef, b);
}


// friend expr operator<=(expr & a, expr & b);
Expr le()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    r = Z3_mk_le(a.context(), a.getAST, b.getAST);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvsle(a.context(), a.getAST, b.getAST);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_leq(a.context(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert (false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator<=(expr & a, int b);
Expr le()(auto ref Expr a, int b) {
  return le(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator<=(int a, expr & b);
Expr le()(int a, auto ref Expr b) {
  return le(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr operator>=(expr & a, expr & b);
Expr ge()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    r = Z3_mk_ge(a.context(), a.getAST, b.getAST);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvsge(a.context(), a.getAST, b.getAST);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_geq(a.context(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert (false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator>=(expr & a, int b);
Expr ge()(auto ref Expr a, int b) {
  return ge(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator>=(int a, expr & b);
Expr ge()(int a, auto ref Expr b) {
  return ge(b.context().numVal(a, b.getSort().byRef).byRef, b);
}


// friend expr operator<(expr & a, expr & b);
Expr lt()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    r = Z3_mk_lt(a.context(), a.getAST, b.getAST);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvslt(a.context(), a.getAST, b.getAST);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_lt(a.context(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert (false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator<(expr & a, int b);
Expr lt()(auto ref Expr a, int b) {
  return lt(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator<(int a, expr & b);
Expr lt()(int a, auto ref Expr b) {
  return lt(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr operator>(expr & a, expr & b);
Expr gt()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = null;
  if (a.isArith() && b.isArith()) {
    r = Z3_mk_gt(a.context(), a.getAST, b.getAST);
  }
  else if (a.isBv() && b.isBv()) {
    r = Z3_mk_bvsgt(a.context(), a.getAST, b.getAST);
  }
  else if (a.isFpa() && b.isFpa()) {
    r = Z3_mk_fpa_gt(a.context(), a.getAST, b.getAST);
  }
  else {
    // operator is not supported by given arguments.
    assert (false);
  }
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator>(expr & a, int b);
Expr gt()(auto ref Expr a, int b) {
  return gt(a, a.context().numVal(b, a.getSort().byRef).byRef);
}

// friend expr operator>(int a, expr & b);
Expr gt()(int a, auto ref Expr b) {
  return gt(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr pble(expr_vector const& es, int * coeffs, int bound);
Expr pble()(auto ref ExprVector es, int* coeffs, int bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_pble(es.context(), cast(uint) _es.length, _es.ptr, coeffs, bound);
  es.context.checkError();
  return Expr(es.context(), r);
}

// friend expr pbge(expr_vector const& es, int * coeffs, int bound);
Expr pbge()(auto ref ExprVector es, int* coeffs, int bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_pbge(es.context(), cast(uint) _es.length, _es.ptr, coeffs, bound);
  es.context.checkError();
  return Expr(es.context(), r);
}

// friend expr pbeq(expr_vector const& es, int * coeffs, int bound);
Expr pbeq()(auto ref ExprVector es, int* coeffs, int bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_pbeq(es.context(), cast(uint) _es.length, _es.ptr, coeffs, bound);
  es.context.checkError();
  return Expr(es.context(), r);
}

// friend expr atmost(expr_vector const& es, uint bound);
Expr atmost()(auto ref ExprVector es, uint bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_atmost(es.context(), cast(uint) _es.length, _es.ptr, bound);
  es.context.checkError();
  return Expr(es.context(), r);
}

// friend expr atleast(expr_vector const& es, uint bound);
Expr atleast()(auto ref ExprVector es, uint bound) {
  assert (es.size() > 0);
  Z3_ast[] _es = es.toArray!Z3_ast;
  Z3_ast r = Z3_mk_atleast(es.context(), cast(uint) _es.length, _es.ptr, bound);
  es.context.checkError();
  return Expr(es.context(), r);
}

// friend expr operator&(expr & a, expr & b);
Expr bvand()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvand(a.context(), a.getAST, b.getAST);
  return Expr(a.context(), r);
}
// friend expr operator&(expr & a, int b);
Expr bvand()(auto ref Expr a, int b) {
  return bvand(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
// friend expr operator&(int a, expr & b);
Expr bvand()(int a, auto ref Expr b) {
  return bvand(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr operator^(expr & a, expr & b);
Expr bvxor()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvxor(a.context(), a.getAST, b.getAST);
  return Expr(a.context(), r);
}
// friend expr operator^(expr & a, int b);
Expr bvxor()(auto ref Expr a, int b) {
  return bvxor(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
// friend expr operator^(int a, expr & b);
Expr bvXor()(int a, auto ref Expr b) {
  return bvxor(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr operator|(expr & a, expr & b);
Expr bvor()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvor(a.context(), a.getAST, b.getAST);
  return Expr(a.context(), r);
}
// friend expr operator|(expr & a, int b);
Expr bvor()(auto ref Expr a, int b) {
  return bvor(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
// friend expr operator|(int a, expr & b);
Expr bvor()(int a, auto ref Expr b) {
  return bvor(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

// friend expr nand(expr const& a, expr const& b);
Expr bvnand()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvnand(a.context(), a.getAST, b.getAST);
  return Expr(a.context(), r);
}
// friend expr nor(expr const& a, expr const& b);
Expr bvnor()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvnor(a.context(), a.getAST, b.getAST);
  return Expr(a.context(), r);
}
// friend expr xnor(expr const& a, expr const& b);
Expr bvxnor()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvxnor(a.context(), a.getAST, b.getAST);
  return Expr(a.context(), r);
}

// friend expr min(expr const& a, expr const& b);
Expr min()(auto ref Expr a, auto ref Expr b) { 
  checkContext(a, b); 
  Z3_ast r;
  if (a.isArith()) {
    r = Z3_mk_ite(a.context(), Z3_mk_ge(a.context(), a.getAST, b.getAST), b.getAST, a.getAST);
  }
  else if (a.isBv()) {
    r = Z3_mk_ite(a.context(), Z3_mk_bvuge(a.context(), a.getAST, b.getAST), b.getAST, a.getAST);
  }
  else {
    assert(a.isFpa());
    r = Z3_mk_fpa_min(a.context(), a.getAST, b.getAST); 
  }
  return Expr(a.context(), r); 
}

// friend expr max(expr const& a, expr const& b);
Expr max()(auto ref Expr a, auto ref Expr b) { 
  checkContext(a, b); 
  Z3_ast r;
  if (a.isArith()) {
    r = Z3_mk_ite(a.context(), Z3_mk_ge(a.context(), a.getAST, b.getAST), a.getAST, b.getAST);
  }
  else if (a.isBv()) {
    r = Z3_mk_ite(a.context(), Z3_mk_bvuge(a.context(), a.getAST, b.getAST), a.getAST, b.getAST);
  }
  else {
    assert(a.isFpa());
    r = Z3_mk_fpa_max(a.context(), a.getAST, b.getAST); 
  }
  return Expr(a.context(), r); 
}

// friend expr bv2int(expr const& a, bool is_signed); 
Expr bv2int()(auto ref Expr a, bool is_signed) {
  Z3_ast r = Z3_mk_bv2int(a.context(), a.getAST, is_signed);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr int2bv(uint n, expr const& a);
Expr int2bv()(uint n, auto ref Expr a) {
  Z3_ast r = Z3_mk_int2bv(a.context(), n, a.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr bvadd_no_overflow(expr const& a, expr const& b, bool is_signed);
Expr bvaddNoOverflow()(auto ref Expr a, auto ref Expr b, bool is_signed) { 
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvadd_no_overflow(a.context(), a.getAST, b.getAST, is_signed);
  a.checkError();
  return Expr(a.context(), r);
}
// friend expr bvadd_no_underflow(expr const& a, expr const& b);
Expr bvaddNoUnderflow()(auto ref Expr a, auto ref Expr b) { 
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvadd_no_underflow(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
// friend expr bvsub_no_overflow(expr const& a, expr const& b);
Expr bvsubNoOverflow()(auto ref Expr a, auto ref Expr b) { 
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvsub_no_overflow(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
// friend expr bvsub_no_underflow(expr const& a, expr const& b, bool is_signed);
Expr bvsubNoUnderflow()(auto ref Expr a, auto ref Expr b, bool is_signed) { 
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvsub_no_underflow(a.context(), a.getAST, b.getAST, is_signed);
  a.checkError();
  return Expr(a.context(), r);
}
// friend expr bvsdiv_no_overflow(expr const& a, expr const& b);
Expr bvdivNoOverflow()(auto ref Expr a, auto ref Expr b) { 
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvsdiv_no_overflow(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
// friend expr bvneg_no_overflow(expr const& a);
Expr bvnegNoOverflow()(auto ref Expr a) { 
  Z3_ast r = Z3_mk_bvneg_no_overflow(a.context(), a.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
// friend expr bvmul_no_overflow(expr const& a, expr const& b, bool is_signed);
Expr bvmulNoOverflow()(auto ref Expr a, auto ref Expr b, bool is_signed) { 
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvmul_no_overflow(a.context(), a.getAST, b.getAST, is_signed);
  a.checkError();
  return Expr(a.context(), r);
}
// friend expr bvmul_no_underflow(expr const& a, expr const& b);
Expr bvmulNoUnderflow()(auto ref Expr a, auto ref Expr b) { 
  checkContext(a, b);
  Z3_ast r = Z3_mk_bvmul_no_underflow(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr abs(expr & a);
Expr abs()(auto ref Expr a) { 
  Z3_ast r;
  if (a.isInt()) {
    Expr zero = a.context().intVal(0);
    r = Z3_mk_ite(a.context(), Z3_mk_ge(a.context(), a.getAST, zero.getAST), a.getAST, neg(a).getAST);
  }
  else if (a.isReal()) {
    Expr zero = a.context().realVal(0);
    r = Z3_mk_ite(a.context(), Z3_mk_ge(a.context(), a.getAST, zero.getAST), a.getAST, neg(a).getAST);
  }
  else {
    r = Z3_mk_fpa_abs(a.context(), a.getAST); 
  }
  a.checkError();
  return Expr(a.context(), r); 
}

// friend expr sqrt(expr & a, expr & rm);
Expr sqrt()(auto ref Expr a, auto ref Expr rm) {
  checkContext(a, rm);
  assert (a.isFpa());
  Z3_ast r = Z3_mk_fpa_sqrt(a.context(), rm.getAST, a.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr operator~(expr & a);
Expr bvnot()(auto ref Expr a) {
  Z3_ast r = Z3_mk_bvnot(a.context(), a.getAST);
  return Expr(a.context(), r);
}

// /**
//    \brief FloatingPoint fused multiply-add.
// */
// friend expr fma(expr const& a, expr const& b, expr const& c, expr const& rm);
Expr fma()(auto ref Expr a, auto ref Expr b, auto ref Expr c, auto ref Expr rm) {
  checkContext(a, b); checkContext(a, c); checkContext(a, rm);
  assert (a.isFpa() && b.isFpa() && c.isFpa());
  Z3_ast r = Z3_mk_fpa_fma(a.context(), rm.getAST, a.getAST, b.getAST, c.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

// friend expr range(expr const& lo, expr const& hi);
Expr range()(auto ref Expr lo, auto ref Expr hi) {
  checkContext(lo, hi);
  Z3_ast r = Z3_mk_re_range(lo.context(), lo.getAST, hi.getAST);
  lo.checkError();
  return Expr(lo.context(), r);
}

// Basic functions for creating quantified formulas.
// The C API should be used for creating quantifiers with patterns, weights, many variables, etc.
Expr forall()(auto ref Expr x, auto ref Expr b) {
  checkContext(x, b);
  Z3_app[] vars = [Z3_to_app(x.context(), x.getAST())];
  Z3_ast r = Z3_mk_forall_const(b.context(), 0, 1, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr forall()(auto ref Expr x1, auto ref Expr x2, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST())];
  Z3_ast r = Z3_mk_forall_const(b.context(), 0, 2, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr forall()(auto ref Expr x1, auto ref Expr x2, auto ref Expr x3, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b); checkContext(x3, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST()),
		   Z3_to_app(x3.context(), x3.getAST())];
  Z3_ast r = Z3_mk_forall_const(b.context(), 0, 3, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr forall()(auto ref Expr x1, auto ref Expr x2, auto ref Expr x3, auto ref Expr x4, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b); checkContext(x3, b); checkContext(x4, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST()),
		   Z3_to_app(x3.context(), x3.getAST()),
		   Z3_to_app(x4.context(), x4.getAST())];
  Z3_ast r = Z3_mk_forall_const(b.context(), 0, 4, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr forall()(auto ref ExprVector xs, auto ref Expr b) {
  Z3_app[] vars = xs.toArray!Z3_app;
  Z3_ast r = Z3_mk_forall_const(b.context(), 0, cast(uint) vars.length, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr exists()(auto ref Expr x, auto ref Expr b) {
  checkContext(x, b);
  Z3_app[] vars = [Z3_to_app(x.context(), x.getAST())];
  Z3_ast r = Z3_mk_exists_const(b.context(), 0, 1, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr exists()(auto ref Expr x1, auto ref Expr x2, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST())];
  Z3_ast r = Z3_mk_exists_const(b.context(), 0, 2, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr exists()(auto ref Expr x1, auto ref Expr x2, auto ref Expr x3, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b); checkContext(x3, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST()),
		   Z3_to_app(x3.context(), x3.getAST())];
  Z3_ast r = Z3_mk_exists_const(b.context(), 0, 3, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr exists()(auto ref Expr x1, auto ref Expr x2, auto ref Expr x3, auto ref Expr x4, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b); checkContext(x3, b); checkContext(x4, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST()),
		   Z3_to_app(x3.context(), x3.getAST()),
		   Z3_to_app(x4.context(), x4.getAST())];
  Z3_ast r = Z3_mk_exists_const(b.context(), 0, 4, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr exists()(auto ref ExprVector xs, auto ref Expr b) {
  Z3_app[] vars = xs.toArray!Z3_app();
  Z3_ast r = Z3_mk_exists_const(b.context(), 0, cast(uint) vars.length, vars.ptr, 0, null, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr lambda()(auto ref Expr x, auto ref Expr b) {
  checkContext(x, b);
  Z3_app[] vars = [Z3_to_app(x.context(), x.getAST())];
  Z3_ast r = Z3_mk_lambda_const(b.context(), 1, vars.ptr, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr lambda()(auto ref Expr x1, auto ref Expr x2, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST())];
  Z3_ast r = Z3_mk_lambda_const(b.context(), 2, vars.ptr, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr lambda()(auto ref Expr x1, auto ref Expr x2, auto ref Expr x3, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b); checkContext(x3, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST()),
		   Z3_to_app(x3.context(), x3.getAST())];
  Z3_ast r = Z3_mk_lambda_const(b.context(), 3, vars.ptr, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr lambda()(auto ref Expr x1, auto ref Expr x2, auto ref Expr x3, auto ref Expr x4, auto ref Expr b) {
  checkContext(x1, b); checkContext(x2, b); checkContext(x3, b); checkContext(x4, b);
  Z3_app[] vars = [Z3_to_app(x1.context(), x1.getAST()),
		   Z3_to_app(x2.context(), x2.getAST()),
		   Z3_to_app(x3.context(), x3.getAST()),
		   Z3_to_app(x4.context(), x4.getAST())];
  Z3_ast r = Z3_mk_lambda_const(b.context(), 4, vars.ptr, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}
Expr lambda()(auto ref ExprVector xs, auto ref Expr b) {
  Z3_app[] vars = xs.toArray!Z3_app();
  Z3_ast r = Z3_mk_lambda_const(b.context(), cast(uint) vars.length, vars.ptr, b.getAST);
  b.checkError();
  return Expr(b.context(), r);
}


/**
   \brief Wraps a Z3_ast as an expr object. It also checks for errors.
   This function allows the user to use the whole C API with the C++ layer defined in this file.
*/
Expr toExpr(Context c, Z3_ast a) {
  c.checkError();
  assert (Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_APP_AST ||
	  Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_NUMERAL_AST ||
	  Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_VAR_AST ||
	  Z3_get_ast_kind(c, a) == Z3_ast_kind.Z3_QUANTIFIER_AST);
  return Expr(c, a);
}

Sort toSort(Context c, Z3_sort s) {
  c.checkError();
  return Sort(c, s);
}

FuncDecl toFuncDecl(Context c, Z3_func_decl f) {
  c.checkError();
  return FuncDecl(c, f);
}

/**
   \brief signed less than or equal to operator for bitvectors.
*/
Expr sle()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvsle(a.context(), a.getAST, b.getAST));
}
Expr sle()(auto ref Expr a, int b) {
  return sle(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr sle()(int a, auto ref Expr b) {
  return sle(b.context().numVal(a, b.getSort().byRef).byRef, b);
}
/**
   \brief signed less than operator for bitvectors.
*/
Expr slt()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvslt(a.context(), a.getAST, b.getAST));
}
Expr slt()(auto ref Expr a, int b) {
  return slt(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr slt()(int a, auto ref Expr b) {
  return slt(b.context().numVal(a, b.getSort().byRef).byRef, b);
}


/**
   \brief unsigned less than or equal to operator for bitvectors.
*/
Expr ule()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvule(a.context(), a.getAST, b.getAST));
}
Expr ule()(auto ref Expr a, int b) {
  return ule(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr ule()(int a, auto ref Expr b) {
  return ule(b.context().numVal(a, b.getSort().byRef).byRef, b);
}
/**
   \brief unsigned less than operator for bitvectors.
*/
Expr ult()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvult(a.context(), a.getAST, b.getAST));
}
Expr ult()(auto ref Expr a, int b) {
  return ult(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr ult()(int a, auto ref Expr b) {
  return ult(b.context().numVal(a, b.getSort().byRef).byRef, b);
}
/**
   \brief unsigned greater than or equal to operator for bitvectors.
*/
Expr uge()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvuge(a.context(), a.getAST, b.getAST));
}
Expr uge()(auto ref Expr a, int b) {
  return uge(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr uge()(int a, auto ref Expr b) {
  return uge(b.context().numVal(a, b.getSort().byRef).byRef, b);
}
/**
   \brief unsigned greater than operator for bitvectors.
*/
Expr ugt()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvugt(a.context(), a.getAST, b.getAST));
}
Expr ugt()(auto ref Expr a, int b) {
  return ugt(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr ugt()(int a, auto ref Expr b) {
  return ugt(b.context().numVal(a, b.getSort().byRef).byRef, b);
}
/**
   \brief unsigned division operator for bitvectors.
*/
Expr udiv()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvudiv(a.context(), a.getAST, b.getAST));
}
Expr udiv()(auto ref Expr a, int b) {
  return udiv(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr udiv()(int a, auto ref Expr b) {
  return udiv(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

/**
   \brief signed remainder operator for bitvectors
*/
Expr srem()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvsrem(a.context(), a.getAST, b.getAST));
}
Expr srem()(auto ref Expr a, int b) {
  return srem(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr srem()(int a, auto ref Expr b) {
  return srem(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

/**
   \brief signed modulus operator for bitvectors
*/
Expr smod()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvsmod(a.context(), a.getAST, b.getAST));
}
Expr smod()(auto ref Expr a, int b) {
  return smod(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr smod()(int a, auto ref Expr b) {
  return smod(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

/**
   \brief unsigned reminder operator for bitvectors
*/
Expr urem()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvurem(a.context(), a.getAST, b.getAST));
}
Expr urem()(auto ref Expr a, int b) {
  return urem(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr urem()(int a, auto ref Expr b) {
  return urem(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

/**
   \brief shift left operator for bitvectors
*/
Expr shl()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvshl(a.context(), a.getAST, b.getAST));
}
Expr shl()(auto ref Expr a, int b) {
  return shl(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr shl()(int a, auto ref Expr b) {
  return shl(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

/**
   \brief logic shift right operator for bitvectors
*/
Expr lshr()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvlshr(a.context(), a.getAST, b.getAST));
}
Expr lshr()(auto ref Expr a, int b) {
  return lshr(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr lshr()(int a, auto ref Expr b) {
  return lshr(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

/**
   \brief arithmetic shift right operator for bitvectors
*/
Expr ashr()(auto ref Expr a, auto ref Expr b) {
  return toExpr(a.context(), Z3_mk_bvashr(a.context(), a.getAST, b.getAST));
}
Expr ashr()(auto ref Expr a, int b) {
  return ashr(a, a.context().numVal(b, a.getSort().byRef).byRef);
}
Expr ashr()(int a, auto ref Expr b) {
  return ashr(b.context().numVal(a, b.getSort().byRef).byRef, b);
}

/**
   \brief Extend the given bit-vector with zeros to the (unsigned) equivalent bitvector of size m+i, where m is the size of the given bit-vector.
*/
Expr zext()(auto ref Expr a, uint i) {
  return toExpr(a.context(), Z3_mk_zero_ext(a.context(), i, a.getAST));
}

/**
   \brief Extend the given bit-vector with sign bit to the (signed) equivalent bitvector of size m+i, where m is the size of the given bit-vector.
*/
Expr sext()(auto ref Expr a, uint i) {
  return toExpr(a.context(), Z3_mk_sign_ext(a.context(), i, a.getAST));
}


Expr toReal()(auto ref Expr a) {
  Z3_ast r = Z3_mk_int2real(a.context(), a.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

FuncDecl func()(auto ref Symbol name, Sort[] domain, auto ref Sort range) {
  return range.context().func(name, domain, range);
}
FuncDecl func()(string name, Sort[] domain, auto ref Sort range) {
  return range.context().func(name, domain, range);
}
FuncDecl func()(string name, auto ref Sort domain, auto ref Sort range) {
  return range.context().func(name, domain, range);
}
FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort range) {
  return range.context().func(name, d1, d2, range);
}
FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort d3, auto ref Sort range) {
  return range.context().func(name, d1, d2, d3, range);
}
FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2,
	      auto ref Sort d3, auto ref Sort d4, auto ref Sort range) {
  return range.context().func(name, d1, d2, d3, d4, range);
}
FuncDecl func()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort d3,
	      auto ref Sort d4, auto ref Sort d5, auto ref Sort range) {
  return range.context().func(name, d1, d2, d3, d4, d5, range);
}
FuncDecl func()(string name, auto ref SortVector domain, auto ref Sort range) {
  return range.context().func(name, domain, range);
}
FuncDecl recfun()(Symbol name, Sort[] domain, auto ref Sort range) {
  return range.context().recfun(name, domain, range);
}
FuncDecl recfun()(string name, Sort[] domain, auto ref Sort range) {
  return range.context().recfun(name, domain, range);
}
FuncDecl recfun()(string name, auto ref Sort d1, auto ref Sort range) {
  return range.context().recfun(name, d1, range);
}
FuncDecl recfun()(string name, auto ref Sort d1, auto ref Sort d2, auto ref Sort range) {
  return range.context().recfun(name, d1, d2, range);
}

Expr select()(auto ref Expr a, auto ref Expr i) {
  checkContext(a, i);
  Z3_ast r = Z3_mk_select(a.context(), a.getAST, i.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
Expr select()(auto ref Expr a, int i) {
  return select(a, a.context().numVal(i, a.getSort().arrayDomain().byRef).byRef);
}
Expr select()(auto ref Expr a, auto ref ExprVector i) {
  checkContext(a, i);
  Z3_ast[] idxs = i.toArray!Z3_ast;
  Z3_ast r = Z3_mk_select_n(a.context(), a.getAST,
			    cast(uint) idxs.length, idxs.ptr);
  a.checkError();
  return Expr(a.context(), r);
}

Expr store()(auto ref Expr a, auto ref Expr i, auto ref Expr v) {
  checkContext(a, i); checkContext(a, v);
  Z3_ast r = Z3_mk_store(a.context(), a.getAST, i.getAST, v.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

Expr store()(auto ref Expr a, int i, auto ref Expr v) {
  return store(a, a.context().numVal(i, a.getSort().arrayDomain().byRef).byRef, v);
}
Expr store()(auto ref Expr a, Expr i, int v) {
  return store(a, i, a.context().numVal(v, a.getSort().arrayRange().byRef).byRef);
}
Expr store()(auto ref Expr a, int i, int v) {
  return store(a, a.context().numVal(i, a.getSort().arrayDomain().byRef).byRef,
	       a.context().numVal(v, a.getSort().arrayRange().byRef).byRef);
}
Expr store()(auto ref Expr a, auto ref ExprVector i, auto ref Expr v) {
  checkContext(a, i); checkContext(a, v);
  Z3_ast[] idxs = i.toArray!Z3_ast;
  Z3_ast r = Z3_mk_store_n(a.context(), a.getAST,
			   cast(uint) idxs.length, idxs.ptr, v.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

Expr asArray()(auto ref FuncDecl f) {
  Z3_ast r = Z3_mk_as_array(f.context(), f);
  f.checkError();
  return Expr(f.context(), r);
}

Expr const_array()(auto ref Sort d, auto ref Expr v) {
  // MK_EXPR2(Z3_mk_const_array, d, v);
  checkContext(d, v);
  Z3_ast r = Z3_mk_const_array(d.context(), d, v.getAST);
  d.checkError();
  return Expr(d.context(), r);
}

Expr emptySet()(auto ref Sort s) {
  // MK_EXPR1(Z3_mk_empty_set, s);
  Z3_ast r = Z3_mk_empty_set(s.context(), s);
  s.checkError();
  return Expr(s.context(), r);
}

Expr fullSet()(auto ref Sort s) {
  // MK_EXPR1(Z3_mk_full_set, s);
  Z3_ast r = Z3_mk_full_set(s.context(), s);
  s.checkError();
  return Expr(s.context(), r);
}

Expr setAdd()(auto ref Expr s, auto ref Expr e) {
  // MK_EXPR2(Z3_mk_set_add, s, e);
  checkContext(s, e);
  Z3_ast r = Z3_mk_set_add(s.context(), s.getAST, e.getAST);
  s.checkError();
  return Expr(s.context(), r);
}

Expr setDel()(auto ref Expr s, auto ref Expr e) {
  // MK_EXPR2(Z3_mk_set_del, s, e);
  checkContext(s, e);
  Z3_ast r = Z3_mk_set_del(s.context(), s.getAST, e.getAST);
  s.checkError();
  return Expr(s.context(), r);
}

Expr setUnion()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast[2] es = [a.getAST, b.getAST];
  Z3_ast r = Z3_mk_set_union(a.context(), 2, es.ptr);
  a.checkError();
  return Expr(a.context(), r);
}

Expr setIntersect()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast[2] es = [a.getAST, b.getAST];
  Z3_ast r = Z3_mk_set_intersect(a.context(), 2, es.ptr);
  a.checkError();
  return Expr(a.context(), r);
}

Expr setDifference()(auto ref Expr a, auto ref Expr b) {
  // MK_EXPR2(Z3_mk_set_difference, a, b);
  checkContext(a, b);
  Z3_ast r = Z3_mk_set_difference(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

Expr setComplement()(auto ref Expr a) {
  // MK_EXPR1(Z3_mk_set_complement, a);
  Z3_ast r = Z3_mk_set_complement(a.context(), a.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

Expr setMember()(auto ref Expr s, auto ref Expr e) {
  // MK_EXPR2(Z3_mk_set_member, s, e);
  checkContext(s, e);
  Z3_ast r = Z3_mk_set_member(s.context(), s.getAST, e.getAST);
  s.checkError();
  return Expr(s.context(), r);
}

Expr setSubset()(auto ref Expr a, auto ref Expr b) {
  // MK_EXPR2(Z3_mk_set_subset, a, b);
  checkContext(a, b);
  Z3_ast r = Z3_mk_set_subset(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}

//     // sequence and regular Expression operations.
//     // union is +
//     // concat is overloaded to handle sequences and regular Expressions

Expr empty()(auto ref Sort s) {
  Z3_ast r = Z3_mk_seq_empty(s.context(), s);
  s.checkError();
  return Expr(s.context(), r);
}
Expr suffixof()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_seq_suffix(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
Expr prefixof()(auto ref Expr a, auto ref Expr b) {
  checkContext(a, b);
  Z3_ast r = Z3_mk_seq_prefix(a.context(), a.getAST, b.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
Expr indexof()(auto ref Expr s, auto ref Expr substr, auto ref Expr offset) {
  checkContext(s, substr); checkContext(s, offset);
  Z3_ast r = Z3_mk_seq_index(s.context(), s.getAST, substr.getAST, offset.getAST);
  s.checkError();
  return Expr(s.context(), r);
}
Expr lastIndexof()(auto ref Expr s, auto ref Expr substr) {
  checkContext(s, substr); 
  Z3_ast r = Z3_mk_seq_last_index(s.context(), s.getAST, substr.getAST);
  s.checkError();
  return Expr(s.context(), r);
}


Expr toRe()(auto ref Expr s) {
  // MK_EXPR1(Z3_mk_seq_to_re, s);
  Z3_ast r = Z3_mk_seq_to_re(s.context(), s.getAST);
  s.checkError();
  return Expr(s.context(), r);
}
Expr inRe()(auto ref Expr s, auto ref Expr re) {
  // MK_EXPR2(Z3_mk_seq_in_re, s, re);
  checkContext(s, re);
  Z3_ast r = Z3_mk_seq_in_re(s.context(), s.getAST, re.getAST);
  s.checkError();
  return Expr(s.context(), r);
}
Expr plus()(auto ref Expr re) {
  // MK_EXPR1(Z3_mk_re_plus, re);
  Z3_ast r = Z3_mk_re_plus(re.context(), re.getAST);
  re.checkError();
  return Expr(re.context(), r);
}
Expr option()(auto ref Expr re) {
  // MK_EXPR1(Z3_mk_re_option, re);
  Z3_ast r = Z3_mk_re_option(re.context(), re.getAST);
  re.checkError();
  return Expr(re.context(), r);
}
Expr star()(auto ref Expr re) {
  // MK_EXPR1(Z3_mk_re_star, re);
  Z3_ast r = Z3_mk_re_star(re.context(), re.getAST);
  re.checkError();
  return Expr(re.context(), r);
}
Expr reEmpty()(auto ref Sort s) {
  Z3_ast r = Z3_mk_re_empty(s.context(), s);
  s.checkError();
  return Expr(s.context(), r);
}
Expr reFull()(auto ref Sort s) {
  Z3_ast r = Z3_mk_re_full(s.context(), s);
  s.checkError();
  return Expr(s.context(), r);
}
Expr reIntersect()(auto ref ExprVector args) {
  assert(args.size() > 0);
  Z3_ast[] _args = args.toArray!Z3_ast;
  Z3_ast r = Z3_mk_re_intersect(args.context(), cast(uint) _args.length,
				_args.ptr);
  args.context().checkError();
  return Expr(args.context(), r);
}
Expr reComplement()(auto ref Expr a) {
  // MK_EXPR1(Z3_mk_re_complement, a);
  Z3_ast r = Z3_mk_re_complement(a.context(), a.getAST);
  a.checkError();
  return Expr(a.context(), r);
}
