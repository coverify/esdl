// Written in the D programming language.

// Copyright: Coverify Systems Technology 2012 - 2015
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.rand.meta;

import std.meta: AliasSeq;
import std.traits: isIntegral, isBoolean, isArray, isSomeChar, isPointer,
  PointerTarget, OriginalType, isAssociativeArray, ValueType, KeyType,
  isSomeString;
import esdl.data.bvec: isBitVector, ubvec, bvec;
import esdl.data.queue: isQueue, Queue;
import esdl.data.packed: _esdl__packed, _esdl__packed_info,
  _esdl__packed_type;
import esdl.data.bstr;

import std.exception: enforce;
import std.range: ElementType;

import esdl.rand.misc;
import esdl.rand.expr: CstVarVisitorExpr;
import esdl.rand.base: CstVecPrim, CstVarGlobIntf, CstVarNodeIntf,
  CstObjectIntf, CstObjArrIntf, CstObjStub;
import esdl.rand.pred: CstPredicate, CstVisitorPredicate;
import esdl.rand.vecx: CstVectorIdx, CstVecArrIdx, CstVectorArg,
  CstVecArrArg, CstVectorGlob, CstVecArrGlob, CstVectorGlobEnum,
  CstVecArrGlobEnum;
import esdl.rand.objx: CstObjectIdx, CstObjArrIdx, CstObjectGlob,
  CstObjArrGlob, CstRootProxy, CstRootLambdaProxy, _esdl__ObjStub,
  _esdl__TypedStub;
import esdl.rand.domain: CstVecValue, CstLogicValue;
import esdl.rand.proxy;
import esdl.rand.cstr;
import esdl.rand.func;
import esdl.cover.group: _esdl__BaseCoverGroup;

import esdl.base.rand: _esdl__RandGen, getRandGen;
// import esdl.base.alloc: make;


/// C++ type static_cast for down-casting when you are sure
private import std.traits: BaseClassesTuple; // required for staticIndexOf

// static Mallocator proxyAllocator;
template _esdl__PackedRandProxyType(PCT, int I, RAND, P, int PI)
{
  import std.traits;

  static assert (isRandomizable!PCT);

  alias _esdl__PackedRandProxyType = CstVectorIdx!(PCT, RAND, PCT, I, P, PI);
}

template _esdl__randIgnore(ATTR...)
{
  static if (ATTR.length == 0)
    enum bool _esdl__randIgnore = false;
  else static if (is (ATTR[0] == rand.ignore))
    enum bool _esdl__randIgnore = true;
  else
    enum bool _esdl__randIgnore =
      _esdl__randIgnore!(ATTR[1..$]);
}

template _esdl__RandProxyType(T, int I, P, int PI)
{
  import std.traits;
  alias L = typeof(T.tupleof[I]);
  enum rand RAND = getRandAttr!(T, I);
 // pragma(msg, "Looking at: ", T.tupleof[I].stringof);
  static if (_esdl__randIgnore!(__traits(getAttributes, T.tupleof[I]))
	     || is (L: rand.disable)) {
    alias _esdl__RandProxyType = _esdl__NotMappedForRandomization;
  }

  else static if (is (L: Constraint!(CST, FILE, LINE),
		      string CST, string FILE, size_t LINE)) {
    alias _esdl__RandProxyType = _esdl__NotMappedForRandomization;
  }
  else static if (isRandomizable!L) {
    alias _esdl__RandProxyType = CstVectorIdx!(L, RAND, L, I, P, PI);
  }
  else static if (isPointer!L && isRandomizable!(PointerTarget!L)) {
    alias LT = PointerTarget!L;
    alias _esdl__RandProxyType = CstVectorIdx!(LT, RAND, L, I, P, PI);
  }
  else static if (isRandVectorSet!L) {
    alias _esdl__RandProxyType = CstVecArrIdx!(L, RAND, L, I, P, PI);
  }
  else static if (isPointer!L && isRandVectorSet!(PointerTarget!L)) {
    alias LT = PointerTarget!L;
    alias _esdl__RandProxyType = CstVecArrIdx!(LT, RAND, L, I, P, PI);
  }
  // Exclude class/struct* elements that have not been rand tagged
  // or are excluded  because of rand.disable or rand.barrier
  else static if (isRandObject!L) {
    alias _esdl__RandProxyType = CstObjectIdx!(L, RAND, L, I, P, PI);
    // static if (RAND.isRand()) {
    //   alias _esdl__RandProxyType = CstObjectIdx!(L, RAND, L, I, P, PI);
    // }
    // else {
    //   alias _esdl__RandProxyType = _esdl__NotMappedForRandomization;
    // }
  }
  else static if (isPointer!L && isRandObject!(PointerTarget!L)) {
    alias LT = PointerTarget!L;
    alias _esdl__RandProxyType = CstObjectIdx!(LT, RAND, L, I, P, PI);
  }
  else static if (isRandObjectSet!L) {
    alias _esdl__RandProxyType = CstObjArrIdx!(L, RAND, L, I, P, PI);
    // static if (RAND.isRand()) {
    //   alias _esdl__RandProxyType = CstObjArrIdx!(L, RAND, L, I, P, PI);
    // }
    // else {
    //   alias _esdl__RandProxyType = _esdl__NotMappedForRandomization;
    // }
  }
  else static if (isPointer!L && isRandObjectSet!(PointerTarget!L)) {
    alias LT = PointerTarget!L;
    alias _esdl__RandProxyType = CstObjArrIdx!(LT, RAND, L, I, P, PI);
  }
  else {
    alias _esdl__RandProxyType = _esdl__NotMappedForRandomization;
  }
}

template _esdl__LambdaArgProxyType(T, size_t I)
{
  static if (isRandomizable!T) {
    alias _esdl__LambdaArgProxyType = CstVectorArg!(T, I);
  }
  else static if (isRandVectorSet!T) {
    alias _esdl__LambdaArgProxyType = CstVecArrArg!(T, I);
  }
}

template _esdl__LambdaArgProxyTypes(size_t I, ARGS...)
{
  static if (ARGS.length == 0)
    alias _esdl__LambdaArgProxyTypes = AliasSeq!();
  else
    alias _esdl__LambdaArgProxyTypes =
      AliasSeq!(_esdl__LambdaArgProxyType!(ARGS[0], I), _esdl__LambdaArgProxyTypes!(I+1, ARGS[1..$]));
}

void _esdl__doConstrainElems(P, int I=0)(P p, _esdl__CstProcessor proc) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0]: _esdl__Proxy) &&
	     is (B[0] == class)) {
    static if (! is (B[0] == _esdl__Proxy)) {
      B[0] b = p;			// super object
      _esdl__doConstrainElems(b, proc);
    }
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q: _esdl__ConstraintBase)) {
      static if (p.tupleof[I].stringof != "p._esdl__lambdaCst") {
	if (p.tupleof[I].isEnabled()) {
	  // Update constraint guards if any
	  p.tupleof[I]._esdl__updateCst();
	  foreach (pred; p.tupleof[I].getConstraintGuards()) {
	    // writeln("Adding predicate: ", pred._esdl__getName());
	    proc.addNewPredicate(pred);
	  }
	  foreach (pred; p.tupleof[I].getConstraints()) {
	    // writeln("Adding predicate: ", pred._esdl__getName());
	    proc.addNewPredicate(pred);
	  }
	}
      }
    }
    static if (is (Q: CstObjectIntf)//  ||
	       // is (Q: CstObjArrIntf)  // handled by the visitor on _esdl__unroll
	       ) {
      static if (P.tupleof[I]._esdl__ISRAND) {
	if (p.tupleof[I]._esdl__isRand()) {
	  // import std.stdio;
	  // writeln(p.tupleof[I].stringof, ": ", p.tupleof[I].rand_mode());
	  p.tupleof[I]._esdl__doConstrain(proc, true);
	}
      // else {
      // 	p.tupleof[I]._esdl__doConstrain(proxy);
      // }
      }
    }
    // static if (is (Q: CstObjectStubBase)//  ||
    // 	       // is (Q: CstObjArrIntf)  // handled by the visitor on _esdl__unroll
    // 	       ) {
    //   // static if (P.tupleof[I]._esdl__ISRAND) {
    //   auto q = p.tupleof[I]._esdl__obj();
    //   if (q !is null) {
    // 	q._esdl__doConstrain(proc);
    //   }
    //   // }
    // }
    _esdl__doConstrainElems!(P, I+1)(p, proc);
  }
}

void _esdl__doRandomizeElems(P, int I=0)(P p, _esdl__RandGen randGen) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0]: _esdl__Proxy) &&
	     is (B[0] == class)) {
    static if (! is (B[0] == _esdl__Proxy)) {
      B[0] b = p;			// super object
      _esdl__doRandomizeElems(b, randGen);
    }
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    static if (is (Q: CstVarNodeIntf)) {
      static if (P.tupleof[I]._esdl__ISRAND) {
	if (p.tupleof[I]._esdl__isRand())
	  p.tupleof[I]._esdl__doRandomize(randGen);
      }
    }
    _esdl__doRandomizeElems!(P, I+1)(p, randGen);
  }
}

void _esdl__doInitRandObjectElems(P, int I=0)(P p) {
  // static if (I == 0 &&
  // 	     is (P B == super) &&
  // 	     is (B[0]: _esdl__Proxy) &&
  // 	     is (B[0] == class)) {
  //   B[0] b = p;			// super object
  //   _esdl__doInitRandObjectElems(b);
  // }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    // pragma(msg, "#" ~ Q.stringof);
    static if (is (Q: CstVarNodeIntf)) {
      // static if (Q._esdl__HASPROXY // && Q._esdl__ISRAND // not just @rand
      // 		 ) {
      // pragma(msg, "#" ~ Q.stringof);
      // enum string NAME = __traits(identifier, P.tupleof[I]);
      // static if (is (T == class)) { // class
      // 	enum NAME = __traits(identifier, T.tupleof[Q._esdl__INDEX]);
      // }
      // else { // struct
      // 	alias U = PointerTarget!T;
      // 	enum NAME = __traits(identifier, U.tupleof[Q._esdl__INDEX]);
      // }
      // pragma(msg, p.tupleof[I].stringof);
      p.tupleof[I] = new Q(p);
      // if (t !is null) {
      // 	alias M = typeof(t.tupleof[Q._esdl__INDEX]);
      // 	static if ((is (M == class) && is (M: Object)) ||
      // 		   (is (M == U*, U) && is (U == struct))) { // class or struct*
      // 	  p.tupleof[I] = new Q(p, t.tupleof[Q._esdl__INDEX]);
      // 	}
      // 	else static if (is (M == struct)) {
      // 	  p.tupleof[I] = new Q(p, &(t.tupleof[Q._esdl__INDEX]));
      // 	}
      // 	else static if (isPointer!M) {
      // 	  p.tupleof[I] = new Q(p, t.tupleof[Q._esdl__INDEX]);
      // 	}
      // 	else {
      // 	  p.tupleof[I] = new Q(p, &(t.tupleof[Q._esdl__INDEX]));
      // 	}
      // }
      // else {
      // 	debug (CSTSOLVERTRACE) {
      // 	  import std.stdio;
      // 	  writeln("Outer not set for: ", p._esdl__getFullName(),
      // 		  " of type: ", P.stringof);
      // 	}
      // 	p.tupleof[I] = new Q(p, null);
      // }
      // // }
    }
    _esdl__doInitRandObjectElems!(P, I+1)(p);
  }
}

void _esdl__doInitConstraintElems(P, int I=0)(P p) {
  // Every proxy class will inherit from _esdl__Proxy
  static if (is (P B == super) &&
	     is (B[0]: _esdl__Proxy) &&
	     is (B[0] == class)) {
    B[0] b = p;			// super object
    //   _esdl__doInitConstraintElems(b);
    // }
    alias Q = P._esdl__Type;
    static if (I == P.tupleof.length) {
      return;
    }
    else if (p._esdl__isReal()) {
      alias E = typeof (P.tupleof[I]);
      // pragma(msg, E.stringof);
      static if (is (E: _esdl__ConstraintBase)) {
	enum string EN = p.tupleof[I].stringof[2..$];
	enum bool IS_USER_DEFINED = __traits(hasMember, Q, EN);
	enum bool OVERRIDES = __traits(hasMember, b, EN);
	static if ((IS_USER_DEFINED && OVERRIDES) is true) {
	  static assert (_esdl__ConstraintIsOverride
			 !(__traits(getAttributes, __traits(getMember, Q, EN))),
			 "Constraint " ~ EN ~ " in class '" ~ Q.stringof ~
			 "' overrides a base class constraint; " ~
			 "Add @constraint_override attribute or change its name");
	  __traits(getMember, b, EN).markOverridden();
	}
	auto cst = p.new E(p, EN);
	p.tupleof[I] = cst;
      }
      _esdl__doInitConstraintElems!(P, I+1)(p);
    }
  }
  else {
    static assert (false);
  }
}

template _esdl__ConstraintIsOverride(T...) {
  static if (T.length == 0)
    enum bool _esdl__ConstraintIsOverride = false;
  else {
    static if (is (T[0]: constraint_override))
      enum bool _esdl__ConstraintIsOverride = true;
    else
      enum bool _esdl__ConstraintIsOverride =
	_esdl__ConstraintIsOverride!(T[1..$]);
  }
}

void _esdl__doInitCoverageElems(P, int I=0)(P p) {
  static if (I >= p.tupleof.length) {
    return;
  }
  else {
    alias E = typeof (p.tupleof[I]);
    static if (is (E: _esdl__BaseCoverGroup)) {
      if (p.tupleof[I] is null) {
	p.tupleof[I] = p.new E();
      }
    }
    _esdl__doInitCoverageElems!(P, I+1)(p);
  }
}


void _esdl__doSetDomainContext(_esdl__ConstraintBase cst,
			       _esdl__CstProcessor proc) { cst.doSetDomainContext(proc); }
void _esdl__doProcDomainContext(_esdl__ConstraintBase cst,
				_esdl__CstProcessor proc) { cst.doProcDomainContext(proc); }

void _esdl__doProcPredicateElems(P, int I=0)(P p, _esdl__CstProcessor proc,
					     void function(_esdl__ConstraintBase cst,
							   _esdl__CstProcessor proc) func) {
  // static if (I == 0 &&
  // 	     is (P B == super) &&
  // 	     is (B[0]: _esdl__Proxy) &&
  // 	     is (B[0] == class)) {
  //   B[0] b = p;			// super object
  //   _esdl__doProcPredicateElems(b);
  // }
  static if (I == P.tupleof.length) {
    return;
  }
  else if (p._esdl__isReal()) {
    alias Q = typeof (P.tupleof[I]);
    // pragma(msg, Q.stringof);
    static if (is (Q: _esdl__ConstraintBase)) {
      func(p.tupleof[I], proc);
    }
    _esdl__doProcPredicateElems!(P, I+1)(p, proc, func);
  }
}

void _esdl__doSetStubElems(P, int I=0)(P p) {
  static if (I == 0 &&
	     is (P B == super) &&
	     is (B[0]: _esdl__Proxy) &&
	     is (B[0] == class)) {
    static if (! is (B[0] == _esdl__Proxy)) {
      B[0] b = p;			// super object
      _esdl__doSetStubElems(b);
    }
  }
  static if (I == P.tupleof.length) {
    return;
  }
  else {
    alias Q = typeof (P.tupleof[I]);
    // static if (is (Q == CstVectorIdx!(L, RAND, LL, IDX, P, PIDX),
    // 		   L, rand RAND, LL, int IDX, P, int PIDX)) {
    //   if (p.tupleof[I] !is null) {
    // 	static if (isPointer!LL) {
    // 	  // assert (p._esdl__ref.tupleof[IDX] !is null,
    // 	  // 	  p._esdl__ref.tupleof[IDX].stringof ~ " is null");
    // 	}
    // 	else {
    // 	}
    //   }
    // }
    static if (is (Q == CstObjectIdx!(L, RAND, LL, IDX, P, PIDX),
		   L, rand RAND, LL, int IDX, P, int PIDX)) {
      p.tupleof[I]._esdl__setStub();
    }
    // static if (is (Q == CstVecArrIdx!(L, RAND, LL, IDX, P, PIDX),
    // 		   L, rand RAND, LL, int IDX, P, int PIDX)) {
    //   if (p.tupleof[I] !is null) {
    // 	static if (isPointer!LL) {
    // 	  // assert (p._esdl__ref.tupleof[IDX] !is null,
    // 	  // 	  p._esdl__ref.tupleof[IDX].stringof ~ " is null");
    // 	}
    // 	else {
    // 	}
    //   }
    // }
    static if (is (Q == CstObjArrIdx!(L, RAND, LL, IDX, P, PIDX),
		   L, rand RAND, LL, int IDX, P, int PIDX)) {
      p.tupleof[I]._esdl__setStub();
    }
    _esdl__doSetStubElems!(P, I+1)(p);
  }
}

template _esdl__RandDeclVars(T, int I, PT, int PI)
{
  static if (I == T.tupleof.length) {
    // enum _esdl__RandDeclVars = "";
    enum _esdl__RandDeclVars =
      "enum uint _esdl__RandCount = " ~ PI.stringof ~ ";\n";
  }
  else {
    enum rand RAND = getRandAttr!(T, I);
    static if (// (! RAND.hasProxy()) ||
	       // is (typeof(T.tupleof[I]): rand.disable) ||
	       is (_esdl__RandProxyType!(T, I, PT, PI) ==
		   _esdl__NotMappedForRandomization)) {
      // pragma(msg, "_esdl__NotMappedForRandomization: " ~ T.tupleof[I].stringof);
      enum string _esdl__RandDeclVars = _esdl__RandDeclVars!(T, I+1, PT, PI);
    }
    else {
      // pragma(msg, I);
      // pragma(msg, __traits(identifier, T.tupleof[I]));
      static if (is (T == U*, U) && is (U == struct)) alias TT = U;
      else                                            alias TT = T;

      static if (isPacked!(T, I)) {
	enum string _esdl__RandDeclVars =
	  _esdl__RandDeclPackedVars!(TT, I, PT, PI, __traits(getAttributes,
								 TT.tupleof[I])) ~
	  _esdl__RandDeclVars!(T, I+1, PT, PI+
			       _esdl__RandCountPackedVars!(__traits(getAttributes,
								    TT.tupleof[I])));
      }
      else {
	enum string _esdl__RandDeclVars =
	  "  public _esdl__RandProxyType!(_esdl__T, " ~ I.stringof ~
	  ", _esdl__PROXYT, " ~ PI.stringof ~ ") " ~
	  __traits(identifier, TT.tupleof[I]) ~ ";\n" ~
	  _esdl__RandDeclVars!(T, I+1, PT, PI+1);
      }
    }
  }
}

template _esdl__RandDeclPackedVars(T, int I, PT, int PI, Attribs...)
{
  import esdl.data.packed: _esdl__packed_info, _esdl__packed_type;
  static if (Attribs.length == 0)
    enum string _esdl__RandDeclPackedVars = "";
  else {
    static if (__traits(compiles, typeof(Attribs[0])) &&
	       is (typeof(Attribs[0]) == _esdl__packed_info)) {
      static if (Attribs[0].isRand == true) enum string RANDSTR = "rand(false, false), ";
      else enum RANDSTR = "rand(true, true), ";
      enum string _esdl__RandDeclPackedVars =
	" public CstVectorIdx!(_esdl__packed_type!(" ~
	Attribs[0].type ~ ", " ~ Attribs[0].aggrtype ~ ", " ~
	Attribs[0].offset.stringof ~ "), " ~ RANDSTR ~ Attribs[0].aggrtype ~
	", " ~ I.stringof ~ ", _esdl__PROXYT, " ~
	PI.stringof ~ ") " ~ Attribs[0].name ~ ";\n" ~
	_esdl__RandDeclPackedVars!(T, I, PT, PI+1, Attribs[1..$]);
    }
    else {
      enum string _esdl__RandDeclPackedVars =
	_esdl__RandDeclPackedVars!(T, I, PT, PI, Attribs[1..$]);
    }
  }
}

template _esdl__RandCountPackedVars(Attribs...)
{
  import esdl.data.packed: _esdl__packed_info, _esdl__packed_type;
  static if (Attribs.length == 0)
    enum uint _esdl__RandCountPackedVars = 0;
  else {
    static if (__traits(compiles, typeof(Attribs[0])) &&
	       is (typeof(Attribs[0]) == _esdl__packed_info)) {
      enum uint _esdl__RandCountPackedVars = 1 +
	_esdl__RandCountPackedVars!(Attribs[1..$]);
    }
    else {
      enum uint _esdl__RandCountPackedVars =
	_esdl__RandCountPackedVars!(Attribs[1..$]);
    }
  }
}

template _esdl__ConstraintsDecl(T, int I=0)
{
  static if(I == T.tupleof.length) {
    enum _esdl__ConstraintsDecl = "";
  }
  else {
    alias L = typeof(T.tupleof[I]);
    enum rand RAND = getRandAttr!(T, I);
    static if (is (T == U*, U) && is (U == struct)) {
      enum NAME = __traits(identifier, U.tupleof[I]);
    }
    else {
      enum NAME = __traits(identifier, T.tupleof[I]);
    }
    // skip the constraints and _esdl__ variables
    static if (is (L == Constraint!(C, F, N), string C, string F, size_t N)) {
      enum CONSTRAINT = _esdl__constraintParams!(T, I).CONSTRAINT;
      enum FILE = _esdl__constraintParams!(T, I).FILE;
      enum LINE = _esdl__constraintParams!(T, I).LINE;
      enum _esdl__ConstraintsDecl =
	"  enum string _esdl__CONSTRAINT_" ~ NAME ~
	" = _esdl__constraintParams!(_esdl__T, " ~ I.stringof ~ ").CONSTRAINT;\n" ~
	"  enum string _esdl__FILE_" ~ NAME ~
	" = _esdl__constraintParams!(_esdl__T, " ~ I.stringof ~ ").FILE;\n" ~
	"  enum size_t _esdl__LINE_" ~ NAME ~
	" = _esdl__constraintParams!(_esdl__T, " ~ I.stringof ~ ").LINE;\n" ~
	"  _esdl__ConstraintImpl!(_esdl__CONSTRAINT_" ~ NAME ~
	", _esdl__FILE_" ~ NAME ~ ", _esdl__LINE_" ~ NAME ~ ", " ~ I.stringof ~ ") " ~
	NAME ~ ";\n" ~ _esdl__ConstraintsDecl!(T, I+1);
    }
    else static if (isRandVectorSet!L || isRandObjectSet!L) {
      // else static if (RAND.isRand() && (isRandVectorSet!L || isRandObjectSet!L)) {
      enum _esdl__ConstraintsDecl =
	"  _esdl__VisitorCst!(\"" ~ NAME ~ "\") _esdl__visitorCst_"
	~ NAME ~ ";\n"  ~ _esdl__ConstraintsDecl!(T, I+1);
    }
    else {
      enum _esdl__ConstraintsDecl = _esdl__ConstraintsDecl!(T, I+1);
    }
  }
}

template _esdl__constraintParams(T, int I)
{
  alias L = typeof(T.tupleof[I]);
  static if (is (L == Constraint!(C, F, N), string C, string F, size_t N)) {
    enum string CONSTRAINT = C;
    enum string FILE = F;
    enum size_t LINE = N;
  }
  else {
    static assert(false);
  }
}

template _esdl__ConstraintsDefDecl(T)
{
  enum _esdl__ConstraintsDefDecl =
    "  _esdl__ConstraintImpl!(_esdl__ConstraintDefaults!(_esdl__T, 0), \"#DEFAULT#\", 0, -1) _esdl__defaultConstraint;\n";
}

template _esdl__ConstraintDefaults(T, int I=0)
{
  static if(I == T.tupleof.length) {
    enum _esdl__ConstraintDefaults = "";
  }
  else {
    alias RAND = getRandAttr!(T, I);
    static if (RAND.isRand) {
      static if (is (T == U*, U) && is (U == struct)) alias TT = U;
      else                                            alias TT = T;
      enum string _esdl__ConstraintDefaults =
	_esdl__ConstraintDefaults!(__traits(identifier, TT.tupleof[I]), 0, RAND) ~
	_esdl__ConstraintDefaults!(T, I+1);
    }
    else {
      enum string _esdl__ConstraintDefaults = _esdl__ConstraintDefaults!(T, I+1);
    }
      
  }
}

template _esdl__ConstraintDefaults(string NAME, int I, rand RAND) {
  enum uint LENGTH = RAND[I];
  enum uint NEXTL = RAND[I+1];
  static if (LENGTH == uint.max) {
    enum string _esdl__ConstraintDefaults = "";
  }
  else {
    static if (I == 0) {
      enum string ARR = NAME;
    }
    else {
      enum J = I - 1;
      enum string ARR = "_esdl__elem_" ~ NAME ~ "_" ~ J.stringof;
    }
    enum string ELEM = "_esdl__elem_" ~ NAME ~ "_" ~ I.stringof;
    enum string _esdl__ConstraintDefaultsLength = ARR ~ ".length <= "
      ~ LENGTH.stringof ~ ";\n";
    
    static if (NEXTL == uint.max) {
      enum string _esdl__ConstraintDefaults = _esdl__ConstraintDefaultsLength;
    }
    else {
      enum string _esdl__ConstraintDefaults = _esdl__ConstraintDefaultsLength
	~ "foreach(" ~ ELEM ~ "; " ~ ARR ~ ") {\n" ~
	_esdl__ConstraintDefaults!(NAME, I+1, RAND) ~ "}";
    }
  }
}

void _esdl__preRandomize(T)(T t) {
  static if (__traits(hasMember, t, "preRandomize")) {
    __traits(getMember, t, "preRandomize")();
  }
  else static if (__traits(hasMember, t, "pre_randomize")) {
    __traits(getMember, t, "pre_randomize")();
  }
}

void _esdl__postRandomize(T)(T t) {
  static if (__traits(hasMember, t, "postRandomize")) {
    __traits(getMember, t, "postRandomize")();
  }
  else static if (__traits(hasMember, t, "post_randomize")) {
    __traits(getMember, t, "post_randomize")();
  }
}

void _esdl__randomize(T) (T t) if (is (T == class))
  {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Type of Randomized Object: ", T.stringof);
    }

    alias _esdl__ProxyType = _esdl__ProxyResolve!T;

    CstRootProxy!T _esdl__createProxy() {
      // import std.stdio;
      // writeln("New: ", _esdl__ProxyType.stringof);
      return new CstRootProxy!T(t);
      // _esdl__ProxyType proxy =
      // 	new _esdl__ProxyType(null, null, null);
      // if (proxy is null) {
      // 	assert (false, "Unable to allocate proxy instance");
      // }
      // return proxy;
    }

    CstRootProxy!T proxyRoot = _esdl__ProxyType._esdl__proxyRootInst;

    if (proxyRoot is null) {
      proxyRoot = _esdl__createProxy();
      _esdl__ProxyType._esdl__proxyRootInst = proxyRoot;
    }
    else {
      proxyRoot.updateRandObj(t);
    }

    _esdl__ProxyType proxyInst = _esdl__staticCast!(_esdl__ProxyType)
      (proxyRoot._esdl__getProxy());

    _esdl__CstProcessor proc = proxyInst._esdl__getProc();

    assert(proc !is null);
    proc._esdl__doResetLambdaPreds();

    _esdl__preRandomize(t);

    version (CACHEDPROXIES) { proxyInst._esdl__doSetStub(); }

    proxyInst._esdl__lambdaCst = null;
    proc.reset();
    proxyInst._esdl__doConstrain(proc, false);
    proc.solve();
    proxyInst._esdl__doRandomize(t._esdl__virtualGetRandGen());
    version (CACHEDPROXIES) { proxyInst._esdl__resetCaches(); }
    // _esdl__postRandomize(t);
  }

void _esdl__randomize(T) (ref T t) if (is (T == struct))
  {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Type of Randomized Object: ", T.stringof);
    }

    alias _esdl__ProxyType = _esdl__ProxyResolve!T;

    CstRootProxy!T _esdl__createProxy() {
      // import std.stdio;
      // writeln("New: ", _esdl__ProxyType.stringof);
      return new CstRootProxy!T(&t);
      // _esdl__ProxyType proxy =
      // 	new _esdl__ProxyType(null, null, null);
      // if (proxy is null) {
      // 	assert (false, "Unable to allocate proxy instance");
      // }
      // return proxy;
    }

    CstRootProxy!T proxyRoot = _esdl__ProxyType._esdl__proxyRootInst;

    if (proxyRoot is null) {
      proxyRoot = _esdl__createProxy();
      _esdl__ProxyType._esdl__proxyRootInst = proxyRoot;
    }
    else {
      proxyRoot.updateRandObj(&t);
    }

    _esdl__ProxyType proxyInst = _esdl__staticCast!(_esdl__ProxyType)
      (proxyRoot._esdl__getProxy());

    _esdl__CstProcessor proc = proxyInst._esdl__getProc();

    assert(proc !is null);
    proc._esdl__doResetLambdaPreds();

    _esdl__preRandomize(t);

    version (CACHEDPROXIES) { proxyInst._esdl__doSetStub(); }

    proxyInst._esdl__lambdaCst = null;
    proc.reset();
    proxyInst._esdl__doConstrain(proc, false);
    proc.solve();
    proxyInst._esdl__doRandomize(t._esdl__virtualGetRandGen());
    version (CACHEDPROXIES) { proxyInst._esdl__resetCaches(); }
    // _esdl__postRandomize(t);
  }

_esdl__Proxy _esdl__getLambdaProxyInst(T)(T t, uint cstID) if (is (T == class)) {
  alias _esdl__ProxyType = _esdl__ProxyResolve!T;

  CstRootLambdaProxy!T _esdl__createLambdaProxy(T t) {
    // import std.stdio;
    // writeln("New: ", _esdl__ProxyType.stringof);
    return new CstRootLambdaProxy!T(t);
    // _esdl__ProxyType lambdaProxy =
    //   new _esdl__ProxyType(null, null, null);
    // if (lambdaProxy is null) {
    //   assert (false, "Unable to allocate lambdaProxy instance");
    // }
    // return lambdaProxy;
  }

  CstRootLambdaProxy!T lambdaProxyRoot = _esdl__ProxyType._esdl__lambdaProxyRootInst;

  if (lambdaProxyRoot is null) {
    lambdaProxyRoot = _esdl__createLambdaProxy(t);
    _esdl__ProxyType._esdl__lambdaProxyRootInst = lambdaProxyRoot;
  }
  else {
    lambdaProxyRoot.updateRandObj(t);
  }

  return lambdaProxyRoot._esdl__getLambdaProxy(cstID);
}

_esdl__Proxy _esdl__getLambdaProxyInst(T)(ref T t, uint cstID) if (is (T == struct)) {
  alias _esdl__ProxyType = _esdl__ProxyResolve!T;

  CstRootLambdaProxy!T _esdl__createLambdaProxy(T* t) {
    // import std.stdio;
    // writeln("New: ", _esdl__ProxyType.stringof);
    return new CstRootLambdaProxy!T(t);
    // _esdl__ProxyType lambdaProxy =
    //   new _esdl__ProxyType(null, null, null);
    // if (lambdaProxy is null) {
    //   assert (false, "Unable to allocate lambdaProxy instance");
    // }
    // return lambdaProxy;
  }

  CstRootLambdaProxy!T lambdaProxyRoot = _esdl__ProxyType._esdl__lambdaProxyRootInst;

  if (lambdaProxyRoot is null) {
    lambdaProxyRoot = _esdl__createLambdaProxy(&t);
    _esdl__ProxyType._esdl__lambdaProxyRootInst = lambdaProxyRoot;
  }
  else {
    lambdaProxyRoot.updateRandObj(&t);
  }

  return lambdaProxyRoot._esdl__getLambdaProxy(cstID);
}

void _esdl__randomizeWith(T)(T t, _esdl__Proxy proxy,
			     _esdl__ConstraintBase lambdaCst) if (is (T == class))
  {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Type of Randomized Object: ", T.stringof);
    }

    _esdl__preRandomize(t);

    _esdl__CstProcessor proc = proxy._esdl__getProc();
    assert(proc !is null);
    version (CACHEDPROXIES) { proxy._esdl__doSetStub(); }

    proc.reset();
    proxy._esdl__doConstrain(proc, false);
    foreach (pred; lambdaCst.getConstraintGuards()) {
      proc.addNewPredicate(pred);
    }
    foreach (pred; lambdaCst.getConstraints()) {
      proc.addNewPredicate(pred);
    }
    proc.solve();
    proxy._esdl__doRandomize(t._esdl__virtualGetRandGen());
    version (CACHEDPROXIES) { proxy._esdl__resetCaches(); }
    // _esdl__postRandomize(t);

  }

void _esdl__randomizeWith(T) (ref T t, _esdl__Proxy proxy,
			      _esdl__ConstraintBase lambdaCst) if (is (T == struct))
  {
    debug (CSTSOLVER) {
      import std.stdio;
      writeln("Type of Randomized Object: ", T.stringof);
    }

    _esdl__preRandomize(t);

    _esdl__CstProcessor proc = proxy._esdl__getProc();
    assert(proc !is null);
    version (CACHEDPROXIES) { proxy._esdl__doSetStub(); }
  
    proc.reset();
    proxy._esdl__doConstrain(proc, false);
    foreach (pred; lambdaCst.getConstraintGuards()) {
      proc.addNewPredicate(pred);
    }
    foreach (pred; lambdaCst.getConstraints()) {
      proc.addNewPredicate(pred);
    }
    proc.solve();
    proxy._esdl__doRandomize(t._esdl__virtualGetRandGen());
    version (CACHEDPROXIES) { proxy._esdl__resetCaches(); }
    // _esdl__postRandomize(t);

  }

class Randomizable {
  mixin Randomization;
}

alias randomization = Randomization;

mixin template Randomization()
{
  import esdl.base.rand: _esdl__RandGen, getRandGen;
  enum bool _esdl__HasRandomizationMixin = true;
  // While making _esdl__ProxyRand class non-static nested class
  // also works as far as dlang compilers are concerned, do not do
  // that since in that case _esdl__ref object would have an
  // implicit pointer to the outer object which can not be changed

  // Need this function for evaluatig constraint guards within the
  // ambit of user code
  auto _esdl__guardEval(string str)() {
    return mixin(str);
  }
  
  static if (is (typeof(this) == class)) {
    import esdl.cover.group: _esdl__BaseCoverGroup, _esdl__parseCoverGroupString;
    import esdl.cover;
    class covergroup(string CoverSpec): _esdl__BaseCoverGroup {
      // alias _esdl__CG_OUTER = typeof(this.outer);
      debug(CVRPARSER) {
	pragma (msg, _esdl__parseCoverGroupString(CoverSpec));
      }
      void start() {
	foreach (ref elem; this.tupleof) {
	  static if (is (typeof(elem): _esdl__BaseCoverPoint))
	    elem.start();
	}
      }
      void stop() {
	foreach (ref elem; this.tupleof) {
	  static if (is (typeof(elem): _esdl__BaseCoverPoint))
	    elem.stop();
	}
      }
      mixin(_esdl__parseCoverGroupString(CoverSpec));
    }

    static if (__traits(hasMember, typeof(this), "_esdl__covergroups_initialized")) {
      override void init_coverage() {
	if (_esdl__covergroups_initialized is false) {
	  super.init_coverage();
	  _esdl__covergroups_initialized = true;
	  _esdl__doInitCoverageElems(this);
	}
      }
    }
    else {
      bool _esdl__covergroups_initialized = false;
      void init_coverage() {
	if (_esdl__covergroups_initialized is false) {
	  _esdl__covergroups_initialized = true;
	  _esdl__doInitCoverageElems(this);
	}
      }
    }
    
    static class _esdl__ProxyRand(_esdl__T): _esdl__ProxyBase!_esdl__T
    {
      mixin _esdl__ProxyMixin!_esdl__T;

      _esdl__T _esdl__ref()() {
	return cast(_esdl__T) _esdl__stub._esdl__refPtr();
      }

      enum bool _esdl__HAS_RAND_INFO = true;
      // override _esdl__Proxy _esdl__createProxyInst(CstObjStub obj, Object outer) {
      // 	_esdl__T outer_ = _esdl__staticCast!_esdl__T(outer);
      // 	return new _esdl__ProxyRand!(_esdl__T)(obj, outer_);
      // }
  
      this(CstObjStub obj) {
	super(obj);
	_esdl__doInitRandObjectElems(this);
	_esdl__doInitConstraintElems(this);
	_esdl__doProcPredicateElems(this, this._esdl__getProc(),
				    &_esdl__doSetDomainContext);
	_esdl__doProcPredicateElems(this, this._esdl__getProc(),
				    &_esdl__doProcDomainContext);
	_esdl__setContextGlobalVisitors(this._esdl__getProc());
      }
    }
  }
  else static if (is (typeof(this) == struct)) {

    static class _esdl__ProxyRand(_esdl__T): _esdl__ProxyBase!_esdl__T
    {
      mixin _esdl__ProxyMixin!_esdl__T;

      _esdl__T* _esdl__ref()() {
	return cast(_esdl__T*) _esdl__stub._esdl__refPtr();
      }

      enum bool _esdl__HAS_RAND_INFO = true;
      // override _esdl__Proxy _esdl__createProxyInst(CstObjStub obj, void* outer) {
      // 	_esdl__T* outer_ = cast(_esdl__T*)(outer);
      // 	return new _esdl__ProxyRand!(_esdl__T)(obj, outer_);
      // }
      this(CstObjStub obj) {
	super(obj);
	_esdl__doInitRandObjectElems(this);
	_esdl__doInitConstraintElems(this);
	_esdl__doProcPredicateElems(this, this._esdl__getProc(),
				    &_esdl__doSetDomainContext);
	_esdl__doProcPredicateElems(this, this._esdl__getProc(),
				    &_esdl__doProcDomainContext);
	_esdl__setContextGlobalVisitors(this._esdl__getProc());
      }
    }
  }
  else {
    static assert (false, "mixin Randomization is allowed only inside a class or a struct; not " ~
		   typeof(this).stringof);
  }

  alias _esdl__ProxyType = _esdl__ProxyResolve!(typeof(this));

  // final auto _esdl__randEval(string NAME)() {
  //   return mixin(NAME);
  // }

  alias rand_mode = randMode;
  
  bool randMode(int PINDX)() {
    return _esdl__RandInfoInst.randMode!(PINDX,
					 _esdl__ProxyType._esdl__RandCount)();
    // if (_esdl__RandInfoInst._randModes.length <= PINDX) return true;
    // else return _esdl__RandInfoInst._randModes[PINDX];
  }

  bool randMode(string rnd)() {
    static assert (__traits(hasMember, _esdl__ProxyType, rnd));

    alias RND = typeof(__traits(getMember, _esdl__ProxyType, rnd));
    enum int PINDX = RND._esdl__PROXYINDEX;

    alias TYPE = RND._esdl__PROXYT._esdl__Type;

    TYPE obj = this;
    return obj.randMode!PINDX();
  }

  void randMode(int PINDX)(bool mode) {
    _esdl__RandInfoInst.randMode!(PINDX,
				  _esdl__ProxyType._esdl__RandCount)(mode);
    // size_t currlen = _esdl__RandInfoInst._randModes.length;

    // if (currlen <= PINDX) {
    //   _esdl__RandInfoInst._randModes.length = PINDX + 1;
    //   for (size_t i=currlen; i!=PINDX; ++i) {
    // 	_esdl__RandInfoInst._randModes[i] = true;
    //   }
    // }
    
    // _esdl__RandInfoInst._randModes[PINDX] = mode;
  }

  void randMode(string rnd)(bool mode) {
    static assert (__traits(hasMember, _esdl__ProxyType, rnd));

    alias RND = typeof(__traits(getMember, _esdl__ProxyType, rnd));
    enum int PINDX = RND._esdl__PROXYINDEX;

    alias TYPE = RND._esdl__PROXYT._esdl__Type;

    TYPE obj = this;

    obj.randMode!PINDX(mode);
  }

  bool constraint_mode(string cst)() {
    return mixin(cst).constraint_mode();
  }

  void constraint_mode(string cst)(bool mode) {
    return mixin(cst).constraint_mode(mode);
  }

  void _esdl__seedRandom()(int seed) {
    if (_esdl__RandInfoInst._randGen is null) _esdl__RandInfoInst._randGen = new _esdl__RandGen(seed);
    _esdl__RandInfoInst._randGen.seed(seed);
  }

  @(rand.ignore) _esdl__RandInfo _esdl__RandInfoInst;

  _esdl__RandGen _esdl__getRandGen()() {
    return _esdl__RandInfoInst._randGen;
  }

  static if(// is(_esdl__T: Randomizable) ||
	    __traits(compiles, _esdl__isBaseRand)) { // this is a derived class
    static assert (is (typeof(this) == class),
		   typeof(this).stringof ~ " is not a class"); // only classes can have a base class
    // enum bool _esdl__isBaseRand = false;
    override void _esdl__virtualRandomize() {
      _esdl__randomize(this);
    }
    override _esdl__Proxy _esdl__virtualGetLambdaProxyInst(uint cstID) {
      return _esdl__getLambdaProxyInst(this, cstID);
    }
    override void _esdl__virtualRandomizeWith(_esdl__Proxy proxy,
					      _esdl__ConstraintBase lambdaCst) {
      _esdl__randomizeWith(this, proxy, lambdaCst);
    }
    alias srandom = seedRandom;
    override void seedRandom(int seed) {
      _esdl__seedRandom(seed);
    }
    override _esdl__RandGen _esdl__virtualGetRandGen() {
      _esdl__RandGen randgen = _esdl__getRandGen();
      if (randgen !is null) return randgen;
      else return getRandGen();
    }
  }
  else {
    enum bool _esdl__isBaseRand = true;
    void _esdl__virtualRandomize() {
      _esdl__randomize(this);
    }
    _esdl__Proxy _esdl__virtualGetLambdaProxyInst(uint cstID) {
      return _esdl__getLambdaProxyInst(this, cstID);
    }
    void _esdl__virtualRandomizeWith(_esdl__Proxy proxy,
				     _esdl__ConstraintBase lambdaCst) {
      _esdl__randomizeWith(this, proxy, lambdaCst);
    }
    alias srandom = seedRandom;
    void seedRandom(int seed) {
      _esdl__seedRandom(seed);
    }
    _esdl__RandGen _esdl__virtualGetRandGen() {
      _esdl__RandGen randgen = _esdl__getRandGen();
      if (randgen !is null) return randgen;
      else return getRandGen();
    }
  }
}

class _esdl__ProxyNoRand(_esdl__T)
   if ((is (_esdl__T == class) && is (_esdl__T: Object)) ||
       (is (_esdl__T == U*, U) && is (U == struct))):
    _esdl__ProxyBase!_esdl__T
      {
	mixin _esdl__ProxyMixin!_esdl__T;

	_esdl__T _esdl__ref()() {
	  return cast(_esdl__T) _esdl__stub._esdl__refPtr();
	}

	enum bool _esdl__HAS_RAND_INFO = false;
	// static if (is (_esdl__T == class)) {
	//   override _esdl__Proxy _esdl__createProxyInst(CstObjStub obj, Object outer) {
	//     _esdl__T outer_ = _esdl__staticCast!_esdl__T(outer);
	//     return new _esdl__ProxyNoRand!(_esdl__T)(obj, outer_);
	//   }
	// }
	// else {
	//   override _esdl__Proxy _esdl__createProxyInst(CstObjStub obj, void* outer) {
	//     _esdl__T outer_ = cast(_esdl__T)(outer);
	//     return new _esdl__ProxyNoRand!(_esdl__T)(obj, outer_);
	//   }
	// }
	this(CstObjStub obj) {
	  super(obj);
	  _esdl__doInitRandObjectElems(this);
	  _esdl__doInitConstraintElems(this);
	  _esdl__doProcPredicateElems(this, this._esdl__getProc(),
				      &_esdl__doSetDomainContext);
	  _esdl__doProcPredicateElems(this, this._esdl__getProc(),
				      &_esdl__doProcDomainContext);
	  _esdl__setContextGlobalVisitors(this._esdl__getProc());
	}

      }

class _esdl__ProxyNoRand(_esdl__T)
  if (is (_esdl__T == struct)):
    _esdl__ProxyBase!_esdl__T
      {
	mixin _esdl__ProxyMixin!_esdl__T;

	_esdl__T* _esdl__ref()() {
	  return cast(_esdl__T*) _esdl__stub._esdl__refPtr();
	}

	enum bool _esdl__HAS_RAND_INFO = false;
	// override _esdl__Proxy _esdl__createProxyInst(CstObjStub obj, void* outer) {
	//   _esdl__T* outer_ = cast(_esdl__T*)(outer);
	//   return new _esdl__ProxyNoRand!(_esdl__T)(obj, outer_);
	// }
	this(CstObjStub obj) {
	  super(obj);
	  _esdl__doInitRandObjectElems(this);
	  _esdl__doInitConstraintElems(this);
	  _esdl__doProcPredicateElems(this, this._esdl__getProc(),
				      &_esdl__doSetDomainContext);
	  _esdl__doProcPredicateElems(this, this._esdl__getProc(),
				      &_esdl__doProcDomainContext);
	  _esdl__setContextGlobalVisitors(this._esdl__getProc());
	}
      }

mixin template _esdl__ProxyMixin(_esdl__T)
{
  import esdl.base.rand: _esdl__RandGen, getRandGen;
  version (CACHEDPROXIES) {
    import esdl.data.vector: Vector;
  }
  
  alias _esdl__PROXYT = typeof(this);
  alias _esdl__Type = _esdl__T;

  static CstRootProxy!_esdl__T _esdl__proxyRootInst;
  static CstRootLambdaProxy!_esdl__T _esdl__lambdaProxyRootInst;

  // static ~this() {
  //   if (_esdl__proxyRootInst !is null) proxyAllocator.dispose(_esdl__proxyRootInst);
  // }

  debug(CSTPARSER) {
    import std.traits: BaseClassesTuple;
    pragma(msg, "// Proxy Declarations START: ", _esdl__PROXYT);
    pragma(msg, "// Base Classes: ", BaseClassesTuple!_esdl__PROXYT);
    pragma(msg, "// For Class: ", _esdl__T);
    static if (is (_esdl__T == class)) {
      pragma(msg, "// Base Classes: ", BaseClassesTuple!_esdl__T);
    }
    else {
      pragma(msg, "// For Struct: ", _esdl__T);
    }
    pragma(msg, _esdl__RandDeclVars!(_esdl__T, 0, _esdl__PROXYT, 0));
    pragma(msg, _esdl__ConstraintsDefDecl!_esdl__T);
    pragma(msg, _esdl__ConstraintsDecl!_esdl__T);
    pragma(msg, "// Proxy Declarations END: ", _esdl__PROXYT);
  }

  mixin (_esdl__RandDeclVars!(_esdl__T, 0, _esdl__PROXYT, 0));
  mixin (_esdl__ConstraintsDefDecl!_esdl__T);
  mixin (_esdl__ConstraintsDecl!_esdl__T);

  bool rand_mode(string rnd)() {
    return mixin(rnd).rand_mode();
  }

  void constraint_mode(string cst)(bool mode) {
    mixin(cst).constraint_mode(mode);
  }

  void rand_mode(string rnd)(bool mode) {
    return mixin(rnd).rand_mode(mode);
  }

  void constraint_mode(string cst)(bool mode) {
    mixin(cst).constraint_mode(mode);
  }

  class _esdl__VisitorCst(string OBJ): _esdl__ConstraintBase, _esdl__VisitorCstIntf
  {
    this(_esdl__Proxy eng, string name) {
      super(eng, name, OBJ);
      this.makeConstraints();
    }

    CstPredicate _pred;
    CstPredicate[1] _preds;
    protected bool _initialized;

    final override bool isLambdaConstraint() { return false; }
    final override bool isVisitorConstraint() { return true; }

    override void makeConstraints() {
      auto obj = mixin(OBJ);
      alias TOBJ = typeof(obj);
      _pred =
	new CstVisitorPredicate(this, null, false, 0, this.outer, 0,
				 new CstVarVisitorExpr(obj), false);
      _preds[0] = _pred;
      _initialized = true;
    }

    final override CstPredicate[] getConstraintGuards() {
      return null;
    }

    final override CstPredicate[] getConstraints() {
      assert (_initialized);
      return _preds[];
    }

    final override void doSetDomainContext(_esdl__CstProcessor proc) {
      _pred.doSetDomainContext(_pred, proc);
    }

    final override void doProcDomainContext(_esdl__CstProcessor proc) {
      _pred.doProcDomainContext(proc);
    }

    override string getCode() {return "";}
  }

  class _esdl__ConstraintImpl(string _esdl__CstString, string FILE, size_t LINE, int INDX):
    _esdl__Constraint!(_esdl__CstString, FILE, LINE)
  {
    this(_esdl__Proxy eng, string name) {
      super(eng, name);
      this._esdl__initCst();
      makeConstraints();
    }

    final override bool isLambdaConstraint() { return false; }
    final override bool isVisitorConstraint() { return false; }
    
    mixin (CST_PARSE_DATA.cstDecls);
    mixin (CST_PARSE_DATA.cstDefines);
    mixin (CST_PARSE_DATA.guardDecls);
    mixin (CST_PARSE_DATA.guardInits);
    // pragma (msg, CST_PARSE_DATA.guardDecls);
    // pragma (msg, CST_PARSE_DATA.guardInits);
    mixin (CST_PARSE_DATA.guardUpdts);
  
    static if (INDX >= 0) {	// only for user defined constraints
      final override void constraintMode(bool mode) {
	this.outer._esdl__ref().tupleof[INDX].constraintMode(mode);
      }

      final override bool constraintMode() {
	return this.outer._esdl__ref().tupleof[INDX].constraintMode();
      }
    }

  }

  class _esdl__ConstraintLambdaImpl(string _esdl__CstString, string FILE, size_t LINE, ARGS...): // size_t N):
    _esdl__ConstraintLambda!(_esdl__CstString, FILE, LINE)
  {
    import std.typecons;

    Tuple!(ARGS) _lambdaArgs;

    Tuple!(_esdl__LambdaArgProxyTypes!(0, ARGS)) _proxyLambdaArgs;

    void lambdaArgs(ARGS...)(ARGS values) // if(allIntengral!ARGS)
    {
      // static assert(ARGS.length == N);
      foreach (i, /*ref*/ v; values) {
	_lambdaArgs[i] = v;
      }
    }

    final override bool isLambdaConstraint() { return true; }
    final override bool isVisitorConstraint() { return false; }

    this(ARGS...)(_esdl__Proxy eng, string name, ARGS args) {
      super(eng, name);
      // writeln("pointer: ", &(args[0]));
      foreach (i, arg; args) {
	_lambdaArgs[i] = arg;
      }
      this._esdl__initCst();
      makeConstraints();
    }

    ref auto _esdl__arg(size_t VAR)() {
      static assert(VAR < _lambdaArgs.length, "Can not map specified constraint with argument: @" ~
      		    VAR.stringof);
      return _lambdaArgs[VAR];
    }

    mixin (CST_PARSE_DATA.cstDecls);
    mixin (CST_PARSE_DATA.cstDefines);
    mixin (CST_PARSE_DATA.guardDecls);
    mixin (CST_PARSE_DATA.guardInits);
    mixin (CST_PARSE_DATA.guardUpdts);

  }

  void _esdl__with(string _esdl__CstString, string FILE, size_t LINE, ARGS...)(ARGS values) {
    _esdl__CstProcessor proc = this._esdl__getProc();
    assert(proc !is null);
    proc._esdl__doResetLambdaPreds();
    auto cstLambda =
      new _esdl__ConstraintLambdaImpl!(_esdl__CstString,
				       FILE, LINE, ARGS)(this, "lambdaConstraint", values);
    cstLambda.doSetDomainContext(proc);
    cstLambda.doProcDomainContext(proc);
    _esdl__lambdaCst = cstLambda;
    proc._esdl__setContextArgVisitors(proc);
  }


  override void _esdl__doConstrain(_esdl__CstProcessor proc, bool callPreRandomize) {
    assert (this._esdl__ref() !is null);
    if (callPreRandomize) _esdl__preRandomize(this._esdl__ref());
    _esdl__doConstrainElems(this, proc);
    foreach (visitor; _esdl__getGlobalVisitors()) {
      foreach (pred; visitor.getConstraints()) proc.addNewPredicate(pred);
    }
    foreach (visitor; proc._esdl__getArgVisitors()) {
      foreach (pred; visitor.getConstraints()) proc.addNewPredicate(pred);
    }
  }

  override void _esdl__doRandomize(_esdl__RandGen randGen) {
    _esdl__doRandomizeElems(this, randGen);
    assert (this._esdl__ref() !is null);
    _esdl__postRandomize(this._esdl__ref());
  }

  void _esdl__doSetStub()() {
    _esdl__doSetStubElems(this);
  }

  debug (CSTSOLVER) {
    enum bool _esdl__DEBUGSOVER = true;
  }
  else {
    enum bool _esdl__DEBUGSOVER = false;
  }

  override bool _esdl__debugSolver() {
    return _esdl__DEBUGSOVER;
  }

  debug (CSTPARSER) {
    import std.traits: FieldNameTuple;
    pragma(msg, __traits(allMembers, typeof(this)));
    pragma(msg, FieldNameTuple!(typeof(this)));
    void _esdl__debugPrintElems() {
      _esdl__debugPrintElems!(typeof(this))();
    }

    void _esdl__debugPrintElems(T)() {
      static if (is (T B == super)) {
	static if (B.length > 0) {
	  pragma(msg, FieldNameTuple!T);
	  _esdl__debugPrintElems!(B[0])();
	}
      }
    }
  }

  version (CACHEDPROXIES) {

    static Vector!(_esdl__PROXYT, "proxyInsts") _esdl__proxyInsts;
    static size_t _esdl__proxyIdx;

    override void _esdl__resetCache() {
      super._esdl__resetCache();
      _esdl__proxyIdx = 0;
    }

    static _esdl__PROXYT _esdl__make(CstObjStub stub) {
      _esdl__PROXYT proxy;
      _esdl__Proxy parent = stub._esdl__parent;
      if (parent !is null && parent._esdl__isRoot()) {
	// import std.stdio;
	// writeln ("Using cache for: ", _esdl__PROXYT.stringof);
	if (_esdl__proxyInsts.length > _esdl__proxyIdx) {
	  proxy = _esdl__proxyInsts[_esdl__proxyIdx];
	}
	else {
	  proxy = new _esdl__PROXYT(stub);
	  _esdl__proxyInsts ~= proxy;
	}
	if (_esdl__proxyIdx == 0) {
	  parent._esdl__addCachedProxy(proxy);
	}
	_esdl__proxyIdx += 1;
      }
      else {
	proxy = new _esdl__PROXYT(stub);
      }
      return proxy;
    }
  }
}

// Just so identify visitor constraints
interface _esdl__VisitorCstIntf { }


// Visitor Constraint for Global Variables
class _esdl__VisitorCst(TOBJ): _esdl__ConstraintBase, _esdl__VisitorCstIntf
{
  this(_esdl__Proxy eng, string name, TOBJ obj) {
    assert(obj !is null);
    _obj = obj;
    super(eng, name, "VISITOR CONSTRAINT");
    this.makeConstraints();
  }

  CstPredicate _pred;
  CstPredicate[1] _preds;
  protected bool _initialized;

  TOBJ _obj;

  final override bool isLambdaConstraint() { return false; }
  final override bool isVisitorConstraint() { return true; }
  
  override void makeConstraints() {
    _pred =
      new CstVisitorPredicate(this, null, false, 0, _proxy, 0,
			       new CstVarVisitorExpr(_obj), false);
    _preds[0] = _pred;
    _initialized = true;
  }

  final override CstPredicate[] getConstraintGuards() {
    return null;
  }

  final override CstPredicate[] getConstraints() {
    assert (_initialized);
    return _preds[];
  }

  final override void doSetDomainContext(_esdl__CstProcessor proc) {
    _pred.doSetDomainContext(_pred, proc);
  }

  final override void doProcDomainContext(_esdl__CstProcessor proc) {
    _pred.doProcDomainContext(proc);
  }

  override string getCode() {return "";}

}

auto _esdl__sym(L)(L l, string name,
		   _esdl__Proxy parent) if (isRandomizable!L) {
  static if (is (L: bool)) {
    return new CstLogicValue(l);
  }
  else {
    return new CstVecValue!L(l); // CstVecValue!L.allocate(l);
  }
 }

struct _esdl__rand_type_proxy(T, P)
{
  string _name;
  P _parent;

  string _esdl__name() {
    return _name;
  }

  this(string name, P parent) {
    _name = name;
    _parent = parent;
  }

  auto opDispatch(string S)() {
    return _esdl__sym(__traits(getMember, T, S), S, _parent);
  }
  // auto _esdl__dot(string S)() {
  //   return _esdl__sym(__traits(getMember, T, S), S, _parent);
  // }
}

// V is a type
auto _esdl__sym(V, S)(string name, S parent) {
  debug (CSTSOLVERTRACE) {
    import std.stdio;
    writeln("_esdl__sym: ", name, " parent type: ", S.stringof);
  }
  return _esdl__rand_type_proxy!(V, S)(name, parent);
}

// or else
auto _esdl__sym(alias V, S)(string name, S parent) {
  debug (CSTSOLVERTRACE) {
    import std.stdio;
    writeln("_esdl__sym: ", name, " parent type: ", S.stringof);
  }
  alias L = typeof(V);
  import std.traits: isArray, isAssociativeArray;
  import esdl.data.queue: Queue, isQueue;
  static if (is (L: CstVarNodeIntf)) {
    if (V is null) {
      V = new L(parent);
      // L._esdl__PROXYT p = parent;
      // if (p is null) {
      // 	V = new L(parent, null);
      // }
      // else {
      // 	alias M = typeof(p._esdl__ref().tupleof[L._esdl__INDEX]);
      // 	static if ((is (M == class) && is (M: Object)) ||
      // 		   (is (M == U*, U) && is (U == struct))) {
      // 	  V = new L(parent, p._esdl__ref().tupleof[L._esdl__INDEX]);
      // 	}
      // 	else static if (isPointer!M) {
      // 	  V = new L(parent, p._esdl__ref().tupleof[L._esdl__INDEX]);
      // 	}
      // 	else {
      // 	  V = new L(parent, &(p._esdl__ref().tupleof[L._esdl__INDEX]));
      // 	}
      // }
    }
    return V;
  }
  else static if (isRandomizable!L) {
    static if (isLvalue!V) {
      alias CstVecType = CstVectorGlob!(L, rand(true, true), V);
      CstVarGlobIntf global = parent._esdl__getGlobalLookup(V.stringof);
      if (global !is null) {
	return cast(CstVecType) global;
      }
      else {
	CstVecType obj = new CstVecType(parent);
	parent._esdl__addGlobalLookup(obj, V.stringof);
	return obj;
      }
    }
    else {
      static if (is (L: bool)) {
	return new CstLogicValue(V);
      }
      else {
	return new CstVecValue!L(V);
      }
    }
  }
  else static if ((is (L == class) && is (L: Object)) || (is (L == struct) && !isQueue!L) ||
		  (is (L == U*, U) && is (U == struct))) {
    // pragma(msg, "inside: ", NAME);
    static if (is (L == class) || is (L == struct)) {
      alias CstObjType = CstObjectGlob!(L, rand(true, true), V);
    }
    else {
      alias CstObjType = CstObjectGlob!(U, rand(true, true), V);
    }
    CstVarGlobIntf global = parent._esdl__getGlobalLookup(V.stringof);
    if (global !is null) {
      return cast(CstObjType) global;
    }
    else {
      // pragma(msg, CstObjType.stringof);
      CstObjType obj = new CstObjType(parent);
      // static if (is (L == struct) && !isQueue!L) {
      // 	CstObjType obj = new CstObjType(parent, &V);
      // }
      // else {
      // 	CstObjType obj = new CstObjType(parent, V);
      // }
      parent._esdl__addGlobalLookup(obj, V.stringof);
      return obj;
    }
  }
  else static if (isRandVectorSet!L) {
    // import std.stdio;
    // writeln("Creating VarVecArr, ", name);
    static if (isLvalue!V) {
      alias CstVecArrType = CstVecArrGlob!(L, rand(true, true), V);
      CstVarGlobIntf global = parent._esdl__getGlobalLookup(V.stringof);
      if (global !is null) {
	return cast(CstVecArrType) global;
      }
      else {
	CstVecArrType obj = new CstVecArrType(parent);
	parent._esdl__addGlobalLookup(obj, V.stringof);
	auto visitor =
	  new _esdl__VisitorCst!CstVecArrType(parent, name, obj);
	parent._esdl__addGlobalVisitor(visitor);
	return obj;
      }
    }
    else {
      alias CstVecArrType = CstVecArrGlobEnum!(L, rand(true, true));
      CstVarGlobIntf global = parent._esdl__getGlobalLookup(V.stringof);
      if (global !is null) {
	return cast(CstVecArrType) global;
      }
      else {
	CstVecArrType obj = new CstVecArrType(parent, V);
	parent._esdl__addGlobalLookup(obj, V.stringof);
	auto visitor =
	  new _esdl__VisitorCst!CstVecArrType(parent, name, obj);
	parent._esdl__addGlobalVisitor(visitor);
	return obj;
      }
    }
  }
  else static if (isRandObjectSet!L) {
    // import std.stdio;
    // writeln("Creating VarVecArr, ", name);
    alias CstObjArrType = CstObjArrGlob!(L, rand(true, true), 0, V);
    CstVarGlobIntf global = parent._esdl__getGlobalLookup(V.stringof);
    if (global !is null) {
      return cast(CstObjArrType) global;
    }
    else {
      CstObjArrType obj = new CstObjArrType(parent);
      parent._esdl__addGlobalLookup(obj, V.stringof);
      auto visitor =
	new _esdl__VisitorCst!CstObjArrType(parent, name, obj);
      parent._esdl__addGlobalVisitor(visitor);
      return obj;
    }
  }
  else {
    static assert (false, "Unhandled Global Lookup -- Please report to the EUVM Developer: " ~ L.stringof);
    // import std.stdio;
    // assert (parent !is null);
    // writeln(V.stringof);
    // writeln(VS);
    // writeln(__traits(getMember, parent, VS).stringof);
    // if (__traits(getMember, parent, VS) is null) {
    //   __traits(getMember, parent, VS) = new L(parent, parent._esdl__ref.tupleof[L._esdl__INDEX]);
    // }
    // return __traits(getMember, parent, VS);
  }
}

// auto _esdl__dot(string S, RV)(RV rv)
// {
//   // pragma(msg, RV.stringof);
//   // pragma(msg, S);
//   // static assert(false);
//   return __traits(getMember, rv, S);
// }


auto _esdl__arg_proxy(size_t IDX, L, X, P)(string name, ref L arg, X proxy, P parent) {
  static if (isRandomizable!L) {
    // import std.stdio;
    // writeln("Creating VarVec, ", name);
    alias CstVectorType = CstVectorArg!(L, IDX);
    CstVarNodeIntf var = proxy._proxyLambdaArgs[IDX];
    if (var is null) {
      CstVectorType vvar = new CstVectorType(parent, &arg);
      proxy._proxyLambdaArgs[IDX] = vvar;
      return vvar;
    }
    else {
      CstVectorType vvar = cast (CstVectorType) var;
      assert (vvar !is null);
      return vvar;
    }
  }
  else static if (isRandVectorSet!L) {
    alias CstVecArrType = CstVecArrArg!(L, IDX);
    CstVarNodeIntf var = proxy._proxyLambdaArgs[IDX];
    if (var is null) {
      CstVecArrType vvar = new CstVecArrType(parent, &arg);
      auto visitor =
	new _esdl__VisitorCst!CstVecArrType(parent, name, vvar);
      parent._esdl__getProc()._esdl__addArgVisitor(visitor);
      proxy._proxyLambdaArgs[IDX] = vvar;
      return vvar;
    }
    else {
      CstVecArrType vvar = cast (CstVecArrType) var;
      assert (vvar !is null);
      return vvar;
    }
  }
  else {
    static assert(false);
  }
}

template _esdl__ProxyResolve(T) {
  // pragma(msg, "_esdl__ProxyResolve called for: " ~ T.stringof);
  // static if(__traits(compiles, T._esdl__hasRandomization)) {
  static if (is (T == class) || is (T == struct)) {
    // pragma(msg, T.stringof);
    static if (__traits(compiles, T._esdl__HasRandomizationMixin)) {
      // pragma(msg, "ProxyRand: ", T.stringof);
      alias _esdl__ProxyResolve = T._esdl__ProxyRand!T;
    }
    else {
      // pragma(msg, "ProxyNoRand: ", T.stringof);
      alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
    }
  }
  // else static if (is (T == struct)) {
  //   alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
  // }
  else static if (is (T == U*, U) && is (U == struct)) {
    alias _esdl__ProxyResolve = _esdl__ProxyNoRand!T;
  }
  else {
    static assert(false, "Unable to resolve proxy for type: " ~ T.stringof);
  }
}

// For a given class, this template returns the Proxy for first
// class in the ancestory that has Randomization mixin -- if there is
// none, returns _esdl__Proxy
template _esdl__ProxyBase(T) {
  static if (is (T == class) &&
	     is (T B == super) &&
	     is (B[0] == class) &&
	     // (! _esdl__TypeHasNorandAttr!(B[0])) &&
	     (! _esdl__TypeHasRandBarrier!(B[0])) &&
	     (! is (B[0] == Object))) {
    alias U = B[0];
    alias _esdl__ProxyBase = _esdl__ProxyResolve!U;
  }
  else {
    alias _esdl__ProxyBase = _esdl__Proxy;
  }
}

alias randomize_with = randomizeWith;

void randomize(T, string FILE=__FILE__, size_t LINE=__LINE__)(T t)
     if (is (T == class) || is (T == struct))
{
  // FIXME
  // first check if the there are @rand or Constraint definitions but
  // missing mixin Randomization for some of the hierarchies
  debug (CSTSOLVER) {
    import std.stdio;
    writeln("randomize() called from ", FILE, ":", LINE, " on: ", T.stringof);
    scope (success) {
      writeln("randomize() finished at ", FILE, ":", LINE, " on: ", T.stringof);
    }
  }
  t._esdl__virtualRandomize();
}

void randomizeWith(string C, string FILE=__FILE__, size_t LINE=__LINE__, T, ARGS...)(ref T t, ARGS values)
     if (is (T == class) || is (T == struct)) // && allIntengral!ARGS
{
  debug (CSTSOLVER) {
    import std.stdio;
    writeln("randomize_with() called from ", FILE, ":", LINE, " on: ", T.stringof);

    scope (success) {
      writeln("randomize_with() finished at ", FILE, ":", LINE, " on: ", T.stringof);
    }
  }

  alias _esdl__ProxyType = _esdl__ProxyResolve!T;

  uint cstID = _esdl__ConstraintLambda!(C, FILE, LINE)._esdl__getLambdaConstraintID();
  
  _esdl__ProxyType lambdaProxyInst =
    _esdl__staticCast!(_esdl__ProxyType)(t._esdl__virtualGetLambdaProxyInst(cstID));

  alias CONSTRAINT = lambdaProxyInst._esdl__ConstraintLambdaImpl!(C, FILE, LINE, ARGS);

  CONSTRAINT cstLambda;

  if (lambdaProxyInst._esdl__lambdaCst !is null)
    cstLambda = _esdl__staticCast!(CONSTRAINT)(lambdaProxyInst._esdl__lambdaCst);
    
      
  if (cstLambda is null)
    lambdaProxyInst._esdl__with!(C, FILE, LINE, ARGS)(values);
  else
    cstLambda.lambdaArgs(values);

  t._esdl__virtualRandomizeWith(lambdaProxyInst, lambdaProxyInst._esdl__lambdaCst);
 }

auto randomize(AA...)() {
  alias SS = _esdl__InlineRandomize!AA;
  SS _esdl__inline;
  _esdl__inline._esdl__init!0();
  return _esdl__inline;
}

struct _esdl__InlineRandomize(AA...)
{
  mixin _esdl__ListRandsMixin!(0, AA);

  void _esdl__init(int N = 0)() {
    static if (N == AA.length) { }
    else {
      alias T = typeof(AA[N]);
      static if (isPointer!T) {
	this.tupleof[N] = AA[N];
      }
      else {
	this.tupleof[N] = & AA[N];
      }
      _esdl__init!(N+1)();
    }
  }

  void constraint(string C, string FILE=__FILE__,
		  size_t LINE=__LINE__, ARGS...)(ARGS values) {
    randomizeWith!(C, FILE, LINE, typeof(this), ARGS)(this, values);
  }

  mixin Randomization;
}

mixin template _esdl__ListRandsMixin(int N, AA...)
{
  static if (AA.length == N) { }
  else {
    mixin (_esdl__ListRandMixin!(N, AA[N]));
    mixin _esdl__ListRandsMixin!(N+1, AA);
  }
}

template _esdl__ListRandMixin(int N, alias A) {
  enum string var = A.stringof;
  alias T = typeof(A);
  enum string TS = T.stringof;
  static if (isPointer!T) {
    enum string _esdl__ListRandMixin =
      "@rand typeof(AA[" ~ N.stringof ~ "]) " ~ var ~ ";\n";
  }
  else {
    enum string _esdl__ListRandMixin =
      "@rand typeof(AA[" ~ N.stringof ~ "]) *" ~ var ~ ";\n";
  }
}

static struct _esdl__RandInfo
{
  import core.memory: pureMalloc, pureFree;
  import esdl.data.bvec: ubvec;

  alias malloc = pureMalloc;
  alias free = pureFree;

  enum uint PTRSIZE = cast(uint) size_t.sizeof * 8;

  bool malloced = false;
  union {
    ubvec!PTRSIZE _bvecRandModes;
    size_t* _ptrRandModes;
  }

  bool randMode(int PINDX, uint RANDNUM)() {
    static if (RANDNUM <= PTRSIZE) {
      if (! _bvecRandModes[PINDX]) return true;
      else return false;
    }
    else {
      import core.bitop: bt;
      if (_ptrRandModes is null) return true;
      else {
	if (bt(_ptrRandModes, PINDX)) return false;
	else return true;
      }
    }
  }
      
  void randMode(int PINDX, uint RANDNUM)(bool mode) {
    static if (RANDNUM <= PTRSIZE) {
      if (mode is true) _bvecRandModes[PINDX] = false;
      else _bvecRandModes[PINDX] = true;
    }
    else {
      import core.bitop: btr, bts;
      import core.stdc.string : memset;
      if (_ptrRandModes is null) {
	enum size_t nbytes = PTRSIZE/8 * ((RANDNUM/PTRSIZE)+1);
	_ptrRandModes = cast (size_t*) malloc(nbytes);
	memset(_ptrRandModes, 0, nbytes);
	malloced = true;
      }
      if (mode is true) btr(_ptrRandModes, PINDX);
      else bts(_ptrRandModes, PINDX);
    }
  }

  ~this() {
    if (malloced && _ptrRandModes !is null) free(_ptrRandModes);
  }
      
  // bool[] _randModes;


  _esdl__RandGen _randGen;

  // This instance would be populated only to avoid
  // proxy duplication -- in cases where proxy objects
  // are instanciated inside other proxy objects
  // CstRootProxy!T _esdl__proxyRootInst;
}


// mixin template _esdl__ListRandMixin(alias A)
// {
//   static if (isPointer!(typeof(A))) {
//     typeof(A) A.stringof = A;
//   }
//   else {
//     typeof(A)* A.stringof = &A;
//   }
// }

// string _esdl__ListRandsMixinString(AA...)() {
//   static if (AA.length == 0) {return "";}
//   else {
//     alias A = AA[0];
//     alias T = typeof(A);

//     static if (isPointer!T) {
//       string mix = T.stringof ~ " " ~ A.stringof ~ = 
//     }
    
//     alias TP = typeof(AA[0]);
//     TP* AA[0].stringof = & AA[0];
//     mixin _esdl__ListRands!(AA[1..$]);
//   }
// }

// FIXME add bitvectors to this template filter
template allIntengral(ARGS...) {
  static if(ARGS.length == 0) {
    enum bool allIntengral = true;
  }
  else static if (isRandomizable!(ARGS[0])) {
    enum bool allIntengral = allIntengral!(ARGS[1..$]);
  }
  else enum bool allIntengral = false;
}
