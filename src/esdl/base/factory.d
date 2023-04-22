module esdl.base.factory;

import core.stdc.stdlib: realloc, malloc;

import std.traits: isExpressionTuple, isAggregateType, isBasicType,
  isAssociativeArray, isArray, isStaticArray, isPointer, Unqual;
import std.meta: AliasSeq;

struct Factory(string ID)
{
  enum uint minSize = 16;

  __gshared ClassInfo* _elems;
  __gshared uint _elemCount = 0;

  __gshared uint _allocCount;

  static void register(T)() {
    register(typeid(T));
  }

  static void register(ClassInfo classInfo) {
    if (_elems is null) {
      _elems = cast(ClassInfo*) malloc(ClassInfo.sizeof * minSize);
      _allocCount = minSize;
    }
    else if (_allocCount <= _elemCount) {
      _allocCount *= 2;
      _elems = cast(ClassInfo*) realloc(_elems, ClassInfo.sizeof * _allocCount);
    }
    _elems[_elemCount] = classInfo;
    _elemCount += 1;
  }

  static ClassInfo[] getElements() {
    return _elems[0.._elemCount];
  }

  static Object create(string tname) {
    foreach (ci; getElements()) {
      if (ci.name == tname) {
	return ci.create();
      }
    }
    return null;
  }
}

template fullyQualifiedName(T...)
if (T.length == 1)
{

    static if (is(T))
        enum fullyQualifiedName = fqnType!(T[0], false, false, false, false);
    else
        enum fullyQualifiedName = fqnSym!(T[0]);
}

private template fqnSym(alias T : X!A, alias X, A...)
{
    template fqnTuple(T...)
    {
        static if (T.length == 0)
            enum fqnTuple = "";
        else static if (T.length == 1)
        {
            static if (isExpressionTuple!T)
                enum fqnTuple = T[0].stringof;
            else
                enum fqnTuple = fullyQualifiedName!(T[0]);
        }
        else
            enum fqnTuple = fqnTuple!(T[0]) ~ ", " ~ fqnTuple!(T[1 .. $]);
    }

    enum fqnSym =
        fqnSym!(__traits(parent, X)) ~
        '.' ~ __traits(identifier, X) ~ "!(" ~ fqnTuple!A ~ ")";
}

private template fqnSym(alias T)
{
    static if (__traits(compiles, __traits(parent, T)) && !__traits(isSame, T, __traits(parent, T)))
        enum parentPrefix = fqnSym!(__traits(parent, T)) ~ ".";
    else
        enum parentPrefix = null;

    static string adjustIdent(string s)
    {
        import std.algorithm.searching : findSplit, skipOver;

        if (s.skipOver("package ") || s.skipOver("module "))
            return s;
        return s.findSplit("(")[0];
    }
    enum fqnSym = parentPrefix ~ adjustIdent(__traits(identifier, T));
}

private template fqnType(T,
			 bool alreadyConst, bool alreadyImmutable, bool alreadyShared, bool alreadyInout)
{
  // Convenience tags
  enum {
    _const = 0,
    _immutable = 1,
    _shared = 2,
    _inout = 3
  }

  alias qualifiers   = AliasSeq!(is(T == const), is(T == immutable), is(T == shared), is(T == inout));
  alias noQualifiers = AliasSeq!(false, false, false, false);

  string storageClassesString(uint psc)() @property
  {
    import std.conv : text;

    alias PSC = ParameterStorageClass;

    return text(
		psc & PSC.scope_ ? "scope " : "",
		psc & PSC.return_ ? "return " : "",
		psc & PSC.in_ ? "in " : "",
		psc & PSC.out_ ? "out " : "",
		psc & PSC.ref_ ? "ref " : "",
		psc & PSC.lazy_ ? "lazy " : "",
		);
  }

  string parametersTypeString(T)() @property
  {
    alias parameters   = Parameters!(T);
    alias parameterStC = ParameterStorageClassTuple!(T);

    enum variadic = variadicFunctionStyle!T;
    static if (variadic == Variadic.no)
      enum variadicStr = "";
    else static if (variadic == Variadic.c)
      enum variadicStr = ", ...";
    else static if (variadic == Variadic.d)
      enum variadicStr = parameters.length ? ", ..." : "...";
    else static if (variadic == Variadic.typesafe)
      enum variadicStr = " ...";
    else
      static assert(0, "New variadic style has been added, please update fullyQualifiedName implementation");

    static if (parameters.length)
      {
	import std.algorithm.iteration : map;
	import std.array : join;
	import std.meta : staticMap;
	import std.range : zip;

	string result = join(
			     map!(a => (a[0] ~ a[1]))(
						      zip([staticMap!(storageClassesString, parameterStC)],
							  [staticMap!(fullyQualifiedName, parameters)])
						      ),
			     ", "
			     );

	return result ~= variadicStr;
      }
    else
      return variadicStr;
  }

  string linkageString(T)() @property
  {
    enum linkage = functionLinkage!T;

    if (linkage != "D")
      return "extern(" ~ linkage ~ ") ";
    else
      return "";
  }

  string functionAttributeString(T)() @property
  {
    alias FA = FunctionAttribute;
    enum attrs = functionAttributes!T;

    static if (attrs == FA.none)
      return "";
    else
      return
	(attrs & FA.pure_ ? " pure" : "")
	~ (attrs & FA.nothrow_ ? " nothrow" : "")
	~ (attrs & FA.ref_ ? " ref" : "")
	~ (attrs & FA.property ? " @property" : "")
	~ (attrs & FA.trusted ? " @trusted" : "")
	~ (attrs & FA.safe ? " @safe" : "")
	~ (attrs & FA.nogc ? " @nogc" : "")
	~ (attrs & FA.return_ ? " return" : "");
  }

  string addQualifiers(string typeString,
		       bool addConst, bool addImmutable, bool addShared, bool addInout)
  {
    auto result = typeString;
    if (addShared)
      {
	result = "shared(" ~ result ~")";
      }
    if (addConst || addImmutable || addInout)
      {
	result = (addConst ? "const" : addImmutable ? "immutable" : "inout")
	  ~ "(" ~ result ~ ")";
      }
    return result;
  }

  // Convenience template to avoid copy-paste
  template chain(string current)
  {
    enum chain = addQualifiers(current,
			       qualifiers[_const]     && !alreadyConst,
			       qualifiers[_immutable] && !alreadyImmutable,
			       qualifiers[_shared]    && !alreadyShared,
			       qualifiers[_inout]     && !alreadyInout);
  }

  static if (is(T == string))
    {
      enum fqnType = "string";
    }
  else static if (is(T == wstring))
    {
      enum fqnType = "wstring";
    }
  else static if (is(T == dstring))
    {
      enum fqnType = "dstring";
    }
  else static if (is(T == typeof(null)))
    {
      enum fqnType = "typeof(null)";
    }
  else static if (isAggregateType!T || is(T == enum))
    {
      enum fqnType = chain!(fqnSym!T);
    }
  else static if (isBasicType!T && !is(T == enum))
    {
      enum fqnType = chain!((Unqual!T).stringof);
    }
  else static if (isStaticArray!T)
    {
      import std.conv : to;
      enum fqnType = chain!(
			    fqnType!(typeof(T.init[0]), qualifiers) ~ "[" ~ to!string(T.length) ~ "]"
			    );
    }
  else static if (isArray!T)
    {
      enum fqnType = chain!(
			    fqnType!(typeof(T.init[0]), qualifiers) ~ "[]"
			    );
    }
  else static if (isAssociativeArray!T)
    {
      enum fqnType = chain!(
			    fqnType!(ValueType!T, qualifiers) ~ '[' ~ fqnType!(KeyType!T, noQualifiers) ~ ']'
			    );
    }
  else static if (isSomeFunction!T)
    {
      static if (is(T F == delegate))
        {
	  enum qualifierString =
	    (is(F == shared) ? " shared" : "")
	    ~ (is(F == inout) ? " inout" :
	       is(F == immutable) ? " immutable" :
	       is(F == const) ? " const" : "");
	  enum fqnType = chain!(
				linkageString!T
				~ fqnType!(ReturnType!T, noQualifiers)
				~ " delegate(" ~ parametersTypeString!(T) ~ ")"
				~ functionAttributeString!T
				~ qualifierString
				);
        }
      else
        {
	  enum fqnType = chain!(
				linkageString!T
				~ fqnType!(ReturnType!T, noQualifiers)
				~ (isFunctionPointer!T ? " function(" : "(")
				~ parametersTypeString!(T) ~ ")"
				~ functionAttributeString!T
				);
        }
    }
  else static if (isPointer!T)
    {
      enum fqnType = chain!(
			    fqnType!(PointerTarget!T, qualifiers) ~ "*"
			    );
    }
  else static if (is(T : __vector(V[N]), V, size_t N))
    {
      import std.conv : to;
      enum fqnType = chain!(
			    "__vector(" ~ fqnType!(V, qualifiers) ~ "[" ~ N.to!string ~ "])"
			    );
    }
  else
    // In case something is forgotten
    static assert(0, "Unrecognized type " ~ T.stringof ~ ", can't convert to fully qualified string");
}

// just to make everything compile
int _dummy;
string _dummy_fqn() {
  return fullyQualifiedName!_dummy;
}
