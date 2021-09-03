module esdl.base.rand;

import std.traits: isIntegral, isBoolean, EnumMembers;
import std.random;

import esdl.data.bvec: isBitVector;


T urandom(T=uint)() if (isIntegral!T || isBitVector!T) {
  static if(isBitVector!T) {
    T v;
    v.randomize(getRandGen().getGen());
    return v;
  }
  else {
    import std.random: uniform;
    auto v = uniform!T(getRandGen().getGen());
    // debug(SEED) {
    //   import std.stdio;
    //   stdout.writeln("URANDOM returns: ", v);
    // }
    return v;
  }
}

bool urandom(T=bool)() if (isBoolean!T) {
  import std.random: uniform;
  uint v = uniform!("[]", uint)(0, 1, getRandGen().getGen());
  if (v == 0) return false;
  else return true;
 }

R shuffle(R)(ref R range) {
  import std.random: randomShuffle;
  return randomShuffle(range, getRandGen().getGen());
 }

T urandom(string BOUNDARY="[)", T=uint)(T min, T max)
  if (isIntegral!T || isBitVector!T) {
    import std.random: uniform;
    return uniform!(BOUNDARY, T)(min, max, getRandGen().getGen());
  }

T urandom_range(string BOUNDARY="[)", T=uint)(T min, T max) {
  import std.random: uniform;
  return uniform!(BOUNDARY, T)(min, max, getRandGen().getGen());
}

void srandom(uint _seed) {
  getRandGen().seed(_seed);
}

_esdl__RandGen getRandGen() {
  return _esdl__RandGen.getRandGen();
}

class _esdl__RandGen
{
  import std.random;

  private Random _gen;

  private uint _seed;

  static _esdl__RandGen _randGen;

  // Each process, routine and the root process have their own random
  // generator. This is done to enable random stability.
  static _esdl__RandGen getRandGen() {
    import esdl.base.core: Procedure, Process, RootThread;
    Procedure proc;
    proc = Process.self;
    if (proc is null) {
      proc = RootThread.self;
    }
    if (proc !is null) {
      return proc.getRandGen();
    }
    else {
      if (_randGen is null) {
	_randGen = new _esdl__RandGen(// uniform!int()
				      0);
      }
      return _randGen;
    }
  }

  ref Random getGen() {
    return _gen;
  }

  this(uint seed) {
    _seed = seed;
    _gen = Random(seed);
  }

  void setState(ref Random state) {
    _gen = state;
  }
  
  void seed(uint seed) {
    _seed = seed;
    _gen.seed(seed);
  }

  bool flip() {
    auto x = dice(_gen, 50, 50);
    if (x == 0) return false;
    else return true;
  }

  double get() {
    return uniform(0.0, 1.0, _gen);
  }

  @property T gen(T)() {
    import esdl.data.bvec: isBitVector;
    static if (isBoolean!T) {
      return flip();
    }
    else static if (is (T == enum)) {
      static immutable T[EnumMembers!T.length] vals = [EnumMembers!T];
      return vals[uniform(0, cast(uint) vals.length, _gen)];
    }
    else static if (isIntegral!T) {
      return uniform!(T)(_gen);
    }
    else static if (isBitVector!T) {
      T val;
      val.randomize(_gen);
      return val;
    }
    else {
      static assert(false);
    }
  }

  @property void gen(T)(T* t) {
    import esdl.data.bvec: isBitVector;
    static if (isBoolean!T) {
      *t = cast(T) flip();
    }
    else static if (is (T == enum)) {
      static immutable T[EnumMembers!T.length] vals = [EnumMembers!T];
      *t = vals[uniform(0, cast(uint) vals.length, _gen)];
    }
    else static if(isIntegral!T) {
      *t = uniform!(T)(_gen);
    }
    else static if(isBitVector!T) {
      t.randomize(_gen);
    }
    else {
      static assert(false);
    }
  }

  @property void gen(T)(ref T t) {
    import esdl.data.bvec: isBitVector;
    static if (isBoolean!T) {
      t = cast(T) flip();
    }
    else static if (is (T == enum)) {
      static immutable T[EnumMembers!T.length] vals = [EnumMembers!T];
      t = vals[uniform(0, cast(uint) vals.length, _gen)];
    }
    else static if(isIntegral!T) {
      t = uniform!(T)(_gen);
    }
    else static if(isBitVector!T) {
      t.randomize(_gen);
    }
    else {
      static assert(false);
    }
  }

  @property auto gen(T1, T2)(T1 a, T2 b)
       if(isIntegral!T1 && isIntegral!T2) {
	 return uniform(a, b, _gen);
       }

  @property void gen(T, T1, T2)(ref T t, T1 a, T2 b)
       if(isIntegral!T1 && isIntegral!T2) {
	 t = uniform(a, b, _gen);
       }

  @property void gen(T, T1, T2)(T* t, T1 a, T2 b)
       if(isIntegral!T1 && isIntegral!T2) {
	 *t = uniform(a, b, _gen);
       }
}
