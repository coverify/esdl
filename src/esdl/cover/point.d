// Written in the D programming language.

// Copyright: Coverify Systems Technology 2016
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.cover.point;
import esdl.cover.bins;
import esdl.data.vector;
import std.typecons: Tuple;
import esdl.data.bvec: ulvec, ubvec, lvec, bvec, isBitVector;
// Coverage

abstract class _esdl__BaseCoverPoint {

  uint[] _hits;	   // Total hits
  // list of indexes that get hit in this sample call
  uint _hitLimit = 1; // _hits[i] >= _hitLimit means we count it
  uint _numHits = 0;
  Vector!(uint, "_indexes") _indexes; 
  
  void sample ();
  
  double get_coverage() {
    return (cast(double) _numHits) / _hits.length;
  }
  double get_curr_coverage() {
    return (cast(double) _indexes.length) / _hits.length;
  }
  
  void start();
  void stop();
  size_t get_weight();
  bool isCross();
  
  void addHit(size_t idx) {
    _hits[idx] ++;
    if (_hits[idx] == _hitLimit) {
      _numHits ++;
    }
    _indexes ~= cast(uint) idx;
  }

  void resetCP() {
    _indexes.length = 0;
  }  
}

struct Parameters {
  size_t weight = 1;
  size_t goal = 90;
  size_t at_least = 1;
  size_t auto_bin_max = 64;
  size_t corss_auto_bin_max = size_t.max;
}

struct StaticParameters {
  size_t weight = 1;
  size_t goal = 90;
}

abstract class CoverPoint(T): _esdl__BaseCoverPoint
{
  import std.traits: isIntegral;

  static if (isIntegral!T) enum size_t BITNUM = T.sizeof * 8;
  static if (isBitVector!T) enum size_t BITNUM = T.SIZE;

  alias LT = ulvec!BITNUM;
  
  alias FilterDG = bool delegate(T val);

  alias ValArray1RT = T[];
  alias ValArray2RT = T[][];

  alias WldArray1RT = LT[];
  alias WldArray2RT = LT[][];

  alias ValArray1DG = T[] delegate();
  alias ValArray2DG = T[][] delegate();

  alias WldArray1DG = LT[] function();
  alias WldArray2DG = LT[][] delegate();

  template ValueDelegateDims(alias DG)
  {
    import std.traits: ReturnType;
    alias RT = ReturnType!DG;
    static if (is (RT == ValArray1RT))
      enum uint ValueDelegateDims = 1;
    else static if (is (RT == ValArray2RT))
      enum uint ValueDelegateDims = 2;
    else static assert (false, "Incompatible Delegate Type: " ~
			typeof(DG).stringof);
  }

  template WildDelegateDims(alias DG)
  {
    import std.traits: ReturnType;
    alias RT = ReturnType!DG;
    static if (is (RT == WldArray1RT))
      enum uint WildDelegateDims = 1;
    else static if (is (RT == WldArray2RT))
      enum uint WildDelegateDims = 2;
    else static assert (false, "Incompatible Delegate Type: " ~
			typeof(DG).stringof);
  }
  
  T _esdl__t();
  alias _esdl__T = T;

  struct EsdlValRangeContainer	// container for constructing value and range bins
  {
    T[] _elems;

    T[] _mins;
    T[] _maxs;

    Tuple!(size_t, size_t)[] _delims;

    string[] _wildcards;

    void reset() {
      _elems.length = 0;
      _mins.length = 0;
      _maxs.length = 0;
      _wildcards.length = 0;
      _delims.length = 0;
    }
  }

  EsdlValRangeContainer _esdl__container;

  void _esdl__addRange(T min, T max) {
    _esdl__container._mins ~= min;
    _esdl__container._maxs ~= max;
  }

  void _esdl__addElem(T elem) {
    _esdl__container._elems ~= elem;
  }

  void _esdl__addWildcard(string wildcard) {
    _esdl__container._wildcards ~= wildcard;
  }

  void _esdl__addDelimiter() {
    _esdl__container._delims ~=
      Tuple!(size_t, size_t)(_esdl__container._mins.length +
			     _esdl__container._wildcards.length,
			     _esdl__container._elems.length);
  }

  void _esdl__initBins() {
    size_t lengthSum = 0;
    foreach (ref b; _esdl__cvrBins) {
      b._offset = lengthSum;
      lengthSum += b._length;
    }
    _hits.length = lengthSum;
  }

  EsdlBaseBin!(T)[] _esdl__cvrBins;
  EsdlBaseBin!(T)[] _esdl__illBins;
  EsdlBaseBin!(T)[] _esdl__ignBins;

  auto getBins() {
    return _esdl__cvrBins;
  }

  string describe() {
    string s = "";
    foreach (bin; _esdl__cvrBins) {
      s ~= bin.describe();
    }
    s ~= "\n";
    return s;
  }
  
  override void sample() {
    auto tval = _esdl__t();
    foreach (ref bin; _esdl__cvrBins) {
      bin.sample(tval);
    }
  }
  
  override void start() { }
  override void stop() { }
  override size_t get_weight() {
    return 1;
  }
  override bool isCross() {
    return false;
  }
}

class Cross: _esdl__BaseCoverPoint {
  _esdl__BaseCoverPoint [] coverPoints;
  size_t [] multFactor;
  
  this (_esdl__BaseCoverPoint[] cps) {
    coverPoints = cps;
    _esdl__initBins();
  }

  void _esdl__initBins() {
    size_t lengthProd = 1;
    foreach (ref b; coverPoints) {
      multFactor ~= lengthProd;
      lengthProd *= b._hits.length;
    }
    _hits.length = lengthProd;
  }

  void sampleRecursive(int idx, size_t pos) {
    if (idx == coverPoints.length) {
      addHit(pos);
      return;
    }
    foreach (hit; coverPoints[idx]._indexes) {
      sampleRecursive(idx+1, pos + hit * multFactor[idx]);
    }
  }
  
  // assume that the coverpoints are sampled before
  override void sample() {
    sampleRecursive(0, 0);
  }

  override void start() { }
  override void stop() { }
  
  override size_t get_weight() {
    return 1;
  }
  override bool isCross() {
    return true;
  }
}
