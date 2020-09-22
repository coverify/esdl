module esdl.rand.dist;
import esdl.rand.base: CstDomain;
import esdl.rand.misc: _esdl__RandGen;

struct DistRange(T)
{
  T _min;
  T _max;
  T [] _purgeList;		// this should be sorted
  uint _purgeLen;

  uint _weight;			// per item weight
  bool _perItem;
  
  uint _adjTotalWeight;

  this(T min, T max, uint weight, bool perItem=false) {
    _min = min;
    _max = max;
    _perItem = perItem;
    _weight = weight;
    reset();
  }
  
  uint getWeight() {
    return _adjTotalWeight;
  }

  void adjustWeights() {
    if (_perItem) {
      _adjTotalWeight = _weight *
	(_max - _min + 1 - cast(uint) _purgeLen);
      // (_max - _min + 1 - cast(uint) _purgeList.length);
    }
    else {
      if (_max - _min + 1 == _purgeLen) _adjTotalWeight = 0;
      // if (_max - _min + 1 == _purgeList.length) _adjTotalWeight = 0;
      else _adjTotalWeight = _weight;
    }
  }

  void reset() {
    _purgeLen = 0;
    // _purgeList.length = 0;
    adjustWeights();
  }

  void addPurgeElem(T elem) {
    if (_purgeLen >= _purgeList.length) {
      assert (_purgeLen == _purgeList.length);
      _purgeList.length = _purgeLen + 1;
    }
    _purgeList[_purgeLen] = elem;
    _purgeLen += 1;
  }

  bool purge(T elem) {
    import std.algorithm.searching: countUntil;
    if (elem >= _min && elem <= _max) {
      ptrdiff_t pos = countUntil!((a, b) {return a >= b;})
        // (_purgeList, elem);
	(_purgeList[0.._purgeLen], elem);
      if (pos == -1) {
	// _purgeList ~= elem;
	addPurgeElem(elem);
      }
      else if (_purgeList[pos] != elem) {
	// _purgeList.length += 1;
	addPurgeElem(0);	// this also increments _purgeLen
	// for (size_t i=_purgeList.length-1; i!=pos; --i) {
	for (size_t i=_purgeLen-1; i!=pos; --i) {
	  _purgeList[i] = _purgeList[i-1];
	}
	_purgeList[pos] = elem;
      }
      adjustWeights();
      return true;
    }
    else return false;
  }

  string describe() {
    import std.conv: to;
    string str;
    str ~= "Min: " ~ _min.to!string;
    str ~= "\nMax: " ~ _max.to!string;
    // str ~= "\nPurge: " ~ _purgeList.to!string;
    str ~= "\nPurge: " ~ _purgeList[0.._purgeLen].to!string;
    str ~= "\nWeight: " ~ _weight.to!string;
    str ~= "\nPer Item: " ~ _perItem.to!string;
    str ~= "\nTotal Adjusted Weight: " ~ _adjTotalWeight.to!string;
    return str;
  }

  bool setVal(ref T var, ref double select) {
    if (select >= _adjTotalWeight) {
      select -= _adjTotalWeight;
      return false;
    }
    else {
      T index = cast(T)
	// ((_max - _min + 1 - cast (T) _purgeList.length) * select) /
	((_max - _min + 1 - cast (T) _purgeLen) * select) /
	_adjTotalWeight;
      // foreach (elem; _purgeList) {
      foreach (elem; _purgeList[0.._purgeLen]) {
	T eindex = cast(T) (elem - _min);
	if (eindex <= index) index += 1;
	else break;
      }
      var = cast(T) (_min + index);
      select = -1;
      return true;
    }
  }
}


abstract class DistRangeSetBase {
  abstract void purge(long item);
  abstract void uniform(CstDomain dom, _esdl__RandGen randGen);
  abstract void reset();
}

class DistRangeSet(T): DistRangeSetBase
{
  import std.random: uniform, rndGen, Random;

  DistRange!T [] _set;

  void opOpAssign(string op)(DistRange!T dist) if(op == "~") {
    import std.algorithm.searching: countUntil;
    ptrdiff_t pos = countUntil!((a, b) {return a._min >= b._min;})(_set, dist);
    if (pos == -1) {
      if (_set.length > 0 && _set[$-1]._max >= dist._min) {
	assert(false, "Overlapping 'dist' constraint");
      }
      else {
	_set ~= dist;
      }
    }
    else {
      // if (_purgeList[pos] != elem) {
      if (_set[pos]._min <= dist._max) {
	assert(false, "Overlapping 'dist' constraint");
      }
      if (pos != 0 && _set[pos-1]._max >= dist._min) {
	assert(false, "Overlapping 'dist' constraint");
      }
      _set.length += 1;
      for (size_t i=_set.length-1; i!=pos; --i) {
	_set[i] = _set[i-1];
      }
      _set[pos] = dist;
    }
  }

  uint getTotalWeight() {
    uint weight = 0;
    foreach (ref dist; _set) {
      weight += dist.getWeight();
    }
    return weight;
  }

  override void purge(long elem) {
    T e = cast(T) elem;
    foreach (ref dist; _set) {
      if (dist.purge(e)) break;
    }
  }

  override void uniform(CstDomain dom, _esdl__RandGen randGen) {
    dom.setVal(this.uniform(randGen));
  }
  
  override void reset() {
    foreach (ref dist; _set) {
      dist.reset();
    }
  }

  T uniform(ref Random gen = rndGen()) {
    double select = getTotalWeight() * uniform(0.0, 1.0, gen);
    T var;
    foreach (ref dist; _set) {
      if (dist.setVal(var, select)) break;
    }
    assert(select <  0);
    return var;
  }

  T uniform(_esdl__RandGen rgen) {
    double select = getTotalWeight() * rgen.get();
    T var;
    foreach (ref dist; _set) {
      if (dist.setVal(var, select)) break;
    }
    assert(select <  0);
    return var;
  }
}
