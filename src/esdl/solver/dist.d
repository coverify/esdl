module esdl.solver.dist;

import esdl.solver.base: CstDistSolverBase;

import esdl.rand.base: CstDomBase;
import esdl.rand.pred: CstPredicate;
import esdl.rand.proxy: _esdl__CstProcessor;

import esdl.data.bvec: isBitVector, to;
import esdl.data.vector: Vector;

struct CstVecDistRange(T)
{
  T _min;
  T _max;
  Vector!(T, "purgeLsst") _purgeList;		// this should be sorted
  size_t _purgeLen;

  uint _weight;			// per item weight
  bool _perItem;
  
  size_t _adjTotalWeight;

  static if (is (T == enum)) {

    enum T[] _elems = getSortedMembers!T();

    static T[] getSortedMembers(T)() {
      import std.algorithm.sorting;
      import std.array;
      import std.traits: EnumMembers;

      return array([EnumMembers!T].sort());
    }

    static size_t distance(T max, T min) {
      assert (max >= min);
      size_t i, j;
      for (i=0; i!=_elems.length; ++i) {
	if (_elems[i] == min) break;
      }
      for (j=_elems.length; j!=0; --j) {
	if (_elems[j-1] == max) break;
      }
      return j - i;
    }

    static T travel(T min, size_t distance) {
      size_t j;
      while (_elems[j] != min) j += 1;
      return (_elems[j + distance]);
    }
  }
  else {
    static size_t distance(T max, T min) {
      assert (max >= min);
      return max - min + 1;
    }

    static T travel(T min, size_t distance) {
      return cast(T) (min + distance);
    }
    
  }


  this(T min, T max, uint weight, bool perItem=false) {
    _min = min <= max ? min : max;
    _max = min <= max ? max : min;
    _perItem = perItem;
    _weight = weight;
    reset();
  }
  
  size_t getWeight() {
    return _adjTotalWeight;
  }

  void adjustWeights() {
    if (_perItem) {
      _adjTotalWeight = _weight *
	(distance(_max, _min) - _purgeLen);
      // (_max - _min + 1 - cast(uint) _purgeList.length);
    }
    else {
      if (distance(_max, _min) == _purgeLen) _adjTotalWeight = 0;
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
	addPurgeElem(T.init);	// this also increments _purgeLen
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
      size_t index = 
	cast(size_t) (((distance(_max, _min) - _purgeLen) * select) / _adjTotalWeight);
      // foreach (elem; _purgeList) {
      foreach (elem; _purgeList[0.._purgeLen]) {
	size_t eindex = distance(elem, _min) - 1;
	if (eindex <= index) index += 1;
	else break;
      }
      var = travel(_min, index);
      select = -1;
      return true;
    }
  }
}


class CstVecDistSolver(T): CstDistSolverBase
{
  import esdl.base.rand: _esdl__RandGen;
  import std.random: uniform;

  Vector!(CstVecDistRange!T, "set") _set;
  CstDomBase _dom;

  this(CstDomBase dom) { _dom = dom; }

  final override CstDomBase getDomain() { return _dom; }

  void opOpAssign(string op)(CstVecDistRange!T dist) if(op == "~") {
    import std.algorithm.searching: countUntil;
    ptrdiff_t pos = countUntil!((a, b) {return a._min >= b._min;})(_set[], dist);
    if (pos == -1) {
      // if (_set.length > 0 && _set[$-1]._max >= dist._min) {
      // 	assert(false, "Overlapping 'dist' constraint");
      // }
      // else {
      _set ~= dist;
      // }
    }
    else {
      // if (_purgeList[pos] != elem) {
      // if (_set[pos]._min <= dist._max) {
      // 	assert(false, "Overlapping 'dist' constraint");
      // }
      // if (pos != 0 && _set[pos-1]._max >= dist._min) {
      // 	assert(false, "Overlapping 'dist' constraint");
      // }
      _set.length = _set.length + 1;
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
    static if (isBitVector!T) {
      T e = to!T(elem);
    }
    else {
      T e = cast(T) elem;
    }
    foreach (ref dist; _set) {
      if (dist.purge(e)) break;
    }
  }

  override void uniform(CstDomBase dom, _esdl__RandGen randGen,
			_esdl__CstProcessor proc) {
    assert (randGen !is null);
    dom.setVal(this.uniform(randGen), proc);
  }
  
  override void reset() {
    foreach (ref dist; _set) {
      dist.reset();
    }
  }

  T urandom() {
    import esdl.base.rand: getRandGen;
    return uniform(getRandGen());
  }

  // T uniform(ref Random gen) {
  //   double select = getTotalWeight() * uniform(0.0, 1.0, gen);
  //   T var;
  //   foreach (ref dist; _set) {
  //     if (dist.setVal(var, select)) break;
  //   }
  //   return var;
  // }

  T uniform(_esdl__RandGen rgen) {
    assert (rgen !is null);
    double select = getTotalWeight() * rgen.get();
    T var;
    foreach (ref dist; _set) {
      if (dist.setVal(var, select)) break;
    }
    return var;
  }
}

struct CstLogicDistRange(T)
{
  T _term;
  bool _purge;

  uint _weight;			// per item weight
  bool _perItem;
  
  size_t _adjTotalWeight;

  static if (is (T == enum)) {
    enum T[] _elems = getSortedMembers!T();

    static T[] getSortedMembers(T)() {
      import std.algorithm.sorting;
      import std.array;
      import std.traits: EnumMembers;

      return array([EnumMembers!T].sort());
    }
  }

  static size_t distance(T max, T min) {
    assert (max >= min);
    return max - min + 1;
  }

  static T travel(T min, size_t distance) {
    return cast(T) (min + distance);
  }


  this(T term, uint weight, bool perItem=false) {
    _term = term;
    _perItem = perItem;
    _weight = weight;
    reset();
  }
  
  size_t getWeight() {
    return _adjTotalWeight;
  }

  void adjustWeights() {
    if (_purge) _adjTotalWeight = 0;
    else _adjTotalWeight = _weight;
  }

  void reset() {
    _purge = false;
    adjustWeights();
  }

  bool purge(T elem) {
    if (elem == _term) {
      _purge = true;
      adjustWeights();
      return true;
    }
    else return false;
  }

  string describe() {
    import std.conv: to;
    string str;
    str ~= "Term: " ~ _term.to!string;
    str ~= "\nPurge: " ~ _purge.to!string;
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
      if (_purge) return false;
      else {
	var = _term;
	select = -1;
	return true;
      }
    }
  }
}

class CstLogicDistSolver(T): CstDistSolverBase
{
  import esdl.base.rand: _esdl__RandGen;
  import std.random: uniform;

  CstLogicDistRange!T [] _set;
  CstDomBase _dom;

  this(CstDomBase dom) { _dom = dom; }

  final override CstDomBase getDomain() { return _dom; }

  void opOpAssign(string op)(CstLogicDistRange!T dist) if(op == "~") {
    _set ~= dist;
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

  override void uniform(CstDomBase dom, _esdl__RandGen randGen,
			_esdl__CstProcessor proc) {
    dom.setVal(this.uniform(randGen), proc);
  }
  
  override void reset() {
    foreach (ref dist; _set) {
      dist.reset();
    }
  }

  // T uniform(ref Random gen) {
  //   double select = getTotalWeight() * uniform(0.0, 1.0, gen);
  //   T var;
  //   foreach (ref dist; _set) {
  //     if (dist.setVal(var, select)) break;
  //   }
  //   return var;
  // }

  T uniform(_esdl__RandGen rgen) {
    double select = getTotalWeight() * rgen.get();
    T var;
    foreach (ref dist; _set) {
      if (dist.setVal(var, select)) break;
    }
    return var;
  }
}

class CstDistPredSolver	// agent of dist and related predicates
{
  void initialize(_esdl__CstProcessor proc) {
    _preds.reset();

    _distPred = null;
    _state = State.INIT;
  }
  
  Vector!(CstPredicate, "preds") _preds;
  CstPredicate _distPred;

  CstPredicate[] predicates() {
    return _preds[];
  }

  void distPred(CstPredicate pred) {
    pred._state = CstPredicate.State.GROUPED;
    _distPred = pred;
  }

  void addPredicate(CstPredicate pred) {
    pred._state = CstPredicate.State.GROUPED;
    _preds ~= pred;
  }

  public enum State: ubyte
  {   INIT,
      SOLVED
      }

  State _state;
  
  void reset() {
    _state = State.INIT;
    if (_distPred !is null) {
      _distPred = null;
    }
  }

  void markSolved() {
    _state = State.SOLVED;
  }

  bool isSolved() {
    return _state == State.SOLVED;
  }

  void solve(_esdl__CstProcessor proc) {
    if (proc.debugSolver()) {
      import std.stdio;
      writeln(describe());
    }

    assert (_distPred.isGuardEnabled());
    CstDistSolverBase dist = _distPred._expr.getDist();
    CstDomBase distDomain = _distPred.distDomain();
    dist.reset();
    foreach (wp; _preds) {
      assert (wp.isGuardEnabled());
      if (wp.isGuardEnabled()) {
	// import std.stdio;
	// writeln(wp.describe());
	bool compat = wp._expr.isCompatWithDist(distDomain);
	if (compat is false)
	  assert (false, "can only use != or !inside operator on distributed domains");
	wp._expr.visit(dist, proc);
	wp.markPredSolved(proc);
      }
      else {
	wp.markPredSolved(proc);
      }
    }
    dist.uniform(distDomain, proc.getRandGen(), proc);
    proc.addSolvedDomain(distDomain);
    _distPred.markPredSolved(proc);


    this.markSolved();

  }
      

  string describe() {
    import std.conv: to;
    string description = "CstDistPredSolver -- \n";
    if (_preds.length > 0) {
      description ~= "  Predicates:\n";
      foreach (pred; _preds) {
	description ~= "    " ~ pred._esdl__getName() ~ '\n';
      }
    }
    if (_distPred !is null) {
      description ~= "  Dist Predicate:\n";
      description ~= "    " ~ _distPred._esdl__getName() ~ '\n';
    }
    return description;
  }
}
