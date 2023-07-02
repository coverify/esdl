// Written in the D programming language.

// Copyright: Coverify Systems Technology 2016
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.cover.point;
import esdl.cover.bins;
// Coverage

interface _esdl__CoverPointIf {
  void sample ();
  double get_coverage();
  double get_curr_coverage();
  void start();
  void stop();
  bool [] get_curr_hits();
  size_t get_weight();
  bool isCross();
  //double query();
}

// cross stuff: 

string _esdl__composeNdimArr(size_t len, string type, string name) {
  string s = type ~ " ";
  for (int i = 0; i < len; i++) {
    s ~= "[]"; 
  }
  s ~= " " ~ name ~ ";";
  return s;
}

string _esdl__crossSampleHelper(int n) {
  import std.conv;
  string s = "bool [][] curr_hits_arr;\n";
  for (int i = 0; i < n; i++) {
    s ~= "curr_hits_arr ~= coverPoints[" ~
      i.to!string() ~ "].get_curr_hits();\n";
  }
  for (int i = 0; i < n; i++) {
    s ~= "foreach (i_" ~ i.to!string() ~ ", is_hit_" ~
      i.to!string() ~ "; curr_hits_arr[" ~ i.to!string() ~ "]) {\n";
    s ~= "if (!is_hit_" ~ i.to!string() ~ ")\ncontinue;\n";
  }
  s ~= "_hits";
  for (int i = 0; i < n; i++) {
    s ~= "[i_" ~ i.to!string() ~ "]"; 
  }
  s ~= "++;\n";
  s ~= "_curr_hits";
  for (int i = 0; i < n; i++) {
    s ~= "[i_" ~ i.to!string() ~ "]"; 
  }
  s ~= " = true;\n";
  for (int i = 0; i < n; i++)
    s ~= "}\n";
  return s;
}

string _esdl__initArrayLengths(string name, int n) {
  import std.conv;
  string s,tmp = name;
  s ~= name ~ ".length = bincnts[0];\n";
  for (int i = 0; i < n; i++) {
    s ~= "for (int i_" ~ (i).to!string() ~
      " = 0; i_" ~ (i).to!string() ~
      " < bincnts[" ~ (i).to!string() ~ "]; i_" ~
      (i).to!string() ~ "++) {\n";
    tmp ~= "[i_" ~ (i).to!string() ~ "]";
    if (i < n - 1)
      s ~= tmp ~ ".length = bincnts[" ~ (i + 1).to!string() ~"];\n";
    else 
      s ~= tmp ~ "= 0;\n";
  }
  for (int i = 0; i < n; i++)
    s ~= "}\n";
  return s;
}

string _esdl__sampleCoverpoints(int n) {
  import std.conv;
  string s;
  for (int i = 0; i < n; i++) {
    s ~= "if (isIntegral!(typeof(N[" ~ i.to!string() ~ "])))";
    s ~= "coverPoints[" ~ i.to!string() ~ "].sample();\n";
  }
  return s;
}

class Cross ( N... ): _esdl__CoverPointIf {
  import std.traits: isIntegral;
  enum size_t len = N.length;
  ulong [] bincnts;
  mixin(_esdl__composeNdimArr(len, "uint", "_hits"));
  mixin(_esdl__composeNdimArr(len, "bool", "_curr_hits"));
  _esdl__CoverPointIf [] coverPoints;
  this () {
    foreach (i , ref elem; N) {
      static if (!(isIntegral!(typeof(elem)))) {
        // elem.Initialize();
        coverPoints ~= elem;
        bincnts ~= elem.getBins().length;
      }
      else {
        auto tmp = new CoverPoint!(elem)(); // here you make from classes which you define inside Cross only
        coverPoints ~= tmp;
        bincnts ~= tmp.getBins().length;
      }
    }
    mixin(_esdl__initArrayLengths("_hits", len));
    mixin(_esdl__initArrayLengths("_curr_hits", len));
  }
  override void sample() {
    mixin(_esdl__initArrayLengths("_curr_hits", len));
    mixin(_esdl__sampleCoverpoints(len));
    mixin(_esdl__crossSampleHelper(N.length));
  }
  override double get_coverage() {
    return 0;
  }
  override double get_curr_coverage() {
    return 0;
  }
  override void start() { }
  override void stop() { }
  override bool [] get_curr_hits() {
    assert (false);
  }
  auto get_cross_curr_hits() {
    return _curr_hits;
  }
  override size_t get_weight() {
    return 1;
  }
  override bool isCross() {
    return true;
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

abstract class CoverPoint(T, string BINS="", N...): _esdl__CoverPointIf
{
  import std.traits: isIntegral;
  T _esdl__t();
  alias _esdl__T = T;
  string outBuffer;
  bool [] _curr_hits;
  bool [] _curr_wild_hits;
  size_t _num_hits;
  size_t _num_curr_hits;
  Parameters option;
  
  static StaticParameters type_option;
  this () {

    // static if (BINS != "") {
    debug (CVRPARSER) pragma(msg, doParse!T(BINS));
    mixin(doParse!T(BINS));
    // }
    // else {
    //   import std.conv;
    //   mixin(doParse!T("bins [64] a = {[" ~ T.min.to!string() ~ ":" ~ T.max.to!string() ~ "]};"));
    // }

    procDyanamicBins(_bins, _dbins);
    procDyanamicBins(_ill_bins, _ill_dbins);
    procStaticBins(_bins, _sbins, _sbinsNum);
    procStaticBins(_ill_bins, _ill_sbins, _ill_sbinsNum);
    procIgnoreBins();
    _curr_hits.length = _bins.length; 
    _curr_wild_hits.length = _wildbins.length;
    if (_bins.length == 0 && _ill_bins.length == 0) {
      import std.conv;
      debug (CVRPARSER) pragma(msg, doParse!T("bins [64] a = {[" ~ T.min.to!string() ~
					      ":" ~ T.max.to!string() ~ "]};"));
      mixin(doParse!T("bins [64] a = {[" ~ T.min.to!string() ~
		      ":" ~ T.max.to!string() ~ "]};"));
      procStaticBins(_bins, _sbins, _sbinsNum);
      _curr_hits.length = _bins.length; 
    }
  }
  
  size_t [] _sbinsNum;
  size_t [] _ig_sbinsNum;
  size_t [] _ill_sbinsNum;
  Bin!(T)[] _bins;
  Bin!(T)[] _sbins;
  Bin!(T)[] _dbins;
  Bin!(T)[] _ig_bins;
  Bin!(T)[] _ill_bins;
  Bin!(T)[] _ill_sbins;
  Bin!(T)[] _ill_dbins;
  WildCardBin!(T)[] _wildbins;
  WildCardBin!(T)[] _ig_wildbins;
  WildCardBin!(T)[] _ill_wildbins;
  DefaultBin _default;
  uint _defaultCount;
  
  int _pos;

  auto getBins() {
    return _bins;
  }

  
  void procIgnoreBins() {
    if (_ig_bins.length == 0) {
      return;
    }
    while (_ig_bins.length > 1) {
      _ig_bins[$-2].or(_ig_bins[$-1]);
      _ig_bins.length --;
    }
    _ig_bins[0].negateBin();
    foreach (ref bin; _bins) {
      bin.and(_ig_bins[0][]);
    }
  }
  void procDyanamicBins(ref Bin!(T) [] alias_bins,
			ref Bin!(T) [] alias_dbins) {
    foreach (tempBin; alias_dbins ) {
      auto ranges = tempBin.getRanges();
      size_t num = 0;
      for (size_t i = 0; i < ranges.length-1; i += 2) {
        for (T j = ranges[i]; j <= ranges[i+1]; j++) {
	  import std.conv;
          string tempname = tempBin.getName ~ "[" ~ to!string(num) ~ "]";
          alias_bins ~= Bin!T(tempname); 
          alias_bins[$ - 1].addRange(j);
          ++num;
        }
      }
    }
    alias_dbins.length = 0;
  }
  void procStaticBins(ref Bin!(T) [] alias_bins,
		      ref Bin!(T) [] alias_sbins,
		      ref size_t [] alias_sbinsNum) {
    import std.conv;
    foreach (index, tempBin; alias_sbins) {
      size_t count = tempBin.count();
      auto ranges = tempBin.getRanges();
      size_t arrSize = alias_sbinsNum[index];
      T Binsize = to!(T)(count / arrSize);
      T rem = to!(T)(count % arrSize);
      size_t binNum = 0;
      T binleft = Binsize;
      for (size_t i = 0; i < arrSize; i++) {
        alias_bins ~= Bin!T(tempBin.getName ~ "[" ~ to!string(i) ~ "]");
      }
      if (Binsize == 0) {
        assert (false, "array size created more than the number " ~
		"of elements in the array");
      }
      for (size_t i = 0; i < ranges.length-1; i+=2) {
        if (binleft == 0) {
          binNum ++;
          assert (binNum < arrSize);
          if (binNum == arrSize - rem) {
            Binsize ++;
          }
          binleft = Binsize;
        }
        size_t rangeCount = size_t(ranges[i+1]) - size_t(ranges[i]) + 1;
        if (rangeCount > binleft) {
          alias_bins[$ - (arrSize - binNum)].addRange((ranges[i]),
						      cast(T)(ranges[i] + binleft - 1));
          ranges[i] += binleft;
          binleft = 0;
          i -= 2;
        }
        else {
          //makeBins ~= 

          alias_bins[$ - (arrSize - binNum)].addRange((ranges[i]),
						      (ranges[i+1]));
          binleft -= rangeCount;
        }
      }
    }
    alias_sbins.length = 0;
    alias_sbinsNum.length = 0;
  }
  string describe() {
    string s = "";
    foreach (bin; _bins) {
      s ~= bin.describe();
    }
    s ~= "\n";
    return s;
  }
  override void sample() {
    // writeln("sampleCalled, number is ", t);
    bool hasHit = false;
    auto tval = _esdl__t();
    foreach (i, ref ill_wbin; _ill_wildbins) {
      if (ill_wbin.checkHit(tval)) {
	assert (false, "illegal bin hit");
      }
    }
    foreach (i, ref ill_bin; _ill_bins) {
      if (ill_bin.checkHit(tval)) {
	assert (false, "illegal bin hit");
      }
    }
    _num_curr_hits = 0;
    foreach (i, ref bin;_bins) {
      _curr_hits[i] = false;
      if (bin.checkHit(tval)) {
	// writeln("bin hit, bin = ", bin.describe());
        if (bin._hits == 0) {
          _num_hits ++;
	  // writeln("first time hit, num_hits ++");
        }
	hasHit = true;
        bin._hits++;
        _curr_hits[i] = true;
        _num_curr_hits ++;
      }
    }
    foreach (i, ref ig_wbin; _ig_wildbins) {
      if (ig_wbin.checkHit(tval)) {
	return;
      }
    }
    foreach (i, ref wbin; _wildbins) {
      _curr_wild_hits[i] = false;
      if (wbin.checkHit(tval)) {
        if (wbin._hits == 0) {
          _num_hits++;
        }
	hasHit = true;
        wbin._hits++;
        _curr_wild_hits[i] = true;
        _num_curr_hits++;
      }
    }
    if (!hasHit) {      
      _default._curr_hit = false      ;
      if (_default._type == Type.ILLEGAL) {
	assert (false, "illegal bin hit");
      }
      else if (_default._type == Type.BIN) {
	_default._curr_hit = true;
	_default._hits ++;
      }
    }
  }
  override double get_coverage() {
    return cast(double)(_num_hits)/_bins.length;
  }
  override double get_curr_coverage() {
    return cast(double)(_num_curr_hits)/_bins.length;
  }
  override void start() { }
  override void stop() { }
  override bool [] get_curr_hits() {
    return _curr_hits;
  }
  override size_t get_weight() {
    return 1;
  }
  override bool isCross() {
    return false;
  }
}

