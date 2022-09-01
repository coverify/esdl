// Written in the D programming language.

// Copyright: Coverify Systems Technology 2016
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.rand.cover;
// Coverage
import esdl.rand.misc: rand;


abstract class _esdl__BaseCoverGroup: rand.disable {
}

// import esdl.rand;
// import esdl.data.bvec;
static string doParse(T)(string Bins) {
  parser!T Parser = parser!T(Bins);
  return Parser.parse();
}

// void sample (T)(T grp) if (is (T: CoverGroup)) {
//   foreach (ref elem; grp.tupleof) {
//     if (!elem.isCross()) {
//       elem.sample();
//     }
//   }
//   foreach (ref elem; grp.tupleof) {
//     if (elem.isCross()) {
//       elem.sample();
//     }
//   }
//  }
// void sample (T)(T grp) if (!is (T: CoverGroup)) {
//   foreach (ref elem; grp.tupleof) {
//     static if (is (typeof(elem): CoverGroup)) {
//       sample(elem);
//     }
//   }
//  }
// double get_coverage (T)(T grp) if (is (T: CoverGroup)) {
//   double total = 0;
//   size_t weightSum = 0;
//   foreach (ref elem; grp.tupleof) {
//     total += elem.get_coverage()*elem.get_weight();
//     weightSum += elem.get_weight();
//   }
//   return total/weightSum;
//  }
// double get_curr_coverage (T)(T grp) if (is (T: CoverGroup)) {
//   double total = 0;
//   size_t weightSum = 0;
//   foreach (ref elem; grp.tupleof) {
//     total += elem.get_curr_coverage()*elem.get_weight();
//     weightSum += elem.get_weight();
//   }
//   return total/weightSum;
//  }
void start (T)(T grp) if (is (T: CoverGroup)) {
  foreach (ref elem; grp.tupleof) {
    elem.start();
  }
 }
void stop (T)(T grp) if (is (T: CoverGroup)) {
  foreach (ref elem; grp.tupleof) {
    elem.stop();
  }
 }
struct parser (T) {
  enum BinType: byte {SINGLE, DYNAMIC, STATIC};
  size_t srcCursor = 0;
  size_t srcLine = 0;
  string outBuffer = "";
  string BINS;

  this(string bins) {
    BINS = bins;
  }
  void fill(in string source) {
    outBuffer ~= source;
  }
  void parseComma() {
    if (BINS[srcCursor] != ',') {
      import std.conv;
      assert (false, "did not add comma in bins range at line " ~
	      srcLine.to!string);
    }
    ++srcCursor;
    parseSpace();
  }
  bool parseRangeType() {
    if (BINS[srcCursor] == ':') {
      ++ srcCursor;
      return true;
    }
    else if (BINS[srcCursor] == '.' && BINS[srcCursor+1] == '.') {
      srcCursor += 2;
      return false;
    }
    else {
      import std.conv;
      assert (false, "error in writing bins at line "~ srcLine.to!string ~
	      " " ~ BINS[srcCursor]);
    }
  }
  void parseCurlyOpen() {
    if (BINS[srcCursor] != '{') {
      assert (false);
    }
    ++ srcCursor;
  }
  void parseEqual() {
    if (BINS[srcCursor] != '=') {
      assert (false);
    }
    ++ srcCursor;
  }
  size_t parseName() {
    auto start = srcCursor;
    while (BINS[srcCursor] != ' ' &&
	   BINS[srcCursor] != '=' &&
	   BINS[srcCursor] != '\n'&&
	   BINS[srcCursor] != '\t' ) {
      ++srcCursor;
    }
    return start;
  }
  BinType parseType() {
    parseSpace();
    if (BINS[srcCursor] == '[') {
      srcCursor ++;
      parseSpace();
      if (BINS[srcCursor] == ']') {
        ++srcCursor;
        return BinType.DYNAMIC;
      }
      return BinType.STATIC;
    }
    else {
      return BinType.SINGLE;
    }
  }
  size_t parseLiteral() {
    size_t start = srcCursor;
    if (BINS[srcCursor] == '$') {
      ++srcCursor;
      return parseLiteral()-1;
    }
    // check for - sign
    if (BINS[srcCursor] == '-') {
      ++srcCursor;
    }
    // look for 0b or 0x
    if (srcCursor + 2 <= BINS.length &&
        BINS[srcCursor] == '0' &&
        (BINS[srcCursor+1] == 'x' ||
         BINS[srcCursor+1] == 'X')) { // hex numbers
      srcCursor += 2;
      while (srcCursor < BINS.length) {
        char c = BINS[srcCursor];
        if ((c >= '0' && c <= '9') ||
            (c >= 'a' && c <= 'f') ||
            (c >= 'A' && c <= 'F') ||
            (c == '_')) {
          ++srcCursor;
        }
        else {
          break;
        }
      }
    }
    else if (srcCursor + 2 <= BINS.length &&
	     BINS[srcCursor] == '0' &&
	     (BINS[srcCursor+1] == 'b' ||
	      BINS[srcCursor+1] == 'B')) { // binary numbers
      srcCursor += 2;
      while (srcCursor < BINS.length) {
        char c = BINS[srcCursor];
        if ((c == '0' || c == '1' || c == '_')) {
          ++srcCursor;
        }
        else {
          break;
        }
      }
    }
    else {			// decimals
      while (srcCursor < BINS.length) {
        char c = BINS[srcCursor];
        if ((c >= '0' && c <= '9') ||
            (c == '_')) {
          ++srcCursor;
        }
        else {
          break;
        }
      }
    }
    if (srcCursor > start) {
      // Look for long/short specifier
      while (srcCursor < BINS.length) {
        char c = BINS[srcCursor];
        if (c == 'L' || c == 'u' ||  c == 'U') {
          ++srcCursor;
        }
        else {
          break;
        }
      }
    }
    return start;
  }
  bool parseIsWild() {
    if (srcCursor + 8 < BINS.length &&
	BINS[srcCursor .. srcCursor+8] == "wildcard") {
      srcCursor += 8;
      parseSpace();
      return true;
    }
    return false;
  }
  string parseBinDeclaration() {
    if (srcCursor + 4 < BINS.length &&
	BINS[srcCursor .. srcCursor+4] == "bins") {
      srcCursor += 4;
      return "";
    }
    else if (srcCursor + 11 < BINS.length &&
	     BINS[srcCursor .. srcCursor + 11] == "ignore_bins") {
      srcCursor += 11;
      return "_ig";
    }
    else if (srcCursor + 12 < BINS.length &&
	     BINS[srcCursor .. srcCursor + 12] == "illegal_bins") {
      srcCursor += 12;
      return "_ill";
    }
    else {
      import std.conv;
      assert (false, "error in writing bins at line " ~ srcLine.to!string);
    }
  }
  size_t parseSpace() {
    size_t start = srcCursor;
    while (srcCursor < BINS.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if (srcCursor > srcTag) {
        continue;
      }
      else {
        break;
      }
    }
    return start;
  }
  size_t parseComment() {
    auto start = srcCursor;
    while (srcCursor < BINS.length) {
      auto srcTag = srcCursor;
      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      if (srcCursor > srcTag) {
        continue;
      }
      else {
        break;
      }
    }
    return start;
  }
  size_t parseWhiteSpace() {
    auto start = srcCursor;
    while (srcCursor < BINS.length) {
      auto c = BINS[srcCursor];
      // eat up whitespaces
      if (c is '\n') ++srcLine;
      if (c is ' ' || c is '\n' || c is '\t' || c is '\r' || c is '\f') {
        ++srcCursor;
        continue;
      }
      else {
        break;
      }
    }
    return start;
  }

  size_t parseLineComment() {
    size_t start = srcCursor;
    if (srcCursor >= BINS.length - 2 ||
        BINS[srcCursor] != '/' || BINS[srcCursor+1] != '/') return start;
    else {
      srcCursor += 2;
      while (srcCursor < BINS.length) {
        if (BINS[srcCursor] == '\n') {
          break;
        }
        else {
          if (srcCursor == BINS.length) {
            // commment unterminated
	    import std.conv;
            assert (false, "Line comment not terminated at line " ~
		    srcLine.to!string);
          }
        }
        srcCursor += 1;
      }
      srcCursor += 1;
      return start;
    }
  }

  size_t parseBlockComment() {
    size_t start = srcCursor;
    if (srcCursor >= BINS.length - 2 ||
        BINS[srcCursor] != '/' || BINS[srcCursor+1] != '*') return start;
    else {
      srcCursor += 2;
      while (srcCursor < BINS.length - 1) {
        if (BINS[srcCursor] == '*' && BINS[srcCursor+1] == '/') {
          break;
        }
        else {
          if (srcCursor == BINS.length - 1) {
            // commment unterminated
	    import std.conv;
            assert (false, "Block comment not terminated at line " ~
		    srcLine.to!string);
          }
        }
        srcCursor += 1;
      }
      srcCursor += 2;
      return start;
    }
  }
  size_t parseNestedComment() {
    size_t nesting = 0;
    size_t start = srcCursor;
    if (srcCursor >= BINS.length - 2 ||
        BINS[srcCursor] != '/' || BINS[srcCursor+1] != '+') return start;
    else {
      srcCursor += 2;
      while (srcCursor < BINS.length - 1) {
        if (BINS[srcCursor] == '/' && BINS[srcCursor+1] == '+') {
          nesting += 1;
          srcCursor += 1;
        }
        else if (BINS[srcCursor] == '+' && BINS[srcCursor+1] == '/') {
          if (nesting == 0) {
            break;
          }
          else {
            nesting -= 1;
            srcCursor += 1;
          }
        }
        srcCursor += 1;
        if (srcCursor >= BINS.length - 1) {
          // commment unterminated
	  import std.conv;
          assert (false, "Block comment not terminated at line " ~
		  srcLine.to!string);
        }
      }
      srcCursor += 2;
      return start;
    }
  }
  bool isDefault() {
    if (srcCursor + 7 < BINS.length &&
	BINS[srcCursor .. srcCursor+7] == "default") {
      srcCursor += 7;
      parseSpace();
      return true;
    }
    return false;
  }
  void parseBin(string BinType) {
    size_t srcTag;
    while (true) {
      if (BINS[srcCursor] == '[') {
        ++srcCursor;
        parseSpace();
        srcTag = parseLiteral();
        string min;
        if (BINS[srcTag .. srcCursor] == "$") {
          min = T.max.stringof;
        }
        else if (BINS[srcTag] == '$') {
          min = "N["~BINS[srcTag+1 .. srcCursor]~"]";
        }
        else {
          min = BINS[srcTag .. srcCursor];
        }
        //min = to!T(BINS[srcTag .. srcCursor]);
        parseSpace();
        bool isInclusive = parseRangeType();
        parseSpace();
        srcTag = parseLiteral();
        string max;
        if (BINS[srcTag .. srcCursor] == "$") {
          max = T.max.stringof;
        }
        else if (BINS[srcTag] == '$') {
          max = "N["~BINS[srcTag+1 .. srcCursor]~"]";
        }
        else {
          max = BINS[srcTag .. srcCursor];
        }
        if (!isInclusive) {
          max ~= "-1";
        }
        fill(BinType ~"[$-1].addRange(" ~ min ~ ", " ~ max ~ ");\n");
        parseSpace();
        if (BINS[srcCursor] != ']') {
	  import std.conv;
          assert (false, "range not ended after two elements at line " ~
		  srcLine.to!string);
        }
        ++srcCursor;
        parseSpace();
      }
      else {
        srcTag = parseLiteral();
        string val;
        if (BINS[srcTag .. srcCursor] == "$") {
          val = T.max.stringof;
        }
        else if (BINS[srcTag] == '$') {
          val = "N["~BINS[srcTag+1 .. srcCursor]~"]";
        }
        else {
          val = BINS[srcTag .. srcCursor];
        }
        //makeBins ~= 
        fill(BinType ~ "[$-1].addRange(" ~ val ~ ");\n");
        parseSpace();
      }
      if (BINS[srcCursor] == '}') {
        break;
      }
      parseComma();
    }
  }

  void parseBinOfType(string type) {
    BinType bintype = parseType();
    if (bintype == BinType.SINGLE) {
      auto srcTag = parseName();
      string name = BINS[srcTag .. srcCursor];
      parseSpace();
      parseEqual();
      parseSpace();
      if (isDefault()) {
	if (type == "_ig") {
	  fill("_default = DefaultBin(Type.IGNORE, \"" ~ name ~ "\");");
	}
	else if (type == "_ill") {
	  fill("_default = DefaultBin(Type.ILLEGAL, \"" ~ name ~ "\");");
	}
	else {
	  fill("_default = DefaultBin(Type.BIN, \"" ~ name ~ "\");");
	}
	if (BINS[srcCursor] != ';') {
	  import std.conv;
	  assert (false, "';' expected, not found at line " ~
		  srcLine.to!string);
	}
	++srcCursor;
	parseSpace();
	return;
      }
      else {
	fill(type ~ "_bins ~= Bin!T( \"" ~ name ~ "\");\n");
	parseCurlyOpen();
	parseSpace();
	parseBin(type ~ "_bins");
      }
    }
    else if (bintype == BinType.DYNAMIC) {
      parseSpace();
      auto srcTag = parseName();
      if (type == "_ig") {
        fill(type ~ "_bins ~= Bin!T( \"" ~
	     BINS[srcTag .. srcCursor] ~ "\");\n");	
      }
      else {
        fill(type ~ "_dbins ~= Bin!T( \"" ~
	     BINS[srcTag .. srcCursor] ~ "\");\n");
      }
      parseSpace();
      parseEqual();
      parseSpace();
      parseCurlyOpen();
      parseSpace();
      if (type == "_ig") {
        parseBin(type ~ "_bins");
      }
      else {
        parseBin(type ~ "_dbins");
      }
    }
    else {
      auto srcTag = parseLiteral();
      string arrSize = BINS[srcTag .. srcCursor];
      parseSpace();
      if (BINS[srcCursor] != ']') {
	import std.conv;
        assert (false, "error in writing bins at line "~ srcLine.to!string);
      }
      ++srcCursor;
      parseSpace();
      srcTag = parseName();
      if (type == "_ig") { //no need for arrays in ignore bins
        fill(type ~ "_bins ~= Bin!T( \"" ~
	     BINS[srcTag .. srcCursor] ~ "\");\n");
        // fill(type ~ "_sbinsNum ~= " ~ arrSize ~ "; \n");
      }
      else {
        fill(type ~ "_sbins ~= Bin!T( \"" ~
	     BINS[srcTag .. srcCursor] ~ "\");\n");
        fill(type ~ "_sbinsNum ~= " ~ arrSize ~ "; \n");
      }
      parseSpace();
      parseEqual();
      parseSpace();
      parseCurlyOpen();
      parseSpace();
      if (type == "_ig") {
        parseBin(type ~ "_bins");
      }
      else {
        parseBin(type ~ "_sbins");
      }
    }
    ++srcCursor;
    parseSpace();
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ srcLine.to!string);
    }
    ++srcCursor;
    parseSpace();
  }
  void parseWildcardBins(string type) {
    parseSpace();
    auto srcTag = parseName();
    string name = BINS[srcTag .. srcCursor];
    parseSpace();
    parseEqual();
    parseSpace();
    parseCurlyOpen();
    parseSpace();
    while (srcCursor < BINS.length && BINS[srcCursor] != 'b')
      srcCursor++;
    srcCursor++;
    srcTag = srcCursor;
    /* char [] possible_chars = ['1', '0', '?', 'x', 'z']; */
    while (srcTag < BINS.length &&
	   (BINS[srcTag] == '1' ||
	    BINS[srcTag] == '0' ||
	    BINS[srcTag] == '?' ||
	    BINS[srcTag] == 'x' ||
	    BINS[srcTag] == 'z') ) {
      srcTag++;
    }
    if (srcTag == BINS.length) {
      assert (false, "incomplete statement");
    }
    fill(type ~ "_wildbins ~= WildCardBin!(T)( \"" ~
	 name ~ "\", \"" ~ BINS[srcCursor .. srcTag] ~ "\" );\n"); 
    srcCursor = srcTag;
    parseSpace();
    ++srcCursor;
    parseSpace();
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ srcLine.to!string);
    }
    ++srcCursor;
    parseSpace();
  }
  bool isTypeStatement() {
    if (BINS[srcCursor] == 'o' || BINS[srcCursor] == 't') {
      return true;
    }
    return false;
  }
  void parseTillEqual() {
    size_t srcTag = srcCursor;
    while (BINS[srcCursor] != '=') {
      srcCursor ++;
    }
    srcCursor++;
    fill(BINS[srcTag .. srcCursor]);
    fill("\n");
  }
  void parseOption() {
    parseTillEqual();
    parseSpace();
    size_t srcTag = parseLiteral();
    string val;
    if (BINS[srcTag .. srcCursor] == "$") {
      val = T.max.stringof;
    }
    else if (BINS[srcTag] == '$') {
      val = "N["~BINS[srcTag+1 .. srcCursor]~"]";
    }
    else {
      val = BINS[srcTag .. srcCursor];
    }
    parseSpace();
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ srcLine.to!string);
    }
    fill(val ~ ";");
    srcCursor++;
  }
  string parse() {
    parseSpace();
    while (srcCursor < BINS.length) {
      if (isTypeStatement()) {
	parseOption();
      }
      else {
	if (parseIsWild()) {
	  string type = parseBinDeclaration();
	  parseWildcardBins(type);
	}
	else {
	  string type = parseBinDeclaration();
	  parseBinOfType(type);
	}
      }
      parseSpace();
    }
    return outBuffer;
  }
}

struct WildCardBin(T) {
  string _bin;
  string _name;
  size_t _hits = 0;
  T _ones = 0, _zeroes = 0;
  this(string word, string num) {
    import std.conv;
    _bin = num;
    _name = word;
    int p = 1, i = _bin.length.to!int() - 1;
    // writeln(i);
    while (i >= 0) {
      if (_bin[i] == '1') {
        _ones += p;
      }
      else if (_bin[i] == '0') {
        _zeroes += p;
      }
      p *= 2;
      i -= 1;
    }
  }
  bool checkHit(T val) {
    if ((val & _ones) == _ones && (val & _zeroes) == 0) {
      return true;
    }
    else 
      return false;
  }
}

struct Bin(T)
{
  string _name;
  uint _hits;
  T [] _ranges;
  this(string name) {
    _name = name;
    _hits = 0;
  }
  size_t length () {
    return _ranges.length;
  }
  ref T opIndex(size_t index) {
    return _ranges[index];
  }
  size_t binarySearch (T val) { // lower_bound, first element greater than or equal to

    size_t count = _ranges.length, step;
    size_t first = 0, last = _ranges.length, it;
    while (count > 0) {
      it = first;
      step = count / 2;
      it += step;
      if (_ranges[it] < val) {
        first = ++it;
        count -= step + 1;
      }
      else {
        count = step;
      }
    }
    return first;
  }
  
  bool checkHit(T val) {
    if (val < _ranges[0] || val > _ranges[$-1]) {
      return false;
    }
    size_t idx = binarySearch(val);
    if (idx % 2 == 1 || _ranges[idx] == val) {
      return true;
    }
    return false;
  }
  void addRange (T val) {
    T [] b = [val, val];
    or(b);
  }
  void addRange (T min, T max) {
    T [] b = [min, max];
    or(b);
  }

  bool fallsIn(T x, T [] a, size_t pos) {
    for (size_t i = pos; i < a.length; i++) {
      T elem = a[i];
      if (x < elem) {
        if (i % 2==0) {
          return false;
        }
        return true;
      }
      if (x == elem) {
        return true;
      }
    }
    return false;
  }

  void or (Bin!T other) {
    or(other._ranges);
  }
  T [] opSlice() {
    return _ranges;
  }
  void slice(size_t start, size_t end) {
    assert (start <= end);
    _ranges = _ranges[start .. end];
  }
  void del (size_t n) {
    _ranges.length -= n;
  }
  void opOpAssign(string op)(T r) if (op == "~") {
    _ranges ~= r;
  }
  void opOpAssign(string op)(T [] r) if (op == "~") {
    _ranges ~= r;
  }
  size_t opDollar() const @safe nothrow {
    return _ranges.length;
  }

  void negateBin() {
    if (_ranges[0] == T.min) {
      _ranges = _ranges[1 .. $];
    }
    else {
      this ~= _ranges[$-1];
      for (size_t i = _ranges.length-2; i > 0; --i) {
        _ranges[i] = _ranges[i-1];
      }
      _ranges[0] = T.max;
    }
    if (_ranges[$-1] == T.max) {
      _ranges.length --;
    }
    else {
      this ~= T.min;
    }
    for (size_t i = 0; i < _ranges.length; ++i) {
      if (i % 2 == 0) {
        _ranges[i] ++;
      }
      else {
        _ranges[i] --;
      }
    }
  }
  void or(T [] b) {
    size_t a1 = 0;
    size_t b1 = 0;
    size_t len = _ranges.length;
    while (a1 < len || b1 < b.length) {
      if (a1 >= len) {
        size_t temp = this.length - len;
        if ((temp != 0) && (temp % 2 == 0) &&
	    ((this[$-1] == b[b1]-1) || (this[$-1] == b[b1]))) {
          this.del(1);
          b1 ++;
        }
        while (b1 < b.length) {
          this ~= b[b1];
          b1++;
        }
        continue;
      }
      else if (b1 >= b.length) {
        size_t temp = this.length - len;
        if ((temp != 0) && (temp % 2 == 0) &&
	    ((this[$-1] == this[a1]-1) || (this[$-1] == this[a1]))) {
          this.del(1);
          a1 ++;
        }
        while (a1 < len) {
          this ~= this[a1];
          a1++;
        }
        continue;
      }
      if (this[a1] < b[b1]) {
        if (!fallsIn(this[a1], b, b1)) {
          size_t temp = this.length - len;
          if ((temp != 0) && (temp % 2 == 0) &&
	      ((this[$-1] == this[a1]-1) || (this[$-1] == this[a1]-1))) {
            this.del(1);
          }
          else {
            this ~= this[a1];
          }
        }
        a1++;
      }
      else if (this[a1] > b[b1]) {
        if (!fallsIn(b[b1], this[], a1)) {
          size_t temp = this.length - len;
          if ((temp != 0) && (temp % 2 == 0) &&
	      ((this[$-1] == b[b1] -1) || (this[$-1] == b[b1]))) {
            this.del(1);
          }
          else {
            this ~= b[b1];
          }
        }
        b1++;
      }
      else {
        if ((a1+b1)%2==0) {
          this ~= this[a1];
          a1++;
          b1++;
        }
        else {
          a1++;
          b1++;
        }
      }
    }
    this.slice(len, _ranges.length);
  }

  void and(T [] b) {
    size_t a1 = 0;
    size_t b1 = 0;
    size_t len = _ranges.length;
    while (a1 != len && b1 != b.length) {
      if (this[a1] < b[b1]) {
        if (fallsIn(this[a1], b, b1)) {
          this ~= this[a1];
        }
        a1++;
      }
      else if (this[a1] > b[b1]) {
        if (fallsIn(b[b1], this[], a1)) {
          this ~= b[b1];
        }
        b1++;
      }
      else {
        if ((a1+b1)%2==0) {
          this ~= this[a1];
          a1++;
          b1++;
        }
        else {
          this ~= this[a1];
          this ~= this[a1];
          a1++;
          b1++;
        }
      }
    }
    this.slice(len, _ranges.length);
  }
  string getName() {
    return _name;    
  }
  auto getRanges() {
    return _ranges;
  }

  string describe()
  {
    string s = "Name : " ~ _name ~ "\n";
    foreach (elem; _ranges)
      {
	import std.conv;
	s ~= to!string(elem) ~ ", ";
      }
    s ~= "\n";
    return s;
  }
  size_t count() {
    size_t c = 0;
    for (size_t i = 0; i < _ranges.length - 1; i += 2) {
      c += (1uL + _ranges[i+1]) - _ranges[i];
    }
    return c;
  }
}
enum Type: ubyte {IGNORE, ILLEGAL, BIN};
struct DefaultBin {
  Type _type = Type.IGNORE;
  bool _curr_hit;
  string _name = "";
  uint _hits = 0;
  this (Type t, string n) {
    _type = t;
    _name = n;
  }
}

interface coverInterface {
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

string makeArray(size_t len, string type,string name) {
  string s = type ~ " ";
  for (int i = 0; i < len; i++) {
    s ~= "[]"; 
  }
  s ~= " " ~ name ~ ";";
  return s;
}

string crossSampleHelper(int n) {
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

string arrayInitialising(string name, int n) {
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

string sampleCoverpoints(int n) {
  import std.conv;
  string s;
  for (int i = 0; i < n; i++) {
    s ~= "if (isIntegral!(typeof(N[" ~ i.to!string() ~ "])))";
    s ~= "coverPoints[" ~ i.to!string() ~ "].sample();\n";
  }
  return s;
}

class Cross ( N... ): coverInterface {
  import std.traits: isIntegral;
  enum size_t len = N.length;
  ulong [] bincnts;
  mixin(makeArray(len, "uint", "_hits"));
  mixin(makeArray(len, "bool", "_curr_hits"));
  coverInterface [] coverPoints;
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
    mixin(arrayInitialising("_hits", len));
    mixin(arrayInitialising("_curr_hits", len));
  }
  override void sample() {
    mixin(arrayInitialising("_curr_hits", len));
    mixin(sampleCoverpoints(len));
    mixin(crossSampleHelper(N.length));
  }
  override double get_coverage() {
    return 0;
  }
  override double get_curr_coverage() {
    return 0;
  }
  override void start() {

  }
  override void stop() {

  }
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

abstract class CoverPoint(T, string BINS="", N...) : coverInterface {
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
    mixin(doParse!T(BINS));
    // }
    // else {
    //   import std.conv;
    //   mixin(doParse!T("bins [64] a = {[" ~ T.min.to!string() ~ ":" ~ T.max.to!string() ~ "]};"));
    // }

    procDyanamicBins(_bins,_dbins);
    procDyanamicBins(_ill_bins,_ill_dbins);
    procStaticBins(_bins,_sbins,_sbinsNum);
    procStaticBins(_ill_bins,_ill_sbins,_ill_sbinsNum);
    procIgnoreBins();
    _curr_hits.length = _bins.length; 
    _curr_wild_hits.length = _wildbins.length;
    if (_bins.length == 0 && _ill_bins.length == 0) {
      import std.conv;
      mixin(doParse!T("bins [64] a = {[" ~ T.min.to!string() ~
		      ":" ~ T.max.to!string() ~ "]};"));
      procStaticBins(_bins,_sbins,_sbinsNum);
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
  override void start() {

  }
  override void stop() {

  }
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

struct CoverGroupParser {
  size_t srcCursor = 0;
  size_t srcLine = 0;
  string S;
  string outBuffer = "";
  void fill(in string source) {
    outBuffer ~= source;
  }
  this(string s) {
    S = s;
  }
  size_t parseName() {
    auto start = srcCursor;
    while (S[srcCursor] != ';' &&
	   S[srcCursor] != ':' &&
	   S[srcCursor] != ' ' &&
	   S[srcCursor] != '=' &&
	   S[srcCursor] != '\n'&&
	   S[srcCursor] != '\t' ) {
      ++srcCursor;
    }
    return start;
  }
  bool parseCoverPointDecl() {
    if (S.length >= srcCursor+10 &&
	S[srcCursor..srcCursor+10] == "coverpoint") {
      srcCursor += 10;
      return true;
    }
    return false;
  }
  bool parseCrossDecl() {
    if (S.length >= srcCursor+5 &&
	S[srcCursor..srcCursor+5] == "cross") {
      srcCursor += 5;
      return true;
    }
    return false;
  }
  size_t parseLineComment() {
    size_t start = srcCursor;
    if (srcCursor >= S.length - 2 ||
        S[srcCursor] != '/' || S[srcCursor+1] != '/') return start;
    else {
      srcCursor += 2;
      while (srcCursor < S.length) {
        if (S[srcCursor] == '\n') {
          break;
        }
        else {
          if (srcCursor == S.length) {
	    import std.conv;
            // commment unterminated
            assert (false, "Line comment not terminated at line " ~
		    srcLine.to!string);
          }
        }
        srcCursor += 1;
      }
      srcCursor += 1;
      return start;
    }
  }

  size_t parseBlockComment() {
    size_t start = srcCursor;
    if (srcCursor >= S.length - 2 ||
        S[srcCursor] != '/' || S[srcCursor+1] != '*') return start;
    else {
      srcCursor += 2;
      while (srcCursor < S.length - 1) {
        if (S[srcCursor] == '*' && S[srcCursor+1] == '/') {
          break;
        }
        else {
          if (srcCursor == S.length - 1) {
	    import std.conv;
            // commment unterminated
            assert (false, "Block comment not terminated at line " ~
		    srcLine.to!string);
          }
        }
        srcCursor += 1;
      }
      srcCursor += 2;
      return start;
    }
  }
  size_t parseNestedComment() {
    size_t nesting = 0;
    size_t start = srcCursor;
    if (srcCursor >= S.length - 2 ||
        S[srcCursor] != '/' || S[srcCursor+1] != '+') return start;
    else {
      srcCursor += 2;
      while (srcCursor < S.length - 1) {
        if (S[srcCursor] == '/' && S[srcCursor+1] == '+') {
          nesting += 1;
          srcCursor += 1;
        }
        else if (S[srcCursor] == '+' && S[srcCursor+1] == '/') {
          if (nesting == 0) {
            break;
          }
          else {
            nesting -= 1;
            srcCursor += 1;
          }
        }
        srcCursor += 1;
        if (srcCursor >= S.length - 1) {
	  import std.conv;
          // commment unterminated
          assert (false, "Block comment not terminated at line " ~
		  srcLine.to!string);
        }
      }
      srcCursor += 2;
      return start;
    }
  }
  size_t parseComment() {
    auto start = srcCursor;
    while (srcCursor < S.length) {
      auto srcTag = srcCursor;
      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      if (srcCursor > srcTag) {
        continue;
      }
      else {
        break;
      }
    }
    return start;
  }
  size_t parseWhiteSpace() {
    auto start = srcCursor;
    while (srcCursor < S.length) {
      auto c = S[srcCursor];
      // eat up whitespaces
      if (c is '\n') ++srcLine;
      if (c is ' ' || c is '\n' || c is '\t' || c is '\r' || c is '\f') {
        ++srcCursor;
        continue;
      }
      else {
        break;
      }
    }
    return start;
  }

  size_t parseSpace() {
    size_t start = srcCursor;
    while (srcCursor < S.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();
      
      
      if (srcCursor > srcTag) {
        continue;
      }
      else {
        break;
      }
    }
    return start;
  }

  size_t nextEndCurlyBrace() {
    size_t start = srcCursor;
    int bracketCount = 0;
    while (srcCursor < S.length && bracketCount >= 0) {
      if (S[srcCursor] == '{') {
	bracketCount ++;
      }
      else if (S[srcCursor] == '}') {
	bracketCount --;
      }
      srcCursor ++;
    }
    if (srcCursor == S.length) {
      import std.conv;
      assert (false, "unterminated ' {' at line " ~ srcLine.to!string);
    }
    return start;
  }
  
  string parse() {    
    parseSpace();
    int coverpointNumber = 0;
    string [] cp_names;
    while (srcCursor < S.length) {
      string cp_name;
      if (parseCoverPointDecl()) {
	parseSpace();
        auto srcTag = parseName();
	string name = S[srcTag .. srcCursor];
	parseSpace();
	string coverpointName = "";
	if (S[srcCursor] == '{') {
	  // goto next }
	  srcCursor ++;
	  srcTag = nextEndCurlyBrace();
	  coverpointName = "CoverPoint!(typeof(" ~ name ~
	    "), \" " ~ S[srcTag .. srcCursor-1] ~ "\")";
	}
	else {
	  if (S[srcCursor] != ';') {
	    import std.conv;
	    assert (false, "expected ; at line " ~ srcLine.to!string);
	  }
	  srcCursor ++;
	  coverpointName = "CoverPoint!(typeof(" ~ name ~ "))";
	}
	if (cp_names.length == coverpointNumber) {
	  import std.conv;
	  cp_name = "_esdl__coverpoint_" ~ coverpointNumber.to!string;
	  cp_names ~= cp_name;
	}
	outBuffer ~= "alias " ~ cp_name ~ "_class = " ~
	  coverpointName ~ ";\n";
	outBuffer ~= cp_name ~ "_class " ~ cp_name ~ ";\n";
	outBuffer ~= "class " ~ cp_name ~ "_override : " ~
	  cp_name ~ "_class { \n override _esdl__T _esdl__t() { return " ~ name ~ "; }\n }\n";
      }
      else if (parseCrossDecl()) { // TODO
	
      }
      else {
	if (cp_names.length > coverpointNumber) {
	  import std.conv;
	  assert (false, "expected 'coverpoint' or 'cross'at line " ~
		  srcLine.to!string);
	}
        auto srcTag = parseName();
	string name = S[srcTag .. srcCursor];
	parseSpace();
	if (S[srcCursor] != ':') {
	  import std.conv;
	  assert (false, "expected : at line " ~ srcLine.to!string);
	}
	cp_names ~= name;
	srcCursor++;
	parseSpace();
	continue;
      }
      parseSpace();
      coverpointNumber ++;
    }
    outBuffer ~= "this () { \n";
    foreach (cp_name; cp_names) {
      outBuffer ~= cp_name ~ " = new " ~ cp_name ~
	"_override();\n";
    }
    outBuffer ~= "}\n";
    outBuffer ~= "void sample() { \n";
    foreach (cp_name; cp_names) {
      outBuffer ~= cp_name ~ ".sample();";
    }
    outBuffer ~= "}\n";
    outBuffer ~= "double get_coverage() {
      double total = 0;
      size_t weightSum = 0;\n";
    foreach (cp_name; cp_names) {
      outBuffer ~= "total += " ~ cp_name ~ ".get_coverage() * " ~
	cp_name ~ ".get_weight();\n";
      outBuffer ~= "weightSum += " ~ cp_name ~ ".get_weight();\n";
    }
    outBuffer ~= "
    return total/weightSum; }\n";
    return outBuffer;
  }
}

string _esdl__parseCoverGroupString(string S) {
  CoverGroupParser parser = CoverGroupParser(S);
  return parser.parse();
}

mixin template CoverGroup (string S) {
  class covergroup_name { // put name of covergroup instead
    mixin(_esdl__parseCoverGroupString(S));
  }
}
