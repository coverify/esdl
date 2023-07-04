// import esdl.rand;
// import esdl.data.bvec;

module esdl.cover.bins;
import esdl.data.vector: Vector;

static string doParse(T)(string Bins) {
  parser!T Parser = parser!T(Bins);
  Parser.parse();
  Parser.setUp();
  Parser.parse();
  
  return Parser.buffer();
}

struct parser (T)
{
  bool druRun = true;
  size_t bufLen = 0;
  
  enum BinType: byte {SINGLE, DYNAMIC, STATIC};
  size_t srcCursor = 0;
  size_t srcLine = 0;
  string BINS;

  Vector!(char, "outBuffer") outBuffer;
  string buffer() {return cast(string) outBuffer[];}

  this(string bins) {
    BINS = bins;
  }

  void setUp() {
    outBuffer.reserve(bufLen);
    srcCursor = 0;
    srcLine = 0;
    druRun = false;
  }

  void fill(T...)(T strs) {
    foreach (str; strs) {
      if (druRun) bufLen += str.length;
      else outBuffer ~= str;
    }
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
  void parseSquareOpen() {
    if (BINS[srcCursor] != '[') {
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
          min = "N[" ~ BINS[srcTag+1 .. srcCursor] ~ "]";
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
          max = "N[" ~ BINS[srcTag+1 .. srcCursor] ~ "]";
        }
        else {
          max = BINS[srcTag .. srcCursor];
        }
        if (!isInclusive) {
          max ~= "-1";
        }
        fill(BinType, "[$-1].addRange(", min, ", ", max, ");\n");
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
          val = "N[" ~ BINS[srcTag+1 .. srcCursor] ~ "]";
        }
        else {
          val = BINS[srcTag .. srcCursor];
        }
        //makeBins ~= 
        fill(BinType, "[$-1].addRange(", val, ");\n");
        parseSpace();
      }
      if (BINS[srcCursor] == ']') {
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
	  fill("_default = DefaultBin(Type.IGNORE, \"", name, "\");");
	}
	else if (type == "_ill") {
	  fill("_default = DefaultBin(Type.ILLEGAL, \"", name, "\");");
	}
	else {
	  fill("_default = DefaultBin(Type.BIN, \"", name, "\");");
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
      else if (BINS[srcCursor] == '[') {
	fill(type, "_bins ~= new Bin!T( \"", name, "\");\n");
	parseSquareOpen();
	parseSpace();
	parseBin(type ~ "_bins");
	fill(type, "_bins[$-1].procRanges();\n");
      }
      else {
	size_t markParen;
	size_t markLastParen;
	srcTag = srcCursor;
	while (BINS[srcCursor] != ';') {
	  size_t srcMark = srcCursor;
	  parseSpace();
	  if (srcMark == srcCursor) {
	    if (BINS[srcCursor] != ';') {
	      if (srcCursor < BINS.length) {
		markParen = srcCursor;
		if (BINS[srcCursor] == '(') {
		  srcCursor += 1;
		  parseSpace();
		  if (BINS[srcCursor] == ')') { // empty parens
		    srcCursor += 1;
		    markLastParen = markParen;
		  }
		}
		else {
		  srcCursor += 1;
		}
	      }
	      else {
		import std.conv: to;
		assert (false, "expected ; at line " ~ srcLine.to!string);
	      }
	    }
	  }
	}
	srcCursor += 1;
      }
    }
    else if (bintype == BinType.DYNAMIC) {
      parseSpace();
      auto srcTag = parseName();
      if (type == "_ig") {
        fill(type, "_bins ~= new Bin!T( \"",
	     BINS[srcTag .. srcCursor], "\");\n");	
      }
      else {
        fill(type, "_dbins ~= new Bin!T( \"",
	     BINS[srcTag .. srcCursor], "\");\n");
      }
      parseSpace();
      parseEqual();
      parseSpace();
      parseSquareOpen();
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
        assert (false, "error in writing bins at line " ~ srcLine.to!string);
      }
      ++srcCursor;
      parseSpace();
      srcTag = parseName();
      if (type == "_ig") { //no need for arrays in ignore bins
        fill(type, "_bins ~= new Bin!T( \"",
	     BINS[srcTag .. srcCursor], "\");\n");
        // fill(type, "_sbinsNum,= ", arrSize, "; \n");
      }
      else {
        fill(type, "_sbins ~= new Bin!T( \"",
	     BINS[srcTag .. srcCursor], "\");\n");
        fill(type, "_sbinsNum ~= ", arrSize, "; \n");
      }
      parseSpace();
      parseEqual();
      parseSpace();
      parseSquareOpen();
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
    parseSquareOpen();
    parseSpace();
    if (srcCursor > BINS.length - 2 || BINS[srcCursor..srcCursor+2] != "0b")
      assert (false, "wildcard bin specification must start with 0b");
    srcCursor += 2;

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
    fill(type, "_wildbins ~= WildCardBin!(T)( \"",
	 name, "\", \"", BINS[srcCursor .. srcTag], "\" );\n"); 
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
    fill(BINS[srcTag .. srcCursor], "\n");
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
      val = "N[" ~ BINS[srcTag+1 .. srcCursor] ~ "]";
    }
    else {
      val = BINS[srcTag .. srcCursor];
    }
    parseSpace();
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ srcLine.to!string);
    }
    fill(val, ";");
    srcCursor++;
  }
  
  void parse() {
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
  }
}

struct WildCardBin(T)
{
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

interface BinIntf(T)
{
  void sample(T val);
  double getCoverage();
  
  string getName();
  string describe();
}


class Bin(T): BinIntf!T
{
  // import std.typecons: Tuple, tuple;

  // alias TRange = Tuple!(T, "min", T, "max");

  struct BinRange(T)
  {
    size_t _count;	  // how much the previous ranges have covered

    T _min;
    T _max;

    int opCmp(ref const BinRange!T other) const {
      if (this._min > other._min) {
	return +1;
      }
      else if (this._min < other._min) {
	return -1;
      }
      else if (this._max == other._max) {
	return 0;
      }
      else if (other._max == T.min ||
	       other._max > this._max) {
	return -1;
      }
      else return +1;
    }
  }
  
  string _name;
  BinRange!T[] _ranges;
  
  uint[] _hits;
  
  this(string name) {
    _name = name;
  }
  
  void addRange (T val) {
    this.addRange(val, cast(T) (val+1));

    // T [] b = [val, val];
    // or(b);
  }

  void addRange (T min, T max) {
    _ranges ~= BinRange!T(0L, min, max);
    // T [] b = [min, max];
    // or(b);
  }

  void procRanges() {
    import std.stdio: writeln;
    import std.algorithm.sorting: sort;
    sort(_ranges);
    writeln(_ranges);
  }
  
  string getName() {
    return _name;    
  }
  auto getRanges() {
    return _ranges;
  }

  void sample(T val) { 
  }

  double getCoverage() {
    return 0.0;
  }

  string describe()
  {
    string s = "Name : " ~ _name ~ "\n";
    // foreach (elem; _ranges)
    //   {
    // 	import std.conv;
    // 	s ~= to!string(elem) ~ ", ";
    //   }
    s ~= "\n";
    return s;
  }
}

enum Type: ubyte {IGNORE, ILLEGAL, BIN};

struct DefaultBin
{
  Type _type = Type.IGNORE;
  bool _curr_hit;
  string _name = "";
  uint _hits = 0;
  this (Type t, string n) {
    _type = t;
    _name = n;
  }
}

