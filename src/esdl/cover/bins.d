// import esdl.rand;
// import esdl.data.bvec;

module esdl.cover.bins;
import esdl.data.vector: Vector;
import esdl.data.bvec: isBitVector;
import std.traits: isIntegral;
import std.conv: parse;

static string doParse(T)(string Bins) {
  EsdlBinsParser!T binsParser = EsdlBinsParser!T(Bins);
  binsParser.parseAllBins();
  binsParser.setUp();
  binsParser.parseAllBins();
  
  return binsParser.buffer();
}

// A context strutcture only to be used while parsing
struct ParsedBin(T)
{
  string _name;
  
  bool _isIllegal;
  bool _isIgnore;
  bool _isTransition;
  bool _isWildcard;

  bool _isArray;

  // _arrayLen != 0 if static array
  uint _arrayLen;

  void checkAttribs() {
    if (_isIllegal && _isIgnore)
      assert (false, "A bin can not have illegal as well as ignore attributes");
    if (_isIgnore && _isWildcard)
      assert (false, "A bin can not have ignore as well as wildcard attributes");
  }
}

struct EsdlBinsParser (T)
{
  bool dryRun = true;
  size_t ctrLen = 0;
  size_t declLen = 0;
  
  enum BinType: byte {SINGLE, DYNAMIC, STATIC};
  size_t srcCursor = 0;
  size_t srcLine = 0;
  string BINS;

  size_t ctrCursor;
  size_t declCursor;
  
  char[] outBuffer;
  string buffer() {return cast(string) outBuffer;}

  this(string bins) {
    BINS = bins;
  }

  void setUp() {
    outBuffer.length =ctrLen+declLen;
    srcCursor = 0;
    srcLine = 0;
    declCursor = 0;
    ctrCursor = declLen;
    dryRun = false;
  }

  void fillCtr(T...)(T strs) {
    foreach (str; strs) {
      if (dryRun) ctrLen += str.length;
      else {
	size_t newCursor = ctrCursor+str.length;
	outBuffer[ctrCursor..newCursor] = str;
	ctrCursor = newCursor;
      }
    }
  }
  
  void fillDecl(T...)(T strs) {
    foreach (str; strs) {
      if (dryRun) declLen += str.length;
      else {
	size_t newCursor = declCursor+str.length;
	outBuffer[declCursor..newCursor] = str;
	declCursor = newCursor;
      }
    }
  }
  
  // void fillDecl(T...)(T strs) {
  //   foreach (str; strs) {
  //     if (dryRun) declLen += str.length;
  //     else outBuffer ~= str;
  //   }
  // }
  
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

  size_t parseIntLiteral(bool isPositive=false) {
    size_t start = srcCursor;
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
    if (BINS[start] == '-' && isPositive) {
      assert(false, "Expecting only positive number, found negative: " ~ BINS[start..srcCursor]);
    }
    return start;
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

  bool checkValue(string val) {
    size_t maxbits = 0;
    size_t bitcount;
    string pval = val;
    if (val[0] == '-') pval = val[1..$];
    static if (isBitVector!T) maxbits = T.SIZE;
    else maxbits = T.sizeof * 8;
    if (pval.length >=2 &&
	(pval[0..2] == "0x" || pval[0..2] == "0X")) {
      bool started = false;
      foreach (d; pval[2..$]) {
	if (started is false) {
	  if (d == '0' || d == '_') continue;
	  else {
	    started = true;
	    if (d == '1') bitcount = 1;
	    else if (d == '2' || d == '3') bitcount = 2;
	    else if (d == '4' || d == '5' ||
		     d == '6' || d == '7') bitcount = 3;
	    else bitcount = 4;
	  }
	}
	else {
	  if (d == '_') continue;
	  else bitcount += 4;
	}
      }
      if (bitcount > maxbits) assert (false, "Value " ~ val ~ " is not be of type " ~ T.stringof);
      else return true;
    }
    if (pval.length >=2 &&
	(pval[0..2] == "0b" || pval[0..2] == "0B")) {
      bool started = false;
      foreach (d; pval[2..$]) {
	if (started is false) {
	  if (d == '0' || d == '_') continue;
	  else {
	    started = true;
	    bitcount = 1;
	  }
	}
	else {
	  if (d == '_') continue;
	  else bitcount += 1;
	}
      }
      if (bitcount > maxbits) assert (false, "Value " ~ val ~ " is not be of type " ~ T.stringof);
    }
    else if (pval[0] <= '9' && pval[0] >= '0') {
      string strval = pval.dup;
      ulong intVal = parse!(ulong, string)(strval, 10);
      assert (cast(T) intVal == intVal, "Value " ~ pval ~ " can not be of type " ~ T.stringof);
    }
    return true;
  }
  
  void parseNamedBin(string binName) {
    size_t srcTag;
    while (true) {
      if (BINS[srcCursor] == '[') {
        string min;
        string max;
        ++srcCursor;
        parseSpace();
	if (BINS[srcCursor] == '$') {
          min = T.max.stringof;
	  srcCursor += 1;
	}
	else {
	  srcTag = parseIntLiteral();
          min = BINS[srcTag .. srcCursor];
        }
        //min = to!T(BINS[srcTag .. srcCursor]);
        parseSpace();
        bool isInclusive = parseRangeType();
        parseSpace();
	if (BINS[srcCursor] == '$') {
          max = T.max.stringof;
	  srcCursor += 1;
	}
	else {
	  srcTag = parseIntLiteral();
          max = BINS[srcTag .. srcCursor];
        }
	checkValue(min);
	checkValue(max);
	static if (isBitVector!T) {
	  if (!isInclusive) {
	    fillCtr(binName, ".addRange(", min, ".to!T, (", max, "-1).to!T);\n");
	  }
	  else {
	    fillCtr(binName, ".addRange(", min, ".to!T, ", max, ".to!T);\n");
	  }
	}
	else {
	  if (!isInclusive) {
	    fillCtr(binName, ".addRange(cast(T) ", min, ", cast(T) (", max, "-1));\n");
	  }
	  else {
	    fillCtr(binName, ".addRange(cast(T) ", min, ", cast(T) ", max, ");\n");
	  }
	}
        parseSpace();
        if (BINS[srcCursor] != ']') {
	  import std.conv;
          assert (false, "range not ended after two elements at line " ~
		  srcLine.to!string);
        }
        srcCursor += 1;
        parseSpace();
      }
      else {
        string val;
	if (BINS[srcCursor] == '$') {
          val = T.max.stringof;
	  srcCursor += 1;
	}
	else {
	  srcTag = parseIntLiteral();
          val = BINS[srcTag .. srcCursor];
        }
	checkValue(val);
	static if (isBitVector!T) {
	  fillCtr(binName, ".addElem(" ~ val ~ ".to!T);\n");
	}
	else {
	  fillCtr(binName, ".addElem(cast(T) " ~ val ~ ");\n");
	}	  
        parseSpace();
      }
      if (BINS[srcCursor] == ']') {
        break;
      }
      parseComma();
    }
  }

  void parseBinOfType() {
    BinType bintype = parseType();
    if (bintype == BinType.SINGLE) {
      auto srcTag = parseName();
      string name = BINS[srcTag .. srcCursor];
      parseSpace();
      parseEqual();
      parseSpace();
      if (isDefault()) {
	fillCtr("_default = DefaultBin(Type.BIN, \"", name, "\");");

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
	string binName = name;
	fillDecl("EsdlRangeBin!T ", binName, ";\n");
	fillCtr(binName, " = new EsdlRangeBin!T( \"", name, "\");\n");
	fillCtr("_bins ~= ", binName, ";\n");
	parseSquareOpen();
	parseSpace();
	parseNamedBin(binName);
	// fillCtr(type, "_bins[$-1].processBin();\n");
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
      fillCtr("_bins ~= new EsdlRangeBin!T( \"",
	      BINS[srcTag .. srcCursor], "\");\n");
      parseSpace();
      parseEqual();
      parseSpace();
      parseSquareOpen();
      parseSpace();
      // if (type == "_ig") {
      //   parseBin(type ~ "_bins");
      // }
      // else {
      //   parseBin(type ~ "_dbins");
      // }
    }
    else {
      auto srcTag = parseIntLiteral();
      string arrSize = BINS[srcTag .. srcCursor];
      string binName;
      parseSpace();
      if (BINS[srcCursor] != ']') {
	import std.conv;
        assert (false, "error in writing bins at line " ~ srcLine.to!string);
      }
      ++srcCursor;
      parseSpace();
      srcTag = parseName();
      binName = BINS[srcTag .. srcCursor];
      fillDecl("EsdlRangeBin!T ", binName, ";\n");
      fillCtr(binName, " = new EsdlRangeBin!T( \"",
	      binName, "\");\n");
      fillCtr("_bins ~= ", binName, ";\n");
      // fillCtr(type, "_sbinsNum ~= ", arrSize, "; \n");
      parseSpace();
      parseEqual();
      parseSpace();
      parseSquareOpen();
      parseSpace();
      parseNamedBin(binName);
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

  void parseWildcardBins(string name) {
    parseSquareOpen();
    parseSpace();
    if (srcCursor > BINS.length - 2 || BINS[srcCursor] != '"')
      assert (false, "wildcard bin specification must start with '\"'");
    srcCursor += 2;

    size_t srcTag = srcCursor;
    /* char [] possible_chars = ['1', '0', '?', 'x', 'z']; */
    while (srcCursor < BINS.length &&
	   (BINS[srcCursor] == '1' ||
	    BINS[srcCursor] == '0' ||
	    BINS[srcCursor] == '_' ||
	    BINS[srcCursor] == '?' ||
	    BINS[srcCursor] == 'x' ||
	    BINS[srcCursor] == 'X' ||
	    BINS[srcCursor] == 'z' ||
	    BINS[srcCursor] == 'Z') ) {
      srcCursor++;
    }
    if (BINS[srcCursor] != '"') {
      assert (false, "Wildcard Bin should be a string");
    }
    fillCtr("_bins ~= new WildcardBin!(T)( \"",
	    name, "\", \"", BINS[srcTag .. srcCursor], "\" );\n"); 
    srcCursor += 1;
    parseSpace();
    if (BINS[srcCursor] != ']') {
      import std.conv;
      assert (false, "']' expected, not found at line " ~ srcLine.to!string);
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
    fillCtr(BINS[srcTag .. srcCursor], "\n");
  }

  void parseOption() {
    string val;
    parseTillEqual();
    parseSpace();
    if (BINS[srcCursor] == '$') {
      val = T.max.stringof;
      srcCursor += 1;
    }
    else {
      size_t srcTag = parseIntLiteral();
      val = BINS[srcTag .. srcCursor];
    }
    parseSpace();
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ srcLine.to!string);
    }
    fillCtr(val, ";");
    srcCursor++;
  }
  
  void parseAllBins() {
    import std.conv: to;
    uint binsCount;
    fillCtr("this () {\n");
    parseSpace();
    while (srcCursor < BINS.length) {
      if (isTypeStatement()) {
	parseOption();
      }
      else {
	binsCount += 1;
	parseABin();
      }
      parseSpace();
    }
    if (binsCount == 0) {
      // Add default bin
      fillDecl("EsdlRangeBin!T _esdl__bin__esdl__defaultBin;\n");
      fillCtr("_esdl__bin__esdl__defaultBin = new EsdlRangeBin!T( q{_esdl__defaultBin});\n");
      fillCtr("_bins ~= _esdl__bin__esdl__defaultBin;\n");
      // fillCtr("_sbinsNum ~= 64;\n");
      fillCtr("_esdl__bin__esdl__defaultBin.addRange(", T.min.to!string(), ", ", T.max.to!string(), ");\n");
    }
    fillCtr("this._esdl__initBins();\n}\n");
  }

  size_t parseIdentifier() {
    size_t start = srcCursor;
    if (srcCursor < BINS.length) {
      char c = BINS[srcCursor];
      if ((c >= 'A' && c <= 'Z') ||
	  (c >= 'a' && c <= 'z') ||
	  (c == '_')) {
	++srcCursor;
      }
      else {
	return start;
      }
    }
    while (srcCursor < BINS.length) {
      char c = BINS[srcCursor];
      if ((c >= 'A' && c <= 'Z') ||
	  (c >= 'a' && c <= 'z') ||
	  (c >= '0' && c <= '9') ||
	  c == '_') {
	++srcCursor;
      }
      else {
	break;
      }
    }
    return start;
  }

  string parseBinAttrib() {
    srcCursor += 1;
    size_t srcTag = parseIdentifier();
    return BINS[srcTag..srcCursor];
  }

  void parseBinAttribs(ref ParsedBin!T bin) {
    while (BINS[srcCursor] == '@') {
      string attr = parseBinAttrib();
      if (attr == "ignore") bin._isIgnore = true;
      else if (attr == "illegal") bin._isIllegal = true;
      else if (attr == "wildcard") bin._isWildcard = true;
      else if (attr == "transition") bin._isTransition = true;
      else assert (false, "Unknown Attribute: @" ~ attr);
      parseSpace();
    }
    bin.checkAttribs();
  }
  
  void parseABin() {
    ParsedBin!T bin;
    parseBinAttribs(bin);
    parseSpace();

    if (srcCursor + 4 < BINS.length &&
	BINS[srcCursor .. srcCursor+4] == "bins") {
      srcCursor += 4;
      parseSpace();
    }
    else {
      auto srcTag = parseIdentifier();
      if (srcTag != srcCursor)
	assert (false, "Expected keyword 'bins', found " ~
		BINS[srcTag..srcCursor] ~ " instead");
      else 
	assert (false, "Expected keyword 'bins' not found");
    }
    if (BINS[srcCursor] == '[') {
      bin._isArray = true;
      srcCursor += 1;
      parseSpace();
      parseIntLiteral(true);
    }
    
    if (bin._isWildcard) {
      parseSpace();
      auto srcTag = parseName();
      string name = BINS[srcTag .. srcCursor];
      parseSpace();
      parseEqual();
      parseSpace();
      parseWildcardBins(name);
    }
    else {
      parseBinOfType();
    }
  }

  

}


class WildcardBin(T): EsdlBaseBin!T
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
  override string getName() {
    return _name;    
  }

  override void sample(T val) { }

  override double getCoverage() {
    return 0.0;
  }

  override string describe()
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

enum EsdlBinAttr: uint {
  ILLEGAL        = 0b000001,
  IGNORE         = 0b000010,
  WILDCARD       = 0b000100,
  TRANSITION     = 0b001000,
  DYNAMICARRAY   = 0b010000,
  STATICARRAY    = 0b100000
}

abstract class EsdlBaseBin(T)
{
  uint _attributes;

  void addAttribute(EsdlBinAttr attr) {
    _attributes |= attr;
  }
  
  void sample(T val);
  double getCoverage();
  
  string getName();
  string describe();

  bool isIllegal() {
    return (EsdlBinAttr.ILLEGAL & _attributes) != 0;
  }

  bool isIgnore() {
    return (EsdlBinAttr.IGNORE & _attributes) != 0;
  }

  bool isWildcard() {
    return (EsdlBinAttr.WILDCARD & _attributes) != 0;
  }

  bool isTransition() {
    return (EsdlBinAttr.TRANSITION & _attributes) != 0;
  }

  bool isDynamicArray() {
    return (EsdlBinAttr.DYNAMICARRAY & _attributes) != 0;
  }

  bool isStaticArray() {
    return (EsdlBinAttr.STATICARRAY & _attributes) != 0;
  }

  bool isArray() {
    return ((EsdlBinAttr.STATICARRAY & _attributes) |
	    (EsdlBinAttr.DYNAMICARRAY & _attributes)) != 0;
  }
}


class EsdlRangeBin(T): EsdlBaseBin!T
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
  
  void addElem (T val) {
    this.addRange(val, cast(T) (val+1));
    // T [] b = [val, val];
    // or(b);
  }

  void addRange (T min, T max) {
    _ranges ~= BinRange!T(0L, min, max);
    // T [] b = [min, max];
    // or(b);
  }

  void processBin() {
    import std.stdio: writeln;
    import std.algorithm.sorting: sort;
    sort(_ranges);
    writeln(_ranges);
  }
  
  override string getName() {
    return _name;    
  }
  auto getRanges() {
    return _ranges;
  }

  override void sample(T val) { 
  }

  override double getCoverage() {
    return 0.0;
  }

  override string describe()
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

