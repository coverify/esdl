// import esdl.rand;
// import esdl.data.bvec;

module esdl.cover.bins;
import esdl.data.vector: Vector;
import esdl.data.bvec: isBitVector, ulvec;
import std.traits: isIntegral;
import std.conv: parse;
import esdl.cover.wild;

static string doParse(T)(string Bins) {
  EsdlBinsParser!T binsParser = EsdlBinsParser!T(Bins);
  binsParser.parseAllBins();
  binsParser.setUp();
  binsParser.parseAllBins();
  
  return binsParser.buffer();
}

// A context strutcture only to be used while parsing
struct EsdlBinsParser (T)
{
  struct ParsedBin
  {
    string _name;
  
    bool _isIllegal;
    bool _isIgnore;
    bool _isTransition;
    bool _isWildcard;

    bool _isArray;

    size_t _arrayDim;

    string _filter;

    // _arrayLen != 0 if static array
    string _arrayLen;

    void checkAttribs() {
      if (_isIllegal && _isIgnore)
	assert (false, "A bin can not have illegal as well as ignore attributes");
      if (_isIgnore && _isWildcard)
	assert (false, "A bin can not have ignore as well as wildcard attributes");
    }
  }

  bool dryRun = true;
  size_t ctrLen = 0;		// constructor
  size_t declLen = 0;		// declarations
  
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

  void procBinOfType(ref ParsedBin bin) {
    parseSpace();
    if (BINS[srcCursor] == '[') {
      if (bin._isWildcard)
	procWildcardBins(bin);
      else
	procRangeBins(bin);
    }
    else if (srcCursor + 7 < BINS.length &&
	     BINS[srcCursor .. srcCursor+7] == "default")
      procDefaultBins(bin);
    else {
      procFunction(bin);
    }
    if (bin._filter != "") {
      fillCtr(bin._name, ".addFilter(&" ~ bin._filter ~ ");\n");
    }

    if (bin._isIllegal) {
      // fillCtr(bin._name, ".markIllegal();\n");
      fillCtr("_esdl__illBins ~= ", bin._name, ";\n");
    }
    else if (bin._isIgnore) {
      // fillCtr(bin._name, ".markIgnore();\n");
      fillCtr("_esdl__ignBins ~= ", bin._name, ";\n");
    }
    else {
      fillCtr("_esdl__cvrBins ~= ", bin._name, ";\n");
    }
  }

  bool checkWildcard(string val) {
    import std.conv: to;
    size_t maxbits;
    size_t bitcount;
    static if (isBitVector!T) maxbits = T.SIZE;
    else maxbits = T.sizeof * 8;
    foreach (d; val[1..$-1]) {
      if (d == '_') continue;
      else bitcount += 1;
    }
    if (bitcount != maxbits) assert (false, "Wildcard " ~ val ~
				     " should match exact number of bits: " ~
				     maxbits.to!string);
    return true;
  }

  bool checkValue(string val) {
    size_t maxbits = 0;
    size_t bitcount;
    bool negative = false;
    string pval = val;
    if (val[0] == '-') {
      pval = val[1..$];
      negative = true;
    }
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
      static if (isIntegral!T) {
	if (negative) {
	  assert (cast(T) (- intVal) == (- intVal), "Value -" ~ pval ~ " can not be of type " ~ T.stringof);
	}
	else {
	  assert (cast(T) intVal == intVal, "Value " ~ pval ~ " can not be of type " ~ T.stringof);
	}
      }
      else {
	import esdl.data.bvec: to;
	import std.format: format;
	if (negative) {
	  assert ((- intVal).to!(T) == (- intVal), "Value -" ~ pval ~ " can not be of type " ~ T.stringof);
	}
	else {
	  assert (intVal.to!(T) == intVal, "Value " ~ pval ~ " can not be of type " ~ T.stringof);
	}
      }
    }
    return true;
  }
  
  bool procRangeElem(ref ParsedBin bin) {
    string min;
    string max;
    size_t srcTag;
    parseSpace();
    if (BINS[srcCursor] == '$') {
      min = T.max.stringof;
      srcCursor += 1;
    }
    else {
      srcTag = parseIntLiteral();
      min = BINS[srcTag .. srcCursor];
    }
    checkValue(min);
    parseSpace();
    if (BINS.length > srcCursor + 2 &&
	BINS[srcCursor..srcCursor+2] == "..") {
      srcCursor += 2;
      parseSpace();
      if (BINS[srcCursor] == '$') {
	max = T.max.stringof;
	srcCursor += 1;
      }
      else {
	srcTag = parseIntLiteral();
	max = BINS[srcTag .. srcCursor];
      }
      checkValue(max);
      static if (isBitVector!T)
	fillCtr(bin._name, ".addRange(", min, ".to!_esdl__T, (", max, "-1).to!_esdl__T);\n");
      else
	fillCtr(bin._name, ".addRange(cast(_esdl__T) ", min, ", cast(_esdl__T) (", max, "-1));\n");
    }
    else if (BINS.length > srcCursor + 1 &&
	     BINS[srcCursor] == ':') {
      srcCursor += 1;
      parseSpace();
      if (BINS[srcCursor] == '$') {
	max = T.max.stringof;
	srcCursor += 1;
      }
      else {
	srcTag = parseIntLiteral();
	max = BINS[srcTag .. srcCursor];
      }
      checkValue(max);
      static if (isBitVector!T) 
	fillCtr(bin._name, ".addRange(", min, ".to!_esdl__T, ", max, ".to!_esdl__T);\n");
      else fillCtr(bin._name, ".addRange(cast(_esdl__T) ", min, ", cast(_esdl__T) ", max, ");\n");
    }
    else {
      static if (isBitVector!T)
	fillCtr(bin._name, ".addElem(" ~ min ~ ".to!_esdl__T);\n");
      else fillCtr(bin._name, ".addElem(cast(_esdl__T) " ~ min ~ ");\n");
    }
    parseSpace();
    if (BINS[srcCursor] == ',') return true;
    else if (BINS[srcCursor] == ']') return false;
    else {
      import std.conv;
      assert (false, "']' expected, not found at line " ~ srcLine.to!string);
    }
  }

  void procDefaultBins(ref ParsedBin bin) {
    srcCursor += 7;
    parseSpace();
    fillDecl("EsdlDefaultBin!_esdl__T ", bin._name, ";\n");
    fillCtr(bin._name, " = new EsdlDefaultBin!_esdl__T( Type.BIN, \"", bin._name, "\");\n");
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~
	      srcLine.to!string);
    }
    ++srcCursor;
    parseSpace();
  }

  void procRangeBins(ref ParsedBin bin) {
    fillDecl("EsdlRangeBin!_esdl__T ", bin._name, ";\n");
    fillCtr(bin._name, " = new EsdlRangeBin!_esdl__T( \"", bin._name, "\");\n");
    if (BINS[srcCursor] != '[') assert (false, "Error parsing bins: " ~ BINS[srcCursor..$]);
    srcCursor += 1;
    parseSpace();
    while (procRangeElem(bin)) {
      srcCursor += 1; 		// for comma
      parseSpace();
    }
    srcCursor += 1; 		// for the closing brace
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ BINS[srcCursor..$]);
    }
    ++srcCursor;
    parseSpace();
  }

  void procFunction(ref ParsedBin bin) {
    size_t srcTag = srcCursor;
    string funcName = parseIdentifierChain();
    if (bin._isWildcard) {
      fillDecl("EsdlWildcardArrBin!_esdl__T ", bin._name, ";\n");
      fillCtr(bin._name, " = new EsdlWildcardArrBin!_esdl__T( \"", bin._name, "\");\n");
    }
    else {
      fillDecl("EsdlValArrBin!_esdl__T ", bin._name, ";\n");
      fillCtr(bin._name, " = new EsdlValArrBin!_esdl__T( \"", bin._name, "\");\n");
    }
    fillCtr(bin._name, ".addArrDG(&" ~ BINS[srcTag..srcCursor] ~ ");\n");
    parseSpace();
    if (BINS[srcCursor] == '(') {
      srcCursor += 1;
      parseSpace();
      if (BINS[srcCursor] == ')') {
	srcCursor += 1;
      }
      else {
	assert (false, "expected ')' but found " ~ BINS[srcCursor..$]);
      }
    }
    parseSpace();
    if (BINS[srcCursor] == ';') {
      srcCursor += 1;
    }
    else {
      assert (false, "expected ';' but found " ~ BINS[srcCursor..$]);
    }
  }
  
  // returns false when this is the last element
  bool procWildcardElem(ref ParsedBin bin) {
    parseSpace();
    size_t srcTag = srcCursor;
    if (srcCursor > BINS.length - 1 || BINS[srcCursor] != '"')
      assert (false, "Error parsing bins: " ~ BINS[srcCursor..$]);
    srcCursor += 1;
    uint bitlen = 0;
    while (true) {
      if (srcCursor < BINS.length &&
	  (BINS[srcCursor] == '1' ||
	   BINS[srcCursor] == '0' ||
	   BINS[srcCursor] == '?' ||
	   BINS[srcCursor] == 'x' ||
	   BINS[srcCursor] == 'X' ||
	   BINS[srcCursor] == 'z' ||
	   BINS[srcCursor] == 'Z') ) {
	bitlen += 1;
	srcCursor += 1;
      }
      else if (BINS[srcCursor] == '_') {
	srcCursor += 1;
	continue;
      }
      else if (BINS[srcCursor] == '"') {
	srcCursor += 1;
	break;
      }
      else assert (false, "Error parsing wildcard bin: " ~
		   BINS[srcCursor..$]);
    }
    checkWildcard(BINS[srcTag .. srcCursor]);
    fillCtr(bin._name, ".addWildCard(", BINS[srcTag..srcCursor], ");\n");
    parseSpace();
    if (BINS[srcCursor] == ',') return true;
    else if (BINS[srcCursor] == ']') return false;
    else {
      import std.conv;
      assert (false, "']' expected, not found at line " ~ srcLine.to!string);
    }
  }
  
  void procWildcardBins(ref ParsedBin bin) {
    fillDecl("EsdlWildcardBin!_esdl__T ", bin._name, ";\n");
    fillCtr(bin._name, " = new EsdlWildcardBin!_esdl__T( \"", bin._name, "\");\n");
    if (BINS[srcCursor] != '[') assert (false, "Error parsing bins: " ~ BINS[srcCursor..$]);
    srcCursor += 1;
    parseSpace();
    while (procWildcardElem(bin)) {
      srcCursor += 1; 		// for comma
      parseSpace();
    }
    srcCursor += 1; 		// for the closing brace
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ BINS[srcCursor..$]);
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
    while (srcCursor < BINS.length) {
      if (isTypeStatement()) {
	parseOption();
      }
      else {
	binsCount += 1;
	parseABin();
	parseSpace();
      }
    }
    if (binsCount == 0) {
      // Add default bin
      fillDecl("EsdlRangeBin!_esdl__T _esdl__bin__esdl__defaultBin;\n");
      fillCtr("_esdl__bin__esdl__defaultBin = new EsdlRangeBin!_esdl__T( q{_esdl__defaultBin});\n");
      fillCtr("_esdl__cvrBins ~= _esdl__bin__esdl__defaultBin;\n");
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
    size_t srcTag = parseIdentifier();
    return BINS[srcTag..srcCursor];
  }

  void parseBinAttribs(ref ParsedBin bin) {
    while (BINS[srcCursor] == '@') {
      srcCursor += 1;
      string attr = parseBinAttrib();
      if (attr == "ignore") bin._isIgnore = true;
      else if (attr == "illegal") bin._isIllegal = true;
      else if (attr == "wildcard") bin._isWildcard = true;
      else if (attr == "transition") bin._isTransition = true;
      else if (attr == "filter") {
	parseSpace();
	if (BINS[srcCursor] != '(') {
	  assert (false, "Error looking for '(', found: " ~
		  BINS[srcCursor..$]);
	}
	else {
	  srcCursor += 1;
	  parseSpace();
	  string filter = parseIdentifierChain();
	  bin._filter = filter;
	}
	parseSpace();
	if (BINS[srcCursor] != ')') {
	  assert (false, "Error looking for ')', found: " ~
		  BINS[srcCursor..$]);
	}
	srcCursor += 1;
      }
      else assert (false, "Unknown Attribute: @" ~ attr);
      parseSpace();
    }
    bin.checkAttribs();
  }
  
  void parseABin() {
    ParsedBin bin;
    parseSpace();

    parseBinAttribs(bin);

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
	assert (false, "Expected keyword 'bins' not found" ~
		BINS[srcTag..$] ~ " instead");
    }

    if (BINS[srcCursor] == '[') {
      bin._isArray = true;
      srcCursor += 1;
      parseSpace();
      size_t srcTag = parseIntLiteral(true);
      bin._arrayLen = BINS[srcTag .. srcCursor];
      parseSpace();
      if (BINS[srcCursor] != ']')
	assert (false, "Expected ']' not found. Found " ~ BINS[srcCursor..$]);
      srcCursor += 1;
      parseSpace();
    }
    
    parseSpace();
    auto srcTag = parseIdentifier();
    string name = BINS[srcTag .. srcCursor];
    bin._name = name;
    parseSpace();
    if (BINS[srcCursor] != '=')
      assert (false, "Expected '=' not found. Found " ~ BINS[srcCursor..$]);
    srcCursor += 1;
    parseSpace();

    procBinOfType(bin);
  }

  // look for square brackets and report dim
  // can only be one or two
  void parseBinsArrDim(ref ParsedBin bin) {
    size_t start = srcCursor;
    size_t dim = 0;
    while (true) {
      if (BINS[srcCursor] == '[') {
	srcCursor += 1;
	dim += 1;
	parseSpace();
      }
      else break;
    }
    bin._arrayDim = dim;
  }

  string parseIdentifierChain() {
    size_t srcUpto;
    size_t start = srcCursor;
    parseIdentifier();
    srcUpto = srcCursor;
    if (start < srcCursor) {
      parseSpace();
      if (BINS.length > srcCursor && BINS[srcCursor] == '.') {
	srcCursor += 1;
	parseSpace();
	parseIdentifierChain();
	srcUpto = srcCursor;
      }
      else {
	srcCursor = srcUpto;
      }
    }
    return BINS[start..srcUpto];
  }
}

class EsdlWildcardBin(T): EsdlBaseBin!T
{
  string _name;
  size_t _hits = 0;

  this(string name) {
    import std.conv;
    _name = name;
  }

  void addWildCard(string wc) {
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
  WILDCARD       = 0b000100,
  TRANSITION     = 0b001000,
  ILLEGAL        = 0b000001,
  IGNORE         = 0b000010,
  DYNAMICARRAY   = 0b010000,
  STATICARRAY    = 0b100000
}

abstract class EsdlBaseBin(T)
{
  alias FilterDG = bool delegate(T val);

  uint _attributes;

  FilterDG _filter;
  
  void addFilter(FilterDG filter) {
    _filter = filter;
  }

  void addAttribute(EsdlBinAttr attr) {
    _attributes |= attr;
  }

  void markIgnore() {
    _attributes |= EsdlBinAttr.IGNORE;
  }
  
  void markIllegal() {
    _attributes |= EsdlBinAttr.ILLEGAL;
  }
  
  abstract void sample(T val);
  abstract double getCoverage();
  
  abstract string getName();
  abstract string describe();

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

class EsdlValArrBin(T): EsdlBaseBin!T
{
  // import std.typecons: Tuple, tuple;

  // alias TRange = Tuple!(T, "min", T, "max");

  alias Array1DG = T[] delegate();
  alias Array2DG = T[][] delegate();

  Array1DG _arr1dg;
  Array2DG _arr2dg;

  void addArrDG(Array1DG dg) {
    _arr1dg = dg;
  }

  void addArrDG(Array2DG dg) {
    _arr2dg = dg;
  }

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

class EsdlWildcardArrBin(T): EsdlBaseBin!T
{
  string _name;
  size_t _hits = 0;

  static if (isIntegral!T) enum size_t BITNUM = T.sizeof * 8;
  static if (isBitVector!T) enum size_t BITNUM = T.SIZE;

  alias LT = ulvec!BITNUM;
  
  alias Array1DG = LT[] delegate();
  alias Array2DG = LT[][] delegate();


  Array1DG _arr1dg;
  Array2DG _arr2dg;

  void addArrDG(Array1DG dg) {
    import std.stdio: writeln;
    auto arr = dg();
    writeln(arr);
    foreach (wc; arr) {
      writeln("Adding Wildcard: ", Wildcard!BITNUM(wc));
    }
    _arr1dg = dg;
  }

  void addArrDG(Array2DG dg) {
    _arr2dg = dg;
  }

  this(string name) {
    import std.conv;
    _name = name;
  }

  void addWildCard(string wc) {
    import std.stdio: writeln;
    writeln("Adding Wildcard: ", Wildcard!BITNUM(wc));
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


enum Type: ubyte {IGNORE, ILLEGAL, BIN};

class EsdlDefaultBin(T): EsdlBaseBin!T
{
  Type _type = Type.IGNORE;
  bool _curr_hit;
  string _name = "";
  uint _hits = 0;
  this (Type t, string n) {
    _type = t;
    _name = n;
  }

  override void sample(T val) {}
  override double getCoverage() {return 0.0;}

  override string getName() {return _name;}
  override string describe() {return "";}

}
