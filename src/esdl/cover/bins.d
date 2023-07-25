// import esdl.rand;
// import esdl.data.bvec;

module esdl.cover.bins;
import esdl.data.vector: Vector;
import esdl.data.bvec: isBitVector, ulvec;
import std.traits: isIntegral;
import std.conv: parse;
import esdl.cover.wild;
import esdl.cover.point: CoverPoint;


const uint maxArrayDymanicLength = 64;

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
    bool _hasRange;

    size_t _arrayDim;

    string _filter;

    // _arrayLen != 0 if static array
    size_t _arrayLen;

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
    if (bin._isArray) { 
      if (bin._arrayLen == 0) { // dynamic array
	fillCtr(bin._name, ".calculateLength();\n");
      }
      else { // static array
	import std.conv: to;
	fillCtr(bin._name, ".setBinArrLength(", bin._arrayLen.to!string,");\n");
      }
    }
    else { // non-array
      fillCtr(bin._name, ".setBinArrLength(1);\n");
    }
    
    if (bin._isIllegal) {
      fillCtr(bin._name, ".markIllegal();\n");
      fillCtr("_esdl__illBins ~= ", bin._name, ";\n");
    }
    else if (bin._isIgnore) {
      fillCtr(bin._name, ".markIgnore();\n");
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
      bin._hasRange = true;
      static if (isBitVector!T)
	fillCtr("_esdl__addRange(", min, ".to!_esdl__T, (", max, "-1).to!_esdl__T);\n");
      else
	fillCtr("_esdl__addRange(cast(_esdl__T) ", min, ", cast(_esdl__T) (", max, "-1));\n");
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
      bin._hasRange = true;
      static if (isBitVector!T) 
	fillCtr("_esdl__addRange(", min, ".to!_esdl__T, ", max, ".to!_esdl__T);\n");
      else
	fillCtr("_esdl__addRange(cast(_esdl__T) ", min, ", cast(_esdl__T) ", max, ");\n");
    }
    else {
      static if (isBitVector!T)
	fillCtr("_esdl__addElem(" ~ min ~ ".to!_esdl__T);\n");
      else fillCtr("_esdl__addElem(cast(_esdl__T) " ~ min ~ ");\n");
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
    fillDecl("EsdlRangeBin!_esdl__T ", bin._name, ";\n");
    import std.conv: to;
    string min = T.min.to!string();
    string max = T.max.to!string();
    static if (isBitVector!T) 
      fillCtr("_esdl__addRange(", min, ".to!_esdl__T, ", max, ".to!_esdl__T);\n");
    else
      fillCtr("_esdl__addRange(cast(_esdl__T) ", min, ", cast(_esdl__T) ", max, ");\n");
    fillCtr(bin._name, " = new EsdlRangeBin!_esdl__T( \"", bin._name, "\", this);\n");
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~
	      srcLine.to!string);
    }
    ++srcCursor;
    parseSpace();
  }

  
  void procRangeBins(ref ParsedBin bin) {
    if (BINS[srcCursor] != '[') assert (false, "Error parsing bins: " ~ BINS[srcCursor..$]);
    srcCursor += 1;
    parseSpace();
    if (BINS[srcCursor] == '[') {
      srcCursor += 1;
      parseSpace();
      proc2DRangeBins(bin);
    }
    else {
      proc1DRangeBins(bin);
    }
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ BINS[srcCursor..$]);
    }
    fillDecl("EsdlRangeBin!_esdl__T ", bin._name, ";\n");
    fillCtr(bin._name, " = new EsdlRangeBin!_esdl__T( \"", bin._name, "\", this);\n");
    srcCursor += 1;
    parseSpace();
  }
  
  void proc2DRangeBins(ref ParsedBin bin) {
    while (true) {
      proc1DRangeBins(bin);
      parseSpace();
      fillCtr("_esdl__addDelimiter();\n");
      if (BINS[srcCursor] == ',') {
	srcCursor += 1;
	parseSpace();
	if (BINS[srcCursor] != '[') {
	  import std.conv;
	  assert (false, "'[' expected, not found at line " ~ srcLine.to!string);
	}
	srcCursor += 1;
	parseSpace();
	continue;
      }
      else if (BINS[srcCursor] == ']') {
	srcCursor += 1;
	break;
      }
      else {
	import std.conv;
	assert (false, "']' expected, not found at line " ~ srcLine.to!string);
      }
    }
  }
  
  void proc1DRangeBins(ref ParsedBin bin) {
    while (procRangeElem(bin)) {
      srcCursor += 1; 		// for comma
      parseSpace();
    }
    srcCursor += 1; // for the closing brace
  }

  void procFunction(ref ParsedBin bin) {
    size_t srcTag = srcCursor;
    string funcName = parseIdentifierChain();
    if (bin._isWildcard) {
      fillDecl("EsdlWildcardBin!_esdl__T ", bin._name, ";\n");
      fillCtr(bin._name, " = new EsdlWildcardBin!_esdl__T( \"", bin._name, "\", this);\n");
    }
    else {
      fillDecl("EsdlRangeBin!_esdl__T ", bin._name, ";\n");
      fillCtr(bin._name, " = new EsdlRangeBin!_esdl__T( \"", bin._name, "\", this);\n");
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
    fillCtr("_esdl__addWildcard(", BINS[srcTag..srcCursor], ");\n");
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
    if (BINS[srcCursor] != '[') assert (false, "Error parsing bins: " ~ BINS[srcCursor..$]);
    srcCursor += 1;
    parseSpace();
    if (BINS[srcCursor] == '[') {
      srcCursor += 1;
      parseSpace();
      proc2DWildcardBins(bin);
    }
    else {
      proc1DWildcardBins(bin);
    }
    if (BINS[srcCursor] != ';') {
      import std.conv;
      assert (false, "';' expected, not found at line " ~ BINS[srcCursor..$]);
    }
    fillCtr(bin._name, " = new EsdlWildcardBin!_esdl__T( \"", bin._name, "\", this);\n");
    srcCursor += 1;
    parseSpace();
  }

  void proc2DWildcardBins(ref ParsedBin bin) {
    while (true) {
      proc1DWildcardBins(bin);
      parseSpace();
      fillCtr("_esdl__addDelimiter();\n");
      if (BINS[srcCursor] == ',') {
	srcCursor += 1;
	parseSpace();
	if (BINS[srcCursor] != '[') {
	  import std.conv;
	  assert (false, "'[' expected, not found at line " ~ srcLine.to!string);
	}
	srcCursor += 1;
	parseSpace();
	continue;
      }
      else if (BINS[srcCursor] == ']') {
	srcCursor += 1;
	break;
      }
      else {
	import std.conv;
	assert (false, "']' expected, not found at line " ~ srcLine.to!string);
      }
    }
  }
  
  void proc1DWildcardBins(ref ParsedBin bin) {
    while (procWildcardElem(bin)) {
      srcCursor += 1; 		// for comma
      parseSpace();
    }
    srcCursor += 1; // for the closing brace
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
      fillCtr("_esdl__addRange(cast(_esdl__T) ", T.min.to!string(), ", cast(_esdl__T) ", T.min.to!string(), ");\n");
      fillCtr("_esdl__bin__esdl__defaultBin = new EsdlRangeBin!_esdl__T( q{_esdl__defaultBin}, this);\n");
      if (T.max - cast(size_t)(T.min) > maxArrayDymanicLength) {
	fillCtr("_esdl__bin__esdl__defaultBin.setBinArrLength(" ~ maxArrayDymanicLength.to!string ~ ");\n");
      }
      else {
	fillCtr("_esdl__bin__esdl__defaultBin.setBinArrLength(" ~ (T.max - T.min).to!string ~ ");\n");
      }
      fillCtr("_esdl__cvrBins ~= _esdl__bin__esdl__defaultBin;\n");
      // fillCtr("_sbinsNum ~= 64;\n");
      import std.conv: to;
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
      if (BINS[srcCursor] == ']') {
	bin._arrayLen = 0;
      }
      else {
	size_t srcTag = parseIntLiteral(true);
	import std.conv: to;
	bin._arrayLen = BINS[srcTag .. srcCursor].to!(size_t);
	parseSpace();
	if (BINS[srcCursor] != ']')
	  assert (false, "Expected ']' not found. Found " ~ BINS[srcCursor..$]);
      }
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

  size_t _length;
  size_t _offset;

  bool _hasFilter = false;
  FilterDG _filter;

  CoverPoint!T _esdl__CP;

  string _name = "";

  void setBinArrLength(size_t len) {
    _length = len;
  }

  abstract void calculateLength();
  
  void addFilter(FilterDG filter) {
    _hasFilter = true;
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

  string getName() {
    return _name;    
  }
  
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

  import std.traits;
  
  alias Array1DG = T[] delegate();
  alias Array2DG = T[][] delegate();
  // alias UT = Unsigned!(T);
  
  struct BinRange {

    size_t _countBefore;

    T _min;
    T _max;

    int opCmp(ref const BinRange other) const {
      if (this._min > other._min) {
	return +1;
      }
      else if (this._min < other._min) {
	return -1;
      }
      else if (this._max == other._max) {
	return 0;
      }
      else if (other._max-1 > this._max-1) {
	return -1;
      }
      else return +1;
    }

    int opCmp(ref const T other) const {
      if (this._min > other) return 1;
      else if (this._min < other) return -1;
      else return 0;
    }
  }
  
  bool _hasRanges;
  bool is1d;
  
  size_t _rangeCount;
  
  union arrays {
    BinRange[] d1Ranges;
    BinRange[][] d2Ranges;
    T[] d1Values;
    T[][] d2Values;
  };
  
  arrays _arrs;


  // in case of dynamic arrays
  override void calculateLength(){
    if (_hasRanges) {
      if (is1d) {
	_length = _rangeCount;
	if (_length > maxArrayDymanicLength) {
	  _length = maxArrayDymanicLength;
	}
      }
      else {
	_length = _arrs.d2Ranges.length;
      }
    }
    else {
      if (is1d) {
	_length = _rangeCount;
	if (_length > maxArrayDymanicLength) {
	  _length = maxArrayDymanicLength;
	}
      }
      else {
	_length = _arrs.d2Values.length;
      }
    }
  }
  
  this(string name, CoverPoint!T cp) {
    
    _name = name;
    _esdl__CP = cp;

    if (cp._esdl__container._mins.length != cp._esdl__container._maxs.length) assert (false);

    
    _hasRanges = cp._esdl__container._mins.length > 0;
    
    if (cp._esdl__container._mins.length + cp._esdl__container._elems.length == 0) {
      // expecting function, this is a really bad way to do this stuff btw
      return;
    }
      
    if (cp._esdl__container._delims.length > 0) {
      is1d = false;
      size_t p_range_num = 0;
      size_t p_val_num = 0;
      foreach (ref delim; cp._esdl__container._delims) {
	this.addArray();
	size_t range_num = delim[0];
	size_t val_num = delim[1];
	for (size_t n = p_range_num; n != range_num; n += 1) {
	  this.addRange(cp._esdl__container._mins[n], cp._esdl__container._maxs[n]);
	}
	for (size_t n = p_val_num; n != val_num; n += 1) {
	  this.addElem(cp._esdl__container._elems[n]);
	}
	p_range_num = range_num;
	p_val_num = val_num;
      }
    }    
    else {
      is1d = true;      
      for (uint n=0; n != cp._esdl__container._mins.length; n += 1) {
	this.addRange(cp._esdl__container._mins[n], cp._esdl__container._maxs[n]);
      }
      for (uint n=0; n != cp._esdl__container._elems.length; n += 1) {
	this.addElem(cp._esdl__container._elems[n]);
      }
    }
  
    processBins();
    
    cp._esdl__container.reset();
  }
  
  void addArray () {
    assert(!is1d);
    if (_hasRanges) {
      _arrs.d2Ranges ~= new BinRange[](0);
    }
    else {
      _arrs.d2Values ~= new T[](0);
    }
  }
  
  void addRange (T min, T max) {
    if (is1d) {
      _arrs.d1Ranges ~= BinRange(0L, min, max);
    }
    else {
      _arrs.d2Ranges[$-1] ~= BinRange(0L, min, max);
    }
  }

  void addElem (T val) {
    if (_hasRanges) {
      this.addRange(val, cast(T) (val+1));
    }
    if (is1d) {
      _arrs.d1Values ~= val;
    }
    else {
      _arrs.d2Values[$-1] ~= val;
    }
  }

  void addArrDG(Array1DG dg) {
    _arrs.d1Values = dg();
    is1d = true;
    processBins();
  }

  void addArrDG(Array2DG dg) {
    _arrs.d2Values = dg();
    is1d = false;
    processBins();
  }

  T [] sortAndRemoveOverlaps (T [] arr) {
    
    import std.algorithm.sorting: sort;

    sort(arr);
    T [] narr;
    narr ~= arr[0];
    foreach (val; arr[1..$]) {
      if (narr[$-1] != val) {
	narr ~= val;
      }
    }
    return narr;
    
  }

  BinRange [] sortAndRemoveOverlaps (BinRange [] ranges) {

    import std.algorithm.sorting: sort;
        
    sort(ranges);
    import std.stdio: writeln;
    writeln(ranges.length);
    BinRange[] newRanges;
    writeln(BinRange.sizeof);
    writeln(newRanges.length);
    newRanges.length = 1;
    newRanges[0] = ranges[0];
    writeln(newRanges.length);
    foreach (range; ranges[1..$]) {
      if (newRanges[$-1]._max >= range._min) {
	newRanges[$-1]._max = range._max;
      }
      else {
	newRanges ~= range;
      }
    }
    return newRanges;
    
  }

  void processBins() {
    if (_hasRanges) {
      if (is1d) {
	_arrs.d1Ranges = sortAndRemoveOverlaps(_arrs.d1Ranges);
	size_t cumsum = 0;
	foreach (ref range; _arrs.d1Ranges) {
	  range._countBefore = cumsum;
	  cumsum += range._max - range._min;
	}
	_rangeCount = cumsum;
      }
      else {
	foreach (ref arr; _arrs.d2Ranges) {
	  arr = sortAndRemoveOverlaps(arr);
	}
	_rangeCount = 0;	
      }
    }
    else {
      if (is1d) {
	_arrs.d1Values = sortAndRemoveOverlaps(_arrs.d1Values);
	_rangeCount = _arrs.d1Values.length;
      }
      else {
	foreach (ref arr; _arrs.d2Values) {
	  arr = sortAndRemoveOverlaps(arr);
	}
	_rangeCount = 0;
      }
    }
  }
    
  size_t getBinNumber (size_t count) {
    return (count * _length) / _rangeCount;
  }
  
  override void sample(T val) {

    
    if (_hasFilter && (!_filter(val))) {
      return;
    }
    
    import std.algorithm.sorting;
    import std.range;
    
    if (_hasRanges) {
      if (is1d) {
	auto sr = assumeSorted(_arrs.d1Ranges);
	size_t idx = _arrs.d1Ranges.length - sr.upperBound!(SearchPolicy.binarySearch, T)(val).length;
	if (idx == 0)
	  return;
	idx --;
	if (val <= (_arrs.d1Ranges[idx]._max-1)) {
	  size_t count = _arrs.d1Ranges[idx]._countBefore + (val - _arrs.d1Ranges[idx]._min);
	  _esdl__CP.addHit(getBinNumber(count) + _offset);
	}
      }
      else {
	foreach (i, ref ar; _arrs.d2Ranges) {
	  auto sr = assumeSorted(ar);
	  size_t idx = ar.length - sr.upperBound(val).length;
	  if (idx == 0)
	    continue;
	  idx --;
	  if (val <= (ar[idx]._max-1)) {
	    _esdl__CP.addHit(i + _offset);
	  }
	}
      }
    }
    else {
      if (is1d) {
	auto sr = assumeSorted(_arrs.d1Values);
	auto ub = sr.upperBound(val);
	if (ub.length != 0 && ub[0] == val) {
	  size_t idx = _arrs.d1Values.length - ub.length;
	  _esdl__CP.addHit(getBinNumber(idx) + _offset);
	}
      }
      else {
	foreach (i, ref ar; _arrs.d2Values) {
	  auto sr = assumeSorted(ar);
	  auto ub = sr.upperBound(val);
	  if (ub.length != 0 && ub[0] == val) {
	    _esdl__CP.addHit(i + _offset);
	  }
	}
      }
    }
  }

  override string describe()
  {
    string s = "Name : " ~ _name ~ "\n";
    return s;
  }
}

class EsdlWildcardBin(T): EsdlBaseBin!T
{

  static if (isIntegral!T) enum size_t BITNUM = T.sizeof * 8;
  static if (isBitVector!T) enum size_t BITNUM = T.SIZE;
  
  alias LT = ulvec!BITNUM;
  
  alias Array1DG = LT[] delegate();
  alias Array2DG = LT[][] delegate();

  union arrays {
    Wildcard!T [] d1;
    Wildcard!T [][] d2;
  };
  arrays _arrs;

  bool is1d = true;
  
  // in case of dynamic arrays
  override void calculateLength(){
    if (is1d) {
      _length = _arrs.d1.length;
      if (_length > maxArrayDymanicLength) {
	_length = maxArrayDymanicLength;
      }
    }
    else {
      _length = _arrs.d2.length;
    }
  }

  void addArrDG(Array1DG dg) {
    is1d = true;
    auto arr = dg();
    foreach (ref wc; arr) {
      _arrs.d1 ~= Wildcard!T(wc);
    }
  }

  void addArrDG(Array2DG dg) {
    is1d = false;
    auto arr = dg();
    foreach (ref arr1; arr) {
      _arrs.d2 ~= new Wildcard!T[](0);
      foreach (ref wc; arr1) {
	_arrs.d2[$-1] ~= Wildcard!T(wc);
      }
    }
  }
      
  this(string name, CoverPoint!T cp) {
    
    _name = name;
    _esdl__CP = cp;

    if (cp._esdl__container._wildcards.length == 0) {
      // expecting function, this is a really bad way to do this stuff btw
      return;
    }

    if (cp._esdl__container._delims.length > 0) {
      is1d = false;
      size_t p_num = 0;
      foreach (ref delim; cp._esdl__container._delims) {
	this.addArray();
	size_t num = delim[0];
	for (size_t n = p_num; n != num; n += 1) {
	  this.addWildcard(cp._esdl__container._wildcards[n]);
	}
	p_num = num;
      }
    }
    else {
      is1d = true;
      foreach (wc; cp._esdl__container._wildcards) {
	this.addWildcard(wc);
      }
    }
    cp._esdl__container.reset();
  }

  void addArray () {
    assert(!is1d);
    _arrs.d2 ~= new Wildcard!T[](0);
  }

    
  void addWildcard(string wc) {
    if (is1d) {
      _arrs.d1 ~= Wildcard!T(wc);
    }
    else {
      _arrs.d2[$-1] ~= Wildcard!T(wc);
    }
  }

  
  override void sample(T val) {

    if (_hasFilter && (!_filter(val))) {
      return;
    }
    
    if (is1d) {
      for (size_t i = 0; i < _arrs.d1.length; i ++) {
	if (_arrs.d1[i].checkHit(val)) {
	  size_t hit = (i * _length) / _arrs.d1.length;
	  _esdl__CP.addHit(hit + _offset);
	  // goto next hit
	  size_t next_hit = hit + 1;
	  size_t next_i = (_arrs.d1.length * next_hit) / _length;
	  i = next_i - 1;
	}
      }
    }
    else {
      foreach (i, ref arr; _arrs.d2) {
	foreach (ref wc; arr) {
	  if (wc.checkHit(val)) {
	    _esdl__CP.addHit(i + _offset);
	    break;
	  }
	}
      }
    }
  }

  override string describe()
  {
    string s = "Name : " ~ _name ~ "\n";
    return s;
  } 
}
