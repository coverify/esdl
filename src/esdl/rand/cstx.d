// Written in the D programming language.

// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>


// This file is a part of esdl.
// This file is a part of VLang.

// This file contains functionality to translate constraint block into
// functions that are used for solving the constraints. Since this
// translator is invoked by vlang at compile time, the code is
// optimized for memory. The translator works in two phases. In the
// first phase we just parse through the code to get an idea of the
// length of the resulting string. In the second phase we actually
// translate the constraint block

// The logic of this translator is simple. Here is what we need to
// achieve:
// 1. If we hit a foreach or if/else block, we need to handle it: TBD
// 2. We need to replace all the identifiers and literals with a
// wrapper around them
// 3. All the compariason operators and the implication operator need
// to be replaced with corresponding function calls. The good thing is
// that none of none of these operators chain together

// Here is how we do it:
//
// 1. Treat all parenthesis, addition, multiplication, substraction
// other lower level operators as whitespace. These just need to be
// replicated in the output
// 2. start from left, reserve space for two left parenthesis, one for
// possible implication operator and another for possible compariason
// operator. Keep two local size_t variables to track these paren
// positions.
// 3. Any logic operator "&&" or "||" or an implication operator "=>"
// or a semicolon will will terminate a comparion. We also keep track
// of whether we are inside a comparison operator using a bool
// variale.
// 4. a semicolon alone can end an implication operator.

// As for foreach block, we need to keep a mapping table to help
// replace the identifiers as required. We shall use two dynamic
// arrays to help achieve that. TBD

module esdl.rand.cstx;
import std.conv;

struct CstParser {

  immutable string CST;
  immutable string FILE;
  immutable size_t LINE;
  
  bool dryRun = true;

  uint stmtCount = 0;

  char[] outBuffer;
  
  string dummy;			// sometimes required in dryRun

  string _proxy;
  
  size_t outCursor = 0;
  size_t dclCursor = 0;

  size_t srcCursor = 0;
  size_t srcLine   = 0;

  size_t numParen  = 0;

  size_t numIndex  = 0;
  size_t[] indexTag;

  VarPair[] varMap = [];

  string[] iterators;

  uint[] soft;
  

  // list of if conditions that are currently active
  Condition[] ifConds = [];

  void setupBuffer() {
    outBuffer.length = outCursor + dclCursor;
    outCursor = dclCursor;
    srcCursor = 0;
    dclCursor = 0;
    dcls.length = 0;
    if (varMap.length !is 0) {
      assert (false, "varMap has not been unrolled completely");
    }
    dryRun = false;
    stmtCount = 0;
  }

  this(string CST, string FILE, size_t LINE) {
    this.CST = CST;
    this.FILE = FILE;
    this.LINE = LINE;
  }

  size_t retreat(size_t step) {
    size_t start = outCursor;
    outCursor -= step;
    return start;
  }
  
  size_t fill(in char c) {
    size_t start = outCursor;
    if (! dryRun) {
      outBuffer[outCursor] = c;
    }
    outCursor += 1;
    return start;
  }

  size_t fill(in string source) {
    size_t start = outCursor;
    if (! dryRun) {
      foreach (i, c; source) {
	outBuffer[outCursor+i] = c;
      }
    }
    outCursor += source.length;
    return start;
  }

  void place(in char c, size_t cursor = 0) {
    if (! dryRun) outBuffer[cursor] = c;
  }

  string[] dcls;
  
  bool needDcl(in string source) {
    // no declaration for numeric literals
    if (source[0] < '9' && source[0] > '0') {
      return false;
    }
    foreach (dcl; dcls) {
      if (source == dcl) return false;
    }
    return true;
  }
  
  void fillDeclaration(in string source) {
    if (needDcl(source)) {
      fillDcl("// _esdl__declProxy!");
      fillDcl(source);
      fillDcl(";\n");
      dcls ~= source;
    }
  }

  size_t fillDcl(in string source) {
    size_t start = dclCursor;
    if (! dryRun) {
      foreach (i, c; source) {
	outBuffer[dclCursor+i] = c;
      }
    }
    dclCursor += source.length;
    return start;
  }

  // CstParser exprParser(size_t cursor) {
  //   CstParser dup = CstParser(CST[cursor..$]);
  //   return dup;
  // }

  enum OpArithToken: byte
  {   NONE = 0,
      AND,
      OR,
      XOR,
      ADD,
      SUB,
      MUL,
      DIV,
      REM,			// remainder
      LSH,
      RSH,
      SLICE,
      }

  enum OpCmpToken: byte
  {   NONE = 0,
      EQU,
      GTE,
      LTE,
      NEQ,
      GTH,
      LTH,
      INSIDE,
      NOTINSIDE,
      DIST,
  }

  enum OpRangeToken: byte
  {   NONE = 0,
      RANGE,
      RANGEINC,
  }

  enum OpLogicToken: byte
  {   NONE = 0,
      LOGICIMP,		// Implication operator
      LOGICAND,
      LOGICOR,
      INDEX,
      }
  
  enum OpToken: byte
  {   NONE = 0,
      AND,
      OR,
      XOR,
      ADD,
      SUB,
      MUL,
      DIV,
      REM,			// remainder
      LSH,
      RSH,
      EQU,
      GTE,
      LTE,
      NEQ,
      GTH,
      LTH,
      LOGICIMP,			// Implication operator
      LOGICAND,
      LOGICOR,
      INDEX,
      SLICE,
      SLICEINC,			// inclusive slice
      }

  enum OpUnaryArithToken: byte
  {   NONE = 0,
      NEG,
      INV,
      }

  enum OpUnaryLogicToken: byte
  {   NONE = 0,
      NOT,
      }

  enum OpDistToken: byte
  {   NONE = 0,
      ITEMWISE,
      RANGEWISE,
  }

  OpUnaryArithToken parseUnaryArithOperator() {
    OpUnaryArithToken tok = OpUnaryArithToken.NONE;
    if (srcCursor < CST.length) {
      if (CST[srcCursor] == '~') tok = OpUnaryArithToken.INV;
      if (CST[srcCursor] == '-') tok = OpUnaryArithToken.NEG;
    }
    if (tok !is OpUnaryArithToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  OpUnaryLogicToken parseUnaryLogicOperator() {
    OpUnaryLogicToken tok = OpUnaryLogicToken.NONE;
    if (srcCursor < CST.length) {
      if (CST[srcCursor] == '!') tok = OpUnaryLogicToken.NOT;
    }
    if (tok !is OpUnaryLogicToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  OpDistToken parseDistOperator() {
    OpDistToken tok = OpDistToken.NONE;
    if (srcCursor < CST.length - 1) {
      if (CST[srcCursor] == ':' && CST[srcCursor+1] == '=') tok = OpDistToken.ITEMWISE;
      if (CST[srcCursor] == ':' && CST[srcCursor+1] == '/') tok = OpDistToken.RANGEWISE;
    }
    if (tok !is OpDistToken.NONE) {
      srcCursor += 2;
    }
    return tok;
  }

  OpArithToken parseArithOperator() {
    OpArithToken tok = OpArithToken.NONE;
    if (srcCursor < CST.length - 1) {
      if (CST[srcCursor] == '<' && CST[srcCursor+1] == '<') tok = OpArithToken.LSH;
      if (CST[srcCursor] == '>' && CST[srcCursor+1] == '>') tok = OpArithToken.RSH;
      // these are not arithmetic operators
      if (CST[srcCursor] == '&' && CST[srcCursor+1] == '&') return tok;
      if (CST[srcCursor] == '|' && CST[srcCursor+1] == '|') return tok;
      if (CST[srcCursor] == '-' && CST[srcCursor+1] == '>') return tok;
    }
    if (tok !is OpArithToken.NONE) {
      srcCursor += 2;
      return tok;
    }
    if (srcCursor < CST.length) {
      if (CST[srcCursor] == '&') tok = OpArithToken.AND;
      if (CST[srcCursor] == '|') tok = OpArithToken.OR;
      if (CST[srcCursor] == '^') tok = OpArithToken.XOR;
      if (CST[srcCursor] == '+') tok = OpArithToken.ADD;
      if (CST[srcCursor] == '-') tok = OpArithToken.SUB;
      if (CST[srcCursor] == '*') tok = OpArithToken.MUL;
      if (CST[srcCursor] == '/') tok = OpArithToken.DIV;
      if (CST[srcCursor] == '%') tok = OpArithToken.REM;
      if (CST[srcCursor] == '[') {
	size_t srcTag = srcCursor;
	while (srcCursor < CST.length - 2) {
	  if (CST[srcCursor..srcCursor+2] == "..") {
	    tok = OpArithToken.SLICE;
	    srcCursor = srcTag;
	    break;
	  }
	  if (CST[srcCursor] == ':') {
	    tok = OpArithToken.SLICE;
	    srcCursor = srcTag;
	    break;
	  }
	  if (CST[srcCursor] == ']') {
	    srcCursor = srcTag;	// TBD -- fixme for nested square brackets
	    break;
	  }
	}
      }
    }
    if (tok !is OpArithToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  OpRangeToken parseRangeOperator() {
    OpRangeToken tok = OpRangeToken.NONE;
    if (srcCursor <= CST.length - 2) {
      if (CST[srcCursor] == '.' && CST[srcCursor+1] == '.') tok = OpRangeToken.RANGE;
    }
    if (tok !is OpRangeToken.NONE) {
      srcCursor += 2;
      return tok;
    }
    if (srcCursor <= CST.length - 1) {
      if (CST[srcCursor] == ':' &&
	  CST[srcCursor+1] != '=') tok = OpRangeToken.RANGEINC;
    }
    if (tok !is OpRangeToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  OpCmpToken parseCmpOperator() {
    OpCmpToken tok = OpCmpToken.NONE;
    if (srcCursor <= CST.length - 7) {
      if (CST[srcCursor..srcCursor+7] == "!inside") {
	tok = OpCmpToken.NOTINSIDE;
	srcCursor += 7;
	return tok;
      }
    }
    if (srcCursor <= CST.length - 6) {
      if (CST[srcCursor..srcCursor+6] == "inside") {
	tok = OpCmpToken.INSIDE;
	srcCursor += 6;
	return tok;
      }
    }
    if (srcCursor <= CST.length - 4) {
      if (CST[srcCursor..srcCursor+4] == "dist") {
	tok = OpCmpToken.DIST;
	srcCursor += 4;
	return tok;
      }
    }
    if (srcCursor <= CST.length - 2) {
      if (CST[srcCursor] == '=' && CST[srcCursor+1] == '=') tok = OpCmpToken.EQU;
      if (CST[srcCursor] == '!' && CST[srcCursor+1] == '=') tok = OpCmpToken.NEQ;
      if (CST[srcCursor] == '<' && CST[srcCursor+1] == '=') tok = OpCmpToken.LTE;
      if (CST[srcCursor] == '>' && CST[srcCursor+1] == '=') tok = OpCmpToken.GTE;
    }
    if (tok !is OpCmpToken.NONE) {
      srcCursor += 2;
      return tok;
    }
    if (srcCursor <= CST.length - 1) {
      if (CST[srcCursor] == '<') tok = OpCmpToken.LTH;
      if (CST[srcCursor] == '>') tok = OpCmpToken.GTH;
    }
    if (tok !is OpCmpToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  bool parseUniqueOperator() {
    bool tok = false;
    if (srcCursor <= CST.length - 6) {
      if (CST[srcCursor..srcCursor+6] == "unique") {
	tok = true;
	srcCursor += 6;
      }
    }
    return tok;
  }

  OpLogicToken parseLogicOperator() {
    OpLogicToken tok = OpLogicToken.NONE;
    if (srcCursor <= CST.length - 2) {
      if (CST[srcCursor] == '-' && CST[srcCursor+1] == '>') tok = OpLogicToken.LOGICIMP;
      if (CST[srcCursor] == '&' && CST[srcCursor+1] == '&') tok = OpLogicToken.LOGICAND;
      if (CST[srcCursor] == '|' && CST[srcCursor+1] == '|') tok = OpLogicToken.LOGICOR;
    }
    if (tok !is OpLogicToken.NONE) {
      srcCursor += 2;
      return tok;
    }
    if (srcCursor <= CST.length - 1) {
      if (CST[srcCursor] == '[') tok = OpLogicToken.INDEX;
    }
    if (tok !is OpLogicToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  OpToken parseOperator() {
    OpToken tok = OpToken.NONE;
    if (srcCursor < CST.length - 1) {
      if (CST[srcCursor] == '<' && CST[srcCursor+1] == '<') tok = OpToken.LSH;
      if (CST[srcCursor] == '>' && CST[srcCursor+1] == '>') tok = OpToken.RSH;
      if (CST[srcCursor] == '=' && CST[srcCursor+1] == '=') tok = OpToken.EQU;
      if (CST[srcCursor] == '>' && CST[srcCursor+1] == '=') tok = OpToken.GTE;
      if (CST[srcCursor] == '<' && CST[srcCursor+1] == '=') tok = OpToken.LTE;
      if (CST[srcCursor] == '!' && CST[srcCursor+1] == '=') tok = OpToken.NEQ;
      if (CST[srcCursor] == '&' && CST[srcCursor+1] == '&') tok = OpToken.LOGICAND;
      if (CST[srcCursor] == '|' && CST[srcCursor+1] == '|') tok = OpToken.LOGICOR;
      if (CST[srcCursor] == '-' && CST[srcCursor+1] == '>') tok = OpToken.LOGICIMP;
      if (CST[srcCursor] == '.' && CST[srcCursor+1] == '.') tok = OpToken.SLICE;
    }
    if (tok !is OpToken.NONE) {
      srcCursor += 2;
      return tok;
    }
    if (srcCursor < CST.length) {
      if (CST[srcCursor] == '&') tok = OpToken.AND;
      if (CST[srcCursor] == '|') tok = OpToken.OR;
      if (CST[srcCursor] == '^') tok = OpToken.XOR;
      if (CST[srcCursor] == '+') tok = OpToken.ADD;
      if (CST[srcCursor] == '-') tok = OpToken.SUB;
      if (CST[srcCursor] == '*') tok = OpToken.MUL;
      if (CST[srcCursor] == '/') tok = OpToken.DIV;
      if (CST[srcCursor] == '%') tok = OpToken.REM;
      if (CST[srcCursor] == '<') tok = OpToken.LTH;
      if (CST[srcCursor] == '>') tok = OpToken.GTH;
      // if (CST[srcCursor] == '[') tok = OpToken.INDEX;
      // if (CST[srcCursor] == ';') tok = OpToken.END;
    }
    if (tok !is OpToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  void errorToken() {
    import std.conv;
    size_t start = srcCursor;
    while (srcCursor < CST.length) {
      char c = CST[srcCursor];
      if (c !is ' ' && c !is '\n' && c !is '\t' && c !is '\r' && c !is '\f') {
	++srcCursor;
      }
      else break;
    }
    if (srcCursor == start) {
      assert (false, "EOF while parsing!");
    }
    assert (false, "Unrecognized token: " ~ "'" ~
	    CST[start..srcCursor] ~ "' -- at: " ~ srcCursor.to!string);
  }

  uint parseSoftAttr() {
    import std.conv: to;
    int softAttr = 0;
    if (srcCursor < CST.length) {
      char c = CST[srcCursor];
      if (c == '@') {
	++srcCursor;
      }
      else {
	return 0;
      }
    }
    size_t srcTag = parseIdentifier();
    if (CST[srcTag..srcCursor] != "soft") {
      import std.conv: to;
      assert (false, "Unknown Attribute " ~ CST[srcTag..srcCursor] ~ " at " ~ srcTag.to!string);
    }
    else {
      softAttr = 1;
    }

    srcTag = parseSpace();
    // fill(CST[srcTag..srcCursor]);
    
    if (srcCursor < CST.length && CST[srcCursor] == '!') {
      ++srcCursor;
    
      srcTag = parseSpace();

      srcTag = srcCursor;

      while (srcCursor < CST.length) {
	char c = CST[srcCursor];
	if ((c >= '0' && c <= '9') ||
	    (c == '_')) {
	  ++srcCursor;
	}
	else {
	  break;
	}
      }

      if (srcTag == srcCursor) {	// no number found
	assert(false, "Expecting a numeral after @soft!");
      }
      else {
	softAttr = CST[srcTag..srcCursor].to!uint;
      }
    }
    
    return softAttr;
  }

  size_t parseIdentifier() {
    size_t start = srcCursor;
    if (srcCursor < CST.length) {
      char c = CST[srcCursor];
      if ((c >= 'A' && c <= 'Z') ||
	  (c >= 'a' && c <= 'z') ||
	  (c == '_')) {
	++srcCursor;
      }
      else {
	return start;
      }
    }
    while (srcCursor < CST.length) {
      char c = CST[srcCursor];
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

  bool parseMappedChain(string mapped, ref int cursor) {
    if (cursor >= mapped.length) return false;
    while (cursor < mapped.length && mapped[cursor] != '.') cursor += 1;
    return true;
  }

  size_t procIdentifier() {
    // parse an identifier and the following '.' heirarcy if any
    auto start = srcCursor;
    auto srcTag = srcCursor;
    
    parseSpace();

    fill(CST[srcTag..srcCursor]);

    srcTag = srcCursor;
    parseIdentifier();

    if (srcCursor != srcTag) {	// some identifier
      fill("_esdl__sym!(");
      string mapped;
      int mappedCursor = 0;
      int mappedPrevCursor = 0;
      int indx = idMatch(CST[srcTag..srcCursor]);
      if (indx == -1) {
	fill(CST[srcTag..srcCursor]);
	fillDeclaration(CST[srcTag..srcCursor]);
      }
      else {
	mapped = varMap[indx].xLat;
	parseMappedChain(mapped, mappedCursor);
	fill(mapped[0..mappedCursor]);
	fillDeclaration(varMap[indx].xLatBase);
	mappedPrevCursor = ++mappedCursor;
      }
      fill(")(\"");
      fill(CST[srcTag..srcCursor]);
      fill("\", this.outer)");
      while (parseMappedChain(mapped, mappedCursor)) {
	fill("._esdl__dot!(\"");
	fill(mapped[mappedPrevCursor..mappedCursor]);
	fill("\")");
	mappedPrevCursor = ++mappedCursor;
      }

      while (true) {
	srcTag = srcCursor;
	parseSpace();
	fill(CST[srcTag..srcCursor]);
	srcTag = srcCursor;
	if (CST[srcCursor] == '.' &&
	    srcCursor + 1 < CST.length &&
	    CST[srcCursor+1] != '.' // that woucd be range expression
	    ) {
	  fill(CST[srcTag..srcCursor]);
	  srcCursor += 1;
	  srcTag = srcCursor;
	  parseSpace();
	  srcTag = srcCursor;
	  fill(CST[srcTag..srcCursor]);
	  fill("._esdl__dot!(\"");
	  srcTag = srcCursor;
	  parseIdentifier();
	  fill(CST[srcTag..srcCursor]);
	  fill("\")");
	  continue;
	}
	else if (CST[srcCursor] == '[') {
	  fill(CST[srcTag..srcCursor]);
	  fill("[");
	  srcCursor += 1;
	  srcTag = srcCursor;
	  procIndexExpr(srcCursor);
	  srcTag = srcCursor;
	  parseSpace();
	  fill(CST[srcTag..srcCursor]);
	  srcTag = srcCursor;
	  if (CST[srcCursor] == ']') {
	    fill("]");
	    srcCursor += 1;
	  }
	  else {
	    assert (false, "Unrecognized token: " ~ "--> " ~
		    CST[srcCursor..$]);
	  }
	  continue;
	}
	else {
	  srcCursor = srcTag;
	  break;
	}
      }
      
    }
    else {
      srcTag = parseLiteral();
      if (srcCursor > srcTag) {
	fill("_esdl__sym!(");
	fill(CST[srcTag..srcCursor]);
	fillDeclaration(CST[srcTag..srcCursor]);
	fill(")(\"");
	fill(CST[start..srcCursor]);
	fill("\", this.outer)");
      }
      else {
	srcTag = parseWithArg();
	if (srcCursor > srcTag) {
	  fill("_esdl__arg_proxy(\"");
	  // fill("_esdl__arg!");
	  // fill(CST[srcTag+1..srcCursor]);
	  // fill("()");
	  // fill(")(\"");
	  fill(CST[start..srcCursor]);
	  fill("\", _esdl__arg!");
	  fill(CST[srcTag+1..srcCursor]);
	  fill("(), this.outer)");
	}
	else {
	  errorToken();
	}
      }
    }
    return start;
  }

  size_t parseLineComment() {
    size_t start = srcCursor;
    if (srcCursor >= CST.length - 2 ||
	CST[srcCursor] != '/' || CST[srcCursor+1] != '/') return start;
    else {
      srcCursor += 2;
      while (srcCursor < CST.length) {
	if (CST[srcCursor] == '\n') {
	  break;
	}
	else {
	  if (srcCursor == CST.length) {
	    // commment unterminated
	    assert (false, "Line comment not terminated");
	  }
	}
	srcCursor += 1;
      }
      srcCursor += 1;
      return start;
    }
  }

  unittest {
    size_t curs = 4;
    assert (parseLineComment("Foo // Bar;\n\n", curs) == 8);
    assert (curs == 12);
  }

  size_t parseBlockComment() {
    size_t start = srcCursor;
    if (srcCursor >= CST.length - 2 ||
	CST[srcCursor] != '/' || CST[srcCursor+1] != '*') return start;
    else {
      srcCursor += 2;
      while (srcCursor < CST.length - 1) {
	if (CST[srcCursor] == '*' && CST[srcCursor+1] == '/') {
	  break;
	}
	else {
	  if (srcCursor == CST.length - 1) {
	    // commment unterminated
	    assert (false, "Block comment not terminated");
	  }
	}
	srcCursor += 1;
      }
      srcCursor += 2;
      return start;
    }
  }

  unittest {
    size_t curs = 4;
    assert (parseBlockComment("Foo /* Bar;\n\n */", curs) == 4);
    assert (curs == 16);
  }

  size_t parseNestedComment() {
    size_t nesting = 0;
    size_t start = srcCursor;
    if (srcCursor >= CST.length - 2 ||
	CST[srcCursor] != '/' || CST[srcCursor+1] != '+') return start;
    else {
      srcCursor += 2;
      while (srcCursor < CST.length - 1) {
	if (CST[srcCursor] == '/' && CST[srcCursor+1] == '+') {
	  nesting += 1;
	  srcCursor += 1;
	}
	else if (CST[srcCursor] == '+' && CST[srcCursor+1] == '/') {
	  if (nesting == 0) {
	    break;
	  }
	  else {
	    nesting -= 1;
	    srcCursor += 1;
	  }
	}
	srcCursor += 1;
	if (srcCursor >= CST.length - 1) {
	  // commment unterminated
	  assert (false, "Block comment not terminated");
	}
      }
      srcCursor += 2;
      return start;
    }
  }

  unittest {
    size_t curs = 4;
    parseNestedComment("Foo /+ Bar;/+// \n+/+*/ +/", curs);
    assert (curs == 25);
  }

  size_t parseLiteral() {
    size_t start = srcCursor;
    // look for 0b or 0x
    if (srcCursor + 2 <= CST.length &&
	CST[srcCursor] == '0' &&
	(CST[srcCursor+1] == 'x' ||
	 CST[srcCursor+1] == 'X')) { // hex numbers
      srcCursor += 2;
      while (srcCursor < CST.length) {
	char c = CST[srcCursor];
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
    else if (srcCursor + 2 <= CST.length &&
	     CST[srcCursor] == '0' &&
	     (CST[srcCursor+1] == 'b' ||
	      CST[srcCursor+1] == 'B')) { // binary numbers
      srcCursor += 2;
      while (srcCursor < CST.length) {
	char c = CST[srcCursor];
	if ((c == '0' || c == '1' || c == '_')) {
	  ++srcCursor;
	}
	else {
	  break;
	}
      }
    }
    else {			// decimals
      while (srcCursor < CST.length) {
	char c = CST[srcCursor];
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
      while (srcCursor < CST.length) {
	char c = CST[srcCursor];
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

  size_t parseWithArg() {
    size_t start = srcCursor;
    if (srcCursor < CST.length &&
	CST[srcCursor] == '$') {
      ++srcCursor;
    }
    else return start;
    while (srcCursor < CST.length) {
      char c = CST[srcCursor];
      if ((c >= '0' && c <= '9')) {
	++srcCursor;
      }
      else {
	break;
      }
    }
    return start;
  }

  unittest {
    size_t curs = 4;
    assert (parseIdentifier("Foo Bar;", curs) == 0);
    assert (curs == 7);
  }


  size_t parseWhiteSpace() {
    auto start = srcCursor;
    while (srcCursor < CST.length) {
      auto c = CST[srcCursor];
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

  size_t parseLeftParens() {
    auto start = srcCursor;
    while (srcCursor < CST.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if (srcCursor > srcTag) {
	continue;
      }
      else {
	if (srcCursor < CST.length && CST[srcCursor] == '(') {
	  ++numParen;
	  ++srcCursor;
	  continue;
	}
	else {
	  break;
	}
      }
    }
    return start;
  }

  // move all the characters in the output puffer forward by one position
  // find the balanced paren -- upto the start anchor and insert a paren at
  // that position
  void insertOpeningParen(size_t startAnchor) {
    fill(' ');			// to create an extra position
    if (!dryRun) {
      int parenCount = 0;
      size_t cursor;
      for (cursor=outCursor-1; cursor != startAnchor; --cursor) {
	outBuffer[cursor] = outBuffer[cursor-1];
	if (outBuffer[cursor] == '(' && parenCount == 0) {
	  break;
	}
	if (outBuffer[cursor] == ')') parenCount += 1;
	if (outBuffer[cursor] == '(') parenCount -= 1;
      }
      outBuffer[cursor] = '(';
    }
  }

  // Parse parenthesis on the right hand side. But stop if and when
  // the numParen has already hit zero. This is important since for if
  // conditional we want to know where to stop parsing.
  size_t parseRightParens() {
    auto start = srcCursor;
    while (srcCursor < CST.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if (srcCursor > srcTag) {
	continue;
      }
      else {
	if (srcCursor < CST.length && CST[srcCursor] == ')') {
	  if (numParen is 0) break;
	  --numParen;
	  ++srcCursor;
	  continue;
	}
	if (srcCursor < CST.length && CST[srcCursor] == ']') {
	  if (numIndex is 0) break;
	  indexTag.length -= 1;
	  --numIndex;
	  ++srcCursor;
	  continue;
	}
	else {
	  break;
	}
      }
    }
    
    return start;
  }

  size_t moveToRightParens(size_t init=0) {
    auto start = srcCursor;
    while (srcCursor < CST.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if (srcCursor > srcTag) {
	fill(CST[srcTag..srcCursor]);
	continue;
      }
      else {
	if (srcCursor < CST.length && CST[srcCursor] == ')') {
	  if (numParen is init) break;
	  --numParen;
	  ++srcCursor;
	  fill(')');
	  continue;
	}
	if (srcCursor < CST.length && CST[srcCursor] == ']') {
	  if (numIndex is 0) break;
	  --numIndex;
	  ++srcCursor;
	  fill(')');
	  continue;
	}
	else {
	  break;
	}
      }
    }
    
    return start;
  }  

  size_t parseSpace() {
    auto start = srcCursor;
    while (srcCursor < CST.length) {
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

  unittest {
    size_t curs = 0;
    assert (parseLeftParens("    // foo\nFoo Bar;", curs) == 11);
    assert (curs == 11);
  }

  char[] translate(string proxy, string name) {
    _proxy = proxy;
    translateBlock(name);
    setupBuffer();
    translateBlock(name);
    return outBuffer;
  }

  void translateBlock(string name) {
    // string blockName;
    import std.conv: to;
    fill("// Constraint @ File: " ~ FILE ~ " Line: " ~ LINE.to!string ~ "\n\n");
    if (name == "") {
      fill("override CstBlock makeCstBlock() {\n"//  ~
	   // "\n  auto cstExpr = new CstBlock;\n"
	   );
      // blockName = "_esdl__cst_block";
    }
    else {
      fill("CstBlock _esdl__cst_func_" ~ name ~ "() {\n"//  ~
	   // "\n  auto cstExpr = new CstBlock;\n"
	   );
      // blockName = "_esdl__cst_block_" ~ name;
    }

    // fill("  if (" ~ blockName ~ " !is null) return " ~
    // 	 blockName ~ ";\n");

    fill("  CstBlock _esdl__block = new CstBlock();\n");

    procBlock();
    // fill("  " ~ blockName ~ " = _esdl__block;\n");
    fill("  return _esdl__block;\n}\n");
  }

  int idMatch(string id) {
    foreach (i, var; varMap) {
      if (var.varName == id) return cast(int) i;
    }
    return -1;
  }

  // Variable translation map
  struct VarPair {
    string varName;
    string xLat;
    string xLatBase;
  }

  struct Condition {
    bool _inverse = false;
    string _cond;
    this(string cond) {
      _cond = cond;
    }
    string cond() {
      return _cond;
    }
    void switchToElse() {
      _inverse = true;
    }
    bool isInverse() {
      return _inverse;
    }
  }

  void procForeachBlock() {
    string index;
    string elem;
    string array;
    string arrayBase;
    size_t srcTag;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    srcTag = parseIdentifier();
    if (CST[srcTag..srcCursor] != "foreach") {
      import std.conv: to;
      assert (false, "Not a FOREACH block at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (CST[srcCursor] != '(') {
      errorToken();
    }

    ++srcCursor;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    // Parse the index
    srcTag = parseIdentifier();
    if (srcCursor > srcTag) {
      // FIXME -- check if the variable names do not shadow earlier
      // names in the table
      index = CST[srcTag..srcCursor];

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      if (CST[srcCursor] == ';') {
	elem = index;
	index = "";
      }
      else if (CST[srcCursor] != ',') {
	errorToken();
      }
      ++srcCursor;

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
    }
    else {
      errorToken();
    }

    // Parse elem
    if (elem.length is 0) {
      srcTag = parseIdentifier();
      if (srcCursor > srcTag) {
	// FIXME -- check if the variable names do not shadow earlier
	// names in the table
	elem = CST[srcTag..srcCursor];

	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);

	if (CST[srcCursor] != ';') {
	  errorToken();
	}
	++srcCursor;

	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
      }
      else {
	errorToken();
      }
    }

    // Parse array
    srcTag = parseIdentifier();
    if (srcCursor > srcTag) {
      // FIXME -- check if the variable names do not shadow earlier
      // names in the table
      array = CST[srcTag..srcCursor];
      arrayBase = CST[srcTag..srcCursor];
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
      if (CST[srcCursor] != ')') {
	errorToken();
      }
      ++srcCursor;
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
    }
    else {
      errorToken();
    }

    int indx = idMatch(array);
    if (indx != -1) {
      array = varMap[indx].xLat;
      arrayBase = varMap[indx].xLatBase;
    }

    // add index
    iterators ~= array ~ "._esdl__iter";
    
    if (index.length != 0) {
      VarPair x;
      x.varName  = index;
      x.xLat     = array ~ "._esdl__iter";
      x.xLatBase = arrayBase;
      varMap ~= x;
    }

    VarPair x;
    x.varName  = elem;
    x.xLat     = array ~ "._esdl__elems";
    x.xLatBase = arrayBase;
    varMap ~= x;

    // start of foreach
    // fill("    // Start of Foreach: " ~ array ~ ".iterator() \n");
    fill("    " ~ _proxy ~ ".pushScope(" ~ array ~ "._esdl__iter);\n");
    if (CST[srcCursor] is '{') {
      ++srcCursor;
      procBlock();
    }
    else {
      procStmt();
    }

    fill("    " ~ _proxy ~ ".popScope();\n");
    // fill("    // End of Foreach \n");
    
    iterators = iterators[0..$-1];

    if (index.length != 0) {
      varMap = varMap[0..$-2];
    }
    else {
      varMap = varMap[0..$-1];
    }

  }

  void procIfBlock() {
    size_t srcTag;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    srcTag = parseIdentifier();
    if (CST[srcTag..srcCursor] != "if") {
      import std.conv: to;
      assert (false, "Not a IF block at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (CST[srcCursor] != '(') {
      errorToken();
    }

    ++srcCursor;

    fill("/* IF Block: ");
    auto outTag = outCursor;
    procLogicExpr();

    if (dryRun) {
      dummy.length = outCursor-outTag;
      Condition ifCond = dummy;
      ifConds ~= ifCond;
    }
    else {
      Condition ifCond = Condition(cast(string) outBuffer[outTag..outCursor]);
      ifConds ~= ifCond;
    }

    fill("*/\n");

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);
    if (CST[srcCursor] != ')') {
      errorToken();
    }
    ++srcCursor;
    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (CST[srcCursor] is '{') {
      ++srcCursor;
      procBlock();
    }
    else {
      procStmt();
    }

    // In case there is an else clause
    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    srcTag = parseIdentifier();
    if (CST[srcTag..srcCursor] != "else") { // no else
      srcCursor = srcTag;		   // revert the cursor
      ifConds = ifConds[0..$-1];
      return;
    }
    else {
      fill("// Else \n");
      ifConds[$-1].switchToElse();

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      if (CST[srcCursor] is '{') {
	++srcCursor;
	procBlock();
      }
      else {
	procStmt();
      }

      ifConds = ifConds[0..$-1];
    }
  }

  void procBeforeStmt() {
    size_t srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    srcTag = parseIdentifier();
    if (CST[srcTag..srcCursor] != "solve") {
      import std.conv: to;
      assert (false, "Not a solve statement at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    procIdentifier();

    fill(".solveBefore(");
    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    srcTag = parseIdentifier();
    if (CST[srcTag..srcCursor] != "before") {
      import std.conv: to;
      assert (false, "Expected keyword \"before\" at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    procIdentifier();

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (CST[srcCursor++] !is ';') {
      assert (false, "Error: -- ';' missing at end of statement; at " ~
	      srcCursor.to!string);
    }

    fill(");\n");
  }

  enum StmtToken: byte
  {   STMT    = 0,
      FOREACH,
      IFCOND,
      ENDCST,		// end of text
      BEFORE,
      BLOCK,
      ENDBLOCK,
      // ANYTHING ELSE COMES HERE

      ERROR,
      }

  // Just return whether the next statement is a normal statement
  // FOREACH or IFCOND etc
  StmtToken nextStmtToken() {
    auto savedCursor = srcCursor;
    auto savedParen  = numParen;
    scope(exit) {
      srcCursor = savedCursor; // restore
      numParen  = savedParen; // restore
    }

    size_t srcTag;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (srcCursor == CST.length) return StmtToken.ENDCST;
    srcTag = parseLeftParens();
    // if a left parenthesis has been found at the beginning it can only
    // be a normal statement
    if (srcCursor > srcTag) return StmtToken.STMT;

    if ((CST[srcCursor] >= 'A' && CST[srcCursor] <= 'Z') ||
	(CST[srcCursor] >= 'a' && CST[srcCursor] <= 'z') ||
	(CST[srcCursor] == '_')) {
	
      srcTag = parseIdentifier();
      if (srcCursor > srcTag) {
	if (CST[srcTag..srcCursor] == "foreach") return StmtToken.FOREACH;
	if (CST[srcTag..srcCursor] == "if") return StmtToken.IFCOND;
	if (CST[srcTag..srcCursor] == "solve") return StmtToken.BEFORE;
	// not a keyword
	return StmtToken.STMT;
      }
    }
    if (CST[srcCursor] is '{') return StmtToken.BLOCK;
    if (CST[srcCursor] is '}') return StmtToken.ENDBLOCK;
    return StmtToken.STMT;
    // return StmtToken.ERROR;
  }


  void procArithSubExpr() {
    auto savedNumIndex = numIndex;
    auto savedNumParen = numParen;
    numIndex = 0;
    numParen = 0;
    procArithExpr();
    numIndex = savedNumIndex;
    numParen = savedNumParen;
  }

  void procInsideElem() {
    auto savedNumIndex = numIndex;
    auto savedNumParen = numParen;
    numIndex = 0;
    numParen = 0;
    procRangeTerm("inside_");
    numIndex = savedNumIndex;
    numParen = savedNumParen;
  }

  void procUniqueElem() {
    auto savedNumIndex = numIndex;
    auto savedNumParen = numParen;
    numIndex = 0;
    numParen = 0;
    procUniqueTerm();
    numIndex = savedNumIndex;
    numParen = savedNumParen;
  }

  void procDistRangeExpr() {
    auto savedNumIndex = numIndex;
    auto savedNumParen = numParen;
    numIndex = 0;
    numParen = 0;
    procRangeTerm("dist_");
    numIndex = savedNumIndex;
    numParen = savedNumParen;
  }

  void procIndexExpr(size_t cursor) {
    auto savedCursor = srcCursor;
    auto savedNumIndex = numIndex;
    auto savedNumParen = numParen;
    srcCursor = cursor;
    numIndex = 0;
    numParen = 0;
    procRangeTerm("index_");
    numIndex = savedNumIndex;
    numParen = savedNumParen;
    // srcCursor = savedCursor;
  }

  bool procArithExpr() {
    bool identOnly = true;
    size_t startNumParen = numParen;
    size_t srcTag = 0;
    size_t startAnchor = outCursor;
    // true in the beginning of the expression or just after a start of parenthesis
    // bool unaryLegal = true;
    while (srcCursor < CST.length) {
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      if (srcCursor == CST.length) break;

      // Parse any left braces now
      srcTag = parseLeftParens();
      // if (srcCursor > srcTag) unaryLegal = true;
      fill(CST[srcTag..srcCursor]);

      // Parse any unary operators
      // if (unaryLegal) {
      auto uTok = parseUnaryArithOperator();
      final switch(uTok) {
      case OpUnaryArithToken.NEG: fill('-');
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	srcTag = srcCursor;
	identOnly = false;
	procArithExpr();
	break;
      case OpUnaryArithToken.INV: fill('~');
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	srcTag = srcCursor;
	identOnly = false;
	procArithExpr();
	break;
      case OpUnaryArithToken.NONE:
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	srcTag = procIdentifier();
	break;
      }
      // }
      // unaryLegal = false;

      // fillDeclaration(CST[srcTag..srcCursor]);
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
      srcTag = moveToRightParens();
      
      // fill(CST[srcTag..srcCursor]);

      srcTag = srcCursor;
      OpArithToken opToken = parseArithOperator();

      final switch(opToken) {
      case OpArithToken.NONE:
	return identOnly;
	// break;
      case OpArithToken.AND:
	fill(" & ");
	break;
      case OpArithToken.OR:
	fill(" | ");
	break;
      case OpArithToken.XOR:
	fill(" ^ ");
	break;
      case OpArithToken.ADD:
	fill(" + ");
	break;
      case OpArithToken.SUB:
	fill(" - ");
	break;
      case OpArithToken.MUL:
	fill(" * ");
	break;
      case OpArithToken.DIV:
	fill(" / ");
	break;
      case OpArithToken.REM:
	fill(" % ");
	break;
      case OpArithToken.LSH:
	fill(" << ");
	break;
      case OpArithToken.RSH:
	fill(" >> ");
	break;
      case OpArithToken.SLICE:
	assert(false); // FIXME
      }
      identOnly = false;
    }
    return false;
  }

  void procRangeTerm(string prefix) {
    size_t srcTag = 0;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    // LHS
    if (srcCursor < CST.length) {
      // size_t openingParenAnchor = fill(' ');
      size_t startAnchor = outCursor;
      srcTag = srcCursor;
      procArithExpr();
      if (srcTag == srcCursor) {
	assert(false, "Expecting an expression, got none");
      }

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      srcTag = srcCursor;
      OpRangeToken opToken = parseRangeOperator();

      insertOpeningParen(startAnchor);

      final switch(opToken) {
      case OpRangeToken.RANGE:
	fill(")._esdl__");
	fill(prefix);
	fill("range(");
	break;
      case OpRangeToken.RANGEINC:
	fill(")._esdl__");
	fill(prefix);
	fill("rangeinc(");
	break;
      case OpRangeToken.NONE:
	fill(")._esdl__");
	fill(prefix);
	fill("range(null)");
	return;
      }
      // RHS
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      srcTag = srcCursor;
      procArithExpr();
      if (srcTag == srcCursor) {
	assert(false, "Expecting an arithmatic expression on RHS, got none");
      }
      fill(')');
    }
  }

  void procUniqueTerm() {
    size_t srcTag = 0;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    // LHS
    if (srcCursor < CST.length) {
      // size_t openingParenAnchor = fill(' ');
      // size_t startAnchor = outCursor;
      srcTag = srcCursor;
      fill("_esdl__unique_elem(");
      procArithExpr();
      fill(")");
      if (srcTag == srcCursor) {
	assert(false, "Expecting an expression, got none");
      }

    }
  }

  void procDistContainer() {
    size_t srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (srcCursor < CST.length && CST[srcCursor] == '[') {
      fill('[');
      srcCursor += 1;
      while (srcCursor < CST.length) {
	procDistRangeExpr();
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	OpDistToken token = parseDistOperator();
	final switch(token) {
	case OpDistToken.ITEMWISE:
	  fill("._esdl__itemWeight(");
	  break;
	case OpDistToken.RANGEWISE:
	  fill("._esdl__rangeWeight(");
	  break;
	case OpDistToken.NONE:
	  assert(false, "Expected dist weight operator in dist constraint");
	}
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	srcTag = srcCursor;
	procArithSubExpr();
	if (srcTag == srcCursor) {
	  assert(false, "Expecting a weight value in dist expression, got none");
	}
	fill(')');
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	if (srcCursor < CST.length && CST[srcCursor] == ',') {
	  srcCursor += 1;
	  fill(',');
	  continue;
	}
	else if (srcCursor < CST.length && CST[srcCursor] == ']') {
	  fill(']');
	  srcCursor += 1;
	  break;
	}
	else {
	  assert (false, "Unexpected token found: " ~ CST[srcCursor]);
	}
      }
    }
    else {
      assert (false, "[ expected after 'inside', found: " ~ CST[srcCursor]);
    }
  }
  
  void procInsideSetContainer() {
    size_t srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (srcCursor < CST.length && CST[srcCursor] == '[') {
      fill('[');
      srcCursor += 1;
      while (srcCursor < CST.length) {
	procInsideElem();
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	if (srcCursor < CST.length && CST[srcCursor] == ',') {
	  srcCursor += 1;
	  fill(',');
	  continue;
	}
	else if (srcCursor < CST.length && CST[srcCursor] == ']') {
	  fill(']');
	  srcCursor += 1;
	  break;
	}
	else {
	  assert (false, "Unexpected token found: " ~ CST[srcCursor]);
	}
      }
    }
    else {
      assert (false, "[ expected after 'inside', found: " ~ CST[srcCursor]);
    }
  }

  void procUniqueSetContainer() {
    size_t srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (srcCursor < CST.length && CST[srcCursor] == '[') {
      fill('[');
      srcCursor += 1;
      while (srcCursor < CST.length) {
	procUniqueElem();
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	if (srcCursor < CST.length && CST[srcCursor] == ',') {
	  srcCursor += 1;
	  fill(',');
	  continue;
	}
	else if (srcCursor < CST.length && CST[srcCursor] == ']') {
	  fill(']');
	  srcCursor += 1;
	  break;
	}
	else {
	  assert (false, "Unexpected token found: " ~ CST[srcCursor]);
	}
      }
    }
    else {
      assert (false, "[ expected after 'unique', found: " ~ CST[srcCursor]);
    }
  }

  enum VEC2BOOL: byte  {COMPARE, INSIDE, DIST}
  
  bool procCmpExpr() {
    size_t srcTag = 0;

    VEC2BOOL opType = VEC2BOOL.COMPARE;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    // LHS
    if (srcCursor < CST.length) {
      // size_t openingParenAnchor = fill(' ');
      size_t startAnchor = outCursor;
      srcTag = srcCursor;
      bool identOnly = procArithExpr();

      if (srcTag == srcCursor) {
	assert(false, "Expecting an expression, got none");
      }

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      srcTag = srcCursor;
      OpCmpToken opToken = parseCmpOperator();

      final switch(opToken) {
      case OpCmpToken.EQU:
	insertOpeningParen(startAnchor);
	fill(")._esdl__equ(");
	break;
      case OpCmpToken.NEQ:
	insertOpeningParen(startAnchor);
	fill(")._esdl__neq(");
	break;
      case OpCmpToken.LTE:
	insertOpeningParen(startAnchor);
	fill(")._esdl__lte(");
	break;
      case OpCmpToken.GTE:
	insertOpeningParen(startAnchor);
	fill(")._esdl__gte(");
	break;
      case OpCmpToken.LTH:
	insertOpeningParen(startAnchor);
	fill(")._esdl__lth(");
	break;
      case OpCmpToken.GTH:
	insertOpeningParen(startAnchor);
	fill(")._esdl__gth(");
	break;
      case OpCmpToken.INSIDE:
	insertOpeningParen(startAnchor);
	opType = VEC2BOOL.INSIDE;
	fill(")._esdl__inside(");
	break;
      case OpCmpToken.NOTINSIDE:
	insertOpeningParen(startAnchor);
	opType = VEC2BOOL.INSIDE;
	fill(")._esdl__notinside(");
	break;
      case OpCmpToken.DIST:
	insertOpeningParen(startAnchor);
	opType = VEC2BOOL.DIST;
	fill(")._esdl__dist(");
	break;
      case OpCmpToken.NONE:
	fill("._esdl__bool()");
	return true;
      }
      // RHS
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      srcTag = srcCursor;
      final switch(opType) {
      case VEC2BOOL.COMPARE:
	procArithExpr();
	if (srcTag == srcCursor) {
	  assert(false, "Expecting an arithmatic expression on RHS, got none");
	}
	break;
      case VEC2BOOL.INSIDE:
	procInsideSetContainer();
	if (srcTag == srcCursor) {
	  assert(false, "Expecting a set container on RHS, got none");
	}
	break;
      case VEC2BOOL.DIST:
	procDistContainer();
	if (srcTag == srcCursor) {
	  assert(false, "Expecting a dist container on RHS, got none");
	}
	break;
      }
      fill(')');
      return true;
    }
    else {
      return false;
    }
  }

  bool procUniqueExpr() {
    // return false;
    size_t srcTag = 0;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    // LHS
    if (srcCursor < CST.length) {
      // size_t openingParenAnchor = fill(' ');
      size_t startAnchor = outCursor;
      srcTag = srcCursor;

      bool tok = parseUniqueOperator();

      if (tok is false) {
	return false;
      }

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      fill("_esdl__unique(");

      procUniqueSetContainer();
      if (srcTag == srcCursor) {
	assert(false, "Expecting a set container on RHS, got none");
      }

      fill(')');
      return true;
    }
    else {
      return false;
    }
  }
  
  void procLogicExpr() {
    size_t startNumParen = numParen;
    size_t srcTag = 0;
    // true in the beginning of the expression or just after a start of parenthesis
    while (srcCursor < CST.length) {
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      if (srcCursor == CST.length) break;

      // Parse any left braces now
      srcTag = parseLeftParens();
      // if (srcCursor > srcTag) unaryLegal = true;
      fill(CST[srcTag..srcCursor]);

      // Parse any unary operators
      // if (unaryLegal) {
      auto uTok = parseUnaryLogicOperator();
      final switch(uTok) {
      case OpUnaryLogicToken.NOT: fill('*');
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	srcTag = srcCursor;
	procLogicExpr();
	break;
      case OpUnaryLogicToken.NONE:
	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);
	// srcTag = srcCursor;
	if (procUniqueExpr() == true) {
	  break;
	}
	else if (procCmpExpr() == true) {
	  break;
	}
	else {
	  assert(false, "Expecting an expression, got none");
	}
	// srcTag = procIdentifier();
      }
      // }
      // unaryLegal = false;

      // fillDeclaration(CST[srcTag..srcCursor]);
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
      srcTag = moveToRightParens();
      
      // srcTag = srcCursor;
      // procCmpExpr();
      // if (srcTag == srcCursor) {
      // 	assert(false, "Expecting an expression, got none");
      // }
      
      srcTag = srcCursor;
      OpLogicToken opToken = parseLogicOperator();

      final switch(opToken) {
      case OpLogicToken.NONE:
	return;
	// break;
      case OpLogicToken.LOGICIMP:
	fill(" >>>= ");
	break;
      case OpLogicToken.LOGICAND:
	fill(" & ");
	break;
      case OpLogicToken.LOGICOR:
	fill(" | ");
	break;
      case OpLogicToken.INDEX:
	assert(false); // FIXME
      }
    }
  }

  // void procExpr() {
  //   bool impRHS;
  //   bool orRHS;
  //   bool andRHS;
  //   bool cmpRHS;

  //   size_t srcTag = 0;

  //   size_t impDstAnchor = fill(' ');
  //   size_t orDstAnchor  = fill(' ');
  //   size_t andDstAnchor = fill(' ');
  //   size_t cmpDstAnchor = fill(' ');

  // loop:
  //   while (srcCursor < CST.length) {
  //     srcTag = parseSpace();
  //     fill(CST[srcTag..srcCursor]);

  //     if (srcCursor == CST.length) break;

  //     // Parse any left braces now
  //     srcTag = parseLeftParens();
  //     fill(CST[srcTag..srcCursor]);

  //     // Parse any unary operators
  //     auto uTok = parseUnaryArithOperator();
  //     final switch(uTok) {
  //     case OpUnaryArithToken.NEG: fill('-'); continue loop;
  //     case OpUnaryArithToken.INV: fill('~'); continue loop;
  //     case OpUnaryArithToken.NONE: break;
  //     }
  //     srcTag = parseSpace();
  //     fill(CST[srcTag..srcCursor]);
  //     srcTag = procIdentifier();
  //     // fillDeclaration(CST[srcTag..srcCursor]);
  //     srcTag = parseSpace();
  //     fill(CST[srcTag..srcCursor]);
  //     srcTag = moveToRightParens();
      
  //     // fill(CST[srcTag..srcCursor]);

  //     srcTag = srcCursor;
  //     OpToken opToken = parseOperator();

  //     final switch(opToken) {
  //     case OpToken.NONE:
  // 	//   errorToken();
  // 	//   break;
  // 	// case OpToken.END:
  // 	if (cmpRHS is true) {
  // 	  fill(')');
  // 	  cmpRHS = false;
  // 	}
  // 	if (andRHS is true) {
  // 	  fill(')');
  // 	  andRHS = false;
  // 	}
  // 	if (orRHS is true) {
  // 	  fill(')');
  // 	  orRHS = false;
  // 	}
  // 	if (impRHS is true) {
  // 	  fill(')');
  // 	  impRHS = false;
  // 	}
  // 	return;
  // 	// break;
  //     case OpToken.LOGICIMP:
  // 	if (cmpRHS is true) {
  // 	  fill(')');
  // 	  cmpRHS = false;
  // 	}
  // 	if (andRHS is true) {
  // 	  fill(')');
  // 	  andRHS = false;
  // 	}
  // 	if (orRHS is true) {
  // 	  fill(')');
  // 	  orRHS = false;
  // 	}
  // 	place('(', impDstAnchor);
  // 	fill(").implies(");
  // 	cmpDstAnchor = fill(' ');
  // 	andDstAnchor = fill(' ');
  // 	orDstAnchor  = fill(' ');
  // 	impRHS = true;
  // 	break;
  //     case OpToken.LOGICOR:		// take care of cmp/and
  // 	if (cmpRHS is true) {
  // 	  fill(')');
  // 	  cmpRHS = false;
  // 	}
  // 	if (andRHS is true) {
  // 	  fill(')');
  // 	  andRHS = false;
  // 	}
  // 	if (orRHS !is true) {
  // 	  place('(', orDstAnchor);
  // 	  orRHS = true;
  // 	}
  // 	fill(")._esdl__logicOr(");
  // 	cmpDstAnchor = fill(' ');
  // 	andDstAnchor = fill(' ');
  // 	break;
  //     case OpToken.LOGICAND:		// take care of cmp
  // 	if (cmpRHS is true) {
  // 	  fill(')');
  // 	  cmpRHS = false;
  // 	}
  // 	if (andRHS !is true) {
  // 	  place('(', andDstAnchor);
  // 	  andRHS = true;
  // 	}
  // 	fill(") ._esdl__logicAnd(");
  // 	cmpDstAnchor = fill(' ');
  // 	break;
  //     case OpToken.EQU:
  // 	place('(', cmpDstAnchor);
  // 	cmpRHS = true;
  // 	fill(")._esdl__equ (");
  // 	break;
  //     case OpToken.NEQ:
  // 	place('(', cmpDstAnchor);
  // 	cmpRHS = true;
  // 	fill(")._esdl__neq (");
  // 	break;
  //     case OpToken.LTE:
  // 	place('(', cmpDstAnchor);
  // 	cmpRHS = true;
  // 	fill(")._esdl__lte (");
  // 	break;
  //     case OpToken.GTE:
  // 	place('(', cmpDstAnchor);
  // 	cmpRHS = true;
  // 	fill(")._esdl__gte (");
  // 	break;
  //     case OpToken.LTH:
  // 	place('(', cmpDstAnchor);
  // 	cmpRHS = true;
  // 	fill(")._esdl__lth (");
  // 	break;
  //     case OpToken.GTH:
  // 	place('(', cmpDstAnchor);
  // 	cmpRHS = true;
  // 	fill(")._esdl__gth (");
  // 	break;
  //     case OpToken.AND:
  // 	fill(" & ");
  // 	break;
  //     case OpToken.OR:
  // 	fill(" | ");
  // 	break;
  //     case OpToken.XOR:
  // 	fill(" ^ ");
  // 	break;
  //     case OpToken.ADD:
  // 	fill(" + ");
  // 	break;
  //     case OpToken.SUB:
  // 	fill(" - ");
  // 	break;
  //     case OpToken.MUL:
  // 	fill(" * ");
  // 	break;
  //     case OpToken.DIV:
  // 	fill(" / ");
  // 	break;
  //     case OpToken.REM:
  // 	fill(" % ");
  // 	break;
  //     case OpToken.LSH:
  // 	fill(" << ");
  // 	break;
  //     case OpToken.RSH:
  // 	fill(" >> ");
  // 	break;
  //     case OpToken.SLICE:
  // 	// if (!dryRun) {
  // 	//   size_t tag = indexTag[$-1];
  // 	//   outBuffer[tag..tag+8] = ".opSlice";
  // 	// }
  // 	fill(", ");
  // 	break;
  //     case OpToken.SLICEINC:
  // 	// if (!dryRun) {
  // 	//   size_t tag = indexTag[$-1];
  // 	//   outBuffer[tag..tag+8] = ".opSlice";
  // 	// }
  // 	assert(false);
  //     case OpToken.INDEX:
  // 	// if (!dryRun) {
  // 	//   size_t tag = indexTag[$-1];
  // 	//   outBuffer[tag..tag+8] = ".opSlice";
  // 	// }
  // 	assert(false);
  //     }
  //   }
  // }

  // translate the expression and also consume the semicolon thereafter
  void procExprStmt() {
    import std.conv: to;
    fill("  _esdl__block ~= new CstPredicate(this, ");
    fill(stmtCount.to!string);
    stmtCount += 1;
    fill(", ");
    fill(_proxy);
    fill(", ");
    uint softAttr = 0;
    foreach_reverse(attr; soft) {
      if (attr != 0) {
	softAttr = attr;
	break;
      }
    }
    fill (softAttr.to!string);
    fill(", ");
    
    if (ifConds.length !is 0) {
      fill("// Conditions \n        ( ");
      foreach (ifCond; ifConds[0..$-1]) {
	if (ifCond.isInverse()) fill('*');
	fill(ifCond.cond);
	fill(" &\n          ");
      }
      if (ifConds[$-1].isInverse()) fill('*');
      fill(ifConds[$-1].cond);
      fill(").implies( // End of Conditions\n");
      fill("       ( ");
      procLogicExpr();
      fill(')');
    }
    else {
      procLogicExpr();
    }

    if (numParen !is 0) {
      import std.conv: to;
      assert (false, "Unbalanced parenthesis on line: " ~
	      srcLine.to!string);
    }

    auto srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if (CST[srcCursor++] !is ';') {
      assert (false, "Error: -- ';' missing at end of statement; at " ~
	      srcCursor.to!string);
    }
    if (ifConds.length !is 0) {
      fill(')');
    }

    // no parent CstPredicate
    // fill(", null, null, 0");

    // if (iterators.length != 0) {
    //   foreach (iterator; iterators) {
    // 	fill(", " ~ iterator);
    //   }
    // }

    fill(");\n");
  }

  void procStmt() {
    import std.conv: to;

    size_t srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    uint softAttr = parseSoftAttr();

    soft ~= softAttr;
    
    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    StmtToken stmtToken = nextStmtToken();

    final switch(stmtToken) {
    case StmtToken.FOREACH:
      procForeachBlock();
      return;
    case StmtToken.IFCOND:
      procIfBlock();
      return;
    case StmtToken.BEFORE:
      procBeforeStmt();
      return;
    case StmtToken.ERROR:
      assert (false, "Unidentified symbol in constraints at: " ~
	      srcCursor.to!string);
    case StmtToken.BLOCK:
      assert (false, "Unidentified symbol in constraints");
    case StmtToken.ENDBLOCK:
    case StmtToken.ENDCST:
      assert (false, "Unexpeceted end of constraint block");
    case StmtToken.STMT:
      procExprStmt();
    }

    soft.length -= 1;
  }
  
  void procBlock() {
    uint stmtCount = 0;
    while (srcCursor <= CST.length) {
      size_t srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      StmtToken stmtToken = nextStmtToken();

      switch(stmtToken) {
      case StmtToken.ENDCST:
	fill("    // END OF CONSTRAINT BLOCK \n");
	return;
      case StmtToken.ENDBLOCK:
	fill("    // END OF BLOCK \n");
	srcCursor++;		// skip the end of block brace '}'
	return;
      default:
	procStmt();
      }
    }
  }


  unittest {
    // assert (translate("FOO;"));
    // assert (translate("FOO > BAR;"));
    // assert (translate("FOO > BAR || FOO == BAR;"));
    //                012345678901234567890123456789012345678901234567890123456789
    assert (translate("_num_seq <= 2 || seq_kind1 >= 2 ;  seq_kind2 <  _num_seq || seq_kind3 == 0;
		   "));
  }
}
