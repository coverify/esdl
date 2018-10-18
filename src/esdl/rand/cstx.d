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

  char[] outBuffer;
  
  string dummy;			// sometimes required in dryRun

  string _solver;
  
  size_t outCursor = 0;
  size_t dclCursor = 0;

  size_t srcCursor = 0;
  size_t srcLine   = 0;

  size_t numParen  = 0;

  size_t numIndex  = 0;
  size_t[] indexTag;

  VarPair[] varMap = [];

  string[] iterators;
  

  // list of if conditions that are currently active
  Condition[] ifConds = [];

  void setupBuffer() {
    outBuffer.length = outCursor + dclCursor;
    outCursor = dclCursor;
    srcCursor = 0;
    dclCursor = 0;
    dcls.length = 0;
    if(varMap.length !is 0) {
      assert(false, "varMap has not been unrolled completely");
    }
    dryRun = false;
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
  
  size_t fill(in string source) {
    size_t start = outCursor;
    if(! dryRun) {
      foreach(i, c; source) {
	outBuffer[outCursor+i] = c;
      }
    }
    outCursor += source.length;
    return start;
  }

  void place(in char c, size_t cursor = 0) {
    if(! dryRun) outBuffer[cursor] = c;
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
    if(! dryRun) {
      foreach(i, c; source) {
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
	LOGICIMP,		// Implication operator
	LOGICAND,
	LOGICOR,
	INDEX,
	SLICE,
	}

  enum OpUnaryToken: byte
    {   NONE = 0,
	NEG,
	INV,
	NOT,
	}

  OpUnaryToken parseUnaryOperator() {
    OpUnaryToken tok = OpUnaryToken.NONE;
    if(srcCursor < CST.length) {
      if(CST[srcCursor] == '~') tok = OpUnaryToken.INV;
      if(CST[srcCursor] == '!') tok = OpUnaryToken.NOT;
      if(CST[srcCursor] == '-') tok = OpUnaryToken.NEG;
    }
    if(tok !is OpUnaryToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  OpToken parseOperator() {
    OpToken tok = OpToken.NONE;
    if(srcCursor < CST.length - 1) {
      if(CST[srcCursor] == '<' && CST[srcCursor+1] == '<') tok = OpToken.LSH;
      if(CST[srcCursor] == '>' && CST[srcCursor+1] == '>') tok = OpToken.RSH;
      if(CST[srcCursor] == '=' && CST[srcCursor+1] == '=') tok = OpToken.EQU;
      if(CST[srcCursor] == '>' && CST[srcCursor+1] == '=') tok = OpToken.GTE;
      if(CST[srcCursor] == '<' && CST[srcCursor+1] == '=') tok = OpToken.LTE;
      if(CST[srcCursor] == '!' && CST[srcCursor+1] == '=') tok = OpToken.NEQ;
      if(CST[srcCursor] == '&' && CST[srcCursor+1] == '&') tok = OpToken.LOGICAND;
      if(CST[srcCursor] == '|' && CST[srcCursor+1] == '|') tok = OpToken.LOGICOR;
      if(CST[srcCursor] == '-' && CST[srcCursor+1] == '>') tok = OpToken.LOGICIMP;
      if(CST[srcCursor] == '.' && CST[srcCursor+1] == '.') tok = OpToken.SLICE;
    }
    if(tok !is OpToken.NONE) {
      srcCursor += 2;
      return tok;
    }
    if(srcCursor < CST.length) {
      if(CST[srcCursor] == '&') tok = OpToken.AND;
      if(CST[srcCursor] == '|') tok = OpToken.OR;
      if(CST[srcCursor] == '^') tok = OpToken.XOR;
      if(CST[srcCursor] == '+') tok = OpToken.ADD;
      if(CST[srcCursor] == '-') tok = OpToken.SUB;
      if(CST[srcCursor] == '*') tok = OpToken.MUL;
      if(CST[srcCursor] == '/') tok = OpToken.DIV;
      if(CST[srcCursor] == '%') tok = OpToken.REM;
      if(CST[srcCursor] == '<') tok = OpToken.LTH;
      if(CST[srcCursor] == '>') tok = OpToken.GTH;
      if(CST[srcCursor] == '[') tok = OpToken.INDEX;
      // if(CST[srcCursor] == ';') tok = OpToken.END;
    }
    if(tok !is OpToken.NONE) {
      srcCursor += 1;
      return tok;
    }
    return tok;			// None
  }

  void errorToken() {
    import std.conv;
    size_t start = srcCursor;
    while(srcCursor < CST.length) {
      char c = CST[srcCursor];
      if(c !is ' ' && c !is '\n' && c !is '\t' && c !is '\r' && c !is '\f') {
	++srcCursor;
      }
      else break;
    }
    if(srcCursor == start) {
      assert(false, "EOF while parsing!");
    }
    assert(false, "Unrecognized token: " ~ "'" ~
	   CST[start..srcCursor] ~ "' -- at: " ~ srcCursor.to!string);
  }

  size_t parseIdentifier() {
    size_t start = srcCursor;
    if(srcCursor < CST.length) {
      char c = CST[srcCursor];
      if((c >= 'A' && c <= 'Z') ||
	 (c >= 'a' && c <= 'z') ||
	 (c == '_')) {
	++srcCursor;
      }
      else {
	return start;
      }
    }
    while(srcCursor < CST.length) {
      char c = CST[srcCursor];
      if((c >= 'A' && c <= 'Z') ||
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

  // I do not want to use any dynamic arrays here since this all is
  // compile time and I do not want DMD to allocate memory for this at
  // compile time.

  enum MaxHierDepth = 20;

  int[MaxHierDepth * 2] parseIdentifierChain() {
    int[MaxHierDepth * 2] result;
    size_t wTag = srcCursor;
    size_t start = srcCursor;
    size_t srcTag = srcCursor;
    
    result[0] = -1;

    wTag = srcCursor;
    parseSpace();
    srcTag = srcCursor;
    parseIdentifier();

    for (size_t i=0; i != MaxHierDepth-1; ++i) {
      if(srcCursor > srcTag) {
	fill(CST[wTag..srcTag]);
	result[2*i] = cast(int) (srcTag - start);
	result[2*i + 1] = cast(int) (srcCursor - start);
      }
      else {
	if(i != 0) srcCursor = wTag - 1;
	result[2*i] = -1;
	break;
      }
      srcTag = srcCursor;
      parseSpace();
      if(CST[srcCursor] == '.') {
	fill(CST[srcTag..srcCursor]);
	++srcCursor;
	wTag = srcCursor;
	parseSpace();
	srcTag = srcCursor;
	parseIdentifier();
	continue;
      }
      else if (CST[srcCursor] == '[') {
      	fill(CST[srcTag..srcCursor]);
      	// ++srcCursor;
	wTag = srcCursor;
	// parseSpace();
	srcTag = srcCursor;
	moveToMatchingBracket();
      	continue;
      }
      else {
	srcCursor = srcTag;
	result[2*i + 2] = -1;
	break;
      }
    }
    return result;
  }

  size_t moveToMatchingBracket() {
    size_t start = srcCursor;
    uint bracketCount = 0;
    while (srcCursor < CST.length) {
      if (CST[srcCursor] == '/' && CST[srcCursor+1] == '/') {
	parseLineComment();
	continue;
      }
      if (CST[srcCursor] == '/' && CST[srcCursor+1] == '*') {
	parseBlockComment();
	continue;
      }
      if (CST[srcCursor] == '/' && CST[srcCursor+1] == '+') {
	parseNestedComment();
	continue;
      }
      if (CST[srcCursor] == '[') {
	bracketCount++;
	srcCursor++;
	continue;
      }
      if (CST[srcCursor] == ']') {
	bracketCount--;
	srcCursor++;
	if (bracketCount == 0) {
	  break;
	}
	continue;
      }
      srcCursor++;
      continue;
    }

    if (bracketCount != 0) {
      assert(false, "Unbalanced backet");
    }
     
    return start;
    
  }
  
  size_t procIdentifier() {
    // parse an identifier and the following '.' heirarcy if any
    auto start = srcCursor;
    auto srcTag = srcCursor;
    int[MaxHierDepth * 2] idChain = parseIdentifierChain();
    if(idChain[0] != -1) {
      int indx = idMatch(CST[srcTag+idChain[0]..srcTag+idChain[1]]);
      if(indx == -1) {
	fill(CST[srcTag+idChain[0]..srcTag+idChain[1]]);
	fillDeclaration(CST[srcTag+idChain[0]..srcTag+idChain[1]]);
      }
      else {
	fill(varMap[indx].xLat);
	fillDeclaration(varMap[indx].xLatBase);
      }
      if(idChain[2] != -1) {
	fill(".");
	for (size_t i=1; i != MaxHierDepth-1; ++i) {
	  if (CST[srcTag+idChain[2*i]] != '[') {
	    fill(CST[srcTag+idChain[2*i]..srcTag+idChain[2*i+1]]);
	  }
	  else {
	    indexTag ~= outCursor-1;
	    fill("opIndex(");
	    ++numIndex;
	    procSubExpr(srcTag+idChain[2*i]+1);
	    fill(")");
	  }
	  if(idChain[2*i+2] == -1) break;
	  else fill(".");
	}
	// fill("}(_outer)");
      }
    }
    else {
      srcTag = parseLiteral();
      if(srcCursor > srcTag) {
	fill(CST[srcTag..srcCursor]);
	fillDeclaration(CST[srcTag..srcCursor]);
      }
      else {
	srcTag = parseWithArg();
	if(srcCursor > srcTag) {
	  fill("_esdl__arg!");
	  fill(CST[srcTag+1..srcCursor]);
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
    if(srcCursor >= CST.length - 2 ||
       CST[srcCursor] != '/' || CST[srcCursor+1] != '/') return start;
    else {
      srcCursor += 2;
      while(srcCursor < CST.length) {
	if(CST[srcCursor] == '\n') {
	  break;
	}
	else {
	  if(srcCursor == CST.length) {
	    // commment unterminated
	    assert(false, "Line comment not terminated");
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
    assert(parseLineComment("Foo // Bar;\n\n", curs) == 8);
    assert(curs == 12);
  }

  size_t parseBlockComment() {
    size_t start = srcCursor;
    if(srcCursor >= CST.length - 2 ||
       CST[srcCursor] != '/' || CST[srcCursor+1] != '*') return start;
    else {
      srcCursor += 2;
      while(srcCursor < CST.length - 1) {
	if(CST[srcCursor] == '*' && CST[srcCursor+1] == '/') {
	  break;
	}
	else {
	  if(srcCursor == CST.length - 1) {
	    // commment unterminated
	    assert(false, "Block comment not terminated");
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
    assert(parseBlockComment("Foo /* Bar;\n\n */", curs) == 4);
    assert(curs == 16);
  }

  size_t parseNestedComment() {
    size_t nesting = 0;
    size_t start = srcCursor;
    if(srcCursor >= CST.length - 2 ||
       CST[srcCursor] != '/' || CST[srcCursor+1] != '+') return start;
    else {
      srcCursor += 2;
      while(srcCursor < CST.length - 1) {
	if(CST[srcCursor] == '/' && CST[srcCursor+1] == '+') {
	  nesting += 1;
	  srcCursor += 1;
	}
	else if(CST[srcCursor] == '+' && CST[srcCursor+1] == '/') {
	  if(nesting == 0) {
	    break;
	  }
	  else {
	    nesting -= 1;
	    srcCursor += 1;
	  }
	}
	srcCursor += 1;
	if(srcCursor >= CST.length - 1) {
	  // commment unterminated
	  assert(false, "Block comment not terminated");
	}
      }
      srcCursor += 2;
      return start;
    }
  }

  unittest {
    size_t curs = 4;
    parseNestedComment("Foo /+ Bar;/+// \n+/+*/ +/", curs);
    assert(curs == 25);
  }

  size_t parseLiteral() {
    size_t start = srcCursor;
    // look for 0b or 0x
    if(srcCursor + 2 <= CST.length &&
       CST[srcCursor] == '0' &&
       (CST[srcCursor+1] == 'x' ||
	CST[srcCursor+1] == 'X')) { // hex numbers
      srcCursor += 2;
      while(srcCursor < CST.length) {
	char c = CST[srcCursor];
	if((c >= '0' && c <= '9') ||
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
    else if(srcCursor + 2 <= CST.length &&
	    CST[srcCursor] == '0' &&
	    (CST[srcCursor+1] == 'b' ||
	     CST[srcCursor+1] == 'B')) { // binary numbers
      srcCursor += 2;
      while(srcCursor < CST.length) {
	char c = CST[srcCursor];
	if((c == '0' || c == '1' || c == '_')) {
	  ++srcCursor;
	}
	else {
	  break;
	}
      }
    }
    else {			// decimals
      while(srcCursor < CST.length) {
	char c = CST[srcCursor];
	if((c >= '0' && c <= '9') ||
	   (c == '_')) {
	  ++srcCursor;
	}
	else {
	  break;
	}
      }
    }
    if(srcCursor > start) {
      // Look for long/short specifier
      while(srcCursor < CST.length) {
	char c = CST[srcCursor];
	if(c == 'L' || c == 'u' ||  c == 'U') {
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
    if(srcCursor < CST.length &&
       CST[srcCursor == '@']) {
      ++srcCursor;
    }
    else return start;
    while(srcCursor < CST.length) {
      char c = CST[srcCursor];
      if((c >= '0' && c <= '9')) {
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
    assert(parseIdentifier("Foo Bar;", curs) == 0);
    assert(curs == 7);
  }


  size_t parseWhiteSpace() {
    auto start = srcCursor;
    while(srcCursor < CST.length) {
      auto c = CST[srcCursor];
      // eat up whitespaces
      if(c is '\n') ++srcLine;
      if(c is ' ' || c is '\n' || c is '\t' || c is '\r' || c is '\f') {
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
    while(srcCursor < CST.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if(srcCursor > srcTag) {
	continue;
      }
      else {
	if(srcCursor < CST.length && CST[srcCursor] == '(') {
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

  // Parse parenthesis on the right hand side. But stop if and when
  // the numParen has already hit zero. This is important since for if
  // conditional we want to know where to stop parsing.
  size_t parseRightParens() {
    auto start = srcCursor;
    while(srcCursor < CST.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if(srcCursor > srcTag) {
	continue;
      }
      else {
	if(srcCursor < CST.length && CST[srcCursor] == ')') {
	  if(numParen is 0) break;
	  --numParen;
	  ++srcCursor;
	  continue;
	}
	if(srcCursor < CST.length && CST[srcCursor] == ']') {
	  if(numIndex is 0) break;
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

  size_t moveToRightParens() {
    auto start = srcCursor;
    while(srcCursor < CST.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if(srcCursor > srcTag) {
	fill(CST[srcTag..srcCursor]);
	continue;
      }
      else {
	if(srcCursor < CST.length && CST[srcCursor] == ')') {
	  if(numParen is 0) break;
	  --numParen;
	  ++srcCursor;
	  fill(")");
	  continue;
	}
	if(srcCursor < CST.length && CST[srcCursor] == ']') {
	  if(numIndex is 0) break;
	  --numIndex;
	  ++srcCursor;
	  fill(")");
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
    while(srcCursor < CST.length) {
      auto srcTag = srcCursor;

      parseLineComment();
      parseBlockComment();
      parseNestedComment();
      parseWhiteSpace();

      if(srcCursor > srcTag) {
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
    assert(parseLeftParens("    // foo\nFoo Bar;", curs) == 11);
    assert(curs == 11);
  }

  char[] translate(string solver, string name) {
    _solver = solver;

    translateBlock(name);

    setupBuffer();

    translateBlock(name);

    return outBuffer;
  }

  void translateBlock(string name) {
    string blockName;
    import std.conv: to;
    fill("// Constraint @ File: " ~ FILE ~ " Line: " ~ LINE.to!string ~ "\n\n");
    if (name == "") {
      fill("override CstBlock getCstExpr() {\n"//  ~
	   // "\n  auto cstExpr = new CstBlock;\n"
	   );
      blockName = "_esdl__cst_block";
    }
    else {
      fill("CstBlock _esdl__cst_func_" ~ name ~ "() {\n"//  ~
	   // "\n  auto cstExpr = new CstBlock;\n"
	   );
      blockName = "_esdl__cst_block_" ~ name;
    }

    fill("  if (" ~ blockName ~ " !is null) return " ~
	 blockName ~ ";\n");

    fill("  CstBlock _esdl__block = new CstBlock();\n");

    procBlock();
    fill("  " ~ blockName ~ " = _esdl__block;\n");
    fill("  return _esdl__block;\n}\n");
  }

  char[] translateExpr() {
    procExpr();
    setupBuffer();
    procExpr();
    return outBuffer;
  }

  int idMatch(string id) {
    foreach(int i, var; varMap) {
      if(var.varName == id) return i;
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
    if(CST[srcTag..srcCursor] != "foreach") {
      import std.conv: to;
      assert(false, "Not a FOREACH block at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if(CST[srcCursor] != '(') {
      errorToken();
    }

    ++srcCursor;

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    // Parse the index
    srcTag = parseIdentifier();
    if(srcCursor > srcTag) {
      // FIXME -- check if the variable names do not shadow earlier
      // names in the table
      index = CST[srcTag..srcCursor];

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      if(CST[srcCursor] == ';') {
	elem = index;
	index = "";
      }
      else if(CST[srcCursor] != ',') {
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
    if(elem.length is 0) {
      srcTag = parseIdentifier();
      if(srcCursor > srcTag) {
	// FIXME -- check if the variable names do not shadow earlier
	// names in the table
	elem = CST[srcTag..srcCursor];

	srcTag = parseSpace();
	fill(CST[srcTag..srcCursor]);

	if(CST[srcCursor] != ';') {
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
    if(srcCursor > srcTag) {
      // FIXME -- check if the variable names do not shadow earlier
      // names in the table
      array = CST[srcTag..srcCursor];
      arrayBase = CST[srcTag..srcCursor];
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
      if(CST[srcCursor] != ')') {
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
    if(indx != -1) {
      array = varMap[indx].xLat;
      arrayBase = varMap[indx].xLatBase;
    }

    // add index
    iterators ~= array ~ ".iterator()";
    
    if(index.length != 0) {
      VarPair x;
      x.varName  = index;
      x.xLat     = array ~ ".iterator()";
      x.xLatBase = arrayBase;
      varMap ~= x;
    }

    VarPair x;
    x.varName  = elem;
    x.xLat     = array ~ ".elements()";
    x.xLatBase = arrayBase;
    varMap ~= x;

    if(CST[srcCursor] is '{') {
      ++srcCursor;
      procBlock();
    }
    else {
      procStmt();
    }

    iterators = iterators[0..$-1];

    if(index.length != 0) {
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
    if(CST[srcTag..srcCursor] != "if") {
      import std.conv: to;
      assert(false, "Not a IF block at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if(CST[srcCursor] != '(') {
      errorToken();
    }

    ++srcCursor;

    fill("/* IF Block: ");
    auto outTag = outCursor;
    procExpr();

    if(dryRun) {
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
    if(CST[srcCursor] != ')') {
      errorToken();
    }
    ++srcCursor;
    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if(CST[srcCursor] is '{') {
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
    if(CST[srcTag..srcCursor] != "else") { // no else
      srcCursor = srcTag;		   // revert the cursor
      ifConds = ifConds[0..$-1];
      return;
    }
    else {
      fill("// Else \n");
      ifConds[$-1].switchToElse();

      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      if(CST[srcCursor] is '{') {
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
    if(CST[srcTag..srcCursor] != "solve") {
      import std.conv: to;
      assert(false, "Not a solve statement at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    procIdentifier();

    fill(".solveBefore(");
    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    srcTag = parseIdentifier();
    if(CST[srcTag..srcCursor] != "before") {
      import std.conv: to;
      assert(false, "Expected keyword \"before\" at: " ~ srcTag.to!string);
    }

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    procIdentifier();

    srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if(CST[srcCursor++] !is ';') {
      assert(false, "Error: -- ';' missing at end of statement; at " ~
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

    if(srcCursor == CST.length) return StmtToken.ENDCST;
    srcTag = parseLeftParens();
    // if a left parenthesis has been found at the beginning it can only
    // be a normal statement
    if(srcCursor > srcTag) return StmtToken.STMT;

    if ((CST[srcCursor] >= 'A' && CST[srcCursor] <= 'Z') ||
	(CST[srcCursor] >= 'a' && CST[srcCursor] <= 'z') ||
	(CST[srcCursor] == '_')) {
	
      srcTag = parseIdentifier();
      if(srcCursor > srcTag) {
	if(CST[srcTag..srcCursor] == "foreach") return StmtToken.FOREACH;
	if(CST[srcTag..srcCursor] == "if") return StmtToken.IFCOND;
	if(CST[srcTag..srcCursor] == "solve") return StmtToken.BEFORE;
	// not a keyword
	return StmtToken.STMT;
      }
    }
    if (CST[srcCursor] is '{') return StmtToken.BLOCK;
    if (CST[srcCursor] is '}') return StmtToken.ENDBLOCK;
    return StmtToken.STMT;
      // return StmtToken.ERROR;
  }


  void procSubExpr(size_t cursor) {
    auto savedCursor = srcCursor;
    auto savedNumIndex = numIndex;
    auto savedNumParen = numParen;
    srcCursor = cursor;
    numIndex = 0;
    numParen = 0;
    procExpr();
    numIndex = savedNumIndex;
    numParen = savedNumParen;
    srcCursor = savedCursor;
  }

  void procExpr() {
    bool cmpRHS;
    bool andRHS;
    bool orRHS;
    bool impRHS;

    size_t srcTag = 0;

    size_t cmpDstAnchor = fill(" ");
    size_t andDstAnchor = fill(" ");
    size_t orDstAnchor  = fill(" ");
    size_t impDstAnchor = fill(" ");

  loop:
    while(srcCursor < CST.length) {
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);

      if(srcCursor == CST.length) break;

      // Parse any left braces now
      srcTag = parseLeftParens();
      fill(CST[srcTag..srcCursor]);

      // Parse any unary operators
      auto uTok = parseUnaryOperator();
      final switch(uTok) {
      case OpUnaryToken.NEG: fill("-"); continue loop;
      case OpUnaryToken.NOT: fill("*"); continue loop;
      case OpUnaryToken.INV: fill("~"); continue loop;
      case OpUnaryToken.NONE: break;
      }
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
      fill("_esdl__vec(");
      srcTag = procIdentifier();
      fill(", \"");
      fill(CST[srcTag..srcCursor]);
      fill("\"");
      fill(")");
      // fillDeclaration(CST[srcTag..srcCursor]);
      srcTag = parseSpace();
      fill(CST[srcTag..srcCursor]);
      srcTag = moveToRightParens();
      
      // fill(CST[srcTag..srcCursor]);

      srcTag = srcCursor;
      OpToken opToken = parseOperator();

      final switch(opToken) {
      case OpToken.NONE:
	//   errorToken();
	//   break;
	// case OpToken.END:
	if(cmpRHS is true) {
	  fill(")");
	  cmpRHS = false;
	}
	if(andRHS is true) {
	  fill(")");
	  andRHS = false;
	}
	if(orRHS is true) {
	  fill(")");
	  orRHS = false;
	}
	if(impRHS is true) {
	  fill(")");
	  impRHS = false;
	}
	return;
	// break;
      case OpToken.LOGICIMP:
	if(cmpRHS is true) {
	  fill(")");
	  cmpRHS = false;
	}
	if(andRHS is true) {
	  fill(")");
	  andRHS = false;
	}
	if(orRHS is true) {
	  fill(")");
	  orRHS = false;
	}
	place('(', impDstAnchor);
	fill(").implies(");
	cmpDstAnchor = fill(" ");
	andDstAnchor = fill(" ");
	orDstAnchor  = fill(" ");
	impRHS = true;
	break;
      case OpToken.LOGICOR:		// take care of cmp/and
	if(cmpRHS is true) {
	  fill(")");
	  cmpRHS = false;
	}
	if(andRHS is true) {
	  fill(")");
	  andRHS = false;
	}
	if(orRHS !is true) {
	  place('(', orDstAnchor);
	  orRHS = true;
	}
	fill(")._esdl__logicOr(");
	cmpDstAnchor = fill(" ");
	andDstAnchor = fill(" ");
	break;
      case OpToken.LOGICAND:		// take care of cmp
	if(cmpRHS is true) {
	  fill(")");
	  cmpRHS = false;
	}
	if(andRHS !is true) {
	  place('(', andDstAnchor);
	  andRHS = true;
	}
	fill(") ._esdl__logicAnd(");
	cmpDstAnchor = fill(" ");
	break;
      case OpToken.EQU:
	place('(', cmpDstAnchor);
	cmpRHS = true;
	fill(")._esdl__equ (");
	break;
      case OpToken.NEQ:
	place('(', cmpDstAnchor);
	cmpRHS = true;
	fill(")._esdl__neq (");
	break;
      case OpToken.LTE:
	place('(', cmpDstAnchor);
	cmpRHS = true;
	fill(")._esdl__lte (");
	break;
      case OpToken.GTE:
	place('(', cmpDstAnchor);
	cmpRHS = true;
	fill(")._esdl__gte (");
	break;
      case OpToken.LTH:
	place('(', cmpDstAnchor);
	cmpRHS = true;
	fill(")._esdl__lth (");
	break;
      case OpToken.GTH:
	place('(', cmpDstAnchor);
	cmpRHS = true;
	fill(")._esdl__gth (");
	break;
      case OpToken.AND:
	fill(" & ");
	break;
      case OpToken.OR:
	fill(" | ");
	break;
      case OpToken.XOR:
	fill(" ^ ");
	break;
      case OpToken.ADD:
	fill(" + ");
	break;
      case OpToken.SUB:
	fill(" - ");
	break;
      case OpToken.MUL:
	fill(" * ");
	break;
      case OpToken.DIV:
	fill(" / ");
	break;
      case OpToken.REM:
	fill(" % ");
	break;
      case OpToken.LSH:
	fill(" << ");
	break;
      case OpToken.RSH:
	fill(" >> ");
	break;
      case OpToken.INDEX:
	indexTag ~= outCursor;
	fill(".opIndex(");
	++numIndex;
	break;
      case OpToken.SLICE:
	if(!dryRun) {
	  size_t tag = indexTag[$-1];
	  outBuffer[tag..tag+8] = ".opSlice";
	}
	fill(",");
	break;
      }
    }
  }

  // translate the expression and also consume the semicolon thereafter
  void procExprStmt() {
    fill("  _esdl__block ~= new CstPredicate(" ~ _solver ~ ", ");

    if(ifConds.length !is 0) {
      fill("// Conditions \n        ( ");
      foreach(ifCond; ifConds[0..$-1]) {
	if(ifCond.isInverse()) fill("*");
	fill(ifCond.cond);
	fill(" &\n          ");
      }
      if(ifConds[$-1].isInverse()) fill("*");
      fill(ifConds[$-1].cond);
      fill(").implies( // End of Conditions\n");
      fill("       ( ");
      procExpr();
      fill(")");
    }
    else {
      procExpr();
    }

    if(numParen !is 0) {
      import std.conv: to;
      assert(false, "Unbalanced parenthesis on line: " ~
	     srcLine.to!string);
    }

    auto srcTag = parseSpace();
    fill(CST[srcTag..srcCursor]);

    if(CST[srcCursor++] !is ';') {
      assert(false, "Error: -- ';' missing at end of statement; at " ~
	     srcCursor.to!string);
    }
    if(ifConds.length !is 0) {
      fill(")");
    }

    // no parent CstPredicate
    fill(", null");

    if (iterators.length != 0) {
      foreach (iterator; iterators) {
	fill(", " ~ iterator);
      }
    }

    fill(");\n");
  }

  void procStmt() {
    import std.conv: to;

    size_t srcTag = parseSpace();
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
      assert(false, "Unidentified symbol in constraints at: " ~
	     srcCursor.to!string);
    case StmtToken.BLOCK:
      assert(false, "Unidentified symbol in constraints");
    case StmtToken.ENDBLOCK:
    case StmtToken.ENDCST:
      assert(false, "Unexpeceted end of constraint block");
    case StmtToken.STMT:
      procExprStmt();
    }
  }
  
  void procBlock() {
    while(srcCursor <= CST.length) {
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
    // assert(translate("FOO;"));
    // assert(translate("FOO > BAR;"));
    // assert(translate("FOO > BAR || FOO == BAR;"));
    //                012345678901234567890123456789012345678901234567890123456789
    assert(translate("_num_seq <= 2 || seq_kind1 >= 2 ;  seq_kind2 <  _num_seq || seq_kind3 == 0;
		   "));
  }
}
