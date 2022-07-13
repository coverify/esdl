module esdl.data.packed;

import esdl.data.bvec;

enum _esdl__packed;
struct _esdl__packed_info(T)
{
  string name;
  bool isRand;
  uint offset;
  uint bitlen;
}

struct packedParser
{
  import std.conv;
  size_t srcCursor = 0;
  size_t outCursor = 0;
  size_t srcLine = 0;
  string outBuffer = "";
  string PACKED;
  enum VARTYPE: ubyte {
    INT, UINT, LONG, ULONG, BOOL, BYTE, UBYTE, BVEC, UBVEC
  };

  this(string str) {
    PACKED = str;
  }
  
  void fill(in string source) {
    outBuffer ~= source;
  }
  
  size_t parseName() {
    auto start = srcCursor;
    import std.ascii;
    while (isAlpha(PACKED[srcCursor]) || isDigit(PACKED[srcCursor]) ||
	   PACKED[srcCursor] == '_') {
      ++srcCursor;
    }
    return start;
  }
  
  bool parseIsRand() {
    if (srcCursor + 5 < PACKED.length &&
	PACKED[srcCursor..srcCursor+5] == "@rand") {
      srcCursor += 5;
      return true;
    }
    return false;
  }
  
  void parseSemiColon() {
    assert (PACKED[srcCursor] == ';',
	    "missing semicolon at line "~ srcLine.to!string);
    srcCursor ++;
  }
  
  void parseExclamation() {
    assert (PACKED[srcCursor] == '!',
	    "missing exclamation at line "~ srcLine.to!string);
    srcCursor ++;
  }
  
  VARTYPE parseType() {
    auto srcTag = parseName();
    switch (PACKED[srcTag..srcCursor]) {
    case "int":
      return VARTYPE.INT;
    case "uint":
      return VARTYPE.UINT;
    case "long":
      return VARTYPE.LONG;
    case "ulong":
      return VARTYPE.ULONG;
    case "byte":
      return VARTYPE.BYTE;
    case "ubyte":
      return VARTYPE.UBYTE;
    case "bool":
      return VARTYPE.BOOL;
    case "bvec":
      return VARTYPE.BVEC;
    case "ubvec":
      return VARTYPE.UBVEC;
    default:
      assert(false, "invalid type " ~ PACKED[srcTag..srcCursor]);
    }
  }
  
  size_t parseLiteral() {
    size_t start = srcCursor;
    // check for - sign
    if (PACKED[srcCursor] == '-') {
      ++srcCursor;
    }
    // look for 0b or 0x
    if (srcCursor + 2 <= PACKED.length &&
        PACKED[srcCursor] == '0' &&
        (PACKED[srcCursor+1] == 'x' ||
         PACKED[srcCursor+1] == 'X')) { // hex numbers
      srcCursor += 2;
      while (srcCursor < PACKED.length) {
        char c = PACKED[srcCursor];
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
    else if (srcCursor + 2 <= PACKED.length &&
	     PACKED[srcCursor] == '0' &&
	     (PACKED[srcCursor+1] == 'b' ||
	      PACKED[srcCursor+1] == 'B')) { // binary numbers
      srcCursor += 2;
      while (srcCursor < PACKED.length) {
        char c = PACKED[srcCursor];
        if ((c == '0' || c == '1' || c == '_')) {
          ++srcCursor;
        }
        else {
          break;
        }
      }
    }
    else {			// decimals
      while (srcCursor < PACKED.length) {
        char c = PACKED[srcCursor];
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
      while (srcCursor < PACKED.length) {
        char c = PACKED[srcCursor];
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
  size_t parseComment() {
    auto start = srcCursor;
    while (srcCursor < PACKED.length) {
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
    while (srcCursor < PACKED.length) {
      auto c = PACKED[srcCursor];
      // eat up whitespaces
      if (c is '\n') ++srcLine;
      if (c is ' ' || c is '\n' || c is '\t' ||
	  c is '\r' || c is '\f') {
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
    if (srcCursor >= PACKED.length - 2 ||
        PACKED[srcCursor] != '/' || PACKED[srcCursor+1] != '/')
      return start;
    else {
      srcCursor += 2;
      while (srcCursor < PACKED.length) {
        if (PACKED[srcCursor] == '\n') {
          break;
        }
        else {
          if (srcCursor == PACKED.length) {
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
    if (srcCursor >= PACKED.length - 2 ||
        PACKED[srcCursor] != '/' || PACKED[srcCursor+1] != '*')
      return start;
    else {
      srcCursor += 2;
      while (srcCursor < PACKED.length - 1) {
        if (PACKED[srcCursor] == '*' && PACKED[srcCursor+1] == '/') {
          break;
        }
        else {
          if (srcCursor == PACKED.length - 1) {
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
    if (srcCursor >= PACKED.length - 2 ||
        PACKED[srcCursor] != '/' || PACKED[srcCursor+1] != '+')
      return start;
    else {
      srcCursor += 2;
      while (srcCursor < PACKED.length - 1) {
        if (PACKED[srcCursor] == '/' && PACKED[srcCursor+1] == '+') {
          nesting += 1;
          srcCursor += 1;
        }
        else if (PACKED[srcCursor] == '+' &&
		 PACKED[srcCursor+1] == '/') {
          if (nesting == 0) {
            break;
          }
          else {
            nesting -= 1;
            srcCursor += 1;
          }
        }
        srcCursor += 1;
        if (srcCursor >= PACKED.length - 1) {
          // commment unterminated
          assert (false, "Block comment not terminated at line " ~
		  srcLine.to!string);
        }
      }
      srcCursor += 2;
      return start;
    }
  }
  
  size_t parseSpace() {
    size_t start = srcCursor;
    while (srcCursor < PACKED.length) {
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

  string [] names;
  VARTYPE [] types;
  size_t [] sizes;
  bool [] isRand;
  string bvecname;


  bool checkname(string s) {
    import std.ascii;
    if (s.length == 0) return false;
    if (isDigit(s[0])) return false;
    return true;
  }

  string vartypeToString (VARTYPE type, size_t size) {
    final switch (type) {
    case VARTYPE.INT:
      return "int";
    case VARTYPE.UINT:
      return "uint";
    case VARTYPE.LONG:
      return "long";
    case VARTYPE.ULONG:
      return "ulong";
    case VARTYPE.BYTE:
      return "byte";
    case VARTYPE.BOOL:
      return "bool";
    case VARTYPE.UBYTE:
      return "ubyte";
    case VARTYPE.BVEC:
      return "bvec!" ~ size.to!string;
    case VARTYPE.UBVEC:
      return "ubvec!" ~ size.to!string;
    }
  }

  string createFunctions (bool isRand, VARTYPE type, size_t size_sum,
			  size_t size, string name) {
    string str;
    string type_str = vartypeToString(type, size);
    str ~= type_str ~ " " ~ name ~ "() @safe  {\n";
    str ~= "\tauto result = " ~ bvecname ~ "[" ~ (size_sum).to!string ~
      ".." ~ (size_sum+size).to!string ~ "];\n";
    str ~= "\treturn cast(" ~ type_str ~ ") result;\n}\n";
    str ~= "void " ~ name ~ "(" ~ type_str ~ " v) @safe  { \n";
    if (type == VARTYPE.BOOL)
      str ~= "\t" ~ bvecname ~ "[" ~ (size_sum).to!string ~ ".." ~
	(size_sum+size).to!string ~ "] = cast(bool)(v);\n}\n";
    else 
    str ~= "\t" ~ bvecname ~ "[" ~ (size_sum).to!string ~ ".." ~
      (size_sum+size).to!string ~ "] = v;\n}\n";
    return str;
  }

  string createAttrib (bool isRand, VARTYPE type, size_t size_sum,
		       size_t size, string name) {
    string attr = "@_esdl__packed_info!(";
    attr ~= vartypeToString(type, size) ~ ")(\"";
    attr ~= name ~ "\", ";
    attr ~= isRand.to!string ~ ", ";
    attr ~= size_sum.to!string ~ ", ";
    attr ~= size.to!string ~ ")\n";
    return attr;
  }
  
  string createMixin() {
    size_t [] size_prefix_sum;
    size_prefix_sum ~= 0;
    foreach (size_t sz; sizes) {
      size_prefix_sum ~= size_prefix_sum[$-1]+sz;
    }
    bvecname = "_esdl__packed_";
    foreach (string n; names) {
      bvecname ~= "_";
      bvecname ~= n;
    }
    string mix = "import esdl.data.packed: _esdl__packed, _esdl__packed_info;\n";
    // mix ~= "alias " ~ bvecname ~ " this;\n";
    mix ~= "@_esdl__packed\n";
    for (int i = 0; i < names.length; i ++) {
      mix ~= createAttrib(isRand[i], types[i], size_prefix_sum[i],
			  sizes[i], names[i]);
    }
    mix ~= "ubvec!" ~ size_prefix_sum[$-1].to!string ~ " " ~
      bvecname ~ ";\n";
    for (int i = 0; i < names.length; i ++) {
      mix ~= createFunctions(isRand[i], types[i], size_prefix_sum[i],
			     sizes[i], names[i]);
    }
    return mix;
  }
  
  string parse() {
    while (true) {
      parseSpace();
      if (parseIsRand()) isRand ~= true;
      else isRand ~= false;
      parseSpace();
      if (srcCursor == PACKED.length) break;
      VARTYPE type = parseType();
      parseSpace();
      string name;
      final switch (type) {
      case VARTYPE.INT:
	sizes ~= 32;
	break;
      case VARTYPE.UINT:
	sizes ~= 32;
	break;
      case VARTYPE.LONG:
	sizes ~= 64;
	break;
      case VARTYPE.ULONG:
	sizes ~= 64;
	break;
      case VARTYPE.BYTE:
	sizes ~= 8;
	break;
      case VARTYPE.BOOL:
	sizes ~= 1;
	break;
      case VARTYPE.UBYTE:
	sizes ~= 8;
	break;
      case VARTYPE.BVEC:
	goto case VARTYPE.UBVEC;
      case VARTYPE.UBVEC:
	parseExclamation();
	size_t srcTag = parseLiteral();
	size_t bvec_size = to!size_t(PACKED[srcTag..srcCursor]);
	sizes ~= bvec_size;
	parseSpace();
	break;
      }
      size_t srcTag = parseName();
      name = PACKED[srcTag..srcCursor];
      if (!checkname(name)) {
	assert (false, "invalid variable name " ~ name ~
		" at line " ~ srcLine.to!string);
      }
      parseSpace();
      parseSemiColon();
      parseSpace();
      types ~= type;
      names ~= name;
    }
    return createMixin();
  }
}

string packed (string str)()
{
  packedParser parser = packedParser(str);
  return parser.parse();
}
