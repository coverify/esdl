module esdl.cover.group;
import esdl.cover.point;
import esdl.base.core: addCoverGroup;
import esdl.base.rand: rand;
import esdl.data.vector: Vector;

abstract class _esdl__BaseCoverGroup: rand.disable {
  this() {
    addCoverGroup(this);
  }
  abstract double get_coverage();
}

struct CoverGroupParser
{
  bool druRun = true;
  size_t bufLen = 0;
  
  size_t srcCursor = 0;
  size_t srcLine = 0;
  string S;

  Vector!(char, "outBuffer") outBuffer;
  string buffer() {return cast(string) outBuffer[];}
  // void fill(in string source) {
  //   outBuffer ~= source;
  // }

  void fill(T...)(T strs) {
    foreach (str; strs) {
      if (druRun) bufLen += str.length;
      else outBuffer ~= str;
    }
  }
  
  this(string s) {
    S = s;
  }

  void setUp() {
    outBuffer.reserve(bufLen);
    srcCursor = 0;
    srcLine = 0;
    druRun = false;
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
  bool parseSampleArg() {
    if (S.length >= srcCursor+7 &&
	S[srcCursor..srcCursor+7] == "@sample") {
      srcCursor += 7;
      return true;
    }
    return false;
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
  
  size_t parseIdentifier() {
    size_t start = srcCursor;
    if (srcCursor < S.length) {
      char c = S[srcCursor];
      if ((c >= 'A' && c <= 'Z') ||
	  (c >= 'a' && c <= 'z') ||
	  (c == '_')) {
	++srcCursor;
      }
      else {
	return start;
      }
    }
    while (srcCursor < S.length) {
      char c = S[srcCursor];
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
  
  void parse() {    
    parseSpace();
    int cpCount = 0;
    string[] cp_names;
    string[] sampleArgTypes;
    string[] sampleArgs;
    while (srcCursor < S.length) {
      string cp_name;
      if (parseSampleArg()) {
	size_t markIdentifier;
	size_t markLastIdentifier;
	size_t srcTag = srcCursor;
	while (S[srcCursor] != ';') {
	  size_t srcMark = srcCursor;
	  parseSpace();
	  if (srcMark == srcCursor) {
	    if (S[srcCursor] != ';') {
	      if (srcCursor < S.length) {
		markIdentifier = srcCursor;
		parseIdentifier();
		if (markIdentifier != srcCursor) {
		  markLastIdentifier = markIdentifier;
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
	fill(S[srcTag..markLastIdentifier]);
	sampleArgTypes ~= S[srcTag..markLastIdentifier];
	fill(S[markLastIdentifier..srcCursor]);
	sampleArgs ~= S[markLastIdentifier..srcCursor-1];
	fill("\n");
      }
      else if (parseCoverPointDecl()) {
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
	    "), q{ " ~ S[srcTag .. srcCursor-1] ~ "})";
	}
	else {
	  if (S[srcCursor] != ';') {
	    import std.conv;
	    assert (false, "expected ; at line " ~ srcLine.to!string);
	  }
	  srcCursor ++;
	  coverpointName = "CoverPoint!(typeof(" ~ name ~ "))";
	}
	if (cp_names.length == cpCount) {
	  import std.conv;
	  cp_name = "_esdl__coverpoint_" ~ cpCount.to!string;
	  cp_names ~= cp_name;
	}
	else {
	  cp_name = cp_names[$-1];
	}
	fill("alias ", cp_name, "_class = ", coverpointName, ";\n");
	fill(cp_name, "_class ", cp_name, ";\n");
	fill("class ", cp_name, "_override : ", cp_name,
	     "_class { \n override _esdl__T _esdl__t() { return ", name, "; }\n }\n");
	cpCount += 1;
      }
      else if (parseCrossDecl()) { // TODO
	
	cpCount += 1;
      }
      else {
	if (cp_names.length > cpCount) {
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
    }
    fill("this () { \n");
    foreach (cp_name; cp_names)
      fill(cp_name, " = new ", cp_name, "_override();\n");
    fill("}\n");
    fill("void sample(");
    for (int i = 0; i != sampleArgs.length; ++i) {
      if (i != 0) fill(",\n            ");
      fill(sampleArgTypes[i], sampleArgs[i]);
    }
    fill(") { \n");
    for (int i = 0; i != sampleArgs.length; ++i) {
      fill("  this.", sampleArgs[i], " = ", sampleArgs[i], ";\n");
    }
    foreach (cp_name; cp_names) {
      fill("  ", cp_name, ".sample();\n");
    }
    fill("}\n");
    fill("override double get_coverage() {
      double total = 0;
      size_t weightSum = 0;\n");
    foreach (cp_name; cp_names) {
      fill("total += ", cp_name, ".get_coverage() * ",
	   cp_name, ".get_weight();\n");
      fill("weightSum += ", cp_name, ".get_weight();\n");
    }
    fill("\n    return total/weightSum; }\n");
  }
}

string _esdl__parseCoverGroupString(string S)
{
  CoverGroupParser parser = CoverGroupParser(S);
  parser.parse();
  parser.setUp();
  parser.parse();
  return parser.buffer();
}

// mixin template CoverGroup (string S) {
//   class covergroup_name { // put name of covergroup instead
//     debug(CVRPARSER) {
//       pragma(msg, _esdl__parseCoverGroupString(S));
//     }
//     mixin(_esdl__parseCoverGroupString(S));
//   }
// }


