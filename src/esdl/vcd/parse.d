// Copyright: Coverify Systems Technology 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

// VCD Parser

// A VCD object corresponds to a VCD file
module esdl.vcd.parse;

import esdl.data.bvec;
import esdl.data.bstr;
import esdl.data.time;

import std.conv: to;
import std.string: isNumeric;	// required for timeScale

// beyond this size the parser would create a logicstring instead of
// an lvec for storing data.
enum uint MaxVectorSize = 1024; // 16384; // 32768; // 65536;

import core.bitop;

// A tightly packed fixed width vector of bits
struct VcdVec(size_t N) if (N > 0)
{

  static if(N <= 8)                     private alias ubyte  store_t;
  else static if(N <= 16)               private alias ushort store_t;
  else static if(N <= 32)               private alias uint   store_t;
  else static if(size_t.sizeof*8 == 32) private alias uint   store_t;
    else                                private alias ulong  store_t;

  private enum size_t STORESIZE =
    (8*store_t.sizeof+N-1)/(8*store_t.sizeof);

  private store_t[STORESIZE] _aval;
  private store_t[STORESIZE] _bval;

  auto setBit(size_t i, char b) {
    static if(STORESIZE == 1) {
      switch(b) {
      case '0':
	this._aval[0] &= ~(1L << i);
	this._bval[0] &= ~(1L << i);
	break;
      case '1':
	this._aval[0] |=  (1L << i);
	this._bval[0] &= ~(1L << i);
	break;
      case 'X':
      case 'x':
	this._aval[0] &= ~(1L << i);
	this._bval[0] |=  (1L << i);
	break;
      case 'Z':
      case 'z':
	this._aval[0] |=  (1L << i);
	this._bval[0] |=  (1L << i);
	break;
      default:
	assert(false, "Illegal character: " ~ b);
      }
    }
    else {
      switch(b) {
      case '0':
	btr((cast(size_t*) _aval.ptr), i);
	btr((cast(size_t*) _bval.ptr), i);
	break;
      case '1':
	bts((cast(size_t*) _aval.ptr), i);
	btr((cast(size_t*) _bval.ptr), i);
	break;
      case 'X':
      case 'x':
	btr((cast(size_t*) _aval.ptr), i);
	bts((cast(size_t*) _bval.ptr), i);
	break;
      case 'Z':
      case 'z':
	bts((cast(size_t*) _aval.ptr), i);
	bts((cast(size_t*) _bval.ptr), i);
	break;
      default:
	assert(false, "Illegal character: " ~ b);
      }
    }
  }
}

enum SCOPE_TYPE: byte
  {   BEGIN,
      FORK,
      FUNCTION,
      MODULE,
      TASK,
      }

enum VAR_TYPE: byte
  {   EVENT,
      INTEGER,
      PARAMETER,
      REAL,
      REALTIME,
      REG,
      SUPPLY0,
      SUPPLY1,
      TIME,
      TRI,
      TRIAND,
      TRIOR,
      TRIREG,
      TRI0,
      TRI1,
      WAND,
      WIRE,
      WOR,
      }

class VcdNode
{
  import std.array: split;
  string _name;
  // root will have null parent
  VcdScope _parent;
  VCD      _vcd;

  this(VcdScope parent, VCD vcd, string name) {
    _parent = parent;
    _vcd    = vcd;
    _name   = name;
    if(_parent !is null) {	// null for _root scope
      _parent._children ~= this;
    }
  }

  alias opCmp = Object.opCmp;

  // VcdNodes need to be sorted by their names
  public int opCmp(VcdNode other) {
    if(this._name < other._name) return -1;
    else if(this._name > other._name) return 1;
    else return 0;
  }

  public int opCmp(string other) {
    if(this._name < other) return -1;
    else if(this._name > other) return 1;
    else return 0;
  }

  final public VcdNode find(string name) {
    return findName(split(name, _vcd.delim()));
  }
  
  abstract VcdNode findName(string[] name);
}

class VcdScope: VcdNode
{
  import std.range;
  // keep this as a dynamic array so that sorting is easy
  string _scopeType;		// keep is string for flexibility
  VcdNode[] _children;
  this(VcdScope parent, VCD vcd, string name, string type) {
    super(parent, vcd, name);
    _scopeType = type;
  }

  override VcdNode findName(string[] name) {
    if(name.length == 0) return this;
    debug(FIND) {
      import std.stdio;
      writeln("Finding: ", name[0], " remaining:", name.length);
      foreach(ch; _children) {
	writeln(ch._name);
      }
    }
    // writeln("In: ", _children[0]._name);
    auto children = assumeSorted(_children);
    auto lb = children.lowerBound(name[0]);
    if(lb.length < _children.length) {
      auto child = _children[lb.length];
      if(child._name == name[0]) {
	debug(FIND) {
	  import std.stdio;
	  writeln("Found: ", name[0]);
	  writeln("Remaining: ", name[1..$]);
	}
	return child.findName(name[1..$]);
      }
    }
    return null;
  }
}

abstract class VcdVar: VcdNode
{
  uint _size;
  this(VcdScope parent, VCD vcd, string name, uint size) {
    super(parent, vcd, name);
    _size = size;
  }

  override VcdNode findName(string[] name) {
    if(name.length == 0) return this;
    else return null;
  }
  
  abstract void addValChange(uint timeStep, string value);

  // Takes too much memory
  // static VcdVar makeVarVec(size_t A=1, size_t N=64, size_t Z=128)
  //   (VcdScope parent, string name, uint size) {
  //   if(size > Z) {
  //     assert(false, "Can not handle variables of size > 65536");
  //   }
  //   else if(size == N) {
  //     alias T = VcdVec!N;
  //     return new VcdWave!T(parent, name, size);
  //   }
  //   else if(size < N) {
  //     return makeVarVec!(A, (N+A)/2, N)(parent, name, size);
  //   }
  //   else {
  //     return makeVarVec!(N, (N+Z)/2, Z)(parent, name, size);
  //   }
  // }

  static VcdVar makeVarVec(size_t A=0, size_t Z=MaxVectorSize/64)
    (VcdScope parent, VCD vcd, string name, uint size) {
    static if(A == 0) {
      if(size > MaxVectorSize) {
	return new VcdLogicStringWave(parent, vcd, name, size);
      }
      if(size <= 8) {
	return new VcdVecWave!8(parent, vcd, name, size);
      }
      else if(size <= 16) {
	return new VcdVecWave!16(parent, vcd, name, size);
      }
      else if(size <= 32) {
	return new VcdVecWave!32(parent, vcd, name, size);
      }
      else if(size <= 64) {
	return new VcdVecWave!64(parent, vcd, name, size);
      }
      else {
	return makeVarVec!(A+1, Z)(parent, vcd, name, size);
      }
    }
    else {			// static if(A != 1)
      size_t n = (size + 64 - 1) / 64;
      enum size_t N = (A + Z)/2;
      if(n == N) {	
	return new VcdVecWave!(N*64)(parent, vcd, name, size);
      }
      else if(n > N) {
	return makeVarVec!(N+1, Z)(parent, vcd, name, size);
      }
      else {
	return makeVarVec!(A, N)(parent, vcd, name, size);
      }
    }
  }
}

enum SIM_COMMAND: byte
  {   DUMPALL,
      DUMPOFF,
      DUMPON,
      DUMPVARS,
      COMMENT,
      }

// V is a type and can be
// bool     -- EVENT
// VcdVec!32 -- INTEGER
// VcdVec!n  -- PARAMETER, REG, SUPPLY0, SUPPLY1, TRI, TRIAND, TRIOR, TRIREG
//             TRI0, TRI1, WAND, WIRE, WOR
// VcdVec!64 -- time
// real     -- REAL
// real     -- REALTIME

struct VcdVecVal(V)
{
  uint _timeStep;
  V     _val;
  this(uint timeStep, V value) {
    _timeStep = timeStep;
    _val = value;
  }
}

class VcdStringWave: VcdVar
{
  VcdVecVal!string[] _wave;
  this(VcdScope parent, VCD vcd, string name, uint size) {
    super(parent, vcd, name, size);
  }
  override void addValChange(uint timeStep, string value) {
    _wave ~= VcdVecVal!string(timeStep, value);
  }
}

class VcdRealWave: VcdVar
{
  VcdVecVal!real[] _wave;
  this(VcdScope parent, VCD vcd, string name, uint size) {
    super(parent, vcd, name, size);
  }
  override void addValChange(uint timeStep, string value) {
    if(value[0] != 'r' && value[0] != 'R') {
      assert(false, "Illegal real value: " ~ value);
    }
    if(!isNumeric(value[1..$])) {
      assert(false, "Illegal real value: " ~ value);
    }
    real val = value[1..$].to!real;
    _wave ~= VcdVecVal!real(timeStep, val);
  }
}
  

class VcdCommandWave: VcdVar
{
  VcdVecVal!SIM_COMMAND[] _wave;
  this(VcdScope parent, VCD vcd, string name, uint size) {
    super(parent, vcd, name, size);
  }
  override void addValChange(uint timeStep, string word) {
    SIM_COMMAND* cmd;
    if((cmd = word in VCD._commandTypeLookup) !is null) {
      _wave ~= VcdVecVal!SIM_COMMAND(timeStep, *cmd);
    }
    else {
      assert(false, "UNEXPECTED command: " ~ word);
    }
  }
}

class VcdEventWave: VcdVar
{
  VcdVecVal!bool[] _wave;
  this(VcdScope parent, VCD vcd, string name, uint size) {
    super(parent, vcd, name, size);
  }
  override void addValChange(uint timeStep, string value) {
    if(value[0] != '1') {
      assert(false, "Illegal value for an event: " ~ value[0]);
    }
    else {
      _wave ~= VcdVecVal!bool(timeStep, true);
    }
  }
}
  
class VcdLogicStringWave: VcdVar
{
  VcdVecVal!lstr[] _wave;
  this(VcdScope parent, VCD vcd, string name, uint size) {
    super(parent, vcd, name, size);
  }

  override void addValChange(uint timeStep, string value) {
    lstr val;			// all 0s
    val.length = _size;
    // left fill bit in value -- 
    char leftFill;
    // 0th char is 'b' or 'B'      

    if(value[0] != 'b' && value[0] != 'B') {
      assert(false, "Illegal vector value: " ~ value);
    }
    switch(value[1]) {
    case '0':
    case '1':
      leftFill = '0';
      break;
    case 'x':
    case 'X':
      leftFill = 'X';
      break;
    case 'z':
    case 'Z':
      leftFill = 'Z';
      break;
    default:
      assert(false, "Illegal vector value: " ~ value);
    }
      
    for (uint n=0; n!=_size; ++n) {
      char nBit;
      if(value.length > n + 1) {
	nBit = value[$-1-n];
      }
      else {
	nBit = leftFill;
      }
      switch(nBit) {
      case '0':
	val[n] = LOGIC_0;
	break;
      case '1':
	val[n] = LOGIC_1;
	break;
      case 'x':
      case 'X':
	val[n] = LOGIC_X;
	break;
      case 'z':
      case 'Z':
	val[n] = LOGIC_Z;
	break;
      default:
	assert(false, "Illegal vector value: " ~ value);
      }
    }
    _wave ~= VcdVecVal!lstr(timeStep, val);
  }
}  


class VcdVecWave(size_t N): VcdVar
{
  VcdVecVal!(VcdVec!N)[] _wave;
  this(VcdScope parent, VCD vcd, string name, uint size) {
    super(parent, vcd, name, size);
  }

  override void addValChange(uint timeStep, string value) {
    VcdVec!N val;			// all 0s
    // left fill bit in value -- 
    char leftFill;
    // 0th char is 'b' or 'B'
    if(_size == 1 && value.length == 1) {
      val.setBit(0, value[0]);
    }
    else {
      if(value[0] != 'b' && value[0] != 'B') {
	assert(false, "Illegal vector value: " ~ value);
      }
      switch(value[1]) {
      case '0':
      case '1':
	leftFill = '0';
	break;
      case 'x':
      case 'X':
	leftFill = 'X';
	break;
      case 'z':
      case 'Z':
	leftFill = 'Z';
	break;
      default:
	assert(false, "Illegal vector value: " ~ value);
      }
      
      for (uint n=0; n!=_size; ++n) {
	char nBit;
	if(value.length > n + 1) {
	  nBit = value[$-1-n];
	}
	else {
	  nBit = leftFill;
	}
	val.setBit(n, nBit);
      }
    }
    _wave ~= VcdVecVal!(VcdVec!N)(timeStep, val);
  }
};

class VcdFile
{
  import std.stdio;
  private this(string name) {
    _name = name;
    _file = File(name, "r");
  }
  File     _file;
  string   _name;
  char[]   _buf;
  char[][] _words;
  // index of the word to return when nextWord called
  size_t   _index = 0;
  // line number of the file
  size_t   _lnum = 0;
  string nextWord() {
    string word = getNextWord();
    if(word is null) {
      assert(false, "Unexpected EOF");
    }
    return word;
  }
  string getNextWord() {
    while(_index == _words.length) {
      import std.array;
      ++_lnum;
      if(_file.readln(_buf) == 0) {
	return null;
      }
      _words = split(_buf);
      _index = 0;
    }
    return cast(string) _words[_index++];
  }
  string errorString() {
    import std.string;
    return format("Unexpected token '%s' while parsing VCD file: " ~
		  "%s at line number %d", _words[_index-1], _name, _lnum);
  }
}

class VCD
{
  public this(string name) {
    _file = new VcdFile(name);
    _timeStamps ~= 0;
    _comments = new VcdStringWave(null, this, "comments", 1);
    _commands = new VcdCommandWave(null, this, "commands", 1);
    _dumpon =   new VcdEventWave(null, this, "$dumpon", 1);
    _dumpoff =  new VcdEventWave(null, this, "$dumpoff", 1);
    _dumpall =  new VcdEventWave(null, this, "$dumpall", 1);
    _dumpvars = new VcdEventWave(null, this, "$dumpvars", 1);
    parseDeclarations();
    parseSimulation();
  }

  char _delim = '.';

  void setDelimiter(char d) {
    _delim = d;
  }

  char delim() {
    return _delim;
  }
  
  VcdFile _file;
  string  _date;
  string  _version;
  Time    _timeScale;
  // comment in the definition area
  string  _comment;
  VcdScope _root;
  // commands along with timestamps
  VcdCommandWave      _commands;
  VcdEventWave        _dumpon;
  VcdEventWave        _dumpoff;
  VcdEventWave        _dumpall;
  VcdEventWave        _dumpvars;
  // comments in the dump area along with timestamps
  VcdStringWave       _comments;

  // associative array that keeps a lookup for the string symbols and
  // the corresponding variable
  VcdVar[string] _lookup;

  ulong[] _timeStamps;

  static VAR_TYPE[string] _varTypeLookup;
  static SIM_COMMAND[string] _commandTypeLookup;

  static this() {
    _varTypeLookup = ["event":VAR_TYPE.EVENT,
		      "integer":VAR_TYPE.INTEGER,
		      "parameter":VAR_TYPE.PARAMETER,
		      "real":VAR_TYPE.REAL,
		      "realtime":VAR_TYPE.REALTIME,
		      "reg":VAR_TYPE.REG,
		      "supply0":VAR_TYPE.SUPPLY0,
		      "supply1":VAR_TYPE.SUPPLY1,
		      "time":VAR_TYPE.TIME,
		      "tri":VAR_TYPE.TRI,
		      "triand":VAR_TYPE.TRIAND,
		      "trior":VAR_TYPE.TRIOR,
		      "trireg":VAR_TYPE.TRIREG,
		      "tri0":VAR_TYPE.TRI0,
		      "tri1":VAR_TYPE.TRI1,
		      "wand":VAR_TYPE.WAND,
		      "wire":VAR_TYPE.WIRE,
		      "wor":VAR_TYPE.WOR,
		      ];
    _commandTypeLookup = ["$dumpall":SIM_COMMAND.DUMPALL,
			  "$dumpoff":SIM_COMMAND.DUMPOFF,
			  "$dumpon":SIM_COMMAND.DUMPON,
			  "$dumpvars":SIM_COMMAND.DUMPVARS,
			  ];
  }

  // enum DECLARATION_COMMAND: byte
  //   {   NONE,
  // 	COMMENT,
  // 	DATE,
  // 	ENDDEFINITIONS,
  // 	SCOPE,
  // 	TIMESCALE,
  // 	UPSCOPE,
  // 	VAR,
  // 	VERSION,
  // 	}

  VcdNode find(string name) {
    return _root.find(name);
  }
  
  void parseDeclarationComment() {
    string word;
    while((word = _file.nextWord()) != "$end") {
      _comment ~= word;
      _comment ~= " ";
    }
    _comment.length -= 1;
    return;
  }

  void parseDate() {
    string word;
    while((word = _file.nextWord()) != "$end") {
      _date ~= word;
      _date ~= " ";
    }
    _date.length -= 1;
    return;
  }
  
  void parseVersion() {
    string word;
    while((word = _file.nextWord()) != "$end") {
      _version ~= word;
      _version ~= " ";
    }
    _version.length -= 1;
    return;
  }
  
  void parseTimeScale() {
    string word;
    int val;
    string values="100000000000000000000";
    word = _file.nextWord();
    if(word == values[0..word.length]) {
      val = word.to!int;
      word = _file.nextWord();
    }
    // cover the case where time is specified as 1s (without space)
    else if(word[0..$-1] == values[0..word.length-1]) {
      val = word[0..$-1].to!int;
      word = word[$-1..$];
    }
    // cover the case where time is specified as 1ns (without space)
    else if(word[0..$-2] == values[0..word.length-2]) {
      val = word[0..$-2].to!int;
      word = word[$-2..$];
    }
    else {
      assert(false, _file.errorString);
    }

    if(word == "s") {
      _timeScale = val.sec;
    }
    else if(word == "ms") {
      _timeScale = val.msec;
    }
    else if(word == "us") {
      _timeScale = val.usec;
    }
    else if(word == "ns") {
      _timeScale = val.nsec;
    }
    else if(word == "ps") {
      _timeScale = val.psec;
    }
    else if(word == "fs") {
      _timeScale = val.fsec;
    }
    else {
      assert(false, _file.errorString);
    }

    word = _file.nextWord();
    if(word != "$end") {
      assert(false, _file.errorString);
    }
  }

  void parseVar(VcdScope currScope) {
    VAR_TYPE varType;
    uint size;
    string id;
    string name;
    auto typeStr = _file.nextWord();
    auto vt = typeStr in _varTypeLookup;
    if(vt is null) {
      assert(false, _file.errorString);
    }
    else {
      varType = *vt;
    }
    auto sizeStr = _file.nextWord();
    if(! isNumeric(sizeStr)) {
      assert(false, _file.errorString);
    }
    else {
      size = sizeStr.to!int;
    }
    id   = _file.nextWord().dup;
    name = _file.nextWord().dup;
    string arrayInfo;
    if((arrayInfo = _file.nextWord()) != "$end") { // this could be the array info
      name ~= arrayInfo;
      if(_file.nextWord() != "$end") {
	assert(false, _file.errorString);
      }
    }
    VcdVar var;
    switch(varType) {
    case VAR_TYPE.EVENT:
      var = new VcdEventWave(currScope, this, name, 1);
      break;
    case VAR_TYPE.REAL:
    case VAR_TYPE.REALTIME:
      var = new VcdRealWave(currScope, this, name, 1);
      break;
    default:			// VcdVec!size
      // if(size >= 1024) assert(false, "Too big vector size 1024");
      // mixin(genVarCode(0, 64));
      VcdVar *var_;
      if((var_ = (id in _lookup)) !is null) {
	var = *var_;
	// assert(false, "Duplicate Variable ID: " ~ id);
      }
      else {
	var = VcdVar.makeVarVec(currScope, this, name, size);
	_lookup[id] = var;
      }
      break;
    }
  }
  
// V is a type and can be
// bool     -- EVENT
// VcdVec!32 -- INTEGER
// VcdVec!n  -- PARAMETER, REG, SUPPLY0, SUPPLY1, TRI, TRIAND, TRIOR, TRIREG
//             TRI0, TRI1, WAND, WIRE, WOR
// VcdVec!64 -- TIME
// real     -- REAL
// real     -- REALTIME

  void parseScope(VcdScope currScope) {
    import std.algorithm;
    if(_file.nextWord() != "$end") {
      assert(false, _file.errorString);
    }
    while(true) {
      auto word = _file.nextWord();
      if(word == "$scope") {
	string scopeType = _file.nextWord().dup;
	string name = _file.nextWord().dup;
	VcdScope child = new VcdScope(currScope, this, name, scopeType);
	parseScope(child);
      }
      else if(word == "$upscope") {
	if(_file.nextWord() != "$end") {
	  assert(false, _file.errorString);
	}
	// before we return, sort the currScope
	sort(currScope._children);
	return;
      }
      else if(word == "$var") {
	parseVar(currScope);
      }
      else {
	assert(false, _file.errorString);
      }
    }
  }
  
  void parseDeclarations() {
    string word;
    assert(_root is null);
    _root = new VcdScope(null, this, "root", "root"); // root has null parent
    while((word = _file.nextWord()) !is null) {
      if(word == "$comment") {
	assert(_comment is null);
	parseDeclarationComment();
      }
      else if(word == "$date") {
	assert(_date is null);
	parseDate();
      }
      else if(word == "$enddefinitions") {
	word = _file.nextWord();
	if(word != "$end") {
	  assert(false, _file.errorString);
	}
	else {
	  return;
	}
      }
      else if(word == "$scope") {
	string scopeType = _file.nextWord().dup;
	string name = _file.nextWord().dup;
	VcdScope child = new VcdScope(_root, this, name, scopeType);
	parseScope(child);
      }
      else if(word == "$timescale") {
	assert(_timeScale.isZero());
	parseTimeScale();
      }
      else if(word == "$version") {
	assert(_version is null);
	parseVersion();
      }
      else {
	assert(false, _file.errorString);
      }
    }
  }

  void parseSimulationComment() {
    string word;
    string comment;
    while((word = _file.nextWord()) != "$end") {
      comment ~= word;
      comment ~= " ";
    }
    _comments.addValChange(cast(uint) (_timeStamps.length-1), comment[0..$-1]);
  }

  void parseValChange(string word) {
    if(word[0] == '0' || word[0] == '1' ||
       word[0] == 'x' || word[0] == 'X' ||
       word[0] == 'z' || word[0] == 'Z') { // scalar value
      string id = word[1..$];
      auto wave = id in _lookup;
      (*wave).addValChange(cast(uint) (_timeStamps.length-1), word[0..1]);
      if(id is null) {
	assert(false, _file.errorString());
      }
    }
    else if(word[0] == 'b' || word[0] == 'B') { // vector value
      string id = _file.nextWord();
      auto wave = id in _lookup;
      if(wave is null) {
	assert(false, _file.errorString());
      }
      if((*wave)._size < MaxVectorSize) {
	(*wave).addValChange(cast(uint) (_timeStamps.length-1), word);
      }
      else {
	(*wave).addValChange(cast(uint) (_timeStamps.length-1), word);
      }
    }
    else if(word[0] == 'r' || word[0] == 'R') {	// vector real
      string id = _file.nextWord();
      auto wave = id in _lookup;
      (*wave).addValChange(cast(uint) (_timeStamps.length-1), word);
      if(id is null) {
	assert(false, _file.errorString());
      }
    }
  }
  
  void parseSimulationCommand(string word) {
    _commands.addValChange(cast(uint) (_timeStamps.length-1), word);
    SIM_COMMAND* command;
    if((command = (word in _commandTypeLookup)) !is null) {
      switch(*command) {
      case SIM_COMMAND.DUMPON:
	_dumpon.addValChange(cast(uint) (_timeStamps.length-1), "1");
	break;
      case SIM_COMMAND.DUMPOFF:
	_dumpoff.addValChange(cast(uint) (_timeStamps.length-1), "1");
	break;
      case SIM_COMMAND.DUMPALL:
	_dumpall.addValChange(cast(uint) (_timeStamps.length-1), "1");
	break;
      case SIM_COMMAND.DUMPVARS:
	_dumpvars.addValChange(cast(uint) (_timeStamps.length-1), "1");
	break;
      default: break;
      }
    }
    string value;
    while((value = _file.nextWord()) != "$end") {
      parseValChange(value);
    }
  }

  void parseSimulation() {
    string word;
    SIM_COMMAND *cmd;
    while((word = _file.getNextWord()) != null) {
      if(word == "$comment") {
	parseSimulationComment();
      }
      else if(word[0] == '#') {	// timestamp
	string timeStr = word[1..$];
	if(! isNumeric(timeStr)) {
	  assert(false, _file.errorString);
	}
	else {
	  _timeStamps ~= timeStr.to!ulong;
	}
      }
      else if(word[0] == '$') {
	parseSimulationCommand(word);
      }
      else {
	parseValChange(word);
      }
    }
  }
}
