module esdl.solver.mono;

import esdl.solver.base;
import esdl.rand.expr;
import esdl.rand.base;
import esdl.rand.misc;
import esdl.rand.proxy: _esdl__Proxy;
enum NumType: ubyte {INT, UINT, LONG, ULONG};
enum Type: ubyte { NUM, ADD, SUB, RAND};
enum RangeType: ubyte {STA, DYN, NUL};

debug (MONOSOLVER){
  debug = CHECKMONO;
}

struct Range (T)
{
  T[2] _sRange;
  T[] _dRange;
  RangeType type;
  this(ref T[] r){
    type = RangeType.DYN;
    _dRange = r;
  }
  this(ref T[2] r){
    type = RangeType.STA;
    _sRange = r;
  }
  this(bool a){
    type = RangeType.NUL;
  }
  RangeType getType(){
    return type;
  }
  ref T[2] getS(){
    assert (type == RangeType.STA);
    return _sRange;
  }
  ref T[] getD(){
    assert (type == RangeType.DYN);
    return _dRange;
  }
  void setType(RangeType x){
    type = x;
  }
}
struct Term
{
  ulong _ulong;
  uint _uint;
  Type _type;
  NumType _numType;
  bool _isNumber;
  
  this(ulong expr) {
    _ulong = expr;
    _isNumber = true;
    _numType = NumType.ULONG;
    _type = Type.NUM;
  }

  this(uint expr) {
    _uint = expr;
    _isNumber = true;
    _numType = NumType.UINT;
    _type = Type.NUM;
  }
  
  this(long expr) {
    _ulong = expr;
    _isNumber = true;
    _numType = NumType.LONG;
    _type = Type.NUM;
  }
  
  this(int expr) {
    _uint = expr;
    _isNumber = true;
    _numType = NumType.INT;
    _type = Type.NUM;
  }
  
  void setNumType(NumType t){
    assert(_type != Type.NUM);
    _numType = t;
  }
  
  this (char op){
    _isNumber = false;
    switch (op){
    case '+':
      _type = Type.ADD;
      break;
    case '-':
      _type = Type.SUB;
      break;
    case 'R':
      _type = Type.RAND;
      break;
    default:
      assert(false);
    }
  }
  
  Type getType(){
    return _type;
  }
  NumType getNumType(){
    return _numType;
  }
  ulong getLong(){
    assert (_numType == NumType.LONG || _numType == NumType.ULONG);
    return _ulong;
  }
  uint getInt(){
    assert (_numType == NumType.INT || _numType == NumType.UINT);
    return _uint;
  }
  bool isNum(){
    return _isNumber;
  }
  Term opBinary(string op)(Term rhs){
    final switch (_numType){
    case NumType.INT:
      final switch (rhs.getNumType()){
      case NumType.INT:
	mixin ("return Term(cast(int)(this.getInt())"~op~"cast(int)(rhs.getInt()));");
      case NumType.LONG:
	mixin ("return Term(cast(int)(this.getInt())"~op~"cast(long)(rhs.getLong()));");
      case NumType.UINT:
	mixin ("return Term(cast(int)(this.getInt())"~op~"(rhs.getInt()));");
      case NumType.ULONG:
	mixin ("return Term(cast(int)(this.getInt())"~op~"(rhs.getLong()));");
      }
    case NumType.LONG:
      final switch (rhs.getNumType()){
      case NumType.INT:
	mixin ("return Term(cast(long)(this.getLong())"~op~"cast(int)(rhs.getInt()));");
      case NumType.LONG:
	mixin ("return Term(cast(long)(this.getLong())"~op~"cast(long)(rhs.getLong()));");
      case NumType.UINT:
	mixin ("return Term(cast(long)(this.getLong())"~op~"(rhs.getInt()));");
      case NumType.ULONG:
	mixin ("return Term(cast(long)(this.getLong())"~op~"(rhs.getLong()));");
      }
    case NumType.UINT:
      final switch (rhs.getNumType()){
      case NumType.INT:
	mixin ("return Term((this.getInt())"~op~"cast(int)(rhs.getInt()));");
      case NumType.LONG:
	mixin ("return Term((this.getInt())"~op~"cast(long)(rhs.getLong()));");
      case NumType.UINT:
	mixin ("return Term((this.getInt())"~op~"(rhs.getInt()));");
      case NumType.ULONG:
	mixin ("return Term((this.getInt())"~op~"(rhs.getLong()));");
      }
    case NumType.ULONG:
      final switch (rhs.getNumType()){
      case NumType.INT:
	mixin ("return Term((this.getLong())"~op~"cast(int)(rhs.getInt()));");
      case NumType.LONG:
	mixin ("return Term((this.getLong())"~op~"cast(long)(rhs.getLong()));");
      case NumType.UINT:
	mixin ("return Term((this.getLong())"~op~"(rhs.getInt()));");
      case NumType.ULONG:
	mixin ("return Term((this.getLong())"~op~"(rhs.getLong()));");
      }
    }
  }
}


class CstMonoSolver (S): CstSolver
{
  bool _hasRand ;
  Term [] _evalStack;
  byte _endFlag = 0;
  Range!S [] _rangeStack;
  S[] _finalRange;
  ulong _count;
  _esdl__Proxy _proxy;
  Term [] _insideEqual;
  Term [] _insideRange; // inclusive
  debug (CHECKMONO){
    bool _debugFlag = false;
    uint _currentRangePos = 0;
    bool _inRangeFlag = false;
    S[] _testfinalRange;
  }
  this(){
    super("");
  }
  this(string signature, CstPredGroup group) {
    super(signature);
  }
  override string describe() {
    return "Mono Solver"  ~ super.describe();
  }
  override void pushToEvalStack(CstDomain domain) {
    if (domain.isRand()) {
      debug (MONOSOLVER){
	if(_debugFlag){
	  import std.stdio;
	  _evalStack ~= Term(nextRangeVal());
	  writeln("value from domain ",nextRangeVal() , " of type ", numTypeToStr(_evalStack[$-1].getNumType()), " pushed to _evalStack");
	  return;
	}
      } 
      if (_hasRand){
	_endFlag = 3;
	debug (MONOSOLVER){
	  import std.stdio;
	  writeln("same domain used twice in one inequality, mono cant solve this");
	}
	return;
      }
      uint n = domain.bitcount();
      /*if (n>32){
	if (domain.signed()){
	  Term a = Term('R');
	  a.setNumType(NumType.LONG);
	  _evalStack ~= a;
	}
	else {
	  Term a = Term('R');
	  a.setNumType(NumType.ULONG);
	  _evalStack ~= a;
	}
      }
      else {
	if (domain.signed()){
	  Term a = Term('R');
	  a.setNumType(NumType.INT);
	  _evalStack ~= a;
	}
	else {
	  Term a = Term('R');
	  a.setNumType(NumType.UINT);
	  _evalStack ~= a;
	}
	}*/
      if (n>32 && n<64){
	Term a = Term('R');
	a.setNumType(NumType.LONG);
	_evalStack ~= a;
      }
      else if (n < 32){
	Term a = Term('R');
	a.setNumType(NumType.INT);
	_evalStack ~= a;
      }
      else if(n == 32){
	if (domain.signed()){
	  Term a = Term('R');
	  a.setNumType(NumType.INT);
	  _evalStack ~= a;
	}
	else {
	  Term a = Term('R');
	  a.setNumType(NumType.UINT);
	  _evalStack ~= a;
	}
      }
      else {
	if (domain.signed()){
	  Term a = Term('R');
	  a.setNumType(NumType.LONG);
	  _evalStack ~= a;
	}
	else {
	  Term a = Term('R');
	  a.setNumType(NumType.ULONG);
	  _evalStack ~= a;
	}
      } 
      _hasRand = true;
      debug (MONOSOLVER){
	import std.stdio;
	writeln("rand of type ", numTypeToStr(_evalStack[$-1].getNumType()), " pushed to _evalStack");
      }
    }
    else {
      uint n = domain.bitcount();
      /*if (n>32){
	if (domain.signed()){
	  _evalStack ~= Term(cast(long)domain.value()); 
	}
	else {
	  _evalStack ~= Term(cast(ulong)domain.value());
	}
      }
      else {
	if (domain.signed()){
	  _evalStack ~= Term(cast(int)domain.value()); 
	}
	else {
	  _evalStack ~= Term(cast(uint)domain.value());
	}
	}*/
      if (n>32 && n<64){
	_evalStack ~= Term(cast(long)domain.value()); 
      }
      else if (n < 32){
	_evalStack ~= Term(cast(int)domain.value()); 
      }
      else if(n == 32){
	if (domain.signed()){
	  _evalStack ~= Term(cast(int)domain.value()); 
	}
	else {
	  _evalStack ~= Term(cast(uint)domain.value()); 
	}
      }
      else {
	if (domain.signed()){
	  _evalStack ~= Term(cast(long)domain.value()); 
	}
	else {
	  _evalStack ~= Term(cast(ulong)domain.value()); 
	}
      }
      debug (MONOSOLVER){
	import std.stdio;
	writeln("variable ",domain.value()," of type ", numTypeToStr(_evalStack[$-1].getNumType()), " pushed to _evalStack");
      }
    }
  }
  override void pushToEvalStack(CstValue value) {
    uint n = value.bitcount();
    /*if (n>32){
      if (value.signed()){
	_evalStack ~= Term(cast(long)value.evaluate()); 
      }
      else {
	_evalStack ~= Term(cast(ulong)value.evaluate());
      }
    }
    else {
      if (value.signed()){
	_evalStack ~= Term(cast(int)value.evaluate()); 
      }
      else {
	_evalStack ~= Term(cast(uint)value.evaluate());
      }
    }*/
    
    if (n>32 && n<64){
      _evalStack ~= Term(cast(long)value.evaluate()); 
    }
    else if (n < 32){
      _evalStack ~= Term(cast(int)value.evaluate()); 
    }
    else if(n == 32){
      if (value.signed()){
	_evalStack ~= Term(cast(int)value.evaluate()); 
      }
      else {
	_evalStack ~= Term(cast(uint)value.evaluate()); 
      }
    }
    else {
      if (value.signed()){
	_evalStack ~= Term(cast(long)value.evaluate()); 
      }
      else {
	_evalStack ~= Term(cast(ulong)value.evaluate()); 
      }
    }
    debug (MONOSOLVER){
      import std.stdio;
      writeln("value ",value.evaluate()," of type ", numTypeToStr(_evalStack[$-1].getNumType()), " pushed to _evalStack");
    }
  }
  override void pushToEvalStack(ulong value, uint bitcount, bool signed){
    
    /*if (bitcount>32){
      if (signed){
	_evalStack ~= Term(cast(long)value); 
      }
      else {
	_evalStack ~= Term(cast(ulong)value);
      }
    }
    else {
      if (signed){
	_evalStack ~= Term(cast(int)value); 
      }
      else {
	_evalStack ~= Term(cast(uint)value);
      }
      }*/
    
    if (bitcount>32 && bitcount<64){
      _evalStack ~= Term(cast(long)value); 
    }
    else if (bitcount < 32){
      _evalStack ~= Term(cast(int)value); 
    }
    else if(bitcount == 32){
      if (signed){
	_evalStack ~= Term(cast(int)value); 
      }
      else {
	_evalStack ~= Term(cast(uint)value); 
      }
    }
    else {
      if (signed){
	_evalStack ~= Term(cast(long)value); 
      }
      else {
	_evalStack ~= Term(cast(ulong)value); 
      }
    }
    debug (MONOSOLVER){
      import std.stdio;
      writeln("constant ",value," of type ", numTypeToStr(_evalStack[$-1].getNumType()), " pushed to _evalStack");
    }
  }
  override void pushToEvalStack(bool value){
    debug (MONOSOLVER){
      import std.stdio;
      writeln("bool value ",value, " pushed to RangeStack");
    }
    if(value){
      S[2] temp = [S.min,S.max];
      _rangeStack ~= Range!S(temp);
    }
    else{
      _rangeStack ~= Range!S(false);
    }
  }
  override void pushIndexToEvalStack(ulong value){
    _endFlag = 3;
  }
  void negateLogic(ref CstCompareOp c){
    final switch (c){
    case CstCompareOp.EQU:
      c = CstCompareOp.NEQ;
      break;
    case CstCompareOp.NEQ:
      c = CstCompareOp.EQU;
      break;
    case CstCompareOp.LTH:
      c = CstCompareOp.GTE;
      break;
    case CstCompareOp.GTH:
      c = CstCompareOp.LTE;
      break;
    case CstCompareOp.LTE:
      c = CstCompareOp.GTH;
      break;
    case CstCompareOp.GTE:
      c = CstCompareOp.LTH;
      break;
    }
  }
  debug (CHECKMONO){
    S nextRangeVal(){
      if(_inRangeFlag){
	return _finalRange[_currentRangePos];
      }
      else {
	if (_currentRangePos %2 == 0){
	  return _finalRange[_currentRangePos] - 1;
	}
	else {
	  return _finalRange[_currentRangePos] + 1;
	}
      }
    }
  }
  void resetSolver () {
    _hasRand = false;
    _evalStack.length = 0;
    _endFlag = 0;
    _rangeStack.length = 0;
    _finalRange.length = 0;
    _count = 0;
    _proxy = null;
  
    debug (CHECKMONO){
      _debugFlag = false;
      _currentRangePos = 0;
      _inRangeFlag = false;
      _testfinalRange.length = 0;
    }
  }
  void trim(int bitcount, bool signed){
    if(signed){
      S a = 1<<(bitcount-1);
      S[2] x = [-a, a-1];
      ANDRANGE(_finalRange, x);
    }
    else {
      S a = 1<<(bitcount);
      S[2] x = [0, a-1];
      ANDRANGE(_finalRange, x);
    }
  }
  override bool solve(CstPredGroup group) {
    CstDomain [] doms = group.domains();
    assert (doms.length == 1);
    CstPredicate [] predSet = group.predicates();
    _finalRange = [S.min, S.max];
    _proxy = group.getProxy();
    foreach (pred; predSet){
      reset();
      pred.visit(this);
      if (_endFlag == 3){
	resetSolver();
	return false;
      }
      if(_endFlag == 1){
	assert(false, "no solutions found");
      }
      assert(_rangeStack.length == 1);
      debug (MONOSOLVER){
	import std.stdio;
	writeln("range for predicate ",pred.describe(), " is:");
	displayRangeStack(_rangeStack);
      }
      if(_rangeStack[0].getType() == RangeType.DYN){
	ANDRANGE(_finalRange, _rangeStack[0].getD());
      }
      else if(_rangeStack[0].getType() == RangeType.STA){
	ANDRANGE(_finalRange, _rangeStack[0].getS());
      }
      else{
	_endFlag = 1;
	assert(false, "no solutions found");
      }
      debug (MONOSOLVER){
	import std.stdio;
	writeln("_finalRange after this predicate is :");
	display(_finalRange);
      }
    }
    _rangeStack.length = 0;
    if(_finalRange.length == 0){
      assert(false, "no solutions found");
    }
    debug (CHECKMONO){
      _debugFlag = true;
      import std.conv;
      while (_currentRangePos < _finalRange.length){
	_testfinalRange = [S.min, S.max];
	foreach (pred; predSet){
	  reset();
	  pred.visit(this);
	  assert(_rangeStack.length == 1);
	  if(_rangeStack[0].getType() == RangeType.DYN){
	    assert(_rangeStack[0].getD() == [S.min, S.max]);
	  }
	  else if(_rangeStack[0].getType() == RangeType.STA){
	    assert(_rangeStack[0].getS() == [S.min, S.max]);
	  }
	  else{
	    _testfinalRange.length = 0;
	  }
	}
	if(_testfinalRange.length == 0){
	  assert(!isInRange(nextRangeVal(), _finalRange), "the value " ~to!string(nextRangeVal()) ~ " is in range yet it doesnt satisfy the predgroup");
	}
	else {
	  assert(_testfinalRange == [S.min, S.max]);
	  assert(isInRange(nextRangeVal(), _finalRange), "the value " ~ to!string(nextRangeVal()) ~ " is not in range yet it satisfies the predgroup");
	}
	if(!_inRangeFlag){
	  _inRangeFlag = true;
	}
	else {
	  _inRangeFlag = false;
	  _currentRangePos += 1; 
	}
	_rangeStack.length = 0;
      }
    }
    debug (MONOSOLVER){
      import std.stdio;
      writeln("all edge elements of the range tested successfully");
    }
    int bitc = doms[0].bitcount();
    if(bitc != 32 && bitc != 64){
      trim(bitc, doms[0].signed());
      debug (MONOSOLVER){
	import std.stdio;
	writeln("reducing _finalRange to fit in bitcount ", bitc);
	writeln("finalRange now: ");
	display(_finalRange);
      }
    }
    _count = counter();
    auto rand = _proxy._esdl__rGen.gen(0, _count);
    ulong num = choose(rand);
    doms[0].setVal(num);
    debug (MONOSOLVER){
      import std.stdio;
      writeln("count for the range is: " ,_count);
      writeln("random number generated is (between 0 and count): " ,rand);
      writeln("random number chosen from range: " ,num);
      assert (isInRange(cast(S)num, _finalRange), "chosen number doesnt fall in range");
    }
    resetSolver();
    return true;
  }
  
  void reset(){
    _hasRand = false;
    _rangeStack.length = 0;
  }
  
  void NotNum(ref Term a){
    switch (a.getNumType()){
    case NumType.INT, NumType.UINT:
      a = Term(!(a.getInt()));
      break;
    case NumType.LONG, NumType.ULONG:
      a = Term(!(a.getLong()));
      break;
    default:
      assert(false);
    }
  }
  
  NumType determineType(NumType a, NumType b){
    if (a > b){
      return a;
    }
    return b;
  }
  
  override void processEvalStack(CstVectorOp op) {
    _endFlag = 3;
    //assert (false, "CstVectorOp is handled only by SMT solvers");
  }

  override void processEvalStack(CstUnaryOp op) {
    if(checkError()){
      return;
    }
    debug (MONOSOLVER){
      import std.stdio;
      final switch (op) {
      case CstUnaryOp.NOT:
	writeln("Unary operator NOT used on evalStack");
	break;
      case CstUnaryOp.NEG:
	writeln("Unary operator NEG used on evalStack");
	break;
      }
    }
    final switch (op) {
    case CstUnaryOp.NOT:
      if (_evalStack[$-1].isNum()){
	NotNum(_evalStack[$-1]);
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstUnaryOp.NEG:
      if (_evalStack[$-1].isNum()){
	int c = 0;
	Term temp = Term(c);
	Term e = temp - _evalStack[$-1];
	_evalStack.length -=1;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    }
    debug (MONOSOLVER){
      import std.stdio;
      if(_endFlag == 3){
	writeln("cannot process unary operator");
	writeln("THE PREDICATE IS NOT SOLVEABLE BY MONOSOLVER");
      }
    }
  }
  
  override void processEvalStack(CstBinaryOp op){
    if(checkError()){
      return;
    }
    debug (MONOSOLVER){
      import std.stdio;
      final switch (op) {
      case CstBinaryOp.AND:
	writeln("Binary operator AND used on evalStack");
	break;
      case CstBinaryOp.OR:
	writeln("Binary operator OR used on evalStack");
	break;
      case CstBinaryOp.ADD:
	writeln("Binary operator ADD used on evalStack");
	break;
      case CstBinaryOp.SUB:
	writeln("Binary operator SUB used on evalStack");
	break;
      case CstBinaryOp.XOR:
	writeln("Binary operator XOR used on evalStack");
	break;
      case CstBinaryOp.MUL:
	writeln("Binary operator MUL used on evalStack");
	break;
      case CstBinaryOp.DIV:
	writeln("Binary operator DIV used on evalStack");
	break;
      case CstBinaryOp.LSH:
	writeln("Binary operator LSH used on evalStack");
	break;
      case CstBinaryOp.RSH:
	writeln("Binary operator RSH used on evalStack");
	break;
      case CstBinaryOp.LRSH:
	writeln("Binary operator LRSH used on evalStack");
	break;
      case CstBinaryOp.REM:
	writeln("Binary operator REM used on evalStack");
	break;
      }
    }
    final switch (op) {
    case CstBinaryOp.AND:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] & _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.OR:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] | _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.XOR:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] ^ _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.ADD:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] + _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	Term a = Term('+');
	a.setNumType(determineType(_evalStack[$-1].getNumType(), _evalStack[$-2].getNumType()));
	_evalStack ~= a;
	debug (MONOSOLVER){
	  import std.stdio;
	  writeln("Term '+' of type ", numTypeToStr(a.getNumType()), " pushed tp _evalStack");
	}
      }
      break;
    case CstBinaryOp.SUB:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] - _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	Term a = Term('-');
	a.setNumType(determineType(_evalStack[$-1].getNumType(), _evalStack[$-2].getNumType()));
	_evalStack ~= a;
	debug (MONOSOLVER){
	  import std.stdio;
	  writeln("Term '-' of type ", numTypeToStr(a.getNumType()), " pushed tp _evalStack");
	}
      }
      break;
    case CstBinaryOp.MUL:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] * _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.DIV:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] / _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.REM:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] % _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.LSH:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] << _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.RSH:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] >> _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    case CstBinaryOp.LRSH:
      if (_evalStack[$-1].isNum() && _evalStack[$-2].isNum()){
	Term e = _evalStack[$-2] >>> _evalStack[$-1];
	_evalStack.length -=2;
	_evalStack ~= e;
      }
      else {
	_endFlag = 3;
      }
      break;
    }
    debug (MONOSOLVER){
      if(_endFlag == 3){
	writeln("cannot process binary operator");
	writeln("THE PREDICATE IS NOT SOLVEABLE BY MONOSOLVER");
      }
    }
  }

  override void processEvalStack(CstCompareOp op) {
    if(checkError()){
      return;
    }
    S[2] range1;
    debug (MONOSOLVER){
      import std.stdio;
      final switch (op){
      case CstCompareOp.EQU:
	writeln("EQU comparison operator used");
	break;
      case CstCompareOp.NEQ:
	writeln("NEQ comparison operator used");
	break;
      case CstCompareOp.LTH:
	writeln("LTH comparison operator used");
	break;
      case CstCompareOp.GTH:
	writeln("GTH comparison operator used");
	break;
      case CstCompareOp.LTE:
	writeln("LTE comparison operator used");
	break;
      case CstCompareOp.GTE:
	writeln("GTE comparison operator used");
	break;
      }
    }
    if(!_hasRand){
      assert(_evalStack.length == 2);
      bool s = doesSatisfy(_evalStack[0], op, _evalStack[1]);
      if(s){
	S[2] temp = [S.min,S.max];
	_rangeStack ~= Range!S(temp);
      }
      else{
	_rangeStack ~= Range!S(false);
      }
      _evalStack.length = 0;
      return;
    }
    if (_evalStack[$-1].isNum()){
      NumType firstRangeType = determineType(_evalStack[$-1].getNumType(), _evalStack[$-2].getNumType());
      final switch (firstRangeType){
      case NumType.ULONG:
	ulong temp =  getTemp!ulong(_evalStack[$-1]);
	_evalStack.length -= 1;
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      case NumType.LONG:
	long temp =   getTemp!long(_evalStack[$-1]);
	_evalStack.length -= 1;
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      case NumType.UINT:
	uint temp =   getTemp!uint(_evalStack[$-1]);
	_evalStack.length -= 1;
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      case NumType.INT:
	int temp =   getTemp!int(_evalStack[$-1]);
	_evalStack.length -= 1;
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      }
    }
    else if (_evalStack[0].isNum()){
      NumType firstRangeType = determineType(_evalStack[$-1].getNumType(), _evalStack[0].getNumType());
      final switch (_evalStack[0].getNumType()){
      case NumType.ULONG:
	ulong temp =  getTemp!ulong(_evalStack[0]);
	_evalStack = _evalStack[1 .. $];
	reverseCompOp(op);
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      case NumType.LONG:
	long temp =  getTemp!long(_evalStack[0]);
	_evalStack = _evalStack[1 .. $];
	reverseCompOp(op);
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      case NumType.UINT:
	uint temp =  getTemp!uint(_evalStack[0]);
	_evalStack = _evalStack[1 .. $];
	reverseCompOp(op);
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      case NumType.INT:
	int temp =  getTemp!int(_evalStack[0]);
	_evalStack = _evalStack[1 .. $];
	reverseCompOp(op);
	range1 = reduce(makeRange(op, temp), _evalStack);
	break;
      }
    }
    debug (MONOSOLVER){
      import std.stdio;
      writeln();
      writeln("range obtained by this predicate:");
      writeln();
      display(range1);
      writeln();
    }
    _evalStack.length = 0;
    _hasRand = false;
    if(_endFlag == 1){
      _rangeStack ~= Range!S(false);
      _endFlag = 0;
    }
    else{
      _rangeStack ~= Range!S(range1);
    }
  }

  T getTemp (T) (Term t){
    final switch (t.getNumType()){
    case NumType.INT:
      return cast(T)(cast(int)((t.getInt())));
    case NumType.UINT:
      return cast(T)((t.getInt()));
    case NumType.LONG:
      return cast(T)(cast(long)((t.getLong())));
    case NumType.ULONG:
      return cast(T)((t.getLong()));
    }
  }
  override void processEvalStack(CstLogicOp op) {
    if(checkError()){
      return;
    }
    debug (MONOSOLVER){
      import std.stdio;
      final switch (op){
      case CstLogicOp.LOGICOR:
	writeln("logical operator OR");
	break;
      case CstLogicOp.LOGICAND:
	writeln("logical operator AND");
	break;
      case CstLogicOp.LOGICNOT:
	writeln("logical operator NOT");
	break;
      case CstLogicOp.LOGICIMP:
	writeln("logical operator IMP");
	break;
      }
      
      writeln("previous _rangeStack :");
      display(_rangeStack);
    }
    final switch (op){
    case CstLogicOp.LOGICOR:
      final switch(_rangeStack[$-1].getType()){
      case RangeType.DYN:
	final switch(_rangeStack[$-2].getType()){
	case RangeType.DYN:
	  ORRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.STA:
	  ORRANGE(_rangeStack[$-1].getD(), _rangeStack[$-2].getS());
	  _rangeStack[$-2] = Range!S(_rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.NUL:
	  _rangeStack[$-2] = Range!S(_rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	}
	break;
      case RangeType.STA:
	final switch(_rangeStack[$-2].getType()){
	case RangeType.DYN:
	  ORRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getS());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.STA:
	  S[] temp = [];
	  S[2] a = _rangeStack[$-2].getS;
	  if(a[1] < a[0]){
	    temp ~= S.min;
	    temp ~= a[1];
	    temp ~= a[0];
	    temp ~= S.max;
	  }
	  else{
	    temp ~= a[0];
	    temp ~= a[1];
	  }
	  _rangeStack[$-2] = Range!S(temp);
	  ORRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getS());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.NUL:
	  _rangeStack[$-2] = Range!S(_rangeStack[$-1].getS());
	  _rangeStack.length -= 1;
	  break;
	}
	break;
      case RangeType.NUL:
	_rangeStack.length -= 1;
	break;
      }
      break;
    case CstLogicOp.LOGICAND:
      final switch(_rangeStack[$-1].getType()){
      case RangeType.DYN:
	final switch(_rangeStack[$-2].getType()){
	case RangeType.DYN:
	  ANDRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.STA:
	  ANDRANGE(_rangeStack[$-1].getD(), _rangeStack[$-2].getS());
	  _rangeStack[$-2] = Range!S(_rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.NUL:
	  _rangeStack.length -= 1;
	  break;
	}
	break;
      case RangeType.STA:
	final switch(_rangeStack[$-2].getType()){
	case RangeType.DYN:
	  ANDRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getS());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.STA:
	  S[2] a = _rangeStack[$-2].getS();
	  if(a[1] < a[0]){
	    S[] temp = [];
	    temp ~= S.min;
	    temp ~= a[1];
	    temp ~= a[0];
	    temp ~= S.max;
	    _rangeStack[$-2] = Range!S(temp);
	    ANDRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getS());
	    _rangeStack.length -= 1;
	  }
	  else{
	    S[2] b = _rangeStack[$-1].getS();
	    if(b[1] < b[0]){
	      S[] temp = [];
	      temp ~= S.min;
	      temp ~= b[1];
	      temp ~= b[0];
	      temp ~= S.max;
	      _rangeStack[$-1] = Range!S(temp);
	      ANDRANGE(_rangeStack[$-1].getD(), _rangeStack[$-2].getS());
	      _rangeStack[$-2] = Range!S(_rangeStack[$-1].getD());
	      _rangeStack.length -= 1;
	    }
	    else{
	      if(!ANDRANGE(a,b)){
		_rangeStack.length -= 2;
		_rangeStack ~= Range!S(false);
	      }
	      else{
		_rangeStack[$-2] = Range!S(a);
		_rangeStack.length -=1;
	      }
	    }
	  }
	  break;
	case RangeType.NUL:
	  _rangeStack.length -= 1;
	  break;
	}
	break;
      case RangeType.NUL:
	_rangeStack.length -= 2;
	_rangeStack ~= Range!S(false);
	break;
      }
      if(_rangeStack[$-1].getType() == RangeType.DYN && _rangeStack[$-1].getD().length == 0){
	_rangeStack[$-1] = Range!S(false);
      }
      break;
    case CstLogicOp.LOGICNOT:
      reverseRange(_rangeStack[$-1]);
      break;
    case CstLogicOp.LOGICIMP:
      reverseRange(_rangeStack[$-2]);
      final switch(_rangeStack[$-1].getType()){
      case RangeType.DYN:
	final switch(_rangeStack[$-2].getType()){
	case RangeType.DYN:
	  ORRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.STA:
	  ORRANGE(_rangeStack[$-1].getD(), _rangeStack[$-2].getS());
	  _rangeStack[$-2] = Range!S(_rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.NUL:
	  _rangeStack[$-2] = Range!S(_rangeStack[$-1].getD());
	  _rangeStack.length -= 1;
	  break;
	}
	break;
      case RangeType.STA:
	final switch(_rangeStack[$-2].getType()){
	case RangeType.DYN:
	  ORRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getS());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.STA:
	  S[] temp = [];
	  S[2] a = _rangeStack[$-2].getS;
	  if(a[1] < a[0]){
	    temp ~= S.min;
	    temp ~= a[1];
	    temp ~= a[0];
	    temp ~= S.max;
	  }
	  else{
	    temp ~= a[0];
	    temp ~= a[1];
	  }
	  _rangeStack[$-2] = Range!S(temp);
	  ORRANGE(_rangeStack[$-2].getD(), _rangeStack[$-1].getS());
	  _rangeStack.length -= 1;
	  break;
	case RangeType.NUL:
	  _rangeStack[$-2] = Range!S(_rangeStack[$-1].getS());
	  _rangeStack.length -= 1;
	  break;
	}
	break;
      case RangeType.NUL:
	_rangeStack.length -= 1;
	break;
      }
      break;
    }
    debug (MONOSOLVER){
      import std.stdio;
      writeln("new _rangeStack :");
      display(_rangeStack);
    }
  }
  override void processEvalStack(CstInsideOp op) {
    if(checkError()){
      return;
    }
    final switch (op){
    case CstInsideOp.INSIDE:
      break;
    case CstInsideOp.EQUAL:
      if(_evalStack[$ - 1].getType() != Type.NUM && _evalStack[$ - 1].getType() != Type.RAND){
	_endFlag = 3;
	break;
      }
      _insideEqual ~= _evalStack[$ - 1];
      _evalStack.length -= 1;
      break;
    case CstInsideOp.RANGE:
      if(_evalStack[$ - 2].getType() != Type.NUM || _evalStack[$ - 1].getType() != Type.NUM){
	_endFlag = 3;
	break;
      }
      if(doesSatisfy(_evalStack[$ - 2], CstCompareOp.GTE, _evalStack[$ - 1])) {
	break;
      }
      _evalStack[$ - 1] = _evalStack[$ - 1] - Term(1);
      _insideRange ~= _evalStack[$ - 2];
      _insideRange ~= _evalStack[$ - 1];
      _evalStack.length -= 2;
      break;
    case CstInsideOp.RANGEINCL:
      if(_evalStack[$ - 2].getType() != Type.NUM || _evalStack[$ - 1].getType() != Type.NUM){
	_endFlag = 3;
	break;
      }
      if(doesSatisfy(_evalStack[$ - 2], CstCompareOp.GTH, _evalStack[$ - 1])){
	break;
      }
      _insideRange ~= _evalStack[$ - 2];
      _insideRange ~= _evalStack[$ - 1];
      _evalStack.length -= 2;
      break;
    case CstInsideOp.DONE:
      generateInsideRange();
      break;
    }
  }
  override void processEvalStack(CstUniqueOp op) {
    if(checkError()){
      return;
    }
    final switch(op) {// insideEqual used to store numbers, insideRange used for domains/expressions
    case CstUniqueOp.INIT:
      break;
    case CstUniqueOp.UINT:
    case CstUniqueOp.LONG:
    case CstUniqueOp.ULONG:
    case CstUniqueOp.INT:
      if(_evalStack[$-1].getType() == Type.NUM){
	assert(_evalStack.length == 1);
	_insideEqual ~= _evalStack[0];
	_evalStack.length = 0;
      }
      else{
	if(_insideRange.length != 0){
	  _endFlag = 3;
	  break;
	}
	_insideRange ~= _evalStack[0..$];
	_evalStack.length = 0;
      }
      break;
    case CstUniqueOp.UNIQUE:
      solveUnique();
      break;
    }
  }

  override void processEvalStack(CstSliceOp op) {
    _endFlag = 3;
  }
  void generateInsideRange() {
    Term [] tempStack = [];
    tempStack ~= _evalStack;
    bool hasX = false;
    foreach(i,elem; tempStack){
      if(elem.getType() == Type.RAND){
	hasX = true;
	break;
      }
    }
    _evalStack.length = 0;
    foreach(i, elem; _insideEqual){
      _evalStack ~= tempStack;
      _evalStack ~= elem;
      if(hasX || elem.getType() == Type.RAND){
	_hasRand = true;
      }
      else{
	_hasRand = false;
      }
      processEvalStack(CstCompareOp.EQU);
    }
    for(size_t i = 0; i < _insideEqual.length; i++){
      processEvalStack(CstLogicOp.LOGICOR);
    }
    for(size_t i = 0; i < _insideRange.length; i+=2){
      _evalStack ~= tempStack;
      _evalStack ~= _insideRange[i];
      if(hasX || _insideRange[i].getType() == Type.RAND){
	_hasRand = true;
      }
      else{
	_hasRand = false;
      }
      processEvalStack(CstCompareOp.GTE);
      _evalStack ~= tempStack;
      _evalStack ~= _insideRange[i+1];
      if(hasX || _insideRange[i+1].getType() == Type.RAND){
	_hasRand = true;
      }
      else{
	_hasRand = false;
      }
      processEvalStack(CstCompareOp.LTE);
      processEvalStack(CstLogicOp.LOGICAND);
      processEvalStack(CstLogicOp.LOGICOR);
    }
    _hasRand = false;
    _insideEqual.length = 0;
    _insideRange.length = 0;
  }
  void solveUnique(){
    import std.algorithm.sorting: sort;
    sort!(compareTerms)(_insideEqual);
    for(size_t i = 0; i<_insideEqual.length-1; ++i){
      if(doesSatisfy(_insideEqual[i], CstCompareOp.EQU, _insideEqual[i+1])){
	pushToEvalStack(false);
	if(_rangeStack.length > 1){
	  processEvalStack(CstLogicOp.LOGICAND);
	}
	return;
      }
    }
    if(_insideRange.length == 0){
      pushToEvalStack(true);
      if(_rangeStack.length > 1){
	processEvalStack(CstLogicOp.LOGICAND);
      }
      return;
    }
    foreach(i, elem; _insideEqual){
      _evalStack ~= _insideRange;
      _evalStack ~= elem;
      _hasRand = true;
      processEvalStack(CstCompareOp.NEQ);
    }
    for(size_t i = 0; i<_insideEqual.length-1; ++i){
      processEvalStack(CstLogicOp.LOGICAND);
    }
    _insideEqual.length = 0;
    _insideRange.length = 0;
    if(_rangeStack.length > 1){
      processEvalStack(CstLogicOp.LOGICAND);
    }
  }
  static bool compareTerms(Term a, Term b){
    return doesSatisfy(a, CstCompareOp.GTH, b);
  }
  void modifyRange1(T)(T n1, Term binOp, ref T[2] range){
    import std.string: format;
    switch (binOp.getType()){
    case Type.ADD:
      SubInRange(range, n1);
      break;
    case Type.SUB:
      AddInRange(range, n1);
      break;
    default:
      assert (false,
	      format("Can not handle binOp: %s", binOp.getType()));
    }
  }


  void modifyRange2(T)(T n1, Term binOp, ref T[2] range){
    switch (binOp.getType()){
    case Type.ADD:
      SubInRange(range, n1);
      break;
    case Type.SUB:
      SubRevRange(range, n1);
      break;
    default:
      assert (false);
    }
  }

  static bool doesSatisfy(Term a, CstCompareOp op, Term b){
    assert(a.getType() == Type.NUM && b.getType == Type.NUM);
    final switch (a.getNumType()){
    case NumType.INT:
      auto A = cast(int)a.getInt();
      final switch (b.getNumType()){
      case NumType.INT:
	auto B = cast(int)b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.UINT:
	auto B = b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.LONG:
	auto B = cast(long)b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.ULONG:
	auto B = b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      }
    case NumType.UINT:
      auto A = a.getInt();
      final switch (b.getNumType()){
      case NumType.INT:
	auto B = cast(int)b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.UINT:
	auto B = b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.LONG:
	auto B = cast(long)b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.ULONG:
	auto B = b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      }
    case NumType.LONG:
      auto A = cast(long)a.getLong();
      final switch (b.getNumType()){
      case NumType.INT:
	auto B = cast(int)b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.UINT:
	auto B = b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.LONG:
	auto B = cast(long)b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.ULONG:
	auto B = b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      }
    case NumType.ULONG:
      auto A = a.getLong();
      final switch (b.getNumType()){
      case NumType.INT:
	auto B = cast(int)b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.UINT:
	auto B = b.getInt();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.LONG:
	auto B = cast(long)b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      case NumType.ULONG:
	auto B = b.getLong();
	final switch (op){
	case CstCompareOp.EQU:
	  return A == B;
	case CstCompareOp.NEQ:
	  return A != B;
	case CstCompareOp.LTH:
	  return A < B;
	case CstCompareOp.GTH:
	  return A > B;
	case CstCompareOp.LTE:
	  return A <= B;
	case CstCompareOp.GTE:
	  return A >= B;
	}
      }
    }
  }
  
  void reverseCompOp(ref CstCompareOp c){
    final switch (c){
    case CstCompareOp.EQU:
      break;
    case CstCompareOp.NEQ:
      break;
    case CstCompareOp.LTH:
      c = CstCompareOp.GTH;
      break;
    case CstCompareOp.GTH:
      c = CstCompareOp.LTH;
      break;
    case CstCompareOp.LTE:
      c = CstCompareOp.GTE;
      break;
    case CstCompareOp.GTE:
      c = CstCompareOp.LTE;
      break;
    }
  }
  R [2]  castRange(R, T)(ref T[2] range){
    static if (is (R == int)){
      static if (is (T == int)){
	return range;
      }
      else static if (is (T == uint)){
	return cast(int[2]) (range);
      }
      else static if (is (T == long)){
	int [2] tempRange = [0, 0];
	if (range[0] > int.max){
	  if (range[1] < range [0] && range[1] > int.min){
	    tempRange[0] = int.min;
	  }
	  else {
	    _endFlag = 1;
	    return tempRange;
	  }
	}
	else if (range[0] < int.min){
	  if (range[1] < int.min){
	    if (range[1] >= range[0]){
	      _endFlag = 1;
	      return tempRange;
	    }
	    else {
	      tempRange[0] = int.min;
	      tempRange[1] = int.max;
	      return tempRange;
	    }
	  }
	  else {
	    tempRange[0] = int.min;
	  }
	}
	else {
	  tempRange[0] = cast(int) range[0];
	}
	if (range[1] > int.max){
	  tempRange[1] = int.max;
	}
	else if (range[1] <= int.min){
	  tempRange[1] = int.max;
	}
	else {
	  tempRange[1] = cast(int) range[1];
	}
	return tempRange;
      }
      else static if (is (T == ulong)){
	int [2] tempRange  = [0, 0];
	if (range[0] > int.max){
	  if (range[1] < range [0]){
	    tempRange[0] = ulong.min;
	  }
	  else {
	    _endFlag = 1;
	    return tempRange;
	  }
	}
	else {
	  tempRange[0] = cast(int) range[0];
	}
	if (range[1] > int.max){
	  tempRange[1] = int.max;
	}
	else {
	  tempRange[1] = cast(int) range[1];
	}
	return tempRange;
      }
    }
    else static if (is (R == uint)){
      static if (is (T == uint)){
	return range;
      }
      else static if (is (T == long)){
	uint [2] tempRange = [0, 0];
	if (range[0] > uint.max){
	  if (range[1] < range [0] && range[1] > uint.min){
	    tempRange[0] = uint.min;
	  }
	  else {
	    _endFlag = 1;
	    return tempRange;
	  }
	}
	else if (range[0] < uint.min){
	  if (range[1] < uint.min){
	    if (range[1] >= range[0]){
	      _endFlag = 1;
	      return tempRange;
	    }
	    else {
	      tempRange[0] = uint.min;
	      tempRange[1] = uint.max;
	      return tempRange;
	    }
	  }
	  else {
	    tempRange[0] = uint.min;
	  }
	}
	else {
	  tempRange[0] = cast(uint) range[0];
	}
	if (range[1] > uint.max){
	  tempRange[1] = uint.max;
	}
	else if (range[1] <= uint.min){
	  tempRange[1] = uint.max;
	}
	else {
	  tempRange[1] = cast(uint) range[1];
	}
	return tempRange;
      }
      else static if (is (T == ulong)){
	uint [2] tempRange = [0, 0];
	if (range[0] > uint.max){
	  if (range[1] < range [0]){
	    tempRange[0] = uint.min;
	  }
	  else {
	    _endFlag = 1;
	    return tempRange;
	  }
	}
	else {
	  tempRange[0] = cast(uint) range[0];
	}
	if (range[1] > uint.max){
	  tempRange[1] = uint.max;
	}
	else {
	  tempRange[1] = cast(uint) range[1];
	}
	return tempRange;
      }
    }
    else static if (is (R == long)){
      static if (is (T == long)){
	return range;
      }
      else static if (is (T == ulong)){
	return cast(long[2]) (range);
      }
    }
    else static if (is (R == ulong)){
      static if (is (T == ulong)){
	return range;
      }
    }
    assert(false);
  }
  S[2] reduce(T)(T[2] range, ref Term [] Stack){
    debug (MONOSOLVER){
      import std.stdio;
      writeln("Stack :");
      display(Stack);
      writeln();
      writeln("current range :");
      display(range);
    }
    if (Stack.length == 1){
      return castRange!S(range);
    }
    if (Stack[$-2].isNum()){
      final switch (Stack[$-1].getNumType()){
      case NumType.INT:
	static if (is (T == int)){
	  int [2] range1 = range;
	}
	else {
	  int [2] range1 = castRange!int(range);
	}
	int num = cast(int)Stack[$-2].getInt();
	assert (Stack[$-2].getNumType() == NumType.INT);
	modifyRange1(num, Stack[$-1], range1);
	Stack.length -= 2;
	return reduce(range1, Stack);
      case NumType.UINT:
	static if (is (T == uint)){
	  uint [2] range1 = range;
	}
	else {
	  uint [2] range1 = castRange!uint(range);
	}
	uint num = Stack[$-2].getInt();
	modifyRange1(num, Stack[$-1], range1);
	Stack.length -= 2;
	return reduce(range1, Stack);
      case NumType.LONG:
	static if (is (T == long)){
	  long [2] range1 = range;
	}
	else {
	  long [2] range1 = castRange!long(range);
	}
	long num;
	final switch (Stack[$-2].getNumType()){
	case NumType.INT:
	  num = cast(long)(cast(int)(Stack[$-2].getInt()));
	  break;
	case NumType.UINT:
	  num = cast(long)(Stack[$-2].getInt());
	  break;
	case NumType.LONG:
	  num = cast(long)(Stack[$-2].getLong());
	  break;
	case NumType.ULONG:
	  assert(false);
	}
	modifyRange1(num, Stack[$-1], range1);
	Stack.length -= 2;
	return reduce(range1, Stack);
      case NumType.ULONG:
	static if (is (T == ulong)){
	  ulong [2] range1 = range;
	}
	else {
	  ulong [2] range1 = castRange!ulong(range);
	}
	ulong num;
	final switch (Stack[$-2].getNumType()){
	case NumType.INT:
	  num = cast(ulong)(cast(int)(Stack[$-2].getInt()));
	  break;
	case NumType.UINT:
	  num = cast(ulong)(Stack[$-2].getInt());
	  break;
	case NumType.LONG:
	  num = cast(ulong)cast(long)(Stack[$-2].getLong());
	  break;
	case NumType.ULONG:
	  num = (Stack[$-2].getLong());
	  break;
	}
	modifyRange1(num, Stack[$-1], range1);
	Stack.length -= 2;
	return reduce(range1, Stack);
      }
    }
    else {
      final switch (Stack[$-1].getNumType()){
      case NumType.INT:
	static if (is (T == int)){
	  int [2] range1 = range;
	}
	else {
	  int [2] range1 = castRange!int(range);
	}
	int num = cast(int)Stack[0].getInt();
	assert (Stack[$-2].getNumType() == NumType.INT);
	modifyRange2(num, Stack[$-1], range1);
	Stack = Stack[1 .. $-1];
	return reduce(range1, Stack);
      case NumType.UINT:
	static if (is (T == uint)){
	  uint [2] range1 = range;
	}
	else {
	  uint [2] range1 = castRange!uint(range);
	}
	uint num = Stack[0].getInt();
	modifyRange2(num, Stack[$-1], range1);
	Stack = Stack[1 .. $-1];
	return reduce(range1, Stack);
      case NumType.LONG:
	static if (is (T == long)){
	  long [2] range1 = range;
	}
	else {
	  long [2] range1 = castRange!long(range);
	}
	long num;
	final switch (Stack[0].getNumType()){
	case NumType.INT:
	  num = cast(long)(cast(int)(Stack[0].getInt()));
	  break;
	case NumType.UINT:
	  num = cast(long)(Stack[0].getInt());
	  break;
	case NumType.LONG:
	  num = cast(long)(Stack[0].getLong());
	  break;
	case NumType.ULONG:
	  assert(false);
	}
	modifyRange2(num, Stack[$-1], range1);
	Stack = Stack[1 .. $-1];
	return reduce(range1, Stack);
      case NumType.ULONG:
	static if (is (T == ulong)){
	  ulong [2] range1 = range;
	}
	else {
	  ulong [2] range1 = castRange!ulong(range);
	}
	ulong num;
	final switch (Stack[0].getNumType()){
	case NumType.INT:
	  num = cast(ulong)(cast(int)(Stack[0].getInt()));
	  break;
	case NumType.UINT:
	  num = cast(ulong)(Stack[0].getInt());
	  break;
	case NumType.LONG:
	  num = cast(ulong)cast(long)(Stack[0].getLong());
	  break;
	case NumType.ULONG:
	  num = (Stack[0].getLong());
	  break;
	}
	modifyRange2(num, Stack[$-1], range1);
	Stack = Stack[1 .. $-1];
	return reduce(range1, Stack);
      }
    }
  }
  ulong counter(){
    ulong num = 0;
    for(size_t i = 0; i < _finalRange.length - 1; i += 2){
      num += _finalRange[i+1] - _finalRange[i] + 1;
    }
    return num;
  }
  ulong choose(ulong rand) {
    size_t i;
    ulong step;
    debug (MONOSOLVER) {
      import std.stdio;
      writeln(rand);
    }
    for(i = 0; i < _finalRange.length - 1; i += 2) {
      step = _finalRange[i+1] - _finalRange[i] + 1;
      if (rand < step) break;
      else rand -= step;
    }
    debug (MONOSOLVER){
      import std.stdio;
      writeln(i);
      writeln(_finalRange.length);
      writeln(rand);
    }
    return (cast(ulong)(_finalRange[i] + rand));
  }
  void ANDRANGE(ref S[] a, ref S[] b){
    int a1 = 0;
    int b1 = 0;
    size_t len = a.length;
    while (a1 != len && b1 != b.length){
      if (a[a1] < b[b1]){
	if (fallsIn(a[a1], b, b1)){
	  a ~= a[a1];
	}
	a1++;
      }
      else if (a[a1] > b[b1]){
	if (fallsIn(b[b1], a, a1)){
	  a ~= b[b1];
	}
	b1++;
      }
      else {
	if ((a1+b1)%2==0){
	  a ~= a[a1];
	  a1++;
	  b1++;
	}
	else {
	  a ~= a[a1];
	  a ~= a[a1];
	  a1++;
	  b1++;
	}
      }
    }
    if (len == a.length){
      a.length = 0;
    }
    else {
      a = a[len .. $];
    }
  }
  bool ANDRANGE(ref S[2] a, S[2] b){
    if(a[1] < b[0] || b[1] < a[0]){
      return false;
    }
    S[2] temp = [S.min, S.max];
    if(a[0] > b[0]){
      temp[0] = a[0];
    }
    else{
      temp[0] = b[0];
    }
    if(a[1] < b[1]){
      temp[1] = a[1];
    }
    else{
      temp[1] = b[1];
    }
    a = temp;
    return true;
  }
  void ORRANGE(ref S[] a, ref S[] b){
    int a1 = 0;
    int b1 = 0;
    size_t len = a.length;
    while (a1 < len || b1 < b.length){
      if (a1 >= len){
	size_t temp = a.length - len;
	if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == b[b1]-1)||(a[$-1] == b[b1]))){
	  a.length --;
	  b1 ++;
	}
	while (b1 < b.length){
	  a ~= b[b1];
	  b1++;
	}
	continue;
      }
      else if (b1 >= b.length){
	size_t temp = a.length - len;
	if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == a[a1]-1)||(a[$-1] == a[a1]))){
	  a.length --;
	  a1 ++;
	}
	while (a1 < len){
	  a ~= a[a1];
	  a1++;
	}
	continue;
      }
      if (a[a1] < b[b1]){
	if (!fallsIn(a[a1], b, b1)){
	  size_t temp = a.length - len;
	  if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == a[a1]-1)||(a[$-1] == a[a1]-1))){
	    a.length --;
	  }
	  else {
	    a ~= a[a1];
	  }
	}
	a1++;
      }
      else if (a[a1] > b[b1]){
	if (!fallsIn(b[b1], a, a1)){
	  size_t temp = a.length - len;
	  if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == b[b1] -1)||(a[$-1] == b[b1]))){
	    a.length --;
	  }
	  else {
	    a ~= b[b1];
	  }
	}
	b1++;
      }
      else {
	if ((a1+b1)%2==0){
	  a ~= a[a1];
	  a1++;
	  b1++;
	}
	else {
	  a1++;
	  b1++;
	}
      }
    }
    if (len == a.length){
      a.length = 0;
    }
    else {
      a = a[len .. $];
    }
  }
  void ANDRANGE(T)(ref T[] a, T[2] b){
    if (b[0] > b[1]){
      T[4] B = [T.min, b[1], b[0], T.max];
      int a1 = 0;
      int b1 = 0;
      size_t len = a.length;
      while (a1 != len && b1 != B.length){
	if (a[a1] < B[b1]){
	  if (fallsIn(a[a1], B)){
	    a ~= a[a1];
	  }
	  a1++;
	}
	else if (a[a1] > B[b1]){
	  if (fallsIn(B[b1], a, a1)){
	    a ~= B[b1];
	  }
	  b1++;
	}
	else {
	  if ((a1+b1)%2==0){
	    a ~= a[a1];
	    a1++;
	    b1++;
	  }
	  else {
	    a ~= a[a1];
	    a ~= a[a1];
	    a1++;
	    b1++;
	  }
	}
      }
      if (len == a.length){
	a.length = 0;
      }
      else {
	a = a[len .. $];
      }
    }
    else {
      int a1 = 0;
      int b1 = 0;
      size_t len = a.length;
      while (a1 != len && b1 != b.length){
	if (a[a1] < b[b1]){
	  if (fallsIn(a[a1], b)){
	    a ~= a[a1];
	  }
	  a1++;
	}
	else if (a[a1] > b[b1]){
	  if (fallsIn(b[b1], a, a1)){
	    a ~= b[b1];
	  }
	  b1++;
	}
	else {
	  if ((a1+b1)%2==0){
	    a ~= a[a1];
	    a1++;
	    b1++;
	  }
	  else {
	    a ~= a[a1];
	    a ~= a[a1];
	    a1++;
	    b1++;
	  }
	}
      }
      if (len == a.length){
	a.length = 0;
      }
      else {
	a = a[len .. $];
      }
    }
  }
  void ORRANGE(ref S[] a, S[2] b){
    if (b[0] > b[1]){
      S[4] B = [S.min, b[1], b[0], S.max];
      int a1 = 0;
      int b1 = 0;
      size_t len = a.length;
      while (a1 < len || b1 < B.length){
	if (a1 >= len){
	  ptrdiff_t temp = a.length - len;
	  if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == B[b1]-1)||(a[$-1] == B[b1]))){
	    a.length --;
	    b1 ++;
	  }
	  while (b1 < B.length){
	    a ~= B[b1];
	    b1++;
	  }
	  continue;
	}
	else if (b1 >= B.length){
	  ptrdiff_t temp = a.length - len;
	  if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == a[a1]-1)||(a[$-1] == a[a1]))){
	    a.length --;
	    a1 ++;
	  }
	  while (a1 < len){
	    a ~= a[a1];
	    a1++;
	  }
	  continue;
	}
	if (a[a1] < B[b1]){
	  if (!fallsIn(a[a1], B)){
	    ptrdiff_t temp = a.length - len;
	    if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == a[a1]-1)||(a[$-1] == a[a1]))){
	      a.length --;
	    }
	    else {
	      a ~= a[a1];
	    }
	  }
	  a1++;
	}
	else if (a[a1] > B[b1]){
	  if (!fallsIn(B[b1], a, a1)){
	    ptrdiff_t temp = a.length - len;
	    if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == B[b1] -1)||(a[$-1] == B[b1]))){
	      a.length --;
	    }
	    else {
	      a ~= B[b1];
	    }
	  }
	  b1++;
	}
	else {
	  if ((a1+b1)%2==0){
	    a ~= a[a1];
	    a1++;
	    b1++;
	  }
	  else {
	    a1++;
	    b1++;
	  }
	}
      }
      if (len == a.length){
	a.length = 0;
      }
      else {
	a = a[len .. $];
      }
    }
    else {
      int a1 = 0;
      int b1 = 0;
      size_t len = a.length;
      while (a1 < len || b1 < b.length){
	if (a1 >= len){
	  ptrdiff_t temp = a.length - len;
	  if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == b[b1]-1)||(a[$-1] == b[b1]))){
	    a.length --;
	    b1 ++;
	  }
	  while (b1 < b.length){
	    a ~= b[b1];
	    b1++;
	  }
	  continue;
	}
	else if (b1 >= b.length){
	  ptrdiff_t temp = a.length - len;
	  if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == a[a1]-1)||(a[$-1] == a[a1]))){
	    a.length --;
	    a1 ++;
	  }
	  while (a1 < len){
	    a ~= a[a1];
	    a1++;
	  }
	  continue;
	}
	if (a[a1] < b[b1]){
	  if (!fallsIn(a[a1], b)){
	    ptrdiff_t temp = a.length - len;
	    if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == a[a1]-1)||(a[$-1] == a[a1]))){
	      a.length --;
	    }
	    else {
	      a ~= a[a1];
	    }
	  }
	  a1++;
	}
	else if (a[a1] > b[b1]){
	  if (!fallsIn(b[b1], a, a1)){
	    ptrdiff_t temp = a.length - len;
	    if ((temp != 0) && (temp % 2 == 0) && ((a[$-1] == b[b1] -1)||(a[$-1] == b[b1]))){
	      a.length --;
	    }
	    else {
	      a ~= b[b1];
	    }
	  }
	  b1++;
	}
	else {
	  if ((a1+b1)%2==0){
	    a ~= a[a1];
	    a1++;
	    b1++;
	  }
	  else {
	    a1++;
	    b1++;
	  }
	}
      }
      if (len == a.length){
	a.length = 0;
      }
      else {
	a = a[len .. $];
      }
    }
  }
  bool isInRange(T)(T x, ref T [] a){
    foreach (i, elem; a){
      if (i % 2 == 0){
	if (x < elem){
	  return false;
	}
      }
      else {
	if (x <= elem){
	  return true;
	}
      }
    }
    return false;
  }
  bool isInRange(T)(T x, ref T [2] a){
    foreach (i, elem; a){
      if (i % 2 == 0){
	if (x < elem){
	  return false;
	}
      }
      else {
	if (x <= elem){
	  return true;
	}
      }
    }
    return false;
  }
  bool isInRange(T)(T x, ref T [4] a){
    foreach (i, elem; a){
      if (i % 2 == 0){
	if (x < elem){
	  return false;
	}
      }
      else {
	if (x <= elem){
	  return true;
	}
      }
    }
    return false;
  }
  bool fallsIn(T)(T x, ref T [] a){
    foreach (i, elem; a){
      if (x < elem){
	if (i % 2==0){
	  return false;
	}
	return true;
      }
    }
    return false;
  }
  bool fallsIn(T)(T x, T [2] a){
    foreach (i, elem; a){
      if (x < elem){
	if (i % 2==0){
	  return false;
	}
	return true;
      }
    }
    return false;
  }
  bool fallsIn(T)(T x, T [4] a){
    foreach (i, elem; a){
      if (x < elem){
	if (i % 2==0){
	  return false;
	}
	return true;
      }
    }
    return false;
  }
  bool fallsIn(T)(T x, ref T [] a, int pos){
    for (int i = pos; i < a.length; i++){
      T elem = a[i];
      if (x < elem){
	if (i % 2==0){
	  return false;
	}
	return true;
      }
    }
    return false;
  }
  void AddInRange(T)(ref T[2] range, T num){
    foreach (ref e; range){
      e = e + num;
    }
  }
  
  void SubInRange(T)(ref T[2] range, T num){
    foreach (ref e; range){
      e = e - num;
    }
  }
  void SubRevRange(T)(ref T[2] range, T num){
    foreach (ref e; range){
      e = num - e;
    }
    T temp = range[0];
    range[0] = range[1];
    range[1] = temp;
  }
  void reverseRange(ref Range!S range){
    final switch (range.getType()){
    case RangeType.STA:
      S[2] temp = range.getS();
      if(temp == [S.min, S.max]){
	range.setType(RangeType.NUL);
	break;
      }
      S a = temp[0];
      temp[0] = temp[1] + 1;
      temp[1] = a - 1;
      break;
    case RangeType.NUL:
      S[2] temp = [S.min, S.max];
      range = Range!S(temp);
      break;
    case RangeType.DYN:
      S[] temp = range.getD();
      if (temp[0] == S.min){
	temp = temp[1 .. $];
      }
      else{
	temp ~= temp[$-1];
	for(size_t i = temp.length - 2; i > 0; --i){
	  temp[i] = temp[i-1];
	}
	temp[0] = S.min;
      }
      if (temp[$-1] == S.max){
	temp.length -= 1;
      }
      else{
	temp ~= [S.max];
      }
      if(temp.length == 0){
	range.setType(RangeType.NUL);
      }
    }
  }
  void display(Term[] Stack){
    import std.stdio;
    writeln();
    foreach (term; Stack){
      display1(term);
      write(" ");
    }
    writeln();
    foreach (term; Stack){
      display2(term);
    }
  }
  void display(T)(T [] r){
    import std.stdio;
    write("[");     
    foreach (elem; r){
      write(elem, ", ");
    }
    write("]");
  }
  void display(T)(T [2] r){
    import std.stdio;
    write("[");     
    foreach (elem; r){
      write(elem, ", ");
    }
    write("]");
  }
  void displayRangeStack(T)(Range!T [] r){
    import std.stdio;
    writeln();
    write("[");     
    foreach (elem; r){
      display(elem);
      write(", ");
    }
    write("]");
    writeln();
  }
  void display(T)(Range!T r){
    import std.stdio;
    final switch(r.getType()){
    case RangeType.NUL:
      write("[]");
      break;
    case RangeType.DYN:
      display(r.getD());
      break;
    case RangeType.STA:
      display(r.getS());
      break;
    }
  }
  void display1(Term a){
    import std.stdio;
    final switch (a.getType()){
    case Type.NUM:
      final switch (a.getNumType()){
      case NumType.INT:
	write(cast(int)(a.getInt()));
	break;
      case NumType.UINT:
	write((a.getInt()));
	break;
      case NumType.LONG:
	write(cast(long)(a.getLong()));
	break;
      case NumType.ULONG:
	write((a.getLong()));
	break;
      }
      break;
    case Type.RAND:
      write("X");
      break;
    case Type.SUB:
      write("-");
      break;
    case Type.ADD:
      write("+");
      break;
    }
  }
  void display2(Term a){
    import std.stdio;
    final switch (a.getType()){
    case Type.NUM:
      final switch (a.getNumType()){
      case NumType.INT:
	write(cast(int)(a.getInt()), " (int) |");
	break;
      case NumType.UINT:
	write((a.getInt())," (uint) |");
	break;
      case NumType.LONG:
	write(cast(long)(a.getLong())," (long) |");
	break;
      case NumType.ULONG:
	write((a.getLong())," (ulong) |");
	break;
      }
      break;
    case Type.RAND:
      write("X");
      final switch (a.getNumType()){
      case NumType.INT:
	write( " (int) |");
	break;
      case NumType.UINT:
	write(" (uint) |");
	break;
      case NumType.LONG:
	write(" (long) |");
	break;
      case NumType.ULONG:
	write(" (ulong) |");
	break;
      }
      break;
    case Type.SUB:
      write("-");
      final switch (a.getNumType()){
      case NumType.INT:
	write( " (int) |");
	break;
      case NumType.UINT:
	write(" (uint) |");
	break;
      case NumType.LONG:
	write(" (long) |");
	break;
      case NumType.ULONG:
	write(" (ulong) |");
	break;
      }
      break;
    case Type.ADD:
      write("+");
      final switch (a.getNumType()){
      case NumType.INT:
	write( " (int) |");
	break;
      case NumType.UINT:
	write(" (uint) |");
	break;
      case NumType.LONG:
	write(" (long) |");
	break;
      case NumType.ULONG:
	write(" (ulong) |");
	break;
      }
      break;
    }
  }
  string numTypeToStr(NumType a){
    final switch(a){
    case NumType.INT:
      return ("int");
    case NumType.UINT:
      return ("uint");
    case NumType.LONG:
      return ("long");
    case NumType.ULONG:
      return ("ulong");
    }
  }
  T[2] makeRange(T)(CstCompareOp op, T num){
    final switch (op){
    case CstCompareOp.EQU:
      return [num, num];
    case CstCompareOp.NEQ:
      return [num + 1, num - 1];
    case CstCompareOp.LTH:
      if(num == T.min){
	_endFlag = 1;
      }
      return [T.min, num - 1];
    case CstCompareOp.GTH:
      if(num == T.max){
	_endFlag = 1;
      }
      return [num + 1, T.max];
    case CstCompareOp.LTE:
      return [T.min, num];
    case CstCompareOp.GTE:
      return [num, T.max];
    }
  }
  bool checkError(){
    if(_endFlag == 3){
      return true;
    }
    return false;
  }
}
unittest
{
  CstMonoSolver!int solver = new CstMonoSolver!int();
}
