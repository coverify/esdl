module esdl.data.charbuf;

import esdl.data.vector: Vector;


struct Charbuf(string NAME, uint MINCAP=1024, uint BUFSIZE=32)
{
  Vector!(char, NAME, MINCAP) _vec;
  alias _vec this;

  char[BUFSIZE] _buf;

  void appendf(alias fmt, Args...)(Args args) {
    import std.format: sformat;
    _vec ~= sformat!(fmt)(_buf, args);
  }

  void appendf(Args...)(scope const(char)[] fmt, Args args) {
    import std.format: sformat;
    _vec ~= sformat(_buf, fmt, args);
  }

  void opOpAssign(string op)(char c) if (op == "~") {
    _vec ~= c;
  }

  void opOpAssign(string op)(string str) if (op == "~") {
    _vec ~= cast(char[]) str;
  }

  void opOpAssign(string op)(char[] str) if (op == "~") {
    _vec ~= str;
  }

}
