module esdl.data.charbuf;

import esdl.data.vector: Vector;


struct Charbuf(string NAME, uint MINCAP=1024, uint BUFSIZE=128)
{
  static assert (MINCAP > BUFSIZE * 2);

  Vector!(char, NAME, MINCAP) _vec;
  alias _vec this;

  private void growCap() {
    if (_vec.length < MINCAP - BUFSIZE)
      _vec.reserve(MINCAP);
    else _vec.reserve(_vec.length * 2);
  }

  char[] appendf(alias fmt, Args...)(Args args) {
    import std.format: sformat;
    if (_vec.capacity < _vec.length + BUFSIZE) growCap();
    auto size = sformat!(fmt)(_vec._reserved(), args).length;
    return _vec._acquire(size);
  }

  char[] appendf(Args...)(scope const(char)[] fmt, Args args) {
    import std.format: sformat;
    if (_vec.capacity < _vec.length + BUFSIZE) growCap();
    auto size = sformat(_vec._reserved(), fmt, args).length;
    return _vec._acquire(size);
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

struct ScratchPad(string NAME, uint BUFSIZE=1024)
{
  alias VEC = Vector!(char, NAME, BUFSIZE);

  VEC[] _pad;
  size_t _bufsize = BUFSIZE;
  size_t _size = BUFSIZE * 1024;

  alias getBuf this;

  void setPageSize(uint size) {
    assert (size > BUFSIZE);
    _size = size;
  }

  char[] getBuf(size_t len=BUFSIZE) {
    if (_pad.length == 0 ||
	_pad[$-1].capacity() - _pad[$-1].length() < len) {
      _pad.length += 1;
      _pad[$-1].reserve(_size);
    }
    _bufsize = len;
    return _pad[$-1]._getPayload()[_pad[$-1].length.._pad[$-1].length+len];
  }

  void register(char[] buf) {
    assert (buf.ptr == _pad[$-1][].ptr + _pad[$-1].length());
    assert (buf.length <= _bufsize);
    _pad[$-1]._acquire(buf.length);
  }

  char[] register(size_t len) {
    assert (len <= _bufsize);
    char[] buf =
      _pad[$-1]._getPayload()[_pad[$-1].length.._pad[$-1].length+len];
    _pad[$-1]._acquire(len);
    return buf;
  }


  string format(alias fmt, Args...)(Args args) {
    import std.format: sformat;
    auto str = sformat!(fmt)(getBuf(), args);
    _acquire(str.length);
    return cast(string) str;
  }

  char[] format(Args...)(scope const(char)[] fmt, Args args) {
    import std.format: sformat;
    auto str = sformat(getBuf(), fmt, args);
    _acquire(str.length);
    return cast(string) str;
  }


}
