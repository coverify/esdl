import std.stdio;
import esdl.rand;

class Foo {
  mixin Randomization;

  @rand uint data;
  @rand uint shl;
  @rand uint val;

  Constraint!q{
    // val == 2;
    // shl == 16;
    data == shl << 6;
  } testCst;
}

void main()
{
  Foo foo = new Foo();
  for (size_t i=0; i!=16; ++i)
    {
  foo.randomize();
  writeln(foo.data);
      
    }
}
