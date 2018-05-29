import std.stdio;
import esdl.rand;

class Base {
  @rand uint a;
  @rand uint xx;
  mixin Randomization;
  Constraint! q{xx < 28;} cstx;
}

class Simple: Base {
  mixin Randomization;
  @rand uint b = 42;
  Constraint! q{
    a[0..4]  == 0;
    a < 128;
    solve a before b;
  } csta;
}

void main()
{
  Simple simple = new Simple();
  for (size_t i=0; i!=4; ++i)
    {
      // simple.randomize();
      simple.randomizeWith! q{b == @0;}(i);
      writeln(simple.a, " ", simple.b);
    }
}
