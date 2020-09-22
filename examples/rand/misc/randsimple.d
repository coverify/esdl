import std.stdio;
import esdl.rand;

enum e1 {
	 A = 0,
	 B = 1,
	 C = 2
}

enum e2 {
	 A = 0,
	 B = 1,
	 C = 2,
	 D = 3
}

int foo = 0x00;

class Base {
  @rand uint a;
  @rand e1 xx;
  @rand e2 yy;
  mixin Randomization;
  Constraint! q{xx < 28;} cst1;
  Constraint! q{yy < 28;} cst2;
}

class Simple: Base {
  mixin Randomization;
  @rand uint b = 42;
  Constraint! q{
    // a[0..4]  == foo;
    // a < 128;
    a >= 64;
    @soft!4 a[0..4]  == 0;
    @soft a > 24;
    a + b > 32;
  } csta;
}

void main()
{
  Simple simple = new Simple();
  for (size_t i=0; i!=1000; ++i) {
    // simple.randomize();
    simple.randomizeWith! q{a <= #0 + 128; b == #1;}(i*128, i+2);
    writeln(simple.a, " ", simple.b);
  }
}
