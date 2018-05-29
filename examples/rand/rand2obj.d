import std.stdio;
import esdl.rand;

class Foo {
  mixin Randomization;
  @rand ubyte foo;
  Constraint!q{
    foo >= 0;
  } cst;
}

class Bar {
  mixin Randomization;
  @rand byte bar;
  Constraint!q{
    bar >= 0;
  } cst;
}
  
void foo()
{
  for (size_t i=0; i!=2; ++i) {
      Foo foo = new Foo;
      foo.randomize;
      Bar bar = new Bar;
      bar.randomize;
      writeln(i);
    }
}

void bar()
{
  for (size_t i=0; i!=2; ++i) {
      Foo foo = new Foo;
      foo.randomize;
      Bar bar = new Bar;
      bar.randomize;
      writeln(i);
    }
}

void main()
{
  import core.memory: GC;
  GC.disable;
  foo();
  GC.collect;
  bar();
}
