import esdl.rand;

import randstructfoo;

struct Foo {
  private @rand int frop;
public:
  void display() {
    import std.stdio;
    writeln("frop is: ", frop);
  }
}

class Bar {
  mixin Randomization;
  @rand Foo* foo;
  void preRandomize() {
    frop++;
  }
  int frop = 64;

  Constraint! q{
    foo.frop < frop;
    foo.frop > frop - 4;
  } frop_cst;
public:
  this(Foo* foo) {
    this.foo = foo;
  }
  void setFoo(Foo* foo) {
    this.foo = foo;
  }
  void display() {
    foo.display();
  }
}

void main() {
  Foo* foo;
  Bar bar = new Bar(null);
  for (size_t i=0; i!=20; ++i) {
    foo = new Foo;
    bar.setFoo(foo);
    bar.randomize();
    foo.display();
  }
}
