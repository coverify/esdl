import esdl.rand;

class Foo {
  mixin Randomization;
  @rand int frop;
  Constraint!q{
    frop >= 0;
    frop < 128;
  } frop_cst;
public:
  void display() {
    import std.stdio;
    writeln("frop is: ", frop);
  }
  this() {
  };
}

class Bar {
  mixin Randomization;
  @rand Foo foo;
  this() {
    foo = new Foo();
  }
  void preRandomize() {
    // foo = new Foo();
    frop++;
  }
  int frop = 64;

  Constraint!q{
    foo.frop == frop;
  } frop_cst;
public:
  void display() {
    foo.display();
  }
}

void main()
{
  Bar bar = new Bar();
  for (size_t i=0; i!=20; ++i)
    {
      bar.randomize();
      bar.display();
    }
}
