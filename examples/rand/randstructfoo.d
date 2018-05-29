import esdl.rand;

struct Foo {
  private @rand int frop;
public:
  void display() {
    import std.stdio;
    writeln("frop is: ", frop);
  }
}

