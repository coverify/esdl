import std.stdio;
import esdl.rand;
import esdl.data.bvec;


class Bar
{
  mixin Randomization;

  @rand!8 byte[] foo;
  // @rand ubyte baz = 12;
  //   @rand ubyte[8] bar;

  void display() {
    writeln("foo: ", foo);
    //     writeln("bar: ", bar);
    // writeln("baz: ", baz);
  }

  Constraint! q{
    foo.length <= 8;
    foo.length > 1;
    foo[1] == 24;
    // baz < 32;
  } cstFooLength;


}

void main() {
  Bar foo = new Bar;
  for (size_t i=0; i!=16; ++i) {
    foo.randomize();
    foo.display();
  }
  import std.stdio;
  writeln("End of program");
}
