import esdl.data;

ubyte b;

class Tx {
  mixin Randomization;
  @rand int c;
  @rand int z;
  Foo coverage;

  class Foo: CoverGroup
  {
    int a;
    CoverPoint!a cp_a;
    CoverPoint!b cp_b;
    CoverPoint!c cp_c;
  }
  this() {
    coverage = new Foo();
  }

}


void main()
{
  import std.stdio;
  Tx tx = new Tx();
  for (size_t i=0; i!=64; ++i) {
    b = cast(ubyte) i;
    tx.randomize();
    tx.coverage.sample(tx.z);
  }
  writeln(tx.coverage.cp_a.getBins());
  writeln(tx.coverage.cp_b.getBins());
  writeln(tx.coverage.cp_c.getBins());
}
