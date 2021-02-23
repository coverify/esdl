import esdl.data;
import esdl.rand;


class Tx {
  mixin Randomization;
  @rand ubyte b;
  @rand int c;
  @rand int z;
  string s;
  Foo coverage;

  @rand(false) class Foo: CoverGroup
  {
    int a;
    CoverPoint!(a, q{
	bins a = { [0:63],65 };
	bins b[] = { [127:130],[137:147],200,[100:108] }; // note overlapping values
	bins c[] = { 200,201,202 };
	bins d = { [1000:$] };
	// bins others[] = default;
      }) cp_a;
      
    CoverPoint!b cp_b;
    CoverPoint!c cp_c;
    // CoverPoint!s cp_s;
  }

  this() {
    coverage = new Foo();
  }

}


void main()
{
  import std.stdio;
  Tx tx = new Tx();
  for (size_t i=0; i!=256; ++i) {
    // b = cast(ubyte) i;
    tx.randomize();
    tx.coverage.sample(tx.z); // sample(tx.coverage, tx.c)
  }
  writeln(tx.coverage.cp_a.getBins());
  writeln(tx.coverage.cp_b.getBins());
  writeln(tx.coverage.cp_c.getBins());
}
