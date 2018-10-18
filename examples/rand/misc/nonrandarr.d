// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.rand;
import esdl.data.obdd;
import esdl.data.bvec;

class Bar
{
  mixin Randomization;
  @rand ubyte bar;
  ubyte[] foo;
  // @rand ubyte baz = 12;
  //   @rand ubyte[8] bar;

  void display() {
    writeln("foo: ", foo);
    writeln("bar: ", bar);
    //     writeln("bar: ", bar);
    // writeln("baz: ", baz);
  }

  Constraint! q{
    foreach (f; foo) {
      bar < f;
    }
  } cstFoo;

}

void main() {
  Bar foo = new Bar;
  foo.foo = [4, 5, 6];
  for (size_t i=0; i!=16; ++i) {
    foo.randomize();
    foo.display();
  }
  import std.stdio;
  writeln("End of program");
}
