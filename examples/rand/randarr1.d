// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

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
  } cst_foo;

  // Constraint! q{
  //   //    foreach(i, f; bar) f <= i;

  //   // this is a comment
  //   foreach(i, f; foo) {
  //     if(i < 6) {
  // 	f < 24;
  //     }
  //     else {
  // 	f < 18;
  //     }
  //   }

  Constraint! q{
    foreach(i, f; foo) {
      // if (i == 1) f == 24;
      f < 64;
      foo[i] > 16;
    }
  } cstFoo;

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
