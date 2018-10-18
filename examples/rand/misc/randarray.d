// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.rand;
import esdl.data.obdd;
import esdl.data.bvec;

int FFFF = 20;

class Foo
{
  mixin Randomization;
  @rand!8 byte[] foo;
  @rand ubyte baz = 12;
  void display() {
    writeln("foo: ", foo);
    writeln("baz: ", baz);
  }
  Constraint! q{
    foo.length > 2;
    baz < 32;
    foreach(i, f; foo) {
      f < 64;
      foo[i] > 16;
    }
  } cstFooLength;
}


void main() {
  Foo foo = new Foo;
  for (size_t i=0; i!=20; ++i) {
    foo.randomize();
    foo.display();
  }
}
