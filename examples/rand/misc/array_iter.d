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

  byte[] bar = [0, 42, 17, 29];

  @rand!8 byte[] foo;

  void display() {
    writeln("foo: ", foo);
  }

  Constraint! q{
    foo.length == 6;
    foreach (i, b; bar) foo[i] == bar[i];
  } cst_arr;

  void preRandomize() {
    bar[0] += 1;
  }
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
