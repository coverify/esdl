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

class Foo: Randomizable
{
  mixin Randomization;
  @rand!(8) byte[] foo;
  // @rand ubyte baz = 12;
  void display() {
    import std.stdio;
    writeln(foo);
  }
  Constraint! q{
    foo.length > 2;
    // baz < 32;
    // FFFF + baz == 50;
  } cstFooLength;
}

class Bar: Foo
{
  // mixin Randomization;
  mixin(randomization());
  @rand ubyte[8] bar;


  override void display() {
    writeln("foo: ", foo);
    writeln("bar: ", bar);
    // writeln("baz: ", baz);
  }

  Constraint! q{
    foo.length > 2;
    // baz < 32;
    // FFFF + baz == 50;
  } cstFooLength;

  Constraint! q{
    foreach(i, f; bar) f <= i;

    // this is a comment
    foreach(i, f; foo) {
      if(i < 6) {
  	f < 24;
      }
      else {
  	f < 18;
      }
    }

    foreach(i, f; foo) {
      f < 64;
      foo[i] > 16;
    }
  } cstFoo;

  override void preRandomize() {
    FFFF++;
  }

}

void main() {
  Foo foo = new Foo;
  for (size_t i=0; i!=16000; ++i) {
    foo.randomize();
    foo.display();
  }
}
