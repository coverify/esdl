// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl;

int FFFF = 20;

class Foo
{
  mixin Randomization;
  @rand(32) byte[] foo;
  @rand ubyte baz = 12;
  void display() {}
}

class Bar : Foo
{
  mixin Randomization;

  @rand ubyte[8] bar;


  override void display() {
    writeln("foo: ", foo);
    writeln("bar: ", bar);
    writeln("baz: ", baz);
  }

  Constraint! q{
    foo.length > 12;
    baz < 32;
    // FFFF + baz == 50;
  } cstFooLength;

  Constraint! q{
    foreach(i, f; bar) f <= i;

    // this is a comment
    foreach(i, f; foo) {
      if (i < 2) {
	f < 24;
      }
      else {
	f < 8;
      }
    }

    foreach(i, f; foo) {
      f < 64;
      foo[i] > 0;
    }
  } cstFoo;

  void preRandomize() {
    FFFF += 2;
  }

  void postRandomize() {
    FFFF++;
  }

}

void main() {
  Bar foo = new Bar;
  for (size_t i=0; i!=40; ++i) {
    foo.randomize();
    foo.display();
  }
  import std.stdio;
  writeln("End of program");
}
