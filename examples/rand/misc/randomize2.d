// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.rand;
import esdl.data.bvec;
import std.string: format;

class Foo: Randomizable
{
  mixin Randomization;
  @rand int roo;
}


enum AhbMode: ubyte {BURST, BURST_WRAP, SINGLE, IDLE, NONE}

class Bar: Foo
{
   mixin Randomization;

  // private @rand!(16) ushort bob[];
  private @rand ubyte pop;
  private @rand ubyte bro;

  private @rand AhbMode mode;
  
  @rand ubyte foo;

  void display() {
    import std.stdio;
    writeln("bro: ", bro, " pop: ", pop, " foo: ", format("%08b", foo), " mode: ", mode);
  }

  void preRandomize() {
    // foo++;
  }

  // void post_randomize() {
  //   writeln("Post Randomize Called");
  // }

  Constraint! q{
    pop > bro;
    pop < 8;
    // foo < 3;
    if(mode == AhbMode.SINGLE) {
      foo[0..3] == 0;
    }
    foo == 2 -> pop == 4;
    pop <= 4 -> bro == 0;
    if(foo[3..5] == 0) {
      bro == 5;
    }
    else {
      bro == 0;
    }
  } cst01;
}

void main()
{
  auto foo = new Bar;
  
  auto myMode = AhbMode.NONE;
  for (size_t i=0; i != 100; ++i)
    {
      if(myMode == AhbMode.NONE) {
	myMode = AhbMode.BURST;
      }
      else {
	myMode++;
      }
      // foo.randomizeWith!q{mode == @0;}(myMode);
      foo.randomize;
      foo.display();
    }
}
