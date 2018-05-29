// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl;

class Foo
{
  mixin Randomization;
  @rand int roo;
  private @rand ubyte pop;
  Constraint! q{
    roo > 2;
  } rooc;
}


byte foo = -10;


class Bar: Foo
{
  // mixin(_esdl__randomizable());

  // private @rand!(16) ushort bob[];
  mixin Randomization;

  private @rand ubyte bro;

  @rand Bit!1 pun3 = 0;
  @rand ubyte mom;
  @rand ubyte sis;

  @rand ULogic!18 pun1 = 0;
  @rand ubyte pun2 = 0;

  // @rand!(16) ubyte[] bar;
  
  void display() {
    import std.stdio;
    writeln("bro: ", bro, " sis: ", sis, " pop: ", pop, " mom: ", mom,
	    " foo: ", foo, " pun3: ", pun3, " pun1: ", pun1, " pun2: ", pun2);
  }

  void preRandomize() {
    if(foo == 20) foo = 0;
    else foo++;
  }

  // void post_randomize() {
  //   writeln("Post Randomize Called");
  // }

  Constraint! q{
    foo + pop + mom == 64;
    // pop % 3 == 0;

    pun1[0..4] == 0;

    // foo + pop + mom == 64 ? pop > 40 : mom > 24;

    (foo + pop + mom == 64 && pop > 40) || (foo + pop + mom != 64 && mom > 24);

    mom > 8 || mom < 25;

    // foreach(b; bar) {
    //   b < 16;
    // }

    // bar.length > 8;
    // bar.length <= 16;

    // bar.length > 8;
    // bar.length < 16;
    
  } cst01;

  Constraint! q{
    // this is a comment
    foo + bro + sis == 64;
    bro > 40;
    bro < 80;
    sis < 24;
    pop > 40;
    if(pop <= 48) {
      bro == pop;
      // if(sis <= 1) pun2 == mom + 5;
      // else pun2 == mom << 4;
    }
    // pop + kid3 == 24;
  } cst10;

  // Constraint! q{
  //   foo > bar;
  //   foo == 0 || foo == 231243432;
  //   solve foo before bar;
  // }

  // Constraint! q{
  //   pop1 + mom2 + kid3 > 64;
  //   pop + kid3 == 24;
  // } cst1;


  // Constraint! q{
  //   pop < 64;
  //   mom == 1;
  //   kid == 4;
  // } cst10;

}

void main()
{
  auto foo = new Bar;
  for (size_t i=0; i!=10; ++i)
    {
      foo.randomize();
      foo.display();
    }
}
