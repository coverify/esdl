// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;

class Foo: Entity {
  Event e1;
  Event e2;

  void hello1() {
    for ( ;  ;  )
      {
	e1.notify(5);
	wait(e2);
	import std.stdio;
	writeln("** --> ", getSimTime());
      }
  }

  void hello2() {
    for ( ;  ;  )
      {
	e2.notify(10);
	wait(e1);
	import std.stdio;
	writeln("## --> ", getSimTime());
      }
  }

  Task!hello1 hello1World; // = Task(&hello);
  Task!hello2 hello2World;
      
}

@timeUnit(10.psec)
class Sim: RootEntity {
    Foo[2] top;
}

int main()
{
  Sim theRootEntity = new Sim;
  theRootEntity.multicore(0, 1);
  theRootEntity.elaborate("theRootEntity");
  theRootEntity.simulate(1.nsec);
  theRootEntity.terminate();
  return 0;
}
