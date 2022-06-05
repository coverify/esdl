// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
import esdl.base.comm;
import std.random;
// import core.thread;

class Foo: Entity {
  // Event e0;
  Event[15] e1;
  Event e2;

  void testEvent()
  {
    // e0.notify();
    // wait(e0);
    Event e3 = orEvents(e1, e2);
    foreach(i, ref e; e1) {
      size_t j = uniform(0,1024);
      e.notify(j.nsec);
      writeln(j);
    }
    // e2.notify();
    wait(e3);
    writeln("Waited till time: ", getSimTime());
  }

  Task!testEvent test;

}

class Sim: RootEntity {
  Inst!(Foo) top;
}

void main()
{
  Sim theRootEntity = new Sim;
  theRootEntity.multicore(0, 1);
  theRootEntity.elaborate("theRootEntity");
  theRootEntity.simulate(1000000.nsec);
  // theRootEntity.terminate();
}
