// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
import esdl.base.comm;
// import core.thread;

class Foo: Entity {
  // Event e0;
  Event e1[15];
  Event e2;

  void testEvent()
  {
    // e0.notify();
    // wait(e0);
    import std.stdio;
    import std.random;
    // Event e3 = andEvents(e1, e2);
    foreach(i, ref e; e1) {
      size_t j = uniform(0,1024);
      e.notify(j.nsec);
      writeln(j);
    }
    // e2.notify();
    waitAll(e1, 100000.nsec);
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
  theRootEntity.elaborate("theRootEntity");
  theRootEntity.simulate(1000000.nsec);
  // theRootEntity.terminate();
}
