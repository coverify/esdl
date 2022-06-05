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
  Notification!int e1;

  void testEvent()
  {
    // e0.post();
    // wait(e0);
    import std.stdio;
    e1.post(0.psec, 10);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 20);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 30);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 100);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 200);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 300);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 1000);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 2000);
    wait(e1);
    writeln("time is: ", getSimTime);
    writeln("Payload is: ", e1.get());
    e1.post(0.psec, 3000);
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
  theRootEntity.simulate(10000.nsec);
  // theRootEntity.terminate();
}
