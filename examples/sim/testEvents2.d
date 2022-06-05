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
  Event [2][2] e0;
  Event e1;
  Event e2;
  Event e3;
  Event e4;
  Event eOred;
  Event eAnded;
  // Event [1] e4;
  // MonoEvent t;
  int test = 42;

  void hello() {
    // eOred = eBase2 | eBase1;
    // eAnded = eBase2 & eBase1;
    e3 = e1 & e2;
    e4 = e3 & e1;
    eOred = e0[1][0] | e0[1][1];
    eAnded = e0[0][0] & eOred;
    e1.notify(DELTA);
    e2.notify(SimTime(5));
    // e2.notify(DELTA);
    e2.notify(SimTime(2));
    wait(e3);
    e0[1][1].notify(DELTA);
    e0[1][0].notify(SimTime(5));
    e2.notify(SimTime(5));
    wait(eOred);
    writeln("Hello World at time ", getSimTime(), " from ", this.getFullName());
    e1.notify(SimTime(10));
    wait(e3);
    e0[0][0].notify(SimTime(100));
    wait(eAnded);
    writeln("Hello World from a Thread from module ", this.getFullName(),
	    " at time: ", getSimTime());
  }

  Task!hello helloWorld;
      
}

class Sim: RootEntity {
  Inst!(Foo) [16] top;
}

void main()
{
  // top level module
  Sim theRootEntity = new Sim;
  theRootEntity.multicore(0, 1);
  theRootEntity.elaborate("theRootEntity");
  theRootEntity.simulate(10000.nsec);
  // theRootEntity.terminate();
}
