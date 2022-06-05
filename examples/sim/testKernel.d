// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
// import core.thread;


class Foo: Entity {
  class Bar: Entity {
    Event [2][] e0;
    Event [][2] e1;
    Event [][] e2;
    Event  e3;
    // Event [1] e4;
    // MonoEvent t;
    int test = 42;
    override void doBuild () {
      e0 = new Event[2][1];
      foreach (ref e; e1)
	e = new Event[1];
      e2 = new Event[][2];
      foreach (ref e; e2)
	e = new Event[1];
    }

    void hello() {
      e3.notify(0);
      wait(e3);
      writeln("Hello World at time 0 from ", this.getFullName);
      e3.notify(SimTime(10));
      wait(e3);
      writeln("Hello World from a Thread from module ", this.getFullName);
    }

    Task!hello helloWorld;
      
  }
    
  Inst!Bar sub1;
  // Inst!(Bar) sub2;
  Inst!Bar [4] sub2;
}

class Sim: RootEntity {
  Inst!(Foo) top;
  Event e1;
  Event e2;
  Event e3;
  uint ui;
  void proc1() {
    Event e5 = e1 | e2;
  }
}

void main()
{

  Sim theSimulator = new Sim;
  theSimulator.multicore(0, 1);
  theSimulator.elaborate("theSimulator");
  theSimulator.simulate(10000.nsec);
  //   theSimulator.terminate();

  auto m = theSimulator.top.sub1;
  auto u = theSimulator.ui;
  writeln("Type of m: ", typeid(typeof(m)));
  writeln(theSimulator.top.sub1.getFullName);
  writeln(theSimulator.top.sub1.getRoot.getName);
  writeln(m.test);
}
