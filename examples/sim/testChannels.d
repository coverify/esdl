// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
import esdl.data.bvec;
import esdl.base.comm;

class Chan: Channel {
  override final void update()
  {
    // writeln("Updating Channel");
  }
}

interface Frop {
  int event(int t);
  Event event();
  Event posedge();
  Event negedge();

  void write(Logic!8);
  Logic!8 read();

  void registerPort();
}
  
class FropChan: Entity, Frop {
  private Event _event;
  private Event _posedge;
  private Event _negedge;

  Logic!8 var1;


  Event event() {return _event;}

  int event(int t) {return 1;}

  Event posedge() {return _posedge;}
  Event negedge() {return _negedge;}
  
  void write(Logic!8 l) {
    var1 ^= l;
  }

  Logic!8 read() {
    return var1;
  }

  void registerPort() {
    writeln("Registering Port");
  }
}

class Bar: Entity {
}

@timePrecision(1.psec)
@timeUnit(100.psec)
class Foo: Entity {
  FropChan chan;

  // Port!Frop p;

  Bar bar;
  Event e1;
  int test = 42;

  void helloDynamicTask() {
    writeln("- - - - - - Hello World from Dynamic Task");
  }

  void helloDynamicRoutine() {
    writeln(". . . . . . Hello World from Dynamic Routine");
    nextTrigger(10.nsec);
    // e1.notify();
  }

  void hello() {
    Event[4] ev; // Event [] ev = 
    Event e2; // = Event();

    Event e3 = e1 & e2;
    Event e4 = e3 | e1;
    // e3 = e1 & e2;
    // Event EEEE = e3 | e4;
    Event eOred = ev[2] | ev[3];
    Event eAnded = ev[0] & eOred;
    e1.notify(SimTime(1));
    e2.notify(SimTime(5));
    // e2.notify(ZERO_TIME);
    e2.notify(2.nsec);
    helloWorld.sensitiveTo = e1 & e3;
    auto hdt=new Task!({helloDynamicTask();}, 0);
    hdt.dontInitialize();
    hdt.sensitiveTo(e1);

    auto hdm = routine(&helloDynamicRoutine);
    // hdm.dontInitialize();
    hdm.sensitiveTo(e1);
    wait(e1 & e3);
    writeln("----------------------------Hello World");
    ev[3].notify(0);
    ev[2].notify(5.psec);
    e2.notify(SimTime(5));
    wait(eOred);
    writeln("Hello World from ", this.getFullName());
    e1.notify(SimTime(10));
    wait(e4);
    ev[0].notify(SimTime(100));
    Event e5 = ev[0] & eOred;
    // wait(eAnded);
    // Event e6 = (ev[0] & eOred) & SimTime(10);
    e1.notify();
    wait(e4);
    // Event e6 = e1 | SimTime(10);
    wait(eAnded);
    // wait(eAnded);
    writeln("Hello World from a Thread from module ", this.getFullName());
  }

  Task!hello helloWorld;
      
  override void doBuild() {
    // printProxyEvents!Frop();
    // auto b = [ __traits(allMembers, BasePort!Frop) ];
    // writeln(b);
  }
}

@timeUnit(100.psec)
@timePrecision(10.psec)
class Sim: RootEntity {
  Inst!(Foo) [2] top;
}

int main()
{
  // top level module
  Sim theRootEntity = new Sim;
  theRootEntity.multicore(0, 1);
  theRootEntity.elaborate("theRootEntity");
  theRootEntity.simulate(100.nsec);
  theRootEntity.terminate();
  return 0;
}
