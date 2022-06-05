// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
import esdl.base.comm;

// class Chan: Channel
// { mixin(Elaboration());
//   override final void update()
//   {
//     // writeln("Updating Channel");
//   }
// }

interface Frop {}

class Bar: Entity {
  // Port!Frop frop;
}

@timePrecision(10.psec)
@timeUnit(100.psec)
class Foo: Entity {
  // Chan channel12;
  Inst!Bar bar;
  Event e1;
  int test = 42;
  Mutex me;
  void helloDynamicTask() {
    me.lock();
    writeln("- - - - - - Hello World from Dynamic Task");
  }

  void helloDynamicRoutine() {
    import std.random: uniform;
    writeln(". . . . . . Hello World from Dynamic Routine");
    writeln("Random integer: ", uniform(0, 31));
    nextTrigger(10.nsec);
    // e1.notify();
  }

  void hello() {
    Event [] ev = Event[4];
    Event e2 = Event();
    Mutex ml;
    Event e3 = e1 & e2;
    Event e4 = e3 | e1;
    // e3 = e1 & e2;
    Event EEEE = e3 | e4;
    Event eOred = ev[2] | ev[3];
    Event eAnded = ev[0] & eOred;
    ml.lock();
    e1.notify(SimTime(1));
    e2.notify(SimTime(5));
    // e2.notify(DELTA);
    e2.notify(2.nsec);
    helloWorld.sensitiveTo = e1 & e3;
    me.lock();
    me.unlock();
    // auto hdt=new Task!({helloDynamicTask();}, 0);
    // // auto foooo = new Task!(() {helloDynamicTask();}, 0);
    // // auto foooooo = new Task!helloDynamicTask;
    // // hdt.dontInitialize();
    // hdt.sensitiveTo(e1);
    ml.unlock();
    auto hdm=routine(&helloDynamicRoutine);
    // hdm.dontInitialize();
    hdm.sensitiveTo(e1);
    assert(RootThread.self is null);
    writeln(getSimTime," Right before Join");
    auto foo = fork
      (
       process({writeln("fork 0"); wait(4.nsec);}),
       process({writeln("fork 1");}),
       process({writeln("fork 2");}),
       process({writeln("fork 3"); wait(5.nsec);}),
       process({writeln("fork 4"); wait(40.nsec);})
       );
    foo.joinAny;
    writeln(getSimTime," Right after Join");
    // wait(1.nsec);
    // abortForks();
    writeln("After abortForks");
    foo.wait();
    // waitForks();
    assert(Process.self !is null);
    assert(RootThread.self is null);
    writeln("After waitForks");
    writeln(getSimTime," Later after Join");
    wait(e1 & e3);
    writeln("----------------------------Hello World");
    ev[3].notify(DELTA);
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
    e1.notify(DELTA);
    writeln("2 Hello World from ", this.getFullName());
    wait(e4);
    // Event e6 = e1 | SimTime(10);
    writeln("3 Hello World from ", this.getFullName());
    wait(eAnded);
    // wait(eAnded);
    writeln("Hello World from a Thread from module ", this.getFullName());
  }

  Task!hello helloWorld;
  // Process!hello helloProcess;
      
}

@timeUnit(100.psec)
@timePrecision(10.psec)
class Sim: RootEntity {
  Inst!Foo [1] top;
  // Inst!(Foo) [2] top;
  // Inst!Foo[4] foo;
  // Foo[2] foo;
  override void doBuild() {
    // srandom(0);
  }

}

void main()
{
  // top level module
  Sim theRootEntity = new Sim();
  theRootEntity.multicore(0, 1);
  theRootEntity.elaborate("theRootEntity");
  theRootEntity.simulate(100.nsec);
  theRootEntity.terminate();
}
