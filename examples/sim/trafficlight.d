// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
import esdl.base.comm;

@timeUnit(1.nsec)
class TrafficLight: Entity
{
  // mixin(entityMixin());

  enum POLES = 4;
  Event[POLES] red;
  Event[POLES] yellow;
  Event[POLES] green;
  long[10]     foo;
  int count = 0;


  void susLight() {
    wait(1000);
    import std.stdio;
    writeln("Suspending Operations");
    foreach(l; tLightTT) {
      l.suspend;
    }
    wait(50);
    writeln("Resuming Operations");
    foreach(l; tLightTT) {
      l.resume;
    }

  }

  void testPhase() {
    // wait(0);
    if(Process.self.stage == 10) {
      wait(0);
    }
    // writeln("Stage: ", Process.self.stage);
  }

  void light() {
    // lockStage();
    // writeln(getSimTime);
    // wait((cast(Dummy) getParent).e);
    auto index = Process.self.taskIndices[0];
    if(index != 0)
      wait(green[index]);
    // writeln("Time unit is: ", timeUnit());
    while(true)
      {
	// lockStage();
	// unlockStage();
	writeln(getRoot().getSimTime(), ": Red -> Green ", index, " -- ",
		Process.self.getFullName());
	yellow[index].notify(20);
	// writeln("I am here: ", index);
	red[index].notify(25);
	wait(yellow[index]);
	// writeln("Green -> Yellow ", index);
	wait(red[index]);
	//writeln("Yellow -> Red ", index);
	green[(index + 1)%POLES].notify();
	wait(green[index]);
	synchronized(this) {
	  count = count + 1;
	  // ++count;
	  // if(count == 1) getRoot.abortTree();
	}
      }
  }
  public int x;
  void weee() {
    import std.stdio;
    writeln("This is Worker");
  }
  Worker!(weee) thisWork;
  // Task!("light()",0)  tLightTT[POLES];
  Work!(light, 5)[POLES]   tLightTT;
  // Task!(testPhase, -1)  test_1;
  // Task!(testPhase, 10)  test2;
  // Task!(testPhase, 11)  test11;
  // Task!(testPhase, -3)  test3;
  // Task!(testPhase, -4)  test4;
  // Task!(testPhase, -5)  test5;

  Task!(susLight, 5) suspendLight;
}

class TrafficLightWrapper: TrafficLight {}

class Dummy: Entity
{
  // Event e;
  // void etrigger()
  // {
  //   wait(990.nsec);
  //   e.notify();
  // }
  // Task!(etrigger, 0) trigE;

  private TrafficLightWrapper[1] traffic;
}

@timeUnit(100.psec)
@timePrecision(10.psec)
class TrafficRoot: RootEntity
{
  @multicore(0, 4) Inst!Dummy[2] dummy;
}

void main()
{
  import std.stdio;
  // top level module
  TrafficRoot theRoot = new TrafficRoot;
  theRoot.multicore(0, 4, 2);
  // theRoot.multicore(0, 4);
  theRoot.elaborate("theRoot");
  // theRoot.waitElab();
  // theRoot.simulate(100.nsec);
  // theRoot.waitSim();
  // theRoot.simulate(200.nsec);
  // theRoot.waitSim();
  // theRoot.simulate(1000.nsec);
  // theRoot.waitSim();
  // theRoot.simulate(2000.nsec);
  // theRoot.waitSim();

  // theRoot.doSim(25.nsec);
  // theRoot.waitSim();
  theRoot.simulateUpto(25.nsec);
  // theRoot.simulate(2500.nsec);
  // theRoot.simulate(0.nsec);

  import core.thread;
  Thread[] all = Thread.getAll();

  // foreach (th; all) {
  //   if (th.isRunning()) {
  //     SimThread sth = cast(SimThread) th;
  //     if (sth !is null) {
  // 	writeln("Thread ", sth.getName(), " is RUNNING");
  //     }
  //     else {
  // 	writeln("Not a SimThread");
  //     }
  //   }
  // }
  

  theRoot.finish();
  // theRoot.simulate();
  // theRoot.terminate();
  // theRoot.simulate(250.nsec);




  // foreach (th; all) {
  //   if (th.isRunning()) {
  //     writeln("Thread ", th, " is running");
  //   }
  // }
  
  // Thread.sleep( dur!("seconds")( 5 ) ); // sleep for 5 seconds
  
  // foreach (th; all) {
  //   if (th.isRunning()) {
  //     SimThread sth = cast(SimThread) th;
  //     if (sth !is null) {
  // 	writeln("Thread ", sth.getName(), " is running");
  //     }
  //     else {
  // 	writeln("Not a SimThread");
  //     }
  //   }
  // }
  
  // for (size_t i=1; i!=20; ++i) {
  //   theRoot.doSim((i*100).nsec);
  //   theRoot.waitSim();
  // }
  // theRoot.terminate();
}
