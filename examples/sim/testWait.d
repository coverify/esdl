// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
import esdl.base.comm;
// import core.thread;

class Payload
{
  this(int load)
  {
    _load = load;
  }

  int _load;

  int load()
  {
    return _load;
  }
  
}

class Foo: Entity {
  // Event e0;
  Event e1;

  void testEvent() {
    Payload p;
    // e0.notify();
    // wait(e0);
    import std.stdio;
    writeln(getSimTime());
    wait(1);
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
  //   theRootEntity.terminate();
}
