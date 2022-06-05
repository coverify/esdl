// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import esdl.base.core;
import esdl.base.comm;

class Foo: Entity {
  Signal!bool sig;

  void SignalRead()
  {
    import std.stdio;
    for(int i=0; i != 10; ++i)
      {
  	// writeln("Waiting for read");
  	wait(1.nsec);
  	// bool a = sig.read();
  	writeln("Reading from Sig: ", sig, " at time ", getSimTime());
      }
  }

  void SignalWrite()
  {
    import std.stdio;
    for(int i=0; i != 20; ++i)
      {
  	wait(1.nsec);
  	sig = cast(bool) (i % 2);
  	writeln("Just wrote: ", i % 2, " at time ", getSimTime());
      }
  }

  void runSig()
  {
    fork(
       {SignalRead();},
       {SignalWrite();},
       ).joinAll;
  }

  Task!runSig sigRun;
  Task!SignalWrite write;
  Task!SignalRead read;
      
  void testDynSig()
  {
    Signal!bool test;
    for(int i=0; i < 10; ++i)
      {
    	test = cast(bool) (i%2);
    	wait(1.nsec);
    	import std.stdio;
    	writeln ("test is ", test);
      }
  }

  Task!testDynSig sigTest;


}

class Sim: RootEntity {
  // Inst!(Foo) [320] top;
  // Inst!(Foo) [2] top;
  Inst!Foo[1] foo;
  // Foo[2] foo;
}

int main()
{
  // top level module
  // writeln("Size of EventNotice is: ", EventNotice.sizeof);
  // writeln("Size of Time is: ", Time.sizeof);
  
  Sim theRootEntity = new Sim;
  theRootEntity.multicore(0, 1);
  theRootEntity.elaborate("theRootEntity");
  theRootEntity.simulate(1000.nsec);
  // theRootEntity.terminate();
  return 0;
}
