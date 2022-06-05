// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import esdl.base.core;
import esdl.base.comm;

class Foo: Entity {
  Signal!uint sig;

  void SignalRead()
  {
    import std.stdio;
    for(int i=0; i != 10; ++i)
      {
  	// writeln("Waiting for read");
  	wait(2.nsec);
  	// uint a = sig.read();
  	writeln("Reading from Sig: ", sig);
      }
  }

  void SignalWrite()
  {
    import std.stdio;
    for(int i=0; i != 20; ++i)
      {
  	wait(1.nsec);
  	sig = i;
  	writeln("Just wrote: ", i);
      }
  }

  void runSig()
  {
    int foo = 45;
    Fork t = fork(
		  {SignalRead();},
		  {SignalWrite();},
		  {
		    int test = 5;
		    wait(150.nsec);
		    import std.stdio;
		    // waitDelta();
		    Process.self.thisFork.abortTree();
		  },
		  {
		    import std.stdio;
		    writeln("foo is: ", foo);
		    int test = 5; wait(200.nsec);
		  }
		  );
    Fork other = fork(
		      {
			import std.stdio;
			writeln("foo is: ", foo);
			wait(150.nsec);
			// waitDelta();
			// auto tt = t.getActiveTasks();
			t.abortTree();
			// wait(25.nsec);
		      },
		      );
    import std.stdio;
    writeln("**** Time: ", getSimTime());
    wait(150.nsec);
    // disableFork(t);
    t.waitTree();
    writeln("**** Time: ", getSimTime());
  }

  Task!runSig sigRun;
      
  void testDynSig()
  {
    Signal!int test;
    for(int i=0; i < 10; ++i)
      {
    	test = i;
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
  Inst!Foo[2] foo;
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
