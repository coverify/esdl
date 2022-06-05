// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import esdl.base.core;

class TestProc: Entity
{
  // Event e;
  void bar(size_t ii, size_t nn) {
    import std.stdio;
    writeln("start- ", nn, ":", ii, " time: ", getSimTime());
    fork({
	frop();
      });
    wait((ii*10).nsec);
    writeln("done-  ", nn, ":", ii, " time: ", getSimTime());
  }
  void frop() {
    Event e;
    Event f;
    wait(e);			// wait forever
  }
  void foo() {
    import std.stdio;
    writeln("starting foo");
    size_t n = 0;
    
    while(true) {
      ++n;
      for (size_t i=0; i!=n; ++i)
	{
	  Fork f = fork({
	      // Local copies of i and j are created on stack and
	      // therefor the current values do not affect the messages
	      bar(i, n);
	    },
	    {
	      wait(5.nsec);
	    },
	    {
	      // this thunk keeps track of the latest ii and nn
	      // and that becomes apparent from the messages printed for
	      // done part
	      writeln("start- ", n, ":", i, " time: ", getSimTime());
	      wait((10*i).nsec);
	      writeln("done-  ", n, ":", i, " time: ", getSimTime());
	    }
	    );
	  wait(0);
	}
      wait((5*n).nsec);
      writeln("Aborting some threads at, ", getSimTime());
      abortForks();
      wait((5*n).nsec);
    }
  }

  Task!(foo, 0) foobar0;
  Task!(foo, 1) foobar1;
  
}

class Root: RootEntity
{
  Inst!TestProc test;
}

void main()
{
  Root root = new Root;
  root.multicore(0, 1);
  root.elaborate("root");
  root.simulate(100.nsec);
  root.terminate();
}
