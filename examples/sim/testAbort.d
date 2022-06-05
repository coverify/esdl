// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import std.stdio;
import esdl.base.core;
import esdl.base.comm;

class Foo: Entity
{
  uint s;
  void frop() {
    // srandom(2);
    writeln("frop 0");
    fork({
	writeln("fork 0");
	wait(0);
	writeln("fork 1");
	wait(100);
	writeln("fork 2");
      });
    import std.stdio;
    writeln("before wait");
    wait(0);
    writeln("after wait");
    fork({
	writeln("fork 4");	// should not get printed
	wait(10);
      });
    // finish();			// 
    writeln("frop 1");
    wait(0);
    writeln("frop 2");
  }
  
  Task!frop p;

  void stage2() {
    import std.stdio;
    writeln("stage2");
  }

  Task!(stage2, 2) s2;

}

@timeUnit(100.psec)
@timePrecision(10.psec)
class Bar: RootEntity {
  Inst!Foo foo;
}

void main()
{
  // top level module
  Bar theRoot = new Bar;
  theRoot.multicore(0, 1);
  theRoot.elaborate("theRoot");
  theRoot.simulate(1.nsec);
  theRoot.terminate();
}
