// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>
import esdl.base;
import esdl.data.bvec;
import std.stdio;

@parallelize(ParallelPolicy.SINGLE)
class Foo: Entity {
  void hello() {
    writeln("Greetings from: ",
	    Process.self.getFullName());
    writeln("Thread: ", getParConfig().getThreadIndex());
    Bit!233 foo = urandom!(Bit!233);
    writeln(foo);
  }
  Task!hello[2] greet;
  Worker!hello[2] greetWorld;
  static this() {
    // import std.stdio;
    // writeln("hehe");
  }
}
@timeUnit(1.nsec)
@timePrecision(1.psec)
class Top: Entity {
  Foo[4] foo;
}
void main() {
  simulate!Top("root");
}
