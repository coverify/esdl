// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

import esdl.base.core;
import esdl.base.comm;


class Consumer: Entity
{
  Port!(FifoInBIF!uint) fifoIn;

  void fifoConsume()
  {
    import std.stdio;
    for(int i=0; i != 50; ++i)
      {
	// writeln("Waiting for read");
	uint a = fifoIn.read();
	writeln("Reading from Fifo: ", a);
	wait(2.nsec);
      }
    // wait(20.nsec);
    for(int i=0; i != 50; ++i)
      {
	// writeln("Waiting for read");
	uint a = fifoIn.read();
	writeln("Reading from Fifo: ", a);
	// wait(2.nsec);
      }
  }
  Task!fifoConsume consume;

}

class Producer: Entity
{
  Port!(FifoOutBIF!uint) fifoOut;

  void fifoProduce()
  {
    import std.stdio;
    for(int i=0; i != 100; ++i)
      {
	wait(1.nsec);
	fifoOut.write(i);
	writeln("Just wrote: ", i);
      }
  }

  Task!fifoProduce produce;
}

class Foo: Entity {
  Fifo!uint fifo;

  Export!(FifoOutBIF!uint) fifoOut;
  Export!(FifoInBIF!uint) fifoIn;

  Inst!Producer producer;
  Inst!Consumer consumer;

  override void doConnect()
  {
    fifoOut(fifo);
    fifoIn(fifo);
    // writeln("Connecting Ports");
    producer.fifoOut(fifoOut);
    consumer.fifoIn(fifoIn);
  }

      

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
