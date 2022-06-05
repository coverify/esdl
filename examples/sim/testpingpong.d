import esdl;

class Foo: Entity {
  Event e1;
  Event e2;

  int x;

  void hello1() {
    while ( x < 100 )
      {
	e1.notify(0);
	wait(e2);
	import std.stdio;
	writeln("** --> ", getSimTime());
      }
  }

  void hello2() {
    while ( x < 100 )
      {
	e2.notify(0);
	wait(e1);
	x += 1;
	import std.stdio;
	writeln("## --> ", getSimTime());
      }
  }

  Task!hello1 hello1World; // = Task(&hello);
  Task!hello2 hello2World;
      
}

@timeUnit(100.psec)

class Sim: RootEntity {

    Foo[2] top;
}

int main()
{
  Sim theRootEntity = new Sim;
  theRootEntity.multicore(0, 1);
  theRootEntity.elaborate("theRootEntity");

  theRootEntity.simulate();
  return 0;
}
