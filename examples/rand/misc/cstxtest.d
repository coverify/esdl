import esdl.rand;
import std.stdio;

void main()
{
  writeln(constraintXlate("solver", q{
  	foreach (i, x; foo) {
  	  foo[i] == 0;
  	}
      }, __FILE__, __LINE__));
  
  writeln(constraintXlate("solver", q{
	a[0+4] == 0;
      }, __FILE__, __LINE__));
    

  writeln(constraintXlate("solver", q{
  	a == 4;
      }, __FILE__, __LINE__));
  
  writeln(constraintXlate("solver", q{
  	foreach (i, x; a) {
  	  a[i] == 0;
  	}
      }, __FILE__, __LINE__));
  
  writeln(constraintXlate("solver", q{
  	a.b == 4;
      }, __FILE__, __LINE__));
  
  writeln(constraintXlate("solver", q{
  	a.b.c.d == 4;
      }, __FILE__, __LINE__));
  
  writeln(constraintXlate("solver", q{
  	foreach (i, x; a) {
  	  a[i].b == 0;
  	}
      }, __FILE__, __LINE__));
  
}
