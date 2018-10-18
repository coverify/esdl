import esdl.rand;
import std.stdio;

void main()
{
  writeln(constraintXlate(q{
  	foreach (i, x; foo) {
  	  foo[i] == 0;
  	}
      }, __FILE__, __LINE__));
  
  writeln(constraintXlate(q{
	a[0+4] == 0;
      }, __FILE__, __LINE__));
    

  writeln(constraintXlate(q{
  	a[0..4] == 0;
      }, __FILE__, __LINE__));
  
}
