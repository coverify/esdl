import esdl.data.packed;
import esdl.data.bvec;

struct A
{
  UBit!32 foo;
  UBit!32 foo1;
  UBit!32 foo2;
  UBit!32 foo3;
  UBit!32 foo4;
  UBit!32 foo5;
  UBit!32 foo6;
  UBit!32 foo7;
  UBit!32 foo8;
  mixin(bitfields!(bool, "flag1",    1,
		   bool, "flag2",    1,
		   uint, "flag4",    6));
  pragma(msg, bitfields!(bool, "flag1",    1,
			 bool, "flag2",    1,
			 uint, "flag4",    6));
}

void main()
{
  import std.stdio;
  writeln(A.sizeof);
}
