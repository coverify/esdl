import esdl.rand;

import randstructfoo;

class Bar {
  mixin Randomization;
  @rand Foo foo;
  void preRandomize() {
    zoo++;
  }
  int zoo = 64;

  Constraint!q{
    foo.frop == zoo;
  } frop_cst;
public:
  void display() {
    foo.display();
  }
}

void main()
{
  Bar bar = new Bar();
  for (size_t i=0; i!=20; ++i)
    {
      bar.randomize();
      bar.display();
    }
}
