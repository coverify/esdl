import esdl;

class mm_seq_item(int DW, int AW): Randomizable
{
  mixin Randomization;
  
  enum kind_e: byte {READ = 0, WRITE = 1};
  enum BW = DW/8;

  @rand UBit!AW address;
  @rand kind_e kind;
  @rand Bit!DW writedata;
  ULogic!DW readdata;
  @rand UBit!BW byteenable;

  @rand ubyte be_lsb;
  @rand ubyte be_msb;
  @rand ubyte be_cnt;
  @rand ubyte be_num;
  
  void display() {
    import std.stdio;
    writeln("address: ", address, ", kind: ", kind,
	    ", writedata: ", writedata, ", readdata: ", readdata,
	    ", byteenable: ", byteenable);
  }
  
  Constraint! q{
    address < 64;
    address % BW == 0;		// byte align the address
  } addressCst;

  Constraint! q{
    kind == kind_e.READ ||
      kind == kind_e.WRITE;
  } kindCst;
  
  Constraint! q{
    be_msb <= BW;
    be_cnt < be_msb;
    be_num == (1 << be_cnt);
    be_msb == be_lsb + be_num;
    be_lsb % be_num == 0;
    byteenable == (1 << be_msb) - (1 << be_lsb);
  } byteenableCst;

}

alias mm_trans = mm_seq_item!(64, 64);

void main()
{
  auto tr = new mm_trans;
  for (size_t i=0; i!=100; ++i)
    {
      import std.stdio;
      tr.randomize();
      tr.display();
    }
}
