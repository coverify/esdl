module esdl.data;

public import esdl.data.bstr;
public import esdl.data.bvec;
public import esdl.data.cover;
public import esdl.data.packer;
public import esdl.data.queue;
public import esdl.data.sync;
public import esdl.data.time;
version(ESDL_NORAND) {}
 else {
   public import esdl.data.rand;
   public import esdl.data.obdd;
   public import esdl.data.cstx;
 }
