module esdl;

public import esdl.base;
public import esdl.data;
public import esdl.intf;
public import esdl.sys;
version(ESDL_NORAND) {}
 else {
   public import esdl.rand;
 }
