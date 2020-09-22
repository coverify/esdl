module esdl.intf.hal;

enum HalOp: ubyte {
  READ_REQ  = 0b00000000,
  WRITE_REQ = 0b00000001,
  READ_RSP  = 0b00000010,
  WRITE_RSP = 0b00000011,
  DONE      = 0b11111111
}

enum HalResult: ubyte {
    SUCCESS       = 0b00000000,
    BAD_ADDRESS   = 0b00000001,
    MALFORMED     = 0b00000010,
    RESOURCE_BUSY = 0b00000011,
    RESOURCE_ERR  = 0b00000100,
    DELAYED       = 0b00000101
}

align(1) struct HalHeader {
  uint     _oplen;
  uint     _seqid;
  uint     _version;
  HalOp    _opcode;
  ubyte    _result;
}

align(1) struct HalReadReq {
  ulong    _address;
  uint     _datalen;
}

align(1) struct HalWriteReq {
  ulong    _address;
  uint     _datalen;
  ubyte[1] _data;
}

align(1) struct HalReadRsp {
  ulong    _address;
  uint     _datalen;
  ubyte[4] _options;
  ubyte[1] _data;
}

align(1) struct HalWriteRsp {
  ulong    _address;
  uint     _datalen;
  ubyte[4] _options;
}

align(1) struct HalCommand {
  HalHeader _header;
  union {
    HalReadReq  _readReq;
    HalReadRsp  _readRsp;
    HalWriteReq _writeReq;
    HalWriteRsp _writeRsp;
  }
}
