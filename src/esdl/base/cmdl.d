module esdl.base.cmdl;

import esdl.intf.vpi;
import esdl.base.core: getRootEntity;
import std.conv: to;
import std.format;

import std.array: split;

class CommandLine
{
  string[][] _argvs;
  uint _index;

  string[string] [] _plusArgvs;
  string[string] [] _minusArgvs;
  
  string[] _argv;

  string[string] _plusArgv;
  string[string] _minusArgv;
  
  void setOptIndex(uint i) {
    _index = i;
    _argv = _argvs[i];
    _plusArgv = _plusArgvs[i];
    _minusArgv = _minusArgvs[i];
  }

  void initTables() {
    foreach (argv; _argvs) {
      string[string] plusArgv;
      string[string] minusArgv;
      foreach (arg; argv) {
	if (arg[0] == '+') {
	  auto splt = arg[1..$].split("=");
	  if (splt.length == 1) plusArgv[splt[0]] = "";
	  else if (splt.length == 2) plusArgv[splt[0]] = splt[1];
	}
	if (arg[0] == '-') {
	  auto splt = arg[1..$].split("=");
	  if (splt.length == 1) minusArgv[splt[0]] = "";
	  else if (splt.length == 2) minusArgv[splt[0]] = splt[1];
	}
      }
      _plusArgvs ~= plusArgv;
      _minusArgvs ~= minusArgv;
    }
    // import std.stdio;
    // writeln(_plusArgvs);
    // writeln(_minusArgvs);
  }

  this() {
    s_vpi_vlog_info info;
    bool vpiUsable = cast(bool) vpi_get_vlog_info(&info);

    string[] argv;

    auto vlogArgv = info.argv;
    auto vlogArgc = info.argc;
    string[] esdlArgv = getRootEntity().getArgv();

    uint argc;

    if(vpiUsable) {
      argc = vlogArgc;
      if (vlogArgv is null) return;
    }
    else {
      // use the esdl commandline arguments if we are not using Verilog
      // Note that command line arguments have to be passed at the time of
      // RootEntity elaboration
      argc = cast(uint) esdlArgv.length;
    }
  
    for (size_t i=0; i != argc; ++i) {
      string arg;
      if(vpiUsable) {
	char* vlogArg = *(vlogArgv+i);
	arg = (vlogArg++).to!string;
      }
      else {
	arg = esdlArgv[i];
      }

      if(arg == "-f" || arg == "-F") {
	_argvs ~= argv;
	argv.length = 0;
      }
      else {
	argv ~= arg;
      }
    }
    _argvs ~= argv;

    initTables();
    setOptIndex(0);
  }

  this(string[] args) {
    string[] argv;
    foreach (arg; args) {
      if(arg == "-f" || arg == "-F") {
	_argvs ~= argv;
	argv.length = 0;
      }
      else {
	argv ~= arg;
      }
    }
    _argvs ~= argv;

    initTables();
    setOptIndex(0);
  }

  // returns true if argument matches
  bool plusArgs(string fmt) {
    if (fmt in _plusArgv) return true;
    else return false;
  }

  bool plusArgs(R, S...)(string fmt, auto ref R r, auto ref S args) { // at least one scan
    auto spltFmt = fmt.split("=");
    if (spltFmt.length != 2)
      assert (false, "Illegal plusArgs argument: " ~ fmt);

    auto scanFmt = spltFmt[0] in _plusArgv;

    if (scanFmt is null) return false;
    else {
      formattedRead(*scanFmt, spltFmt[1], r, args);
      return true;
    }
  }

  bool minusArgs(R, S...)(string fmt, auto ref R r, auto ref S args) { // at least one scan
    auto spltFmt = fmt.split("=");
    if (spltFmt.length != 2)
      assert (false, "Illegal minusArgs argument: " ~ fmt);

    auto scanFmt = spltFmt[0] in _minusArgv;

    if (scanFmt is null) return false;
    else {
      formattedRead(*scanFmt, spltFmt[1], r, args);
      return true;
    }
  }

  // Due to a bug in formattedRead, these methods are not usable
  // uint matchingArgs(Char, S...) (const(Char)[] fmt,
  // 				auto ref S args) {
  //   uint matched;
  //   foreach (arg; _argv) {
  //     try {
  // 	matched = formattedRead(arg, fmt, args);
  //     }
  //     catch (FormatException e) {
  // 	continue;
  //     }
  //     return matched;
  //   }
  //   return 0;
  // }

  // uint plusArgs(Char, S...) (const(Char)[] fmt,
  // 			    auto ref S args) {
  //   uint matched;
  //   foreach (arg; _argv) {
  //     try {
  // 	matched = formattedRead(arg, "+" ~ fmt, args);
  //     }
  //     catch (FormatException e) {
  // 	continue;
  //     }
  //     return matched;
  //   }
  //   return 0;
  // }

  // uint minusArgs(Char, S...) (const(Char)[] fmt,
  // 			    auto ref S args) {
  //   uint matched;
  //   foreach (arg; _argv) {
  //     try {
  // 	matched = formattedRead(arg, "-" ~ fmt, args);
  //     }
  //     catch (FormatException e) {
  // 	continue;
  //     }
  //     return matched;
  //   }
  //   return 0;
  // }

}
