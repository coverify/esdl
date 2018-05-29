// Copyright: Coverify Systems Technology 2013 - 2016
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.intf.vpi;
import core.vararg;
import core.stdc.string: strlen;
import esdl.base.core: simulateAllRootsUpto, terminateAllRoots;
import esdl.data.time;

version(LDC) {
  import ldc.attributes;
}
 else {
   enum weak;
 }
/******************************** TYPEDEFS ********************************/

static string declareEnums (alias E)()
{
  import std.traits;
  import std.conv;
  string res;
  
  foreach(e; __traits(allMembers, E))
    {
      res ~= "enum " ~ E.stringof ~ " " ~ e ~ " = " ~
	E.stringof ~ "." ~ e ~ ";\n";
    }
  return res;
}

alias vpiHandle = uint*;

enum vpiObjectTypeT: int {
  vpiAlways = 1, /* always procedure */
  vpiAssignStmt = 2, /* quasi-continuous assignment */
  vpiAssignment = 3, /* procedural assignment */
  vpiBegin = 4, /* block statement */
  vpiCase = 5, /* case statement */
  vpiCaseItem = 6, /* case statement item */
  vpiConstant = 7, /* numerical constant or string literal */
  vpiContAssign = 8, /* continuous assignment */
  vpiDeassign = 9, /* deassignment statement */
  vpiDefParam = 10, /* defparam */
  vpiDelayControl = 11, /* delay statement (e.g., #10) */
  vpiDisable = 12, /* named block disable statement */
  vpiEventControl = 13, /* wait on event, e.g., @e */
  vpiEventStmt = 14, /* event trigger, e.g., ->e */
  vpiFor = 15, /* for statement */
  vpiForce = 16, /* force statement */
  vpiForever = 17, /* forever statement */
  vpiFork = 18, /* fork-join block */
  vpiFuncCall = 19, /* function call */
  vpiFunction = 20, /* function */
  vpiGate = 21, /* primitive gate */
  vpiIf = 22, /* if statement */
  vpiIfElse = 23, /* if–else statement */
  vpiInitial = 24, /* initial procedure */
  vpiIntegerVar = 25, /* integer variable */
  vpiInterModPath = 26, /* intermodule wire delay */
  vpiIterator = 27, /* iterator */
  vpiIODecl = 28, /* input/output declaration */
  vpiMemory = 29, /* behavioral memory */
  vpiMemoryWord = 30, /* single word of memory */
  vpiModPath = 31, /* module path for path delays */
  vpiModule = 32, /* module instance */
  vpiNamedBegin = 33, /* named block statement */
  vpiNamedEvent = 34, /* event variable */
  vpiNamedFork = 35, /* named fork-join block */
  vpiNet = 36, /* scalar or vector net */
  vpiNetBit = 37, /* bit of vector net */
  vpiNullStmt = 38, /* a semicolon. Ie. #10 ; */
  vpiOperation = 39, /* behavioral operation */
  vpiParamAssign = 40, /* module parameter assignment */
  vpiParameter = 41, /* module parameter */
  vpiPartSelect = 42, /* part-select */
  vpiPathTerm = 43, /* terminal of module path */
  vpiPort = 44, /* module port */
  vpiPortBit = 45, /* bit of vector module port */
  vpiPrimTerm = 46, /* primitive terminal */
  vpiRealVar = 47, /* real variable */
  vpiReg = 48, /* scalar or vector reg */
  vpiRegBit = 49, /* bit of vector reg */
  vpiRelease = 50, /* release statement */
  vpiRepeat = 51, /* repeat statement */
  vpiRepeatControl = 52, /* repeat control in an assign stmt */
  vpiSchedEvent = 53, /* vpi_put_value() event */
  vpiSpecParam = 54, /* specparam */
  vpiSwitch = 55, /* transistor switch */
  vpiSysFuncCall = 56, /* system function call */
  vpiSysTaskCall = 57, /* system task call */
  vpiTableEntry = 58, /* UDP state table entry */
  vpiTask = 59, /* task */
  vpiTaskCall = 60, /* task call */
  vpiTchk = 61, /* timing check */
  vpiTchkTerm = 62, /* terminal of timing check */
  vpiTimeVar = 63, /* time variable */
  vpiTimeQueue = 64, /* simulation event queue */
  vpiUdp = 65, /* user-defined primitive */
  vpiUdpDefn = 66, /* UDP definition */
  vpiUserSystf = 67, /* user-defined system task/function */
  vpiVarSelect = 68, /* variable array selection */
  vpiWait = 69, /* wait statement */
  vpiWhile = 70, /* while statement */
  /********************** object types added with 1364-2001 *********************/
  vpiAttribute = 105, /* attribute of an object */
  vpiBitSelect = 106, /* Bit-select of parameter, var select */
  vpiCallback = 107, /* callback object */
  vpiDelayTerm = 108, /* Delay term which is a load or driver */
  vpiDelayDevice = 109, /* Delay object within a net */
  vpiFrame = 110, /* reentrant task/func frame */
  vpiGateArray = 111, /* gate instance array */
  vpiModuleArray = 112, /* module instance array */
  vpiPrimitiveArray = 113, /* vpiprimitiveArray type */
  vpiNetArray = 114, /* multidimensional net */
  vpiRange = 115, /* range declaration */
  vpiRegArray = 116, /* multidimensional reg */
  vpiSwitchArray = 117, /* switch instance array */
  vpiUdpArray = 118, /* UDP instance array */
  vpiContAssignBit = 128, /* Bit of a vector continuous assignment */
  vpiNamedEventArray = 129, /* multidimensional named event */
  /********************** object types added with 1364-2005 *********************/
  vpiIndexedPartSelect = 130, /* Indexed part-select object */
  vpiGenScopeArray = 133, /* array of generated scopes */
  vpiGenScope = 134, /* A generated scope */
  vpiGenVar = 135, /* Object used to instantiate gen scopes */
}

  mixin(declareEnums!vpiObjectTypeT());


enum vpiRelationT: int {
  /*********************************** METHODS **********************************/
  /**************** methods used to traverse 1 to 1 relationships ***************/
  vpiCondition = 71, /* condition expression */
  vpiDelay = 72, /* net or gate delay */
  vpiElseStmt = 73, /* else statement */
  vpiForIncStmt = 74, /* increment statement in for loop */
  vpiForInitStmt = 75, /* initialization statement in for loop */
  vpiHighConn = 76, /* higher connection to port */
  vpiLhs = 77, /* left-hand side of assignment */
  vpiIndex = 78, /* index of var select, bit-select, etc. */
  vpiLeftRange = 79, /* left range of vector or part-select */
  vpiLowConn = 80, /* lower connection to port */
  vpiParent = 81, /* parent object */
  vpiRhs = 82, /* right-hand side of assignment */
  vpiRightRange = 83, /* right range of vector or part-select */
  vpiScope = 84, /* containing scope object */
  vpiSysTfCall = 85, /* task function call */
  vpiTchkDataTerm = 86, /* timing check data term */
  vpiTchkNotifier = 87, /* timing check notifier */
  vpiTchkRefTerm = 88, /* timing check reference term */
  /************* methods used to traverse 1 to many relationships ***************/
  vpiArgument = 89, /* argument to (system) task/function */
  vpiBit = 90, /* bit of vector net or port */
  vpiDriver = 91, /* driver for a net */
  vpiInternalScope = 92, /* internal scope in module */
  vpiLoad = 93, /* load on net or reg */
  vpiModDataPathIn = 94, /* data terminal of a module path */
  vpiModPathIn = 95, /* Input terminal of a module path */
  vpiModPathOut = 96, /* output terminal of a module path */
  vpiOperand = 97, /* operand of expression */
  vpiPortInst = 98, /* connected port instance */
  vpiProcess = 99, /* process in module */
  vpiVariables = 100, /* variables in module */
  vpiUse = 101, /* usage */
  /******** methods which can traverse 1 to 1, or 1 to many relationships *******/
  vpiExpr = 102, /* connected expression */
  vpiPrimitive = 103, /* primitive (gate, switch, UDP) */
  vpiStmt = 104, /* statement in process or task */
  /************************ methods added with 1364-2001 ************************/
  vpiActiveTimeFormat = 119, /* active $timeformat() system task */
  vpiInTerm = 120, /* To get to a delay device's drivers. */
  vpiInstanceArray = 121, /* vpiInstance arrays */
  vpiLocalDriver = 122, /* local drivers (within a module */
  vpiLocalLoad = 123, /* local loads (within a module */
  vpiOutTerm = 124, /* To get to a delay device's loads. */
  vpiPorts = 125, /* Module port */
  vpiSimNet = 126, /* simulated net after collapsing */
  vpiTaskFunc = 127, /* task/function */
  /************************ methods added with 1364-2005 ************************/
  vpiBaseExpr = 131, /* Indexed part-select's base expression */
  vpiWidthExpr = 132, /* Indexed part-select's width expression */
  /************************ methods added with 1800-2009 ************************/
  vpiAutomatics = 136, /* Automatic variables of a frame */
}

  mixin(declareEnums!vpiRelationT());

enum vpiPropertyT: int {
  /********************************* PROPERTIES *********************************/
  /************************** generic object properties *************************/
  vpiUndefined = -1, /* undefined property */
  vpiType = 1, /* type of object */
  vpiName = 2, /* local name of object */
  vpiFullName = 3, /* full hierarchical name */
  vpiSize = 4, /* size of gate, net, port, etc. */
  vpiFile = 5, /* File name in which the object is used*/
  vpiLineNo = 6, /* line number where the object is used */
  /***************************** module properties ******************************/
  vpiTopModule = 7, /* top-level module (Boolean) */
  vpiCellInstance = 8, /* cell (Boolean) */
  vpiDefName = 9, /* module definition name */
  vpiProtected = 10, /* source protected module (Boolean) */
  vpiTimeUnit = 11, /* module time unit */
  vpiTimePrecision = 12, /* module time precision */
  vpiDefNetType = 13, /* default net type */
  vpiUnconnDrive = 14, /* unconnected port drive strength */
  vpiDefFile = 15, /* File name where the module is defined*/
  vpiDefLineNo = 16, /* line number for module definition */
  vpiDefDelayMode = 47, /* Default delay mode for a module */
  vpiDefDecayTime = 48, /* Default decay time for a module */
  /*************************** port and net properties **************************/
  vpiScalar = 17, /* scalar (Boolean) */
  vpiVector = 18, /* vector (Boolean) */
  vpiExplicitName = 19, /* port is explicitly named */
  vpiDirection = 20, /* direction of port: */
  vpiConnByName = 21, /* connected by name (Boolean) */
  vpiNetType = 22, /* net subtypes: */
  vpiExplicitScalared = 23, /* explicitly scalared (Boolean) */
  vpiExplicitVectored = 24, /* explicitly vectored (Boolean) */
  vpiExpanded = 25, /* expanded vector net (Boolean) */
  vpiImplicitDecl = 26, /* implicitly declared net (Boolean) */
  vpiChargeStrength = 27, /* charge decay strength of net */
  /* Defined as part of strengths section.
     #define vpiLargeCharge 0x10
     #define vpiMediumCharge 0x04
     #define vpiSmallCharge 0x02
  */
  vpiArray = 28, /* variable array (Boolean) */
  vpiPortIndex = 29, /* Port index */
  /************************ gate and terminal properties ************************/
  vpiTermIndex = 30, /* Index of a primitive terminal */
  vpiStrength0 = 31, /* 0-strength of net or gate */
  vpiStrength1 = 32, /* 1-strength of net or gate */
  vpiPrimType = 33, /* primitive subtypes: */
  /**************** path, path terminal, timing check properties ****************/
  vpiPolarity = 34, /* polarity of module path... */
  vpiDataPolarity = 35, /* ...or data path: */
  vpiEdge = 36, /* edge type of module path: */
  vpiPathType = 37, /* path delay connection subtypes: */
  vpiTchkType = 38, /* timing check subtypes: */
  /**************************** expression properties ***************************/
  vpiOpType = 39, /* operation subtypes: */
  vpiConstType = 40, /* constant subtypes: */
  vpiBlocking = 41, /* blocking assignment (Boolean) */
  vpiCaseType = 42, /* case statement subtypes: */
  vpiNetDeclAssign = 43, /* assign part of decl (Boolean) */
  /************************** task/function properties **************************/
  vpiFuncType = 44, /* function & system function type */
  vpiSysFuncType = vpiFuncType,
  vpiUserDefn = 45, /*user-defined system task/func(Boolean)*/
  vpiScheduled = 46, /* object still scheduled (Boolean) */
  /*********************** properties added with 1364-2001 **********************/
  vpiActive = 49, /* reentrant task/func frame is active */
  vpiAutomatic = 50, /* task/func obj is automatic */
  vpiCell = 51, /* configuration cell */
  vpiConfig = 52, /* configuration config file */
  vpiConstantSelect = 53, /* (Boolean) bit-select or part-select
			     indices are constant expressions */
  vpiDecompile = 54, /* decompile the object */
  vpiDefAttribute = 55, /* Attribute defined for the obj */
  vpiDelayType = 56, /* delay subtype */
  vpiIteratorType = 57, /* object type of an iterator */
  vpiLibrary = 58, /* configuration library */
  vpiOffset = 60, /* offset from LSB */
  vpiResolvedNetType = 61, /* net subtype after resolution, returns
			      same subtypes as vpiNetType */
  vpiSaveRestartID = 62, /* unique ID for save/restart data */
  vpiSaveRestartLocation = 63, /* name of save/restart data file */
  /* vpiValid,vpiValidTrue,vpiValidFalse were deprecated in 1800-2009 */
  vpiValid = 64, /* reentrant task/func frame or automatic
		    variable is valid */
  vpiSigned = 65, /* TRUE for vpiIODecl and any object in
		     the expression class if the object
		     has the signed attribute */
  vpiLocalParam = 70, /* TRUE when a param is declared as a
			 localparam */
  vpiModPathHasIfNone = 71, /* Mod path has an ifnone statement */
  /*********************** properties added with 1364-2005 **********************/
  vpiIndexedPartSelectType = 72, /* Indexed part-select type */
  vpiIsMemory = 73, /* TRUE for a one-dimensional reg array */
  vpiIsProtected = 74, /* TRUE for protected design information */
}

  mixin(declareEnums!vpiPropertyT());

enum vpiUnconnDriveT: int {
  vpiHighZ = 1, /* No default drive given */
  vpiPull1 = 2, /* default pull1 drive */
  vpiPull0 = 3, /* default pull0 drive */
}

  mixin(declareEnums!vpiUnconnDriveT());

enum vpiDefDelayModeT: int {
  vpiDelayModeNone = 1, /* no delay mode specified */
  vpiDelayModePath = 2, /* path delay mode */
  vpiDelayModeDistrib = 3, /* distributed delay mode */
  vpiDelayModeUnit = 4, /* unit delay mode */
  vpiDelayModeZero = 5, /* zero delay mode */
  vpiDelayModeMTM = 6, /* min:typ:max delay mode */
}

  mixin(declareEnums!vpiDefDelayModeT());

enum vpiDirectionT: int {
  vpiInput = 1, /* input */
  vpiOutput = 2, /* output */
  vpiInout = 3, /* inout */
  vpiMixedIO = 4, /* mixed input-output */
  vpiNoDirection = 5, /* no direction */
}

  mixin(declareEnums!vpiDirectionT());

enum vpiNetTypeT: int {
  vpiWire = 1, /* wire net */
  vpiWand = 2, /* wire-and net */
  vpiWor = 3, /* wire-or net */
  vpiTri = 4, /* tri net */
  vpiTri0 = 5, /* pull-down net */
  vpiTri1 = 6, /* pull-up net */
  vpiTriReg = 7, /* three-state reg net */
  vpiTriAnd = 8, /* three-state wire-and net */
  vpiTriOr = 9, /* three-state wire-or net */
  vpiSupply1 = 10, /* supply-1 net */
  vpiSupply0 = 11, /* supply-0 net */
  vpiNone = 12, /* no default net type (1364-2001) */
  vpiUwire = 13, /* unresolved wire net (1364-2005) */
}

  mixin(declareEnums!vpiNetTypeT());

enum vpiPrimTypeT: int {
  vpiAndPrim = 1, /* and gate */
  vpiNandPrim = 2, /* nand gate */
  vpiNorPrim = 3, /* nor gate */
  vpiOrPrim = 4, /* or gate */
  vpiXorPrim = 5, /* xor gate */
  vpiXnorPrim = 6, /* xnor gate */
  vpiBufPrim = 7, /* buffer */
  vpiNotPrim = 8, /* not gate */
  vpiBufif0Prim = 9, /* zero-enabled buffer */
  vpiBufif1Prim = 10, /* one-enabled buffer */
  vpiNotif0Prim = 11, /* zero-enabled not gate */
  vpiNotif1Prim = 12, /* one-enabled not gate */
  vpiNmosPrim = 13, /* nmos switch */
  vpiPmosPrim = 14, /* pmos switch */
  vpiCmosPrim = 15, /* cmos switch */
  vpiRnmosPrim = 16, /* resistive nmos switch */
  vpiRpmosPrim = 17, /* resistive pmos switch */
  vpiRcmosPrim = 18, /* resistive cmos switch */
  vpiRtranPrim = 19, /* resistive bidirectional */
  vpiRtranif0Prim = 20, /* zero-enable resistive bidirectional */
  vpiRtranif1Prim = 21, /* one-enable resistive bidirectional */
  vpiTranPrim = 22, /* bidirectional */
  vpiTranif0Prim = 23, /* zero-enabled bidirectional */
  vpiTranif1Prim = 24, /* one-enabled bidirectional */
  vpiPullupPrim = 25, /* pullup */
  vpiPulldownPrim = 26, /* pulldown */
  vpiSeqPrim = 27, /* sequential UDP */
  vpiCombPrim = 28, /* combinational UDP */
}

  mixin(declareEnums!vpiPrimTypeT());

enum vpiDataPolarityT: int {
  vpiPositive = 1, /* positive */
  vpiNegative = 2, /* negative */
  vpiUnknown = 3, /* unknown (unspecified) */
}

  mixin(declareEnums!vpiDataPolarityT());

enum vpiEdgeT: int {
  vpiNoEdge = 0x00, /* no edge */
  vpiEdge01 = 0x01, /* 0 -> 1 */
  vpiEdge10 = 0x02, /* 1 -> 0 */
  vpiEdge0x = 0x04, /* 0 -> x */
  vpiEdgex1 = 0x08, /* x -> 1 */
  vpiEdge1x = 0x10, /* 1 -> x */
  vpiEdgex0 = 0x20, /* x -> 0 */
  vpiPosedge = (vpiEdgex1 | vpiEdge01 | vpiEdge0x),
  vpiNegedge = (vpiEdgex0 | vpiEdge10 | vpiEdge1x),
  vpiAnyEdge = (vpiPosedge | vpiNegedge),
}

  mixin(declareEnums!vpiEdgeT());

enum vpiPathTypeT: int {
  vpiPathFull = 1, /* ( a *> b ) */
  vpiPathParallel = 2, /* ( a => b ) */
}

  mixin(declareEnums!vpiPathTypeT());

enum vpiTchkTypeT: int {
  vpiSetup = 1, /* $setup */
  vpiHold = 2, /* $hold */
  vpiPeriod = 3, /* $period */
  vpiWidth = 4, /* $width */
  vpiSkew = 5, /* $skew */
  vpiRecovery = 6, /* $recovery */
  vpiNoChange = 7, /* $nochange */
  vpiSetupHold = 8, /* $setuphold */
  vpiFullskew = 9, /* $fullskew -- added for 1364-2001 */
  vpiRecrem = 10, /* $recrem -- added for 1364-2001 */
  vpiRemoval = 11, /* $removal -- added for 1364-2001 */
  vpiTimeskew = 12, /* $timeskew -- added for 1364-2001 */
}

  mixin(declareEnums!vpiTchkTypeT());

enum vpiOpTypeT: int {
  vpiMinusOp = 1, /* unary minus */
  vpiPlusOp = 2, /* unary plus */
  vpiNotOp = 3, /* unary not */
  vpiBitNegOp = 4, /* bitwise negation */
  vpiUnaryAndOp = 5, /* bitwise reduction AND */
  vpiUnaryNandOp = 6, /* bitwise reduction NAND */
  vpiUnaryOrOp = 7, /* bitwise reduction OR */
  vpiUnaryNorOp = 8, /* bitwise reduction NOR */
  vpiUnaryXorOp = 9, /* bitwise reduction XOR */
  vpiUnaryXNorOp = 10, /* bitwise reduction XNOR */
  vpiSubOp = 11, /* binary subtraction */
  vpiDivOp = 12, /* binary division */
  vpiModOp = 13, /* binary modulus */
  vpiEqOp = 14, /* binary equality */
  vpiNeqOp = 15, /* binary inequality */
  vpiCaseEqOp = 16, /* case (x and z) equality */
  vpiCaseNeqOp = 17, /* case inequality */
  vpiGtOp = 18, /* binary greater than */
  vpiGeOp = 19, /* binary greater than or equal */
  vpiLtOp = 20, /* binary less than */
  vpiLeOp = 21, /* binary less than or equal */
  vpiLShiftOp = 22, /* binary left shift */
  vpiRShiftOp = 23, /* binary right shift */
  vpiAddOp = 24, /* binary addition */
  vpiMultOp = 25, /* binary multiplication */
  vpiLogAndOp = 26, /* binary logical AND */
  vpiLogOrOp = 27, /* binary logical OR */
  vpiBitAndOp = 28, /* binary bitwise AND */
  vpiBitOrOp = 29, /* binary bitwise OR */
  vpiBitXorOp = 30, /* binary bitwise XOR */
  vpiBitXNorOp = 31, /* binary bitwise XNOR */
  vpiBitXnorOp = vpiBitXNorOp, /* added with 1364-2001 */
  vpiConditionOp = 32, /* ternary conditional */
  vpiConcatOp = 33, /* n-ary concatenation */
  vpiMultiConcatOp = 34, /* repeated concatenation */
  vpiEventOrOp = 35, /* event OR */
  vpiNullOp = 36, /* null operation */
  vpiListOp = 37, /* list of expressions */
  vpiMinTypMaxOp = 38, /* min:typ:max: delay expression */
  vpiPosedgeOp = 39, /* posedge */
  vpiNegedgeOp = 40, /* negedge */
  vpiArithLShiftOp = 41, /* arithmetic left shift (1364-2001) */
  vpiArithRShiftOp = 42, /* arithmetic right shift (1364-2001) */
  vpiPowerOp = 43, /* arithmetic power op (1364-2001) */
}

  mixin(declareEnums!vpiOpTypeT());

enum vpiConstTypeT: int {
  vpiDecConst = 1, /* decimal integer */
  vpiRealConst = 2, /* real */
  vpiBinaryConst = 3, /* binary integer */
  vpiOctConst = 4, /* octal integer */
  vpiHexConst = 5, /* hexadecimal integer */
  vpiStringConst = 6, /* string literal */
  vpiIntConst = 7, /* integer constant (1364-2001) */
  vpiTimeConst = 8, /* time constant */
}

  mixin(declareEnums!vpiConstTypeT());

enum vpiCaseTypeT: int {
  vpiCaseExact = 1, /* exact match */
  vpiCaseX = 2, /* ignore X's */
  vpiCaseZ = 3, /* ignore Z's */
}

  mixin(declareEnums!vpiCaseTypeT());

enum vpiFuncTypeT: int {
  vpiIntFunc = 1, /* returns integer */
  vpiRealFunc = 2, /* returns real */
  vpiTimeFunc = 3, /* returns time */
  vpiSizedFunc = 4, /* returns an arbitrary size */
  vpiSizedSignedFunc = 5, /* returns sized signed value */
  /** alias 1364-1995 system function subtypes to 1364-2001 function subtypes ***/
  vpiSysFuncInt = vpiIntFunc,
  vpiSysFuncReal = vpiRealFunc,
  vpiSysFuncTime = vpiTimeFunc,
  vpiSysFuncSized = vpiSizedFunc,
}

  mixin(declareEnums!vpiFuncTypeT());

enum vpiDelayTypeT: int {
  vpiModPathDelay = 1, /* module path delay */
  vpiInterModPathDelay = 2, /* intermodule path delay */
  vpiMIPDelay = 3, /* module input port delay */
}

  mixin(declareEnums!vpiDelayTypeT());

enum vpiValidT: int {
  vpiValidFalse = 0,
  vpiValidTrue = 1,
}

  mixin(declareEnums!vpiValidT());

enum vpiIndexedPartSelectTypeT: int {
  vpiPosIndexed = 1, /* +: */
  vpiNegIndexed = 2, /* -: */
}

  mixin(declareEnums!vpiIndexedPartSelectTypeT());

enum vpiControlTypeT: int {
  vpiStop = 66, /* execute simulator's $stop */
  vpiFinish = 67, /* execute simulator's $finish */
  vpiReset = 68, /* execute simulator's $reset */
  vpiSetInteractiveScope = 69, /* set simulator's interactive scope */
}

  mixin(declareEnums!vpiControlTypeT());

/************************** I/O related defines ***************************/
enum int VPI_MCD_STDOUT=0x00000001;

/************************** STRUCTURE DEFINITIONS *************************/

/***************************** time structure *****************************/
struct s_vpi_time
{
  int type;               /* [vpiScaledRealTime, vpiSimTime,
			     vpiSuppressTime] */
  uint high, low;          /* for vpiSimTime */
  double floating;               /* for vpiScaledRealTime */
}

  alias s_vpi_time* p_vpi_time;

/* time types */
enum vpiTimeTypeT: int {
  vpiScaledRealTime = 1,
  vpiSimTime = 2,
  vpiSuppressTime = 3,
}

  mixin(declareEnums!vpiTimeTypeT());

/**************************** delay structures ****************************/
struct s_vpi_delay
{
  s_vpi_time *da; /* pointer to application-allocated
		     array of delay values */
  int no_of_delays; /* number of delays */
  int time_type; /* [vpiScaledRealTime, vpiSimTime,
		    vpiSuppressTime] */
  int mtm_flag; /* true for mtm values */
  int append_flag; /* true for append */
  int pulsere_flag; /* true for pulsere values */
}

  alias s_vpi_delay* p_vpi_delay;

/**************************** value structures ****************************/
/* vector value */

struct s_vpi_vecval
{
  /* following fields are repeated enough times to contain vector */
  uint aval, bval; /* bit encoding: ab: 00=0, 10=1, 11=X, 01=Z */
}

  alias s_vpi_vecval* p_vpi_vecval;

/* strength (scalar) value */
struct s_vpi_strengthval
{
  int logic; /* vpi[0,1,X,Z] */
  int s0, s1; /* refer to strength coding below */
}

  alias s_vpi_strengthval* p_vpi_strengthval;

enum vpiStrengthT: int {
  /* strength values */
  vpiSupplyDrive = 0x80,
  vpiStrongDrive = 0x40,
  vpiPullDrive = 0x20,
  vpiWeakDrive = 0x08,
  vpiLargeCharge = 0x10,
  vpiMediumCharge = 0x04,
  vpiSmallCharge = 0x02,
  vpiHiZ = 0x01,
}

  mixin(declareEnums!vpiStrengthT());

/* generic value */
struct s_vpi_value
{
  vpiValueFormatT format; /* vpi[[Bin,Oct,Dec,Hex]Str,Scalar,Int,Real,String,
			     Vector,Strength,Suppress,Time,ObjType]Val */
  union U
  {
    char *str; /* string value */
    int scalar; /* vpi[0,1,X,Z] */
    int integer; /* integer value */
    double floating; /* real value */
    s_vpi_time *time; /* time value */
    s_vpi_vecval *vector; /* vector value */
    s_vpi_strengthval *strength; /* strength value */
    char *misc; /* ...other */
  }
    U value;
}
  alias s_vpi_value* p_vpi_value;

struct s_vpi_arrayvalue
{
  uint format; /* vpi[Int,Real,Time,ShortInt,LongInt,ShortReal,
		  RawTwoState,RawFourState]Val */
  uint flags; /* array bit flags- vpiUserAllocFlag */
  union U
  {
    int *integers; /* integer values */
    short *shortints; /* short integer values */
    long *longints; /* long integer values */
    char *rawvals; /* 2/4-state vector elements */
    s_vpi_vecval *vectors; /* 4-state vector elements */
    s_vpi_time *times; /* time values */
    double *foltings; /* real values */
    float *shortreals; /* short real values */
  }
    U value;
}

  alias s_vpi_arrayvalue* p_vpi_arrayvalue;

enum vpiValueFormatT: int {
  /* value formats */
  vpiBinStrVal = 1,
  vpiOctStrVal = 2,
  vpiDecStrVal = 3,
  vpiHexStrVal = 4,
  vpiScalarVal = 5,
  vpiIntVal = 6,
  vpiRealVal = 7,
  vpiStringVal = 8,
  vpiVectorVal = 9,
  vpiStrengthVal = 10,
  vpiTimeVal = 11,
  vpiObjTypeVal = 12,
  vpiSuppressVal = 13,
  vpiShortIntVal = 14,
  vpiLongIntVal = 15,
  vpiShortRealVal = 16,
  vpiRawTwoStateVal = 17,
  vpiRawFourStateVal = 18,
}

  mixin(declareEnums!vpiValueFormatT());

enum vpiFlagsTypeT: int {
  /* force and release flags */
  vpiNoDelay = 1,
  vpiInertialDelay = 2,
  vpiTransportDelay = 3,
  vpiPureTransportDelay = 4,
  vpiForceFlag = 5,
  vpiReleaseFlag = 6,
  /* scheduled event cancel flag */
  vpiCancelEvent = 7,
  /* bit mask for the flags argument to vpi_put_value() */
  vpiReturnEvent = 0x1000,
  /* bit flags for vpi_get_value_array flags field */
  vpiUserAllocFlag = 0x2000,
  /* bit flags for vpi_put_value_array flags field */
  vpiOneValue = 0x4000,
  vpiPropagateOff = 0x8000,
}

  mixin(declareEnums!vpiFlagsTypeT());

enum vpiScalarValueT: int {
  /* scalar values */
  vpi0 = 0,
  vpi1 = 1,
  vpiZ = 2,
  vpiX = 3,
  vpiH = 4,
  vpiL = 5,
  vpiDontCare = 6,
  vpiUnChanged = 7,		// vpiNoChange
  /*
    #define vpiNoChange 7 Defined under vpiTchkType, but
    can be used here.
  */
}

  mixin(declareEnums!vpiScalarValueT());

/*********************** system task/function structure ***********************/
struct s_vpi_systf_data
{
  int type; /* vpiSysTask, vpiSysFunc */
  int sysfunctype; /* vpiSysTask, vpi[Int,Real,Time,Sized,
		      SizedSigned]Func */
  char *tfname; /* first character must be '$' */
  // int (*calltf)(char *);
  // int (*compiletf)(char *);
  // int (*sizetf)(char *); /* for sized function callbacks only */
  int function(char*) calltf;
  int function(char*) compiletf;
  int function(char*) sizetf;
  void *user_data;		// char* in vpi_user.h
}

  alias s_vpi_systf_data* p_vpi_systf_data;

enum vpiTaskOrFuncT: int {
  vpiSysTask = 1,
  vpiSysFunc = 2,
}

  mixin(declareEnums!vpiTaskOrFuncT());

/* the subtypes are defined under the vpiFuncType property */

/************* SystemVerilog execution information structure **************/

struct s_vpi_vlog_info
{
  int argc;
  char **argv;
  char *product;
  char *product_version;
}

  alias s_vpi_vlog_info* p_vpi_vlog_info;

/******************** PLI error information structure *********************/
struct s_vpi_error_info
{
  int state; /* vpi[Compile,PLI,Run] */
  int level; /* vpi[Notice,Warning,Error,System,Internal] */
  char *message;
  char *product;
  char *code;
  char *file;
  int line;
}
  alias s_vpi_error_info* p_vpi_error_info;

enum vpiErrorStateT: int {
  /* state when error occurred */
  vpiCompile = 1,
  vpiPLI = 2,
  vpiRun = 3,
}

  mixin(declareEnums!vpiErrorStateT());

/* error severity levels */
enum vpiErrorSeverityLevelT: int {
  vpiNotice = 1,
  vpiWarning = 2,
  vpiError = 3,
  vpiSystem = 4,
  vpiInternal = 5,
}

  mixin(declareEnums!vpiErrorSeverityLevelT());

/************************** callback structures ***************************/

/* normal callback structure */

struct s_cb_data
{
  vpiCbReasonT reason; /* callback reason */
  // int (*cb_rtn)(s_cb_data *); /* call routine */
  int function(s_cb_data *) cb_rtn;
  vpiHandle obj; /* trigger object */
  p_vpi_time time; /* callback time */
  p_vpi_value value; /* trigger object value */
  int index; /* index of the memory word or
		var select that changed */
  void *user_data;		// char* in vpi_user.h
}

  alias s_cb_data* p_cb_data;

enum vpiCbReasonT: int {
  /****************************** CALLBACK REASONS ******************************/
  /***************************** Simulation related *****************************/
  vpiCbValueChange = 1,
  vpiCbStmt = 2,
  vpiCbForce = 3,
  vpiCbRelease = 4,
  /******************************** Time related ********************************/
  vpiCbAtStartOfSimTime = 5,
  vpiCbReadWriteSynch = 6,
  vpiCbReadOnlySynch = 7,
  vpiCbNextSimTime = 8,
  vpiCbAfterDelay = 9,
  /******************************* Action related *******************************/
  vpiCbEndOfCompile = 10,
  vpiCbStartOfSimulation = 11,
  vpiCbEndOfSimulation = 12,
  vpiCbError = 13,
  vpiCbTchkViolation = 14,
  vpiCbStartOfSave = 15,
  vpiCbEndOfSave = 16,
  vpiCbStartOfRestart = 17,
  vpiCbEndOfRestart = 18,
  vpiCbStartOfReset = 19,
  vpiCbEndOfReset = 20,
  vpiCbEnterInteractive = 21,
  vpiCbExitInteractive = 22,
  vpiCbInteractiveScopeChange = 23,
  vpiCbUnresolvedSystf = 24,
  /**************************** Added with 1364-2001 ****************************/
  vpiCbAssign = 25,
  vpiCbDeassign = 26,
  vpiCbDisable = 27,
  vpiCbPLIError = 28,
  vpiCbSignal = 29,
  /**************************** Added with 1364-2005 ****************************/
  vpiCbNBASynch = 30,
  vpiCbAtEndOfSimTime = 31,
}

  mixin(declareEnums!vpiCbReasonT());

/************************* FUNCTION DECLARATIONS **************************/

/* Include compatibility mode macro definitions. */
/* ---------------------------------------------------------------- */
/* @TODO :: To uncomment when VCS is ready with vpi_compatibility.h */
/*          funtionality                                            */
/* #include "vpi_compatibility.h"                                   */
/* ---------------------------------------------------------------- */

/* callback related */
@weak extern(C) vpiHandle vpi_register_cb (p_cb_data cb_data_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_remove_cb (vpiHandle cb_obj) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) void vpi_get_cb_info (vpiHandle object, p_cb_data cb_data_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) vpiHandle vpi_register_systf (p_vpi_systf_data systf_data_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) void vpi_get_systf_info (vpiHandle object,
				   p_vpi_systf_data systf_data_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

/* for obtaining handles */
@weak extern(C) vpiHandle vpi_handle_by_name (char *name, vpiHandle scope_handle) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}
  
vpiHandle vpiGetHandleByName (string name, vpiHandle scope_handle) {
  import std.string;
  char* cstr = cast(char*) name.toStringz();
  return vpi_handle_by_name(cstr, scope_handle);
}

@weak extern(C) vpiHandle vpi_handle_by_index (vpiHandle object, int indx) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

/* for traversing relationships */
@weak extern(C) vpiHandle vpi_handle (int type, vpiHandle refHandle) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) vpiHandle vpi_handle_multi (int type, vpiHandle refHandle1,
				      vpiHandle refHandle2, ... ) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) vpiHandle vpi_iterate (int type, vpiHandle refHandle) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) vpiHandle vpi_scan (vpiHandle iterator) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

/* for processing properties */
@weak extern(C) int vpi_get (int property, vpiHandle object) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) long vpi_get64 (int property, vpiHandle object) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) char *vpi_get_str (int property, vpiHandle object) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

string vpiGetStr(vpiPropertyT prop, vpiHandle obj) {
  import std.conv;
  auto cstr = vpi_get_str(prop, obj);
  return cstr.to!string;
}

/* delay processing */
@weak extern(C) void vpi_get_delays (vpiHandle object, p_vpi_delay delay_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) void vpi_put_delays (vpiHandle object, p_vpi_delay delay_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

/* value processing */
@weak extern(C) void vpi_get_value (vpiHandle expr, p_vpi_value value_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) vpiHandle vpi_put_value (vpiHandle object, p_vpi_value value_p,
				   p_vpi_time time_p, vpiFlagsTypeT flags) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) void vpi_get_value_array (vpiHandle object,
				    p_vpi_arrayvalue arrayvalue_p,
				    int *index_p, uint num) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) void vpi_put_value_array (vpiHandle object,
				    p_vpi_arrayvalue arrayvalue_p,
				    int *index_p, uint num) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

/* time processing */
@weak extern(C) void vpi_get_time (vpiHandle object, p_vpi_time time_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

/* I/O routines */
@weak extern(C) uint vpi_mcd_open (char *fileName) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) uint vpi_mcd_close (uint mcd) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) char *vpi_mcd_name (uint cd) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}
// TBD

@weak extern(C) int vpi_mcd_printf (uint mcd, char *format, ...) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}
// TBD

@weak extern(C) int vpi_printf (char *format, ...) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}
// TBD

/* utility routines */
@weak extern(C) int vpi_compare_objects (vpiHandle object1, vpiHandle object2) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_chk_error (p_vpi_error_info error_info_p) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_configure (int item, char *value) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

/* vpi_free_object() is deprecated in 1800-2009 */
@weak extern(C) int vpi_free_object (vpiHandle object) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_release_handle (vpiHandle object) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_get_vlog_info (p_vpi_vlog_info vlog_info_p) {
  import std.string;
  vlog_info_p.argc = 0;
  vlog_info_p.argv = null;
  vlog_info_p.product = cast(char*) "Vlang".toStringz();
  vlog_info_p.product_version = cast(char*) "void".toStringz();
  return false;	     // dummy function and hence returns false
}

string vpiGetProduct() {
  import std.string;
  s_vpi_vlog_info info;
  vpi_get_vlog_info(&info);
  return cast(string) fromStringz(info.product);
}

string vpiGetProductVersion() {
  import std.string;
  s_vpi_vlog_info info;
  vpi_get_vlog_info(&info);
  return cast(string) fromStringz(info.product_version);
}
  
bool vpiIsUsable() {
  static bool _isUsable = false;
  static bool _init = true;
  if(_init) {
    s_vpi_vlog_info info;
    auto status = vpi_get_vlog_info(&info);
    if(status) {
      _isUsable = true;
    }
    else {
      import std.stdio;
      stderr.writeln("vpi_get_vlog_info is returning false");
      _isUsable = false;
    }
    _init = false;
  }
  return _isUsable;
}
  
/* routines added with 1364-2001 */
@weak extern(C) int vpi_get_data (int id, char *dataLoc, int numOfBytes) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_put_data (int id, char *dataLoc, int numOfBytes) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) void *vpi_get_userdata (vpiHandle obj) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_put_userdata (vpiHandle obj, void *userdata) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

// extern(C) int vpi_vprintf (char *format, va_list ap) {
//   assert(false, "Kindly link to a Verilog compiler that supports VPI");
// }
// extern(C) int vpi_mcd_vprintf (uint mcd, char *format, va_list ap) {
//   assert(false, "Kindly link to a Verilog compiler that supports VPI");
// }
@weak extern(C) int vpi_flush () {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_mcd_flush (uint mcd) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) int vpi_control (int operation, ...) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}

@weak extern(C) vpiHandle vpi_handle_by_multi_index (vpiHandle obj, int num_index,
					       int *index_array) {
  assert(false, "Kindly link to a Verilog compiler that supports VPI");
}


/**************************** GLOBAL VARIABLES ****************************/
// extern void (**vlog_startup_routines)()
// extern void function() *vlog_startup_routines;
alias vpi_thunk = void function();

// @weak shared extern(C) vpi_thunk* vlog_startup_routines;

/* array of function pointers, last pointer should be null */

// Meta Functions
void vpiGetValue(T)(vpiHandle handle, ref T t) {
  import esdl.data.bvec;
  s_vpi_value val;
  import std.traits; // isIntegral
  import std.conv;
  static if(isIntegral!T) {
    uint size = vpi_get(vpiPropertyT.vpiSize, handle);
    auto hname = vpi_get_str(vpiFullName, handle);
    assert(size == T.sizeof*8,
	   hname[0..hname.strlen] ~ " is " ~ size.to!string() ~
	   " long; vpiPutValue received a Integer of size: " ~
	   T.sizeof.stringof ~ "(bytes)\n");
    static if(T.sizeof <= 32) {
      val.format = vpiIntVal;
      vpi_get_value(handle, &val);
      t = cast(T) val.value.integer;
    }
    else {
      alias TT = _bvec!T;
      enum VECLEN = T.sizeof / 4;
      s_vpi_vecval[VECLEN] vecval;
      val.format = vpiVectorVal;
      val.value.vector = vecval.ptr;
      vpi_get_value(handle, &val);
      TT tt = vecval;
      t = tt;
    }
  }
  else static if(is(T: bool)) {
    uint size = vpi_get(vpiPropertyT.vpiSize, handle);
    auto hname = vpi_get_str(vpiFullName, handle);
    assert(size == 1,
	   hname[0..hname.strlen] ~ " is " ~ size.to!string() ~
	   " long; vpiPutValue received a BitVector of size: 1"
	   ~ "\n");
    val.format = vpiScalarVal;
    vpi_get_value(handle, &val);
    if(val.value.scalar == 0) {
      t = false;
    }
    else {
      t = true;
    }
  }
  else static if(isBitVector!T) {
    uint size = vpi_get(vpiPropertyT.vpiSize, handle);
    auto hname = vpi_get_str(vpiFullName, handle);
    assert(size == T.SIZE,
	   hname[0..hname.strlen] ~ " is " ~ size.to!string() ~
	   " long; vpiPutValue received a BitVector of size: " ~
	   T.SIZE.stringof ~ "\n");
    enum VECLEN = (T.SIZE+31)/32;
    s_vpi_vecval[VECLEN] vecval;
    val.format = vpiVectorVal;
    val.value.vector = vecval.ptr;
    vpi_get_value(handle, &val);
    t = vecval;
  }
  else {
    static assert(false, "vpiGetValue not yet implemented for type: " ~
		  T.stringof);
  }
}

void vpiPutValue(T)(vpiHandle handle, T t,
		    vpiFlagsTypeT flag = vpiNoDelay) {
  import esdl.data.bvec;
  s_vpi_value val;
  import std.traits; // isIntegral
  import std.conv;
  static if(isIntegral!T) {
    uint size = vpi_get(vpiPropertyT.vpiSize, handle);
    auto hname = vpi_get_str(vpiFullName, handle);
    assert(size == T.sizeof*8,
	   hname[0..hname.strlen] ~ " is " ~ size.to!string() ~
	   " long; vpiPutValue received a BitVector of size: " ~
	   T.sizeof.stringof ~ "(bytes)\n");
    static if(T.sizeof <= 32) {
      val.format = vpiIntVal;
      val.value.integer = t;
      vpi_put_value(handle, &val, null, flag);
    }
    else {
      alias TT = _bvec!T;
      enum VECLEN = T.sizeof / 4;
      s_vpi_vecval[VECLEN] vecval;
      TT tt = t;
      tt.toVpiVecValue(vecval);
      val.format = vpiVectorVal;
      val.value.vector = vecval.ptr;
      vpi_put_value(handle, &val, null, vpiNoDelay);
    }
  }
  else static if(is(T: bool)) {
    uint size = vpi_get(vpiPropertyT.vpiSize, handle);
    // auto hname = vpi_get_str(vpiFullName, handle);
    assert(size == 1,
	   "Mismatch:  " ~ size.to!string() ~
	   " long; vpiPutValue received a BitVector of size: 1"
	   ~ "\n");
    val.format = vpiScalarVal;
    val.value.scalar = t;
    vpi_put_value(handle, &val, null, vpiNoDelay);
  }
  else static if(isBitVector!T) {
    uint size = vpi_get(vpiPropertyT.vpiSize, handle);
    auto hname = vpi_get_str(vpiFullName, handle);
    assert(size == T.SIZE,
	   hname[0..hname.strlen] ~ " is " ~ size.to!string() ~
	   " long; vpiPutValue received a BitVector of size: " ~
	   T.SIZE.stringof ~ "\n");
    enum VECLEN = (T.SIZE+31)/32;
    s_vpi_vecval[VECLEN] vecval;
    t.toVpiVecValue(vecval);
    val.format = vpiVectorVal;
    val.value.vector = vecval.ptr;
    vpi_put_value(handle, &val, null, vpiNoDelay);
  }
  else {
    static assert(false, "vpiPutValue not yet implemented for type: " ~
		  T.stringof);
  }
}
  
private void vpiGetNextValue(T)(vpiHandle iter, ref T t) {
  vpiHandle handle = vpi_scan(iter);
  assert(handle);
  vpiGetValue(handle, t);
}
  
private void vpiPutNextValue(T)(vpiHandle iter, T t,
				vpiFlagsTypeT flag = vpiNoDelay) {
  vpiHandle handle = vpi_scan(iter);
  assert(handle);
  vpiPutValue(handle, t, flag);
}

private void vpiGetValuesByOne(U, T...)(vpiHandle iter, ref U u, ref T t) {
  vpiGetNextValue(iter, u);
  static if(T.length > 0) {
    vpiGetValuesByOne(iter, t[0], t[1..$]);
  }
}

void vpiGetValues(T...)(vpiHandle iter, ref T t) {
  static if(T.length > 0) {
    vpiGetValuesByOne(iter, t[0], t[1..$]);
  }
}

private void vpiPutValuesByOne(U, T...)(vpiHandle iter, U u, T t) {
  vpiPutNextValue(iter, u, vpiNoDelay);
  static if(T.length > 0) {
    vpiPutValuesByOne(iter, t[0], t[1..$]);
  }
}

void vpiPutValues(T...)(vpiHandle iter, T t) {
  static if(T.length > 0) {
    vpiPutValuesByOne(iter, t[0], t[1..$]);
  }
}

struct Vpi {
  static void startCosim() {
    auto new_cb = new s_cb_data();
    
    new_cb.reason = vpiCbStartOfSimulation;
    new_cb.cb_rtn = &cbStartCosim;
    vpi_register_cb(new_cb);

    auto end_cb = new s_cb_data();
    end_cb.reason = vpiCbEndOfSimulation;
    end_cb.cb_rtn = &terminateESDL;//next callback address
    vpi_register_cb(end_cb);
  }

  static int cbNextSimTime(p_cb_data cb) {
    s_vpi_time  now;
    now.type = vpiSimTime;
    vpi_get_time(null, &now);
    long time = now.high;
    time <<= 32;
    time += now.low;

    // import std.stdio;

    // writeln("vpiCbNextSimTimeProc: Running simulation till ", time);
    simulateAllRootsUpto(time.psec);

    // writeln("Done simulation till ", time);

    auto new_cb = new s_cb_data();
    new_cb.reason = vpiCbReadOnlySynch;
    new_cb.cb_rtn = &cbReadOnlySynch;//next callback address
    new_cb.time = &now;
    new_cb.obj = null;
    new_cb.value = null;
    new_cb.user_data = null;
    vpi_register_cb(new_cb);
    return 0;
  }

  static int cbReadOnlySynch(p_cb_data cb) {
    s_vpi_time  now;
    now.type = vpiSimTime;
    vpi_get_time(null, &now);
    long time = now.high;
    time <<= 32;
    time += now.low;

    // writeln("callback_cbReadOnlySync: Running simulation till ", time);
    simulateAllRootsUpto(time.psec);

    auto new_cb = new s_cb_data();
    new_cb.reason = vpiCbNextSimTime;
    new_cb.cb_rtn = &cbNextSimTime;
    new_cb.time = null;
    new_cb.obj = null;
    new_cb.value = null;
    new_cb.user_data = null;
    vpi_register_cb(new_cb);
    return 0;
  }

  static int cbStartCosim(p_cb_data cb) {
    import std.random: uniform;
    s_vpi_time  now;
    now.type = vpiSimTime;
    vpi_get_time(null, &now);
    long time = now.high;
    time <<= 32;
    time += now.low;

    simulateAllRootsUpto(time.nsec);

    auto new_cb = new s_cb_data();
    new_cb.reason = vpiCbReadOnlySynch;
    new_cb.cb_rtn = &cbReadOnlySynch;//next callback address
    new_cb.time = &now;
    new_cb.obj = null;
    new_cb.value = null;
    new_cb.user_data = null;
    vpi_register_cb(new_cb);
    return 0;
  }

  static int terminateESDL(p_cb_data cb) {
    terminateAllRoots();
    import core.runtime;  
    Runtime.terminate();
    return 0;
  }

  static void initialize() {
    import core.runtime;
    Runtime.initialize();

    s_cb_data end_cb;
    end_cb.reason = vpiCbEndOfSimulation;
    end_cb.cb_rtn = &finalize;
    vpi_register_cb(&end_cb);
  }

  static int finalize(p_cb_data cb) {
    import core.runtime;
    Runtime.terminate();
    return 0;
  }

  static int getTimeUnit() {
    auto hndl = vpi_handle(vpiScope, vpi_handle(vpiSysTfCall, null));
    return vpi_get(vpiTimeUnit, hndl);
  }
  
  static int getTimePrecision() {
    return vpi_get(vpiTimePrecision, null);
  }

  static ulong getSimTime() {
    s_vpi_time stime;
    stime.type = vpiSimTime;
    vpi_get_time(null, &stime);
    ulong ltime = stime.high;
    ltime = (ltime << 32) + stime.low;
    return ltime;
  }

  static Time getTime() {
    s_vpi_time stime;
    stime.type = vpiSimTime;
    vpi_get_time(null, &stime);
    ulong ltime = stime.high;
    ltime = (ltime << 32) + stime.low;
    Time t = Time(ltime, cast(byte) getTimePrecision());
    return t;
  }
}

enum VpiStatus: int {
    SUCCESS = 0x0,
    FAILURE = 0x1,
    DISABLED = 0x2,
    UNKNOWN = 0x3,
    FINISHED = 0x4
}

void vpiReturnVal(T)(T t) {
  static if (is (T: int)) {
    vpiHandle systf_handle = vpi_handle(vpiSysTfCall, null);
    s_vpi_value value;
    value.format = vpiIntVal;
    value.value.integer = t;
    vpi_put_value(systf_handle, &value, null, vpiNoDelay);
  }
  else {
    static assert ("vpiReturnVal undefined for non int values");
  }
}

void vpi_finish() {
  vpi_control(vpiFinish);
}
