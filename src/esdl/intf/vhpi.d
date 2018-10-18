// Copyright: Coverify Systems Technology 2013 - 2014
// License:   Distributed under the Boost Software License, Version 1.0.
//            (See accompanying file LICENSE_1_0.txt or copy at
//            http://www.boost.org/LICENSE_1_0.txt)
// Authors:   Puneet Goel <puneet@coverify.com>

module esdl.intf.vhpi;

import core.stdc.stdarg;	// va_list
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

version(LDC) {
  import ldc.attributes;
}
 else {
   enum weak;
 }

alias vhpiHandleT = uint*;
alias vhpiEnumT = uint;
alias vhpiSmallEnumT = ubyte;
alias vhpiIntT = int;
alias vhpiLongIntT = long;
alias vhpiCharT = char;
alias vhpiRealT = double;
alias vhpiSmallPhysT = int;

struct vhpiPhysT
{
  int high;
  uint low;
};

/********************** time structure ****************************/

struct vhpiTimeT
{
  int high;
  uint low;
};

/********************** value structure **************************/

/* value formats */
enum vhpiFormatT
  {   vhpiBinStrVal        = 1, /* do not move */
      vhpiOctStrVal        = 2, /* do not move */
      vhpiDecStrVal        = 3, /* do not move */
      vhpiHexStrVal        = 4, /* do not move */
      vhpiEnumVal          = 5,
      vhpiIntVal           = 6,
      vhpiLogicVal         = 7,
      vhpiRealVal          = 8,
      vhpiStrVal           = 9,
      vhpiCharVal          = 10,
      vhpiTimeVal          = 11,
      vhpiPhysVal          = 12,
      vhpiObjTypeVal       = 13,
      vhpiPtrVal           = 14,
      vhpiEnumVecVal       = 15,
      vhpiIntVecVal        = 16,
      vhpiLogicVecVal      = 17,
      vhpiRealVecVal       = 18,
      vhpiTimeVecVal       = 19,
      vhpiPhysVecVal       = 20,
      vhpiPtrVecVal        = 21,
      vhpiRawDataVal       = 22,
      vhpiSmallEnumVal     = 23,
      vhpiSmallEnumVecVal  = 24,
      vhpiLongIntVal       = 25,
      vhpiLongIntVecVal    = 26,
      vhpiSmallPhysVal     = 27,
      vhpiSmallPhysVecVal  = 28
  };

mixin(declareEnums!vhpiFormatT());
  
/* value structure */
struct vhpiValueT
{
  vhpiFormatT format;  /* vhpi[Char,[Bin,Oct,Dec,Hex]Str,
			  [Small]Enum,Logic,Int,Real,[Small]Phys,Time,Ptr,
			  [Small]EnumVec,LogicVec,IntVect,RealVec,[Small]PhysVec,TimeVec,
			  PtrVec,ObjType,RawData]Val */
  size_t bufSize;  /* the size in bytes of the value buffer; this is set by the user */
  int numElems;
  /* different meanings depending on the format:
     vhpiStrVal, vhpi{Bin...}StrVal: size of string
     array type values: number of array elements
     scalar type values: undefined
  */

  vhpiPhysT unit;
  union ValueT
  {
    vhpiEnumT enumv;
    vhpiEnumT *enumvs;
    vhpiSmallEnumT smallenumv;
    vhpiSmallEnumT *smallenumvs;
    vhpiIntT  intg;
    vhpiIntT *intgs;
    vhpiLongIntT  longintg;
    vhpiLongIntT *longintgs;
    vhpiRealT realv; // in vhpi_user.h real was used, but it is a keyword in D
    vhpiRealT *realvs;
    vhpiSmallPhysT smallphys;
    vhpiSmallPhysT *smallphyss;
    vhpiPhysT phys;
    vhpiPhysT *physs;
    vhpiTimeT time;
    vhpiTimeT *times;
    vhpiCharT ch;
    vhpiCharT *str;
    void *ptr;
    void **ptrs;
  };
  ValueT value;
} /*vhpiValueT*/;

/* Following are the constant definitions. They are divided into
   three major areas:

   1) object types

   2) access methods

   3) properties

*/

enum vhpiUndefined = -1;
  
/*************** OBJECT KINDS *******************/
enum  vhpiClassKindT
  {
   vhpiAccessTypeDeclK           = 1001,
   vhpiAggregateK                = 1002,
   vhpiAliasDeclK                = 1003,
   vhpiAllK                      = 1004,
   vhpiAllocatorK                = 1005,
   vhpiAnyCollectionK            = 1006,
   vhpiArchBodyK                 = 1007,
   vhpiArgvK                     = 1008,
   vhpiArrayTypeDeclK            = 1009,
   DEPRECATED_vhpiAssertStmtK    = 1010,
   vhpiAssocElemK                = 1011,
   vhpiAttrDeclK                 = 1012,
   vhpiAttrSpecK                 = 1013,
   DEPRECATED_vhpiBinaryExprK    = 1014, /* DEPRECATED */
   vhpiBitStringLiteralK         = 1015,
   vhpiBlockConfigK              = 1016,
   vhpiBlockStmtK                = 1017,
   vhpiBranchK                   = 1018,
   vhpiCallbackK                 = 1019,
   vhpiCaseStmtK                 = 1020,
   vhpiCharLiteralK              = 1021,
   vhpiCompConfigK               = 1022,
   vhpiCompDeclK                 = 1023,
   vhpiCompInstStmtK             = 1024,
   vhpiCondSigAssignStmtK        = 1025,
   vhpiCondWaveformK             = 1026,
   vhpiConfigDeclK               = 1027,
   vhpiConstDeclK                = 1028,
   vhpiConstParamDeclK           = 1029,
   vhpiConvFuncK                 = 1030,
   vhpiDeRefObjK                 = 1031,
   vhpiDisconnectSpecK           = 1032,
   vhpiDriverK                   = 1033,
   vhpiDriverCollectionK         = 1034,
   vhpiElemAssocK                = 1035,
   vhpiElemDeclK                 = 1036,
   vhpiEntityClassEntryK         = 1037,
   vhpiEntityDeclK               = 1038,
   vhpiEnumLiteralK              = 1039,
   vhpiEnumRangeK                = 1040,
   vhpiEnumTypeDeclK             = 1041,
   vhpiExitStmtK                 = 1042,
   vhpiFileDeclK                 = 1043,
   vhpiFileParamDeclK            = 1044,
   vhpiFileTypeDeclK             = 1045,
   vhpiFloatRangeK               = 1046,
   vhpiFloatTypeDeclK            = 1047,
   vhpiForGenerateK              = 1048,
   vhpiForLoopK                  = 1049,
   vhpiForeignfK                 = 1050,
   vhpiFuncCallK                 = 1051,
   vhpiFuncDeclK                 = 1052,
   vhpiGenericDeclK              = 1053,
   vhpiGroupDeclK                = 1054,
   vhpiGroupTempDeclK            = 1055,
   vhpiIfGenerateK               = 1056,
   vhpiIfStmtK                   = 1057,
   vhpiInPortK                   = 1058,
   vhpiIndexedNameK              = 1059,
   vhpiIntLiteralK               = 1060,
   vhpiIntRangeK                 = 1061,
   vhpiIntTypeDeclK              = 1062,
   vhpiIteratorK                 = 1063,
   vhpiLibraryDeclK              = 1064,
   DEPRECATED_vhpiLoopStmtK      = 1065,
   vhpiNextStmtK                 = 1066,
   vhpiNullLiteralK              = 1067,
   vhpiNullStmtK                 = 1068,
   DEPRECATED_vhpiOperatorK      = 1069,
   vhpiOthersK                   = 1070,
   vhpiOutPortK                  = 1071,
   vhpiPackBodyK                 = 1072,
   vhpiPackDeclK                 = 1073,
   vhpiPackInstK                 = 1074,
   vhpiParamAttrNameK            = 1075,
   vhpiPhysLiteralK              = 1076,
   vhpiPhysRangeK                = 1077,
   vhpiPhysTypeDeclK             = 1078,
   vhpiPortDeclK                 = 1079,
   DEPRECATED_vhpiProcCallStmtK  = 1080,
   vhpiProcDeclK                 = 1081,
   vhpiProcessStmtK              = 1082,
   DEPRECATED_vhpiProtectedTypeK = 1083,
   vhpiProtectedTypeBodyK        = 1084,
   vhpiProtectedTypeDeclK        = 1085,
   vhpiRealLiteralK              = 1086,
   vhpiRecordTypeDeclK           = 1087,
   vhpiReportStmtK               = 1088,
   vhpiReturnStmtK               = 1089,
   vhpiRootInstK                 = 1090,
   vhpiSelectSigAssignStmtK      = 1091,
   vhpiSelectWaveformK           = 1092,
   vhpiSelectedNameK             = 1093,
   vhpiSigDeclK                  = 1094,
   vhpiSigParamDeclK             = 1095,
   vhpiSimpAttrNameK             = 1096,
   vhpiSimpleSigAssignStmtK      = 1097,
   vhpiSliceNameK                = 1098,
   vhpiStringLiteralK            = 1099,
   vhpiSubpBodyK                 = 1100,
   vhpiSubtypeDeclK              = 1101,
   DEPRECATED_vhpiSubtypeIndicK  = 1102, /* DEPRECATED */
   vhpiToolK                     = 1103,
   vhpiTransactionK              = 1104,
   vhpiTypeConvK                 = 1105,
   DEPRECATED_vhpiUnaryExprK     = 1106, /* DEPRECATED */
   vhpiUnitDeclK                 = 1107,
   vhpiUserAttrNameK             = 1108,
   vhpiVarAssignStmtK            = 1109,
   vhpiVarDeclK                  = 1110,
   vhpiVarParamDeclK             = 1111,
   vhpiWaitStmtK                 = 1112,
   vhpiWaveformElemK             = 1113,
   vhpiWhileLoopK                = 1114,
   vhpiQualifiedExprK            = 1115,
   vhpiUseClauseK                = 1116,
   vhpiConcAssertStmtK           = 1117,
   vhpiConcProcCallStmtK         = 1118,
   vhpiForeverLoopK              = 1119,
   vhpiSeqAssertStmtK            = 1120,
   vhpiSeqProcCallStmtK          = 1121,
   vhpiSeqSigAssignStmtK         = 1122,
   vhpiProtectedTypeInstK        = 1123

  };

mixin(declareEnums!vhpiClassKindT());

/************** methods used to traverse 1 to 1 relationships *******************/
enum  vhpiOneToOneT
  {
   vhpiAbstractLiteral           = 1301,
   vhpiActual                    = 1302,
   vhpiAll                       = 1303,
   vhpiAttrDecl                  = 1304,
   vhpiAttrSpec                  = 1305,
   vhpiBaseType                  = 1306,
   vhpiBaseUnit                  = 1307,
   DEPRECATED_vhpiBasicSignal    = 1308,
   vhpiBlockConfig               = 1309,
   vhpiCaseExpr                  = 1310,
   vhpiCondExpr                  = 1311,
   vhpiConfigDecl                = 1312,
   vhpiConfigSpec                = 1313,
   vhpiConstraint                = 1314,
   vhpiContributor               = 1315,
   vhpiCurCallback               = 1316,
   DEPRECATED_vhpiCurEqProcess   = 1317,
   vhpiCurStackFrame             = 1318,
   vhpiDeRefObj                  = 1319,
   vhpiDecl                      = 1320,
   vhpiDesignUnit                = 1321,
   vhpiDownStack                 = 1322,
   DEPRECATED_vhpiElemSubtype    = 1323, /* DEPRECATED */
   vhpiEntityAspect              = 1324,
   vhpiEntityDecl                = 1325,
   vhpiEqProcessStmt             = 1326,
   vhpiExpr                      = 1327,
   vhpiFormal                    = 1328,
   vhpiFuncDecl                  = 1329,
   vhpiGroupTempDecl             = 1330,
   vhpiGuardExpr                 = 1331,
   vhpiGuardSig                  = 1332,
   vhpiImmRegion                 = 1333,
   vhpiInPort                    = 1334,
   vhpiInitExpr                  = 1335,
   DEPRECATED_vhpiIterScheme     = 1336,
   vhpiLeftExpr                  = 1337,
   vhpiLexicalScope              = 1338,
   vhpiLhsExpr                   = 1339,
   vhpiLocal                     = 1340,
   vhpiLogicalExpr               = 1341,
   DEPRECATED_vhpiName           = 1342,
   DEPRECATED_vhpiOperator       = 1343,
   vhpiOthers                    = 1344,
   vhpiOutPort                   = 1345,
   vhpiParamDecl                 = 1346,
   DEPRECATED_vhpiParamExpr      = 1347,
   vhpiParent                    = 1348,
   vhpiPhysLiteral               = 1349,
   vhpiPrefix                    = 1350,
   vhpiPrimaryUnit               = 1351,
   vhpiProtectedTypeBody         = 1352,
   vhpiProtectedTypeDecl         = 1353,
   vhpiRejectTime                = 1354,
   vhpiReportExpr                = 1355,
   vhpiResolFunc                 = 1356,
   vhpiReturnExpr                = 1357,
   DEPRECATED_vhpiReturnTypeMark = 1358, /* DEPRECATED */
   vhpiRhsExpr                   = 1359,
   vhpiRightExpr                 = 1360,
   vhpiRootInst                  = 1361,
   vhpiSelectExpr                = 1362,
   vhpiSeverityExpr              = 1363,
   vhpiSimpleName                = 1364,
   vhpiSubpBody                  = 1365,
   vhpiSubpDecl                  = 1366,
   DEPRECATED_vhpiSubtype        = 1367, /* DEPRECATED */
   vhpiSuffix                    = 1368,
   vhpiTimeExpr                  = 1369,
   vhpiTimeOutExpr               = 1370,
   vhpiTool                      = 1371,
   vhpiType                      = 1372,
   DEPRECATED_vhpiTypeMark       = 1373, /* DEPRECATED */
   vhpiUnitDecl                  = 1374,
   vhpiUpStack                   = 1375,
   vhpiUpperRegion               = 1376,
   vhpiUse                       = 1377,
   vhpiValExpr                   = 1378,
   DEPRECATED_vhpiValSubtype     = 1379, /* DEPRECATED */
   vhpiElemType                  = 1380,
   vhpiFirstNamedType            = 1381,
   vhpiReturnType                = 1382,
   vhpiValType                   = 1383,
   vhpiCurRegion                 = 1384,
   vhpiSignal                    = 1385,
   vhpiLibraryDecl               = 1386,
   vhpiSimNet                    = 1387,
   vhpiAliasedName               = 1388,
   vhpiCompDecl                  = 1389,
   vhpiProtectedTypeInst         = 1390,
   vhpiGenIndex                  = 1391
  };

mixin(declareEnums!vhpiOneToOneT());
  

/************** methods used to traverse 1 to many relationships *******************/
enum  vhpiOneToManyT
  {
   vhpiAliasDecls                  = 1501,
   vhpiArgvs                       = 1502,
   vhpiAttrDecls                   = 1503,
   vhpiAttrSpecs                   = 1504,
   vhpiBasicSignals                = 1505,
   vhpiBlockStmts                  = 1506,
   vhpiBranchs                     = 1507,
   vhpiCallbacks                   = 1508,
   /* 1508 */
   vhpiChoices                     = 1509,
   vhpiCompInstStmts               = 1510,
   DEPRECATED_vhpiCondExprs        = 1511,
   vhpiCondWaveforms               = 1512,
   vhpiConfigItems                 = 1513,
   vhpiConfigSpecs                 = 1514,
   vhpiConstDecls                  = 1515,
   vhpiConstraints                 = 1516,
   DEPRECATED_vhpiContributors     = 1517,
   // vhpiCurRegions              = 1518,
   /* 1518 */
   vhpiDecls                       = 1519,
   vhpiDepUnits                    = 1520,
   vhpiDesignUnits                 = 1521,
   vhpiDrivenSigs                  = 1522,
   vhpiDrivers                     = 1523,
   vhpiElemAssocs                  = 1524,
   DEPRECATED_vhpiEntityClassEntrys= 1525,
   vhpiEntityDesignators           = 1526,
   vhpiEnumLiterals                = 1527,
   vhpiForeignfs                   = 1528,
   vhpiGenericAssocs               = 1529,
   vhpiGenericDecls                = 1530,
   vhpiIndexExprs                  = 1531,
   vhpiIndexedNames                = 1532,
   vhpiInternalRegions             = 1533,
   vhpiMembers                     = 1534,
   vhpiPackInsts                   = 1535,
   vhpiParamAssocs                 = 1536,
   vhpiParamDecls                  = 1537,
   vhpiPortAssocs                  = 1538,
   vhpiPortDecls                   = 1539,
   vhpiRecordElems                 = 1540,
   vhpiSelectWaveforms             = 1541,
   vhpiSelectedNames               = 1542,
   DEPRECATED_vhpiSensitivitys     = 1543,
   vhpiSensitivitys                = 1543,
   vhpiSeqStmts                    = 1544,
   vhpiSigAttrs                    = 1545,
   vhpiSigDecls                    = 1546,
   vhpiSigNames                    = 1547,
   vhpiSignals                     = 1548,
   DEPRECATED_vhpiSpecNames        = 1549,
   vhpiSpecs                       = 1550,
   vhpiStmts                       = 1551,
   vhpiTransactions                = 1552,
   DEPRECATED_vhpiTypeMarks        = 1553, /* DEPRECATED */
   vhpiUnitDecls                   = 1554,
   vhpiUses                        = 1555,
   vhpiVarDecls                    = 1556,
   vhpiWaveformElems               = 1557,
   vhpiLibraryDecls                = 1558,
   vhpiLocalLoads                  = 1559,
   vhpiOptimizedLoads              = 1560,
   vhpiTypes                       = 1561,
   vhpiUseClauses                  = 1562,
   vhpiGenerateStmts               = 1563,
   vhpiLocalContributors           = 1564,
   vhpiOptimizedContributors       = 1565,
   vhpiParamExprs                  = 1566,
   vhpiEqProcessStmts              = 1567,
   vhpiEntityClassEntries          = 1568,
   vhpiSensitivities               = 1569
  };

mixin(declareEnums!vhpiOneToManyT());

/****************** PROPERTIES *******************/
/******* INTEGER or BOOLEAN PROPERTIES **********/
enum  vhpiIntPropertyT
  {
   vhpiAccessP                 = 1001,
   vhpiArgcP                   = 1002,
   vhpiAttrKindP               = 1003,
   vhpiBaseIndexP              = 1004,
   vhpiBeginLineNoP            = 1005,
   vhpiEndLineNoP              = 1006,
   vhpiEntityClassP            = 1007,
   vhpiForeignKindP            = 1008,
   vhpiFrameLevelP             = 1009,
   vhpiGenerateIndexP          = 1010,
   vhpiIntValP                 = 1011,
   vhpiIsAnonymousP            = 1012,
   vhpiIsBasicP                = 1013,
   vhpiIsCompositeP            = 1014,
   vhpiIsDefaultP              = 1015,
   vhpiIsDeferredP             = 1016,
   vhpiIsDiscreteP             = 1017,
   vhpiIsForcedP               = 1018,
   vhpiIsForeignP              = 1019,
   vhpiIsGuardedP              = 1020,
   vhpiIsImplicitDeclP         = 1021,
   DEPRECATED_vhpiIsInvalidP   = 1022, /* DEPRECATED */
   vhpiIsLocalP                = 1023,
   vhpiIsNamedP                = 1024,
   vhpiIsNullP                 = 1025,
   vhpiIsOpenP                 = 1026,
   vhpiIsPLIP                  = 1027,
   vhpiIsPassiveP              = 1028,
   vhpiIsPostponedP            = 1029,
   vhpiIsProtectedTypeP        = 1030,
   vhpiIsPureP                 = 1031,
   vhpiIsResolvedP             = 1032,
   vhpiIsScalarP               = 1033,
   vhpiIsSeqStmtP              = 1034,
   vhpiIsSharedP               = 1035,
   vhpiIsTransportP            = 1036,
   vhpiIsUnaffectedP           = 1037,
   vhpiIsUnconstrainedP        = 1038,
   vhpiIsUninstantiatedP       = 1039,
   vhpiIsUpP                   = 1040,
   vhpiIsVitalP                = 1041,
   vhpiIteratorTypeP           = 1042,
   vhpiKindP                   = 1043,
   vhpiLeftBoundP              = 1044,
   DEPRECATED_vhpiLevelP       = 1045, /* DEPRECATED */
   vhpiLineNoP                 = 1046,
   vhpiLineOffsetP             = 1047,
   vhpiLoopIndexP              = 1048,
   vhpiModeP                   = 1049,
   vhpiNumDimensionsP          = 1050,
   DEPRECATED_vhpiNumFieldsP   = 1051, /* DEPRECATED */
   vhpiNumGensP                = 1052,
   vhpiNumLiteralsP            = 1053,
   vhpiNumMembersP             = 1054,
   vhpiNumParamsP              = 1055,
   vhpiNumPortsP               = 1056,
   vhpiOpenModeP               = 1057,
   vhpiPhaseP                  = 1058,
   vhpiPositionP               = 1059,
   vhpiPredefAttrP             = 1060,
   // vhpiProtectedLevelP         = 1061,
   /* 1061 */
   vhpiReasonP                 = 1062,
   vhpiRightBoundP             = 1063,
   vhpiSigKindP                = 1064,
   vhpiSizeP                   = 1065,
   vhpiStartLineNoP            = 1066,
   vhpiStateP                  = 1067,
   vhpiStaticnessP             = 1068,
   vhpiVHDLversionP            = 1069,
   vhpiIdP                     = 1070,
   vhpiCapabilitiesP           = 1071,
   vhpiAutomaticRestoreP       = 1072,
   vhpiCompInstKindP           = 1073,
   vhpiIsBuiltInP              = 1074,
   vhpiIsDynamicP              = 1075,
   vhpiIsOperatorP             = 1076,
   vhpiNumFieldsP              = 1077
  };

mixin(declareEnums!vhpiIntPropertyT());

/******* STRING PROPERTIES **********/
enum  vhpiStrPropertyT
  {
   vhpiCaseNameP               = 1301,
   vhpiCompNameP               = 1302,
   vhpiDefNameP                = 1303,
   vhpiFileNameP               = 1304,
   vhpiFullCaseNameP           = 1305,
   vhpiFullNameP               = 1306,
   vhpiKindStrP                = 1307,
   vhpiLabelNameP              = 1308,
   vhpiLibLogicalNameP         = 1309,
   vhpiLibPhysicalNameP        = 1310,
   vhpiLogicalNameP            = 1311,
   vhpiLoopLabelNameP          = 1312,
   vhpiNameP                   = 1313,
   DEPRECATED_vhpiOpNameP      = 1314,
   vhpiStrValP                 = 1315,
   vhpiToolVersionP            = 1316,
   vhpiUnitNameP               = 1317,
   vhpiSaveRestartLocationP    = 1318,
   vhpiCompInstNameP           = 1319,
   vhpiInstNamesP              = 1320,
   vhpiSignatureNameP          = 1321,
   vhpiSpecNameP               = 1322,


   // /* MIXED LANG PROPERTIES */
   // vhpiFullVlogNameP           = 1500,
   // vhpiFullVHDLNameP           = 1501,
   // vhpiFullLSNameP             = 1502,
   // vhpiFullLSCaseNameP         = 1503

  };

mixin(declareEnums!vhpiStrPropertyT());

/******* REAL PROPERTIES **********/
enum  vhpiRealPropertyT
  {
   vhpiFloatLeftBoundP         = 1601,
   vhpiFloatRightBoundP        = 1602,
   vhpiRealValP                = 1603
  };

mixin(declareEnums!vhpiRealPropertyT());

/******* PHYSICAL PROPERTIES **********/
enum vhpiPhysPropertyT
  {
   vhpiPhysLeftBoundP          = 1651,
   vhpiPhysPositionP           = 1652,
   vhpiPhysRightBoundP         = 1653,
   vhpiPhysValP                = 1654,
   DEPRECATED_vhpiPrecisionP   = 1655, /* DEPRECATED */
   DEPRECATED_vhpiSimTimeUnitP = 1656, /* DEPRECATED */
   vhpiResolutionLimitP        = 1657,
   vhpiTimeP                   = 1658
  };

mixin(declareEnums!vhpiPhysPropertyT());

/******************* PROPERTY VALUES ************************/

/* vhpiCapabilitiesP */
enum vhpiCapabibilityT
  {
   vhpiProvidesHierarchy             = 1,
   vhpiProvidesStaticAccess          = 2,
   vhpiProvidesConnectivity          = 4,
   vhpiProvidesPostAnalysis          = 8,
   vhpiProvidesForeignModel          = 16,
   vhpiProvidesAdvancedForeignModel  = 32,
   vhpiProvidesSaveRestart           = 64,
   vhpiProvidesReset                 = 128,
   vhpiProvidesDebugRuntime          = 256,
   vhpiProvidesAdvancedDebugRuntime  = 512,
   vhpiProvidesDynamicElab           = 1024
  };

mixin(declareEnums!vhpiCapabibilityT());

/* vhpiOpenModeP */
enum vhpiOpenModeT
  {
   vhpiInOpen          = 1001,
   vhpiOutOpen         = 1002,
   vhpiReadOpen        = 1003,
   vhpiWriteOpen       = 1004,
   vhpiAppendOpen      = 1005
  };

mixin(declareEnums!vhpiOpenModeT());

/* vhpiModeP */
enum vhpiModeT
  {
   vhpiInMode          = 1001,
   vhpiOutMode         = 1002,
   vhpiInoutMode       = 1003,
   vhpiBufferMode      = 1004,
   vhpiLinkageMode     = 1005
  };

mixin(declareEnums!vhpiModeT());

/* vhpiSigKindP */
enum vhpiSigKindT
  {
   vhpiRegister        = 1001,
   vhpiBus             = 1002,
   vhpiNormal          = 1003
  };

mixin(declareEnums!vhpiSigKindT());

/* vhpiStaticnessP */
enum vhpiStaticnessT
  {
   vhpiLocallyStatic   = 1001,
   vhpiGloballyStatic  = 1002,
   vhpiDynamic         = 1003
  };

mixin(declareEnums!vhpiStaticnessT());

/* vhpiPredefAttrP */
enum vhpiPredefAttrT
  {
   vhpiActivePA        = 1001,
   vhpiAscendingPA     = 1002,
   vhpiBasePA          = 1003,
   vhpiDelayedPA       = 1004,
   vhpiDrivingPA       = 1005,
   vhpiDriving_valuePA = 1006,
   vhpiEventPA         = 1007,
   vhpiHighPA          = 1008,
   vhpiImagePA         = 1009,
   vhpiInstance_namePA = 1010,
   vhpiLast_activePA   = 1011,
   vhpiLast_eventPA    = 1012,
   vhpiLast_valuePA    = 1013,
   vhpiLeftPA          = 1014,
   vhpiLeftofPA        = 1015,
   vhpiLengthPA        = 1016,
   vhpiLowPA           = 1017,
   vhpiPath_namePA     = 1018,
   vhpiPosPA           = 1019,
   vhpiPredPA          = 1020,
   vhpiQuietPA         = 1021,
   vhpiRangePA         = 1022,
   vhpiReverse_rangePA = 1023,
   vhpiRightPA         = 1024,
   vhpiRightofPA       = 1025,
   vhpiSimple_namePA   = 1026,
   vhpiStablePA        = 1027,
   vhpiSuccPA          = 1028,
   vhpiTransactionPA   = 1029,
   vhpiValPA           = 1030,
   vhpiValuePA         = 1031
  };

mixin(declareEnums!vhpiPredefAttrT());

/* vhpiAttrKindP */
enum vhpiAttrKindT
  {
   vhpiFunctionAK        = 1,
   vhpiRangeAK           = 2,
   vhpiSignalAK          = 3,
   vhpiTypeAK            = 4,
   vhpiValueAK           = 5
  };

mixin(declareEnums!vhpiAttrKindT());

/* vhpiEntityClassP */
enum vhpiEntityClassT
  {
   vhpiEntityEC        = 1001,
   vhpiArchitectureEC  = 1002,
   vhpiConfigurationEC = 1003,
   vhpiProcedureEC     = 1004,
   vhpiFunctionEC      = 1005,
   vhpiPackageEC       = 1006,
   vhpiTypeEC          = 1007,
   vhpiSubtypeEC       = 1008,
   vhpiConstantEC      = 1009,
   vhpiSignalEC        = 1010,
   vhpiVariableEC      = 1011,
   vhpiComponentEC     = 1012,
   vhpiLabelEC         = 1013,
   vhpiLiteralEC       = 1014,
   vhpiUnitsEC         = 1015,
   vhpiFileEC          = 1016,
   vhpiGroupEC         = 1017
  };

mixin(declareEnums!vhpiEntityClassT());

/* vhpiAccessP */
enum vhpiAccessT
  {
   vhpiRead            = 1,
   vhpiWrite           = 2,
   vhpiConnectivity    = 4,
   vhpiNoAccess        = 8
  };

mixin(declareEnums!vhpiAccessT());

/* value for vhpiStateP property for callbacks */
enum vhpiStateT
  {
   vhpiEnable,
   vhpiDisable,
   vhpiMature /* callback has occurred */
  };

mixin(declareEnums!vhpiStateT());

enum vhpiVHDL                 = 1001;
enum vhpiVerilog              = 1002;

/* enumeration type for vhpiCompInstKindP property */
enum vhpiCompInstKindT
  {
   vhpiDirect,
   vhpiComp,
   vhpiConfig
  };

mixin(declareEnums!vhpiCompInstKindT());

/* the following values are used only for the
   vhpiResolutionLimitP property and for setting the unit field of the value
   structure; they represent the physical position of a given
   VHDL time unit */
/* time unit physical position values {high, low} */
extern(C) {
  immutable vhpiPhysT vhpiFS;
  immutable vhpiPhysT vhpiPS;
  immutable vhpiPhysT vhpiNS;
  immutable vhpiPhysT vhpiUS;
  immutable vhpiPhysT vhpiMS;
  immutable vhpiPhysT vhpiS;
  immutable vhpiPhysT vhpiMN;
  immutable vhpiPhysT vhpiHR;
}
/* IEEE std_logic values */
enum vhpiU =                 0; /* uninitialized */
enum vhpiX =                 1; /* unknown */
enum vhpi0 =                 2; /* forcing 0 */
enum vhpi1 =                 3; /* forcing 1 */
enum vhpiZ =                 4; /* high impedance */
enum vhpiW =                 5; /* weak unknown */
enum vhpiL =                 6; /* weak 0 */
enum vhpiH =                 7; /* weak 1 */
enum vhpiDontCare =          8; /* don't care */

/* IEEE std bit values */
enum vhpibit0 =              0; /* bit 0 */
enum vhpibit1 =              1; /* bit 1 */

/* IEEE std boolean values */
enum vhpiFalse =             0; /* false */
enum vhpiTrue =              1; /* true */

/************** vhpiPhaseP property values *************/
enum vhpiPhaseT
  {
   vhpiRegistrationPhase   = 1,
   vhpiAnalysisPhase       = 2,
   vhpiElaborationPhase    = 3,
   vhpiInitializationPhase = 4,
   vhpiSimulationPhase     = 5,
   vhpiTerminationPhase    = 6,
   vhpiSavePhase           = 7,
   vhpiRestartPhase        = 8,
   vhpiResetPhase          = 9
  } /*vhpiPhaseT*/ ;

mixin(declareEnums!vhpiPhaseT());

/**************** PLI error information structure ****************/

enum vhpiSeverityT
  {
   vhpiNote                = 1,
   vhpiWarning             = 2,
   vhpiError               = 3,
   vhpiFailure             = 6,
   vhpiSystem              = 4,
   vhpiInternal            = 5
  } /*vhpiSeverityT*/;

mixin(declareEnums!vhpiSeverityT());

struct vhpiErrorInfoT
{
  vhpiSeverityT severity;
  char *message;
  char *str;
  char *file; /* Name of the VHDL file where the VHPI error originated */
  int line; /* Line number in the VHDL file */
} /*vhpiErrorInfoT*/;

/********************* callback structures ************************/
/* callback user data structure */

alias cb_rtn_func_type = void function(const vhpiCbDataT *);

struct vhpiCbDataT
{
  int reason; /* callback reason */
  cb_rtn_func_type *cb_rtn;
  vhpiHandleT obj; /* trigger object */
  vhpiTimeT *time; /* callback time */
  vhpiValueT *value; /* trigger object value */
  void *user_data; /* pointer to user data to be passed to the callback function */
} /*vhpiCbDataT*/;

/**************************** CALLBACK REASONS ****************************/
/*************************** Simulation object related ***********************/
/* These are repetitive callbacks */
enum vhpiCbValueChange =               1001;
enum vhpiCbForce =                     1002;
enum vhpiCbRelease =                   1003;
enum vhpiCbTransaction =               1004; /* optional callback reason */

/****************************** Statement related ****************************/
/* These are repetitive callbacks */
enum vhpiCbStmt =                      1005;
enum vhpiCbResume =                    1006;
enum vhpiCbSuspend =                   1007;
enum vhpiCbStartOfSubpCall =           1008;
enum vhpiCbEndOfSubpCall =             1009;

/****************************** Time related ******************************/
/* the Rep callback reasons are the repeated versions of the callbacks */

enum vhpiCbAfterDelay =                1010;
enum vhpiCbRepAfterDelay =             1011;

/*************************** Simulation cycle phase related *****************/
enum vhpiCbNextTimeStep =              1012;
enum vhpiCbRepNextTimeStep =           1013;
enum vhpiCbStartOfNextCycle =          1014;
enum vhpiCbRepStartOfNextCycle =       1015;
enum vhpiCbStartOfProcesses =          1016;
enum vhpiCbRepStartOfProcesses =       1017;
enum vhpiCbEndOfProcesses =            1018;
enum vhpiCbRepEndOfProcesses =         1019;
enum vhpiCbLastKnownDeltaCycle =       1020;
enum vhpiCbRepLastKnownDeltaCycle =    1021;
enum vhpiCbStartOfPostponed =          1022;
enum vhpiCbRepStartOfPostponed =       1023;
enum vhpiCbEndOfTimeStep =             1024;
enum vhpiCbRepEndOfTimeStep =          1025;

/***************************** Action related *****************************/
/* these are one time callback unless otherwise noted */
enum vhpiCbStartOfTool =               1026;
enum vhpiCbEndOfTool =                 1027;
enum vhpiCbStartOfAnalysis =           1028;
enum vhpiCbEndOfAnalysis =             1029;
enum vhpiCbStartOfElaboration =        1030;
enum vhpiCbEndOfElaboration =          1031;
enum vhpiCbStartOfInitialization =     1032;
enum vhpiCbEndOfInitialization =       1033;
enum vhpiCbStartOfSimulation =         1034;
enum vhpiCbEndOfSimulation =           1035;
enum vhpiCbQuiescense =                1036; /* repetitive */
enum vhpiCbPLIError =                  1037; /* repetitive */
enum vhpiCbStartOfSave =               1038;
enum vhpiCbEndOfSave =                 1039;
enum vhpiCbStartOfRestart =            1040;
enum vhpiCbEndOfRestart =              1041;
enum vhpiCbStartOfReset =              1042;
enum vhpiCbEndOfReset =                1043;
enum vhpiCbEnterInteractive =          1044; /* repetitive */
enum vhpiCbExitInteractive =           1045; /* repetitive */
enum vhpiCbSigInterrupt =              1046; /* repetitive */

/* Foreign model callbacks */
enum vhpiCbTimeOut =                   1047; /* non repetitive */
enum vhpiCbRepTimeOut =                1048; /* repetitive */
enum vhpiCbSensitivity =               1049; /* repetitive */

/**************************** CALLBACK FLAGS ******************************/
enum vhpiReturnCb =  0x00000001;
enum vhpiDisableCb = 0x00000010;

/************** vhpiAutomaticRestoreP property values *************/
enum vhpiAutomaticRestoreT
  {
   vhpiRestoreAll       = 1,
   vhpiRestoreUserData  = 2,
   vhpiRestoreHandles   = 4,
   vhpiRestoreCallbacks = 8
  };

mixin(declareEnums!vhpiAutomaticRestoreT());

/******************** FUNCTION DECLARATIONS *********************/

extern(C) int vhpi_assert (vhpiSeverityT severity,
			   const char *formatmsg,
			   ...);


/* callback related */

extern(C) vhpiHandleT vhpi_register_cb (vhpiCbDataT *cb_data_p,
					int flags);

extern(C) int vhpi_remove_cb (vhpiHandleT cb_obj);

extern(C) int vhpi_disable_cb (vhpiHandleT cb_obj);

extern(C) int vhpi_enable_cb (vhpiHandleT cb_obj);

extern(C) int vhpi_get_cb_info (vhpiHandleT object,
				vhpiCbDataT *cb_data_p);

// /* utilities for sensitivity-set bitmaps */
// /* The replacement text for these macros is implementation defined */
// /* The behavior is specified in G.1 */
// int vhpi_sens_first (vhpiValueT *sens);

// int vhpi_sens_zero (vhpiValueT *sens);

// int vhpi_sens_clr (int obj,
// 		   vhpiValueT *sens);

// int vhpi_sens_set (int obj,
// 		   vhpiValueT *sens);

// int vhpi_sens_isset (int obj,
// 		     vhpiValueT *sens);

// alias VHPI_SENS_ZERO = vhpi_sens_zero;
// alias VHPI_SENS_SET = vhpi_sens_set;
// alias VHPI_SENS_CLR = vhpi_sens_clr;
// alias VHPI_SENS_ISSET = vhpi_sens_isset;
// alias VHPI_SENS_FIRST = vhpi_sens_first;

/* for obtaining handles */

@weak extern(C) vhpiHandleT vhpi_handle_by_name (const char *name,
						 vhpiHandleT hier) {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}

vhpiHandleT vhpiHandleByName(string name, vhpiHandleT hier) {
  import std.string;
  return vhpi_handle_by_name(name.toStringz, hier);
}
    
@weak extern(C) vhpiHandleT vhpi_handle_by_index (vhpiOneToManyT itRel,
						  vhpiHandleT parent,
						  int indx) {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiHandleByIndex = vhpi_handle_by_index;

/* for traversing relationships */

@weak extern(C) vhpiHandleT vhpi_handle (vhpiOneToOneT type,
					 vhpiHandleT referenceHandle) {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiHandle = vhpi_handle;

@weak extern(C) vhpiHandleT vhpi_iterator (vhpiOneToManyT type,
					   vhpiHandleT referenceHandle)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiIterator = vhpi_iterator;

@weak extern(C) vhpiHandleT vhpi_scan (vhpiHandleT iterator)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiScan = vhpi_scan;
    
/* for processsing properties */

@weak extern(C) vhpiIntT vhpi_get (vhpiIntPropertyT property,
				   vhpiHandleT object)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGet = vhpi_get;

@weak extern(C) const(vhpiCharT) * vhpi_get_str (vhpiStrPropertyT property,
						 vhpiHandleT object)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetStr = vhpi_get_str;

@weak extern(C) vhpiRealT vhpi_get_real (vhpiRealPropertyT property,
					 vhpiHandleT object)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetReal = vhpi_get_real;

@weak extern(C) vhpiPhysT vhpi_get_phys (vhpiPhysPropertyT property,
					 vhpiHandleT object)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetPhys = vhpi_get_phys;
    
/* for access to protected types */

alias vhpiUserFctT = int function();

@weak extern(C) int vhpi_protected_call (vhpiHandleT varHdl,
					 vhpiUserFctT userFct,
					 void *userData)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiProtectedCall = vhpi_protected_call;

/* value processing */

/* vhpi_put_value flags */
enum vhpiPutValueModeT
  {
   vhpiDeposit,
   vhpiDepositPropagate,
   vhpiForce,
   vhpiForcePropagate,
   vhpiRelease,
   vhpiSizeConstraint
  };

mixin(declareEnums!vhpiPutValueModeT());

enum vhpiDelayModeT
  {
   vhpiInertial,
   vhpiTransport
  };

mixin(declareEnums!vhpiDelayModeT());

@weak extern(C) int vhpi_get_value (vhpiHandleT expr,
				    vhpiValueT *value_p)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetValue = vhpi_get_value;

@weak extern(C) int vhpi_put_value (vhpiHandleT object,
				    vhpiValueT *value_p,
				    vhpiPutValueModeT flags)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}

    
alias vhpiPutValue = vhpi_put_value;

// enum vhpiPutValueFlagsT {
// 			   vhpiDeposit,
// 			   vhpiDepositPropagate,
// 			   vhpiForce,
// 			   vhpiForcePropagate,
// 			   vhpiRelease,
// 			   vhpiSizeConstraint
// }

@weak extern(C) int vhpi_schedule_transaction (vhpiHandleT drivHdl,
					       vhpiValueT *value_p,
					       uint numValues,
					       vhpiTimeT *delayp,
					       uint delayMode,
					       vhpiTimeT *pulseRejp)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}

alias vhpiScheduleTransaction = vhpi_schedule_transaction;

    
@weak extern(C) int vhpi_format_value (const vhpiValueT *in_value_p,
				       vhpiValueT *out_value_p)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiFormatValue = vhpi_format_value;

/* time processing */

@weak extern(C) void vhpi_get_time (vhpiTimeT *time_p,
				    long *cycles)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetTime = vhpi_get_time;

enum vhpiNoActivity = -1;

@weak extern(C) int vhpi_get_next_time (vhpiTimeT *time_p)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetNextTime = vhpi_get_next_time;

/* simulation control */

enum vhpiSimControlT
  {
   vhpiStop     = 0,
   vhpiFinish   = 1,
   vhpiReset    = 2

  };

mixin(declareEnums!vhpiSimControlT());

@weak extern(C) int vhpi_sim_control (vhpiSimControlT command,
				      ...)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiSimControl = vhpi_sim_control;

/* I/O routine */

@weak extern(C) int vhpi_printf (const char *format,
				 ...)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}

int vhpiPrintf(string format, ...) {
  va_list argp;
  va_start(argp, format);
  return vhpiVprintf(format, argp);
}

int vhpi_vprintf (const char *format,
		  va_list args)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
int vhpiVprintf(string formatmsg, va_list args) {
  import std.string;	// toStringz
  return vhpi_vprintf(formatmsg.toStringz, args);
}

/* utilities to print VHDL strings */

@weak extern(C) int vhpi_is_printable(char ch)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiIsPrintable = vhpi_is_printable;


/* utility routines */

@weak extern(C) int vhpi_compare_handles (vhpiHandleT handle1,
					  vhpiHandleT handle2)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiCompareHandles = vhpi_compare_handles;

@weak extern(C) int vhpi_check_error (vhpiErrorInfoT *error_info_p)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiCheckError = vhpi_check_error;

@weak extern(C) int vhpi_release_handle (vhpiHandleT object)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiReleaseHandle = vhpi_release_handle;

/* creation functions */

@weak extern(C) vhpiHandleT vhpi_create (vhpiClassKindT kind,
					 vhpiHandleT handle1,
					 vhpiHandleT handle2)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiCreate = vhpi_create;

/* Foreign model data structures and functions */

enum vhpiForeignT
  {
   vhpiArchF   = 1,
   vhpiArchFK  = 1, /* for compatibility reasons */
   vhpiFuncF   = 2,
   vhpiFuncFK  = 2, /* for compatibility reasons */
   vhpiProcF   = 3,
   vhpiProcFK  = 3, /* for compatibility reasons */
   vhpiLibF    = 4,
   vhpiAppF    = 5
  };

mixin(declareEnums!vhpiForeignT());

alias elabcf_func_type = void function(const vhpiCbDataT *cb_data_p);
alias execf_func_type = void function(const vhpiCbDataT *cb_data_p);

struct vhpiForeignDataT
{
  vhpiForeignT kind;
  char * libraryName;
  char * modelName;
  elabcf_func_type *elabf;
  execf_func_type *execf;
};

@weak extern(C) vhpiHandleT vhpi_register_foreignf (vhpiForeignDataT *foreignDatap)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiRegisterForeignf = vhpi_register_foreignf;

@weak extern(C) int vhpi_get_foreignf_info (vhpiHandleT hdl,
					    vhpiForeignDataT *foreignDatap)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetForeignfInfo = vhpi_get_foreignf_info;

/* vhpi_get_foreign_info is DEPRECATED */
@weak extern(C) int vhpi_get_foreign_info (vhpiHandleT hdl,
					   vhpiForeignDataT *foreignDatap)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetForeignInfo = vhpi_get_foreign_info;

/* for saving and restoring foreign models data */

@weak extern(C) size_t vhpi_get_data (int id,
				      void *dataLoc,
				      uint numBytes)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiGetData = vhpi_get_data;

@weak extern(C) size_t vhpi_put_data (int id,
				      void *dataLoc,
				      uint numBytes)  {
  assert(false, "Kindly link to a VHDL compiler that supports VHPI");
}
alias vhpiPutData = vhpi_put_data;

