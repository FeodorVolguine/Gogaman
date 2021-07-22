#pragma once

#define OpCodeCase(x) case SpvOp::x: return #x;

enum SpvOp
{
    SpvOpNop = 0,
    SpvOpUndef = 1,
    SpvOpSourceContinued = 2,
    SpvOpSource = 3,
    SpvOpSourceExtension = 4,
    SpvOpName = 5,
    SpvOpMemberName = 6,
    SpvOpString = 7,
    SpvOpLine = 8,
    SpvOpExtension = 10,
    SpvOpExtInstImport = 11,
    SpvOpExtInst = 12,
    SpvOpMemoryModel = 14,
    SpvOpEntryPoint = 15,
    SpvOpExecutionMode = 16,
    SpvOpCapability = 17,
    SpvOpTypeVoid = 19,
    SpvOpTypeBool = 20,
    SpvOpTypeInt = 21,
    SpvOpTypeFloat = 22,
    SpvOpTypeVector = 23,
    SpvOpTypeMatrix = 24,
    SpvOpTypeImage = 25,
    SpvOpTypeSampler = 26,
    SpvOpTypeSampledImage = 27,
    SpvOpTypeArray = 28,
    SpvOpTypeRuntimeArray = 29,
    SpvOpTypeStruct = 30,
    SpvOpTypeOpaque = 31,
    SpvOpTypePointer = 32,
    SpvOpTypeFunction = 33,
    SpvOpTypeEvent = 34,
    SpvOpTypeDeviceEvent = 35,
    SpvOpTypeReserveId = 36,
    SpvOpTypeQueue = 37,
    SpvOpTypePipe = 38,
    SpvOpTypeForwardPointer = 39,
    SpvOpConstantTrue = 41,
    SpvOpConstantFalse = 42,
    SpvOpConstant = 43,
    SpvOpConstantComposite = 44,
    SpvOpConstantSampler = 45,
    SpvOpConstantNull = 46,
    SpvOpSpecConstantTrue = 48,
    SpvOpSpecConstantFalse = 49,
    SpvOpSpecConstant = 50,
    SpvOpSpecConstantComposite = 51,
    SpvOpSpecConstantOp = 52,
    SpvOpFunction = 54,
    SpvOpFunctionParameter = 55,
    SpvOpFunctionEnd = 56,
    SpvOpFunctionCall = 57,
    SpvOpVariable = 59,
    SpvOpImageTexelPointer = 60,
    SpvOpLoad = 61,
    SpvOpStore = 62,
    SpvOpCopyMemory = 63,
    SpvOpCopyMemorySized = 64,
    SpvOpAccessChain = 65,
    SpvOpInBoundsAccessChain = 66,
    SpvOpPtrAccessChain = 67,
    SpvOpArrayLength = 68,
    SpvOpGenericPtrMemSemantics = 69,
    SpvOpInBoundsPtrAccessChain = 70,
    SpvOpDecorate = 71,
    SpvOpMemberDecorate = 72,
    SpvOpDecorationGroup = 73,
    SpvOpGroupDecorate = 74,
    SpvOpGroupMemberDecorate = 75,
    SpvOpVectorExtractDynamic = 77,
    SpvOpVectorInsertDynamic = 78,
    SpvOpVectorShuffle = 79,
    SpvOpCompositeConstruct = 80,
    SpvOpCompositeExtract = 81,
    SpvOpCompositeInsert = 82,
    SpvOpCopyObject = 83,
    SpvOpTranspose = 84,
    SpvOpSampledImage = 86,
    SpvOpImageSampleImplicitLod = 87,
    SpvOpImageSampleExplicitLod = 88,
    SpvOpImageSampleDrefImplicitLod = 89,
    SpvOpImageSampleDrefExplicitLod = 90,
    SpvOpImageSampleProjImplicitLod = 91,
    SpvOpImageSampleProjExplicitLod = 92,
    SpvOpImageSampleProjDrefImplicitLod = 93,
    SpvOpImageSampleProjDrefExplicitLod = 94,
    SpvOpImageFetch = 95,
    SpvOpImageGather = 96,
    SpvOpImageDrefGather = 97,
    SpvOpImageRead = 98,
    SpvOpImageWrite = 99,
    SpvOpImage = 100,
    SpvOpImageQueryFormat = 101,
    SpvOpImageQueryOrder = 102,
    SpvOpImageQuerySizeLod = 103,
    SpvOpImageQuerySize = 104,
    SpvOpImageQueryLod = 105,
    SpvOpImageQueryLevels = 106,
    SpvOpImageQuerySamples = 107,
    SpvOpConvertFToU = 109,
    SpvOpConvertFToS = 110,
    SpvOpConvertSToF = 111,
    SpvOpConvertUToF = 112,
    SpvOpUConvert = 113,
    SpvOpSConvert = 114,
    SpvOpFConvert = 115,
    SpvOpQuantizeToF16 = 116,
    SpvOpConvertPtrToU = 117,
    SpvOpSatConvertSToU = 118,
    SpvOpSatConvertUToS = 119,
    SpvOpConvertUToPtr = 120,
    SpvOpPtrCastToGeneric = 121,
    SpvOpGenericCastToPtr = 122,
    SpvOpGenericCastToPtrExplicit = 123,
    SpvOpBitcast = 124,
    SpvOpSNegate = 126,
    SpvOpFNegate = 127,
    SpvOpIAdd = 128,
    SpvOpFAdd = 129,
    SpvOpISub = 130,
    SpvOpFSub = 131,
    SpvOpIMul = 132,
    SpvOpFMul = 133,
    SpvOpUDiv = 134,
    SpvOpSDiv = 135,
    SpvOpFDiv = 136,
    SpvOpUMod = 137,
    SpvOpSRem = 138,
    SpvOpSMod = 139,
    SpvOpFRem = 140,
    SpvOpFMod = 141,
    SpvOpVectorTimesScalar = 142,
    SpvOpMatrixTimesScalar = 143,
    SpvOpVectorTimesMatrix = 144,
    SpvOpMatrixTimesVector = 145,
    SpvOpMatrixTimesMatrix = 146,
    SpvOpOuterProduct = 147,
    SpvOpDot = 148,
    SpvOpIAddCarry = 149,
    SpvOpISubBorrow = 150,
    SpvOpUMulExtended = 151,
    SpvOpSMulExtended = 152,
    SpvOpAny = 154,
    SpvOpAll = 155,
    SpvOpIsNan = 156,
    SpvOpIsInf = 157,
    SpvOpIsFinite = 158,
    SpvOpIsNormal = 159,
    SpvOpSignBitSet = 160,
    SpvOpLessOrGreater = 161,
    SpvOpOrdered = 162,
    SpvOpUnordered = 163,
    SpvOpLogicalEqual = 164,
    SpvOpLogicalNotEqual = 165,
    SpvOpLogicalOr = 166,
    SpvOpLogicalAnd = 167,
    SpvOpLogicalNot = 168,
    SpvOpSelect = 169,
    SpvOpIEqual = 170,
    SpvOpINotEqual = 171,
    SpvOpUGreaterThan = 172,
    SpvOpSGreaterThan = 173,
    SpvOpUGreaterThanEqual = 174,
    SpvOpSGreaterThanEqual = 175,
    SpvOpULessThan = 176,
    SpvOpSLessThan = 177,
    SpvOpULessThanEqual = 178,
    SpvOpSLessThanEqual = 179,
    SpvOpFOrdEqual = 180,
    SpvOpFUnordEqual = 181,
    SpvOpFOrdNotEqual = 182,
    SpvOpFUnordNotEqual = 183,
    SpvOpFOrdLessThan = 184,
    SpvOpFUnordLessThan = 185,
    SpvOpFOrdGreaterThan = 186,
    SpvOpFUnordGreaterThan = 187,
    SpvOpFOrdLessThanEqual = 188,
    SpvOpFUnordLessThanEqual = 189,
    SpvOpFOrdGreaterThanEqual = 190,
    SpvOpFUnordGreaterThanEqual = 191,
    SpvOpShiftRightLogical = 194,
    SpvOpShiftRightArithmetic = 195,
    SpvOpShiftLeftLogical = 196,
    SpvOpBitwiseOr = 197,
    SpvOpBitwiseXor = 198,
    SpvOpBitwiseAnd = 199,
    SpvOpNot = 200,
    SpvOpBitFieldInsert = 201,
    SpvOpBitFieldSExtract = 202,
    SpvOpBitFieldUExtract = 203,
    SpvOpBitReverse = 204,
    SpvOpBitCount = 205,
    SpvOpDPdx = 207,
    SpvOpDPdy = 208,
    SpvOpFwidth = 209,
    SpvOpDPdxFine = 210,
    SpvOpDPdyFine = 211,
    SpvOpFwidthFine = 212,
    SpvOpDPdxCoarse = 213,
    SpvOpDPdyCoarse = 214,
    SpvOpFwidthCoarse = 215,
    SpvOpEmitVertex = 218,
    SpvOpEndPrimitive = 219,
    SpvOpEmitStreamVertex = 220,
    SpvOpEndStreamPrimitive = 221,
    SpvOpControlBarrier = 224,
    SpvOpMemoryBarrier = 225,
    SpvOpAtomicLoad = 227,
    SpvOpAtomicStore = 228,
    SpvOpAtomicExchange = 229,
    SpvOpAtomicCompareExchange = 230,
    SpvOpAtomicCompareExchangeWeak = 231,
    SpvOpAtomicIIncrement = 232,
    SpvOpAtomicIDecrement = 233,
    SpvOpAtomicIAdd = 234,
    SpvOpAtomicISub = 235,
    SpvOpAtomicSMin = 236,
    SpvOpAtomicUMin = 237,
    SpvOpAtomicSMax = 238,
    SpvOpAtomicUMax = 239,
    SpvOpAtomicAnd = 240,
    SpvOpAtomicOr = 241,
    SpvOpAtomicXor = 242,
    SpvOpPhi = 245,
    SpvOpLoopMerge = 246,
    SpvOpSelectionMerge = 247,
    SpvOpLabel = 248,
    SpvOpBranch = 249,
    SpvOpBranchConditional = 250,
    SpvOpSwitch = 251,
    SpvOpKill = 252,
    SpvOpReturn = 253,
    SpvOpReturnValue = 254,
    SpvOpUnreachable = 255,
    SpvOpLifetimeStart = 256,
    SpvOpLifetimeStop = 257,
    SpvOpGroupAsyncCopy = 259,
    SpvOpGroupWaitEvents = 260,
    SpvOpGroupAll = 261,
    SpvOpGroupAny = 262,
    SpvOpGroupBroadcast = 263,
    SpvOpGroupIAdd = 264,
    SpvOpGroupFAdd = 265,
    SpvOpGroupFMin = 266,
    SpvOpGroupUMin = 267,
    SpvOpGroupSMin = 268,
    SpvOpGroupFMax = 269,
    SpvOpGroupUMax = 270,
    SpvOpGroupSMax = 271,
    SpvOpReadPipe = 274,
    SpvOpWritePipe = 275,
    SpvOpReservedReadPipe = 276,
    SpvOpReservedWritePipe = 277,
    SpvOpReserveReadPipePackets = 278,
    SpvOpReserveWritePipePackets = 279,
    SpvOpCommitReadPipe = 280,
    SpvOpCommitWritePipe = 281,
    SpvOpIsValidReserveId = 282,
    SpvOpGetNumPipePackets = 283,
    SpvOpGetMaxPipePackets = 284,
    SpvOpGroupReserveReadPipePackets = 285,
    SpvOpGroupReserveWritePipePackets = 286,
    SpvOpGroupCommitReadPipe = 287,
    SpvOpGroupCommitWritePipe = 288,
    SpvOpEnqueueMarker = 291,
    SpvOpEnqueueKernel = 292,
    SpvOpGetKernelNDrangeSubGroupCount = 293,
    SpvOpGetKernelNDrangeMaxSubGroupSize = 294,
    SpvOpGetKernelWorkGroupSize = 295,
    SpvOpGetKernelPreferredWorkGroupSizeMultiple = 296,
    SpvOpRetainEvent = 297,
    SpvOpReleaseEvent = 298,
    SpvOpCreateUserEvent = 299,
    SpvOpIsValidEvent = 300,
    SpvOpSetUserEventStatus = 301,
    SpvOpCaptureEventProfilingInfo = 302,
    SpvOpGetDefaultQueue = 303,
    SpvOpBuildNDRange = 304,
    SpvOpImageSparseSampleImplicitLod = 305,
    SpvOpImageSparseSampleExplicitLod = 306,
    SpvOpImageSparseSampleDrefImplicitLod = 307,
    SpvOpImageSparseSampleDrefExplicitLod = 308,
    SpvOpImageSparseSampleProjImplicitLod = 309,
    SpvOpImageSparseSampleProjExplicitLod = 310,
    SpvOpImageSparseSampleProjDrefImplicitLod = 311,
    SpvOpImageSparseSampleProjDrefExplicitLod = 312,
    SpvOpImageSparseFetch = 313,
    SpvOpImageSparseGather = 314,
    SpvOpImageSparseDrefGather = 315,
    SpvOpImageSparseTexelsResident = 316,
    SpvOpNoLine = 317,
    SpvOpAtomicFlagTestAndSet = 318,
    SpvOpAtomicFlagClear = 319,
    SpvOpImageSparseRead = 320,
    SpvOpSizeOf = 321,
    SpvOpTypePipeStorage = 322,
    SpvOpConstantPipeStorage = 323,
    SpvOpCreatePipeFromPipeStorage = 324,
    SpvOpGetKernelLocalSizeForSubgroupCount = 325,
    SpvOpGetKernelMaxNumSubgroups = 326,
    SpvOpTypeNamedBarrier = 327,
    SpvOpNamedBarrierInitialize = 328,
    SpvOpMemoryNamedBarrier = 329,
    SpvOpModuleProcessed = 330,
    SpvOpExecutionModeId = 331,
    SpvOpDecorateId = 332,
    SpvOpGroupNonUniformElect = 333,
    SpvOpGroupNonUniformAll = 334,
    SpvOpGroupNonUniformAny = 335,
    SpvOpGroupNonUniformAllEqual = 336,
    SpvOpGroupNonUniformBroadcast = 337,
    SpvOpGroupNonUniformBroadcastFirst = 338,
    SpvOpGroupNonUniformBallot = 339,
    SpvOpGroupNonUniformInverseBallot = 340,
    SpvOpGroupNonUniformBallotBitExtract = 341,
    SpvOpGroupNonUniformBallotBitCount = 342,
    SpvOpGroupNonUniformBallotFindLSB = 343,
    SpvOpGroupNonUniformBallotFindMSB = 344,
    SpvOpGroupNonUniformShuffle = 345,
    SpvOpGroupNonUniformShuffleXor = 346,
    SpvOpGroupNonUniformShuffleUp = 347,
    SpvOpGroupNonUniformShuffleDown = 348,
    SpvOpGroupNonUniformIAdd = 349,
    SpvOpGroupNonUniformFAdd = 350,
    SpvOpGroupNonUniformIMul = 351,
    SpvOpGroupNonUniformFMul = 352,
    SpvOpGroupNonUniformSMin = 353,
    SpvOpGroupNonUniformUMin = 354,
    SpvOpGroupNonUniformFMin = 355,
    SpvOpGroupNonUniformSMax = 356,
    SpvOpGroupNonUniformUMax = 357,
    SpvOpGroupNonUniformFMax = 358,
    SpvOpGroupNonUniformBitwiseAnd = 359,
    SpvOpGroupNonUniformBitwiseOr = 360,
    SpvOpGroupNonUniformBitwiseXor = 361,
    SpvOpGroupNonUniformLogicalAnd = 362,
    SpvOpGroupNonUniformLogicalOr = 363,
    SpvOpGroupNonUniformLogicalXor = 364,
    SpvOpGroupNonUniformQuadBroadcast = 365,
    SpvOpGroupNonUniformQuadSwap = 366,
    SpvOpCopyLogical = 400,
    SpvOpPtrEqual = 401,
    SpvOpPtrNotEqual = 402,
    SpvOpPtrDiff = 403,
    SpvOpTerminateInvocation = 4416,
    SpvOpSubgroupBallotKHR = 4421,
    SpvOpSubgroupFirstInvocationKHR = 4422,
    SpvOpSubgroupAllKHR = 4428,
    SpvOpSubgroupAnyKHR = 4429,
    SpvOpSubgroupAllEqualKHR = 4430,
    SpvOpSubgroupReadInvocationKHR = 4432,
    SpvOpTraceRayKHR = 4445,
    SpvOpExecuteCallableKHR = 4446,
    SpvOpConvertUToAccelerationStructureKHR = 4447,
    SpvOpIgnoreIntersectionKHR = 4448,
    SpvOpTerminateRayKHR = 4449,
    SpvOpTypeRayQueryKHR = 4472,
    SpvOpRayQueryInitializeKHR = 4473,
    SpvOpRayQueryTerminateKHR = 4474,
    SpvOpRayQueryGenerateIntersectionKHR = 4475,
    SpvOpRayQueryConfirmIntersectionKHR = 4476,
    SpvOpRayQueryProceedKHR = 4477,
    SpvOpRayQueryGetIntersectionTypeKHR = 4479,
    SpvOpGroupIAddNonUniformAMD = 5000,
    SpvOpGroupFAddNonUniformAMD = 5001,
    SpvOpGroupFMinNonUniformAMD = 5002,
    SpvOpGroupUMinNonUniformAMD = 5003,
    SpvOpGroupSMinNonUniformAMD = 5004,
    SpvOpGroupFMaxNonUniformAMD = 5005,
    SpvOpGroupUMaxNonUniformAMD = 5006,
    SpvOpGroupSMaxNonUniformAMD = 5007,
    SpvOpFragmentMaskFetchAMD = 5011,
    SpvOpFragmentFetchAMD = 5012,
    SpvOpReadClockKHR = 5056,
    SpvOpImageSampleFootprintNV = 5283,
    SpvOpGroupNonUniformPartitionNV = 5296,
    SpvOpWritePackedPrimitiveIndices4x8NV = 5299,
    SpvOpReportIntersectionKHR = 5334,
    SpvOpReportIntersectionNV = 5334,
    SpvOpIgnoreIntersectionNV = 5335,
    SpvOpTerminateRayNV = 5336,
    SpvOpTraceNV = 5337,
    SpvOpTypeAccelerationStructureKHR = 5341,
    SpvOpTypeAccelerationStructureNV = 5341,
    SpvOpExecuteCallableNV = 5344,
    SpvOpTypeCooperativeMatrixNV = 5358,
    SpvOpCooperativeMatrixLoadNV = 5359,
    SpvOpCooperativeMatrixStoreNV = 5360,
    SpvOpCooperativeMatrixMulAddNV = 5361,
    SpvOpCooperativeMatrixLengthNV = 5362,
    SpvOpBeginInvocationInterlockEXT = 5364,
    SpvOpEndInvocationInterlockEXT = 5365,
    SpvOpDemoteToHelperInvocationEXT = 5380,
    SpvOpIsHelperInvocationEXT = 5381,
    SpvOpSubgroupShuffleINTEL = 5571,
    SpvOpSubgroupShuffleDownINTEL = 5572,
    SpvOpSubgroupShuffleUpINTEL = 5573,
    SpvOpSubgroupShuffleXorINTEL = 5574,
    SpvOpSubgroupBlockReadINTEL = 5575,
    SpvOpSubgroupBlockWriteINTEL = 5576,
    SpvOpSubgroupImageBlockReadINTEL = 5577,
    SpvOpSubgroupImageBlockWriteINTEL = 5578,
    SpvOpSubgroupImageMediaBlockReadINTEL = 5580,
    SpvOpSubgroupImageMediaBlockWriteINTEL = 5581,
    SpvOpUCountLeadingZerosINTEL = 5585,
    SpvOpUCountTrailingZerosINTEL = 5586,
    SpvOpAbsISubINTEL = 5587,
    SpvOpAbsUSubINTEL = 5588,
    SpvOpIAddSatINTEL = 5589,
    SpvOpUAddSatINTEL = 5590,
    SpvOpIAverageINTEL = 5591,
    SpvOpUAverageINTEL = 5592,
    SpvOpIAverageRoundedINTEL = 5593,
    SpvOpUAverageRoundedINTEL = 5594,
    SpvOpISubSatINTEL = 5595,
    SpvOpUSubSatINTEL = 5596,
    SpvOpIMul32x16INTEL = 5597,
    SpvOpUMul32x16INTEL = 5598,
    SpvOpFunctionPointerINTEL = 5600,
    SpvOpFunctionPointerCallINTEL = 5601,
    SpvOpDecorateString = 5632,
    SpvOpDecorateStringGOOGLE = 5632,
    SpvOpMemberDecorateString = 5633,
    SpvOpMemberDecorateStringGOOGLE = 5633,
    SpvOpVmeImageINTEL = 5699,
    SpvOpTypeVmeImageINTEL = 5700,
    SpvOpTypeAvcImePayloadINTEL = 5701,
    SpvOpTypeAvcRefPayloadINTEL = 5702,
    SpvOpTypeAvcSicPayloadINTEL = 5703,
    SpvOpTypeAvcMcePayloadINTEL = 5704,
    SpvOpTypeAvcMceResultINTEL = 5705,
    SpvOpTypeAvcImeResultINTEL = 5706,
    SpvOpTypeAvcImeResultSingleReferenceStreamoutINTEL = 5707,
    SpvOpTypeAvcImeResultDualReferenceStreamoutINTEL = 5708,
    SpvOpTypeAvcImeSingleReferenceStreaminINTEL = 5709,
    SpvOpTypeAvcImeDualReferenceStreaminINTEL = 5710,
    SpvOpTypeAvcRefResultINTEL = 5711,
    SpvOpTypeAvcSicResultINTEL = 5712,
    SpvOpSubgroupAvcMceGetDefaultInterBaseMultiReferencePenaltyINTEL = 5713,
    SpvOpSubgroupAvcMceSetInterBaseMultiReferencePenaltyINTEL = 5714,
    SpvOpSubgroupAvcMceGetDefaultInterShapePenaltyINTEL = 5715,
    SpvOpSubgroupAvcMceSetInterShapePenaltyINTEL = 5716,
    SpvOpSubgroupAvcMceGetDefaultInterDirectionPenaltyINTEL = 5717,
    SpvOpSubgroupAvcMceSetInterDirectionPenaltyINTEL = 5718,
    SpvOpSubgroupAvcMceGetDefaultIntraLumaShapePenaltyINTEL = 5719,
    SpvOpSubgroupAvcMceGetDefaultInterMotionVectorCostTableINTEL = 5720,
    SpvOpSubgroupAvcMceGetDefaultHighPenaltyCostTableINTEL = 5721,
    SpvOpSubgroupAvcMceGetDefaultMediumPenaltyCostTableINTEL = 5722,
    SpvOpSubgroupAvcMceGetDefaultLowPenaltyCostTableINTEL = 5723,
    SpvOpSubgroupAvcMceSetMotionVectorCostFunctionINTEL = 5724,
    SpvOpSubgroupAvcMceGetDefaultIntraLumaModePenaltyINTEL = 5725,
    SpvOpSubgroupAvcMceGetDefaultNonDcLumaIntraPenaltyINTEL = 5726,
    SpvOpSubgroupAvcMceGetDefaultIntraChromaModeBasePenaltyINTEL = 5727,
    SpvOpSubgroupAvcMceSetAcOnlyHaarINTEL = 5728,
    SpvOpSubgroupAvcMceSetSourceInterlacedFieldPolarityINTEL = 5729,
    SpvOpSubgroupAvcMceSetSingleReferenceInterlacedFieldPolarityINTEL = 5730,
    SpvOpSubgroupAvcMceSetDualReferenceInterlacedFieldPolaritiesINTEL = 5731,
    SpvOpSubgroupAvcMceConvertToImePayloadINTEL = 5732,
    SpvOpSubgroupAvcMceConvertToImeResultINTEL = 5733,
    SpvOpSubgroupAvcMceConvertToRefPayloadINTEL = 5734,
    SpvOpSubgroupAvcMceConvertToRefResultINTEL = 5735,
    SpvOpSubgroupAvcMceConvertToSicPayloadINTEL = 5736,
    SpvOpSubgroupAvcMceConvertToSicResultINTEL = 5737,
    SpvOpSubgroupAvcMceGetMotionVectorsINTEL = 5738,
    SpvOpSubgroupAvcMceGetInterDistortionsINTEL = 5739,
    SpvOpSubgroupAvcMceGetBestInterDistortionsINTEL = 5740,
    SpvOpSubgroupAvcMceGetInterMajorShapeINTEL = 5741,
    SpvOpSubgroupAvcMceGetInterMinorShapeINTEL = 5742,
    SpvOpSubgroupAvcMceGetInterDirectionsINTEL = 5743,
    SpvOpSubgroupAvcMceGetInterMotionVectorCountINTEL = 5744,
    SpvOpSubgroupAvcMceGetInterReferenceIdsINTEL = 5745,
    SpvOpSubgroupAvcMceGetInterReferenceInterlacedFieldPolaritiesINTEL = 5746,
    SpvOpSubgroupAvcImeInitializeINTEL = 5747,
    SpvOpSubgroupAvcImeSetSingleReferenceINTEL = 5748,
    SpvOpSubgroupAvcImeSetDualReferenceINTEL = 5749,
    SpvOpSubgroupAvcImeRefWindowSizeINTEL = 5750,
    SpvOpSubgroupAvcImeAdjustRefOffsetINTEL = 5751,
    SpvOpSubgroupAvcImeConvertToMcePayloadINTEL = 5752,
    SpvOpSubgroupAvcImeSetMaxMotionVectorCountINTEL = 5753,
    SpvOpSubgroupAvcImeSetUnidirectionalMixDisableINTEL = 5754,
    SpvOpSubgroupAvcImeSetEarlySearchTerminationThresholdINTEL = 5755,
    SpvOpSubgroupAvcImeSetWeightedSadINTEL = 5756,
    SpvOpSubgroupAvcImeEvaluateWithSingleReferenceINTEL = 5757,
    SpvOpSubgroupAvcImeEvaluateWithDualReferenceINTEL = 5758,
    SpvOpSubgroupAvcImeEvaluateWithSingleReferenceStreaminINTEL = 5759,
    SpvOpSubgroupAvcImeEvaluateWithDualReferenceStreaminINTEL = 5760,
    SpvOpSubgroupAvcImeEvaluateWithSingleReferenceStreamoutINTEL = 5761,
    SpvOpSubgroupAvcImeEvaluateWithDualReferenceStreamoutINTEL = 5762,
    SpvOpSubgroupAvcImeEvaluateWithSingleReferenceStreaminoutINTEL = 5763,
    SpvOpSubgroupAvcImeEvaluateWithDualReferenceStreaminoutINTEL = 5764,
    SpvOpSubgroupAvcImeConvertToMceResultINTEL = 5765,
    SpvOpSubgroupAvcImeGetSingleReferenceStreaminINTEL = 5766,
    SpvOpSubgroupAvcImeGetDualReferenceStreaminINTEL = 5767,
    SpvOpSubgroupAvcImeStripSingleReferenceStreamoutINTEL = 5768,
    SpvOpSubgroupAvcImeStripDualReferenceStreamoutINTEL = 5769,
    SpvOpSubgroupAvcImeGetStreamoutSingleReferenceMajorShapeMotionVectorsINTEL = 5770,
    SpvOpSubgroupAvcImeGetStreamoutSingleReferenceMajorShapeDistortionsINTEL = 5771,
    SpvOpSubgroupAvcImeGetStreamoutSingleReferenceMajorShapeReferenceIdsINTEL = 5772,
    SpvOpSubgroupAvcImeGetStreamoutDualReferenceMajorShapeMotionVectorsINTEL = 5773,
    SpvOpSubgroupAvcImeGetStreamoutDualReferenceMajorShapeDistortionsINTEL = 5774,
    SpvOpSubgroupAvcImeGetStreamoutDualReferenceMajorShapeReferenceIdsINTEL = 5775,
    SpvOpSubgroupAvcImeGetBorderReachedINTEL = 5776,
    SpvOpSubgroupAvcImeGetTruncatedSearchIndicationINTEL = 5777,
    SpvOpSubgroupAvcImeGetUnidirectionalEarlySearchTerminationINTEL = 5778,
    SpvOpSubgroupAvcImeGetWeightingPatternMinimumMotionVectorINTEL = 5779,
    SpvOpSubgroupAvcImeGetWeightingPatternMinimumDistortionINTEL = 5780,
    SpvOpSubgroupAvcFmeInitializeINTEL = 5781,
    SpvOpSubgroupAvcBmeInitializeINTEL = 5782,
    SpvOpSubgroupAvcRefConvertToMcePayloadINTEL = 5783,
    SpvOpSubgroupAvcRefSetBidirectionalMixDisableINTEL = 5784,
    SpvOpSubgroupAvcRefSetBilinearFilterEnableINTEL = 5785,
    SpvOpSubgroupAvcRefEvaluateWithSingleReferenceINTEL = 5786,
    SpvOpSubgroupAvcRefEvaluateWithDualReferenceINTEL = 5787,
    SpvOpSubgroupAvcRefEvaluateWithMultiReferenceINTEL = 5788,
    SpvOpSubgroupAvcRefEvaluateWithMultiReferenceInterlacedINTEL = 5789,
    SpvOpSubgroupAvcRefConvertToMceResultINTEL = 5790,
    SpvOpSubgroupAvcSicInitializeINTEL = 5791,
    SpvOpSubgroupAvcSicConfigureSkcINTEL = 5792,
    SpvOpSubgroupAvcSicConfigureIpeLumaINTEL = 5793,
    SpvOpSubgroupAvcSicConfigureIpeLumaChromaINTEL = 5794,
    SpvOpSubgroupAvcSicGetMotionVectorMaskINTEL = 5795,
    SpvOpSubgroupAvcSicConvertToMcePayloadINTEL = 5796,
    SpvOpSubgroupAvcSicSetIntraLumaShapePenaltyINTEL = 5797,
    SpvOpSubgroupAvcSicSetIntraLumaModeCostFunctionINTEL = 5798,
    SpvOpSubgroupAvcSicSetIntraChromaModeCostFunctionINTEL = 5799,
    SpvOpSubgroupAvcSicSetBilinearFilterEnableINTEL = 5800,
    SpvOpSubgroupAvcSicSetSkcForwardTransformEnableINTEL = 5801,
    SpvOpSubgroupAvcSicSetBlockBasedRawSkipSadINTEL = 5802,
    SpvOpSubgroupAvcSicEvaluateIpeINTEL = 5803,
    SpvOpSubgroupAvcSicEvaluateWithSingleReferenceINTEL = 5804,
    SpvOpSubgroupAvcSicEvaluateWithDualReferenceINTEL = 5805,
    SpvOpSubgroupAvcSicEvaluateWithMultiReferenceINTEL = 5806,
    SpvOpSubgroupAvcSicEvaluateWithMultiReferenceInterlacedINTEL = 5807,
    SpvOpSubgroupAvcSicConvertToMceResultINTEL = 5808,
    SpvOpSubgroupAvcSicGetIpeLumaShapeINTEL = 5809,
    SpvOpSubgroupAvcSicGetBestIpeLumaDistortionINTEL = 5810,
    SpvOpSubgroupAvcSicGetBestIpeChromaDistortionINTEL = 5811,
    SpvOpSubgroupAvcSicGetPackedIpeLumaModesINTEL = 5812,
    SpvOpSubgroupAvcSicGetIpeChromaModeINTEL = 5813,
    SpvOpSubgroupAvcSicGetPackedSkcLumaCountThresholdINTEL = 5814,
    SpvOpSubgroupAvcSicGetPackedSkcLumaSumThresholdINTEL = 5815,
    SpvOpSubgroupAvcSicGetInterRawSadsINTEL = 5816,
    SpvOpLoopControlINTEL = 5887,
    SpvOpReadPipeBlockingINTEL = 5946,
    SpvOpWritePipeBlockingINTEL = 5947,
    SpvOpFPGARegINTEL = 5949,
    SpvOpRayQueryGetRayTMinKHR = 6016,
    SpvOpRayQueryGetRayFlagsKHR = 6017,
    SpvOpRayQueryGetIntersectionTKHR = 6018,
    SpvOpRayQueryGetIntersectionInstanceCustomIndexKHR = 6019,
    SpvOpRayQueryGetIntersectionInstanceIdKHR = 6020,
    SpvOpRayQueryGetIntersectionInstanceShaderBindingTableRecordOffsetKHR = 6021,
    SpvOpRayQueryGetIntersectionGeometryIndexKHR = 6022,
    SpvOpRayQueryGetIntersectionPrimitiveIndexKHR = 6023,
    SpvOpRayQueryGetIntersectionBarycentricsKHR = 6024,
    SpvOpRayQueryGetIntersectionFrontFaceKHR = 6025,
    SpvOpRayQueryGetIntersectionCandidateAABBOpaqueKHR = 6026,
    SpvOpRayQueryGetIntersectionObjectRayDirectionKHR = 6027,
    SpvOpRayQueryGetIntersectionObjectRayOriginKHR = 6028,
    SpvOpRayQueryGetWorldRayDirectionKHR = 6029,
    SpvOpRayQueryGetWorldRayOriginKHR = 6030,
    SpvOpRayQueryGetIntersectionObjectToWorldKHR = 6031,
    SpvOpRayQueryGetIntersectionWorldToObjectKHR = 6032,
    SpvOpAtomicFAddEXT = 6035,
    SpvOpMax = 0x7fffffff,
};

std::string svOpCodeName(SpvOp opcode)
{
    switch(opcode)
    {
             OpCodeCase(SpvOpNop); 
             OpCodeCase(SpvOpUndef); 
             OpCodeCase(SpvOpSourceContinued); 
             OpCodeCase(SpvOpSource); 
             OpCodeCase(SpvOpSourceExtension); 
             OpCodeCase(SpvOpName); 
             OpCodeCase(SpvOpMemberName); 
             OpCodeCase(SpvOpString); 
             OpCodeCase(SpvOpLine); 
             OpCodeCase(SpvOpExtension); 
             OpCodeCase(SpvOpExtInstImport); 
             OpCodeCase(SpvOpExtInst); 
             OpCodeCase(SpvOpMemoryModel); 
             OpCodeCase(SpvOpEntryPoint); 
             OpCodeCase(SpvOpExecutionMode); 
             OpCodeCase(SpvOpCapability); 
             OpCodeCase(SpvOpTypeVoid); 
             OpCodeCase(SpvOpTypeBool); 
             OpCodeCase(SpvOpTypeInt); 
             OpCodeCase(SpvOpTypeFloat); 
             OpCodeCase(SpvOpTypeVector); 
             OpCodeCase(SpvOpTypeMatrix); 
             OpCodeCase(SpvOpTypeImage); 
             OpCodeCase(SpvOpTypeSampler); 
             OpCodeCase(SpvOpTypeSampledImage); 
             OpCodeCase(SpvOpTypeArray); 
             OpCodeCase(SpvOpTypeRuntimeArray); 
             OpCodeCase(SpvOpTypeStruct); 
             OpCodeCase(SpvOpTypeOpaque); 
             OpCodeCase(SpvOpTypePointer); 
             OpCodeCase(SpvOpTypeFunction); 
             OpCodeCase(SpvOpTypeEvent); 
             OpCodeCase(SpvOpTypeDeviceEvent); 
             OpCodeCase(SpvOpTypeReserveId); 
             OpCodeCase(SpvOpTypeQueue); 
             OpCodeCase(SpvOpTypePipe); 
             OpCodeCase(SpvOpTypeForwardPointer); 
             OpCodeCase(SpvOpConstantTrue); 
             OpCodeCase(SpvOpConstantFalse); 
             OpCodeCase(SpvOpConstant); 
             OpCodeCase(SpvOpConstantComposite); 
             OpCodeCase(SpvOpConstantSampler); 
             OpCodeCase(SpvOpConstantNull); 
             OpCodeCase(SpvOpSpecConstantTrue); 
             OpCodeCase(SpvOpSpecConstantFalse); 
             OpCodeCase(SpvOpSpecConstant); 
             OpCodeCase(SpvOpSpecConstantComposite); 
             OpCodeCase(SpvOpSpecConstantOp); 
             OpCodeCase(SpvOpFunction); 
             OpCodeCase(SpvOpFunctionParameter); 
             OpCodeCase(SpvOpFunctionEnd); 
             OpCodeCase(SpvOpFunctionCall); 
             OpCodeCase(SpvOpVariable); 
             OpCodeCase(SpvOpImageTexelPointer); 
             OpCodeCase(SpvOpLoad); 
             OpCodeCase(SpvOpStore); 
             OpCodeCase(SpvOpCopyMemory); 
             OpCodeCase(SpvOpCopyMemorySized); 
             OpCodeCase(SpvOpAccessChain); 
             OpCodeCase(SpvOpInBoundsAccessChain); 
             OpCodeCase(SpvOpPtrAccessChain); 
             OpCodeCase(SpvOpArrayLength); 
             OpCodeCase(SpvOpGenericPtrMemSemantics); 
             OpCodeCase(SpvOpInBoundsPtrAccessChain); 
             OpCodeCase(SpvOpDecorate); 
             OpCodeCase(SpvOpMemberDecorate); 
             OpCodeCase(SpvOpDecorationGroup); 
             OpCodeCase(SpvOpGroupDecorate); 
             OpCodeCase(SpvOpGroupMemberDecorate); 
             OpCodeCase(SpvOpVectorExtractDynamic); 
             OpCodeCase(SpvOpVectorInsertDynamic); 
             OpCodeCase(SpvOpVectorShuffle); 
             OpCodeCase(SpvOpCompositeConstruct); 
             OpCodeCase(SpvOpCompositeExtract); 
             OpCodeCase(SpvOpCompositeInsert); 
             OpCodeCase(SpvOpCopyObject); 
             OpCodeCase(SpvOpTranspose); 
             OpCodeCase(SpvOpSampledImage); 
             OpCodeCase(SpvOpImageSampleImplicitLod); 
             OpCodeCase(SpvOpImageSampleExplicitLod); 
             OpCodeCase(SpvOpImageSampleDrefImplicitLod); 
             OpCodeCase(SpvOpImageSampleDrefExplicitLod); 
             OpCodeCase(SpvOpImageSampleProjImplicitLod); 
             OpCodeCase(SpvOpImageSampleProjExplicitLod); 
             OpCodeCase(SpvOpImageSampleProjDrefImplicitLod); 
             OpCodeCase(SpvOpImageSampleProjDrefExplicitLod); 
             OpCodeCase(SpvOpImageFetch); 
             OpCodeCase(SpvOpImageGather); 
             OpCodeCase(SpvOpImageDrefGather); 
             OpCodeCase(SpvOpImageRead); 
             OpCodeCase(SpvOpImageWrite); 
             OpCodeCase(SpvOpImage); 
             OpCodeCase(SpvOpImageQueryFormat); 
             OpCodeCase(SpvOpImageQueryOrder); 
             OpCodeCase(SpvOpImageQuerySizeLod); 
             OpCodeCase(SpvOpImageQuerySize); 
             OpCodeCase(SpvOpImageQueryLod); 
             OpCodeCase(SpvOpImageQueryLevels); 
             OpCodeCase(SpvOpImageQuerySamples); 
             OpCodeCase(SpvOpConvertFToU); 
             OpCodeCase(SpvOpConvertFToS); 
             OpCodeCase(SpvOpConvertSToF); 
             OpCodeCase(SpvOpConvertUToF); 
             OpCodeCase(SpvOpUConvert); 
             OpCodeCase(SpvOpSConvert); 
             OpCodeCase(SpvOpFConvert); 
             //OpCodeCase(SpvOpQuantizeToF); 
             OpCodeCase(SpvOpConvertPtrToU); 
             OpCodeCase(SpvOpSatConvertSToU); 
             OpCodeCase(SpvOpSatConvertUToS); 
             OpCodeCase(SpvOpConvertUToPtr); 
             OpCodeCase(SpvOpPtrCastToGeneric); 
             OpCodeCase(SpvOpGenericCastToPtr); 
             OpCodeCase(SpvOpGenericCastToPtrExplicit); 
             OpCodeCase(SpvOpBitcast); 
             OpCodeCase(SpvOpSNegate); 
             OpCodeCase(SpvOpFNegate); 
             OpCodeCase(SpvOpIAdd); 
             OpCodeCase(SpvOpFAdd); 
             OpCodeCase(SpvOpISub); 
             OpCodeCase(SpvOpFSub); 
             OpCodeCase(SpvOpIMul); 
             OpCodeCase(SpvOpFMul); 
             OpCodeCase(SpvOpUDiv); 
             OpCodeCase(SpvOpSDiv); 
             OpCodeCase(SpvOpFDiv); 
             OpCodeCase(SpvOpUMod); 
             OpCodeCase(SpvOpSRem); 
             OpCodeCase(SpvOpSMod); 
             OpCodeCase(SpvOpFRem); 
             OpCodeCase(SpvOpFMod); 
             OpCodeCase(SpvOpVectorTimesScalar); 
             OpCodeCase(SpvOpMatrixTimesScalar); 
             OpCodeCase(SpvOpVectorTimesMatrix); 
             OpCodeCase(SpvOpMatrixTimesVector); 
             OpCodeCase(SpvOpMatrixTimesMatrix); 
             OpCodeCase(SpvOpOuterProduct); 
             OpCodeCase(SpvOpDot); 
             OpCodeCase(SpvOpIAddCarry); 
             OpCodeCase(SpvOpISubBorrow); 
             OpCodeCase(SpvOpUMulExtended); 
             OpCodeCase(SpvOpSMulExtended); 
             OpCodeCase(SpvOpAny); 
             OpCodeCase(SpvOpAll); 
             OpCodeCase(SpvOpIsNan); 
             OpCodeCase(SpvOpIsInf); 
             OpCodeCase(SpvOpIsFinite); 
             OpCodeCase(SpvOpIsNormal); 
             OpCodeCase(SpvOpSignBitSet); 
             OpCodeCase(SpvOpLessOrGreater); 
             OpCodeCase(SpvOpOrdered); 
             OpCodeCase(SpvOpUnordered); 
             OpCodeCase(SpvOpLogicalEqual); 
             OpCodeCase(SpvOpLogicalNotEqual); 
             OpCodeCase(SpvOpLogicalOr); 
             OpCodeCase(SpvOpLogicalAnd); 
             OpCodeCase(SpvOpLogicalNot); 
             OpCodeCase(SpvOpSelect); 
             OpCodeCase(SpvOpIEqual); 
             OpCodeCase(SpvOpINotEqual); 
             OpCodeCase(SpvOpUGreaterThan); 
             OpCodeCase(SpvOpSGreaterThan); 
             OpCodeCase(SpvOpUGreaterThanEqual); 
             OpCodeCase(SpvOpSGreaterThanEqual); 
             OpCodeCase(SpvOpULessThan); 
             OpCodeCase(SpvOpSLessThan); 
             OpCodeCase(SpvOpULessThanEqual); 
             OpCodeCase(SpvOpSLessThanEqual); 
             OpCodeCase(SpvOpFOrdEqual); 
             OpCodeCase(SpvOpFUnordEqual); 
             OpCodeCase(SpvOpFOrdNotEqual); 
             OpCodeCase(SpvOpFUnordNotEqual); 
             OpCodeCase(SpvOpFOrdLessThan); 
             OpCodeCase(SpvOpFUnordLessThan); 
             OpCodeCase(SpvOpFOrdGreaterThan); 
             OpCodeCase(SpvOpFUnordGreaterThan); 
             OpCodeCase(SpvOpFOrdLessThanEqual); 
             OpCodeCase(SpvOpFUnordLessThanEqual); 
             OpCodeCase(SpvOpFOrdGreaterThanEqual); 
             OpCodeCase(SpvOpFUnordGreaterThanEqual); 
             OpCodeCase(SpvOpShiftRightLogical); 
             OpCodeCase(SpvOpShiftRightArithmetic); 
             OpCodeCase(SpvOpShiftLeftLogical); 
             OpCodeCase(SpvOpBitwiseOr); 
             OpCodeCase(SpvOpBitwiseXor); 
             OpCodeCase(SpvOpBitwiseAnd); 
             OpCodeCase(SpvOpNot); 
             OpCodeCase(SpvOpBitFieldInsert); 
             OpCodeCase(SpvOpBitFieldSExtract); 
             OpCodeCase(SpvOpBitFieldUExtract); 
             OpCodeCase(SpvOpBitReverse); 
             OpCodeCase(SpvOpBitCount); 
             OpCodeCase(SpvOpDPdx); 
             OpCodeCase(SpvOpDPdy); 
             OpCodeCase(SpvOpFwidth); 
             OpCodeCase(SpvOpDPdxFine); 
             OpCodeCase(SpvOpDPdyFine); 
             OpCodeCase(SpvOpFwidthFine); 
             OpCodeCase(SpvOpDPdxCoarse); 
             OpCodeCase(SpvOpDPdyCoarse); 
             OpCodeCase(SpvOpFwidthCoarse); 
             OpCodeCase(SpvOpEmitVertex); 
             OpCodeCase(SpvOpEndPrimitive); 
             OpCodeCase(SpvOpEmitStreamVertex); 
             OpCodeCase(SpvOpEndStreamPrimitive); 
             OpCodeCase(SpvOpControlBarrier); 
             OpCodeCase(SpvOpMemoryBarrier); 
             OpCodeCase(SpvOpAtomicLoad); 
             OpCodeCase(SpvOpAtomicStore); 
             OpCodeCase(SpvOpAtomicExchange); 
             OpCodeCase(SpvOpAtomicCompareExchange); 
             OpCodeCase(SpvOpAtomicCompareExchangeWeak); 
             OpCodeCase(SpvOpAtomicIIncrement); 
             OpCodeCase(SpvOpAtomicIDecrement); 
             OpCodeCase(SpvOpAtomicIAdd); 
             OpCodeCase(SpvOpAtomicISub); 
             OpCodeCase(SpvOpAtomicSMin); 
             OpCodeCase(SpvOpAtomicUMin); 
             OpCodeCase(SpvOpAtomicSMax); 
             OpCodeCase(SpvOpAtomicUMax); 
             OpCodeCase(SpvOpAtomicAnd); 
             OpCodeCase(SpvOpAtomicOr); 
             OpCodeCase(SpvOpAtomicXor); 
             OpCodeCase(SpvOpPhi); 
             OpCodeCase(SpvOpLoopMerge); 
             OpCodeCase(SpvOpSelectionMerge); 
             OpCodeCase(SpvOpLabel); 
             OpCodeCase(SpvOpBranch); 
             OpCodeCase(SpvOpBranchConditional); 
             OpCodeCase(SpvOpSwitch); 
             OpCodeCase(SpvOpKill); 
             OpCodeCase(SpvOpReturn); 
             OpCodeCase(SpvOpReturnValue); 
             OpCodeCase(SpvOpUnreachable); 
             OpCodeCase(SpvOpLifetimeStart); 
             OpCodeCase(SpvOpLifetimeStop); 
             OpCodeCase(SpvOpGroupAsyncCopy); 
             OpCodeCase(SpvOpGroupWaitEvents); 
             OpCodeCase(SpvOpGroupAll); 
             OpCodeCase(SpvOpGroupAny); 
             OpCodeCase(SpvOpGroupBroadcast); 
             OpCodeCase(SpvOpGroupIAdd); 
             OpCodeCase(SpvOpGroupFAdd); 
             OpCodeCase(SpvOpGroupFMin); 
             OpCodeCase(SpvOpGroupUMin); 
             OpCodeCase(SpvOpGroupSMin); 
             OpCodeCase(SpvOpGroupFMax); 
             OpCodeCase(SpvOpGroupUMax); 
             OpCodeCase(SpvOpGroupSMax); 
             OpCodeCase(SpvOpReadPipe); 
             OpCodeCase(SpvOpWritePipe); 
             OpCodeCase(SpvOpReservedReadPipe); 
             OpCodeCase(SpvOpReservedWritePipe); 
             OpCodeCase(SpvOpReserveReadPipePackets); 
             OpCodeCase(SpvOpReserveWritePipePackets); 
             OpCodeCase(SpvOpCommitReadPipe); 
             OpCodeCase(SpvOpCommitWritePipe); 
             OpCodeCase(SpvOpIsValidReserveId); 
             OpCodeCase(SpvOpGetNumPipePackets); 
             OpCodeCase(SpvOpGetMaxPipePackets); 
             OpCodeCase(SpvOpGroupReserveReadPipePackets); 
             OpCodeCase(SpvOpGroupReserveWritePipePackets); 
             OpCodeCase(SpvOpGroupCommitReadPipe); 
             OpCodeCase(SpvOpGroupCommitWritePipe); 
             OpCodeCase(SpvOpEnqueueMarker); 
             OpCodeCase(SpvOpEnqueueKernel); 
             OpCodeCase(SpvOpGetKernelNDrangeSubGroupCount); 
             OpCodeCase(SpvOpGetKernelNDrangeMaxSubGroupSize); 
             OpCodeCase(SpvOpGetKernelWorkGroupSize); 
             OpCodeCase(SpvOpGetKernelPreferredWorkGroupSizeMultiple); 
             OpCodeCase(SpvOpRetainEvent); 
             OpCodeCase(SpvOpReleaseEvent); 
             OpCodeCase(SpvOpCreateUserEvent); 
             OpCodeCase(SpvOpIsValidEvent); 
             OpCodeCase(SpvOpSetUserEventStatus); 
             OpCodeCase(SpvOpCaptureEventProfilingInfo); 
             OpCodeCase(SpvOpGetDefaultQueue); 
             OpCodeCase(SpvOpBuildNDRange); 
             OpCodeCase(SpvOpImageSparseSampleImplicitLod); 
             OpCodeCase(SpvOpImageSparseSampleExplicitLod); 
             OpCodeCase(SpvOpImageSparseSampleDrefImplicitLod); 
             OpCodeCase(SpvOpImageSparseSampleDrefExplicitLod); 
             OpCodeCase(SpvOpImageSparseSampleProjImplicitLod); 
             OpCodeCase(SpvOpImageSparseSampleProjExplicitLod); 
             OpCodeCase(SpvOpImageSparseSampleProjDrefImplicitLod); 
             OpCodeCase(SpvOpImageSparseSampleProjDrefExplicitLod); 
             OpCodeCase(SpvOpImageSparseFetch); 
             OpCodeCase(SpvOpImageSparseGather); 
             OpCodeCase(SpvOpImageSparseDrefGather); 
             OpCodeCase(SpvOpImageSparseTexelsResident); 
             OpCodeCase(SpvOpNoLine); 
             OpCodeCase(SpvOpAtomicFlagTestAndSet); 
             OpCodeCase(SpvOpAtomicFlagClear); 
             OpCodeCase(SpvOpImageSparseRead); 
             OpCodeCase(SpvOpSizeOf); 
             OpCodeCase(SpvOpTypePipeStorage); 
             OpCodeCase(SpvOpConstantPipeStorage); 
             OpCodeCase(SpvOpCreatePipeFromPipeStorage); 
             OpCodeCase(SpvOpGetKernelLocalSizeForSubgroupCount); 
             OpCodeCase(SpvOpGetKernelMaxNumSubgroups); 
             OpCodeCase(SpvOpTypeNamedBarrier); 
             OpCodeCase(SpvOpNamedBarrierInitialize); 
             OpCodeCase(SpvOpMemoryNamedBarrier); 
             OpCodeCase(SpvOpModuleProcessed); 
             OpCodeCase(SpvOpExecutionModeId); 
             OpCodeCase(SpvOpDecorateId); 
             OpCodeCase(SpvOpGroupNonUniformElect); 
             OpCodeCase(SpvOpGroupNonUniformAll); 
             OpCodeCase(SpvOpGroupNonUniformAny); 
             OpCodeCase(SpvOpGroupNonUniformAllEqual); 
             OpCodeCase(SpvOpGroupNonUniformBroadcast); 
             OpCodeCase(SpvOpGroupNonUniformBroadcastFirst); 
             OpCodeCase(SpvOpGroupNonUniformBallot); 
             OpCodeCase(SpvOpGroupNonUniformInverseBallot); 
             OpCodeCase(SpvOpGroupNonUniformBallotBitExtract); 
             OpCodeCase(SpvOpGroupNonUniformBallotBitCount); 
             OpCodeCase(SpvOpGroupNonUniformBallotFindLSB); 
             OpCodeCase(SpvOpGroupNonUniformBallotFindMSB); 
             OpCodeCase(SpvOpGroupNonUniformShuffle); 
             OpCodeCase(SpvOpGroupNonUniformShuffleXor); 
             OpCodeCase(SpvOpGroupNonUniformShuffleUp); 
             OpCodeCase(SpvOpGroupNonUniformShuffleDown); 
             OpCodeCase(SpvOpGroupNonUniformIAdd); 
             OpCodeCase(SpvOpGroupNonUniformFAdd); 
             OpCodeCase(SpvOpGroupNonUniformIMul); 
             OpCodeCase(SpvOpGroupNonUniformFMul); 
             OpCodeCase(SpvOpGroupNonUniformSMin); 
             OpCodeCase(SpvOpGroupNonUniformUMin); 
             OpCodeCase(SpvOpGroupNonUniformFMin); 
             OpCodeCase(SpvOpGroupNonUniformSMax); 
             OpCodeCase(SpvOpGroupNonUniformUMax); 
             OpCodeCase(SpvOpGroupNonUniformFMax); 
             OpCodeCase(SpvOpGroupNonUniformBitwiseAnd); 
             OpCodeCase(SpvOpGroupNonUniformBitwiseOr); 
             OpCodeCase(SpvOpGroupNonUniformBitwiseXor); 
             OpCodeCase(SpvOpGroupNonUniformLogicalAnd); 
             OpCodeCase(SpvOpGroupNonUniformLogicalOr); 
             OpCodeCase(SpvOpGroupNonUniformLogicalXor); 
             OpCodeCase(SpvOpGroupNonUniformQuadBroadcast); 
             OpCodeCase(SpvOpGroupNonUniformQuadSwap); 
             OpCodeCase(SpvOpCopyLogical); 
             OpCodeCase(SpvOpPtrEqual); 
             OpCodeCase(SpvOpPtrNotEqual); 
             OpCodeCase(SpvOpPtrDiff); 
             OpCodeCase(SpvOpTerminateInvocation); 
             OpCodeCase(SpvOpSubgroupBallotKHR); 
             OpCodeCase(SpvOpSubgroupFirstInvocationKHR); 
             OpCodeCase(SpvOpSubgroupAllKHR); 
             OpCodeCase(SpvOpSubgroupAnyKHR); 
             OpCodeCase(SpvOpSubgroupAllEqualKHR); 
             OpCodeCase(SpvOpSubgroupReadInvocationKHR); 
             OpCodeCase(SpvOpTraceRayKHR); 
             OpCodeCase(SpvOpExecuteCallableKHR); 
             OpCodeCase(SpvOpConvertUToAccelerationStructureKHR); 
             OpCodeCase(SpvOpIgnoreIntersectionKHR); 
             OpCodeCase(SpvOpTerminateRayKHR); 
             OpCodeCase(SpvOpTypeRayQueryKHR); 
             OpCodeCase(SpvOpRayQueryInitializeKHR); 
             OpCodeCase(SpvOpRayQueryTerminateKHR); 
             OpCodeCase(SpvOpRayQueryGenerateIntersectionKHR); 
             OpCodeCase(SpvOpRayQueryConfirmIntersectionKHR); 
             OpCodeCase(SpvOpRayQueryProceedKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionTypeKHR); 
             OpCodeCase(SpvOpGroupIAddNonUniformAMD); 
             OpCodeCase(SpvOpGroupFAddNonUniformAMD); 
             OpCodeCase(SpvOpGroupFMinNonUniformAMD); 
             OpCodeCase(SpvOpGroupUMinNonUniformAMD); 
             OpCodeCase(SpvOpGroupSMinNonUniformAMD); 
             OpCodeCase(SpvOpGroupFMaxNonUniformAMD); 
             OpCodeCase(SpvOpGroupUMaxNonUniformAMD); 
             OpCodeCase(SpvOpGroupSMaxNonUniformAMD); 
             OpCodeCase(SpvOpFragmentMaskFetchAMD); 
             OpCodeCase(SpvOpFragmentFetchAMD); 
             OpCodeCase(SpvOpReadClockKHR); 
             OpCodeCase(SpvOpImageSampleFootprintNV); 
             OpCodeCase(SpvOpGroupNonUniformPartitionNV); 
             //OpCodeCase(SpvOpWritePackedPrimitiveIndicesxNV); 
             OpCodeCase(SpvOpReportIntersectionKHR); 
             //OpCodeCase(SpvOpReportIntersectionNV); 
             OpCodeCase(SpvOpIgnoreIntersectionNV); 
             OpCodeCase(SpvOpTerminateRayNV); 
             OpCodeCase(SpvOpTraceNV); 
             OpCodeCase(SpvOpTypeAccelerationStructureKHR); 
             //OpCodeCase(SpvOpTypeAccelerationStructureNV); 
             OpCodeCase(SpvOpExecuteCallableNV); 
             OpCodeCase(SpvOpTypeCooperativeMatrixNV); 
             OpCodeCase(SpvOpCooperativeMatrixLoadNV); 
             OpCodeCase(SpvOpCooperativeMatrixStoreNV); 
             OpCodeCase(SpvOpCooperativeMatrixMulAddNV); 
             OpCodeCase(SpvOpCooperativeMatrixLengthNV); 
             OpCodeCase(SpvOpBeginInvocationInterlockEXT); 
             OpCodeCase(SpvOpEndInvocationInterlockEXT); 
             OpCodeCase(SpvOpDemoteToHelperInvocationEXT); 
             OpCodeCase(SpvOpIsHelperInvocationEXT); 
             OpCodeCase(SpvOpSubgroupShuffleINTEL); 
             OpCodeCase(SpvOpSubgroupShuffleDownINTEL); 
             OpCodeCase(SpvOpSubgroupShuffleUpINTEL); 
             OpCodeCase(SpvOpSubgroupShuffleXorINTEL); 
             OpCodeCase(SpvOpSubgroupBlockReadINTEL); 
             OpCodeCase(SpvOpSubgroupBlockWriteINTEL); 
             OpCodeCase(SpvOpSubgroupImageBlockReadINTEL); 
             OpCodeCase(SpvOpSubgroupImageBlockWriteINTEL); 
             OpCodeCase(SpvOpSubgroupImageMediaBlockReadINTEL); 
             OpCodeCase(SpvOpSubgroupImageMediaBlockWriteINTEL); 
             OpCodeCase(SpvOpUCountLeadingZerosINTEL); 
             OpCodeCase(SpvOpUCountTrailingZerosINTEL); 
             OpCodeCase(SpvOpAbsISubINTEL); 
             OpCodeCase(SpvOpAbsUSubINTEL); 
             OpCodeCase(SpvOpIAddSatINTEL); 
             OpCodeCase(SpvOpUAddSatINTEL); 
             OpCodeCase(SpvOpIAverageINTEL); 
             OpCodeCase(SpvOpUAverageINTEL); 
             OpCodeCase(SpvOpIAverageRoundedINTEL); 
             OpCodeCase(SpvOpUAverageRoundedINTEL); 
             OpCodeCase(SpvOpISubSatINTEL); 
             OpCodeCase(SpvOpUSubSatINTEL); 
             //OpCodeCase(SpvOpIMulxINTEL); 
             //OpCodeCase(SpvOpUMulxINTEL); 
             OpCodeCase(SpvOpFunctionPointerINTEL); 
             OpCodeCase(SpvOpFunctionPointerCallINTEL); 
             OpCodeCase(SpvOpDecorateString); 
             //OpCodeCase(SpvOpDecorateStringGOOGLE); 
             OpCodeCase(SpvOpMemberDecorateString); 
             //OpCodeCase(SpvOpMemberDecorateStringGOOGLE); 
             OpCodeCase(SpvOpVmeImageINTEL); 
             OpCodeCase(SpvOpTypeVmeImageINTEL); 
             OpCodeCase(SpvOpTypeAvcImePayloadINTEL); 
             OpCodeCase(SpvOpTypeAvcRefPayloadINTEL); 
             OpCodeCase(SpvOpTypeAvcSicPayloadINTEL); 
             OpCodeCase(SpvOpTypeAvcMcePayloadINTEL); 
             OpCodeCase(SpvOpTypeAvcMceResultINTEL); 
             OpCodeCase(SpvOpTypeAvcImeResultINTEL); 
             OpCodeCase(SpvOpTypeAvcImeResultSingleReferenceStreamoutINTEL); 
             OpCodeCase(SpvOpTypeAvcImeResultDualReferenceStreamoutINTEL); 
             OpCodeCase(SpvOpTypeAvcImeSingleReferenceStreaminINTEL); 
             OpCodeCase(SpvOpTypeAvcImeDualReferenceStreaminINTEL); 
             OpCodeCase(SpvOpTypeAvcRefResultINTEL); 
             OpCodeCase(SpvOpTypeAvcSicResultINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultInterBaseMultiReferencePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetInterBaseMultiReferencePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultInterShapePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetInterShapePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultInterDirectionPenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetInterDirectionPenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultIntraLumaShapePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultInterMotionVectorCostTableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultHighPenaltyCostTableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultMediumPenaltyCostTableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultLowPenaltyCostTableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetMotionVectorCostFunctionINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultIntraLumaModePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultNonDcLumaIntraPenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetDefaultIntraChromaModeBasePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetAcOnlyHaarINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetSourceInterlacedFieldPolarityINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetSingleReferenceInterlacedFieldPolarityINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceSetDualReferenceInterlacedFieldPolaritiesINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceConvertToImePayloadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceConvertToImeResultINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceConvertToRefPayloadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceConvertToRefResultINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceConvertToSicPayloadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceConvertToSicResultINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetMotionVectorsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetInterDistortionsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetBestInterDistortionsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetInterMajorShapeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetInterMinorShapeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetInterDirectionsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetInterMotionVectorCountINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetInterReferenceIdsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcMceGetInterReferenceInterlacedFieldPolaritiesINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeInitializeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeSetSingleReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeSetDualReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeRefWindowSizeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeAdjustRefOffsetINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeConvertToMcePayloadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeSetMaxMotionVectorCountINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeSetUnidirectionalMixDisableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeSetEarlySearchTerminationThresholdINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeSetWeightedSadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithSingleReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithDualReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithSingleReferenceStreaminINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithDualReferenceStreaminINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithSingleReferenceStreamoutINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithDualReferenceStreamoutINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithSingleReferenceStreaminoutINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeEvaluateWithDualReferenceStreaminoutINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeConvertToMceResultINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetSingleReferenceStreaminINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetDualReferenceStreaminINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeStripSingleReferenceStreamoutINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeStripDualReferenceStreamoutINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetStreamoutSingleReferenceMajorShapeMotionVectorsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetStreamoutSingleReferenceMajorShapeDistortionsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetStreamoutSingleReferenceMajorShapeReferenceIdsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetStreamoutDualReferenceMajorShapeMotionVectorsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetStreamoutDualReferenceMajorShapeDistortionsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetStreamoutDualReferenceMajorShapeReferenceIdsINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetBorderReachedINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetTruncatedSearchIndicationINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetUnidirectionalEarlySearchTerminationINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetWeightingPatternMinimumMotionVectorINTEL); 
             OpCodeCase(SpvOpSubgroupAvcImeGetWeightingPatternMinimumDistortionINTEL); 
             OpCodeCase(SpvOpSubgroupAvcFmeInitializeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcBmeInitializeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefConvertToMcePayloadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefSetBidirectionalMixDisableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefSetBilinearFilterEnableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefEvaluateWithSingleReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefEvaluateWithDualReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefEvaluateWithMultiReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefEvaluateWithMultiReferenceInterlacedINTEL); 
             OpCodeCase(SpvOpSubgroupAvcRefConvertToMceResultINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicInitializeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicConfigureSkcINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicConfigureIpeLumaINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicConfigureIpeLumaChromaINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetMotionVectorMaskINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicConvertToMcePayloadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicSetIntraLumaShapePenaltyINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicSetIntraLumaModeCostFunctionINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicSetIntraChromaModeCostFunctionINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicSetBilinearFilterEnableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicSetSkcForwardTransformEnableINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicSetBlockBasedRawSkipSadINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicEvaluateIpeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicEvaluateWithSingleReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicEvaluateWithDualReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicEvaluateWithMultiReferenceINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicEvaluateWithMultiReferenceInterlacedINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicConvertToMceResultINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetIpeLumaShapeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetBestIpeLumaDistortionINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetBestIpeChromaDistortionINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetPackedIpeLumaModesINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetIpeChromaModeINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetPackedSkcLumaCountThresholdINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetPackedSkcLumaSumThresholdINTEL); 
             OpCodeCase(SpvOpSubgroupAvcSicGetInterRawSadsINTEL); 
             OpCodeCase(SpvOpLoopControlINTEL); 
             OpCodeCase(SpvOpReadPipeBlockingINTEL); 
             OpCodeCase(SpvOpWritePipeBlockingINTEL); 
             OpCodeCase(SpvOpFPGARegINTEL); 
             OpCodeCase(SpvOpRayQueryGetRayTMinKHR); 
             OpCodeCase(SpvOpRayQueryGetRayFlagsKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionTKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionInstanceCustomIndexKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionInstanceIdKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionInstanceShaderBindingTableRecordOffsetKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionGeometryIndexKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionPrimitiveIndexKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionBarycentricsKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionFrontFaceKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionCandidateAABBOpaqueKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionObjectRayDirectionKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionObjectRayOriginKHR); 
             OpCodeCase(SpvOpRayQueryGetWorldRayDirectionKHR); 
             OpCodeCase(SpvOpRayQueryGetWorldRayOriginKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionObjectToWorldKHR); 
             OpCodeCase(SpvOpRayQueryGetIntersectionWorldToObjectKHR); 
             OpCodeCase(SpvOpAtomicFAddEXT); 
             OpCodeCase(SpvOpMax);
    }
}