package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.*;
import com.sun.jna.ptr.*;
import org.jetbrains.annotations.*;

import java.nio.file.*;
import java.util.*;

/**
 * LLVM C interface functions mapped for LLVM-18 using JNA.
 */
public class Llvm {
    static final String LLVM_DIR_SYSTEM_PROPERTY = "emerge.backend.llvm.llvm-18-dir";
    public static final Path LLVM_DIR = Paths.get(Objects.requireNonNull(
            System.getProperty(LLVM_DIR_SYSTEM_PROPERTY),
            "You must specify the Java system property " + LLVM_DIR_SYSTEM_PROPERTY
    )).toAbsolutePath();

    static {
        NativeLibrary.addSearchPath("LLVM-18", LLVM_DIR.resolve("lib").toString());
        NativeLibrary.addSearchPath("LLVM-C", LLVM_DIR.resolve("bin").toString());
        Map<String, Object> options = Map.of(
                Library.OPTION_TYPE_MAPPER, new LlvmTypeMapper()
        );
        NativeLibrary llvmLib;
        try {
            llvmLib = NativeLibrary.getInstance("LLVM-18", options);
        }
        catch (UnsatisfiedLinkError ex) {
            try {
                llvmLib = NativeLibrary.getInstance("LLVM-C", options);
            }
            catch (UnsatisfiedLinkError ex2) {
                ex.addSuppressed(ex2);
                throw ex;
            }
        }
        Native.register(llvmLib);
    }

    public static native void LLVMGetVersion(@NotNull @Unsigned IntByReference major, @NotNull @Unsigned IntByReference minor, @NotNull @Unsigned IntByReference path);

    /** see Core.h */
    public static native @NotNull LlvmContextRef LLVMContextCreate();

    /** see Core.h */
    public static native void LLVMContextDispose(@NotNull LlvmContextRef context);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMVoidTypeInContext(@NotNull LlvmContextRef context);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMPointerTypeInContext(@NotNull LlvmContextRef context, @Unsigned int addressSpace);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMIntTypeInContext(@NotNull LlvmContextRef context, @Unsigned int numBits);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMStructTypeInContext(@NotNull LlvmContextRef context, @NotNull NativePointerArray<LlvmTypeRef> elementTypes, @ArraySizeOf("elementTypes") int elementCount, @LlvmBool int packed);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMStructCreateNamed(@NotNull LlvmContextRef context, String name);

    /** see Core.h */
    public static native void LLVMStructSetBody(@NotNull LlvmTypeRef structTy, @NotNull NativePointerArray<LlvmTypeRef> elementTypes, @ArraySizeOf("elementTypes") int elementCount, @LlvmBool int packed);

    /** see Core.h */
    public static native @Unsigned int LLVMCountStructElementTypes(@NotNull LlvmTypeRef structTy);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMArrayType2(@NotNull LlvmTypeRef elementType, @Unsigned long elementCount);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMFunctionType(@NotNull LlvmTypeRef returnType, @NotNull NativePointerArray<LlvmTypeRef> paramTypes, @ArraySizeOf("paramTypes") int paramCount, @LlvmBool int isVarArg);

    /** see Target.h */
    public static native @Unsigned long LLVMSizeOfTypeInBits(@NotNull LlvmTargetDataRef targetData, @NotNull LlvmTypeRef type);

    public static native @Unsigned int LLVMGetIntTypeWidth(@NotNull LlvmTypeRef intType);

    /** see Core.h */
    public static native @NotNull LlvmTypeKind LLVMGetTypeKind(@NotNull LlvmTypeRef value);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMConstNull(@NotNull LlvmTypeRef type);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMGetUndef(@NotNull LlvmTypeRef type);

    public static native @NotNull LlvmValueRef LLVMConstInt(@NotNull LlvmTypeRef type, long value, @LlvmBool int signExtend);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMConstStructInContext(@NotNull LlvmContextRef context, @NotNull NativePointerArray<LlvmValueRef> constantVals, @ArraySizeOf("constantVals") int count, @LlvmBool int packed);

    public static native @NotNull LlvmValueRef LLVMConstNamedStruct(@NotNull LlvmTypeRef structType, @NotNull NativePointerArray<LlvmValueRef> constantVals, @ArraySizeOf("constantVals") int count);

    public static native @NotNull LlvmValueRef LLVMConstArray2(@NotNull LlvmTypeRef elementType, @NotNull NativePointerArray<LlvmValueRef> values, @ArraySizeOf("values") long length);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMTypeOf(@NotNull LlvmValueRef value);

    /** see Core.h */
    public static native @NotNull LlvmContextRef LLVMGetTypeContext(@NotNull LlvmTypeRef type);

    /** see Core.h */
    public static native @NotNull LlvmMessage LLVMPrintTypeToString(@NotNull LlvmTypeRef type);

    /** see Core.h */
    public static native @Nullable LlvmMessage LLVMPrintValueToString(@NotNull LlvmValueRef value);

    /** see Core.h */
    public static native @NotNull LlvmValueKind LLVMGetValueKind(@NotNull LlvmValueRef value);

    /** see Core.h */
    public static native @LlvmBool int LLVMIsConstant(@NotNull LlvmValueRef value);

    /** see Core.h */
    public static native @LlvmBool int LLVMIsLiteralStruct(@NotNull LlvmTypeRef value);

    /** see Core.h */
    public static native @NotNull String LLVMGetStructName(@NotNull LlvmTypeRef type);

    /** see Core.h */
    public static native void LLVMGetStructElementTypes(@NotNull LlvmTypeRef structType, @Out @NotNull NativePointerArray<LlvmTypeRef> dest);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMGetElementType(@NotNull LlvmTypeRef arrayOrVectorType);

    /** see Core.h */
    public static native long LLVMGetArrayLength2(@NotNull LlvmTypeRef arrayType);

    /** see Core.h */
    public static native @Unsigned int LLVMGetVectorSize(@NotNull LlvmTypeRef arrayType);

    /** see Core.h */
    public static native void LLVMSetTarget(@NotNull LlvmModuleRef module, @NotNull String triple);

    /** see Core.h */
    public static native @NotNull LlvmModuleRef LLVMModuleCreateWithNameInContext(@NotNull String moduleId, @NotNull LlvmContextRef context);

    public static native @NotNull LlvmContextRef LLVMGetModuleContext(@NotNull LlvmModuleRef module);

    /** see Core.h */
    public static native @LlvmBool int LLVMPrintModuleToFile(LlvmModuleRef module, String filename, @Out PointerByReference errorMessage);

    /** see Analysis.h */
    public static native @LlvmBool int LLVMVerifyModule(@NotNull LlvmModuleRef module, @NotNull LlvmVerifierFailureAction action, @Out PointerByReference errorMessage);

    /** see Transforms/PassBuilder.h */
    public static native @Nullable LlvmErrorRef LLVMRunPasses(
            @NotNull LlvmModuleRef module,
            @NotNull String passes,
            @NotNull LlvmTargetMachineRef targetMachine,
            @NotNull LlvmPassBuilderOptionsRef options
    );

    /** see BitWriter.h */
    public static native int LLVMWriteBitcodeToFile(@NotNull LlvmModuleRef module, @NotNull String path);

    /** see Core.h */
    public static native void LLVMDisposeModule(@NotNull LlvmModuleRef moduleRef);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMAddFunction(@NotNull LlvmModuleRef module, @NotNull String name, @NotNull LlvmTypeRef functionType);

    /** see Core.h */
    public static native @Nullable LlvmValueRef LLVMGetNamedFunction(@NotNull LlvmModuleRef module, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMGetParam(@NotNull LlvmValueRef function, @Unsigned int index);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMAddGlobal(@NotNull LlvmModuleRef module, @NotNull LlvmTypeRef type, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmThreadLocalMode LLVMGetThreadLocalMode(@NotNull LlvmValueRef globalVar);

    /** see Core.h */
    public static native void LLVMSetInitializer(@NotNull LlvmValueRef globalVar, @NotNull LlvmValueRef constantVal);

    /** see Core.h */
    public static native void LLVMSetUnnamedAddress(@NotNull LlvmValueRef globalVar, @NotNull LlvmUnnamedAddr unnamedAddr);

    /** see Core.h */
    public static native void LLVMSetLinkage(@NotNull LlvmValueRef globalVar, @NotNull LlvmLinkage linkage);

    /** see Core.h */
    public static native void LLVMSetThreadLocalMode(@NotNull LlvmValueRef globalVar, @NotNull LlvmThreadLocalMode mode);

    /** see Target.h */
    public static native void LLVMSetModuleDataLayout(@NotNull LlvmModuleRef module, @NotNull LlvmTargetDataRef DL);

    /** see Target.h */
    public static native @Unsigned int LLVMPointerSize(@NotNull LlvmTargetDataRef TD);

    /** see Target.h */
    public static native @Unsigned long LLVMOffsetOfElement(LlvmTargetDataRef TD, LlvmTypeRef structTy, @Unsigned int element);

    /** see Core.h */
    public static native void LLVMDisposeMessage(@NotNull Pointer message);

    /** see Core.h */
    public static native @NotNull LlvmBasicBlockRef LLVMAppendBasicBlockInContext(@NotNull LlvmContextRef context, @NotNull LlvmValueRef function, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmBuilderRef LLVMCreateBuilderInContext(@NotNull LlvmContextRef context);

    /** see Core.h */
    public static native void LLVMDisposeBuilder(@NotNull LlvmBuilderRef builder);

    /** see Core.h */
    public static native void LLVMPositionBuilderAtEnd(@NotNull LlvmBuilderRef builder, @NotNull LlvmBasicBlockRef block);

    /** see Core.h */
    public static native @NotNull LlvmBasicBlockRef LLVMGetInsertBlock(@NotNull LlvmBuilderRef builder);

    /** see Core.h */
    public static native @Nullable LlvmValueRef LLVMGetLastInstruction(@NotNull LlvmBasicBlockRef basicBlock);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildGEP2(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmTypeRef type,
            @NotNull LlvmValueRef pointer,
            @NotNull NativePointerArray<LlvmValueRef> indices,
            @ArraySizeOf("indices") int numIndices,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildRet(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef val);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildRetVoid(@NotNull LlvmBuilderRef builder);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildLoad2(@NotNull LlvmBuilderRef builder, @NotNull LlvmTypeRef type, @NotNull LlvmValueRef pointerVal, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildStore(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef val, @NotNull LlvmValueRef ptr);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildAdd(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildSub(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildMul(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildShl(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildLShr(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildZExt(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef val, @NotNull LlvmTypeRef destType, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildAlloca(@NotNull LlvmBuilderRef builder, @NotNull LlvmTypeRef type, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildICmp(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmIntPredicate op,
            @NotNull LlvmValueRef lhs,
            @NotNull LlvmValueRef rhs,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildCall2(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmTypeRef functionType,
            @NotNull LlvmValueRef function,
            @NotNull NativePointerArray<LlvmValueRef> args,
            @ArraySizeOf("args") int numArgs,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMSizeOf(@NotNull LlvmTypeRef type);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildPtrToInt(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef value, @NotNull LlvmTypeRef destTy, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildMemCpy(
            @NotNull LlvmBuilderRef builderRef,
            @NotNull LlvmValueRef dst,
            @Unsigned int dstAlign,
            @NotNull LlvmValueRef src,
            @Unsigned int srcAlign,
            @NotNull LlvmValueRef size
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildMemSet(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef ptr,
            @NotNull LlvmValueRef val,
            @NotNull LlvmValueRef len,
            @Unsigned int align
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildIsNull(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef val,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildIsNotNull(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef val,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildNot(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef val,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildUnreachable(@NotNull LlvmBuilderRef builder);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildBr(@NotNull LlvmBuilderRef builder, @NotNull LlvmBasicBlockRef block);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildCondBr(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef condition,
            @NotNull LlvmBasicBlockRef thenBlock,
            @NotNull LlvmBasicBlockRef elseBlock
    );

    /** see Core.h */
    public static native void LLVMSetCurrentDebugLocation2(@NotNull LlvmBuilderRef builder, LlvmMetadataRef location);

    public static native void LLVMSetInstDebugLocation(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef instruction);

    /** see Core.h */
    public static native @Nullable LlvmValueRef LLVMIsATerminatorInst(@NotNull LlvmValueRef inst);

    /** see Core.h */
    public static native @NotNull Pointer LLVMGetValueName2(@NotNull LlvmValueRef value, @Out NativeLongByReference length);

    /** see Core.h */
    public static native void LLVMSetVolatile(@NotNull LlvmValueRef memoryAccessInst, @LlvmBool int isVolatile);

    /** see Target.h */
    public static native void LLVMInitializeX86TargetInfo();

    /** see Target.h */
    public static native void LLVMInitializeX86Target();

    /** see Target.h */
    public static native void LLVMInitializeX86TargetMC();

    /** see Target.h */
    public static native void LLVMInitializeX86AsmPrinter();

    /** see Target.h */
    public static native void LLVMInitializeX86AsmParser();

    /** see TargetMachine.h */
    public static native @LlvmBool int LLVMGetTargetFromTriple(@NotNull String triple, @Out PointerByReference target, @Out PointerByReference errorMessage);

    /** see TargetMachine.h */
    public static native @NotNull String LLVMGetTargetName(@NotNull LlvmTargetRef target);

    /** see TargetMachine.h */
    public static native @NotNull LlvmTargetMachineRef LLVMCreateTargetMachine(
            @NotNull LlvmTargetRef target,
            @NotNull String triple,
            @NotNull String cpu,
            @NotNull String features,
            @NotNull LlvmCodeGenOptModel level,
            @NotNull LlvmRelocMode reloc,
            @NotNull LlvmCodeModel codeModel
    );

    /** see TargetMachine.h */
    public static native @NotNull LlvmTargetDataRef LLVMCreateTargetDataLayout(@NotNull LlvmTargetMachineRef targetMachine);

    /** see TargetMachine.h */
    public static native @NotNull String LLVMGetTargetMachineTriple(LlvmTargetMachineRef targetMachine);

    /** see Target.h */
    public static native @NotNull LlvmMessage LLVMCopyStringRepOfTargetData(LlvmTargetDataRef targetData);

    /** see Transforms/PassBuilder.h */
    public static native @NotNull LlvmPassBuilderOptionsRef LLVMCreatePassBuilderOptions();

    /** see Transforms/PassBuilder.h */
    public static native void LLVMDisposePassBuilderOptions(@NotNull LlvmPassBuilderOptionsRef pbo);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetDebugLogging(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int debugLogging);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetLoopInterleaving(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int loopInterleaving);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetLoopVectorization(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int loopVectorization);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetSLPVectorization(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int slpVectorization);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetLoopUnrolling(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int loopUnrolling);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetForgetAllSCEVInLoopUnroll(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int forgetAllScevInLoopUnroll);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetCallGraphProfile(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int callGraphProfile);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetMergeFunctions(@NotNull LlvmPassBuilderOptionsRef pbo, @LlvmBool int mergeFunctions);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetLicmMssaOptCap(@NotNull LlvmPassBuilderOptionsRef pbo, @Unsigned int lcimMssaOptCap);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetLicmMssaNoAccForPromotionCap(@NotNull LlvmPassBuilderOptionsRef pbo, @Unsigned int licmMssaNoAccForPromotionCap);

    /** see Transforms/PassBuilder.h */
    public static native void LLVMPassBuilderOptionsSetInlinerThreshold(@NotNull LlvmPassBuilderOptionsRef pbo, int threshold);

    /** see Error.h */
    public static native Pointer LLVMGetErrorMessage(@NotNull LlvmErrorRef err);

    /** see Error.h */
    public static native void LLVMDisposeErrorMessage(@NotNull Pointer errMsg);

    /** see Core.h */
    public static native @Unsigned int LLVMGetEnumAttributeKindForName(@NotNull byte[] name, @ArraySizeOf("name") NativeLong len);

    /** see Core.h */
    public static native @NotNull LlvmAttributeRef LLVMCreateEnumAttribute(@NotNull LlvmContextRef context, @Unsigned int kindId, @Unsigned long val);

    /**
     * see Core.h
     * @param index -1 for adding the attribute to the function itself, 0 for adding it to the return value, and 1, 2, 3, ...
     *              for adding to the parameters
     */
    public static native void LLVMAddAttributeAtIndex(@NotNull LlvmValueRef functionValue, int index, @NotNull LlvmAttributeRef attribute);

    /** see DebugInfo.h */
    public static native @NotNull LlvmDiBuilderRef LLVMCreateDIBuilder(@NotNull LlvmModuleRef module);

    /** see DebugInfo.h */
    public static native void LLVMDIBuilderFinalize(@NotNull LlvmDiBuilderRef diBuilder);

    /** see DebugInfo.h */
    public static native void LLVMDisposeDIBuilder(@NotNull LlvmDiBuilderRef diBuilder);

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateCompileUnit(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmDwarfSourceLanguage lang,
            @NotNull LlvmMetadataRef file,
            byte[] producer,
            @NotNull @ArraySizeOf("producer") NativeLong producerLen,
            @LlvmBool int isOptimized,
            byte[] flags,
            @NotNull @ArraySizeOf("flags") NativeLong flagsLen,
            @Unsigned int runtimeVer,
            byte[] splitName,
            @NotNull @ArraySizeOf("splitName") NativeLong splitNameLen,
            @NotNull LlvmDwarfEmissionKind kind,
            @Unsigned int DWOId,
            @LlvmBool int splitDebugInlining,
            @LlvmBool int DebugInfoForProfiling,
            byte[] sysRoot,
            @NotNull @ArraySizeOf("sysRoot") NativeLong sysRootLen,
            byte[] sdk,
            @NotNull @ArraySizeOf("sdkLen") NativeLong sdkLen
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateFile(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull byte[] filename,
            @NotNull @ArraySizeOf("filename") NativeLong filenameLen,
            @NotNull byte[] directory,
            @NotNull @ArraySizeOf("directory") NativeLong directoryLen
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateSubroutineType(
            @NotNull LlvmDiBuilderRef builderRef,
            @NotNull LlvmMetadataRef file,
            @NotNull NativePointerArray<LlvmMetadataRef> parameterTypes,
            @ArraySizeOf("parameterTypes") int numParameterTypes,
            int flags
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateFunction(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmMetadataRef scope,
            @NotNull byte[] name,
            @NotNull @ArraySizeOf("name") NativeLong nameLen,
            byte[] linkageName,
            @NotNull @ArraySizeOf("name") NativeLong linkageNameLen,
            @NotNull LlvmMetadataRef file,
            @Unsigned int lineNo,
            @NotNull LlvmMetadataRef type,
            @LlvmBool int isLocalToUnit,
            @LlvmBool int isDefinition,
            @Unsigned int scopeLine,
            @Unsigned int flags,
            @LlvmBool int isOptimized
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateDebugLocation(
            @NotNull LlvmContextRef context,
            @Unsigned int line,
            @Unsigned int column,
            @NotNull LlvmMetadataRef scope,
            @Nullable LlvmMetadataRef inlinedAt
    );
}