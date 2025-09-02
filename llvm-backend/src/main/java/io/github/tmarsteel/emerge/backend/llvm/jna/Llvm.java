package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.*;
import com.sun.jna.ptr.*;
import org.jetbrains.annotations.*;

import java.nio.file.*;
import java.util.*;

/**
 * LLVM C interface functions mapped for LLVM-20 using JNA.
 */
public class Llvm {
    private volatile static Path LLVM_DIR = null;
    public static void loadNativeLibrary(Path llvmInstallationDirectory) {
        synchronized (Llvm.class) {
            if (LLVM_DIR != null) {
                if (!LLVM_DIR.equals(llvmInstallationDirectory)) {
                    throw new IllegalStateException("The installation path for LLVM has already been set to " + LLVM_DIR + ", it cannot be changed (trying to change to " + llvmInstallationDirectory + ")");
                }
                return;
            }
            LLVM_DIR = llvmInstallationDirectory;
            NativeLibrary.addSearchPath("LLVM-20", LLVM_DIR.resolve("lib").toString());
            NativeLibrary.addSearchPath("LLVM-C", LLVM_DIR.resolve("bin").toString());
            Map<String, Object> options = Map.of(
                    Library.OPTION_TYPE_MAPPER, new LlvmTypeMapper()
            );
            NativeLibrary llvmLib;
            try {
                llvmLib = NativeLibrary.getInstance("LLVM-20", options);
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
            Native.register(Llvm.class, llvmLib);
        }
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
    public static native @NotNull LlvmTypeRef LLVMFloatTypeInContext(@NotNull LlvmContextRef context);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMDoubleTypeInContext(@NotNull LlvmContextRef context);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMStructTypeInContext(@NotNull LlvmContextRef context, @NotNull NativePointerArray<LlvmTypeRef> elementTypes, @ArraySizeOf("elementTypes") int elementCount, @LlvmBool int packed);

    /** see Core.h */
    public static native @NotNull LlvmTypeRef LLVMStructCreateNamed(@NotNull LlvmContextRef context, String name);

    /** see Core.h */
    public static native void LLVMStructSetBody(@NotNull LlvmTypeRef structTy, @NotNull NativePointerArray<LlvmTypeRef> elementTypes, @ArraySizeOf("elementTypes") int elementCount, @LlvmBool int packed);

    /** see Core.h */
    public static native @Unsigned int LLVMCountStructElementTypes(@NotNull LlvmTypeRef structTy);

    /** see Core.h */
    public static native @LlvmBool int LLVMIsPackedStruct(@NotNull LlvmTypeRef StructTy);

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

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMGetPoison(@NotNull LlvmTypeRef type);

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

    /** see Core.h */
    public static native @NotNull LlvmContextRef LLVMGetModuleContext(@NotNull LlvmModuleRef module);

    /** see Core.h */
    public static native void LLVMAddModuleFlag(
            @NotNull LlvmModuleRef module,
            @NotNull LlvmModuleFlagBehavior behavior,
            @NotNull byte[] key,
            @ArraySizeOf("key") NativeLong keyLen,
            @NotNull LlvmMetadataRef value
    );

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
    public static native @NotNull LlvmTargetDataRef LLVMGetModuleDataLayout(LlvmModuleRef module);

    /** see Target.h */
    public static native void LLVMSetModuleDataLayout(@NotNull LlvmModuleRef module, @NotNull LlvmTargetDataRef DL);

    /** see Target.h */
    public static native @Unsigned int LLVMPointerSize(@NotNull LlvmTargetDataRef TD);

    /** see Target.h */
    public static native @Unsigned long LLVMOffsetOfElement(LlvmTargetDataRef TD, LlvmTypeRef structTy, @Unsigned int element);

    /** see Target.h */
    public static native @Unsigned int LLVMABIAlignmentOfType(LlvmTargetDataRef TD, LlvmTypeRef ty);

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

    public static native void LLVMPositionBuilderBefore(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef instruction);

    /** see Core.h */
    public static native @NotNull LlvmBasicBlockRef LLVMGetEntryBasicBlock(@NotNull LlvmValueRef function);

    /** see Core.h */
    public static native @NotNull LlvmBasicBlockRef LLVMGetInsertBlock(@NotNull LlvmBuilderRef builder);

    /** see Core.h */
    public static native @Nullable LlvmValueRef LLVMGetFirstInstruction(@NotNull LlvmBasicBlockRef basicBlock);

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
    public static native @NotNull LlvmValueRef LLVMBuildExtractValue(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef aggregateValue,
            @Unsigned int index,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildInsertValue(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef aggregateVal,
            @NotNull LlvmValueRef valueToInsert,
            @Unsigned int index,
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
    public static native @NotNull LlvmValueRef LLVMBuildUDiv(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildExactUDiv(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildSDiv(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildExactSDiv(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildShl(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildLShr(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildAShr(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildAnd(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildOr(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildXor(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef lhs, @NotNull LlvmValueRef rhs, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildZExt(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef val, @NotNull LlvmTypeRef destType, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildSExt(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef val, @NotNull LlvmTypeRef destType, @NotNull String name);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildURem(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef LHS,
            @NotNull LlvmValueRef RHS,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildSRem(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef LHS,
            @NotNull LlvmValueRef RHS,
            @NotNull String name
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMBuildTrunc(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef val, @NotNull LlvmTypeRef destType, @NotNull String name);

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
    public static native @NotNull LlvmValueRef LLVMBuildSelect(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmValueRef If,
            @NotNull LlvmValueRef Then,
            @NotNull LlvmValueRef Else,
            @NotNull String name
    );

    /** see Core.h */
    public static native LlvmValueRef LLVMBuildPhi(
            @NotNull LlvmBuilderRef builder,
            @NotNull LlvmTypeRef Ty,
            @NotNull String name
    );

    public static native void LLVMAddIncoming(
            @NotNull LlvmValueRef PhiNode,
            @NotNull NativePointerArray<LlvmValueRef> incomingValues,
            @NotNull NativePointerArray<LlvmBasicBlockRef> incomingBlocks,
            @Unsigned int count
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
    public static native @Unsigned int LLVMLookupIntrinsicID(@NotNull byte[] name, @NotNull @ArraySizeOf("name") NativeLong nameLength);

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMGetIntrinsicDeclaration(
            @NotNull LlvmModuleRef module,
            @Unsigned int id,
            @NotNull NativePointerArray<LlvmTypeRef> paramTypes,
            @NotNull @ArraySizeOf("paramTypes") NativeLong paramCount
    );

    /** see Core.h */
    public static native void LLVMSetCurrentDebugLocation2(@NotNull LlvmBuilderRef builder, LlvmMetadataRef location);

    /** see Core.h */
    public static native @Nullable LlvmMetadataRef LLVMGetCurrentDebugLocation2(@NotNull LlvmBuilderRef builder);

    /** see Core.h */
    public static native void LLVMSetInstDebugLocation(@NotNull LlvmBuilderRef builder, @NotNull LlvmValueRef instruction);

    /** see Core.h */
    public static native @Nullable LlvmValueRef LLVMIsATerminatorInst(@NotNull LlvmValueRef inst);

    /** see Core.h */
    public static native @NotNull Pointer LLVMGetValueName2(@NotNull LlvmValueRef value, @Out NativeLongByReference length);

    /** see Core.h */
    public static native void LLVMSetValueName2(@NotNull LlvmValueRef value, @NotNull byte[] nameBytes, @NotNull @ArraySizeOf("nameBytes") NativeLong nameLength);

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

    /** see Core.h */
    public static native @NotNull LlvmAttributeRef LLVMCreateStringAttribute(
            @NotNull LlvmContextRef context,
            @NotNull byte[] key,
            @ArraySizeOf("key") @Unsigned int keyLength,
            @NotNull byte[] value,
            @ArraySizeOf("value") @Unsigned int valueLength
    );

    /**
     * see Core.h
     * @param index -1 for adding the attribute to the function itself, 0 for adding it to the return value, and 1, 2, 3, ...
     *              for adding to the parameters
     */
    public static native void LLVMAddAttributeAtIndex(@NotNull LlvmValueRef functionValue, int index, @NotNull LlvmAttributeRef attribute);

    /** see Core.h */
    public static native @NotNull LlvmMetadataRef LLVMMDStringInContext2(
            @NotNull LlvmContextRef context,
            @NotNull byte[] string,
            @ArraySizeOf("string") NativeLong stringLen
    );

    /** see Core.h */
    public static native @NotNull LlvmMetadataRef LLVMMDNodeInContext2(
            @NotNull LlvmContextRef context,
            @NotNull NativePointerArray<LlvmMetadataRef> entries,
            @ArraySizeOf("entries") NativeLong count
    );

    /** see Core.h */
    public static native @NotNull LlvmValueRef LLVMMetadataAsValue(
            @NotNull LlvmContextRef context,
            @NotNull LlvmMetadataRef metadata
    );

    /** see Core.h */
    public static native @NotNull LlvmMetadataRef LLVMValueAsMetadata(@NotNull LlvmValueRef value);

    /** see Core.h */
    public static native @Unsigned int LLVMGetMDNodeNumOperands(LlvmValueRef metadataAsValue);

    /** see Core.h */
    public static native void LLVMGetMDNodeOperands(
            @NotNull LlvmValueRef metadataAsValue,
            @NotNull NativePointerArray<LlvmValueRef> dest
    );

    /** see DebugInfo.h */
    public static native @Unsigned int LLVMDebugMetadataVersion();

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
            @Nullable LlvmMetadataRef type,
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

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMTemporaryMDNode(
            @NotNull LlvmContextRef context,
            @NotNull NativePointerArray<LlvmMetadataRef> elements,
            @Unsigned @ArraySizeOf("elements") int numElements
    );

    /** see DebugInfo.h */
    public static native void LLVMDisposeTemporaryMDNode(@NotNull LlvmMetadataRef temporaryNode);

    /** see DebugInfo.h */
    public static native void LLVMMetadataReplaceAllUsesWith(LlvmMetadataRef TempTargetMetadata, LlvmMetadataRef Replacement);

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateStructType(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmMetadataRef scope,
            @NotNull byte[] name,
            @NotNull @ArraySizeOf("name") NativeLong nameLen,
            @NotNull LlvmMetadataRef file,
            @Unsigned int lineNumber,
            @Unsigned long sizeInBits,
            @Unsigned int alignInBits,
            @NotNull NativeI32FlagGroup<LlvmDiFlags> Flags,
            @Nullable LlvmMetadataRef DerivedFrom,
            @Nullable NativePointerArray<LlvmMetadataRef> elements,
            int NumElements,
            @Unsigned int objectiveCRuntimeVersion,
            LlvmMetadataRef VTableHolder,
            @Nullable byte[] uniqueId,
            @NotNull @ArraySizeOf("uniqueId") NativeLong uniqueIdLen
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateReplaceableCompositeType(
            @NotNull LlvmDiBuilderRef builder,
            @Unsigned int tag,
            @NotNull byte[] name,
            @NotNull @ArraySizeOf("name") NativeLong nameLen,
            @NotNull LlvmMetadataRef scope,
            @NotNull LlvmMetadataRef file,
            @Unsigned int lineNumber,
            @Unsigned int objectiveCRuntimeVersion,
            @Unsigned long sizeInBits,
            @Unsigned int alignInBits,
            @NotNull NativeI32FlagGroup<LlvmDiFlags> flags,
            @NotNull byte[] uniqueId,
            @NotNull @ArraySizeOf("uniqueId") NativeLong uniqueIdLen
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreatePointerType(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmMetadataRef pointeeType,
            @Unsigned long sizeInBits,
            @Unsigned int alignInBits,
            @Unsigned int addressSpace,
            @Nullable byte[] name,
            @Nullable @ArraySizeOf("name") NativeLong nameLen
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateBasicType(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull byte[] name,
            @NotNull @ArraySizeOf("name") NativeLong nameLen,
            long sizeInBits,
            @NotNull DwarfBaseTypeEncoding encoding,
            @NotNull NativeI32FlagGroup<LlvmDiFlags> flags
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateUnspecifiedType(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull byte[] name,
            @NotNull @ArraySizeOf("name") NativeLong nameLen
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateMemberType(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmMetadataRef scope,
            @NotNull byte[] name,
            @NotNull @ArraySizeOf("name") NativeLong nameLen,
            @NotNull LlvmMetadataRef file,
            @Unsigned int lineNumber,
            @Unsigned long sizeInBits,
            @Unsigned long alignInBits,
            @Unsigned long offsetInBits,
            @NotNull NativeI32FlagGroup<LlvmDiFlags> Flags,
            @NotNull LlvmMetadataRef type
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateArrayType(
            @NotNull LlvmDiBuilderRef builder,
            @Unsigned long size,
            @Unsigned int alignInBits,
            @NotNull LlvmMetadataRef elementType,
            @Nullable NativePointerArray<LlvmMetadataRef> subscripts,
            @Unsigned int numSubscripts
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateParameterVariable(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmMetadataRef scope,
            @NotNull byte[] name,
            @NotNull @ArraySizeOf("name") NativeLong nameLen,
            @Unsigned int argNo,
            @NotNull LlvmMetadataRef file,
            @Unsigned int lineNo,
            @NotNull LlvmMetadataRef type,
            @LlvmBool int alwaysPreserve,
            @NotNull NativeI32FlagGroup<LlvmDiFlags> flags
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateLexicalBlock(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmMetadataRef parentScope,
            @NotNull LlvmMetadataRef file,
            @Unsigned int line,
            @Unsigned int column
    );

    /** see DebugInfo.h */
    public static native void LLVMSetSubprogram(@NotNull LlvmValueRef func, @Nullable LlvmMetadataRef subprogram);

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataKind LLVMGetMetadataKind(@NotNull LlvmMetadataRef metadataRef);

    /** see DebugInfo.h */
    public static native @Unsigned long LLVMDITypeGetSizeInBits(LlvmMetadataRef diType);

    /** see DebugInfo.h */
    public static native @Unsigned int LLVMDITypeGetAlignInBits(LlvmMetadataRef diType);

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateExpression(
            @NotNull LlvmDiBuilderRef builder,
            @Nullable @Unsigned long[] addr,
            @NotNull @ArraySizeOf("addr") NativeLong length
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmMetadataRef LLVMDIBuilderCreateConstantValueExpression(
            @NotNull LlvmDiBuilderRef builder,
            @Unsigned long value
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmDbgRecordRef LLVMDIBuilderInsertDeclareRecordAtEnd(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmValueRef storage,
            @NotNull LlvmMetadataRef varInfo,
            @NotNull LlvmMetadataRef expression,
            @NotNull LlvmMetadataRef debugLocation,
            @NotNull LlvmBasicBlockRef block
    );

    /** see DebugInfo.h */
    public static native @NotNull LlvmDbgRecordRef LLVMDIBuilderInsertDbgValueRecordAtEnd(
            @NotNull LlvmDiBuilderRef builder,
            @NotNull LlvmValueRef storage,
            @NotNull LlvmMetadataRef varInfo,
            @NotNull LlvmMetadataRef expression,
            @NotNull LlvmMetadataRef debugLocation,
            @NotNull LlvmBasicBlockRef block
    );
}