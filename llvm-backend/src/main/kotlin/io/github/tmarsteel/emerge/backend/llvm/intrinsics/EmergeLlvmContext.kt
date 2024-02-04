package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.bodyDefined
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitCode
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.rawLlvmRef
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.global.LLVM

class EmergeLlvmContext(val base: LlvmContext) : LlvmContext by base {
    /**
     * The IR tree node that is the pointed member of the CPointer struct; for use in special-treating
     * the intrinsic
     */
    lateinit var cPointerPointedMember: IrStruct.Member
        private set

    fun registerStruct(struct: IrStruct) {
        if (struct.rawLlvmRef != null) {
            return
        }

        val structType = LLVM.LLVMStructCreateNamed(ref, struct.llvmName)
        // register here to allow cyclic references
        struct.rawLlvmRef = structType
        struct.llvmType = EmergeStructType.fromLlvmStructWithoutBody(
            this,
            structType,
            struct,
        )

        if (struct.fqn.toString() == "emerge.ffi.c.CPointer") {
            cPointerPointedMember = struct.members.first { it.name == "pointed" }
        }
    }

    fun registerFunction(fn: IrFunction) {
        if (fn.llvmRef != null) {
            return
        }

        val functionType = LLVM.LLVMFunctionType(
            getReferenceSiteType(fn.returnType).getRawInContext(this),
            PointerPointer(*fn.parameters.map { getReferenceSiteType(it.type).getRawInContext(this) }.toTypedArray()),
            fn.parameters.size,
            0,
        )
        val rawRef = LLVM.LLVMAddFunction(module, fn.llvmName, functionType)
        fn.llvmRef = LlvmFunction(
            rawRef,
            functionType,
            getReferenceSiteType(fn.returnType),
            fn.parameters.map { getReferenceSiteType(it.type) }
        )
    }

    fun defineFunctionBody(fn: IrImplementedFunction) {
        val llvmFunction = fn.llvmRef ?: throw CodeGenerationException("You must register the functions through ${this::registerFunction.name} first to handle cyclic references (especially important for recursion)")
        if (fn.bodyDefined) {
            throw CodeGenerationException("Cannot define body for function ${fn.fqn} multiple times!")
        }

        println("Emitting code for ${fn.fqn}")
        val entryBlock = LLVM.LLVMAppendBasicBlockInContext(ref, llvmFunction.raw, "entry")
        BasicBlockBuilder.fill(this, entryBlock) {
            emitCode(fn.body)
                ?: throw CodeGenerationException("Function body for ${fn.fqn} does not return or throw on all possible execution paths.")
        }
    }

    /**
     * @return the [LlvmType] of the given emerge type, for use in the reference location. This is
     * [LlvmPointerType] for all structural/heap-allocated types, and an LLVM value type for the emerge value types.
     */
    fun getReferenceSiteType(type: IrType): LlvmType {
        if (type is IrParameterizedType && type.simpleType.baseType.fqn.toString() == "emerge.ffi.c.CPointer") {
            return LlvmPointerType(getReferenceSiteType(type.arguments["T"]!!.type))
        }

        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getReferenceSiteType(type.effectiveBound)
        }

        when (baseType.fqn.toString()) {
            "emerge.ffi.c.COpaquePointer",
            "emerge.ffi.c.CPointer" -> return opaquePointer
            "emerge.core.Int" -> return LlvmI32Type
            "emerge.core.Array" -> return opaquePointer
            "emerge.core.iword",
            "emerge.core.uword" -> return LlvmWordType
            "emerge.core.Unit" -> return LlvmVoidType
            "emerge.core.Any" -> return PointerToAnyValue // TODO: remove, Any will be a pure language-defined type
        }

        return PointerToAnyValue
    }

    fun getAllocationSiteType(type: IrType): LlvmType {
        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getAllocationSiteType(type.effectiveBound)
        }

        when (baseType.fqn.toString()) {
            "emerge.ffi.c.COpaquePointer",
            "emerge.ffi.c.CPointer" -> return opaquePointer
            "emerge.core.Int" -> return LlvmI32Type
            "emerge.core.iword",
            "emerge.core.uword" -> return LlvmWordType
        }

        throw CodeGenerationException("Cannot determine LLVM type for allocation of $type")
    }

    companion object {
        fun createDoAndDispose(targetTriple: String, action: (EmergeLlvmContext) -> Unit) {
            return LlvmContext.createDoAndDispose(targetTriple) {
                action(EmergeLlvmContext(it))
            }
        }
    }
}