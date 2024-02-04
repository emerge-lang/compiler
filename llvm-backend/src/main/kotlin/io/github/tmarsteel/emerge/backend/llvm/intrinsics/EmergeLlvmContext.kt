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
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.llvmDefinition
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.global.LLVM

class EmergeLlvmContext(val base: LlvmContext) : LlvmContext by base {
    fun registerStruct(struct: IrStruct) {
        if (struct.llvmDefinition != null) {
            return
        }

        val structType = LLVM.LLVMStructCreateNamed(ref, struct.llvmName)
        // register here to allow cyclic references
        struct.llvmDefinition = structType
        val elements = PointerPointer(*struct.members.map { getReferenceSiteType(it.type).raw }.toTypedArray())
        LLVM.LLVMStructSetBody(structType, elements, struct.members.size, 0)
    }

    fun registerFunction(fn: IrFunction) {
        if (fn.llvmRef != null) {
            return
        }

        val functionType = LLVM.LLVMFunctionType(
            getReferenceSiteType(fn.returnType).raw,
            PointerPointer(*fn.parameters.map { getReferenceSiteType(it.type).raw }.toTypedArray()),
            fn.parameters.size,
            0,
        )
        fn.llvmRef = LLVM.LLVMAddFunction(module, fn.llvmName, functionType)
    }

    fun defineFunctionBody(fn: IrImplementedFunction) {
        val rawRef = fn.llvmRef ?: throw CodeGenerationException("You must register the functions through ${this::registerFunction.name} first to handle cyclic references (especially important for recursion)")
        if (fn.bodyDefined) {
            throw CodeGenerationException("Cannot define body for function ${fn.fqn} multiple times!")
        }

        val entryBlock = LLVM.LLVMAppendBasicBlockInContext(ref, rawRef, "entry")
        BasicBlockBuilder.appendToUnsafe(this, entryBlock) {
            emitCode(fn.body, it)
        }
    }

    /**
     * @return the [LlvmType] of the given emerge type, for use in the reference location. This is
     * [LlvmPointerType] for all structural/heap-allocated types, and an LLVM value type for the emerge value types.
     */
    fun getReferenceSiteType(type: IrType): LlvmType {
        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getReferenceSiteType(type.effectiveBound)
        }

        when (baseType.fqn.toString()) {
            "emerge.ffi.c.COpaquePointer",
            "emerge.ffi.c.CPointer" -> return opaquePointer
            "emerge.core.Int" -> return i32
            "emerge.core.Array" -> return opaquePointer
            "emerge.core.iword",
            "emerge.core.uword" -> return word
            "emerge.core.Unit" -> return void
            "emerge.core.Any" -> return pointerToAnyValue // TODO: remove, Any will be a pure language-defined type
        }

        return pointerToAnyValue
    }

    companion object {
        fun createDoAndDispose(targetTriple: String, action: (EmergeLlvmContext) -> Unit) {
            return LlvmContext.createDoAndDispose(targetTriple) {
                action(EmergeLlvmContext(it))
            }
        }
    }
}