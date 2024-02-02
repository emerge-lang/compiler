package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

class EmergeLlvmContext(val base: LlvmContext) : LlvmContext by base {
    private val baseTypeRefs = HashMap<IrBaseType, LLVMTypeRef>()
    fun registerStruct(struct: IrStruct) {
        if (struct in baseTypeRefs) {
            return
        }

        val structType = LLVM.LLVMStructCreateNamed(ref, struct.llvmName)
        // register here to allow cyclic references
        baseTypeRefs[struct] = structType
        val elements = PointerPointer(*struct.members.map { getType(it.type) }.toTypedArray())
        LLVM.LLVMStructSetBody(structType, elements, struct.members.size, 0)
    }

    fun getType(type: IrType): LLVMTypeRef {
        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getType(type.effectiveBound)
        }

        /*
        when (baseType.fqn.toString()) {
            "emerge.ffi.c.COpaquePointer",
            "emerge.ffi.c.CPointer" -> return pointerTypeRaw
            "emerge.core.Int" -> return intTypeRaw
            "emerge.core.Array" -> return pointerTypeRaw
            "emerge.core.iword",
            "emerge.core.uword" -> return wordTypeRaw
            "emerge.core.Unit" -> return voidTypeRaw
            "emerge.core.Any" -> return pointerTypeRaw // TODO: remove, Any will be a pure language-defined type
        }

         */

        return baseTypeRefs[baseType] ?: throw CodeGenerationException("Unknown base type $baseType")
    }

    companion object {
        fun createDoAndDispose(targetTriple: String, action: (EmergeLlvmContext) -> Unit) {
            return LlvmContext.createDoAndDispose(targetTriple) {
                action(EmergeLlvmContext(it))
            }
        }
    }
}