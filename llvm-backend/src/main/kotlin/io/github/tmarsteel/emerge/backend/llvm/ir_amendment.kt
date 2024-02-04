package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.AnyValueType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.LlvmWordType
import org.bytedeco.llvm.LLVM.LLVMTypeRef

/*
Amendmends to the backend-api IR using tack.kt
Once the LLVM backend is somewhat stable all of this should move into a new set of AST classes
 */

/**
 * If this is one of the emerge value types, returns the corresponding type.
 * Null otherwise, which means that the value should probably be represented as a
 * `pointerTo(AnyvalueType)`
 */
internal val IrType.llvmValueType: LlvmType? by tackLazyVal {
    if (this !is IrSimpleType) {
        return@tackLazyVal null
    }

    when (this.baseType.fqn.toString()) {
        "emerge.core.Any" -> AnyValueType
        "emerge.core.Byte",
        "emerge.core.UByte" -> LlvmI8Type

        "emerge.core.Short",
        "emerge.core.UShort" -> LlvmI16Type

        "emerge.core.Int",
        "emerge.core.UInt" -> LlvmI32Type

        "emerge.core.Long",
        "emerge.core.ULong" -> LlvmI64Type

        "emerge.core.iword",
        "emerge.core.uword" -> LlvmWordType

        "emerge.ffi.c.COpaquePointer" -> LlvmPointerType(LlvmVoidType)

        else -> null
    }
}

internal var IrStruct.rawLlvmRef: LLVMTypeRef? by tackState { null }
internal var IrStruct.llvmType: EmergeStructType? by tackState { null }
internal var IrStruct.Member.indexInLlvmStruct: Int? by tackState { null }

/**
 * True only for the member `pointed` of `emerge.ffi.c.CPointer`
 */
internal var IrStruct.Member.isCPointerPointed: Boolean by tackState { false }

internal var IrFunction.llvmRef: LlvmFunction<LlvmType>? by tackState { null }
internal var IrFunction.bodyDefined: Boolean by tackState { false }
