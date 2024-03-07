package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
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
        "emerge.core.Byte",
        "emerge.core.UByte" -> LlvmI8Type

        "emerge.core.Short",
        "emerge.core.UShort" -> LlvmI16Type

        "emerge.core.Int",
        "emerge.core.UInt" -> LlvmI32Type

        "emerge.core.Long",
        "emerge.core.ULong" -> LlvmI64Type

        "emerge.core.iword",
        "emerge.core.uword" -> EmergeWordType

        "emerge.core.Boolean" -> LlvmBooleanType

        "emerge.ffi.c.COpaquePointer" -> LlvmPointerType(LlvmVoidType)

        else -> null
    }
}
internal val IrType.isUnit by tackLazyVal { this is IrSimpleType && this.baseType.fqn.toString() == "emerge.core.Unit" }

internal var IrClass.rawLlvmRef: LLVMTypeRef? by tackState { null }
internal val IrClass.llvmName: String get() = this.fqn.toString()
internal var IrClass.llvmType: EmergeStructType? by tackState { null }
internal var IrClass.MemberVariable.indexInLlvmStruct: Int? by tackState { null }

/**
 * True only for the member `pointed` of `emerge.ffi.c.CPointer`
 */
internal var IrClass.MemberVariable.isCPointerPointed: Boolean by tackState { false }

internal var IrFunction.llvmRef: LlvmFunction<LlvmType>? by tackState { null }
internal var IrFunction.bodyDefined: Boolean by tackState { false }
internal val IrFunction.llvmName: String get() = if (isExternalC) fqn.last else fqn.toString()

internal val IrSoftwareContext.packagesSeq: Sequence<IrPackage> get() = modules.asSequence()
    .flatMap { it.packages }