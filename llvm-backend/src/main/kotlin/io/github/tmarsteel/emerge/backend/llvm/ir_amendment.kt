package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
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
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef

/*
Amendmends to the backend-api IR using tack.kt
Once the LLVM backend is somewhat stable all of this should move into a new set of AST classes
 */

internal val IrBaseType.autoboxer: Autoboxer? by tackLazyVal {
    when (this.canonicalName.toString()) {
        "emerge.core.S8" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeS8, LlvmI8Type)
        "emerge.core.U8" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeU8, LlvmI8Type)
        "emerge.core.S16" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeS16, LlvmI16Type)
        "emerge.core.U16" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeU16, LlvmI16Type)
        "emerge.core.S32" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeU32, LlvmI32Type)
        "emerge.core.U32" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeS32, LlvmI32Type)
        "emerge.core.S64" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeS64, LlvmI64Type)
        "emerge.core.U64" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeU64, LlvmI64Type)
        "emerge.core.SWord" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeU64, EmergeWordType)
        "emerge.core.UWord" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeU64, EmergeWordType)
        "emerge.core.Bool" -> Autoboxer.UserFacingUnboxed(EmergeLlvmContext::boxTypeBool, LlvmBooleanType)
        "emerge.ffi.c.CPointer" -> Autoboxer.UserFacingBoxed(EmergeLlvmContext::cPointerType, "pointed", LlvmPointerType(LlvmVoidType))
        "emerge.ffi.c.COpaquePointer" -> Autoboxer.UserFacingBoxed(EmergeLlvmContext::cOpaquePointerType, "pointed", LlvmPointerType(LlvmVoidType))
        else -> null
    }
}

internal val IrType.autoboxer: Autoboxer? get() = when(this) {
    is IrParameterizedType -> simpleType.baseType.autoboxer
    is IrSimpleType -> baseType.autoboxer
    else -> null
}

internal val IrType.isUnit by tackLazyVal { this is IrSimpleType && this.baseType.canonicalName.toString() == "emerge.core.Unit" }

internal var IrClass.rawLlvmRef: LlvmTypeRef? by tackState { null }
internal val IrClass.llvmName: String get() = this.canonicalName.toString()
internal var IrClass.llvmType: EmergeClassType by tackLateInitState()
internal var IrClass.MemberVariable.indexInLlvmStruct: Int? by tackState { null }

/**
 * True only for the member `pointed` of `emerge.ffi.c.CPointer`
 */
internal var IrClass.MemberVariable.isCPointerPointed: Boolean by tackState { false }

internal var IrFunction.llvmRef: LlvmFunction<LlvmType>? by tackState { null }
internal var IrFunction.bodyDefined: Boolean by tackState { false }
internal val IrFunction.llvmName: String get() = if (isExternalC) canonicalName.simpleName else canonicalName.toString()

internal val IrSoftwareContext.packagesSeq: Sequence<IrPackage> get() = modules.asSequence()
    .flatMap { it.packages }