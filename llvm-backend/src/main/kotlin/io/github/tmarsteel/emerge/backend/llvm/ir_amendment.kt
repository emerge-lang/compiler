package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrWhileLoop
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
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
        "emerge.core.S8" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS8, EmergeLlvmContext::rawS8Clazz, LlvmI8Type)
        "emerge.core.U8" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU8, EmergeLlvmContext::rawU8Clazz, LlvmI8Type)
        "emerge.core.S16" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS16, EmergeLlvmContext::rawS16Clazz, LlvmI16Type)
        "emerge.core.U16" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU16, EmergeLlvmContext::rawU16Clazz, LlvmI16Type)
        "emerge.core.S32" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS32, EmergeLlvmContext::rawS32Clazz, LlvmI32Type)
        "emerge.core.U32" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU32, EmergeLlvmContext::rawU32Clazz, LlvmI32Type)
        "emerge.core.S64" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS64, EmergeLlvmContext::rawS64Clazz, LlvmI64Type)
        "emerge.core.U64" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU64, EmergeLlvmContext::rawU64Clazz, LlvmI64Type)
        "emerge.core.SWord" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeSWord, EmergeLlvmContext::rawSWordClazz, EmergeWordType)
        "emerge.core.UWord" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeUWord, EmergeLlvmContext::rawUWordClazz, EmergeWordType)
        "emerge.core.Bool" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeBool, EmergeLlvmContext::rawBoolClazz, LlvmBooleanType)
        "emerge.ffi.c.CPointer" -> Autoboxer.CFfiPointerType(EmergeLlvmContext::cPointerType, "pointed", LlvmPointerType(LlvmVoidType))
        "emerge.ffi.c.COpaquePointer" -> Autoboxer.CFfiPointerType(EmergeLlvmContext::cOpaquePointerType, "pointed", LlvmPointerType(LlvmVoidType))
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

internal var IrWhileLoop.emitBreak: (() -> BasicBlockBuilder.Termination)? by tackState { null }

internal val IrSoftwareContext.packagesSeq: Sequence<IrPackage> get() = modules.asSequence()
    .flatMap { it.packages }