package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.codegen.findSimpleTypeBound
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmF32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmF64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeInterfaceTypeinfoHolder
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeSWordType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeUWordType
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import java.util.Collections
import java.util.IdentityHashMap

/*
Amendmends to the backend-api IR using tack.kt
Once the LLVM backend is somewhat stable all of this should move into a new set of AST classes
 */

internal val IrBaseType.autoboxer: Autoboxer? by tackLazyVal {
    when (this.canonicalName.toString()) {
        "emerge.core.S8" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS8, "value", EmergeLlvmContext::rawS8Clazz, LlvmS8Type)
        "emerge.core.U8" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU8, "value", EmergeLlvmContext::rawU8Clazz, LlvmU8Type)
        "emerge.core.S16" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS16, "value", EmergeLlvmContext::rawS16Clazz, LlvmS16Type)
        "emerge.core.U16" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU16, "value", EmergeLlvmContext::rawU16Clazz, LlvmU16Type)
        "emerge.core.S32" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS32, "value", EmergeLlvmContext::rawS32Clazz, LlvmS32Type)
        "emerge.core.U32" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU32, "value", EmergeLlvmContext::rawU32Clazz, LlvmU32Type)
        "emerge.core.S64" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeS64, "value", EmergeLlvmContext::rawS64Clazz, LlvmS64Type)
        "emerge.core.U64" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeU64, "value", EmergeLlvmContext::rawU64Clazz, LlvmU64Type)
        "emerge.core.F32" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeF32, "value", EmergeLlvmContext::rawF32Clazz, LlvmF32Type)
        "emerge.core.F64" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeF64, "value", EmergeLlvmContext::rawF64Clazz, LlvmF64Type)
        "emerge.core.SWord" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeSWord, "value", EmergeLlvmContext::rawSWordClazz, EmergeSWordType)
        "emerge.core.UWord" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeUWord, "value", EmergeLlvmContext::rawUWordClazz, EmergeUWordType)
        "emerge.core.Bool" -> Autoboxer.PrimitiveType(EmergeLlvmContext::boxTypeBool, "value", EmergeLlvmContext::rawBoolClazz, LlvmBooleanType)
        "emerge.core.reflection.ReflectionBaseType" -> Autoboxer.ReflectionBaseType
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
internal val IrBaseType.isAny by tackLazyVal { canonicalName.toString() == "emerge.core.Any" }
internal val IrBaseType.isNothing by tackLazyVal { canonicalName.toString() == "emerge.core.Nothing" }

internal var IrClass.rawLlvmRef: LlvmTypeRef? by tackState { null }
internal val IrClass.llvmName: String get() = this.canonicalName.toString()
internal var IrClass.llvmType: EmergeClassType by tackLateInitState()
internal var IrClass.Field.indexInLlvmStruct: Int? by tackState { null }

internal val IrInterface.typeinfoHolder: EmergeInterfaceTypeinfoHolder by tackLazyVal {
    EmergeInterfaceTypeinfoHolder(this)
}

internal val IrBaseType.allDistinctSupertypesExceptAny: Set<IrInterface> by tackLazyVal {
    val allSupertypes: MutableSet<IrInterface> = Collections.newSetFromMap(IdentityHashMap())
    allSupertypes.addAll(supertypes)
    do {
        val additional = allSupertypes
            .asSequence()
            .flatMap { it.supertypes }
            .filter { it !in allSupertypes }
            .toList()
        allSupertypes.addAll(additional)
    } while (additional.isNotEmpty())

    allSupertypes.removeAll { it.isAny }

    allSupertypes
}

/**
 * True only for the member `pointed` of `emerge.ffi.c.CPointer`
 */
internal var IrClass.Field.isCPointerPointed: Boolean by tackState { false }

internal var IrFunction.llvmRef: LlvmFunction<LlvmType>? by tackState { null }
internal var IrFunction.bodyDefined: Boolean by tackState { false }
internal var IrFunction.llvmName: String by tackState {
    if (isExternalC) canonicalName.simpleName else {
        Mangler.computeMangledNameFor(this)
    }
}

/**
 * if `true`, the function returns its result value plain. If `false`, the function returns a [EmergeFallibleCallResult] wrapper.
 */
internal val IrFunction.hasNothrowAbi: Boolean by tackLazyVal {
    if (canonicalName.toString() in setOf(
        "emerge.ffi.c.CPointer::\$constructor",
        "emerge.ffi.c.CPointer::\$destructor",
        "emerge.ffi.c.COpaquePointer::\$constructor",
        "emerge.ffi.c.COpaquePointer::\$destructor",
    )) {
        // the CPointer types are really just used to turn off emerges reference counting; they never actually manifest
        // in memory, so the constructor and destructor are noops
        return@tackLazyVal true
    }

    if (this is IrMemberFunction) {
        if (overrides.any { !it.hasNothrowAbi }) {
            // a super function is not nothrow, so overriding functions need to adhere to that ABI
            return@tackLazyVal false
        }
    }

    isNothrow
}

internal var IrLoop.emitBreak: (() -> BasicBlockBuilder.Termination)? by tackState { null }
internal var IrLoop.emitContinue: (() -> BasicBlockBuilder.Termination)? by tackState { null }

internal val IrClassFieldAccessExpression.baseBaseType: IrBaseType by tackLazyVal {
    base.type.findSimpleTypeBound().baseType
}
internal val IrClassFieldAccessExpression.memberVariable: IrClass.MemberVariable? by tackLazyVal {
    val localBaseBaseType = baseBaseType
    if (localBaseBaseType !is IrClass) {
        return@tackLazyVal null
    }

    localBaseBaseType.memberVariables.find {
        val readStrat = it.readStrategy
        if (readStrat !is IrClass.MemberVariable.AccessStrategy.BareField) {
            return@find false
        }
        readStrat.fieldId == field.id
    }
}

internal val IrSoftwareContext.packagesSeq: Sequence<IrPackage> get() = modules.asSequence()
    .flatMap { it.packages }