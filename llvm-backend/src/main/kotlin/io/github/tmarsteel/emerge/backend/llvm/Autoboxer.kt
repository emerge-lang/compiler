package io.github.tmarsteel.emerge.backend.llvm

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrClassMemberVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.codegen.llvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext

/**
 * Helps with automatic boxing and unboxing of values
 */
internal sealed interface Autoboxer {
    fun getBoxedType(context: EmergeLlvmContext): EmergeClassType
    val unboxedType: LlvmType

    fun isAccessingIntoTheBox(context: EmergeLlvmContext, readAccess: IrClassMemberVariableAccessExpression): Boolean

    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun rewriteAccessIntoTheBox(readAccess: IrClassMemberVariableAccessExpression): LlvmValue<*>

    fun getReferenceSiteType(context: EmergeLlvmContext, forceBoxed: Boolean): LlvmType {
        return if (forceBoxed) LlvmPointerType.pointerTo(getBoxedType(context)) else unboxedType
    }

    /**
     * the type that the programmer and the frontend handle is the unboxed one; the boxed type is what is hidden
     * by the backend
     */
    class UserFacingUnboxed(
        val boxedTypeGetter: (EmergeLlvmContext) -> EmergeClassType,
        override val unboxedType: LlvmType,
    ) : Autoboxer {
        override fun getBoxedType(context: EmergeLlvmContext): EmergeClassType {
            return boxedTypeGetter(context)
        }

        override fun isAccessingIntoTheBox(
            context: EmergeLlvmContext,
            readAccess: IrClassMemberVariableAccessExpression
        ): Boolean = false

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun rewriteAccessIntoTheBox(readAccess: IrClassMemberVariableAccessExpression): LlvmValue<*> {
            throw UnsupportedOperationException("cannot access into an unboxed type")
        }
    }

    /**
     * the type that the programmer and the frontend handle is the boxed one; the backend hides the unboxed
     * version as a member variable in the box.
     */
    class UserFacingBoxed(
        val boxedTypeGetter: (EmergeLlvmContext) -> EmergeClassType,
        val memberVariableNameToAccessUnboxedValue: String,
        override val unboxedType: LlvmType,
    ) : Autoboxer {
        override fun getBoxedType(context: EmergeLlvmContext): EmergeClassType {
            return boxedTypeGetter(context)
        }

        override fun isAccessingIntoTheBox(
            context: EmergeLlvmContext,
            readAccess: IrClassMemberVariableAccessExpression,
        ): Boolean {
            check(readAccess.base.type.autoboxer === this)
            return readAccess.memberVariable.name == memberVariableNameToAccessUnboxedValue
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun rewriteAccessIntoTheBox(readAccess: IrClassMemberVariableAccessExpression): LlvmValue<*> {
            // currently this has to work for CPointer<T> only

            val resultAutoboxer = readAccess.evaluatesTo.autoboxer
            if (resultAutoboxer == null) {
                // reference type
                return readAccess.base.declaration.llvmValue.reinterpretAs(unboxedType)
            } else {
                // value type, dereference
                return readAccess.base.declaration.llvmValue
                    .reinterpretAs(pointerTo(resultAutoboxer.unboxedType))
                    .dereference()
            }
        }

        val constructorByContext = MapMaker().weakKeys().makeMap<EmergeLlvmContext, LlvmFunction<LlvmPointerType<EmergeClassType>>>()
        fun getConstructorIntrinsic(context: EmergeLlvmContext, name: CanonicalElementName.Function): LlvmFunction<LlvmPointerType<EmergeClassType>> {
            return constructorByContext.computeIfAbsent(context) { _ ->
                val emergeClazz = getBoxedType(context)
                require(emergeClazz.irClass.memberVariables.size == 1)
                val template = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmPointerType<EmergeClassType>>(
                    name.toString(),
                    pointerTo(emergeClazz),
                ) {
                    val unboxedValue by param(unboxedType)

                    body {
                        val heapAllocation = emergeClazz.allocateUninitializedDynamicObject(this)
                        store(unboxedValue, getelementptr(heapAllocation).member(emergeClazz.irClass.memberVariables.single()).get())
                        ret(heapAllocation)
                    }
                }
                context.registerIntrinsic(template)
            }
        }

        fun getDestructorIntrinsic(context: EmergeLlvmContext): LlvmFunction<LlvmVoidType> {
            return context.registerIntrinsic(boxDestructor)
        }
    }

    companion object {
        fun requireNotAutoboxed(value: IrTemporaryValueReference, operation: String) {
            requireNotAutoboxed(value.type, operation)
            requireNotAutoboxed(value.declaration.type, operation)
        }

        fun requireNotAutoboxed(type: IrType, operation: String) {
            require(type.autoboxer == null) {
                "Boxed types are not supported for $operation; encountered $type"
            }
        }
    }
}

private val boxDestructor = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.platform.destructBox",
    LlvmVoidType,
) {
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)

    val self by param(LlvmPointerType.pointerTo(LlvmVoidType))

    body {
        call(context.freeFunction, listOf(self))
        retVoid()
    }
}