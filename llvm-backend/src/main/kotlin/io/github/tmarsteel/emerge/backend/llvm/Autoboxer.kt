package io.github.tmarsteel.emerge.backend.llvm

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassMemberVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
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

    /**
     * to be invoked on the [Autoboxer] of the [IrClassMemberVariableAccessExpression.base]s type. If this function
     * returns `true` the [readAccess] must be rewritten using [rewriteAccessIntoTheBox].
     */
    fun isAccessingIntoTheBox(context: EmergeLlvmContext, readAccess: IrClassMemberVariableAccessExpression): Boolean

    /**
     * @see isAccessingIntoTheBox
     * Inserts instructions on the [BasicBlockBuilder] that perform the correct steps for accessing the boxed value
     * @return the unboxed value
     */
    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun rewriteAccessIntoTheBox(readAccess: IrClassMemberVariableAccessExpression): LlvmValue<*>

    /**
     * to be invoked on the [Autoboxer] of the type of a value that is to be assigned to a reference/storage of type
     * [toType]. If this function returns `true` the value needs to be transformed using [transformForAssignmentTo]
     * before the actual assignment
     */
    fun assignmentRequiresTransformation(context: EmergeLlvmContext, toType: IrType): Boolean

    /**
     * @see rewriteAccessIntoTheBox
     * inserts instructions on the [BasicBlockBuilder] that perform the transformation
     * @return the transformed value, ready to be assigned
     */
    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun transformForAssignmentTo(value: IrTemporaryValueReference, toType: IrType): LlvmValue<*>

    fun getReferenceSiteType(context: EmergeLlvmContext, forceBoxed: Boolean): LlvmType {
        return if (forceBoxed) LlvmPointerType.pointerTo(getBoxedType(context)) else unboxedType
    }

    /**
     * the type that the programmer and the frontend handle is a primitive type (integer, boolean, float, ...)
     */
    class PrimitiveType(
        val boxedTypeGetter: (EmergeLlvmContext) -> EmergeClassType,
        val primitiveTypeGetter: (EmergeLlvmContext) -> IrClass,
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

        override fun assignmentRequiresTransformation(context: EmergeLlvmContext, toType: IrType): Boolean {
            if (!toType.isNullable && toType is IrSimpleType && toType.baseType == primitiveTypeGetter(context)) {
                return false
            }

            return true
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>) override fun transformForAssignmentTo(
            value: IrTemporaryValueReference,
            toType: IrType
        ): LlvmValue<*> {
            val llvmValue = value.declaration.llvmValue
            check(llvmValue.type == unboxedType)
            return call(getBoxedType(context).constructor, listOf(llvmValue))
        }
    }

    /**
     * used for types that resemble pointers in the C FFI. In contrast to the primitive emerge types,
     * the user/input program is handling the **boxed** version of the value, but under the hood it
     * should be simplified to a primitive version wherever possible, without the input program being able
     * to even mention that primitive type.
     */
    class CFfiPointerType(
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

        override fun assignmentRequiresTransformation(context: EmergeLlvmContext, toType: IrType): Boolean {
            if (toType is IrSimpleType && toType.baseType == getBoxedType(context).irClass) {
                // nullability is not relevant here; a null reference in emerge is a perfectly fine null pointer in C
                return false
            }

            return true
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>) override fun transformForAssignmentTo(
            value: IrTemporaryValueReference,
            toType: IrType
        ): LlvmValue<*> {
            val llvmValue = value.declaration.llvmValue
            check(llvmValue.type == unboxedType)
            return call(getBoxedType(context).constructor, listOf(llvmValue))
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

        /**
         * Whenever a [value] is placed in a reference/storage of type [targetType],
         * this function ensures that the value is unboxed if necessary
         * @return the unboxed value, or simply [value] if unboxing is not needed
         */
        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        fun assureBoxed(value: IrTemporaryValueReference, targetType: IrType): LlvmValue<*> {
            if (value.type == targetType) {
                return value.declaration.llvmValue
            }

            val autoboxer = value.declaration.type.autoboxer
            if (autoboxer == null || !autoboxer.assignmentRequiresTransformation(context, targetType)) {
                return value.declaration.llvmValue
            }
            return autoboxer.transformForAssignmentTo(value, targetType)
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