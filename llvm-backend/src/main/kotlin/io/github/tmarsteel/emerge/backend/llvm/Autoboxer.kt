package io.github.tmarsteel.emerge.backend.llvm

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassMemberVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.independentEquals
import io.github.tmarsteel.emerge.backend.llvm.codegen.findSimpleTypeBound
import io.github.tmarsteel.emerge.backend.llvm.codegen.llvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.PhiBucket
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.abortOnException
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.TypeinfoType

/**
 * Helps with automatic boxing and unboxing of values
 */
internal sealed interface Autoboxer {
    fun getBoxedType(context: EmergeLlvmContext): EmergeClassType

    /**
     * Overrides the [TypeinfoType.canonicalNamePtr] on the boxed type; e.g. for `emerge.platform.S8Box`,
     * overrides to `emerge.core.S8` so that the typeinfo of S8Box can act as the effective typeinfo for S8.
     */
    fun getTypeinfoNameOverrideInContext(context: EmergeLlvmContext): CanonicalElementName.BaseType?

    val unboxedType: LlvmType

    val omitConstructorAndDestructor: Boolean

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
     * @see assignmentRequiresTransformation
     * inserts instructions on the [BasicBlockBuilder] that perform the transformation
     * @return the transformed value, ready to be assigned
     */
    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun transformForAssignmentTo(llvmValue: LlvmValue<*>, toType: IrType): LlvmValue<*>

    /**
     * @return whether [value] holds a box of this autoboxing type
     */
    fun isBox(context: EmergeLlvmContext, value: IrTemporaryValueReference): Boolean

    /**
     * Assumes [value] is a box according to [isBox] and that [value] does not hold a
     * null value at runtime, even if its type is nullable.
     */
    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun unbox(value: IrTemporaryValueReference): LlvmValue<*>

    fun getReferenceSiteType(context: EmergeLlvmContext, forceBoxed: Boolean): LlvmType {
        return if (forceBoxed) LlvmPointerType.pointerTo(getBoxedType(context)) else unboxedType
    }

    /**
     * the type that the programmer and the frontend handle is a primitive type (integer, boolean, float, ...)
     */
    class PrimitiveType(
        val boxedTypeGetter: (EmergeLlvmContext) -> EmergeClassType,
        /** the name of the emerge member variable in the boxed type that holds the raw value */
        val boxValueHoldingMemberVariableName: String,
        val primitiveTypeGetter: (EmergeLlvmContext) -> IrClass,
        override val unboxedType: LlvmType,
    ) : Autoboxer {
        override val omitConstructorAndDestructor = true

        override fun getBoxedType(context: EmergeLlvmContext): EmergeClassType {
            return boxedTypeGetter(context)
        }

        override fun getTypeinfoNameOverrideInContext(context: EmergeLlvmContext): CanonicalElementName.BaseType? {
            return primitiveTypeGetter(context).canonicalName
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

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun transformForAssignmentTo(
            llvmValue: LlvmValue<*>,
            toType: IrType
        ): LlvmValue<*> {
            check(llvmValue.type == unboxedType)
            val boxedType = getBoxedType(context)
            val box = call(boxedType.constructor, listOf(llvmValue)).abortOnException { exceptionPtr ->
                propagateOrPanic(exceptionPtr, "autoboxing failed; constructor of ${boxedType.irClass.canonicalName} threw")
            }

            return box
        }

        override fun isBox(context: EmergeLlvmContext, value: IrTemporaryValueReference): Boolean {
            if (value.type.isNullable) {
                return true
            }

            val valueTypeBound = value.type.findSimpleTypeBound()
            if (valueTypeBound.baseType != primitiveTypeGetter(context)) {
                return true
            }

            return false
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun unbox(value: IrTemporaryValueReference): LlvmValue<*> {
            val boxedType = getBoxedType(context)
            val valueHolderMember = boxedType.irClass.memberVariables.single { it.name == boxValueHoldingMemberVariableName }
            val valueAsBoxPtr = value.declaration.llvmValue.reinterpretAs(pointerTo(boxedType))
            return getelementptr(valueAsBoxPtr)
                .member(valueHolderMember)
                .get()
                .dereference()
        }
    }

    /**
     * Used for bridging `emerge.core.reflection.ReflectionBaseType` to [TypeinfoType]
     */
    object ReflectionBaseType : Autoboxer {
        override val omitConstructorAndDestructor = true

        override fun getBoxedType(context: EmergeLlvmContext): EmergeClassType {
            return context.boxTypeReflectionBaseType
        }

        override fun getTypeinfoNameOverrideInContext(context: EmergeLlvmContext): CanonicalElementName.BaseType? {
            return context.rawReflectionBaseTypeClazz.canonicalName
        }

        override val unboxedType: LlvmType get() = pointerTo(TypeinfoType.GENERIC)

        private val memberVariableMappings: Map<String, TypeinfoType.() -> LlvmStructType.Member<TypeinfoType, *>> = mapOf(
            "supertypes" to { supertypes },
            "canonicalName" to { canonicalNamePtr },
            "dynamicInstance" to { dynamicTypeInfoPtr },
        )

        override fun isAccessingIntoTheBox(
            context: EmergeLlvmContext,
            readAccess: IrClassMemberVariableAccessExpression
        ): Boolean {
            check(readAccess.base.type.autoboxer === this)
            return readAccess.memberVariable.name in memberVariableMappings
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun rewriteAccessIntoTheBox(readAccess: IrClassMemberVariableAccessExpression): LlvmValue<*> {
            val baseValue = readAccess.base.declaration.llvmValue
            check(baseValue.type is LlvmPointerType<*> && baseValue.type.pointed is TypeinfoType) {
                "cannot rewrite this access, base value needs to be a pointer to typeinfo"
            }
            @Suppress("UNCHECKED_CAST")
            baseValue as LlvmValue<LlvmPointerType<TypeinfoType>>

            return getelementptr(baseValue)
                .member {
                    memberVariableMappings.getValue(readAccess.memberVariable.name).invoke(this) as LlvmStructType.Member<TypeinfoType, LlvmType>
                }
                .get()
                .dereference()
        }

        override fun assignmentRequiresTransformation(context: EmergeLlvmContext, toType: IrType): Boolean {
            if (!toType.isNullable && toType is IrSimpleType && toType.baseType == context.rawReflectionBaseTypeClazz) {
                return false
            }

            return true
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun transformForAssignmentTo(
            llvmValue: LlvmValue<*>,
            toType: IrType
        ): LlvmValue<*> {
            check(llvmValue.type is LlvmPointerType<*> && llvmValue.type.pointed is TypeinfoType) {
                "transformForAssignmentTo called on a value of unsupported type"
            }
            llvmValue as LlvmValue<LlvmPointerType<TypeinfoType>>
            val boxedType = getBoxedType(context)
            val boxed = PhiBucket(pointerTo(boxedType))
            conditionalBranch(
                condition = isNull(llvmValue),
                ifTrue = {
                    boxed.setBranchResult(context.nullValue(boxed.type))
                    concludeBranch()
                },
                ifFalse = {
                    boxed.setBranchResult(call(boxedType.constructor, listOf(llvmValue)).abortOnException { exceptionPtr ->
                        propagateOrPanic(exceptionPtr, "autoboxing failed; constructor of ${boxedType.irClass.canonicalName} threw")
                    })
                    concludeBranch()
                }
            )
            val box = boxed.buildPhi()

            return box
        }

        override fun isBox(context: EmergeLlvmContext, value: IrTemporaryValueReference): Boolean {
            if (value.type.isNullable) {
                return true
            }

            val valueTypeBound = value.type.findSimpleTypeBound()
            if (valueTypeBound.baseType != context.rawReflectionBaseTypeClazz) {
                return true
            }

            return false
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun unbox(value: IrTemporaryValueReference): LlvmValue<*> {
            val boxedType = getBoxedType(context)
            val valueHolderMember = boxedType.irClass.memberVariables.single { it.name == "value" }
            val valueAsBoxPtr = value.declaration.llvmValue.reinterpretAs(pointerTo(boxedType))
            return getelementptr(valueAsBoxPtr)
                .member(valueHolderMember)
                .get()
                .dereference()
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
        override val omitConstructorAndDestructor = false

        override fun getBoxedType(context: EmergeLlvmContext): EmergeClassType {
            return boxedTypeGetter(context)
        }

        override fun getTypeinfoNameOverrideInContext(context: EmergeLlvmContext): CanonicalElementName.BaseType? {
            return null
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

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun transformForAssignmentTo(
            llvmValue: LlvmValue<*>,
            toType: IrType
        ): LlvmValue<*> {
            check(llvmValue.type == unboxedType)
            val boxedType = getBoxedType(context)
            val box = call(boxedType.constructor, listOf(llvmValue)).abortOnException { exceptionPtr ->
                propagateOrPanic(exceptionPtr, "autoboxing failed; constructor of ${boxedType.irClass.canonicalName} threw")
            }

            return box
        }

        override fun isBox(context: EmergeLlvmContext, value: IrTemporaryValueReference): Boolean {
            return false
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun unbox(value: IrTemporaryValueReference): LlvmValue<*> {
            throw UnsupportedOperationException("Cannot unbox a C FFI pointer")
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
            return assureBoxed(value.declaration.llvmValue, value.type, targetType)
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        fun assureBoxed(llvmValue: LlvmValue<*>, irTypeOfValue: IrType, targetIrType: IrType): LlvmValue<*> {
            if (irTypeOfValue.independentEquals(targetIrType)) {
                return llvmValue
            }

            val autoboxer = irTypeOfValue.autoboxer
            if (autoboxer == null || !autoboxer.assignmentRequiresTransformation(context, targetIrType)) {
                return llvmValue
            }
            return autoboxer.transformForAssignmentTo(llvmValue, targetIrType)
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        fun assureUnboxed(value: IrTemporaryValueReference): LlvmValue<*> {
            val autoboxer = value.declaration.type.autoboxer!!
            if (!autoboxer.isBox(context, value)) {
                return value.declaration.llvmValue
            }

            return autoboxer.unbox(value)
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