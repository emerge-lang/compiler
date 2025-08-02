package io.github.tmarsteel.emerge.backend.llvm

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
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
import io.github.tmarsteel.emerge.common.CanonicalElementName

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
     * to be invoked on the [Autoboxer] of the [IrClassFieldAccessExpression.base]s type. If this function
     * returns `true` the [readAccess] must be rewritten using [rewriteAccessIntoTheBox].
     */
    fun isAccessingIntoTheBox(context: EmergeLlvmContext, readAccess: IrClassFieldAccessExpression): Boolean

    /**
     * @see isAccessingIntoTheBox
     * Inserts instructions on the [BasicBlockBuilder] that perform the correct steps for accessing the boxed value
     * @return the unboxed value
     */
    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun rewriteAccessIntoTheBox(readAccess: IrClassFieldAccessExpression): LlvmValue<*>

    /**
     * Given a value of the type this autoboxer is responsible for should be stored in a reference of type [IrType].
     * @return whether storing the value there requires boxing it.
     */
    fun isBox(context: EmergeLlvmContext, type: IrType): Boolean

    /**
     * Given [llvmValue] is of some type `T` for which [isBox] = `false` inserts instructions on the [BasicBlockBuilder]
     * that create a box around [llvmValue]
     * @return the boxed value
     */
    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun box(llvmValue: LlvmValue<*>): LlvmValue<*>

    /**
     * Assumes [value] is a box according to [isBox] and that [value] does not hold a
     * null value at runtime, even if its type is nullable.
     */
    context(BasicBlockBuilder<EmergeLlvmContext, *>)
    fun unbox(llvmValue: LlvmValue<*>): LlvmValue<*>

    fun getReferenceSiteType(context: EmergeLlvmContext, referenceSiteType: IrType, forceBoxed: Boolean): LlvmType {
        return if (forceBoxed || referenceSiteType.isNullable) pointerTo(getBoxedType(context)) else unboxedType
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
            readAccess: IrClassFieldAccessExpression
        ): Boolean = false

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun rewriteAccessIntoTheBox(readAccess: IrClassFieldAccessExpression): LlvmValue<*> {
            throw UnsupportedOperationException("cannot access into an unboxed type")
        }

        override fun isBox(context: EmergeLlvmContext, type: IrType): Boolean {
            if (type.isNullable) {
                return true
            }

            val valueTypeBound = type.findSimpleTypeBound()
            if (valueTypeBound.baseType != primitiveTypeGetter(context)) {
                return true
            }

            return false
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun box(llvmValue: LlvmValue<*>): LlvmValue<*> {
            check(llvmValue.type == unboxedType) {
                "cannot box an ${llvmValue.type} as a $unboxedType"
            }
            val boxedType = getBoxedType(context)
            val box = call(boxedType.constructor, listOf(llvmValue)).abortOnException { exceptionPtr ->
                propagateOrPanic(exceptionPtr, "autoboxing failed; constructor of ${boxedType.irClass.canonicalName} threw")
            }

            return box
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun unbox(llvmValue: LlvmValue<*>): LlvmValue<*> {
            val boxedType = getBoxedType(context)
            val valueHolderMember = boxedType.irClass.fields.single()
            val valueAsBoxPtr = llvmValue.reinterpretAs(pointerTo(boxedType))
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
            readAccess: IrClassFieldAccessExpression
        ): Boolean {
            check(readAccess.base.type.autoboxer === this)
            return readAccess.memberVariable?.name in memberVariableMappings
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun rewriteAccessIntoTheBox(readAccess: IrClassFieldAccessExpression): LlvmValue<*> {
            val baseValue = readAccess.base.declaration.llvmValue
            check(baseValue.type is LlvmPointerType<*> && baseValue.type.pointed is TypeinfoType) {
                "cannot rewrite this access, base value needs to be a pointer to typeinfo"
            }
            @Suppress("UNCHECKED_CAST")
            baseValue as LlvmValue<LlvmPointerType<TypeinfoType>>

            return getelementptr(baseValue)
                .member {
                    memberVariableMappings.getValue(readAccess.memberVariable!!.name).invoke(this) as LlvmStructType.Member<TypeinfoType, LlvmType>
                }
                .get()
                .dereference()
        }

        override fun isBox(context: EmergeLlvmContext, type: IrType): Boolean {
            if (type.isNullable) {
                return true
            }

            val valueTypeBound = type.findSimpleTypeBound()
            if (valueTypeBound.baseType != context.rawReflectionBaseTypeClazz) {
                return true
            }

            return false
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun box(llvmValue: LlvmValue<*>, ): LlvmValue<*> {
            check(llvmValue.type is LlvmPointerType<*> && llvmValue.type.pointed is TypeinfoType) {
                "${Autoboxer::box} called on a value of unsupported type"
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

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun unbox(llvmValue: LlvmValue<*>): LlvmValue<*> {
            val boxedType = getBoxedType(context)
            val valueHolderMember = boxedType.irClass.memberVariables.single { it.name == "value" }
                .readStrategy
                .let { it as IrClass.MemberVariable.AccessStrategy.BareField }
                .let { accessStrat -> boxedType.irClass.fields.single { it.id == accessStrat.fieldId } }

            val valueAsBoxPtr = llvmValue.reinterpretAs(pointerTo(boxedType))
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
            readAccess: IrClassFieldAccessExpression,
        ): Boolean {
            check(readAccess.base.type.autoboxer === this)
            return readAccess.memberVariable?.name == memberVariableNameToAccessUnboxedValue
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun rewriteAccessIntoTheBox(readAccess: IrClassFieldAccessExpression): LlvmValue<*> {
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
                require(emergeClazz.irClass.fields.size == 1)
                val template = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmPointerType<EmergeClassType>>(
                    name.toString(),
                    pointerTo(emergeClazz),
                ) {
                    val unboxedValue by param(unboxedType)

                    body {
                        val heapAllocation = emergeClazz.allocateUninitializedDynamicObject(this)
                        store(unboxedValue, getelementptr(heapAllocation).member(emergeClazz.irClass.fields.single()).get())
                        ret(heapAllocation)
                    }
                }
                context.registerIntrinsic(template)
            }
        }

        fun getDestructorIntrinsic(context: EmergeLlvmContext): LlvmFunction<LlvmVoidType> {
            return context.registerIntrinsic(boxDestructor)
        }

        override fun isBox(context: EmergeLlvmContext, type: IrType): Boolean {
            if (type is IrSimpleType && type.baseType == getBoxedType(context).irClass) {
                // nullability is not relevant here; a null reference in emerge is a perfectly fine null pointer in C
                return false
            }

            return true
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun box(llvmValue: LlvmValue<*>): LlvmValue<*> {
            check(llvmValue.type == unboxedType)
            val boxedType = getBoxedType(context)
            val box = call(boxedType.constructor, listOf(llvmValue)).abortOnException { exceptionPtr ->
                propagateOrPanic(exceptionPtr, "autoboxing failed; constructor of ${boxedType.irClass.canonicalName} threw")
            }

            return box
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        override fun unbox(llvmValue: LlvmValue<*>): LlvmValue<*> {
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
         * Performs necessary auto boxing or unboxing on [value] before the value is to be used
         * with the semantics of [targetType]. E.g.
         * * if [value] is of type `S8` and [targetType] is `Any`, emits creation of a box.
         * * if [value] is of type `S8?` and [targetType] is `S8`, emits code that takes the value from inside the box
         */
        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        fun autoBoxOrUnbox(value: IrTemporaryValueReference, targetType: IrType): LlvmValue<*> {
            return autoBoxOrUnbox(value.declaration.llvmValue, value.type, targetType)
        }

        /**
         * @see autoBoxOrUnbox
         */
        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        fun autoBoxOrUnbox(llvmValue: LlvmValue<*>, irTypeOfValue: IrType, targetIrType: IrType): LlvmValue<*> {
            if (irTypeOfValue.independentEquals(targetIrType)) {
                // ir types identical -> no autoboxing needed
                return llvmValue
            }

            val valueAutoboxer = irTypeOfValue.autoboxer
            val targetAutoboxer = targetIrType.autoboxer
            if (valueAutoboxer == null && targetAutoboxer == null) {
                // neither source type nor target type have autoboxing semantics -> no autoboxing needed
                return llvmValue
            }

            if (valueAutoboxer == null) {
                // the source type doesn't have autoboxing semantics
                check(targetAutoboxer != null) { "assured by previous check" }
                check(targetAutoboxer.isBox(context, irTypeOfValue))
                return when {
                    targetAutoboxer.isBox(context, targetIrType) -> llvmValue
                    llvmValue.type == targetAutoboxer.unboxedType -> llvmValue
                    else -> targetAutoboxer.unbox(llvmValue)
                }
            }

            if (targetAutoboxer == null) {
                return when {
                    valueAutoboxer.isBox(context, irTypeOfValue) -> llvmValue
                    else -> valueAutoboxer.box(llvmValue)
                }
            }

            check(valueAutoboxer === targetAutoboxer) {
                "autoboxing cannot convert between types - value is $irTypeOfValue, target is $targetIrType (${currentDebugLocation()})"
            }

            val valueIsBox = valueAutoboxer.isBox(context, irTypeOfValue)
            val targetIsBox = targetAutoboxer.isBox(context, targetIrType)

            return when {
                valueIsBox == targetIsBox -> llvmValue
                valueIsBox -> valueAutoboxer.unbox(llvmValue)
                else -> {
                    check(!valueIsBox && targetIsBox)
                    targetAutoboxer.box(llvmValue)
                }
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