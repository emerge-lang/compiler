package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmCachedType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFixedIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmNamedStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef

internal object EmergeWordType : LlvmCachedType(), LlvmIntegerType {
    override fun getNBitsInContext(context: LlvmContext): Int = context.targetData.pointerSizeInBytes * 8
    override fun computeRaw(context: LlvmContext) = Llvm.LLVMIntTypeInContext(context.ref, getNBitsInContext(context))
    override fun toString() = "%word"
    override fun isAssignableTo(other: LlvmType): Boolean {
        return isLlvmAssignableTo(other)
    }

    override fun isLlvmAssignableTo(target: LlvmType): Boolean {
        // bit width depends on context, assume yes
        return target is LlvmIntegerType
    }
}

internal fun LlvmContext.word(value: Int): LlvmConstant<EmergeWordType> {
    val wordMax = EmergeWordType.getMaxUnsignedValueInContext(this)
    check (value.toBigInteger() <= wordMax) {
        "The value $value cannot be represented by the word type on this target (max $wordMax)"
    }

    return LlvmConstant(
        Llvm.LLVMConstInt(EmergeWordType.getRawInContext(this), value.toLong(), 0),
        EmergeWordType,
    )
}

internal fun LlvmContext.word(value: Long): LlvmConstant<EmergeWordType> {
    val wordMax = EmergeWordType.getMaxUnsignedValueInContext(this)
    check (value.toBigInteger() <= wordMax) {
        "The value $value cannot be represented by the word type on this target (max $wordMax)"
    }

    return LlvmConstant(
        Llvm.LLVMConstInt(EmergeWordType.getRawInContext(this), value, 0),
        EmergeWordType,
    )
}

internal fun LlvmContext.word(value: ULong): LlvmConstant<EmergeWordType> = word(value.toLong())

internal object EmergeAnyValueVirtualsType : LlvmNamedStructType("anyvalue_virtuals") {
    val finalizeFunction by structMember(LlvmFunctionAddressType)

    val finalizeFunctionType = LlvmFunctionType(LlvmVoidType, listOf(PointerToAnyEmergeValue))
}

internal val PointerToAnyEmergeValue: LlvmPointerType<out EmergeHeapAllocated> by lazy { pointerTo(EmergeHeapAllocatedValueBaseType) }

internal object EmergeWeakReferenceCollectionType : LlvmNamedStructType("weakrefcoll") {
    /**
     * pointers to the actual memory locations where a pointer to another object is kept. In practice this
     * will exclusively be the addresses of the `value` member in the `emerge.core.Weak` class.
     */
    val pointersToWeakReferences by structMember(
        LlvmArrayType(10, pointerTo(PointerToAnyEmergeValue)),
    )
    val next by structMember(pointerTo(this@EmergeWeakReferenceCollectionType))
}

/**
 * The data common to all heap-allocated objects in emerge
 */
internal object EmergeHeapAllocatedValueBaseType : LlvmNamedStructType("anyvalue"), EmergeHeapAllocated {
    val strongReferenceCount by structMember(EmergeWordType)
    val typeinfo by structMember(pointerTo(TypeinfoType.GENERIC))
    val weakReferenceCollection by structMember(pointerTo(EmergeWeakReferenceCollectionType))

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>,
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        require(value.type is LlvmPointerType<*>)
        return builder.getelementptr(value.reinterpretAs(pointerTo(this)))
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LlvmTypeRef) {
        // this is AnyValue itself, noop
    }
}

internal interface EmergeHeapAllocated : LlvmType {
    fun pointerToCommonBase(builder: BasicBlockBuilder<*, *>, value: LlvmValue<*>): GetElementPointerStep<EmergeHeapAllocatedValueBaseType>

    /**
     * This abstract method is a reminder to check *at emerge compile time* that your subtype of [EmergeHeapAllocated]#
     * can actually be [LlvmValue.reinterpretAs] any([EmergeHeapAllocatedValueBaseType]).
     * @throws CodeGenerationException if that is not the case.
     */
    fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LlvmTypeRef)
}

/**
 * Returned by all emerge functions that are not declared `nothrow`. As I currently dread getting a C++-ABI compatible
 * unwinding library to work, this is the mechanism by which exceptions propagate. Yep, no landingpads or cleanuppads are used.
 */
internal sealed interface EmergeFallibleCallResult<Value : LlvmType> : LlvmType {

    context(builder: BasicBlockBuilder<C, R>)
    fun <C : EmergeLlvmContext, R : LlvmType> handle(
        compoundReturnValue: LlvmValue<EmergeFallibleCallResult<Value>>,
        regularBranch: BasicBlockBuilder.Branch<C, R>.(LlvmValue<Value>) -> BasicBlockBuilder.Termination,
        exceptionBranch: BasicBlockBuilder.Branch<C, R>.(LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
    )

    context(builder: BasicBlockBuilder<C, R>)
    fun <C : EmergeLlvmContext, R : LlvmType> abortOnException(
        compoundReturnValue: LlvmValue<EmergeFallibleCallResult<Value>>,
        abortBuilder: ExceptionAbortBuilder<C, R>,
        doAbort: ExceptionAbortBuilder<C, R>.(LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
    ): LlvmValue<Value>

    class WithValue<Value : LlvmType> private constructor(valueType: Value) : EmergeFallibleCallResult<Value>, LlvmNamedStructType(packed = false, name = buildTypeName(valueType)) {
        val exceptionPtr by structMember(PointerToAnyEmergeValue)
        val returnValue by structMember(valueType)

        context(builder: BasicBlockBuilder<C, R>)
        override fun <C : EmergeLlvmContext, R : LlvmType> handle(
            compoundReturnValue: LlvmValue<EmergeFallibleCallResult<Value>>,
            regularBranch: BasicBlockBuilder.Branch<C, R>.(LlvmValue<Value>) -> BasicBlockBuilder.Termination,
            exceptionBranch: BasicBlockBuilder.Branch<C, R>.(LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
        ) {
            with(builder) {
                @Suppress("UNCHECKED_CAST")
                compoundReturnValue as LlvmValue<WithValue<Value>>
                val exceptionPtr = extractValue(compoundReturnValue) { exceptionPtr }
                conditionalBranch(
                    condition = isNull(exceptionPtr),
                    ifTrue = {
                        val returnValue = extractValue(compoundReturnValue) { returnValue }
                        regularBranch(returnValue)
                    },
                    ifFalse = {
                        exceptionBranch(exceptionPtr)
                    }
                )
            }
        }

        context(builder: BasicBlockBuilder<C, R>)
        override fun <C : EmergeLlvmContext, R : LlvmType> abortOnException(
            compoundReturnValue: LlvmValue<EmergeFallibleCallResult<Value>>,
            abortBuilder: ExceptionAbortBuilder<C, R>,
            doAbort: ExceptionAbortBuilder<C, R>.(LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
        ): LlvmValue<Value> {
            with(builder) {
                @Suppress("UNCHECKED_CAST")
                compoundReturnValue as LlvmValue<WithValue<Value>>
                val exceptionPtr = extractValue(compoundReturnValue) { exceptionPtr }
                conditionalBranch(
                    condition = isNotNull(exceptionPtr),
                    ifTrue = {
                        abortBuilder.doAbort(exceptionPtr)
                    },
                    branchBlockName = "fallible_result",
                )
                val returnValue = extractValue(compoundReturnValue) { returnValue }
                return returnValue
            }
        }

        override fun isAssignableTo(other: LlvmType): Boolean {
            return other is WithValue<*> && this.returnValue.type.isAssignableTo(other.returnValue.type)
        }

        companion object {
            val ofPointer: WithValue<LlvmPointerType<out EmergeHeapAllocated>> by lazy { WithValue(PointerToAnyEmergeValue) }
            private val ofBool by lazy { WithValue(LlvmBooleanType) }
            private val ofI8 by lazy { WithValue(LlvmI8Type) }
            private val ofI16 by lazy { WithValue(LlvmI16Type) }
            private val ofI32 by lazy { WithValue(LlvmI32Type) }
            private val ofI64 by lazy { WithValue(LlvmI64Type) }
            private val ofWord by lazy { WithValue(EmergeWordType) }

            @Suppress("UNCHECKED_CAST")
            operator fun <Value : LlvmType> invoke(valueType: Value): WithValue<Value> {
                require(valueType !is LlvmVoidType)

                if (valueType == EmergeWordType) {
                    return ofWord as WithValue<Value>
                }
                if (valueType is LlvmPointerType<*>) {
                    return ofPointer as WithValue<Value>
                }
                if (valueType is LlvmFixedIntegerType) {
                    when (valueType.nBits) {
                        1 -> return ofBool as WithValue<Value>
                        8 -> return ofI8 as WithValue<Value>
                        16 -> return ofI16 as WithValue<Value>
                        32 -> return ofI32 as WithValue<Value>
                        64 -> return ofI64 as WithValue<Value>
                        else -> {}
                    }
                }

                return WithValue(valueType)
            }

            private fun buildTypeName(nakedResultType: LlvmType): String {
                return "exc_or_" + (
                    nakedResultType.toString()
                        .replace(Regex("^\\*(.+)$")) { it.groupValues[1] + "ptr" }
                        .replace("%", "")
                )
            }
        }
    }

    object OfVoid : EmergeFallibleCallResult<LlvmVoidType>, LlvmType {
        override fun getRawInContext(context: LlvmContext): LlvmTypeRef {
            return PointerToAnyEmergeValue.getRawInContext(context)
        }

        override fun toString(): String {
            return PointerToAnyEmergeValue.toString()
        }

        context(builder: BasicBlockBuilder<C, R>)
        override fun <C : EmergeLlvmContext, R : LlvmType> handle(
            compoundReturnValue: LlvmValue<EmergeFallibleCallResult<LlvmVoidType>>,
            regularBranch: BasicBlockBuilder.Branch<C, R>.(LlvmValue<LlvmVoidType>) -> BasicBlockBuilder.Termination,
            exceptionBranch: BasicBlockBuilder.Branch<C, R>.(LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
        ) {
            with(builder) {
                val exceptionPtr = compoundReturnValue.reinterpretAs(PointerToAnyEmergeValue)
                conditionalBranch(
                    condition = isNull(exceptionPtr),
                    ifTrue = {
                        regularBranch(context.poisonValue(LlvmVoidType))
                    },
                    ifFalse = {
                        exceptionBranch(exceptionPtr)
                    },
                    branchBlockName = "propagate_exc",
                )
            }
        }

        context(builder: BasicBlockBuilder<C, R>)
        override fun <C : EmergeLlvmContext, R : LlvmType> abortOnException(
            compoundReturnValue: LlvmValue<EmergeFallibleCallResult<LlvmVoidType>>,
            abortBuilder: ExceptionAbortBuilder<C, R>,
            doAbort: ExceptionAbortBuilder<C, R>.(LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
        ): LlvmValue<LlvmVoidType> {
            with(builder) {
                val exceptionPtr = compoundReturnValue.reinterpretAs(PointerToAnyEmergeValue)
                conditionalBranch(
                    condition = isNotNull(exceptionPtr),
                    ifTrue = {
                        abortBuilder.doAbort(exceptionPtr)
                    },
                    branchBlockName = "fallible_result",
                )

                return context.poisonValue(LlvmVoidType)
            }
        }

        override fun isAssignableTo(other: LlvmType): Boolean {
            return other is OfVoid
        }

        override fun isLlvmAssignableTo(target: LlvmType): Boolean {
            return target is OfVoid || target is LlvmPointerType<*>
        }
    }

    companion object {


        val ofEmergeReference: WithValue<LlvmPointerType<out EmergeHeapAllocated>>
            get() = WithValue.ofPointer

        @Suppress("UNCHECKED_CAST")
        operator fun <Value : LlvmType> invoke(valueType: Value): EmergeFallibleCallResult<Value> {
            if (valueType == LlvmVoidType) {
                return OfVoid as EmergeFallibleCallResult<Value>
            }

            return WithValue.invoke(valueType)
        }

        context(builder: BasicBlockBuilder<*, WithValue<T>>)
        fun <T : LlvmType> fallibleSuccess(value: LlvmValue<T>): LlvmValue<EmergeFallibleCallResult.WithValue<T>> {
            with(builder) {
                var compoundValue = llvmFunctionReturnType.buildConstantIn(context) {
                    setNull(llvmFunctionReturnType.returnValue)
                    setNull(llvmFunctionReturnType.exceptionPtr)
                } as LlvmValue<WithValue<T>>
                compoundValue = insertValue(compoundValue, value) { llvmFunctionReturnType.returnValue }
                return compoundValue
            }
        }

        context(builder: BasicBlockBuilder<*, out EmergeFallibleCallResult<*>>)
        fun fallibleFailure(exceptionPointer: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>): BasicBlockBuilder.Termination {
            with(builder) {
                when (llvmFunctionReturnType) {
                    is WithValue<*> -> {
                        val llvmReturnTypeAsWithValue = llvmFunctionReturnType as WithValue<LlvmType>
                        var compoundValue = llvmReturnTypeAsWithValue.buildConstantIn(context) {
                            setPoison(llvmReturnTypeAsWithValue.returnValue)
                            setNull(llvmReturnTypeAsWithValue.exceptionPtr)
                        } as LlvmValue<WithValue<LlvmType>>
                        compoundValue = insertValue(compoundValue, exceptionPointer) { exceptionPtr }
                        return ret(compoundValue as LlvmValue<Nothing>)
                    }
                    is OfVoid -> {
                        return ret(exceptionPointer.reinterpretAs(OfVoid) as LlvmValue<Nothing>)
                    }
                }
            }
        }

        /**
         * Given a returned [compoundReturnValue] of `this` type, interprets it and transfers control either to [regularBranch] if the
         * call was successful or to [exceptionBranch] if the call resulted in an exception.
         */
        context(builder: BasicBlockBuilder<C, R>)
        fun <C : EmergeLlvmContext, R : LlvmType, Value : LlvmType> LlvmValue<EmergeFallibleCallResult<Value>>.handle(
            regularBranch: BasicBlockBuilder.Branch<C, R>.(returnValue: LlvmValue<Value>) -> BasicBlockBuilder.Termination,
            exceptionBranch: BasicBlockBuilder.Branch<C, R>.(exceptionPtr: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
        ) {
            this@handle.type.handle(this, regularBranch, exceptionBranch)
        }

        /**
         * Transfers control to [doAbort] in case the compound value resembles a raised exception.
         * @param doAbort must either return from the currently executing function (e.g. to propagate the exception
         * further up) or panic the process
         * @return the actual return value, after having moved the [BasicBlockBuilder] to a new basic-block which
         * only executes on the successful-return path
         */
        context(builder: BasicBlockBuilder<C, R>)
        fun <C : EmergeLlvmContext, R : LlvmType, Value : LlvmType> LlvmValue<EmergeFallibleCallResult<Value>>.abortOnException(
            doAbort: ExceptionAbortBuilder<C, R>.(exceptionPtr: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>) -> BasicBlockBuilder.Termination
        ): LlvmValue<Value> {
            return this@abortOnException.type.abortOnException(
                this@abortOnException,
                ExceptionAbortBuilder(builder, this),
                doAbort
            )
        }

        class ExceptionAbortBuilder<C : EmergeLlvmContext, R : LlvmType>(
            parentBuilder: BasicBlockBuilder<C, R>,
            private val compoundResult: LlvmValue<EmergeFallibleCallResult<*>>,
        ) : BasicBlockBuilder<C, R> by parentBuilder {
            fun propagateOrPanic(
                exceptionPtr: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>,
                panicMessage: String = "unhandled exception in nothrow code"
            ): BasicBlockBuilder.Termination {
                if (this.llvmFunctionReturnType is EmergeFallibleCallResult<*>) {
                    // we can propagate, but we need to pay attention to use the correct actual value type
                    if (compoundResult.type.isAssignableTo(this.llvmFunctionReturnType)) {
                        return ret(compoundResult as LlvmValue<R>)
                    }

                    if (this.llvmFunctionReturnType is OfVoid) {
                        return ret(exceptionPtr as LlvmValue<R>)
                    }

                    val withValueReturnType = this.llvmFunctionReturnType as WithValue<LlvmType>
                    var newCompoundReturnValue = withValueReturnType.buildConstantIn(context) {
                        setValue(
                            withValueReturnType.returnValue,
                            context.poisonValue(withValueReturnType.returnValue.type),
                        )
                        setNull(withValueReturnType.exceptionPtr)
                    } as LlvmValue<WithValue<R>>
                    newCompoundReturnValue = insertValue(newCompoundReturnValue, exceptionPtr) { this@insertValue.exceptionPtr }
                    return ret(newCompoundReturnValue as LlvmValue<R>)
                }

                // this function is nothrow and is catching an exception from a child call; can only panic
                return inlinePanic(panicMessage)
            }
        }

        fun BasicBlockBuilder<*, OfVoid>.retFallibleVoid(): BasicBlockBuilder.Termination {
            return ret(context.nullValue(PointerToAnyEmergeValue).reinterpretAs(OfVoid))
        }
    }
}