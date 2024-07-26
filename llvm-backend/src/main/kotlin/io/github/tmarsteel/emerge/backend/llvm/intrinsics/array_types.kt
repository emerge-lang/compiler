package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.codegen.sizeof
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFixedIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmInlineStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmNamedStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.UnsignedWordAddWithOverflow
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.abortOnException
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.fallibleSuccess
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.retFallibleVoid
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.instructionAliasAttributes
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef

internal object EmergeArrayBaseType : LlvmNamedStructType("anyarray"), EmergeHeapAllocated {
    val anyBase by structMember(EmergeHeapAllocatedValueBaseType)
    val elementCount by structMember(EmergeWordType)

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        require(value.type is LlvmPointerType<*>)
        with(builder) {
            return getelementptr(value.reinterpretAs(pointerTo(this@EmergeArrayBaseType))).member { anyBase }
        }
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LlvmTypeRef) {
        check(Llvm.LLVMOffsetOfElement(context.targetData.ref, selfInContext, anyBase.indexInStruct) == 0L)
    }
}

internal class EmergeArrayType<Element : LlvmType>(
    elementTypeName: String,

    val elementType: Element,

    /**
     * A function of the signature (self: Array<Element>, index: UWord) -> Any, to be placed in the vtable.
     * This is important for arrays of primitives, as this function will do the automatic boxing (e.g. S8 -> S8Box)
     */
    private val virtualGetterWithFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<LlvmPointerType<out EmergeHeapAllocated>>>,

    /**
     * A function of the signature (self: Array<Element>, index: UWord) -> Any, to be placed in the vtable.
     * This is important for arrays of primitives, as this function will do the automatic boxing (e.g. S8 -> S8Box)
     */
    private val virtualGetterWithPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>>,

    /**
     * A function of the signature (self: Array<Element>, index: UWord, value: Any) -> Unit, to be placed in the vtable.
     * This is important for arrays of primitives, as this function will do the automatic unboxing (e.g. S8Box -> S8)
     */
    private val virtualSetterWithFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid>,

    /**
     * A function of the signature (self: Array<Element>, index: UWord, value: Any) -> Unit, to be placed in the vtable.
     * This is important for arrays of primitives, as this function will do the automatic unboxing (e.g. S8Box -> S8)
     */
    private val virtualSetterWithPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * like [virtualGetterWithFallibleBoundsCheck], but doesn't do any boxing; assumes the caller knows the binary types.
     */
    val rawGetterWithFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<Element>>,

    /**
     * like [virtualGetterWithFallibleBoundsCheck], but doesn't do any boxing; assumes the caller knows the binary types.
     */
    val rawGetterWithPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,

    /**
     * like [rawGetterWithFallibleBoundsCheck], but doesn't check the bounds; hence also nothrow.
     */
    val rawGetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,

    /**
     * like [virtualSetterWithFallibleBoundsCheck], but doesn't do any unboxing; assumes the caller knows the binary types.
     */
    val rawSetterWithFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid>,

    /**
     * like [virtualSetterWithFallibleBoundsCheck], but doesn't do any unboxing; assumes the caller knows the binary types.
     */
    val rawSetterWithPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * like [rawSetterWithFallibleBoundsCheck], but doesn't check the bounds, hence also nothrow
     */
    val rawSetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * the finalizer for this array type
     */
    private val finalizer: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * A function of the signature (size: UWord, defaultValue: Element) -> Array<Element> that creates a new array
     * of the given size and sets all the elements to the given value.
     */
    val defaultValueConstructor: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>>,

    val supertypes: Iterable<StaticAndDynamicTypeInfo.Provider>,
) : LlvmNamedStructType("array_$elementTypeName"), EmergeHeapAllocated {
    val base by structMember(EmergeArrayBaseType)
    val elements by structMember(LlvmArrayType(0L, elementType))

    val typeinfo = StaticAndDynamicTypeInfo.defineRaw(
        { _ -> name },
        supertypes.map { superTiP -> { ctx: EmergeLlvmContext -> superTiP.provide(ctx).dynamic } },
        { ctx -> ctx.registerIntrinsic(finalizer) },
        { mapOf(
            VIRTUAL_FUNCTION_HASH_GET_ELEMENT_FALLIBLE to registerIntrinsic(virtualGetterWithFallibleBoundsCheck),
            VIRTUAL_FUNCTION_HASH_GET_ELEMENT_PANIC    to registerIntrinsic(virtualGetterWithPanicBoundsCheck),
            VIRTUAL_FUNCTION_HASH_SET_ELEMENT_FALLIBLE to registerIntrinsic(virtualSetterWithFallibleBoundsCheck),
            VIRTUAL_FUNCTION_HASH_SET_ELEMENT_PANIC    to registerIntrinsic(virtualSetterWithPanicBoundsCheck),
        ) },
    )

    /**
     * A constructor that will allocate an array of [this] type, filled with [LlvmContext.undefValue]s. Signature:
     *
     *     declare ptr array_E__ctor(%word elementCount)
     */
    val constructorOfNullEntries: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeArrayType<Element>>> by lazy {
        KotlinLlvmFunction.define(
            super.name + "__ctor",
            pointerTo(this),
        ) {
            val elementCount by param(EmergeWordType)
            body {
                val allocationSizeForContiguousElements = mul(elementType.sizeof(), elementCount)
                val allocationSize = add(this@EmergeArrayType.sizeof(), allocationSizeForContiguousElements)
                val allocation = heapAllocate(allocationSize)
                    .reinterpretAs(pointerTo(this@EmergeArrayType))
                // TODO: check allocation == null, OOM

                // initialize the any
                val anyBasePtr = getelementptr(allocation)
                    .member { base }
                    .member { anyBase }
                    .get()
                store(context.word(1), getelementptr(anyBasePtr).member { strongReferenceCount }.get())
                store(typeinfo.provide(context).dynamic, getelementptr(anyBasePtr).member { typeinfo }.get())
                store(context.nullValue(pointerTo(EmergeWeakReferenceCollectionType)), getelementptr(anyBasePtr).member { weakReferenceCollection }.get())

                // initialize the array
                val arrayElementCountPtr = getelementptr(allocation)
                    .member { base }
                    .member { this@member.elementCount }
                    .get()
                store(elementCount, arrayElementCountPtr)

                // set all the data to 0
                memset(
                    getelementptr(allocation)
                        .member { elements }
                        .index(context.word(0))
                        .get(),
                    context.i8(0),
                    allocationSizeForContiguousElements,
                )

                ret(allocation)
            }
        }
    }

    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        val raw = super.computeRaw(context)
        assureReinterpretableAsAnyValue(context, raw)
        return raw
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LlvmTypeRef) {
        check(Llvm.LLVMOffsetOfElement(context.targetData.ref, selfInContext, base.indexInStruct) == 0L)
    }

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        check(value.type is LlvmPointerType<*>)
        with(builder) {
            return getelementptr(value.reinterpretAs(pointerTo(this@EmergeArrayType)))
                .member { base }
                .member { anyBase }
        }
    }

    fun <Raw> buildConstantIn(
        context: EmergeLlvmContext,
        data: Collection<Raw>,
        rawTransform: (Raw) -> LlvmValue<Element>,
    ): LlvmConstant<LlvmInlineStructType> {
        /*
        there is a problem with constant arrays of the dynamic-array format of emerge:
        array types are declared with [0 x %element] so no space is wasted but getelementptr access
        is well defined. However, declaring a constant "Hello World" string directly against an
        array type is not valid:

        @myString = global %array_i8 { %anyarray { %anyvalue { ... }, i64 11 }, [11 x i8] c"Hello World" }

        LLVM will complain that we put an [13 x i8] where a [0 x i8] should go.
        The solution: declare the global as what it is, but use %array_i8 when referring to it:

        @myString = global { %anyarray, [11 x i8] } { %anyarray { %anyvalue { ... }, i64 11 }, [11 x i8] c"Hello World" }

        and when referring to it:

        define i8 @access_string_constant(i64 %index) {
        entry:
            %elementPointer = getelementptr %array_i8, ptr @myString, i32 0, i32 1, i64 %index
            %value = load i8, ptr %elementPointer
            ret i8 %value
        }

        Hence: here, we don't use ArrayType.buildConstantIn, but hand-roll it to do the typing trick
         */

        val anyArrayBaseConstant = EmergeArrayBaseType.buildConstantIn(context) {
            setValue(EmergeArrayBaseType.anyBase, EmergeHeapAllocatedValueBaseType.buildConstantIn(context) {
                setValue(EmergeHeapAllocatedValueBaseType.strongReferenceCount, context.word(1))
                setValue(EmergeHeapAllocatedValueBaseType.typeinfo, typeinfo.provide(context).static)
                setValue(
                    EmergeHeapAllocatedValueBaseType.weakReferenceCollection,
                    context.nullValue(pointerTo(EmergeWeakReferenceCollectionType))
                )
            })
            setValue(EmergeArrayBaseType.elementCount, context.word(data.size))
        }
        val payload = LlvmArrayType(data.size.toLong(), elementType).buildConstantIn(
            context,
            data.map { rawTransform(it) },
        )

        val inlineConstant = LlvmInlineStructType.buildInlineTypedConstantIn(
            context,
            anyArrayBaseConstant,
            payload
        )

        val anyArrayBaseOffsetInGeneralType = Llvm.LLVMOffsetOfElement(
            context.targetData.ref,
            this.getRawInContext(context),
            base.indexInStruct,
        )
        val anyArrayBaseOffsetInConstant = Llvm.LLVMOffsetOfElement(
            context.targetData.ref,
            inlineConstant.type.getRawInContext(context),
            0,
        )
        check(anyArrayBaseOffsetInConstant == anyArrayBaseOffsetInGeneralType)

        val firstElementOffsetInGeneralType = Llvm.LLVMOffsetOfElement(
            context.targetData.ref,
            this.getRawInContext(context),
            1,
        )
        val firstElementOffsetInConstant = Llvm.LLVMOffsetOfElement(
            context.targetData.ref,
            inlineConstant.type.getRawInContext(context),
            1,
        )
        check(firstElementOffsetInConstant == firstElementOffsetInGeneralType)

        return inlineConstant
    }

    companion object {
        val VIRTUAL_FUNCTION_HASH_GET_ELEMENT_FALLIBLE: ULong = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000uL
        val VIRTUAL_FUNCTION_HASH_GET_ELEMENT_PANIC: ULong    = 0b0100_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000uL
        val VIRTUAL_FUNCTION_HASH_SET_ELEMENT_FALLIBLE: ULong = 0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000uL
        val VIRTUAL_FUNCTION_HASH_SET_ELEMENT_PANIC: ULong    = 0b1100_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000uL
    }
}

internal val valueArrayFinalize = KotlinLlvmFunction.define<EmergeLlvmContext, _>("emerge.platform.finalizeValueArray", LlvmVoidType) {
    param(PointerToAnyEmergeValue)
    body {
        // nothing to do. There are no references, just values, so no dropping needed
        retVoid()
    }
}

private fun <Element : LlvmType> buildValueArrayBoxingElementGetterWithFallibleBoundsCheck(
    typeName: String,
    getValueArrayType: () -> EmergeArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
): KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<LlvmPointerType<out EmergeHeapAllocated>>> {
    return KotlinLlvmFunction.define(
        "emerge.platform.array_${typeName}_getBoxed_fallibleBoundsCheck",
        EmergeFallibleCallResult.ofEmergeReference,
    ) {
        val self by param(pointerTo(getValueArrayType()))
        val index by param(EmergeWordType)
        body {
            inlineFallibleBoundsCheck(self, index)

            val raw = getelementptr(self)
                .member { elements }
                .index(index)
                .get()
                .dereference()

            ret(
                call(getBoxType(context).constructor, listOf(raw))
                    .reinterpretAs(EmergeFallibleCallResult.ofEmergeReference)
            )
        }
    }
}

private fun <Element : LlvmType> buildValueArrayBoxingElementGetterWithPanicBoundsCheck(
    typeName: String,
    getValueArrayType: () -> EmergeArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
): KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>> {
    return KotlinLlvmFunction.define(
        "emerge.platform.value_${typeName}_getBoxed_panicBoundsCheck",
        PointerToAnyEmergeValue,
    ) {
        val self by param(pointerTo(getValueArrayType()))
        val index by param(EmergeWordType)
        body {
            inlinePanicBoundsCheck(self, index)

            val raw = getelementptr(self)
                .member { elements }
                .index(index)
                .get()
                .dereference()

            val box = call(getBoxType(context).constructor, listOf(raw)).abortOnException { exceptionPtr ->
                inlinePanic("failed to allocate box - OOM")
            }

            ret(box.reinterpretAs(PointerToAnyEmergeValue))
        }
    }
}

private fun <Element : LlvmType> buildValueArrayBoxingElementSetterWithFallibleBoundsCheck(
    typeName: String,
    getValueArrayType: () -> EmergeArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
): KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid> {
    return KotlinLlvmFunction.define(
        "emerge.platform.array_${typeName}_setBoxed_fallibleBoundsCheck",
        EmergeFallibleCallResult.OfVoid,
    ) {
        val arrayType = getValueArrayType()
        val self by param(pointerTo(arrayType))
        val index by param(EmergeWordType)
        val valueBoxAny by param(PointerToAnyEmergeValue)
        body {
            val boxType = getBoxType(context)
            val valueMember = boxType.irClass.memberVariables.single()
            check(valueMember.name == "value")
            check(context.getReferenceSiteType(valueMember.type) == arrayType.elementType)

            val valueBox = valueBoxAny.reinterpretAs(pointerTo(boxType))

            inlineFallibleBoundsCheck(self, index)
            val raw = getelementptr(valueBox)
                .member(boxType.irClass.memberVariables.single())
                .get()
                .dereference()
                .reinterpretAs(arrayType.elementType)
            val targetPointer = getelementptr(self)
                .member { elements }
                .index(index)
                .get()

            store(raw, targetPointer)
            retFallibleVoid()
        }
    }
}

private fun <Element : LlvmType> buildValueArrayBoxingElementSetterWithPanicBoundsCheck(
    typeName: String,
    getValueArrayType: () -> EmergeArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
): KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    return KotlinLlvmFunction.define(
        "emerge.platform.array_${typeName}_setBoxed_panicBoundsCheck",
        LlvmVoidType,
    ) {
        val arrayType = getValueArrayType()
        val self by param(pointerTo(arrayType))
        val index by param(EmergeWordType)
        val valueBoxAny by param(PointerToAnyEmergeValue)
        body {
            val boxType = getBoxType(context)
            val valueMember = boxType.irClass.memberVariables.single()
            check(valueMember.name == "value")
            check(context.getReferenceSiteType(valueMember.type) == arrayType.elementType)

            val valueBox = valueBoxAny.reinterpretAs(pointerTo(boxType))

            inlinePanicBoundsCheck(self, index)
            val raw = getelementptr(valueBox)
                .member(boxType.irClass.memberVariables.single())
                .get()
                .dereference()
                .reinterpretAs(arrayType.elementType)
            val targetPointer = getelementptr(self)
                .member { elements }
                .index(index)
                .get()

            store(raw, targetPointer)
            retVoid()
        }
    }
}

private fun <Element : LlvmType> buildValueArrayRawGetterWithoutBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>
) : KotlinLlvmFunction<EmergeLlvmContext, Element> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawGet_noBoundsCheck",
        elementType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)
        functionAttribute(LlvmFunctionAttribute.AlwaysInline)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)

        body {
            ret(
                getelementptr(arrayPtr)
                    .member { elements }
                    .index(index)
                    .get()
                    .dereference()
            )
        }
    }
}

private fun <Element : LlvmType> buildValueArrayRawGetterWithFallibleBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
    rawGetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<Element>> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawGetWithFallibleBoundsCheck",
        EmergeFallibleCallResult.WithValue(elementType),
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)

        body {
            inlineFallibleBoundsCheck(arrayPtr, index)
            val raw = call(context.registerIntrinsic(rawGetterNoBoundsCheck), listOf(arrayPtr, index))
            ret(fallibleSuccess(raw))
        }
    }
}

private fun <Element : LlvmType> buildValueArrayRawGetterWithPanicBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
    rawGetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, Element> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawGetWithPanicBoundsCheck",
        elementType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)

        body {
            inlinePanicBoundsCheck(arrayPtr, index)
            val raw = call(context.registerIntrinsic(rawGetterNoBoundsCheck), listOf(arrayPtr, index))
            ret(raw)
        }
    }
}

private fun <Element : LlvmType> buildValueArrayRawSetterWithoutBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawSetNoBoundsCheck",
        LlvmVoidType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)
        functionAttribute(LlvmFunctionAttribute.AlwaysInline)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)
        val value by param(elementType)

        body {
            store(
                value,
                getelementptr(arrayPtr)
                    .member { elements }
                    .index(index)
                    .get()
            )
            retVoid()
        }
    }
}

private fun <Element : LlvmType> buildValueArrayRawSetterWithFallibleBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
    rawSetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,
) : KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawSetWithFallibleBoundsCheck",
        EmergeFallibleCallResult.OfVoid,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)
        val value by param(elementType)

        body {
            inlineFallibleBoundsCheck(arrayPtr, index)
            call(context.registerIntrinsic(rawSetterWithoutBoundsCheck), listOf(arrayPtr, index, value))
            retFallibleVoid()
        }
    }
}

private fun <Element : LlvmType> buildValueArrayRawSetterWithPanicBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
    rawSetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,
) : KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawSetWithPanicBoundsCheck",
        LlvmVoidType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)
        val value by param(elementType)

        body {
            inlinePanicBoundsCheck(arrayPtr, index)
            call(context.registerIntrinsic(rawSetterWithoutBoundsCheck), listOf(arrayPtr, index, value))
            retVoid()
        }
    }
}

private fun <Element : LlvmType> buildValueArrayDefaultValueConstructor(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_defaultValueCtor",
        PointerToAnyEmergeValue,
    ) {
        val size by param(EmergeWordType)
        val defaultValue by param(elementType)

        body {
            val rawSetterNoBoundsCheck = context.registerIntrinsic(getSelfType().rawSetterWithoutBoundsCheck)
            val arrayPtr = call(context.registerIntrinsic(getSelfType().constructorOfNullEntries), listOf(size))
            val indexStack = alloca(EmergeWordType)
            store(context.word(0), indexStack)
            loop(
                header = {
                    conditionalBranch(
                        condition = icmp(indexStack.dereference(), LlvmIntPredicate.EQUAL, size),
                        ifTrue = { this@loop.breakLoop() }
                    )
                    doIteration()
                },
                body = {
                    val index = indexStack.dereference()
                    call(rawSetterNoBoundsCheck, listOf(arrayPtr, index, defaultValue))
                    store(add(index, context.word(1)), indexStack)
                    loopContinue()
                }
            )
            ret(arrayPtr.reinterpretAs(PointerToAnyEmergeValue))
        }
    }
}

private fun <Element : LlvmType> buildValueArrayType(
    elementTypeName: String,
    elementType: Element,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
) : EmergeArrayType<Element> {
    lateinit var arrayTypeHolder: EmergeArrayType<Element>
    val virtualFallibleGetter = buildValueArrayBoxingElementGetterWithFallibleBoundsCheck(elementTypeName, { arrayTypeHolder }, getBoxType)
    val virtualPanicGetter = buildValueArrayBoxingElementGetterWithPanicBoundsCheck(elementTypeName, { arrayTypeHolder }, getBoxType)
    val virtualFallibleSetter = buildValueArrayBoxingElementSetterWithFallibleBoundsCheck(elementTypeName, { arrayTypeHolder }, getBoxType)
    val virtualPanicSetter = buildValueArrayBoxingElementSetterWithPanicBoundsCheck(elementTypeName, { arrayTypeHolder }, getBoxType)
    val rawGetterWithoutBoundsCheck = buildValueArrayRawGetterWithoutBoundsCheck(elementTypeName, elementType, { arrayTypeHolder })
    val rawGetterWithFallibleBoundsCheck = buildValueArrayRawGetterWithFallibleBoundsCheck(elementTypeName, elementType, { arrayTypeHolder }, rawGetterWithoutBoundsCheck)
    val rawGetterWithPanicBoundsCheck = buildValueArrayRawGetterWithPanicBoundsCheck(elementTypeName, elementType, { arrayTypeHolder }, rawGetterWithoutBoundsCheck)
    val rawSetterWithoutBoundsCheck = buildValueArrayRawSetterWithoutBoundsCheck(elementTypeName, elementType, { arrayTypeHolder })
    val rawSetterWithFallibleBoundsCheck = buildValueArrayRawSetterWithFallibleBoundsCheck(elementTypeName, elementType, { arrayTypeHolder }, rawSetterWithoutBoundsCheck)
    val rawSetterWithPanicBoundsCheck = buildValueArrayRawSetterWithPanicBoundsCheck(elementTypeName, elementType, { arrayTypeHolder }, rawSetterWithoutBoundsCheck)
    val defaultValueCtor = buildValueArrayDefaultValueConstructor(elementTypeName, elementType, { arrayTypeHolder })
    arrayTypeHolder = EmergeArrayType(
        elementTypeName,
        elementType,
        virtualFallibleGetter,
        virtualPanicGetter,
        virtualFallibleSetter,
        virtualPanicSetter,
        rawGetterWithFallibleBoundsCheck,
        rawGetterWithPanicBoundsCheck,
        rawGetterWithoutBoundsCheck,
        rawSetterWithFallibleBoundsCheck,
        rawSetterWithPanicBoundsCheck,
        rawSetterWithoutBoundsCheck,
        valueArrayFinalize,
        defaultValueCtor,
        listOf(EmergeReferenceArrayType.typeinfo),
    )

    return arrayTypeHolder
}

/** intrinsic for emerge.std.Array::copy */
private fun <Element : LlvmIntegerType> buildValueArrayCopy(
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    val typename = when (elementType) {
        is EmergeWordType -> "word"
        is LlvmFixedIntegerType -> "i" + elementType.nBits.toString()
        else -> error("Should never happen")
    }
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${typename}_copy",
        LlvmVoidType,
    ) {
        val sourceArrUntypedPtr by param(PointerToAnyEmergeValue)
        val sourceOffset by param(EmergeWordType)
        val destArrayUntypedPtr by param(PointerToAnyEmergeValue)
        val destOffset by param(EmergeWordType)
        val length by param(EmergeWordType)

        body {
            conditionalBranch(
                condition = isZero(length),
                ifTrue = {
                    retVoid()
                }
            )

            val sourceArrPtr = sourceArrUntypedPtr.reinterpretAs(pointerTo(getSelfType()))
            val destArrPtr = destArrayUntypedPtr.reinterpretAs(pointerTo(getSelfType()))

            val sourceSize = getelementptr(sourceArrPtr)
                .member { base }
                .member { elementCount }
                .get()
                .dereference()

            val sourceMinSizeResult = call(UnsignedWordAddWithOverflow, listOf(sourceOffset, length))
            conditionalBranch(
                condition = or(
                    extractValue(sourceMinSizeResult) { hadOverflow },
                    icmp(extractValue(sourceMinSizeResult) { result }, LlvmIntPredicate.UNSIGNED_GREATER_THAN, sourceSize),
                ),
                ifTrue = {
                    inlinePanic("length overflows bounds of source")
                }
            )

            val destSize = getelementptr(destArrPtr)
                .member { base }
                .member { elementCount }
                .get()
                .dereference()

            val destMinSizeResult = call(UnsignedWordAddWithOverflow, listOf(destOffset, length))
            conditionalBranch(
                condition = or(
                    extractValue(destMinSizeResult) { hadOverflow },
                    icmp(extractValue(destMinSizeResult) { result }, LlvmIntPredicate.UNSIGNED_GREATER_THAN, destSize),
                ),
                ifTrue = {
                    inlinePanic("length overflows bounds of dest")
                }
            )

            memcpy(
                destination = getelementptr(destArrPtr)
                    .member { elements }
                    .index(destOffset)
                    .get(),
                source = getelementptr(sourceArrPtr)
                    .member { elements }
                    .index(sourceOffset)
                    .get(),
                mul(elementType.sizeof(), length)
            )

            retVoid()
        }
    }
}

val EmergeBoolArrayCopyFn = buildValueArrayCopy(LlvmBooleanType) { EmergeBooleanArrayType }
val EmergeI8ArrayCopyFn = buildValueArrayCopy(LlvmI8Type) { EmergeU8ArrayType }
val EmergeI16ArrayCopyFn = buildValueArrayCopy(LlvmI16Type) { EmergeU16ArrayType }
val EmergeI32ArrayCopyFn = buildValueArrayCopy(LlvmI32Type) { EmergeU32ArrayType }
val EmergeI64ArrayCopyFn = buildValueArrayCopy(LlvmI64Type) { EmergeU64ArrayType }
val EmergeWordArrayCopyFn = buildValueArrayCopy(EmergeWordType) { EmergeUWordArrayType }

private val referenceArrayElementGetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_get_noBoundsCheck",
    PointerToAnyEmergeValue,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)

    instructionAliasAttributes()

    body {
        val referenceEntry = getelementptr(self)
            .member { elements }
            .index(index)
            .get()
            .dereference()
        referenceEntry.afterReferenceCreated(isNullable = true)
        ret(referenceEntry)
    }
}

private val referenceArrayElementGetterFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<LlvmPointerType<out EmergeHeapAllocated>>> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_get_fallibleBoundsCheck",
    EmergeFallibleCallResult.ofEmergeReference,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    body {
        inlineFallibleBoundsCheck(self, index)
        ret(fallibleSuccess(
            call(context.registerIntrinsic(referenceArrayElementGetterNoBoundsCheck), listOf(self, index))
        ))
    }
}

private val referenceArrayElementGetterPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_get_panicBoundsCheck",
    PointerToAnyEmergeValue,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    body {
        inlinePanicBoundsCheck(self, index)
        ret(
            call(context.registerIntrinsic(referenceArrayElementGetterNoBoundsCheck), listOf(self, index))
        )
    }
}

private val referenceArrayElementSetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_set_noBoundsCheck",
    LlvmVoidType,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    val value by param(PointerToAnyEmergeValue)
    body {
        val pointerToSlotInArray = getelementptr(self)
            .member { elements }
            .index(index)
            .get()
        val previousValue = pointerToSlotInArray.dereference()
        previousValue.afterReferenceDropped(isNullable = true)

        store(value, pointerToSlotInArray)
        value.afterReferenceCreated(isNullable = true)
        retVoid()
    }
}

private val referenceArrayElementSetterFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_set_fallibleBoundsCheck",
    EmergeFallibleCallResult.OfVoid,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    val value by param(PointerToAnyEmergeValue)
    body {
        inlineFallibleBoundsCheck(self, index)
        call(context.registerIntrinsic(referenceArrayElementSetterNoBoundsCheck), listOf(self, index, value))
        retFallibleVoid()
    }
}

private val referenceArrayElementSetterPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_set_fallibleBoundsCheck",
    LlvmVoidType,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    val value by param(PointerToAnyEmergeValue)
    body {
        inlinePanicBoundsCheck(self, index)
        call(context.registerIntrinsic(referenceArrayElementSetterNoBoundsCheck), listOf(self, index, value))
        retVoid()
    }
}

private val referenceArrayFinalizer: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_finalize",
    LlvmVoidType,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    body {
        val indexStackSlot = alloca(EmergeWordType)
        store(context.word(0), indexStackSlot)
        val size = getelementptr(self)
            .member { base }
            .member { elementCount }
            .get()
            .dereference()

        loop(
            header = {
                val endReached = icmp(indexStackSlot.dereference(), LlvmIntPredicate.EQUAL, size)
                conditionalBranch(endReached, ifTrue = {
                    this@loop.breakLoop()
                })
                doIteration()
            },
            body = {
                val currentIndex = indexStackSlot.dereference()
                val element = getelementptr(self)
                    .member { elements }
                    .index(currentIndex)
                    .get()
                    .dereference()
                element.afterReferenceDropped(isNullable = true)

                val nextIndex = add(currentIndex, context.word(1))
                store(nextIndex, indexStackSlot)
                loopContinue()
            }
        )

        call(context.freeFunction, listOf(self))

        retVoid()
    }
}

internal val EmergeReferenceArrayType: EmergeArrayType<LlvmPointerType<out EmergeHeapAllocated>> by lazy {
    lateinit var arrayTypeHolder: EmergeArrayType<LlvmPointerType<out EmergeHeapAllocated>>
    val defaultValueCtor = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "emerge.platform.ref_array_defaultValueCtor",
        PointerToAnyEmergeValue,
    ) {
        val size by param(EmergeWordType)
        val defaultValue by param(PointerToAnyEmergeValue)

        body {
            val indexStack = alloca(EmergeWordType)
            store(context.word(0), indexStack)

            // efficient refcounting
            conditionalBranch(
                condition = isNotNull(defaultValue),
                ifTrue = {
                    val refcountLocation = defaultValue
                        .anyValueBase()
                        .member { strongReferenceCount }
                        .get()
                    store(add(refcountLocation.dereference(), size), refcountLocation)
                    concludeBranch()
                }
            )
            val arrayPtr = call(context.registerIntrinsic(arrayTypeHolder.constructorOfNullEntries), listOf(size))
            loop(
                header = {
                    conditionalBranch(
                        condition = icmp(indexStack.dereference(), LlvmIntPredicate.EQUAL, size),
                        ifTrue = { this@loop.breakLoop() },
                    )
                    doIteration()
                },
                body = {
                    val index = indexStack.dereference()
                    store(
                        defaultValue,
                        getelementptr(arrayPtr)
                            .member { elements }
                            .index(index)
                            .get()
                    )
                    store(add(index, context.word(1)), indexStack)
                    loopContinue()
                }
            )
            ret(arrayPtr.reinterpretAs(PointerToAnyEmergeValue))
        }
    }
    arrayTypeHolder = EmergeArrayType(
        "ref",
        elementType = PointerToAnyEmergeValue,
        virtualGetterWithFallibleBoundsCheck = referenceArrayElementGetterFallibleBoundsCheck,
        virtualGetterWithPanicBoundsCheck = referenceArrayElementGetterPanicBoundsCheck,
        virtualSetterWithFallibleBoundsCheck = referenceArrayElementSetterFallibleBoundsCheck,
        virtualSetterWithPanicBoundsCheck = referenceArrayElementSetterPanicBoundsCheck,
        rawGetterWithFallibleBoundsCheck = referenceArrayElementGetterFallibleBoundsCheck,
        rawGetterWithPanicBoundsCheck = referenceArrayElementGetterPanicBoundsCheck,
        rawGetterWithoutBoundsCheck = referenceArrayElementGetterNoBoundsCheck,
        rawSetterWithFallibleBoundsCheck = referenceArrayElementSetterFallibleBoundsCheck,
        rawSetterWithPanicBoundsCheck = referenceArrayElementSetterPanicBoundsCheck,
        rawSetterWithoutBoundsCheck = referenceArrayElementSetterNoBoundsCheck,
        finalizer = referenceArrayFinalizer,
        defaultValueConstructor = defaultValueCtor,
        emptyList(),
    )
    arrayTypeHolder
}

/* TODO: refactor to addressOf(index: uword)
   that would be easy to do for concrete types; but there should be an overload for Array<out Any>
   and with the currently planned rules for overloading, having an addressOf(self: Array<out Any>)
   would prevent declaring a specialized addressOf(self: Array<Byte>) etc.

   other possibility: arrays always as slices. Right now array references are a single ptr to the array
   object on the heap. Array references could become fat pointers consisting of
   1. a pointer to the array object on the heap, for reference counting
   2. the number of elements being referenced
   3. a pointer to the first element being referenced, null when <num of elements referenced> == 0
   Then, when you need the address of any other array element other than the first, you can create a slice
   of the array (e.g. someArray.subArray(2, someArray.length)) and then do addressOfFirst
 */
internal val arrayAddressOfFirst = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.ffi.c.addressOfFirst",
    pointerTo(LlvmVoidType),
) {
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    functionAttribute(LlvmFunctionAttribute.NoFree)

    val arrayPointer by param(pointerTo(EmergeArrayBaseType))

    body {
        val ptr = getelementptr(arrayPointer, context.i32(1))
            .get()
            .reinterpretAs(pointerTo(LlvmVoidType))

        ret(ptr)
    }
}

internal val arraySize = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.core.Array::size",
    EmergeWordType,
) {
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    val arrayPointer by param(pointerTo(EmergeArrayBaseType))
    body {
        ret(
            getelementptr(arrayPointer)
                .member { elementCount }
                .get()
                .dereference()
        )
    }
}

/**
 * this must never be invoked directly. Either one of these gets invoked directly or through the vtable
 * * [referenceArrayElementGetterFallibleBoundsCheck]
 * * [buildValueArrayBoxingElementGetterWithFallibleBoundsCheck]
 *
 * or the backend must emit specialized code for accessing the elements, just as in [buildValueArrayBoxingElementGetterWithFallibleBoundsCheck],
 * because that depends on the element size.
 */
internal val arrayAbstractFallibleGet = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Array::get",
    EmergeFallibleCallResult.ofEmergeReference,
) {
    param(pointerTo(EmergeArrayBaseType))
    param(EmergeWordType)
    body {
        inlinePanic("abstract array getter invoked")
    }
}

/** like [arrayAbstractFallibleGet], but with a different return type. */
internal val arrayAbstractPanicGet = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Array::getOrPanic",
    PointerToAnyEmergeValue,
) {
    param(pointerTo(EmergeArrayBaseType))
    param(EmergeWordType)
    body {
        inlinePanic("abstract array getter invoked")
    }
}

/**
 * this must never be invoked directly. Either one of these gets invoked directly or through the vtable
 * * [referenceArrayElementSetterFallibleBoundsCheck]
 * * [buildValueArrayBoxingElementSetterWithFallibleBoundsCheck]
 *
 * or the backend must emit specialized code for accessing the elements, just as in [buildValueArrayBoxingElementSetterWithFallibleBoundsCheck],
 * because that depends on the element size.
 */
internal val arrayAbstractFallibleSet = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Array::set",
    EmergeFallibleCallResult.OfVoid,
) {
    param(pointerTo(EmergeArrayBaseType))
    param(EmergeWordType)
    param(PointerToAnyEmergeValue)
    body {
        inlinePanic("abstract array setter invoked")
    }
}

/** like [arrayAbstractFallibleSet], but with a different return type. */
internal val arrayAbstractPanicSet = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Array::setOrPanic",
    LlvmVoidType,
) {
    param(pointerTo(EmergeArrayBaseType))
    param(EmergeWordType)
    param(PointerToAnyEmergeValue)
    body {
        inlinePanic("abstract array setter invoked")
    }
}

context(BasicBlockBuilder<*, *>)
internal fun indexIsOutOfBounds(arrayPtr: LlvmValue<LlvmPointerType<out EmergeArrayType<*>>>, index: LlvmValue<EmergeWordType>): LlvmValue<LlvmBooleanType> {
    val size = getelementptr(arrayPtr)
        .member { base }
        .member { elementCount }
        .get()
        .dereference()

    return icmp(index, LlvmIntPredicate.UNSIGNED_GREATER_THAN_OR_EQUAL, size)
}

context(BasicBlockBuilder<EmergeLlvmContext, out EmergeFallibleCallResult<*>>)
internal fun inlineFallibleBoundsCheck(
    arrayPtr: LlvmValue<LlvmPointerType<out EmergeArrayType<*>>>,
    index: LlvmValue<EmergeWordType>,
) {
    conditionalBranch(
        condition = indexIsOutOfBounds(arrayPtr, index),
        ifTrue = {
            inlineThrow(context.arrayIndexOutOfBoundsErrorType.irClass, listOf(index))
        }
    )
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun inlinePanicBoundsCheck(
    arrayPtr: LlvmValue<LlvmPointerType<out EmergeArrayType<*>>>,
    index: LlvmValue<EmergeWordType>,
) {
    conditionalBranch(
        condition = indexIsOutOfBounds(arrayPtr, index),
        ifTrue = {
           inlinePanic("Array index is out of bounds")
        }
    )
}

internal val EmergeS8ArrayType = buildValueArrayType("s8", LlvmI8Type, EmergeLlvmContext::boxTypeS8)
internal val EmergeU8ArrayType = buildValueArrayType("u8", LlvmI8Type, EmergeLlvmContext::boxTypeU8)
internal val EmergeS16ArrayType = buildValueArrayType("s16", LlvmI16Type, EmergeLlvmContext::boxTypeS16)
internal val EmergeU16ArrayType = buildValueArrayType("u16", LlvmI16Type, EmergeLlvmContext::boxTypeU16)
internal val EmergeS32ArrayType = buildValueArrayType("s32", LlvmI32Type, EmergeLlvmContext::boxTypeS32)
internal val EmergeU32ArrayType = buildValueArrayType("u32", LlvmI32Type, EmergeLlvmContext::boxTypeU32)
internal val EmergeS64ArrayType = buildValueArrayType("s64", LlvmI64Type, EmergeLlvmContext::boxTypeS64)
internal val EmergeU64ArrayType = buildValueArrayType("u64", LlvmI64Type, EmergeLlvmContext::boxTypeU64)
internal val EmergeSWordArrayType = buildValueArrayType("sword", EmergeWordType, EmergeLlvmContext::boxTypeSWord)
internal val EmergeUWordArrayType = buildValueArrayType("uword", EmergeWordType, EmergeLlvmContext::boxTypeUWord)
internal val EmergeBooleanArrayType = buildValueArrayType("bool", LlvmBooleanType, EmergeLlvmContext::boxTypeBool)