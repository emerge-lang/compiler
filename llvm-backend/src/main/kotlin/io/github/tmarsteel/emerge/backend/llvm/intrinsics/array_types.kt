package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.GET_AT_INDEX_FN_NAME
import io.github.tmarsteel.emerge.backend.SET_AT_INDEX_FN_NAME
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
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
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

/**
 * The reference-site representation of every `emerge.core.Array<...>`: a view of [length] elements of the
 * array object [base], starting at element [offset].
 */
internal object EmergeArraySliceType : LlvmNamedStructType("arrayslice") {
    val base by structMember(pointerTo(EmergeArrayBaseType))
    val offset by structMember(EmergeWordType)
    val length by structMember(EmergeWordType)
}

context(BasicBlockBuilder<*, *>)
internal val LlvmValue<EmergeArraySliceType>.sliceBase: LlvmValue<LlvmPointerType<EmergeArrayBaseType>>
    get() = extractValue(this) { base }

context(BasicBlockBuilder<*, *>)
internal val LlvmValue<EmergeArraySliceType>.sliceOffset: LlvmValue<EmergeWordType>
    get() = extractValue(this) { offset }

context(BasicBlockBuilder<*, *>)
internal val LlvmValue<EmergeArraySliceType>.sliceLength: LlvmValue<EmergeWordType>
    get() = extractValue(this) { length }

context(BasicBlockBuilder<*, *>)
internal fun buildArraySlice(
    base: LlvmValue<LlvmPointerType<*>>,
    offset: LlvmValue<EmergeWordType>,
    length: LlvmValue<EmergeWordType>,
): LlvmValue<EmergeArraySliceType> {
    var slice: LlvmValue<EmergeArraySliceType> = context.undefValue(EmergeArraySliceType)
    slice = insertValue(slice, base.reinterpretAs(pointerTo(EmergeArrayBaseType))) { this.base }
    slice = insertValue(slice, offset) { this.offset }
    slice = insertValue(slice, length) { this.length }
    return slice
}

/** @return a slice covering the entire array object [base] */
context(BasicBlockBuilder<*, *>)
internal fun buildArraySliceOfEntireArray(base: LlvmValue<LlvmPointerType<*>>): LlvmValue<EmergeArraySliceType> {
    val typedBase = base.reinterpretAs(pointerTo(EmergeArrayBaseType))
    val elementCount = getelementptr(typedBase)
        .member { elementCount }
        .get()
        .dereference()
    return buildArraySlice(typedBase, context.word(0), elementCount)
}

/**
 * @return a pointer to the element at [index] in the slice [slice], assuming its base is of type [arrayType].
 * Doesn't check bounds.
 */
context(BasicBlockBuilder<*, *>)
internal fun <Element : LlvmType> sliceElementPointer(
    arrayType: EmergeArrayType<Element>,
    slice: LlvmValue<EmergeArraySliceType>,
    index: LlvmValue<EmergeWordType>,
): LlvmValue<LlvmPointerType<Element>> {
    return getelementptr(slice.sliceBase.reinterpretAs(pointerTo(arrayType)))
        .member { elements }
        .index(add(slice.sliceOffset, index))
        .get()
}

/**
 * Builds a constant slice covering all of [baseArray], a constant array object.
 */
internal fun EmergeLlvmContext.buildConstantSliceOf(
    baseArray: LlvmValue<LlvmPointerType<*>>,
    elementCount: Long,
): LlvmConstant<EmergeArraySliceType> {
    return EmergeArraySliceType.buildConstantIn(this) {
        setValue(EmergeArraySliceType.base, baseArray.reinterpretAs(pointerTo(EmergeArrayBaseType)))
        setValue(EmergeArraySliceType.offset, word(0))
        setValue(EmergeArraySliceType.length, word(elementCount))
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
     * A function of the signature nothrow (self: Array<Element>, index: UWord) -> Any, to be placed in the vtable.
     * This is important for arrays of primitives, as this function will do the automatic boxing (e.g. S8 -> S8Box)
     */
    private val virtualGetterWithPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>>,

    /**
     * A function of the signature (self: Array<Element>, index: UWord, value: Any) -> Unit, to be placed in the vtable.
     * This is important for arrays of primitives, as this function will do the automatic unboxing (e.g. S8Box -> S8)
     */
    private val virtualSetterWithFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid>,

    /**
     * A function of the signature nothrow (self: Array<Element>, index: UWord, value: Any) -> Unit, to be placed in the vtable.
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
    val defaultValueConstructor: KotlinLlvmFunction<EmergeLlvmContext, EmergeArraySliceType>,
) : LlvmNamedStructType("array_$elementTypeName"), EmergeHeapAllocated {
    val base by structMember(EmergeArrayBaseType)
    val elements by structMember(LlvmArrayType(0L, elementType))

    /**
     * A function of the signature nothrow (self: Array<Element>) -> COpaquePointer, to be placed in the vtable.
     * Returns the address of the first element of the slice.
     */
    private val virtualAddressOfFirst: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<LlvmVoidType>> by lazy {
        KotlinLlvmFunction.define(
            "emerge.platform.array_${elementTypeName}_addressOfFirst",
            pointerTo(LlvmVoidType),
        ) {
            val self by param(EmergeArraySliceType)
            body {
                ret(sliceElementPointer(this@EmergeArrayType, self, context.word(0)).reinterpretAs(pointerTo(LlvmVoidType)))
            }
        }
    }

    /**
     * Array objects are never visible to emerge code as values of type `Any`; [EmergeArraySliceType]s are boxed
     * into `emerge.platform.ArrayBox` for that. Hence, this typeinfo only serves for the vtable and the finalizer.
     */
    val typeinfo = StaticAndDynamicTypeInfo.defineRaw(
        { _ -> name },
        emptyList(),
        { ctx -> ctx.registerIntrinsic(finalizer) },
        { mapOf(
            VIRTUAL_FUNCTION_HASH_GET_ELEMENT_FALLIBLE to registerIntrinsic(virtualGetterWithFallibleBoundsCheck),
            VIRTUAL_FUNCTION_HASH_GET_ELEMENT_PANIC    to registerIntrinsic(virtualGetterWithPanicBoundsCheck),
            VIRTUAL_FUNCTION_HASH_SET_ELEMENT_FALLIBLE to registerIntrinsic(virtualSetterWithFallibleBoundsCheck),
            VIRTUAL_FUNCTION_HASH_SET_ELEMENT_PANIC    to registerIntrinsic(virtualSetterWithPanicBoundsCheck),
            VIRTUAL_FUNCTION_HASH_ADDRESS_OF_FIRST     to registerIntrinsic(virtualAddressOfFirst),
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
        val VIRTUAL_FUNCTION_HASH_ADDRESS_OF_FIRST: ULong     = 0b0010_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000uL
    }
}

internal val valueArrayDestructor = KotlinLlvmFunction.define<EmergeLlvmContext, _>("emerge.platform.destructValueArray", LlvmVoidType) {
    val self by param(PointerToAnyEmergeValue)
    body {
        // nothing to do for the array elements; there are no references, just values, so no dropping needed
        call(context.freeFunction, listOf(self))
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
        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)
        body {
            inlineFallibleBoundsCheck(self, index)

            val raw = sliceElementPointer(getValueArrayType(), self, index).dereference()

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
        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)
        body {
            inlinePanicBoundsCheck(self, index)

            val raw = sliceElementPointer(getValueArrayType(), self, index).dereference()

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
        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)
        val valueBoxAny by param(PointerToAnyEmergeValue)
        body {
            val arrayType = getValueArrayType()
            val boxType = getBoxType(context)
            val valueMember = boxType.irClass.fields.single()
            check(context.getReferenceSiteType(valueMember.type) == arrayType.elementType)

            val valueBox = valueBoxAny.reinterpretAs(pointerTo(boxType))

            inlineFallibleBoundsCheck(self, index)
            val raw = getelementptr(valueBox)
                .member(boxType.irClass.fields.single())
                .get()
                .dereference()
                .reinterpretAs(arrayType.elementType)

            store(raw, sliceElementPointer(arrayType, self, index))
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
        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)
        val valueBoxAny by param(PointerToAnyEmergeValue)
        body {
            val arrayType = getValueArrayType()
            val boxType = getBoxType(context)
            val valueMember = boxType.irClass.fields.single()
            check(context.getReferenceSiteType(valueMember.type) == arrayType.elementType)

            val valueBox = valueBoxAny.reinterpretAs(pointerTo(boxType))

            inlinePanicBoundsCheck(self, index)
            val raw = getelementptr(valueBox)
                .member(boxType.irClass.fields.single())
                .get()
                .dereference()
                .reinterpretAs(arrayType.elementType)

            store(raw, sliceElementPointer(arrayType, self, index))
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

        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)

        body {
            ret(sliceElementPointer(getSelfType(), self, index).dereference())
        }
    }
}

private fun <Element : LlvmType> buildRawGetterWithFallibleBoundsCheck(
    name: String,
    elementType: Element,
    rawGetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<Element>> {
    return KotlinLlvmFunction.define<_, _>(
        name,
        EmergeFallibleCallResult.WithValue(elementType),
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)

        body {
            inlineFallibleBoundsCheck(self, index)
            val raw = call(context.registerIntrinsic(rawGetterNoBoundsCheck), listOf(self, index))
            ret(fallibleSuccess(raw))
        }
    }
}

private fun <Element : LlvmType> buildRawGetterWithPanicBoundsCheck(
    name: String,
    elementType: Element,
    rawGetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, Element> {
    return KotlinLlvmFunction.define<_, _>(
        name,
        elementType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)

        body {
            inlinePanicBoundsCheck(self, index)
            val raw = call(context.registerIntrinsic(rawGetterNoBoundsCheck), listOf(self, index))
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

        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)
        val value by param(elementType)

        body {
            store(value, sliceElementPointer(getSelfType(), self, index))
            retVoid()
        }
    }
}

private fun <Element : LlvmType> buildRawSetterWithFallibleBoundsCheck(
    name: String,
    elementType: Element,
    rawSetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,
) : KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid> {
    return KotlinLlvmFunction.define<_, _>(
        name,
        EmergeFallibleCallResult.OfVoid,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)
        val value by param(elementType)

        body {
            inlineFallibleBoundsCheck(self, index)
            call(context.registerIntrinsic(rawSetterWithoutBoundsCheck), listOf(self, index, value))
            retFallibleVoid()
        }
    }
}

private fun <Element : LlvmType> buildRawSetterWithPanicBoundsCheck(
    name: String,
    elementType: Element,
    rawSetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,
) : KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    return KotlinLlvmFunction.define<_, _>(
        name,
        LlvmVoidType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val self by param(EmergeArraySliceType)
        val index by param(EmergeWordType)
        val value by param(elementType)

        body {
            inlinePanicBoundsCheck(self, index)
            call(context.registerIntrinsic(rawSetterWithoutBoundsCheck), listOf(self, index, value))
            retVoid()
        }
    }
}

private fun <Element : LlvmType> buildValueArrayDefaultValueConstructor(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, EmergeArraySliceType> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_defaultValueCtor",
        EmergeArraySliceType,
    ) {
        val size by param(EmergeWordType)
        val defaultValue by param(elementType)

        body {
            val arrayPtr = call(context.registerIntrinsic(getSelfType().constructorOfNullEntries), listOf(size))
            val indexStack = alloca(EmergeWordType)
            store(context.word(0), indexStack)
            loop {
                val index = indexStack.dereference()

                conditionalBranch(
                    condition = icmp(index, LlvmIntPredicate.EQUAL, size),
                    ifTrue = { this@loop.breakLoop() }
                )

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
            ret(buildArraySlice(arrayPtr, context.word(0), size))
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
    val rawGetterWithFallibleBoundsCheck = buildRawGetterWithFallibleBoundsCheck("emerge.core.array_${elementTypeName}_rawGetWithFallibleBoundsCheck", elementType, rawGetterWithoutBoundsCheck)
    val rawGetterWithPanicBoundsCheck = buildRawGetterWithPanicBoundsCheck("emerge.core.array_${elementTypeName}_rawGetWithPanicBoundsCheck", elementType, rawGetterWithoutBoundsCheck)
    val rawSetterWithoutBoundsCheck = buildValueArrayRawSetterWithoutBoundsCheck(elementTypeName, elementType, { arrayTypeHolder })
    val rawSetterWithFallibleBoundsCheck = buildRawSetterWithFallibleBoundsCheck("emerge.core.array_${elementTypeName}_rawSetWithFallibleBoundsCheck", elementType, rawSetterWithoutBoundsCheck)
    val rawSetterWithPanicBoundsCheck = buildRawSetterWithPanicBoundsCheck("emerge.core.array_${elementTypeName}_rawSetWithPanicBoundsCheck", elementType, rawSetterWithoutBoundsCheck)
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
        valueArrayDestructor,
        defaultValueCtor,
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
        val source by param(EmergeArraySliceType)
        val sourceOffset by param(EmergeWordType)
        val dest by param(EmergeArraySliceType)
        val destOffset by param(EmergeWordType)
        val length by param(EmergeWordType)

        body {
            conditionalBranch(
                condition = isZero(length),
                ifTrue = {
                    retVoid()
                }
            )

            val sourceMinSizeResult = call(UnsignedWordAddWithOverflow, listOf(sourceOffset, length))
            conditionalBranch(
                condition = or(
                    extractValue(sourceMinSizeResult) { hadOverflow },
                    icmp(extractValue(sourceMinSizeResult) { result }, LlvmIntPredicate.UNSIGNED_GREATER_THAN, source.sliceLength),
                ),
                ifTrue = {
                    inlinePanic("length overflows bounds of source")
                }
            )

            val destMinSizeResult = call(UnsignedWordAddWithOverflow, listOf(destOffset, length))
            conditionalBranch(
                condition = or(
                    extractValue(destMinSizeResult) { hadOverflow },
                    icmp(extractValue(destMinSizeResult) { result }, LlvmIntPredicate.UNSIGNED_GREATER_THAN, dest.sliceLength),
                ),
                ifTrue = {
                    inlinePanic("length overflows bounds of dest")
                }
            )

            // memmove semantics are needed because source and dest can be overlapping slices of the same array
            memmove(
                destination = sliceElementPointer(getSelfType(), dest, destOffset),
                source = sliceElementPointer(getSelfType(), source, sourceOffset),
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
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)

    instructionAliasAttributes()

    body {
        val referenceEntry = sliceElementPointer(EmergeReferenceArrayType, self, index).dereference()
        referenceEntry.afterReferenceCreated(isNullable = true)
        ret(referenceEntry)
    }
}

private val referenceArrayElementGetterFallibleBoundsCheck = buildRawGetterWithFallibleBoundsCheck(
    "emerge.platform.referenceArray_get_fallibleBoundsCheck",
    PointerToAnyEmergeValue,
    referenceArrayElementGetterNoBoundsCheck,
)

private val referenceArrayElementGetterPanicBoundsCheck = buildRawGetterWithPanicBoundsCheck(
    "emerge.platform.referenceArray_get_panicBoundsCheck",
    PointerToAnyEmergeValue,
    referenceArrayElementGetterNoBoundsCheck,
)

private val referenceArrayElementSetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArray_set_noBoundsCheck",
    LlvmVoidType,
) {
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)
    val value by param(PointerToAnyEmergeValue)
    body {
        val pointerToSlotInArray = sliceElementPointer(EmergeReferenceArrayType, self, index)
        val previousValue = pointerToSlotInArray.dereference()
        previousValue.afterReferenceDropped(isNullable = true)

        store(value, pointerToSlotInArray)
        value.afterReferenceCreated(isNullable = true)
        retVoid()
    }
}

private val referenceArrayElementSetterFallibleBoundsCheck = buildRawSetterWithFallibleBoundsCheck(
    "emerge.platform.referenceArray_set_fallibleBoundsCheck",
    PointerToAnyEmergeValue,
    referenceArrayElementSetterNoBoundsCheck,
)

private val referenceArrayElementSetterPanicBoundsCheck = buildRawSetterWithPanicBoundsCheck(
    "emerge.platform.referenceArray_set_panicBoundsCheck",
    PointerToAnyEmergeValue,
    referenceArrayElementSetterNoBoundsCheck,
)

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

        loop {
            val currentIndex = indexStackSlot.dereference()
            conditionalBranch(icmp(currentIndex, LlvmIntPredicate.EQUAL, size), ifTrue = {
                this@loop.breakLoop()
            })

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

        call(context.freeFunction, listOf(self))
        retVoid()
    }
}

internal val EmergeReferenceArrayType: EmergeArrayType<LlvmPointerType<out EmergeHeapAllocated>> by lazy {
    lateinit var arrayTypeHolder: EmergeArrayType<LlvmPointerType<out EmergeHeapAllocated>>
    val defaultValueCtor = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "emerge.platform.ref_array_defaultValueCtor",
        EmergeArraySliceType,
    ) {
        val size by param(EmergeWordType)
        val defaultValue by param(PointerToAnyEmergeValue)

        body {
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
            val indexStack = alloca(EmergeWordType, forceEntryBlock = true)
            store(context.word(0), indexStack)
            loop {
                val index = indexStack.dereference()
                conditionalBranch(
                    condition = icmp(index, LlvmIntPredicate.EQUAL, size),
                    ifTrue = { this@loop.breakLoop() },
                )

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

            ret(buildArraySlice(arrayPtr, context.word(0), size))
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
    )
    arrayTypeHolder
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun LlvmValue<EmergeArraySliceType>.afterSliceReferenceCreated() {
    sliceBase.afterReferenceCreated(isNullable = true)
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun LlvmValue<EmergeArraySliceType>.afterSliceReferenceDropped() {
    sliceBase.afterReferenceDropped(isNullable = true)
}

private val sliceArrayElementGetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeArraySliceType> = KotlinLlvmFunction.define(
    "emerge.platform.sliceArray_get_noBoundsCheck",
    EmergeArraySliceType,
) {
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)

    body {
        val element = sliceElementPointer(EmergeSliceArrayType, self, index).dereference()
        element.afterSliceReferenceCreated()
        ret(element)
    }
}

private val sliceArrayElementSetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.sliceArray_set_noBoundsCheck",
    LlvmVoidType,
) {
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)
    val value by param(EmergeArraySliceType)
    body {
        val pointerToSlotInArray = sliceElementPointer(EmergeSliceArrayType, self, index)
        // the slot may still be zero-initialized, hence the nullable base
        pointerToSlotInArray.dereference().afterSliceReferenceDropped()

        store(value, pointerToSlotInArray)
        value.afterSliceReferenceCreated()
        retVoid()
    }
}

private val sliceArrayBoxingElementGetterWithFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<LlvmPointerType<out EmergeHeapAllocated>>> = KotlinLlvmFunction.define(
    "emerge.platform.sliceArray_getBoxed_fallibleBoundsCheck",
    EmergeFallibleCallResult.ofEmergeReference,
) {
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)
    body {
        inlineFallibleBoundsCheck(self, index)
        val element = sliceElementPointer(EmergeSliceArrayType, self, index).dereference()
        ret(
            call(context.boxTypeArray.constructor, listOf(element))
                .reinterpretAs(EmergeFallibleCallResult.ofEmergeReference)
        )
    }
}

private val sliceArrayBoxingElementGetterWithPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<out EmergeHeapAllocated>> = KotlinLlvmFunction.define(
    "emerge.platform.sliceArray_getBoxed_panicBoundsCheck",
    PointerToAnyEmergeValue,
) {
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)
    body {
        inlinePanicBoundsCheck(self, index)
        val element = sliceElementPointer(EmergeSliceArrayType, self, index).dereference()
        val box = call(context.boxTypeArray.constructor, listOf(element)).abortOnException { _ ->
            inlinePanic("failed to allocate box - OOM")
        }
        ret(box.reinterpretAs(PointerToAnyEmergeValue))
    }
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun unboxArrayBox(box: LlvmValue<*>): LlvmValue<EmergeArraySliceType> {
    val boxType = context.boxTypeArray
    @Suppress("UNCHECKED_CAST")
    return getelementptr(box.reinterpretAs(pointerTo(boxType)))
        .member(boxType.irClass.fields.single())
        .get()
        .dereference() as LlvmValue<EmergeArraySliceType>
}

private val sliceArrayBoxingElementSetterWithFallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid> = KotlinLlvmFunction.define(
    "emerge.platform.sliceArray_setBoxed_fallibleBoundsCheck",
    EmergeFallibleCallResult.OfVoid,
) {
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)
    val valueBox by param(PointerToAnyEmergeValue)
    body {
        inlineFallibleBoundsCheck(self, index)
        call(context.registerIntrinsic(sliceArrayElementSetterNoBoundsCheck), listOf(self, index, unboxArrayBox(valueBox)))
        retFallibleVoid()
    }
}

private val sliceArrayBoxingElementSetterWithPanicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.sliceArray_setBoxed_panicBoundsCheck",
    LlvmVoidType,
) {
    val self by param(EmergeArraySliceType)
    val index by param(EmergeWordType)
    val valueBox by param(PointerToAnyEmergeValue)
    body {
        inlinePanicBoundsCheck(self, index)
        call(context.registerIntrinsic(sliceArrayElementSetterNoBoundsCheck), listOf(self, index, unboxArrayBox(valueBox)))
        retVoid()
    }
}

private val sliceArrayFinalizer: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.sliceArray_finalize",
    LlvmVoidType,
) {
    val self by param(pointerTo(EmergeSliceArrayType))
    body {
        val indexStackSlot = alloca(EmergeWordType)
        store(context.word(0), indexStackSlot)
        val size = getelementptr(self)
            .member { base }
            .member { elementCount }
            .get()
            .dereference()

        loop {
            val currentIndex = indexStackSlot.dereference()
            conditionalBranch(icmp(currentIndex, LlvmIntPredicate.EQUAL, size), ifTrue = {
                this@loop.breakLoop()
            })

            getelementptr(self)
                .member { elements }
                .index(currentIndex)
                .get()
                .dereference()
                .afterSliceReferenceDropped()

            store(add(currentIndex, context.word(1)), indexStackSlot)
            loopContinue()
        }

        call(context.freeFunction, listOf(self))
        retVoid()
    }
}

/**
 * The array objects for arrays whose elements are arrays themselves: the elements are [EmergeArraySliceType]s.
 */
internal val EmergeSliceArrayType: EmergeArrayType<EmergeArraySliceType> by lazy {
    lateinit var arrayTypeHolder: EmergeArrayType<EmergeArraySliceType>
    val defaultValueCtor = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "emerge.platform.slice_array_defaultValueCtor",
        EmergeArraySliceType,
    ) {
        val size by param(EmergeWordType)
        val defaultValue by param(EmergeArraySliceType)

        body {
            val arrayPtr = call(context.registerIntrinsic(arrayTypeHolder.constructorOfNullEntries), listOf(size))
            val indexStack = alloca(EmergeWordType, forceEntryBlock = true)
            store(context.word(0), indexStack)
            loop {
                val index = indexStack.dereference()
                conditionalBranch(
                    condition = icmp(index, LlvmIntPredicate.EQUAL, size),
                    ifTrue = { this@loop.breakLoop() },
                )

                store(
                    defaultValue,
                    getelementptr(arrayPtr)
                        .member { elements }
                        .index(index)
                        .get()
                )
                defaultValue.afterSliceReferenceCreated()
                store(add(index, context.word(1)), indexStack)
                loopContinue()
            }

            ret(buildArraySlice(arrayPtr, context.word(0), size))
        }
    }
    val getterFallible = buildRawGetterWithFallibleBoundsCheck(
        "emerge.platform.sliceArray_get_fallibleBoundsCheck",
        EmergeArraySliceType,
        sliceArrayElementGetterNoBoundsCheck,
    )
    val getterPanic = buildRawGetterWithPanicBoundsCheck(
        "emerge.platform.sliceArray_get_panicBoundsCheck",
        EmergeArraySliceType,
        sliceArrayElementGetterNoBoundsCheck,
    )
    val setterFallible = buildRawSetterWithFallibleBoundsCheck(
        "emerge.platform.sliceArray_set_fallibleBoundsCheck",
        EmergeArraySliceType,
        sliceArrayElementSetterNoBoundsCheck,
    )
    val setterPanic = buildRawSetterWithPanicBoundsCheck(
        "emerge.platform.sliceArray_set_panicBoundsCheck",
        EmergeArraySliceType,
        sliceArrayElementSetterNoBoundsCheck,
    )
    arrayTypeHolder = EmergeArrayType(
        "slice",
        elementType = EmergeArraySliceType,
        virtualGetterWithFallibleBoundsCheck = sliceArrayBoxingElementGetterWithFallibleBoundsCheck,
        virtualGetterWithPanicBoundsCheck = sliceArrayBoxingElementGetterWithPanicBoundsCheck,
        virtualSetterWithFallibleBoundsCheck = sliceArrayBoxingElementSetterWithFallibleBoundsCheck,
        virtualSetterWithPanicBoundsCheck = sliceArrayBoxingElementSetterWithPanicBoundsCheck,
        rawGetterWithFallibleBoundsCheck = getterFallible,
        rawGetterWithPanicBoundsCheck = getterPanic,
        rawGetterWithoutBoundsCheck = sliceArrayElementGetterNoBoundsCheck,
        rawSetterWithFallibleBoundsCheck = setterFallible,
        rawSetterWithPanicBoundsCheck = setterPanic,
        rawSetterWithoutBoundsCheck = sliceArrayElementSetterNoBoundsCheck,
        finalizer = sliceArrayFinalizer,
        defaultValueConstructor = defaultValueCtor,
    )
    arrayTypeHolder
}

/**
 * implementation of `emerge.ffi.c.addressOfFirst`; works for slices of all element types by dispatching
 * on the base array object.
 */
internal val arrayAddressOfFirst = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.ffi.c.addressOfFirst",
    pointerTo(LlvmVoidType),
) {
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    functionAttribute(LlvmFunctionAttribute.NoFree)

    val self by param(EmergeArraySliceType)

    body {
        val addressOfFirstFn = call(context.registerIntrinsic(getDynamicCallAddress), listOf(
            self.sliceBase,
            context.word(EmergeArrayType.VIRTUAL_FUNCTION_HASH_ADDRESS_OF_FIRST),
        ))
        ret(call(addressOfFirstFn, LlvmFunctionType(pointerTo(LlvmVoidType), listOf(EmergeArraySliceType)), listOf(self)))
    }
}

internal val arraySize = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.core.Array::size",
    EmergeWordType,
) {
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    val self by param(EmergeArraySliceType)
    body {
        ret(self.sliceLength)
    }
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun slicedIsOutOfBounds(
    self: LlvmValue<EmergeArraySliceType>,
    fromIndex: LlvmValue<EmergeWordType>,
    toIndexExclusive: LlvmValue<EmergeWordType>,
): LlvmValue<LlvmBooleanType> = or(
    icmp(fromIndex, LlvmIntPredicate.UNSIGNED_GREATER_THAN, toIndexExclusive),
    icmp(toIndexExclusive, LlvmIntPredicate.UNSIGNED_GREATER_THAN, self.sliceLength),
)

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun buildSubSlice(
    self: LlvmValue<EmergeArraySliceType>,
    fromIndex: LlvmValue<EmergeWordType>,
    toIndexExclusive: LlvmValue<EmergeWordType>,
): LlvmValue<EmergeArraySliceType> {
    val subSlice = buildArraySlice(
        self.sliceBase,
        add(self.sliceOffset, fromIndex),
        sub(toIndexExclusive, fromIndex),
    )
    // the result is a new reference to the base
    subSlice.afterSliceReferenceCreated()
    return subSlice
}

/** implementation of `emerge.core.Array::slice` */
internal val arraySlice = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Array::slice",
    EmergeFallibleCallResult.WithValue(EmergeArraySliceType),
) {
    val self by param(EmergeArraySliceType)
    val fromIndex by param(EmergeWordType)
    val toIndexExclusive by param(EmergeWordType)

    body {
        conditionalBranch(
            condition = slicedIsOutOfBounds(self, fromIndex, toIndexExclusive),
            ifTrue = {
                val invalidIndex = select(
                    icmp(toIndexExclusive, LlvmIntPredicate.UNSIGNED_GREATER_THAN, self.sliceLength),
                    toIndexExclusive,
                    fromIndex,
                )
                inlineThrow(context.arrayIndexOutOfBoundsErrorType.irClass, listOf(invalidIndex))
            }
        )
        ret(fallibleSuccess(buildSubSlice(self, fromIndex, toIndexExclusive)))
    }
}

/** implementation of `emerge.core.Array::sliceOrPanic` */
internal val arraySliceOrPanic = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Array::sliceOrPanic",
    EmergeArraySliceType,
) {
    val self by param(EmergeArraySliceType)
    val fromIndex by param(EmergeWordType)
    val toIndexExclusive by param(EmergeWordType)

    body {
        conditionalBranch(
            condition = slicedIsOutOfBounds(self, fromIndex, toIndexExclusive),
            ifTrue = {
                inlinePanic("Array slice bounds are out of range")
            }
        )
        ret(buildSubSlice(self, fromIndex, toIndexExclusive))
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
    "emerge.core.Array::${GET_AT_INDEX_FN_NAME}",
    EmergeFallibleCallResult.ofEmergeReference,
) {
    param(EmergeArraySliceType)
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
    param(EmergeArraySliceType)
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
    "emerge.core.Array::${SET_AT_INDEX_FN_NAME}",
    EmergeFallibleCallResult.OfVoid,
) {
    param(EmergeArraySliceType)
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
    param(EmergeArraySliceType)
    param(EmergeWordType)
    param(PointerToAnyEmergeValue)
    body {
        inlinePanic("abstract array setter invoked")
    }
}

context(BasicBlockBuilder<*, *>)
internal fun indexIsOutOfBounds(slice: LlvmValue<EmergeArraySliceType>, index: LlvmValue<EmergeWordType>): LlvmValue<LlvmBooleanType> {
    return icmp(index, LlvmIntPredicate.UNSIGNED_GREATER_THAN_OR_EQUAL, slice.sliceLength)
}

context(BasicBlockBuilder<EmergeLlvmContext, out EmergeFallibleCallResult<*>>)
internal fun inlineFallibleBoundsCheck(
    slice: LlvmValue<EmergeArraySliceType>,
    index: LlvmValue<EmergeWordType>,
) {
    conditionalBranch(
        condition = indexIsOutOfBounds(slice, index),
        ifTrue = {
            inlineThrow(context.arrayIndexOutOfBoundsErrorType.irClass, listOf(index))
        }
    )
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun inlinePanicBoundsCheck(
    slice: LlvmValue<EmergeArraySliceType>,
    index: LlvmValue<EmergeWordType>,
) {
    conditionalBranch(
        condition = indexIsOutOfBounds(slice, index),
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
