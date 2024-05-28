package io.github.tmarsteel.emerge.backend.llvm.intrinsics

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
    private val virtualGetter: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeHeapAllocatedValueBaseType>>,

    /**
     * A function of the signature (self: Array<Element>, index: UWord, value: Any) -> Unit, to be placed in the vtable.
     * This is important for arrays of primitives, as this function will do the automatic unboxing (e.g. S8Box -> S8)
     */
    private val virtualSetter: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * like [virtualGetter], but doesn't do any boxing; assumes the caller knows the binary types.
     */
    private val rawGetterWithBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,

    /**
     * like [rawGetterWithBoundsCheck], but doesn't check the bounds.
     */
    private val rawGetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,

    /**
     * like [virtualSetter], but doesn't do any unboxing; assumes the caller knows the binary types.
     */
    private val rawSetterWithBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * like [rawSetterWithBoundsCheck], but doesn't check the bounds
     */
    private val rawSetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * the finalizer for this array type
     */
    private val finalizer: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,

    /**
     * A function of the signature (size: UWord, defaultValue: Element) -> Array<Element> that creates a new array
     * of the given size and sets all the elements to the given value.
     */
    val defaultValueConstructor: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeHeapAllocatedValueBaseType>>,
) : LlvmNamedStructType("array_$elementTypeName"), EmergeHeapAllocated {
    val base by structMember(EmergeArrayBaseType)
    val elements by structMember(LlvmArrayType(0L, elementType))

    val typeinfo = StaticAndDynamicTypeInfo.define(
        name,
        emptyList(),
        { ctx -> ctx.registerIntrinsic(finalizer) },
        { mapOf(
            VIRTUAL_FUNCTION_HASH_GET_ELEMENT to registerIntrinsic(virtualGetter),
            VIRTUAL_FUNCTION_HASH_SET_ELEMENT to registerIntrinsic(virtualSetter),
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

    fun getRawGetter(trustsIndexInBounds: Boolean): KotlinLlvmFunction<EmergeLlvmContext, Element> {
        return if (trustsIndexInBounds) rawGetterWithoutBoundsCheck else rawGetterWithBoundsCheck
    }

    fun getRawSetter(trustsIndexInBounds: Boolean): KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
        return if (trustsIndexInBounds) rawSetterWithoutBoundsCheck else rawSetterWithBoundsCheck
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
        val VIRTUAL_FUNCTION_HASH_GET_ELEMENT: ULong = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000uL
        val VIRTUAL_FUNCTION_HASH_SET_ELEMENT: ULong = 0b0100_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000uL
    }
}

internal val valueArrayFinalize = KotlinLlvmFunction.define<EmergeLlvmContext, _>("emerge.platform.finalizeValueArray", LlvmVoidType) {
    param(PointerToAnyEmergeValue)
    body {
        // nothing to do. There are no references, just values, so no dropping needed
        retVoid()
    }
}

private fun <Element : LlvmType> buildValueArrayBoxingElementGetter(
    typeName: String,
    getValueArrayType: () -> EmergeArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
): KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeHeapAllocatedValueBaseType>> {
    return KotlinLlvmFunction.define(
        "emerge.platform.valueArrayGetBoxed_${typeName}",
        PointerToAnyEmergeValue,
    ) {
        val self by param(pointerTo(getValueArrayType()))
        val index by param(EmergeWordType)
        body {
            inlineBoundsCheck(self, index)

            val raw = getelementptr(self)
                .member { elements }
                .index(index)
                .get()
                .dereference()

            ret(call(getBoxType(context).constructor, listOf(raw)).reinterpretAs(PointerToAnyEmergeValue))
        }
    }
}

private fun <Element : LlvmType> buildValueArrayBoxingElementSetter(
    typeName: String,
    getValueArrayType: () -> EmergeArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
): KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    return KotlinLlvmFunction.define(
        "emerge.platform.valueArraySetBoxed_${typeName}",
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

            inlineBoundsCheck(self, index)
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
        "emerge.core.array_${elementTypeName}_rawGetNoBoundsCheck",
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

private fun <Element : LlvmType> buildValueArrayRawGetterWithBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
    rawGetterNoBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, Element> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawGetWithBoundsCheck",
        elementType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)

        body {
            inlineBoundsCheck(arrayPtr, index)
            ret(call(context.registerIntrinsic(rawGetterNoBoundsCheck), listOf(arrayPtr, index)))
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

private fun <Element : LlvmType> buildValueArrayRawSetterWithBoundsCheck(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
    rawSetterWithoutBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,
) : KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_rawSetWithBoundsCheck",
        LlvmVoidType,
    ) {
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.NoFree)

        val arrayPtr by param(pointerTo(getSelfType()))
        val index by param(EmergeWordType)
        val value by param(elementType)

        body {
            inlineBoundsCheck(arrayPtr, index)
            call(context.registerIntrinsic(rawSetterWithoutBoundsCheck), listOf(arrayPtr, index, value))
            retVoid()
        }
    }
}

private fun <Element : LlvmType> buildValueArrayDefaultValueConstructor(
    elementTypeName: String,
    elementType: Element,
    getSelfType: () -> EmergeArrayType<Element>,
) : KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeHeapAllocatedValueBaseType>> {
    return KotlinLlvmFunction.define<_, _>(
        "emerge.core.array_${elementTypeName}_nullCtor",
        PointerToAnyEmergeValue,
    ) {
        val size by param(EmergeWordType)
        val defaultValue by param(elementType)

        body {
            val rawSetter = context.registerIntrinsic(getSelfType().getRawSetter(true))
            val arrayPtr = call(context.registerIntrinsic(getSelfType().constructorOfNullEntries), listOf(size))
            val indexStack = alloca(EmergeWordType)
            store(context.word(0), indexStack)
            loop(
                header = {
                    conditionalBranch(
                        condition = icmp(indexStack.dereference(), LlvmIntPredicate.EQUAL, size),
                        ifTrue = { breakLoop() }
                    )
                    doIteration()
                },
                body = {
                    val index = indexStack.dereference()
                    call(rawSetter, listOf(arrayPtr, index, defaultValue))
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
    val virtualGetter = buildValueArrayBoxingElementGetter(elementTypeName, { arrayTypeHolder }, getBoxType)
    val virtualSetter = buildValueArrayBoxingElementSetter(elementTypeName, { arrayTypeHolder }, getBoxType)
    val rawGetterWithoutBoundsCheck = buildValueArrayRawGetterWithoutBoundsCheck(elementTypeName, elementType, { arrayTypeHolder })
    val rawGetterWithBoundsCheck = buildValueArrayRawGetterWithBoundsCheck(elementTypeName, elementType, { arrayTypeHolder }, rawGetterWithoutBoundsCheck)
    val rawSetterWithoutBoundsCheck = buildValueArrayRawSetterWithoutBoundsCheck(elementTypeName, elementType, { arrayTypeHolder })
    val rawSetterWithBoundsCheck = buildValueArrayRawSetterWithBoundsCheck(elementTypeName, elementType, { arrayTypeHolder }, rawSetterWithoutBoundsCheck)
    val defaultValueCtor = buildValueArrayDefaultValueConstructor(elementTypeName, elementType, { arrayTypeHolder })
    arrayTypeHolder = EmergeArrayType(
        elementTypeName,
        elementType,
        virtualGetter,
        virtualSetter,
        rawGetterWithBoundsCheck,
        rawGetterWithoutBoundsCheck,
        rawSetterWithBoundsCheck,
        rawSetterWithoutBoundsCheck,
        valueArrayFinalize,
        defaultValueCtor,
    )

    return arrayTypeHolder
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

private val referenceArrayElementGetter: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeHeapAllocatedValueBaseType>> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArrayGet",
    PointerToAnyEmergeValue,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    body {
        inlineBoundsCheck(self, index)
        val referenceEntry = getelementptr(self)
            .member { elements }
            .index(index)
            .get()
            .dereference()

        referenceEntry.afterReferenceCreated(isNullable = true)
        ret(referenceEntry)
    }
}

private val referenceArrayElementSetter: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArraySet",
    LlvmVoidType,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    val value by param(PointerToAnyEmergeValue)
    body {
        inlineBoundsCheck(self, index)
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

private val referenceArrayFinalizer: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArrayFinalize",
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
                    breakLoop()
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

internal val EmergeReferenceArrayType: EmergeArrayType<LlvmPointerType<EmergeHeapAllocatedValueBaseType>> by lazy {
    lateinit var arrayTypeHolder: EmergeArrayType<LlvmPointerType<EmergeHeapAllocatedValueBaseType>>
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
                    val refcountLocation = getelementptr(defaultValue)
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
                        ifTrue = { breakLoop() },
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
        virtualGetter = referenceArrayElementGetter,
        virtualSetter = referenceArrayElementSetter,
        rawGetterWithBoundsCheck = referenceArrayElementGetter,
        rawGetterWithoutBoundsCheck = referenceArrayElementGetter,
        rawSetterWithBoundsCheck = referenceArrayElementSetter,
        rawSetterWithoutBoundsCheck = referenceArrayElementSetter,
        finalizer = referenceArrayFinalizer,
        defaultValueConstructor = defaultValueCtor,
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
 * * [referenceArrayElementGetter]
 * * [buildValueArrayBoxingElementGetter]
 *
 * or the backend must emit specialized code for accessing the elements, just as in [buildValueArrayBoxingElementGetter],
 * because that depends on the element size.
 */
internal val arrayAbstractGet = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.core.Array::get",
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
 * * [referenceArrayElementSetter]
 * * [buildValueArrayBoxingElementSetter]
 *
 * or the backend must emit specialized code for accessing the elements, just as in [buildValueArrayBoxingElementSetter],
 * because that depends on the element size.
 */
internal val arrayAbstractSet = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.core.Array::set",
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
internal fun inlineBoundsCheck(arrayPtr: LlvmValue<LlvmPointerType<out EmergeArrayType<*>>>, index: LlvmValue<EmergeWordType>) {
    val size = getelementptr(arrayPtr)
        .member { base }
        .member { EmergeArrayBaseType.elementCount }
        .get()
        .dereference()
    conditionalBranch(
        condition = icmp(index, LlvmIntPredicate.UNSIGNED_GREATER_THAN_OR_EQUAL, size),
        ifTrue = {
            inlinePanic("Array index out of bounds")
        }
    )
}