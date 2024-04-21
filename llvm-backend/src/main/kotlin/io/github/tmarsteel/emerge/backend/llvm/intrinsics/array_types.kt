package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.codegen.sizeof
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.IntegerComparison
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmInlineStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

internal object EmergeArrayBaseType : LlvmStructType("anyarray"), EmergeHeapAllocated {
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

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LLVMTypeRef) {
        check(LLVM.LLVMOffsetOfElement(context.targetData.ref, selfInContext, anyBase.indexInStruct) == 0L)
    }
}

internal class EmergeArrayType<Element : LlvmType>(
    val elementType: Element,
    /**
     * Has to return typeinfo that suits for an Array<E>. This is so boxed types can supply their type-specific virtual functions
     */
    private val typeinfo: StaticAndDynamicTypeInfo.Provider,
    elementTypeName: String,
) : LlvmStructType("array_$elementTypeName"), EmergeHeapAllocated {
    val base by structMember(EmergeArrayBaseType)
    val elements by structMember(LlvmArrayType(0L, elementType))

    /**
     * A constructor that will allocate an array of [this] type, filled with [LlvmContext.undefValue]s. Signature:
     *
     *     declare ptr array_E__ctor(%word elementCount)
     */
    val constructorOfUndefEntries: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeArrayType<Element>>> by lazy {
        KotlinLlvmFunction.define(
            super.name + "__ctor",
            pointerTo(this),
        ) {
            val elementCount by param(EmergeWordType)
            body {
                val allocationSize = add(this@EmergeArrayType.sizeof(), mul(elementType.sizeof(), elementCount))
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

                ret(allocation)
            }
        }
    }

    override fun computeRaw(context: LlvmContext): LLVMTypeRef {
        val raw = super.computeRaw(context)
        assureReinterpretableAsAnyValue(context, raw)
        return raw
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LLVMTypeRef) {
        check(LLVM.LLVMOffsetOfElement(context.targetData.ref, selfInContext, base.indexInStruct) == 0L)
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

        val anyArrayBaseOffsetInGeneralType = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            this.getRawInContext(context),
            base.indexInStruct,
        )
        val anyArrayBaseOffsetInConstant = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            inlineConstant.type.getRawInContext(context),
            0,
        )
        check(anyArrayBaseOffsetInConstant == anyArrayBaseOffsetInGeneralType)

        val firstElementOffsetInGeneralType = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            this.getRawInContext(context),
            1,
        )
        val firstElementOffsetInConstant = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            inlineConstant.type.getRawInContext(context),
            1,
        )
        check(firstElementOffsetInConstant == firstElementOffsetInGeneralType)

        return inlineConstant
    }

    companion object {
        val VIRTUAL_FUNCTION_HASH_GET_ELEMENT: Long = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
        val VIRTUAL_FUNCTION_HASH_SET_ELEMENT: Long = 0b0100_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
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
            // TODO: bounds check!
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

            // TODO: bounds check!
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

private fun <Element : LlvmType> buildValueArrayType(
    elementTypeName: String,
    elementType: Element,
    getBoxType: EmergeLlvmContext.() -> EmergeClassType,
) : EmergeArrayType<Element> {
    lateinit var arrayTypeHolder: EmergeArrayType<Element>
    val getter = buildValueArrayBoxingElementGetter(elementTypeName, { arrayTypeHolder }, getBoxType)
    val setter = buildValueArrayBoxingElementSetter(elementTypeName, { arrayTypeHolder }, getBoxType)
    arrayTypeHolder = EmergeArrayType(
        elementType,
        StaticAndDynamicTypeInfo.define(
            "array_$elementTypeName",
            emptyList(),
            { ctx -> ctx.registerIntrinsic(valueArrayFinalize) },
        ) {
            mapOf(
                EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT to registerIntrinsic(getter),
                EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT to registerIntrinsic(setter),
            )
        },
        elementTypeName,
    )

    return arrayTypeHolder
}

internal val EmergeS8ArrayType = buildValueArrayType("s8", LlvmI8Type, EmergeLlvmContext::boxTypeS8)
internal val EmergeU8ArrayType = buildValueArrayType("u8", LlvmI8Type, EmergeLlvmContext::boxTypeU8)
internal val EmergeS16ArrayType = buildValueArrayType("s16", LlvmI8Type, EmergeLlvmContext::boxTypeS16)
internal val EmergeU16ArrayType = buildValueArrayType("u16", LlvmI8Type, EmergeLlvmContext::boxTypeU16)
internal val EmergeS32ArrayType = buildValueArrayType("s32", LlvmI8Type, EmergeLlvmContext::boxTypeS32)
internal val EmergeU32ArrayType = buildValueArrayType("u32", LlvmI8Type, EmergeLlvmContext::boxTypeU32)
internal val EmergeS64ArrayType = buildValueArrayType("s64", LlvmI8Type, EmergeLlvmContext::boxTypeS64)
internal val EmergeU64ArrayType = buildValueArrayType("u64", LlvmI8Type, EmergeLlvmContext::boxTypeU64)
internal val EmergeSWordArrayType = buildValueArrayType("sword", LlvmI8Type, EmergeLlvmContext::boxTypeSWord)
internal val EmergeUWordArrayType = buildValueArrayType("uword", LlvmI8Type, EmergeLlvmContext::boxTypeUWord)
internal val EmergeBooleanArrayType = buildValueArrayType("bool", LlvmBooleanType, EmergeLlvmContext::boxTypeBoolean)

private val referenceArrayElementGetter: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeHeapAllocatedValueBaseType>> = KotlinLlvmFunction.define(
    "emerge.platform.referenceArrayGet",
    PointerToAnyEmergeValue,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(EmergeWordType)
    body {
        // TODO: bounds check!
        val referenceEntry = getelementptr(self)
            .member { elements }
            .index(index)
            .get()
            .dereference()

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
        // TODO: bounds check!
        val pointerToSlotInArray = getelementptr(self)
            .member { elements }
            .index(index)
            .get()

        store(value, pointerToSlotInArray)
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
        val size = getelementptr(self)
            .member { base }
            .member { elementCount }
            .get()
            .dereference()

        loop(
            header = {
                val endReached = icmp(indexStackSlot.dereference(), IntegerComparison.EQUAL, size)
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

internal val EmergeReferenceArrayType: EmergeArrayType<LlvmPointerType<EmergeHeapAllocatedValueBaseType>> = EmergeArrayType(
    PointerToAnyEmergeValue,
    StaticAndDynamicTypeInfo.define(
        "array_ref",
        emptyList(),
        { ctx -> ctx.registerIntrinsic(referenceArrayFinalizer) },
    ) {
        mapOf(
            EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT to registerIntrinsic(referenceArrayElementGetter),
            EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT to registerIntrinsic(referenceArrayElementSetter),
        )
    },
    "ref"
)

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
    val arrayPointer by param(pointerTo(EmergeArrayBaseType))
    body {
        val ptr = getelementptr(arrayPointer, context.i32(1))
            .get()
            .reinterpretAs(pointerTo(LlvmVoidType))

        ret(ptr)
    }
}
internal val arraySize = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.core.size",
    EmergeWordType,
) {
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