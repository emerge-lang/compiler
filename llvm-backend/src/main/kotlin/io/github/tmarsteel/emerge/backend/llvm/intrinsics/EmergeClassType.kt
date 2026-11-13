package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.*
import io.github.tmarsteel.emerge.backend.llvm.*
import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.codegen.emergeStringLiteral
import io.github.tmarsteel.emerge.backend.llvm.codegen.findSimpleTypeBound
import io.github.tmarsteel.emerge.backend.llvm.dsl.*
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.jna.*
import io.github.tmarsteel.emerge.common.CanonicalElementName

internal class EmergeClassType private constructor(
    val context: EmergeLlvmContext,
    val structRef: LlvmTypeRef,
    val irClass: IrClass,
) : LlvmType, EmergeHeapAllocated {
    override fun getRawInContext(context: LlvmContext): LlvmTypeRef {
        check(context === context)
        return structRef
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LlvmTypeRef) {
        // done in [fromLlvmStructWithoutBody]
    }

    /**
     * For the classes the backend instantiates on its own; their constructors have to be `nothrow`.
     */
    val constructor: LlvmFunction<LlvmPointerType<EmergeClassType>> get() {
        check(irClass.constructor.hasNothrowAbi) {
            "The constructor of ${irClass.canonicalName} must be nothrow, the backend depends on it"
        }
        @Suppress("UNCHECKED_CAST")
        return irClass.constructor.llvmRef!! as LlvmFunction<LlvmPointerType<EmergeClassType>>
    }
    val destructor: LlvmFunction<*> get() = irClass.destructor.llvmRef!! as LlvmFunction<*>

    private val isBox: Boolean
        get() = irClass.canonicalName.packageName.toString() == "emerge.platform" && irClass.canonicalName.simpleName.endsWith("Box")

    /**
     * The base type this classes typeinfo describes: boxes have only one member variable, holding the boxed value,
     * and their typeinfo acts as the typeinfo of the boxed type.
     */
    private val reflectedBaseType: IrBaseType
        get() = if (isBox) irClass.singleMemberVariableField.type.findSimpleTypeBound().baseType else irClass

    private val typeinfoProvider: StaticAndDynamicTypeInfo.Provider by lazy {
        if (this.irClass.canonicalName.toString() == "emerge.core.Array") {
            // the only objects of type Array that emerge code can observe are boxes
            return@lazy StaticAndDynamicTypeInfo.Provider { ctx -> ctx.boxTypeArray.getTypeinfoInContext(ctx) }
        }

        if (this.irClass.canonicalName.toString() == "emerge.platform.ArrayBox") {
            return@lazy StaticAndDynamicTypeInfo.define(
                { ctx -> ctx.rawArrayClazz.canonicalName.toString() },
                context.rawArrayClazz.allDistinctSupertypesExceptAny,
                finalizerFunction = { _ -> destructor },
                runtimeTypeGetter = { context -> context.registerIntrinsic(arrayRuntimeTypeGetter) },
                virtualFunctions = {
                    rawArrayClazz.memberFunctions
                        .asSequence()
                        .flatMap { it.overloads }
                        .filter { it.overrides.isNotEmpty() && it.supportsDynamicDispatch }
                        .flatMap { memberFn ->
                            val bridge = registerIntrinsic(buildArrayBoxBridge(memberFn))
                            memberFn.signatureHashes.map { hash -> Pair(hash, bridge) }
                        }
                        .associateErrorOnDuplicate()
                },
                arrayElementLayoutKind = ArrayElementLayoutKind.SLICE,
            )
        }

        StaticAndDynamicTypeInfo.define(
            { _ -> reflectedBaseType.canonicalName.toString() },
            irClass.allDistinctSupertypesExceptAny,
            runtimeTypeGetter = { context -> buildRuntimeTypeGetter(context, this@EmergeClassType, irClass) },
            finalizerFunction = { _ -> destructor },
            virtualFunctions = {
                irClass.memberFunctions
                    .asSequence()
                    .flatMap { it.overloads }
                    .filter { it.overrides.isNotEmpty() && it.supportsDynamicDispatch }
                    .flatMap { memberFn -> memberFn.signatureHashes.map { hash -> Pair(hash, memberFn.llvmRef!!) } }
                    .associateErrorOnDuplicate()
            },
            arrayElementLayoutKind = context.arrayElementLayoutKindOf(reflectedBaseType),
        )
    }

    fun getTypeinfoInContext(context: EmergeLlvmContext): StaticAndDynamicTypeInfo {
        try {
            return typeinfoProvider.provide(context)
        } catch (ex: VirtualFunctionHashCollisionException) {
            throw VirtualFunctionHashCollisionException("Type ${irClass.canonicalName}: ${ex.message}", ex)
        }
    }

    /**
     * The implementation of [IrAllocateObjectExpression], for objects that are supposed to be de-allocate-able (not static)
     */
    fun allocateUninitializedDynamicObject(builder: BasicBlockBuilder<EmergeLlvmContext, *>): LlvmValue<LlvmPointerType<EmergeClassType>> {
        check(builder.context === this.context)
        val typeinfo = getTypeinfoInContext(builder.context)
        val heapAllocation: LlvmValue<LlvmPointerType<EmergeClassType>>
        with(builder) {
            heapAllocation = heapAllocate(this@EmergeClassType)
            val basePointer = getelementptr(heapAllocation).anyValueBase().get()
            store(
                context.uWord(1u),
                getelementptr(basePointer)
                    .member { this.strongReferenceCount }
                    .get()
            )
            store(
                typeinfo.dynamic,
                getelementptr(basePointer)
                    .member { this.typeinfo }
                    .get()
            )
            store(
                context.nullValue(pointerTo(EmergeWeakReferenceCollectionType)),
                getelementptr(basePointer)
                    .member { this.weakReferenceCollection }
                    .get()
            )
        }

        return heapAllocation
    }

    private var diStructType: LlvmDebugInfo.Type? = null
    private var temporaryRefs: MutableList<LlvmDebugInfo.Type>? = null
    fun fillDiStructType(diBuilder: DiBuilder) {
        if (this.diStructType != null) {
            return
        }

        assureLlvmStructMembersDefined()

        diStructType = diBuilder.createStructType(
            irClass.canonicalName.toString(),
            Llvm.LLVMSizeOfTypeInBits(context.targetData.ref, structRef).toULong(),
            Llvm.LLVMABIAlignmentOfType(context.targetData.ref, structRef).toUInt() * 8u,
            NativeI32FlagGroup(),
            irClass.memberVariables
                .filter { it.readStrategy is IrClass.MemberVariable.AccessStrategy.BareField && it.writeStrategy is IrClass.MemberVariable.AccessStrategy.BareField }
                .associateWith {
                    val fieldId = (it.readStrategy as IrClass.MemberVariable.AccessStrategy.BareField).fieldId
                    irClass.fields.single { it.id == fieldId }
                }
                .map { (irMember, field) ->
                    val memberLlvmType = context.getReferenceSiteType(irMember.type)
                    val memberDiType = memberLlvmType.getDiType(diBuilder)
                    diBuilder.createStructMember(
                        irMember.name,
                        memberDiType.sizeInBits,
                        memberDiType.alignInBits,
                        Llvm.LLVMOffsetOfElement(diBuilder.context.targetData.ref, structRef, field.indexInLlvmStruct!!).toULong() * 8u,
                        memberDiType,
                        NativeI32FlagGroup(),
                        irMember.declaredAt,
                    )
                },
            irClass.declaredAt,
        )

        temporaryRefs?.forEach {
            Llvm.LLVMMetadataReplaceAllUsesWith(it.ref, diStructType!!.ref)
        }
    }

    override fun getDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        diStructType?.let { return it }

        val tmpRef = diBuilder.createTemporaryForwardDeclarationOfStructType(
            name = irClass.canonicalName.toString(),
            sizeInBits = 0u,
            alignInBits = 0u,
            flags = NativeI32FlagGroup(),
            declaredAt = irClass.declaredAt,
        )
        if (temporaryRefs == null) {
            temporaryRefs = ArrayList()
        }
        temporaryRefs!!.add(tmpRef)
        return tmpRef
    }

    /**
     * Builds an LLVM constant of the same shape as [allocateUninitializedDynamicObject] would build at runtime.
     * Initializes all fields as per [fieldValues], **entirely ignoring any initializer expressions or constructors
     * defined in the emerge source**.
     */
    fun buildStaticConstant(fieldValues: Map<IrClass.Field, LlvmConstant<*>>): LlvmConstant<EmergeClassType> {
        fieldValues.keys.firstOrNull { it !in irClass.fields }?.also {
            throw CodeGenerationException("Field #${it.id} is not a member of ${irClass.canonicalName}")
        }

        assureLlvmStructMembersDefined()

        val typeinfo = getTypeinfoInContext(context)
        val baseValue = EmergeHeapAllocatedValueBaseType.buildConstantIn(context) {
            setValue(EmergeHeapAllocatedValueBaseType.strongReferenceCount, context.uWord(1u))
            setValue(EmergeHeapAllocatedValueBaseType.typeinfo, typeinfo.static)
            setNull(EmergeHeapAllocatedValueBaseType.weakReferenceCollection)
        }
        val fieldValueConstants = irClass.fields
            .sortedBy { it.indexInLlvmStruct }
            .map { irField ->
                val fieldValue = fieldValues[irField] ?: throw CodeGenerationException("Missing a value for field #${irField.id}")
                val fieldType = context.getReferenceSiteType(irField.type)
                check(fieldValue.type.isAssignableTo(fieldType)) {
                    "Value for field #${irField.id} is of type ${fieldValue.type}, which is not assignable to the type of the field $fieldType"
                }
                fieldValue
            }
            .map { it.raw }

        val structValues = listOf(baseValue.raw) + fieldValueConstants

        val rawConstant = NativePointerArray.fromJavaPointers(structValues).use { rawFieldLlvmValues ->
            Llvm.LLVMConstNamedStruct(structRef, rawFieldLlvmValues, rawFieldLlvmValues.length)
        }

        return LlvmConstant(rawConstant, this)
    }

    private var llvmStructMembersDefined = false
    fun assureLlvmStructMembersDefined() {
        if (llvmStructMembersDefined) {
            return
        }
        llvmStructMembersDefined = true

        val baseElements = listOf(
            EmergeHeapAllocatedValueBaseType
        ).map { it.getRawInContext(context) }

        irClass.fields.forEachIndexed { index, member ->
            member.indexInLlvmStruct = baseElements.size + index
        }

        val emergeMemberTypesRaw = irClass.fields.map { context.getReferenceSiteType(it.type).getRawInContext(context) }
        NativePointerArray.fromJavaPointers(baseElements + emergeMemberTypesRaw).use { llvmMemberTypesRaw ->
            Llvm.LLVMStructSetBody(structRef, llvmMemberTypesRaw, llvmMemberTypesRaw.length, 0)
        }

        check(Llvm.LLVMOffsetOfElement(context.targetData.ref, structRef, 0) == 0L) {
            "Cannot reinterpret emerge type ${irClass.canonicalName} as Any"
        }
    }

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        require(value.type is LlvmPointerType<*>)
        require(value.type.pointed is EmergeClassType)
        @Suppress("UNCHECKED_CAST")
        return builder.getelementptr(value as LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>)
            .stepUnsafe(builder.context.s32(0), EmergeHeapAllocatedValueBaseType)
    }

    override fun toString(): String {
        return "EmergeStruct[${irClass.canonicalName}]"
    }

    companion object {
        fun fromLlvmStructWithoutBody(
            context: EmergeLlvmContext,
            structRef: LlvmTypeRef,
            irClass: IrClass,
        ): EmergeClassType {
            return EmergeClassType(context, structRef, irClass)
        }

        context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
        internal fun GetElementPointerStep<EmergeClassType>.anyValueBase(): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
            return stepUnsafe(builder.context.s32(0), EmergeHeapAllocatedValueBaseType)
        }

        context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
        fun GetElementPointerStep<EmergeClassType>.member(field: IrClass.Field): GetElementPointerStep<LlvmType> {
            if (field.isCPointerPointed) {
                return this as GetElementPointerStep<LlvmType>
            }

            check(field in this@member.pointeeType.irClass.fields) {
                "field#${field.id} of type ${field.type} is not part of emerge class ${this@member.pointeeType.irClass.canonicalName}"
            }
            return stepUnsafe(builder.context.s32(field.indexInLlvmStruct!!), builder.context.getReferenceSiteType(field.type))
        }

        private fun buildRuntimeTypeGetter(
            context: EmergeLlvmContext,
            llvmSelfType: EmergeClassType,
            irClass: IrClass
        ): LlvmFunction<LlvmPointerType<out EmergeHeapAllocated>> {
            val irFnForMangler = object : IrMemberFunction {
                override val overrides = emptySet<IrMemberFunction>()
                override val supportsDynamicDispatch = false
                override val ownerBaseType = irClass
                override val canonicalName = CanonicalElementName.Function(
                    irClass.canonicalName,
                    "__runtime_type",
                )
                override val parameters = emptyList<IrVariableDeclaration>()
                override val declaresReceiver = true
                override val returnType = IrSimpleTypeImpl(context.reifiedNamedTypeClass.irClass, IrTypeMutability.IMMUTABLE, false)
                override val isNothrow = true
                override val isExternalC = false
                override val externalSymbolName: String? = null
                override val typeParameters = emptyList<IrBaseType.Parameter>()
                override val body = null
                override val declaredAt = irClass.declaredAt
            }

            val template = KotlinLlvmFunction.define(
                Mangler.computeMangledNameFor(irFnForMangler),
                PointerToAnyEmergeValue,
            ) {
                val self by param(pointerTo(llvmSelfType))

                body {
                    val selfTypeInfo = self.anyValueBase().member { typeinfo }.get().dereference("typeinfo")
                    val typeArguments = irClass.parameters.mapIndexed { index, parameter ->
                        val field = irClass.typeParameterFields.getValue(parameter)
                        Pair(
                            IrTypeVariance.INVARIANT,
                            getelementptr(self).member(field).get().dereference("ta$index").reinterpretAs(PointerToReifiedType),
                        )
                    }
                    ret(newNamedType(selfTypeInfo, false, typeArguments))
                }
            }

            val declared = template.declareInContext(context)
            declared.defineBody()
            return declared.function
        }
    }
}

private val bridgeParameter = Unit

/**
 * @return a function to put into the vtable of `emerge.platform.ArrayBox` in place of [arrayFn]: takes the
 * box as the receiver and forwards to [arrayFn] with the boxed slice.
 */
private fun buildArrayBoxBridge(arrayFn: IrMemberFunction): KotlinLlvmFunction<EmergeLlvmContext, LlvmType> {
    val arrayFnType = arrayFn.llvmFunctionType
    check(arrayFnType.parameterTypes.firstOrNull() == EmergeArraySliceType) {
        "Cannot bridge ${arrayFn.canonicalName} through emerge.platform.ArrayBox: its receiver is of type " +
            "${arrayFnType.parameterTypes.firstOrNull()}, not an array slice. Only functions declared on emerge.core.Array " +
            "can be bridged; a function inherited from a supertype of Array needs a bridge of its own."
    }
    return KotlinLlvmFunction.define(
        "emerge.platform.ArrayBox::${arrayFn.llvmName}",
        arrayFnType.returnType,
    ) {
        val box by param(PointerToAnyEmergeValue)
        val forwardedParams = arrayFnType.parameterTypes.drop(1).map { param(it) }
        body {
            val slice = Autoboxer.ArraySlice.unboxNotNull(box)
            val arguments = listOf(slice) + forwardedParams.map { it.getValue(null, ::bridgeParameter) }
            @Suppress("UNCHECKED_CAST")
            val result = call(arrayFn.llvmRef!! as LlvmFunction<LlvmType>, arguments)
            if (arrayFnType.returnType == LlvmVoidType) {
                (this as BasicBlockBuilder<EmergeLlvmContext, LlvmVoidType>).retVoid()
            } else {
                ret(result)
            }
        }
    }
}

internal class EmergeInterfaceTypeinfoHolder(
    val emergeInterface: IrInterface
) {
    private val valuesByContext: MutableMap<EmergeLlvmContext, LlvmGlobal<TypeinfoType>> = MapMaker().weakKeys().makeMap()

    fun getTypeinfoInContext(context: EmergeLlvmContext): LlvmGlobal<TypeinfoType> {
        return valuesByContext.computeIfAbsent(context) { context ->
            val canonicalName = emergeInterface.canonicalName.toString()
            val namePtr = context.emergeStringLiteral(canonicalName)

            val tArrayOfTypeinfoPtr = PointerToEmergeArrayOfPointersToTypeInfoType.pointed
            val supertypesArrayPtr = context.addGlobal(
                tArrayOfTypeinfoPtr.buildConstantIn(
                    context,
                    emergeInterface.allDistinctSupertypesExceptAny,
                    context.staticReifiedType(IrSimpleTypeImpl(context.rawReflectionBaseTypeClazz, IrTypeMutability.IMMUTABLE, false)),
                ) {
                    it.typeinfoHolder.getTypeinfoInContext(context)
                },
                LlvmThreadLocalMode.NOT_THREAD_LOCAL,
            ).reinterpretAs(pointerTo(LlvmVoidType))

            val constant = TypeinfoType.GENERIC.buildConstantIn(context) {
                setValue(TypeinfoType.GENERIC.supertypes, supertypesArrayPtr)
                setValue(TypeinfoType.GENERIC.anyValueVirtuals, context.poisonValue(EmergeAnyValueVirtualsType))
                setNull(TypeinfoType.GENERIC.dynamicTypeInfoPtr)
                setValue(TypeinfoType.GENERIC.canonicalNamePtr, namePtr)
                setValue(TypeinfoType.GENERIC.arrayElementLayoutKind, context.uWord(ArrayElementLayoutKind.REFERENCE.code))
                setValue(TypeinfoType.GENERIC.vtable, context.poisonValue(VTableType(0)))
            }

            context.addGlobal(constant, LlvmThreadLocalMode.NOT_THREAD_LOCAL, "typeinfo_${canonicalName}_interface")
        }
    }
}