package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrIntersectionType
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.llvm.IrSimpleTypeImpl
import io.github.tmarsteel.emerge.backend.llvm.autoboxer
import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitRead
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.PhiBucket
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.dsl.u8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.abortOnException
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.llvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.reifiedTypeArgumentValues
import io.github.tmarsteel.emerge.backend.llvm.signatureHashes
import io.github.tmarsteel.emerge.backend.llvm.typeinfoHolder
import io.github.tmarsteel.emerge.common.EmergeConstants

/**
 * The layout of the array object that holds elements of a type; stored in the typeinfo of every base type
 * (`arrayElementLayoutKind`) so that `Array.new::<T>` can pick the layout at runtime.
 */
internal enum class ArrayElementLayoutKind {
    REFERENCE,
    S8, U8, S16, U16, S32, U32, S64, U64, SWORD, UWORD, BOOL,
    SLICE,
    TYPEINFO_PTR,
    ;

    val code: ULong get() = ordinal.toULong()
}

internal fun layoutKindOf(arrayObjectType: LlvmType): ArrayElementLayoutKind = when (arrayObjectType) {
    EmergeReferenceArrayType -> ArrayElementLayoutKind.REFERENCE
    EmergeS8ArrayType -> ArrayElementLayoutKind.S8
    EmergeU8ArrayType -> ArrayElementLayoutKind.U8
    EmergeS16ArrayType -> ArrayElementLayoutKind.S16
    EmergeU16ArrayType -> ArrayElementLayoutKind.U16
    EmergeS32ArrayType -> ArrayElementLayoutKind.S32
    EmergeU32ArrayType -> ArrayElementLayoutKind.U32
    EmergeS64ArrayType -> ArrayElementLayoutKind.S64
    EmergeU64ArrayType -> ArrayElementLayoutKind.U64
    EmergeSWordArrayType -> ArrayElementLayoutKind.SWORD
    EmergeUWordArrayType -> ArrayElementLayoutKind.UWORD
    EmergeBooleanArrayType -> ArrayElementLayoutKind.BOOL
    EmergeSliceArrayType -> ArrayElementLayoutKind.SLICE
    PointerToEmergeArrayOfPointersToTypeInfoType.pointed -> ArrayElementLayoutKind.TYPEINFO_PTR
    else -> throw CodeGenerationException("$arrayObjectType is not an array object type with a known element layout")
}

internal fun arrayTypeForLayoutKind(kind: ArrayElementLayoutKind): EmergeArrayType<*> = when (kind) {
    ArrayElementLayoutKind.REFERENCE -> EmergeReferenceArrayType
    ArrayElementLayoutKind.S8 -> EmergeS8ArrayType
    ArrayElementLayoutKind.U8 -> EmergeU8ArrayType
    ArrayElementLayoutKind.S16 -> EmergeS16ArrayType
    ArrayElementLayoutKind.U16 -> EmergeU16ArrayType
    ArrayElementLayoutKind.S32 -> EmergeS32ArrayType
    ArrayElementLayoutKind.U32 -> EmergeU32ArrayType
    ArrayElementLayoutKind.S64 -> EmergeS64ArrayType
    ArrayElementLayoutKind.U64 -> EmergeU64ArrayType
    ArrayElementLayoutKind.SWORD -> EmergeSWordArrayType
    ArrayElementLayoutKind.UWORD -> EmergeUWordArrayType
    ArrayElementLayoutKind.BOOL -> EmergeBooleanArrayType
    ArrayElementLayoutKind.SLICE -> EmergeSliceArrayType
    ArrayElementLayoutKind.TYPEINFO_PTR -> PointerToEmergeArrayOfPointersToTypeInfoType.pointed
}

/**
 * @return the layout of arrays whose elements are exactly (not nullable, not a subtype) of [baseType]
 */
internal fun EmergeLlvmContext.arrayElementLayoutKindOf(baseType: IrBaseType): ArrayElementLayoutKind {
    return layoutKindOf(getArrayObjectTypeOfExactElement(baseType, isNullable = false))
}

/**
 * @return the runtime type information object for [baseType], as `reflect <baseType>` evaluates to
 */
internal fun EmergeLlvmContext.typeinfoPointerOf(baseType: IrBaseType): LlvmGlobal<TypeinfoType> {
    val boxedType = baseType.autoboxer?.getBoxedType(this)
    if (boxedType != null) {
        return boxedType.getTypeinfoInContext(this).dynamic
    }

    return when (baseType) {
        is IrClass -> {
            val emergeClass = getEmergeClassByIrType(baseType)
                ?: throw CodeGenerationException("Cannot reflect on unknown base type $baseType")
            emergeClass.getTypeinfoInContext(this).dynamic
        }
        is IrInterface -> baseType.typeinfoHolder.getTypeinfoInContext(this)
        else -> throw CodeGenerationException("Unsupported base type ${baseType::class.qualifiedName}")
    }
}

internal fun IrClass.fieldOfMemberVariable(name: String): IrClass.Field {
    val memberVariable = memberVariables.singleOrNull { it.name == name }
        ?: throw CodeGenerationException("$canonicalName has no member variable $name")
    val fieldId = (memberVariable.readStrategy as IrClass.MemberVariable.AccessStrategy.BareField).fieldId
    return fields.single { it.id == fieldId }
}

/**
 * Whether [this] mentions a type parameter; if so, the runtime type information for it has to be constructed
 * at runtime (see `TypeEnvironment`), otherwise [staticReifiedType] applies.
 */
internal val IrType.mentionsTypeParameter: Boolean get() = when (this) {
    is IrGenericTypeReference -> true
    is IrSimpleType -> false
    is IrParameterizedType -> arguments.values.any { it.type.mentionsTypeParameter }
    is IrIntersectionType -> components.any { it.mentionsTypeParameter }
}

/**
 * @return a static `emerge.core.reflection.Type` object describing [type]. Mutability is not part of the runtime
 * type information, so types that differ only in mutability share the object.
 */
internal fun EmergeLlvmContext.staticReifiedType(type: IrType): LlvmGlobal<EmergeClassType> {
    check(!type.mentionsTypeParameter) {
        "Cannot build a static runtime type for $type, it mentions a type parameter"
    }

    val key = reifiedTypeKey(type)
    staticReifiedTypes[key]?.let { return it }

    return when (type) {
        is IrSimpleType -> buildStaticNamedType(key, type.baseType, type.isNullable, emptyList())
        is IrParameterizedType -> buildStaticNamedType(
            key,
            type.simpleType.baseType,
            type.isNullable,
            type.simpleType.baseType.parameters.map { type.arguments.getValue(it.name) },
        )
        is IrIntersectionType -> {
            val clazz = reifiedIntersectionTypeClass
            val global = addGlobal(undefValue(clazz), LlvmThreadLocalMode.NOT_THREAD_LOCAL)
            staticReifiedTypes[key] = global
            val components = type.components.map { staticReifiedType(it) }
            val componentsArray = staticReferenceArray(components, IrSimpleTypeImpl(reifiedNamedTypeClass.irClass, IrTypeMutability.IMMUTABLE, false))
            val constant = clazz.buildStaticConstant(mapOf(
                clazz.irClass.fieldOfMemberVariable("components") to componentsArray,
            ))
            Llvm.LLVMSetInitializer(global.raw, constant.raw)
            global
        }
        is IrGenericTypeReference -> throw CodeGenerationException("unreachable")
    }
}

private fun EmergeLlvmContext.buildStaticNamedType(
    key: String,
    baseType: IrBaseType,
    nullable: Boolean,
    arguments: List<IrParameterizedType.Argument>,
): LlvmGlobal<EmergeClassType> {
    val clazz = reifiedNamedTypeClass
    val global = addGlobal(undefValue(clazz), LlvmThreadLocalMode.NOT_THREAD_LOCAL)
    // register before building the initializer; the arguments array and the typeinfo of NamedType refer back to this
    staticReifiedTypes[key] = global

    val argumentObjects = arguments.map { argument ->
        val argumentClazz = reifiedTypeArgumentClass
        val constant = argumentClazz.buildStaticConstant(mapOf(
            argumentClazz.irClass.fieldOfMemberVariable("variance") to u8(argument.variance.runtimeCode).asConstant(),
            argumentClazz.irClass.fieldOfMemberVariable("value") to staticReifiedType(argument.type),
        ))
        addGlobal(constant, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
    }
    val argumentsArray = staticReferenceArray(argumentObjects, IrSimpleTypeImpl(reifiedTypeArgumentClass.irClass, IrTypeMutability.IMMUTABLE, false))

    val constant = clazz.buildStaticConstant(mapOf(
        clazz.irClass.fieldOfMemberVariable("baseType") to LlvmConstant(typeinfoPointerOf(baseType).raw, pointerTo(TypeinfoType.GENERIC)),
        clazz.irClass.fieldOfMemberVariable("nullable") to i1(nullable).asConstant(),
        clazz.irClass.fieldOfMemberVariable("arguments") to argumentsArray,
    ))
    Llvm.LLVMSetInitializer(global.raw, constant.raw)
    return global
}

/**
 * @return a constant slice of a static reference array holding [elements]
 */
private fun EmergeLlvmContext.staticReferenceArray(
    elements: List<LlvmGlobal<EmergeClassType>>,
    elementType: IrType,
): LlvmConstant<EmergeArraySliceType> {
    val arrayConstant = EmergeReferenceArrayType.buildConstantIn(this, elements, staticReifiedType(elementType)) { it }
    val arrayGlobal = addGlobal(arrayConstant, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
    return buildConstantSliceOf(arrayGlobal, elements.size.toLong())
}

internal val IrTypeVariance.runtimeCode: UByte get() = when (this) {
    IrTypeVariance.INVARIANT -> EmergeConstants.ReflectionModule.VARIANCE_INVARIANT
    IrTypeVariance.IN -> EmergeConstants.ReflectionModule.VARIANCE_IN
    IrTypeVariance.OUT -> EmergeConstants.ReflectionModule.VARIANCE_OUT
}

private fun <T : LlvmType> LlvmValue<T>.asConstant(): LlvmConstant<T> = this as? LlvmConstant<T> ?: LlvmConstant(raw, type)

/**
 * identifies the runtime type information for [type]; ignores mutability
 */
private fun reifiedTypeKey(type: IrType): String {
    val nullableSuffix = if (type.isNullable) "?" else ""
    return when (type) {
        is IrSimpleType -> type.baseType.canonicalName.toString() + nullableSuffix
        is IrParameterizedType -> {
            val base = type.simpleType.baseType
            base.canonicalName.toString() + base.parameters.joinToString(",", "<", ">") { parameter ->
                val argument = type.arguments.getValue(parameter.name)
                "${argument.variance} ${reifiedTypeKey(argument.type)}"
            } + nullableSuffix
        }
        is IrIntersectionType -> type.components.map(::reifiedTypeKey).sorted().joinToString("&")
        is IrGenericTypeReference -> throw CodeGenerationException("type parameters have no static runtime type information")
    }
}

/**
 * The reference-site type of hidden type arguments and of fields holding runtime type information:
 * `emerge.core.reflection.Type` is an interface.
 */
internal val PointerToReifiedType: LlvmPointerType<out EmergeHeapAllocated> get() = PointerToAnyEmergeValue

internal typealias ReifiedTypeValue = LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>

/**
 * Resolves type parameters to their runtime type information while the body of [function] is being emitted.
 */
internal class TypeEnvironment(val function: IrFunction) {
    /**
     * @return a borrowed reference to the runtime type information for [parameter]
     */
    context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
    fun resolve(parameter: IrBaseType.Parameter): ReifiedTypeValue {
        function.reifiedTypeArgumentValues[parameter]?.let { return it }

        if (function is IrBaseTypeFunction && function.declaresReceiver) {
            val owner = function.ownerBaseType
            if (owner is IrClass && parameter in owner.parameters) {
                with(builder) {
                    val self = function.parameters.first().emitRead!!(builder)
                    if (owner.canonicalName == EmergeConstants.CoreModule.ARRAY_TYPE_NAME) {
                        // array objects are not instances of the Array class; the element type sits in the array header
                        @Suppress("UNCHECKED_CAST")
                        return getelementptr((self as LlvmValue<EmergeArraySliceType>).sliceBase)
                            .member { elementType }
                            .get()
                            .dereference()
                    }

                    val field = owner.typeParameterFields[parameter]
                        ?: throw CodeGenerationException("${owner.canonicalName} has no field for its type parameter ${parameter.name}")
                    return getelementptr(self.reinterpretAs(pointerTo(owner.llvmType)))
                        .member(field)
                        .get()
                        .dereference()
                        .reinterpretAs(PointerToReifiedType)
                }
            }
        }

        throw CodeGenerationException("Type parameter ${parameter.name} is not in scope in ${function.canonicalName}")
    }
}

/**
 * @return the runtime type information for [type]; a reference owned by the caller (must be dropped).
 */
context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun lowerReifiedType(type: IrType): ReifiedTypeValue {
    with(builder) {
        if (!type.mentionsTypeParameter) {
            val static = context.staticReifiedType(type).reinterpretAs(PointerToReifiedType)
            static.afterReferenceCreated(isNullable = false)
            return static
        }

        val environment = context.currentTypeEnvironment
            ?: throw CodeGenerationException("Cannot reify $type outside of a function body")

        return when (type) {
            is IrGenericTypeReference -> {
                val borrowed = environment.resolve(type.parameter)
                when (val override = type.nullabilityOverride) {
                    null -> {
                        borrowed.afterReferenceCreated(isNullable = false)
                        borrowed
                    }
                    else -> callWithNullability(borrowed, override)
                }
            }
            is IrParameterizedType -> {
                val base = type.simpleType.baseType
                val arguments = base.parameters.map { parameter ->
                    val argument = type.arguments.getValue(parameter.name)
                    Pair(argument.variance, lowerReifiedType(argument.type))
                }
                val namedType = newNamedType(
                    context.typeinfoPointerOf(base).reinterpretAs(pointerTo(TypeinfoType.GENERIC)),
                    type.isNullable,
                    arguments,
                )
                arguments.forEach { (_, argumentType) -> argumentType.afterReferenceDropped(isNullable = false) }
                namedType
            }
            is IrIntersectionType -> {
                val componentObjects = type.components.map { lowerReifiedType(it) }
                val componentsArray = newReferenceArrayOf(componentObjects, IrSimpleTypeImpl(context.reifiedTypeInterface, IrTypeMutability.IMMUTABLE, false))
                @Suppress("UNCHECKED_CAST")
                val intersection = call(
                    context.intersectionOfFn.llvmRef as LlvmFunction<EmergeFallibleCallResult<LlvmPointerType<out EmergeHeapAllocated>>>,
                    listOf(buildArraySliceOfEntireArray(componentsArray)),
                ).abortOnException { exceptionPtr -> propagateOrPanic(exceptionPtr) }
                componentsArray.afterReferenceDropped(isNullable = false)
                intersection
            }
            is IrSimpleType -> throw CodeGenerationException("unreachable, simple types don't mention type parameters")
        }
    }
}

/**
 * @param arguments the types are borrowed
 * @return a new `emerge.core.reflection.NamedType`, a reference owned by the caller
 */
context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun newNamedType(
    baseType: LlvmValue<LlvmPointerType<TypeinfoType>>,
    nullable: Boolean,
    arguments: List<Pair<IrTypeVariance, ReifiedTypeValue>>,
): ReifiedTypeValue {
    with(builder) {
        val argumentObjects = arguments.map { (variance, type) ->
            call(
                context.reifiedTypeArgumentClass.constructor,
                listOf(context.u8(variance.runtimeCode), type),
            ).abortOnException { exceptionPtr -> propagateOrPanic(exceptionPtr) }
        }
        val argumentsArray = newReferenceArrayOf(argumentObjects, IrSimpleTypeImpl(context.reifiedTypeArgumentClass.irClass, IrTypeMutability.IMMUTABLE, false))
        val namedType = call(
            context.reifiedNamedTypeClass.constructor,
            listOf(
                baseType,
                context.i1(nullable),
                buildArraySliceOfEntireArray(argumentsArray),
            ),
        ).abortOnException { exceptionPtr -> propagateOrPanic(exceptionPtr) }
        argumentsArray.afterReferenceDropped(isNullable = false)
        return namedType.reinterpretAs(PointerToReifiedType)
    }
}

/**
 * @return `type.withNullability(nullable)`, a reference owned by the caller
 */
context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
private fun callWithNullability(type: ReifiedTypeValue, nullable: Boolean): ReifiedTypeValue {
    with(builder) {
        val fn = context.reifiedTypeInterface.memberFunctions
            .asSequence()
            .flatMap { it.overloads }
            .single { it.canonicalName.simpleName == EmergeConstants.ReflectionModule.TYPE_WITH_NULLABILITY_FN_NAME }
        val address = callIntrinsic(getDynamicCallAddress, listOf(type, context.uWord(fn.signatureHashes.first())))
        @Suppress("UNCHECKED_CAST")
        return call(
            address,
            fn.llvmFunctionType as LlvmFunctionType<EmergeFallibleCallResult<LlvmPointerType<out EmergeHeapAllocated>>>,
            listOf(type, context.i1(nullable)),
        ).abortOnException { exceptionPtr -> propagateOrPanic(exceptionPtr) }
    }
}

/**
 * `(type: Type) -> uword`: the [ArrayElementLayoutKind.code] of arrays whose elements are of the given runtime type.
 * Must agree with [EmergeLlvmContext.getArrayObjectTypeOfExactElement] and [EmergeLlvmContext.getArrayObjectType].
 */
internal val arrayElementLayoutKindOfReifiedType = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeUWordType>(
    "emerge.platform.arrayElementLayoutKindOf",
    EmergeUWordType,
) {
    val type by param(PointerToReifiedType)
    body {
        val namedTypeClass = context.reifiedNamedTypeClass
        val namedTypeTypeinfo = namedTypeClass.getTypeinfoInContext(context)
        val typeinfoPtr = type.anyValueBase().member { this.typeinfo }.get().dereference()
        val isNamedType = or(isEq(typeinfoPtr, namedTypeTypeinfo.dynamic), isEq(typeinfoPtr, namedTypeTypeinfo.static))

        val result = PhiBucket(EmergeUWordType)
        conditionalBranch(
            condition = isNamedType,
            ifTrue = {
                val namedType = type.reinterpretAs(pointerTo(namedTypeClass))
                val baseTypeinfo = getelementptr(namedType)
                    .member(namedTypeClass.irClass.fieldOfMemberVariable("baseType"))
                    .get()
                    .dereference()
                    .reinterpretAs(pointerTo(TypeinfoType.GENERIC))
                val kind = getelementptr(baseTypeinfo)
                    .member { arrayElementLayoutKind }
                    .get()
                    .dereference()
                val nullable = getelementptr(namedType)
                    .member(namedTypeClass.irClass.fieldOfMemberVariable("nullable"))
                    .get()
                    .dereference()
                    .reinterpretAs(LlvmBooleanType)
                // nullable elements of value types are boxed; nullable arrays are still slices
                val isSlice = icmp(kind, LlvmIntPredicate.EQUAL, context.uWord(ArrayElementLayoutKind.SLICE.code))
                val nullableKind = select(isSlice, kind, context.uWord(ArrayElementLayoutKind.REFERENCE.code))
                result.setBranchResult(select(nullable, nullableKind, kind))
                concludeBranch()
            },
            ifFalse = {
                // an intersection type has no single base type; its values are references
                result.setBranchResult(context.uWord(ArrayElementLayoutKind.REFERENCE.code))
                concludeBranch()
            },
        )
        ret(result.buildPhi())
    }
}

private val arrayCtorOfNullEntriesType = LlvmFunctionType(pointerTo(EmergeArrayBaseType), listOf(EmergeUWordType, PointerToReifiedType))
private val arrayDefaultValueCtorFromBoxedType = LlvmFunctionType(EmergeArraySliceType, listOf(EmergeUWordType, PointerToAnyEmergeValue, PointerToReifiedType))

/**
 * @return a global array of function addresses, indexed by [ArrayElementLayoutKind.code]
 */
private fun EmergeLlvmContext.functionTableByLayoutKind(
    name: String,
    functionFor: (ArrayElementLayoutKind) -> LlvmFunction<*>,
): LlvmGlobal<LlvmArrayType<LlvmFunctionAddressType>> {
    val kinds = ArrayElementLayoutKind.entries
    val tableType = LlvmArrayType(kinds.size.toLong(), LlvmFunctionAddressType)
    val table = tableType.buildConstantIn(this, kinds.map { functionFor(it).address })
    return addGlobal(table, LlvmThreadLocalMode.NOT_THREAD_LOCAL, name)
}

/**
 * `(size: uword, elementType: Type) -> ptr anyarray`: like [EmergeArrayType.constructorOfNullEntries], with the
 * array object type chosen from the runtime type of the elements.
 */
internal val arrayNewNullDynamic = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmPointerType<EmergeArrayBaseType>>(
    "emerge.platform.array_new_null_dynamic",
    pointerTo(EmergeArrayBaseType),
) {
    val size by param(EmergeUWordType)
    val elementType by param(PointerToReifiedType)
    body {
        val kind = callIntrinsic(arrayElementLayoutKindOfReifiedType, listOf(elementType))
        val table = context.functionTableByLayoutKind("array_null_ctors_by_layout") { layoutKind ->
            context.registerIntrinsic(arrayTypeForLayoutKind(layoutKind).constructorOfNullEntries)
        }
        val ctor = getelementptr(table).index(kind).get().dereference()
        ret(call(ctor, arrayCtorOfNullEntriesType, listOf(size, elementType)))
    }
}

/**
 * `(size: uword, defaultValue: Any, elementType: Type) -> arrayslice`: like [EmergeArrayType.defaultValueConstructor],
 * with the array object type chosen from the runtime type of the elements; the default value is boxed.
 */
internal val arrayNewDynamic = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeArraySliceType>(
    "emerge.platform.array_new_dynamic",
    EmergeArraySliceType,
) {
    val size by param(EmergeUWordType)
    val boxedDefaultValue by param(PointerToAnyEmergeValue)
    val elementType by param(PointerToReifiedType)
    body {
        val kind = callIntrinsic(arrayElementLayoutKindOfReifiedType, listOf(elementType))
        val table = context.functionTableByLayoutKind("array_default_value_ctors_by_layout") { layoutKind ->
            context.registerIntrinsic(arrayTypeForLayoutKind(layoutKind).defaultValueConstructorFromBoxed)
        }
        val ctor = getelementptr(table).index(kind).get().dereference()
        ret(call(ctor, arrayDefaultValueCtorFromBoxedType, listOf(size, boxedDefaultValue, elementType)))
    }
}

/**
 * @param elements owned references; ownership moves into the array
 * @return a new reference array holding [elements], a reference owned by the caller
 */
context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
private fun newReferenceArrayOf(elements: List<ReifiedTypeValue>, elementType: IrType): LlvmValue<LlvmPointerType<EmergeArrayType<LlvmPointerType<out EmergeHeapAllocated>>>> {
    with(builder) {
        val reifiedElementType = lowerReifiedType(elementType)
        val array = callIntrinsic(EmergeReferenceArrayType.constructorOfNullEntries, listOf(context.uWord(elements.size.toULong()), reifiedElementType))
        reifiedElementType.afterReferenceDropped(isNullable = false)
        elements.forEachIndexed { index, element ->
            store(
                element,
                getelementptr(array)
                    .member { this.elements }
                    .index(context.uWord(index.toULong()))
                    .get()
            )
        }
        return array
    }
}
