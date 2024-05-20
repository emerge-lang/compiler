package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrIntrinsicType
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer
import io.github.tmarsteel.emerge.backend.llvm.autoboxer
import io.github.tmarsteel.emerge.backend.llvm.bodyDefined
import io.github.tmarsteel.emerge.backend.llvm.codegen.ExecutableResult
import io.github.tmarsteel.emerge.backend.llvm.codegen.ExpressionResult
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitCode
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitExpressionCode
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitRead
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitWrite
import io.github.tmarsteel.emerge.backend.llvm.codegen.sizeof
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmTarget
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.isUnit
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.llvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.rawLlvmRef
import java.util.Collections
import java.util.IdentityHashMap

class EmergeLlvmContext(
    target: LlvmTarget
) : LlvmContext(target) {
    /**
     * The function that allocates heap memory. Semantically equivalent to libcs
     * `void* malloc(size_t size)`.
     * Must be set by the backend class after [registerIntrinsic]
     */
    lateinit var allocateFunction: LlvmFunction<LlvmPointerType<LlvmVoidType>>

    /**
     * The function the deallocates heap memory. Semantically equivalent to libcs
     * `void free(void* memory)`
     * Must be set by the backend class after [registerIntrinsic]
     */
    lateinit var freeFunction: LlvmFunction<LlvmVoidType>

    /**
     * The function that exits the process. Semantically equivalent to libcs
     * `void exit(int status)`
     * Must be set by the backend class after [registerIntrinsic]
     */
    lateinit var exitFunction: LlvmFunction<LlvmVoidType>

    /**
     * The main function of the program. `fun main() -> Unit`
     * Set by [registerIntrinsic].
     */
    lateinit var mainFunction: LlvmFunction<LlvmVoidType>

    /** `emerge.platform.S8Box` */
    internal lateinit var boxTypeS8: EmergeClassType
    /** `emerge.platform.U8Box` */
    internal lateinit var boxTypeU8: EmergeClassType
    /** `emerge.platform.S16Box` */
    internal lateinit var boxTypeS16: EmergeClassType
    /** `emerge.platform.U16Box` */
    internal lateinit var boxTypeU16: EmergeClassType
    /** `emerge.platform.S32Box` */
    internal lateinit var boxTypeS32: EmergeClassType
    /** `emerge.platform.U32Box` */
    internal lateinit var boxTypeU32: EmergeClassType
    /** `emerge.platform.S64Box` */
    internal lateinit var boxTypeS64: EmergeClassType
    /** `emerge.platform.U64Box` */
    internal lateinit var boxTypeU64: EmergeClassType
    /** `emerge.platform.SWordBox` */
    internal lateinit var boxTypeSWord: EmergeClassType
    /** `emerge.platform.UWordBox` */
    internal lateinit var boxTypeUWord: EmergeClassType
    /** `emerge.platform.BoolBox` */
    internal lateinit var boxTypeBool: EmergeClassType
    /** `emerge.ffi.c.CPointer */
    internal lateinit var cPointerType: EmergeClassType
    /** `emerge.ffi.c.COpaquePointer` */
    internal lateinit var cOpaquePointerType: EmergeClassType

    /** `emerge.core.Unit` */
    internal lateinit var unitType: EmergeClassType
    internal lateinit var pointerToPointerToUnitInstance: LlvmGlobal<LlvmPointerType<EmergeClassType>>

    private val emergeStructs = ArrayList<EmergeClassType>()
    private val kotlinLlvmFunctions: MutableMap<KotlinLlvmFunction<in EmergeLlvmContext, *>, KotlinLlvmFunction.DeclaredInContext<in EmergeLlvmContext, *>> = IdentityHashMap()

    fun registerClass(clazz: IrClass) {
        if (clazz.rawLlvmRef != null) {
            return
        }

        val structType = Llvm.LLVMStructCreateNamed(ref, clazz.llvmName)
        // register here to allow cyclic references
        clazz.rawLlvmRef = structType
        val emergeClassType = EmergeClassType.fromLlvmStructWithoutBody(
            this,
            structType,
            clazz,
        )
        clazz.llvmType = emergeClassType

        when (clazz.canonicalName.toString()) {
            "emerge.platform.S8Box" -> boxTypeS8 = emergeClassType
            "emerge.platform.U8Box" -> boxTypeU8 = emergeClassType
            "emerge.platform.S16Box" -> boxTypeS16 = emergeClassType
            "emerge.platform.U16Box" -> boxTypeU16 = emergeClassType
            "emerge.platform.S32Box" -> boxTypeS32 = emergeClassType
            "emerge.platform.U32Box" -> boxTypeU32 = emergeClassType
            "emerge.platform.S64Box" -> boxTypeS64 = emergeClassType
            "emerge.platform.U64Box" -> boxTypeU64 = emergeClassType
            "emerge.platform.SWordBox" -> boxTypeSWord = emergeClassType
            "emerge.platform.UWordBox" -> boxTypeUWord = emergeClassType
            "emerge.platform.BoolBox" -> boxTypeBool = emergeClassType
            "emerge.ffi.c.CPointer" -> cPointerType = emergeClassType
            "emerge.ffi.c.COpaquePointer" -> cOpaquePointerType = emergeClassType
            "emerge.core.Unit" -> {
                unitType = emergeClassType
                pointerToPointerToUnitInstance = addGlobal(undefValue(pointerTo(emergeClassType)), LlvmThreadLocalMode.NOT_THREAD_LOCAL)
                addModuleInitFunction(registerIntrinsic(KotlinLlvmFunction.define(
                    "emerge.platform.initUnit",
                    LlvmVoidType,
                ) {
                    body {
                        val p = call(emergeClassType.constructor, emptyList())
                        store(p, pointerToPointerToUnitInstance)
                        retVoid()
                    }
                }))
            }
        }

        emergeStructs.add(emergeClassType)
    }

    fun defineClassStructure(clazz: IrClass) {
        clazz.llvmType.assureLlvmStructMembersDefined()
    }

    fun <R : LlvmType> registerIntrinsic(fn: KotlinLlvmFunction<in EmergeLlvmContext, R>): LlvmFunction<R> {
        val rawFn = this.kotlinLlvmFunctions
            .computeIfAbsent(fn) { it.declareInContext(this) }
            .function

        @Suppress("UNCHECKED_CAST")
        return rawFn as LlvmFunction<R>
    }

    /**
     * @param returnTypeOverride the return type on LLVM level. **DANGER!** there is only one intended use case for this:
     * making the constructor of core.emerge.Unit return ptr instead of void.
     */
    fun registerFunction(fn: IrFunction, returnTypeOverride: LlvmType? = null): LlvmFunction<*>? {
        fn.llvmRef?.let { return it }

        val parameterTypes = fn.parameters.map { getReferenceSiteType(it.type) }

        getInstrinsic(fn)?.let { intrinsic ->
            check(parameterTypes.size == intrinsic.type.parameterTypes.size)
            intrinsic.type.parameterTypes.forEachIndexed { paramIndex, intrinsicType ->
                val declaredType = parameterTypes[paramIndex]
                check(declaredType.isAssignableTo(intrinsicType)) { "${fn.canonicalName} param #$paramIndex; intrinsic $intrinsicType, declared $declaredType" }
            }
            fn.llvmRef = intrinsic
            if (fn is IrMemberFunction) {
                fn.llvmFunctionType = intrinsic.type
            }
            return intrinsic
        }

        val returnLlvmType = returnTypeOverride ?: if (fn.returnType.isUnit) LlvmVoidType else getReferenceSiteType(fn.returnType)
        val functionType = LlvmFunctionType(
            returnLlvmType,
            parameterTypes,
        )
        if (fn is IrMemberFunction) {
            fn.llvmFunctionType = functionType
            if (fn.body == null) {
                // abstract member fn is not relevant to LLVM
                return null
            }
        }
        val rawRef = Llvm.LLVMAddFunction(module, fn.llvmName, functionType.getRawInContext(this))
        fn.llvmRef = LlvmFunction(
            LlvmConstant(rawRef, LlvmFunctionAddressType),
            functionType,
        )

        fn.parameters.forEachIndexed { index, param ->
            param.emitRead = {
                LlvmValue(Llvm.LLVMGetParam(rawRef, index), getReferenceSiteType(param.type))
            }
            param.emitWrite = {
                throw CodeGenerationException("Writing to function parameters is forbidden.")
            }
        }

        if (fn.canonicalName.simpleName == "main") {
            if (this::mainFunction.isInitialized) {
                throw CodeGenerationException("Found multiple main functions!")
            }
            if (fn.parameters.isNotEmpty()) {
                throw CodeGenerationException("Main function must not declare parameters")
            }
            if (!fn.returnType.isUnit) {
                throw CodeGenerationException("Main function ${fn.canonicalName} must return Unit")
            }

            @Suppress("UNCHECKED_CAST")
            this.mainFunction = fn.llvmRef as LlvmFunction<LlvmVoidType>
        }

        return fn.llvmRef!!
    }

    fun registerGlobal(global: IrVariableDeclaration) {
        val globalType = getReferenceSiteType(global.type)
        val allocation = addGlobal(
            LlvmConstant(
                Llvm.LLVMGetUndef(globalType.getRawInContext(this)),
                globalType,
            ),
            LlvmThreadLocalMode.LOCAL_DYNAMIC,
        )
        global.emitRead = {
            allocation.dereference()
        }
        global.emitWrite = { newValue ->
            store(newValue, allocation)
        }
    }

    private var structConstructorsRegistered: Boolean = false
    fun defineFunctionBody(fn: IrFunction) {
        if (getInstrinsic(fn) != null) {
            return
        }

        val body = fn.body!!
        val llvmFunction = fn.llvmRef ?: throw CodeGenerationException("You must register the functions through ${this::registerFunction.name} first to handle cyclic references (especially important for recursion): ${fn.canonicalName}")
        if (fn.bodyDefined) {
            throw CodeGenerationException("Cannot define body for function ${fn.canonicalName} multiple times!")
        }

        if (!structConstructorsRegistered) {
            structConstructorsRegistered = true
            emergeStructs.forEach {
                // TODO: this handling is wonky, needs more conceptual work
                // the code will convert a return value of Unit to LLvmVoidType. That is correct except for this one
                // function -> adapt
                val returnTypeOverride = if (it == unitType) PointerToAnyEmergeValue else null
                val ref = registerFunction(it.irClass.constructor, returnTypeOverride)
                it.irClass.constructor.llvmRef = ref

                registerFunction(it.irClass.destructor)
                defineFunctionBody(it.irClass.destructor)
            }
        }

        BasicBlockBuilder.fillBody(this, llvmFunction) {
            fn.parameters
                .filterNot { it.isBorrowed }
                .forEach { param ->
                    param.emitRead!!().afterReferenceCreated(param.type)
                    defer {
                        param.emitRead!!().afterReferenceDropped(param.type)
                    }
                }

            when (val codeResult = emitCode(body)) {
                is ExecutableResult.ExecutionOngoing,
                is ExpressionResult.Value -> {
                    (this as BasicBlockBuilder<*, LlvmVoidType>).retVoid()
                }
                is ExpressionResult.Terminated -> {
                    codeResult.termination
                }
            }
        }
    }

    private val globalVariableInitializers = ArrayList<Pair<IrVariableDeclaration, IrExpression>>()
    fun defineGlobalInitializer(global: IrVariableDeclaration, initializer: IrExpression) {
        check(!completed)

        globalVariableInitializers.add(Pair(global, initializer))
    }

    lateinit var threadInitializerFn: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>
        private set
    private var completed = false
    override fun complete() {
        if (completed) {
            return
        }
        completed = true

        threadInitializerFn = KotlinLlvmFunction.define(
            "_emerge_thread_init",
            LlvmVoidType,
        ) {
            body {
                for ((global, initializer) in globalVariableInitializers) {
                    (this as BasicBlockBuilder<EmergeLlvmContext, LlvmType>)
                    val initResult = emitExpressionCode(initializer)
                    if (initResult is ExpressionResult.Value) {
                        global.emitWrite!!(initResult.value)
                    } else {
                        check(initResult is ExpressionResult.Terminated)
                        return@body initResult.termination
                    }
                }
                retVoid()
            }
        }

        // each intrinsic can introduce new ones that it references, loop until all are known
        val defined: MutableSet<KotlinLlvmFunction<*, *>> = Collections.newSetFromMap(IdentityHashMap())
        while (true) {
            val allInstrinsics = kotlinLlvmFunctions.entries.toList()
            var anyNewDefined = false
            for (intrinsic in allInstrinsics) {
                if (intrinsic.key in defined) {
                    continue
                }
                intrinsic.value.defineBody()
                defined.add(intrinsic.key)
                anyNewDefined = true
            }
            if (!anyNewDefined) {
                break
            }
        }

        super.complete()
    }

    /**
     * @return the [LlvmType] of the given emerge type, for use in the reference location. This is
     * [LlvmPointerType] for all structural/heap-allocated types, and an LLVM value type for the emerge value types.
     */
    fun getReferenceSiteType(type: IrType, forceBoxed: Boolean = false): LlvmType {
        if (type is IrParameterizedType && type.simpleType.baseType.canonicalName.toString() == "emerge.ffi.c.CPointer") {
            return LlvmPointerType(getReferenceSiteType(type.arguments.values.single().type))
        }

        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getReferenceSiteType(type.effectiveBound)
        }

        baseType.autoboxer?.let { return it.getReferenceSiteType(this, forceBoxed) }

        return pointerTo(getAllocationSiteType(type))
    }

    fun getAllocationSiteType(type: IrType): LlvmType {
        type.autoboxer?.let { return it.unboxedType }
        when (type) {
            is IrGenericTypeReference -> return getAllocationSiteType(type.effectiveBound)
            is IrParameterizedType -> when (type.simpleType.baseType.canonicalName.toString()) {
                "emerge.core.Array" -> {
                    val component = type.arguments.values.single()
                    if (component.variance == IrTypeVariance.IN || component.type !is IrSimpleType) {
                        return EmergeArrayBaseType
                    }

                    return when ((component.type as IrSimpleType).baseType.canonicalName.toString()) {
                        "emerge.core.S8" -> EmergeS8ArrayType
                        "emerge.core.U8" -> EmergeU8ArrayType
                        "emerge.core.S16" -> EmergeS16ArrayType
                        "emerge.core.U16" -> EmergeU16ArrayType
                        "emerge.core.S32" -> EmergeS32ArrayType
                        "emerge.core.U32" -> EmergeU32ArrayType
                        "emerge.core.S64" -> EmergeS64ArrayType
                        "emerge.core.U64" -> EmergeU64ArrayType
                        "emerge.core.SWord" -> EmergeSWordArrayType
                        "emerge.core.UWord" -> EmergeUWordArrayType
                        "emerge.core.Bool" -> EmergeBooleanArrayType
                        "emerge.core.Any" -> EmergeArrayBaseType
                        else -> EmergeReferenceArrayType
                    }
                }

                "emerge.ffi.c.CPointer" -> {
                    val componentType = getAllocationSiteType(type.arguments.values.single().type)
                    return LlvmPointerType(componentType)
                }

                "emerge.ffi.c.CValue" -> {
                    // TODO: any logic needed?
                    val componentType = type.arguments.values.single()
                    return getAllocationSiteType(componentType.type)
                }

                else -> return getAllocationSiteType(type.simpleType)
            }
            is IrSimpleType -> {
                return when(type.baseType) {
                    is IrIntrinsicType -> when (type.baseType.canonicalName.toString()) {
                        "emerge.core.Any",
                        "emerge.core.Unit",
                        "emerge.core.Nothing" -> EmergeHeapAllocatedValueBaseType
                        else -> throw CodeGenerationException("Missing allocation-site representation for this intrinsic type: $type")
                    }
                    is IrInterface -> EmergeHeapAllocatedValueBaseType
                    else -> (type.baseType as IrClass).llvmType
                }

                // there are no other possibilities AFAICT right now
            }
        }
    }

    private fun getInstrinsic(fn: IrFunction): LlvmFunction<*>? {
        var intrinsic: LlvmFunction<*>? = null
        if (fn is IrBaseTypeFunction) {
            val autoboxer = fn.declaredOn.autoboxer
            if (autoboxer is Autoboxer.UserFacingBoxed) {
                if (fn.canonicalName.simpleName == "\$constructor") {
                    intrinsic = autoboxer.getConstructorIntrinsic(this, fn.canonicalName)
                }
                if (fn.canonicalName.simpleName == "\$destructor") {
                    intrinsic = autoboxer.getDestructorIntrinsic(this)
                }
            }
        }

        if (intrinsic == null) {
            intrinsic = intrinsicFunctions[fn.canonicalName.toString()]?.let { this.registerIntrinsic(it) }
            // TODO: different intrinsic per overload
        }

        return intrinsic
    }

    companion object {
        fun createDoAndDispose(target: LlvmTarget, action: (EmergeLlvmContext) -> Unit) {
            return EmergeLlvmContext(target).use(action)
        }
    }
}

/**
 * Allocates [nBytes] bytes on the heap, triggering an OOM exception if [EmergeLlvmContext.allocateFunction] returns `null`.
 */
internal fun BasicBlockBuilder<EmergeLlvmContext, *>.heapAllocate(nBytes: LlvmValue<EmergeWordType>): LlvmValue<LlvmPointerType<LlvmVoidType>> {
    val allocationPointer = call(context.allocateFunction, listOf(nBytes))
    // TODO: check allocation pointer == null, OOM
    return allocationPointer
}

/**
 * Allocates [T].[sizeof] bytes on the heap, triggering an OOM exception if needed
 */
fun <T : LlvmType> BasicBlockBuilder<EmergeLlvmContext, *>.heapAllocate(type: T): LlvmValue<LlvmPointerType<T>> {
    val size = type.sizeof()
    return heapAllocate(size).reinterpretAs(pointerTo(type))
}

private val intrinsicFunctions: Map<String, KotlinLlvmFunction<in EmergeLlvmContext, *>> by lazy {
    listOf(
        arrayAddressOfFirst,
        arraySize,
        arrayAbstractGet,
        arrayAbstractSet,
    )
        .associateBy { it.name }
}

private val IrFunction.isDestructorOnValueOrBoxType: Boolean get() {
    return this is IrMemberFunction
        && this.canonicalName.simpleName == "\$destructor"
        && this.declaredOn.autoboxer != null
}

private val IrFunction.isUserFacingBoxDestructor: Boolean get() {
    return this is IrMemberFunction
        && this.canonicalName.simpleName == "\$destructor"
        && this.declaredOn.autoboxer is Autoboxer.UserFacingBoxed
}