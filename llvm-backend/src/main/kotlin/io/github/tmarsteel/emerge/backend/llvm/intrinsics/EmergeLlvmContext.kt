package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrDeclaredFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrIntrinsicType
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
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
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.isUnit
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.llvmValueType
import io.github.tmarsteel.emerge.backend.llvm.rawLlvmRef
import org.bytedeco.llvm.global.LLVM
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
    /** `emerge.platform.BooleanBox` */
    internal lateinit var boxTypeBoolean: EmergeClassType

    /** `emerge.core.Unit` */
    internal lateinit var unitType: EmergeClassType
    internal lateinit var pointerToPointerToUnitInstance: LlvmGlobal<LlvmPointerType<EmergeClassType>>

    private val emergeStructs = ArrayList<EmergeClassType>()
    private val kotlinLlvmFunctions: MutableMap<KotlinLlvmFunction<in EmergeLlvmContext, *>, KotlinLlvmFunction.DeclaredInContext<in EmergeLlvmContext, *>> = IdentityHashMap()

    fun registerStruct(struct: IrClass) {
        if (struct.rawLlvmRef != null) {
            return
        }

        val structType = LLVM.LLVMStructCreateNamed(ref, struct.llvmName)
        // register here to allow cyclic references
        struct.rawLlvmRef = structType
        val emergeClassType = EmergeClassType.fromLlvmStructWithoutBody(
            this,
            structType,
            struct,
        )
        struct.llvmType = emergeClassType

        when (struct.fqn.toString()) {
            "emerge.ffi.c.CPointer" -> {
                struct.memberVariables.single { it.name == "pointed" }.isCPointerPointed = true
            }
            "emerge.platform.I8Box" -> boxTypeS8 = emergeClassType
            "emerge.platform.U8Box" -> boxTypeU8 = emergeClassType
            "emerge.platform.S16Box" -> boxTypeS16 = emergeClassType
            "emerge.platform.U16Box" -> boxTypeU16 = emergeClassType
            "emerge.platform.S32Box" -> boxTypeS32 = emergeClassType
            "emerge.platform.U32Box" -> boxTypeU32 = emergeClassType
            "emerge.platform.S64Box" -> boxTypeS64 = emergeClassType
            "emerge.platform.U64Box" -> boxTypeU64 = emergeClassType
            "emerge.platform.SWordBox" -> boxTypeSWord = emergeClassType
            "emerge.platform.UWordBox" -> boxTypeUWord = emergeClassType
            "emerge.core.Unit" -> {
                unitType = emergeClassType
                pointerToPointerToUnitInstance = addGlobal(undefValue(pointerTo(emergeClassType)), LlvmGlobal.ThreadLocalMode.SHARED)
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
    fun registerFunction(fn: IrFunction, returnTypeOverride: LlvmType? = null): LlvmFunction<*> {
        fn.llvmRef?.let { return it }

        val parameterTypes = fn.parameters.map { getReferenceSiteType(it.type) }

        if (fn is IrDeclaredFunction) {
            intrinsicFunctions[fn.fqn.toString()]?.let { intrinsic ->
                // TODO: different intrinsic per overload
                val intrinsicImpl = registerIntrinsic(intrinsic)
                check(parameterTypes.size == intrinsicImpl.type.parameterTypes.size)
                intrinsicImpl.type.parameterTypes.forEachIndexed { paramIndex, intrinsicType ->
                    val declaredType = parameterTypes[paramIndex]
                    check(intrinsicType == declaredType) { "${fn.fqn} param #$paramIndex; intrinsic $intrinsicType, declared $declaredType" }
                }
                fn.llvmRef = intrinsicImpl
                return intrinsicImpl
            }
        }

        val returnLlvmType = returnTypeOverride ?: if (fn.returnType.isUnit) LlvmVoidType else getReferenceSiteType(fn.returnType)
        val functionType = LlvmFunctionType(
            returnLlvmType,
            parameterTypes,
        )
        val rawRef = LLVM.LLVMAddFunction(module, fn.llvmName, functionType.getRawInContext(this))
        fn.llvmRef = LlvmFunction(
            LlvmConstant(rawRef, LlvmFunctionAddressType),
            functionType,
        )

        fn.parameters.forEachIndexed { index, param ->
            param.emitRead = {
                LlvmValue(LLVM.LLVMGetParam(rawRef, index), getReferenceSiteType(param.type))
            }
            param.emitWrite = {
                throw CodeGenerationException("Writing to function parameters is forbidden.")
            }
        }

        if (fn.fqn.last == "main") {
            if (this::mainFunction.isInitialized) {
                throw CodeGenerationException("Found multiple main functions!")
            }
            if (fn.parameters.isNotEmpty()) {
                throw CodeGenerationException("Main function must not declare parameters")
            }
            if (!fn.returnType.isUnit) {
                throw CodeGenerationException("Main function ${fn.fqn} must return Unit")
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
                LLVM.LLVMGetUndef(globalType.getRawInContext(this)),
                globalType,
            ),
            LlvmGlobal.ThreadLocalMode.LOCAL_DYNAMIC,
        )
        global.emitRead = {
            allocation.dereference()
        }
        global.emitWrite = { newValue ->
            store(newValue, allocation)
        }
    }

    private var structConstructorsRegistered: Boolean = false
    fun defineFunctionBody(fn: IrImplementedFunction) {
        val llvmFunction = fn.llvmRef ?: throw CodeGenerationException("You must register the functions through ${this::registerFunction.name} first to handle cyclic references (especially important for recursion)")
        if (fn.bodyDefined) {
            throw CodeGenerationException("Cannot define body for function ${fn.fqn} multiple times!")
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
            }
        }

        BasicBlockBuilder.fillBody(this, llvmFunction) {
            for (param in fn.parameters) {
                param.emitRead!!().afterReferenceCreated(param.type)
                defer {
                    param.emitRead!!().afterReferenceDropped(param.type)
                }
            }

            when (val codeResult = emitCode(fn.body)) {
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
    fun getReferenceSiteType(type: IrType): LlvmType {
        if (type is IrParameterizedType && type.simpleType.baseType.fqn.toString() == "emerge.ffi.c.CPointer") {
            return LlvmPointerType(getReferenceSiteType(type.arguments.values.single().type))
        }

        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getReferenceSiteType(type.effectiveBound)
        }

        type.llvmValueType?.let { return it }
        return pointerTo(getAllocationSiteType(type))
    }

    fun getAllocationSiteType(type: IrType): LlvmType {
        when (type) {
            is IrGenericTypeReference -> return getAllocationSiteType(type.effectiveBound)
            is IrParameterizedType -> when (type.simpleType.baseType.fqn.toString()) {
                "emerge.core.Array" -> {
                    val component = type.arguments.values.single()
                    if (component.variance == IrTypeVariance.IN || component.type !is IrSimpleType) {
                        return EmergeArrayBaseType
                    }

                    return when ((component.type as IrSimpleType).baseType.fqn.toString()) {
                        "emerge.core.Byte" -> EmergeS8ArrayType
                        "emerge.core.UByte" -> EmergeU8ArrayType
                        "emerge.core.Short" -> EmergeS16ArrayType
                        "emerge.core.UShort" -> EmergeU16ArrayType
                        "emerge.core.Int" -> EmergeS32ArrayType
                        "emerge.core.UInt" -> EmergeU32ArrayType
                        "emerge.core.Long" -> EmergeS64ArrayType
                        "emerge.core.ULong" -> EmergeU64ArrayType
                        "emerge.core.iword" -> EmergeSWordArrayType
                        "emerge.core.uword" -> EmergeUWordArrayType
                        "emerge.core.Boolean" -> EmergeBooleanArrayType
                        "emerge.core.Any" -> EmergeArrayBaseType
                        "emerge.core.Number" -> EmergeArrayBaseType
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
            }
            is IrSimpleType -> {
                type.llvmValueType?.let { return it }
                if (type.baseType is IrIntrinsicType) {
                    return when (type.baseType.fqn.toString()) {
                        "emerge.core.Any",
                        "emerge.core.Unit",
                        "emerge.core.Nothing" -> EmergeHeapAllocatedValueBaseType
                        else -> throw CodeGenerationException("Missing allocation-site representation for this intrinsic type: $type")
                    }
                }

                // there are no other possibilities AFAICT right now
                return (type.baseType as IrClass).llvmType
            }
        }
        throw CodeGenerationException("Failed to determine allocation-site type for $type")
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

private val intrinsicFunctions: Map<String, KotlinLlvmFunction<in EmergeLlvmContext, *>> = listOf(
    arrayAddressOfFirst,
    arraySize,
)
    .associateBy { it.name }