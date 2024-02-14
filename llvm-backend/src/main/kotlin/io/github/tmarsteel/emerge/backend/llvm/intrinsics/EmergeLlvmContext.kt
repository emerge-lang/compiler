package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrDeclaredFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrIntrinsicType
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.llvm.bodyDefined
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitCode
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitExpressionCode
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitRead
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitWrite
import io.github.tmarsteel.emerge.backend.llvm.codegen.typeForAllocationSite
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmTarget
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.llvmValueType
import io.github.tmarsteel.emerge.backend.llvm.rawLlvmRef
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.global.LLVM

class EmergeLlvmContext(
    target: LlvmTarget
) : LlvmContext(target) {
    /**
     * The function that allocates heap memory. Semantically equivalent to libcs
     * `void* malloc(size_t size)`.
     * Must be set by the backend class after [registerFunction]
     */
    lateinit var allocateFunction: LlvmFunction<LlvmPointerType<LlvmVoidType>>

    /**
     * The function the deallocates heap memory. Semantically equivalent to libcs
     * `void free(void* memory)`
     * Must be set by the backend class after [registerFunction]
     */
    lateinit var freeFunction: LlvmFunction<LlvmVoidType>

    /**
     * The function that exits the process. Semantically equivalent to libcs
     * `void exit(int status)`
     * Must be set by the backend class after [registerFunction]
     */
    lateinit var exitFunction: LlvmFunction<LlvmVoidType>

    /**
     * The main function of the program. `fun main() -> Unit`
     * Set by [registerFunction].
     */
    lateinit var mainFunction: LlvmFunction<LlvmVoidType>

    fun registerStruct(struct: IrStruct) {
        if (struct.rawLlvmRef != null) {
            return
        }

        val structType = LLVM.LLVMStructCreateNamed(ref, struct.llvmName)
        // register here to allow cyclic references
        struct.rawLlvmRef = structType
        struct.llvmType = EmergeStructType.fromLlvmStructWithoutBody(
            this,
            structType,
            struct,
        )

        if (struct.fqn.toString() == "emerge.ffi.c.CPointer") {
            struct.members.single { it.name == "pointed" }.isCPointerPointed = true
        }

        // constructors need not be registered as of now. There only is the default
        // constructor, and it finds its way into the context by being invoked
        // and added through KotlinLlvmFunction.getInContext
    }

    fun registerFunction(fn: IrFunction): LlvmFunction<*> {
        fn.llvmRef?.let { return it }

        val parameterTypes = fn.parameters.map { getReferenceSiteType(it.type) }

        if (fn is IrDeclaredFunction) {
            intrinsicFunctions[fn.fqn.toString()]?.let { intrinsic ->
                // TODO: different intrinsic per overload
                val intrinsicImpl = intrinsic.getInContext(this@EmergeLlvmContext)
                check(parameterTypes.size == intrinsicImpl.parameterTypes.size)
                intrinsicImpl.parameterTypes.forEachIndexed { paramIndex, intrinsicType ->
                    val declaredType = parameterTypes[paramIndex]
                    check(intrinsicType == declaredType) { "param #$paramIndex; intrinsic $intrinsicType, declared $declaredType" }
                }
                fn.llvmRef = intrinsicImpl
                return intrinsicImpl
            }
        }

        val functionType = LLVM.LLVMFunctionType(
            getReferenceSiteType(fn.returnType).getRawInContext(this),
            PointerPointer(*parameterTypes.map{ it.getRawInContext(this) }.toTypedArray()),
            fn.parameters.size,
            0,
        )
        val rawRef = LLVM.LLVMAddFunction(module, fn.llvmName, functionType)
        fn.llvmRef = LlvmFunction(
            LlvmConstant(rawRef, LlvmFunctionAddressType),
            functionType,
            getReferenceSiteType(fn.returnType),
            fn.parameters.map { getReferenceSiteType(it.type) }
        )

        fn.parameters.forEachIndexed { index, param ->
            param.emitRead = {
                LlvmValue(LLVM.LLVMGetParam(rawRef, index), getReferenceSiteType(param.type))
            }
            param.emitWrite = {
                throw CodeGenerationException("Writing to function parameters is forbidden.")
            }
            param.typeForAllocationSite = getAllocationSiteType(param.type)
        }

        if (fn.fqn.last == "main") {
            if (this::mainFunction.isInitialized) {
                throw CodeGenerationException("Found multiple main functions!")
            }
            if (fn.parameters.isNotEmpty()) {
                throw CodeGenerationException("Main function must not declare parameters")
            }
            if (getReferenceSiteType(fn.returnType) != LlvmVoidType) {
                throw CodeGenerationException("Main function ${fn.fqn} must return Unit")
            }

            @Suppress("UNCHECKED_CAST")
            this.mainFunction = fn.llvmRef as LlvmFunction<LlvmVoidType>
        }

        return fn.llvmRef!!
    }

    fun registerGlobal(global: IrVariableDeclaration) {
        val allocationSiteType = getAllocationSiteType(global.type)
        val allocation = addGlobal(
            LlvmConstant(
                LLVM.LLVMGetUndef(allocationSiteType.getRawInContext(this)),
                allocationSiteType,
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

    fun defineFunctionBody(fn: IrImplementedFunction) {
        val llvmFunction = fn.llvmRef ?: throw CodeGenerationException("You must register the functions through ${this::registerFunction.name} first to handle cyclic references (especially important for recursion)")
        if (fn.bodyDefined) {
            throw CodeGenerationException("Cannot define body for function ${fn.fqn} multiple times!")
        }

        val entryBlock = LLVM.LLVMAppendBasicBlockInContext(ref, llvmFunction.address.raw, "entry")
        BasicBlockBuilder.fill(this, entryBlock) {
            emitCode(fn.body)
                ?: run {
                    // TODO: this happens when the frontend doesn't give a return instruction when it should.
                    // this currently on implicit Unit returns. Workaround until all the infrastructure for object Unit {}
                    // is in place
                    (this as BasicBlockBuilder<*, LlvmVoidType>).retVoid()
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
                globalVariableInitializers.forEach {
                    it.first.emitWrite!!(emitExpressionCode(it.second))
                }
                retVoid()
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
        when (baseType.fqn.toString()) {
            "emerge.ffi.c.CPointer" -> return pointerTo(getAllocationSiteType(type))
            "emerge.core.Unit",
            "emerge.core.Nothing" -> return LlvmVoidType
            "emerge.core.Any" -> return PointerToAnyValue // TODO: remove, Any will be a pure language-defined type
        }

        return pointerTo(getAllocationSiteType(type))
    }

    fun getAllocationSiteType(type: IrType): LlvmType {
        when (type) {
            is IrGenericTypeReference -> return getAllocationSiteType(type.effectiveBound)
            is IrParameterizedType -> when (type.simpleType.baseType.fqn.toString()) {
                "emerge.core.Array" -> {
                    val component = type.arguments.values.single()
                    if (component.variance == IrTypeVariance.IN || component.type !is IrSimpleType) {
                        return EmergeReferenceArrayType
                    }

                    when ((component.type as IrSimpleType).baseType.fqn.toString()) {
                        "emerge.core.Byte" -> return ValueArrayI8Type
                        "emerge.core.Any" -> return EmergeReferenceArrayType
                        else -> TODO("other intrinsic types??")
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
                        "emerge.core.Any" -> AnyValueType
                        "emerge.core.Nothing" -> LlvmVoidType
                        else -> throw CodeGenerationException("Missing allocation-site representation for this intrinsic type: $type")
                    }
                }

                // there are no other possibilities AFAICT right now
                return (type.baseType as IrStruct).llvmType
                    ?: throw CodeGenerationException("Encountered Emerge struct type ${type.baseType.fqn} that wasn't registered through ${EmergeLlvmContext::registerStruct.name}")
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

fun <T : LlvmType> BasicBlockBuilder<EmergeLlvmContext, *>.heapAllocate(type: T): LlvmValue<LlvmPointerType<T>> {
    val size = type.sizeof()
    val voidPtr = call(context.allocateFunction, listOf(size))
    return LlvmValue(voidPtr.raw, pointerTo(type))
}

private val intrinsicFunctions: Map<String, KotlinLlvmFunction<EmergeLlvmContext, *>> = listOf(
    arrayIndexOfFirst,
    arraySize,
)
    .associateBy { it.name }