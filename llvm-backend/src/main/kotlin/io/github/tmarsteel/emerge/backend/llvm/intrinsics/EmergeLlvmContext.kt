package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
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
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.rawLlvmRef
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.global.LLVM

class EmergeLlvmContext(val base: LlvmContext) : LlvmContext by base {
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

        struct.constructors.overloads.forEach(this::registerFunction)
    }

    fun registerFunction(fn: IrFunction) {
        if (fn.llvmRef != null) {
            return
        }

        val functionType = LLVM.LLVMFunctionType(
            getReferenceSiteType(fn.returnType).getRawInContext(this),
            PointerPointer(*fn.parameters.map { getReferenceSiteType(it.type).getRawInContext(this) }.toTypedArray()),
            fn.parameters.size,
            0,
        )
        val rawRef = LLVM.LLVMAddFunction(module, fn.llvmName, functionType)
        fn.llvmRef = LlvmFunction(
            LlvmValue(rawRef, LlvmFunctionAddressType),
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
        }
    }

    fun registerGlobal(global: IrVariableDeclaration) {
        val allocationSiteType = getAllocationSiteType(global.type).getRawInContext(this)
        val rawRef = LLVM.LLVMAddGlobal(
            module,
            allocationSiteType,
            globalsScope.next()
        )
        val allocation = LlvmValue(
            rawRef,
            pointerTo(getReferenceSiteType(global.type)),
        )
        global.emitRead = {
            allocation.dereference()
        }
        global.emitWrite = { newValue ->
            store(newValue, allocation)
        }
        LLVM.LLVMSetInitializer(rawRef, LLVM.LLVMGetUndef(allocationSiteType))
    }

    fun defineFunctionBody(fn: IrImplementedFunction) {
        val llvmFunction = fn.llvmRef ?: throw CodeGenerationException("You must register the functions through ${this::registerFunction.name} first to handle cyclic references (especially important for recursion)")
        if (fn.bodyDefined) {
            throw CodeGenerationException("Cannot define body for function ${fn.fqn} multiple times!")
        }

        println("Emitting code for ${fn.fqn}")
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
        val writeEmitter = global.emitWrite
            ?: throw CodeGenerationException("Global not registered through ${this::registerGlobal.name} first")

        globalVariableInitializers.add(Pair(global, initializer))
    }

    private var completed = false
    override fun complete() {
        if (completed) {
            return
        }

        val initializeGlobalsFn = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
            "initialize_global_variables",
            LlvmVoidType,
        ) {
            body {
                globalVariableInitializers.forEach {
                    it.first.emitWrite!!(emitExpressionCode(it.second))
                }
                retVoid()
            }
        }

        addModuleInitFunction(initializeGlobalsFn.addTo(this))
        base.complete()
    }

    /**
     * @return the [LlvmType] of the given emerge type, for use in the reference location. This is
     * [LlvmPointerType] for all structural/heap-allocated types, and an LLVM value type for the emerge value types.
     */
    fun getReferenceSiteType(type: IrType): LlvmType {
        if (type is IrParameterizedType && type.simpleType.baseType.fqn.toString() == "emerge.ffi.c.CPointer") {
            return LlvmPointerType(getReferenceSiteType(type.arguments["T"]!!.type))
        }

        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getReferenceSiteType(type.effectiveBound)
        }

        when (baseType.fqn.toString()) {
            "emerge.ffi.c.COpaquePointer",
            "emerge.ffi.c.CPointer" -> return opaquePointer
            "emerge.core.Int" -> return LlvmI32Type
            "emerge.core.Array" -> return opaquePointer
            "emerge.core.iword",
            "emerge.core.uword" -> return LlvmWordType
            "emerge.core.Unit" -> return LlvmVoidType
            "emerge.core.Any" -> return PointerToAnyValue // TODO: remove, Any will be a pure language-defined type
        }

        return pointerTo(getAllocationSiteType(type))
    }

    fun getAllocationSiteType(type: IrType): LlvmType {
        if (type is IrParameterizedType && type.simpleType.baseType.fqn.toString() == "emerge.core.Array") {
            val component = type.arguments["Item"]!!
            if (component.variance == IrTypeVariance.IN || component.type !is IrSimpleType) {
                TODO("this is a reference type, return reference array type")
            }

            when ((component.type as IrSimpleType).baseType.fqn.toString()) {
                "emerge.core.Byte" -> return ValueArrayType.i8s
                else -> TODO("other intrinsic types??")
            }
        }

        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getAllocationSiteType(type.effectiveBound)
        }

        when (baseType.fqn.toString()) {
            "emerge.ffi.c.COpaquePointer",
            "emerge.ffi.c.CPointer" -> return opaquePointer
            "emerge.core.Int" -> return LlvmI32Type
            "emerge.core.iword",
            "emerge.core.uword" -> return LlvmWordType
        }

        if (baseType is IrStruct) {
            return baseType.llvmType!!
        }

        throw CodeGenerationException("Cannot determine LLVM type for allocation of $baseType")
    }

    companion object {
        fun createDoAndDispose(targetTriple: String, action: (EmergeLlvmContext) -> Unit) {
            return LlvmContext.createDoAndDispose(targetTriple) {
                action(EmergeLlvmContext(it))
            }
        }
    }
}