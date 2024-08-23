package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrFullyInheritedMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrGlobalVariable
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrIntrinsicType
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceFile
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer
import io.github.tmarsteel.emerge.backend.llvm.IrSimpleTypeImpl
import io.github.tmarsteel.emerge.backend.llvm.associateByErrorOnDuplicate
import io.github.tmarsteel.emerge.backend.llvm.autoboxer
import io.github.tmarsteel.emerge.backend.llvm.bodyDefined
import io.github.tmarsteel.emerge.backend.llvm.codegen.ExecutableResult
import io.github.tmarsteel.emerge.backend.llvm.codegen.ExpressionResult
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitCode
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitExpressionCode
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitRead
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitWrite
import io.github.tmarsteel.emerge.backend.llvm.codegen.findSimpleTypeBound
import io.github.tmarsteel.emerge.backend.llvm.codegen.sizeof
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.DiBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmTarget
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.hasNothrowAbi
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.retFallibleVoid
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.exceptions.unwindContextSize
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.exceptions.unwindCursorSize
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.addressOfBuiltin
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.anyReflect
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.intrinsicNumberOperations
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.isNullBuiltin
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.pureWrite
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.reflectionBaseTypeIsSameObjectAs
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib.safemathFns
import io.github.tmarsteel.emerge.backend.llvm.isNothing
import io.github.tmarsteel.emerge.backend.llvm.isUnit
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmModuleFlagBehavior
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.llvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.rawLlvmRef
import io.github.tmarsteel.emerge.common.CanonicalElementName
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
    internal lateinit var mainFunction: LlvmFunction<*>

    /**
     * `emerge.platform.printStackTraceToStandardError()`, set by [registerFunction]
     */
    internal lateinit var printStackTraceToStdErrFunction: LlvmFunction<*>

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
    /** `emerge.platform.F32Box` */
    internal lateinit var boxTypeF32: EmergeClassType
    /** `emerge.platform.F64Box` */
    internal lateinit var boxTypeF64: EmergeClassType
    /** `emerge.platform.SWordBox` */
    internal lateinit var boxTypeSWord: EmergeClassType
    /** `emerge.platform.UWordBox` */
    internal lateinit var boxTypeUWord: EmergeClassType
    /** `emerge.platform.BoolBox` */
    internal lateinit var boxTypeBool: EmergeClassType
    /** `emerge.platform.ReflectionBaseTypeBox */
    internal lateinit var boxTypeReflectionBaseType: EmergeClassType
    /** `emerge.ffi.c.CPointer */
    internal lateinit var cPointerType: EmergeClassType
    /** `emerge.ffi.c.COpaquePointer` */
    internal lateinit var cOpaquePointerType: EmergeClassType
    /** `emerge.core.String */
    internal lateinit var stringType: EmergeClassType
    /** `emerge.core.ArrayIndexOutOfBoundsError` */
    internal lateinit var arrayIndexOutOfBoundsErrorType: EmergeClassType

    /** `emerge.core.S8 */
    internal lateinit var rawS8Clazz: IrClass
    /** `emerge.core.U8 */
    internal lateinit var rawU8Clazz: IrClass
    /** `emerge.core.S16 */
    internal lateinit var rawS16Clazz: IrClass
    /** `emerge.core.U16 */
    internal lateinit var rawU16Clazz: IrClass
    /** `emerge.core.S32 */
    internal lateinit var rawS32Clazz: IrClass
    /** `emerge.core.U32 */
    internal lateinit var rawU32Clazz: IrClass
    /** `emerge.core.64 */
    internal lateinit var rawS64Clazz: IrClass
    /** `emerge.core.U64*/
    internal lateinit var rawU64Clazz: IrClass
    /** `emerge.core.F32*/
    internal lateinit var rawF32Clazz: IrClass
    /** `emerge.core.F64*/
    internal lateinit var rawF64Clazz: IrClass
    /** `emerge.core.SWord */
    internal lateinit var rawSWordClazz: IrClass
    /** `emerge.core.UWord */
    internal lateinit var rawUWordClazz: IrClass
    /** `emerge.core.Bool */
    internal lateinit var rawBoolClazz: IrClass
    /** `emerge.core.reflection.ReflectionBaseType` */
    internal lateinit var rawReflectionBaseTypeClazz: IrClass
    /** `emerge.core.Throwable` */
    internal lateinit var throwableClazz: IrInterface
    /** `emerge.core.ArithmeticError` */
    internal lateinit var arithmeticErrorClazz: IrClass

    /** `emerge.core.Unit` */
    internal lateinit var unitType: EmergeClassType
    internal lateinit var pointerToUnitInstance: LlvmGlobal<EmergeClassType>
    /** `emerge.platform.StandardError` */
    internal lateinit var standardErrorStreamGlobalVar: IrGlobalVariable

    private val emergeStructs = ArrayList<EmergeClassType>()
    private val kotlinLlvmFunctions: MutableMap<KotlinLlvmFunction<in EmergeLlvmContext, *>, KotlinLlvmFunction.DeclaredInContext<in EmergeLlvmContext, *>> = IdentityHashMap()

    private var diBuilderCache = IdentityHashMap<IrSourceFile, DiBuilder>()
    private val IrSourceFile.diBuilder: DiBuilder get() {
        return diBuilderCache.computeIfAbsent(this) { location ->
            DiBuilder(module, location.path)
        }
    }
    
    fun registerBaseType(type: IrBaseType) {
        when (type) {
            is IrInterface -> {
                when (type.canonicalName.toString()) {
                    "emerge.core.Throwable" -> throwableClazz = type
                }
            }
            is IrClass -> registerClass(type)
        }
    }
    
    private fun registerClass(clazz: IrClass) {
        if (clazz.rawLlvmRef != null) {
            return
        }

        when (clazz.canonicalName.toString()) {
            "emerge.core.S8" -> rawS8Clazz = clazz
            "emerge.core.U8" -> rawU8Clazz = clazz
            "emerge.core.S16" -> rawS16Clazz = clazz
            "emerge.core.U16" -> rawU16Clazz = clazz
            "emerge.core.S32" -> rawS32Clazz = clazz
            "emerge.core.U32" -> rawU32Clazz = clazz
            "emerge.core.S64" -> rawS64Clazz = clazz
            "emerge.core.U64" -> rawU64Clazz = clazz
            "emerge.core.F32" -> rawF32Clazz = clazz
            "emerge.core.F64" -> rawF64Clazz = clazz
            "emerge.core.SWord" -> rawSWordClazz = clazz
            "emerge.core.UWord" -> rawUWordClazz = clazz
            "emerge.core.Bool" -> rawBoolClazz = clazz
            "emerge.core.ArithmeticError" -> arithmeticErrorClazz = clazz
            "emerge.core.reflection.ReflectionBaseType" -> rawReflectionBaseTypeClazz = clazz
        }

        if (clazz.autoboxer is Autoboxer.PrimitiveType) {
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
            "emerge.platform.F32Box" -> boxTypeF32 = emergeClassType
            "emerge.platform.F64Box" -> boxTypeF64 = emergeClassType
            "emerge.platform.SWordBox" -> boxTypeSWord = emergeClassType
            "emerge.platform.UWordBox" -> boxTypeUWord = emergeClassType
            "emerge.platform.BoolBox" -> boxTypeBool = emergeClassType
            "emerge.platform.ReflectionBaseTypeBox" -> boxTypeReflectionBaseType = emergeClassType
            "emerge.ffi.c.CPointer" -> cPointerType = emergeClassType
            "emerge.ffi.c.COpaquePointer" -> cOpaquePointerType = emergeClassType
            "emerge.core.String" -> stringType = emergeClassType
            "emerge.core.ArrayIndexOutOfBoundsError" -> arrayIndexOutOfBoundsErrorType = emergeClassType
            "emerge.core.Unit" -> {
                unitType = emergeClassType
                pointerToUnitInstance = addGlobal(undefValue(emergeClassType), LlvmThreadLocalMode.NOT_THREAD_LOCAL, "unit_instance")
            }
        }

        emergeStructs.add(emergeClassType)
    }

    fun defineClassStructure(clazz: IrClass) {
        clazz.llvmType.assureLlvmStructMembersDefined()
    }

    private val emergeClassesByIrTypeCache: MutableMap<CanonicalElementName.BaseType, EmergeClassType> = MapMaker().weakValues().makeMap()
    internal fun getEmergeClassByIrType(irType: IrBaseType): EmergeClassType? {
        emergeClassesByIrTypeCache[irType.canonicalName]?.let { return it }
        val instance = emergeStructs.find { it.irClass.canonicalName == irType.canonicalName }
        if (instance != null) {
            emergeClassesByIrTypeCache[irType.canonicalName] = instance
        }
        return instance
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
    fun registerFunction(
        fn: IrFunction,
        returnTypeOverride: LlvmType? = null,
        symbolNameOverride: String? = null
    ): LlvmFunction<*>? {
        fn.llvmRef?.let { return it }

        if (fn is IrFullyInheritedMemberFunction) {
            check(returnTypeOverride == null) {
                "cannot override return type on fully inherited function ${fn.canonicalName}"
            }
            check(symbolNameOverride == null) {
                "cannot override symbol name on fully inherited function ${fn.canonicalName}"
            }
            val llvmFn = registerFunction(fn.superFunction, null, null)
            llvmFn?.let { fn.llvmRef = it }
            return llvmFn
        }

        val llvmParameterTypes = fn.parameters.map { getReferenceSiteType(it.type) }
        val coreReturnValueLlvmType = returnTypeOverride ?: when {
            fn.returnType.isUnit -> LlvmVoidType
            !fn.returnType.isNullable && (fn.returnType as? IrSimpleType)?.baseType?.isNothing == true -> LlvmVoidType
            else  -> getReferenceSiteType(fn.returnType)
        }
        val returnLlvmType = if (fn.hasNothrowAbi) coreReturnValueLlvmType else EmergeFallibleCallResult(coreReturnValueLlvmType)

        getInstrinsic(fn)?.let { intrinsic ->
            assert(llvmParameterTypes.size == intrinsic.type.parameterTypes.size)
            intrinsic.type.parameterTypes.forEachIndexed { paramIndex, intrinsicType ->
                val declaredType = llvmParameterTypes[paramIndex]
                assert(declaredType.isAssignableTo(intrinsicType)) { "${fn.canonicalName} param #$paramIndex; intrinsic $intrinsicType, declared $declaredType" }
            }
            assert(intrinsic.type.returnType.isAssignableTo(returnLlvmType))

            fn.llvmRef = intrinsic
            fn.llvmName = intrinsic.name
            if (fn is IrMemberFunction) {
                fn.llvmFunctionType = intrinsic.type
            }
            return intrinsic
        }

        val functionType = LlvmFunctionType(
            returnLlvmType,
            llvmParameterTypes,
        )
        if (fn is IrMemberFunction) {
            fn.llvmFunctionType = functionType
            if (fn.body == null) {
                // abstract member fn is not relevant to LLVM
                return null
            }
        }
        if (symbolNameOverride != null) {
            fn.llvmName = symbolNameOverride
        }
        val rawRef = Llvm.LLVMAddFunction(module, fn.llvmName, functionType.getRawInContext(this))
        fn.llvmRef = LlvmFunction(
            LlvmConstant(rawRef, LlvmFunctionAddressType),
            functionType,
        )
        fn.llvmRef!!.addAttributeToFunction(LlvmFunctionAttribute.FramePointerAll)
        fn.llvmRef!!.addAttributeToFunction(LlvmFunctionAttribute.UnwindTableAsync)
        fn.llvmRef!!.addAttributeToFunction(LlvmFunctionAttribute.NoUnwind) // emerge doesn't use unwinding as of now

        fn.parameters.zip(llvmParameterTypes).forEachIndexed { index, (param, llvmParamType) ->
            val paramLlvmRawValue = Llvm.LLVMGetParam(rawRef, index)
            LlvmValue.setName(paramLlvmRawValue, param.name)
            param.emitRead = {
                LlvmValue(paramLlvmRawValue, llvmParamType)
            }
            param.emitWrite = {
                throw CodeGenerationException("illegal IR - cannot write to function parameters")
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
            this.mainFunction = fn.llvmRef as LlvmFunction<*>
        }

        if (fn.canonicalName.parent.toString() == "emerge.platform") {
            if (fn.canonicalName.simpleName == "printStackTraceToStandardError" && fn.parameters.isEmpty()) {
                printStackTraceToStdErrFunction = fn.llvmRef!!
            }
        }

        return fn.llvmRef!!
    }

    private val globalVariables = ArrayList<IrGlobalVariable>()
    fun registerGlobal(global: IrGlobalVariable) {
        val globalType = getReferenceSiteType(global.declaration.type)
        val allocation = addGlobal(
            LlvmConstant(
                Llvm.LLVMGetUndef(globalType.getRawInContext(this)),
                globalType,
            ),
            LlvmThreadLocalMode.LOCAL_DYNAMIC,
            global.name.toString(),
        )
        global.declaration.emitRead = {
            allocation.dereference()
        }
        global.declaration.emitWrite = { newValue ->
            store(newValue, allocation)
        }
        globalVariables.add(global)

        if (global.name.toString() == "emerge.platform.StandardError") {
            standardErrorStreamGlobalVar = global
        }
    }

    private var structConstructorsRegistered: Boolean = false
    fun defineFunctionBody(fn: IrFunction) {
        if (getInstrinsic(fn) != null) {
            return
        }
        if (fn is IrFullyInheritedMemberFunction) {
            // re-uses code of super fn
            return
        }

        val body = fn.body!!
        val llvmFunction = fn.llvmRef ?: throw CodeGenerationException("You must register the functions through ${this::registerFunction.name} first to handle cyclic references (especially important for recursion): ${fn.canonicalName}")
        if (fn.bodyDefined) {
            throw CodeGenerationException("Cannot define body for function ${fn.canonicalName} multiple times!")
        }

        if (!structConstructorsRegistered) {
            structConstructorsRegistered = true
            emergeStructs
                .asSequence()
                .filter { it.irClass.autoboxer?.omitConstructorAndDestructor != true && it.irClass.canonicalName.toString() !in setOf("emerge.core.Array") }
                .forEach {
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

        val diBuilder = fn.declaredAt.file.diBuilder
        val diFunction = diBuilder.createFunction(fn.canonicalName, fn.declaredAt.lineNumber)
        llvmFunction.setDiFunction(diFunction)

        BasicBlockBuilder.fillBody(this, llvmFunction, diBuilder, diFunction) {
            when (val codeResult = emitCode(body, fn.returnType, fn.hasNothrowAbi, false, null)) {
                is ExecutableResult.ExecutionOngoing,
                is ExpressionResult.Value -> {
                    if (fn.hasNothrowAbi) {
                        (this as BasicBlockBuilder<*, LlvmVoidType>).retVoid()
                    } else {
                        (this as BasicBlockBuilder<*, EmergeFallibleCallResult.OfVoid>).retFallibleVoid()
                    }
                }
                is ExpressionResult.Terminated -> {
                    codeResult.termination
                }
            }
        }
    }

    lateinit var globalInitializerFn: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>
    internal lateinit var threadInitializerFn: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid>
        private set
    private var completed = false
    fun complete() {
        if (completed) {
            return
        }
        completed = true

        emergeStructs.forEach {
            if (it.irClass.autoboxer?.omitConstructorAndDestructor != true && it.irClass.canonicalName.toString() != "emerge.core.Array") {
                defineFunctionBody(it.irClass.constructor)
            }
        }

        Llvm.LLVMSetInitializer(pointerToUnitInstance.raw, unitType.buildStaticConstant(emptyMap()).raw)

        // todo: move to llvm global_ctors
        // this doesn't work as of now because for some reason, llc doesn't emit them into the .init_array.X sections of the object file
        globalInitializerFn = KotlinLlvmFunction.define(
            "_emerge_static_init",
            LlvmVoidType,
        ) {
            body {
                // currently nothing to do here :)
                retVoid()
            }
        }

        threadInitializerFn = KotlinLlvmFunction.define(
            "_emerge_thread_init",
            EmergeFallibleCallResult.OfVoid,
        ) {
            body {
                for (global in globalVariables) {
                    (this as BasicBlockBuilder<EmergeLlvmContext, LlvmType>)
                    val initResult = emitExpressionCode(
                        global.initializer,
                        IrSimpleTypeImpl(context.unitType.irClass, IrTypeMutability.READONLY, false),
                        functionHasNothrowAbi = false,
                        expressionResultUsed = true,
                        null,
                    )
                    if (initResult is ExpressionResult.Value) {
                        global.declaration.emitWrite!!(initResult.value)
                    } else {
                        check(initResult is ExpressionResult.Terminated)
                        return@body initResult.termination
                    }
                }
                retFallibleVoid()
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

        addModuleFlag(
            LlvmModuleFlagBehavior.ERROR,
            "Debug Info Version",
            this.i32(Llvm.LLVMDebugMetadataVersion()).toMetadata(),
        )

        diBuilderCache.values.forEach { it.diFinalize() }
    }

    override fun close() {
        diBuilderCache.values.forEach { it.close() }
        diBuilderCache.clear()
        super.close()
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

        baseType.autoboxer?.let { return it.getReferenceSiteType(this, type, forceBoxed) }
        /*if (baseType.isNothing && !type.isNullable) {
            return LlvmVoidType
        }*/

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

        if (intrinsic == null && fn.canonicalName.parent == CanonicalElementName.Package(listOf("emerge", "core", "safemath")) && fn.parameters.size == 2) {
            intrinsic = safemathFns[fn.canonicalName.simpleName]
                ?.get(fn.parameters.first().type.findSimpleTypeBound().baseType.canonicalName.simpleName)
                ?.let { registerIntrinsic(it) }
        }

        if (intrinsic == null && fn.canonicalName.parent == CanonicalElementName.Package(listOf("emerge", "platform")) && fn.canonicalName.simpleName == "panic") {
            if (fn.parameters.size == 1) {
                val paramType = fn.parameters.single().type.findSimpleTypeBound().baseType
                if (paramType.canonicalName.simpleName == "String") {
                    intrinsic = registerIntrinsic(panicOnString)
                }
                if (paramType.canonicalName.simpleName == "Throwable") {
                    intrinsic = registerIntrinsic(panicOnThrowable)
                }
            }
        }

        if (intrinsic == null && fn is IrBaseTypeFunction) {
            val autoboxer = fn.ownerBaseType.autoboxer
            if (autoboxer is Autoboxer.CFfiPointerType) {
                if (fn.canonicalName.simpleName == "\$constructor") {
                    intrinsic = autoboxer.getConstructorIntrinsic(this, fn.canonicalName)
                }
                if (fn.canonicalName.simpleName == "\$destructor") {
                    intrinsic = autoboxer.getDestructorIntrinsic(this)
                }
            }
        }

        if (intrinsic == null) {
            intrinsic = intrinsicFunctions[fn.canonicalName.toString()]?.let {
                this.registerIntrinsic(it as KotlinLlvmFunction<in EmergeLlvmContext, *>)
            }
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
fun <T : LlvmType> BasicBlockBuilder<EmergeLlvmContext, *>.heapAllocate(type: T, memset: Byte? = 0): LlvmValue<LlvmPointerType<T>> {
    val size = type.sizeof()
    val allocation = heapAllocate(size)
    memset(allocation, context.i8(0), size)
    return allocation.reinterpretAs(pointerTo(type))
}

private val intrinsicFunctions: Map<String, KotlinLlvmFunction<*, *>> by lazy {
    (
        listOf(
            arrayAddressOfFirst,
            arraySize,
            arrayAbstractFallibleGet,
            arrayAbstractFallibleSet,
            arrayAbstractPanicGet,
            arrayAbstractPanicSet,
            unwindContextSize,
            unwindCursorSize,
            isNullBuiltin,
            addressOfBuiltin,
            panicOnThrowable,
            writeMemoryAddress,
            pureWrite,
            anyReflect,
            reflectionBaseTypeIsSameObjectAs,
            unitInstance,
        )
            + intrinsicNumberOperations
    )
        .associateByErrorOnDuplicate { it.name }
}