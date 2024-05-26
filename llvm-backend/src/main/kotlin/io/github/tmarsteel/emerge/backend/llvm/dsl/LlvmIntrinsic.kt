package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.google.common.collect.MapMaker
import com.sun.jna.NativeLong
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray

open class LlvmIntrinsic<R : LlvmType>(
    val name: String,
    /**
     * the types relevant for overloading; e.g. llvm.sadd.with.overflow.* takes two parameters, but only
     * one type for overloading (because both params are the same type)
     */
    val parameterTypesForOverload: List<LlvmType>,
    /**
     * the parameters for actual invocation
     */
    val parameterTypes: List<LlvmType>,
    /**
     * the type the intrinsic will return
     */
    val returnType: R,
) {
    private val rawCache: MutableMap<LlvmContext, LlvmFunction<R>> = MapMaker().weakKeys().weakValues().makeMap()
    fun getRawInContext(context: LlvmContext): LlvmFunction<R> {
        return rawCache.computeIfAbsent(context, this::computeRaw)
    }

    protected open fun computeRaw(context: LlvmContext): LlvmFunction<R> {
        val nameBytes = name.toByteArray(Charsets.US_ASCII)
        val intrinsicId = Llvm.LLVMLookupIntrinsicID(nameBytes, NativeLong(nameBytes.size.toLong()))
        val intrinsicFnValue =
            NativePointerArray.fromJavaPointers(parameterTypesForOverload.map { it.getRawInContext(context) })
                .use { paramTypesArray ->
                    Llvm.LLVMGetIntrinsicDeclaration(
                        context.module,
                        intrinsicId,
                        paramTypesArray,
                        NativeLong(paramTypesArray.length.toLong()),
                    )
                }

        return LlvmFunction(
            LlvmConstant(intrinsicFnValue, LlvmFunctionAddressType),
            LlvmFunctionType(returnType, parameterTypes),
        )
    }
}