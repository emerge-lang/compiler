package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.google.common.collect.MapMaker
import com.sun.jna.NativeLong
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmAttributeRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmContextRef

/**
 * For info on the semantics of each attribute, see [the llvm docs](https://llvm.org/docs/LangRef.html#function-attributes)
 */
sealed class LlvmFunctionAttribute(val kindName: String, val value: ULong? = null) {
    object NoUnwind : LlvmFunctionAttribute("nounwind")
    object WillReturn : LlvmFunctionAttribute("willreturn")
    object NoRecurse : LlvmFunctionAttribute("norecurse")
    object NoFree : LlvmFunctionAttribute("nofree")
    object NoReturn : LlvmFunctionAttribute("noreturn")
    object Hot : LlvmFunctionAttribute("hot")
    object AlwaysInline : LlvmFunctionAttribute("alwaysinline")

    /**
     * For passing to [Llvm.LLVMCreateEnumAttribute]
     */
    val kindId: UInt by lazy {
        val nameBytes = kindName.toByteArray(Charsets.US_ASCII)
        Llvm.LLVMGetEnumAttributeKindForName(nameBytes, NativeLong(nameBytes.size.toLong())).toUInt()
    }

    private val instanceCacheByContext = MapMaker().weakKeys().makeMap<LlvmContextRef, LlvmAttributeRef>()
    fun getRawInContext(context: LlvmContextRef): LlvmAttributeRef {
        return instanceCacheByContext.computeIfAbsent(context) {
            Llvm.LLVMCreateEnumAttribute(context, kindId.toInt(), (value ?: 0U).toLong())
        }
    }
}