package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.google.common.collect.MapMaker
import com.sun.jna.NativeLong
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmAttributeRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmContextRef

interface LlvmAttribute {
    fun getRawInContext(context: LlvmContextRef): LlvmAttributeRef
}

abstract class LlvmEnumAttribute(val kindName: String, val value: ULong? = null) : LlvmAttribute {
    /**
     * For passing to [Llvm.LLVMCreateEnumAttribute]
     */
    val kindId: UInt by lazy {
        val nameBytes = kindName.toByteArray(Charsets.US_ASCII)
        val value = Llvm.LLVMGetEnumAttributeKindForName(nameBytes, NativeLong(nameBytes.size.toLong())).toUInt()
        if (value == 0u) {
            throw CodeGenerationException("Unknown function attribute $kindName")
        }
        value
    }

    private val instanceCacheByContext = MapMaker().weakKeys().makeMap<LlvmContextRef, LlvmAttributeRef>()
    override fun getRawInContext(context: LlvmContextRef): LlvmAttributeRef {
        return instanceCacheByContext.computeIfAbsent(context) {
            Llvm.LLVMCreateEnumAttribute(it, kindId.toInt(), (value ?: 0U).toLong())
        }
    }
}

abstract class LlvmStringAttribute(val key: String, val value: String) : LlvmAttribute {
    private val instanceCacheByContext = MapMaker().weakKeys().makeMap<LlvmContextRef, LlvmAttributeRef>()
    override fun getRawInContext(context: LlvmContextRef): LlvmAttributeRef {
        return instanceCacheByContext.computeIfAbsent(context) {
            val keyBytes = key.toByteArray(Charsets.UTF_8)
            val valueBytes = value.toByteArray(Charsets.UTF_8)

            Llvm.LLVMCreateStringAttribute(
                it,
                keyBytes,
                keyBytes.size,
                valueBytes,
                valueBytes.size,
            )
        }
    }
}

/**
 * For info on the semantics of each attribute, see [the llvm docs](https://llvm.org/docs/LangRef.html#function-attributes)
 */
sealed interface LlvmFunctionAttribute : LlvmAttribute {
    object NoUnwind : LlvmFunctionAttribute, LlvmEnumAttribute("nounwind")
    object WillReturn : LlvmFunctionAttribute, LlvmEnumAttribute("willreturn")
    object NoRecurse : LlvmFunctionAttribute, LlvmEnumAttribute("norecurse")
    object NoFree : LlvmFunctionAttribute, LlvmEnumAttribute("nofree")
    object NoReturn : LlvmFunctionAttribute, LlvmEnumAttribute("noreturn")
    object Hot : LlvmFunctionAttribute, LlvmEnumAttribute("hot")
    object AlwaysInline : LlvmFunctionAttribute, LlvmEnumAttribute("alwaysinline")
    object FramePointerAll : LlvmFunctionAttribute, LlvmStringAttribute("frame-pointer", "all")
    object UnwindTableAsync : LlvmFunctionAttribute, LlvmStringAttribute("uwtable", "async")
}