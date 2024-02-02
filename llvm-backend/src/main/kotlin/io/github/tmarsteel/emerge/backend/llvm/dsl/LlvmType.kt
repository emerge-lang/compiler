package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM
import kotlin.reflect.KProperty

/**
 * A type-safe wrapper around [LLVMTypeRef]
 */
internal interface LlvmType {
    val context: LlvmContext
    val raw: LLVMTypeRef
}

/**
 * For non-structural types like i32, ptr, ...
 */
internal class LlvmLeafType(
    override val context: LlvmContext,
    override val raw: LLVMTypeRef,
) : LlvmType

internal class LlvmPointerType<Pointed : LlvmType>(val pointed: Pointed) : LlvmType {
    override val context = pointed.context
    override val raw: LLVMTypeRef = pointed.context.pointerTypeRaw
}

/**
 * Provides access by name to a struct type, keeping references stable
 * when the ordering changes. Intended for use of intrinsic/internal types
 * that are defined by the LLVM backend, not by the emerge source code. That
 * is mostly the code around handling references.
 */
internal abstract class LlvmStructType(
    override val context: LlvmContext,
    val name: String,
) : LlvmType {
    private var registered = false
    override val raw: LLVMTypeRef by lazy {
        registered = true
        val structType = LLVM.LLVMStructCreateNamed(context.ref, name)
        val elements = PointerPointer(*membersInOrder.map { it.type.raw }.toTypedArray())
        LLVM.LLVMStructSetBody(structType, elements, membersInOrder.size, 0)

        structType
    }

    private val membersInOrder = ArrayList<StructMemberDelegate<*>>()
    protected fun <T : LlvmType> structMember(builder: LlvmContext.() -> T): StructMemberDelegate<T> {
        check(!registered)
        val member = StructMemberDelegate(context, builder)
        membersInOrder.add(member)
        return member
    }

    protected fun structMemberRaw(builder: LlvmContext.() -> LLVMTypeRef): StructMemberDelegate<LlvmLeafType> {
        return structMember {
            val raw = builder(context)
            LlvmLeafType(context, raw)
        }
    }

    inner class StructMemberDelegate<T : LlvmType>(
        private val context: LlvmContext,
        private val builder: (context: LlvmContext) -> T
    ) {
        val type: T by lazy {
            builder(context)
        }

        operator fun getValue(thisRef: Any, prop: KProperty<*>): T {
            return type
        }
    }
}

internal class LlvmArrayType<Element : LlvmType>(
    override val context: LlvmContext,
    val elementCount: Long,
    val elementType: Element
) : LlvmType {
    init {
        require(elementCount >= 0)
    }

    override val raw by lazy {
        LLVM.LLVMArrayType2(elementType.raw, elementCount)
    }
}

internal class LlvmFunctionAddressType(
    override val context: LlvmContext,
) : LlvmType {
    override val raw = context.pointerTypeRaw
}