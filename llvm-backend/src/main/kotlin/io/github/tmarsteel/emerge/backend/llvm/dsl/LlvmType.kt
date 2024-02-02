package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM
import kotlin.reflect.KProperty

/**
 * A type-safe wrapper around [LLVMTypeRef]
 * TODO: remove need for context, compute raw on-demand when a context is known
 * This should allow intrinsic types to be defined as kotlin objects, not class instances
 */
interface LlvmType {
    val context: LlvmContext
    val raw: LLVMTypeRef
}

class LlvmVoidType(
    override val context: LlvmContext
) : LlvmType {
    override val raw = LLVM.LLVMVoidTypeInContext(context.ref)
}

/**
 * For non-structural types like i32, ptr, ...
 */
open class LlvmLeafType(
    override val context: LlvmContext,
    override val raw: LLVMTypeRef,
) : LlvmType

class LlvmIntegerType(
    context: LlvmContext,
    val nBits: Int,
) : LlvmLeafType(context, LLVM.LLVMIntTypeInContext(context.ref, nBits)) {
    init {
        check(nBits > 0)
    }

    operator fun invoke(value: Int) = invoke(value.toLong())

    operator fun invoke(value: Long): LlvmValue<LlvmIntegerType> {
        return LlvmValue(
            LLVM.LLVMConstInt(raw, value, 1),
            this,
        )
    }
}

open class LlvmPointerType<Pointed : LlvmType>(val pointed: Pointed) : LlvmType {
    override val context = pointed.context
    override val raw: LLVMTypeRef = pointed.context.rawPointer

    companion object {
        fun <T : LlvmType> pointerTo(t: T): LlvmPointerType<T> = LlvmPointerType(t)
    }
}

/**
 * Provides access by name to a struct type, keeping references stable
 * when the ordering changes. Intended for use of intrinsic/internal types
 * that are defined by the LLVM backend, not by the emerge source code. That
 * is mostly the code around handling references.
 */
abstract class LlvmStructType(
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

    private val membersInOrder = ArrayList<Member<*>>()
    protected fun <T : LlvmType> structMember(builder: LlvmContext.() -> T): ImmediateDelegate<LlvmStructType, Member<T>> {
        check(!registered)
        val member = Member(membersInOrder.size, builder)
        membersInOrder.add(member)
        return ImmediateDelegate(member)
    }

    inner class Member<T : LlvmType>(
        val indexInStruct: Int,
        builder: LlvmContext.() -> T
    ) {
        init {
            check(indexInStruct > 0)
        }
        val type: T by lazy {
            builder(context)
        }
    }
}

class LlvmArrayType<Element : LlvmType>(
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

class LlvmFunctionAddressType(
    override val context: LlvmContext,
) : LlvmType {
    override val raw = context.rawPointer
}