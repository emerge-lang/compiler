package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.google.common.collect.MapMaker
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

/**
 * A type-safe wrapper around [LLVMTypeRef]
 * This should allow intrinsic types to be defined as kotlin objects, not class instances
 */
interface LlvmType {
    fun getRawInContext(context: LlvmContext): LLVMTypeRef
}

abstract class LlvmCachedType : LlvmType {
    private val byContext: MutableMap<LlvmContext, LLVMTypeRef> = MapMaker().weakKeys().makeMap()
    final override fun getRawInContext(context: LlvmContext): LLVMTypeRef {
        return byContext.computeIfAbsent(context, this::computeRaw)
    }

    protected abstract fun computeRaw(context: LlvmContext): LLVMTypeRef
}

object LlvmVoidType : LlvmCachedType() {
    override fun computeRaw(context: LlvmContext): LLVMTypeRef {
        return LLVM.LLVMVoidTypeInContext(context.ref)
    }
}

interface LlvmIntegerType : LlvmType

abstract class LlvmFixedIntegerType(
    val nBits: Int,
) : LlvmCachedType(), LlvmIntegerType {
    init {
        check(nBits > 0)
    }

    override fun computeRaw(context: LlvmContext): LLVMTypeRef {
        return LLVM.LLVMIntTypeInContext(context.ref, nBits)
    }
}

open class LlvmPointerType<Pointed : LlvmType>(val pointed: Pointed) : LlvmType {
    override fun getRawInContext(context: LlvmContext): LLVMTypeRef = context.rawPointer

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
    val name: String,
) : LlvmCachedType() {
    private var observed = false

    override fun computeRaw(context: LlvmContext): LLVMTypeRef {
        observed = true
        val structType = LLVM.LLVMStructCreateNamed(context.ref, name)
        val elements = PointerPointer(*membersInOrder.map { it.type.getRawInContext(context) }.toTypedArray())
        LLVM.LLVMStructSetBody(structType, elements, membersInOrder.size, 0)

        return structType
    }

    private val membersInOrder = ArrayList<Member<*, *>>()

    inner class Member<S : LlvmStructType, T : LlvmType>(
        val indexInStruct: Int,
        val type: T,
    ) {
        init {
            check(indexInStruct >= 0)
        }
    }

    val nMembers: Int
        get() {
            observed = true
            return membersInOrder.size
        }

    companion object {
        @JvmStatic
        protected fun <S : LlvmStructType, T : LlvmType> S.structMember(type: T): ImmediateDelegate<LlvmStructType, Member<S, T>> {
            check(!observed) {
                "You can only declare struct members at the creation time of your type, not later."
            }
            val member = Member<S, T>(membersInOrder.size, type)
            membersInOrder.add(member)
            return ImmediateDelegate(member)
        }
    }
}

class LlvmArrayType<Element : LlvmType>(
    val elementCount: Long,
    val elementType: Element
) : LlvmType {
    init {
        require(elementCount >= 0)
    }

    override fun getRawInContext(context: LlvmContext): LLVMTypeRef {
        return LLVM.LLVMArrayType2(elementType.getRawInContext(context), elementCount)
    }
}

object LlvmFunctionAddressType : LlvmType {
    override fun getRawInContext(context: LlvmContext) = context.rawPointer
}