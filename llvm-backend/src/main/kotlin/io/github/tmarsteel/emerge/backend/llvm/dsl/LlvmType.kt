package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.LlvmWordType
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM
import java.math.BigInteger

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

    override fun toString() = "void"
}

interface LlvmIntegerType : LlvmType {
    fun getMaxUnsignedValueInContext(context: LlvmContext): BigInteger {
        val rawInContext = LlvmWordType.getRawInContext(context)
        val nBits = LLVM.LLVMSizeOfTypeInBits(context.targetData.ref, rawInContext)
        check(nBits in 0 .. Int.MAX_VALUE)
        return BigInteger.TWO.pow(nBits.toInt()) - BigInteger.ONE
    }
}

abstract class LlvmFixedIntegerType(
    val nBits: Int,
) : LlvmCachedType(), LlvmIntegerType {
    init {
        check(nBits > 0)
    }

    override fun computeRaw(context: LlvmContext): LLVMTypeRef {
        return LLVM.LLVMIntTypeInContext(context.ref, nBits)
    }

    override fun toString() = "i$nBits"

    final override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmFixedIntegerType) return false

        if (nBits != other.nBits) return false

        return true
    }

    final override fun hashCode(): Int {
        return nBits
    }
}

class LlvmPointerType<Pointed : LlvmType>(val pointed: Pointed) : LlvmType {
    override fun getRawInContext(context: LlvmContext): LLVMTypeRef = context.rawPointer

    override fun toString() = "$pointed*"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmPointerType<*>) return false

        if (pointed != other.pointed) return false

        return true
    }

    override fun hashCode(): Int {
        return pointed.hashCode()
    }

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

    final override fun computeRaw(context: LlvmContext): LLVMTypeRef {
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

    override fun toString(): String = "%$name"

    final override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmStructType) return false

        if (name != other.name) return false

        return true
    }

    final override fun hashCode(): Int {
        return name.hashCode()
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

class LlvmInlineStructType(
    val memberTypes: List<LlvmType>,
    val packed: Boolean = false,
) : LlvmCachedType() {
    override fun computeRaw(context: LlvmContext): LLVMTypeRef {
        val memberTypesRaw = memberTypes.map { it.getRawInContext(context) }.toTypedArray()
        val memberTypesPointerPointer = PointerPointer(*memberTypesRaw)
        return LLVM.LLVMStructTypeInContext(context.ref, memberTypesPointerPointer, memberTypesRaw.size, if (packed) 1 else 0)
    }

    override fun toString() = memberTypes.joinToString(
        prefix = if (packed) "<{ " else "{ ",
        separator = ", ",
        postfix = if (packed) " }>" else " }",
    )

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmInlineStructType) return false

        if (memberTypes != other.memberTypes) return false
        if (packed != other.packed) return false

        return true
    }

    override fun hashCode(): Int {
        var result = memberTypes.hashCode()
        result = 31 * result + packed.hashCode()
        return result
    }

    companion object {
        /**
         * Builds a constant struct (see [LLVM.LLVMConstStructInContext]) with an inline type
         * (as opposed to a named type) inferred from the members.
         */
        fun buildInlineTypedConstantIn(context: LlvmContext, vararg members: LlvmValue<*>, packed: Boolean = false): LlvmConstant<LlvmInlineStructType> {
            val type = LlvmInlineStructType(members.map { it.type }, packed)

            val rawMembers = members.map { it.raw }.toTypedArray()
            val membersPointerPointer = PointerPointer(*rawMembers)
            val constant = LLVM.LLVMConstStructInContext(context.ref, membersPointerPointer, rawMembers.size, if (packed) 1 else 0)

            return LlvmConstant(constant, type)
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

    override fun toString() = "[$elementCount x $elementType]"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmArrayType<*>) return false

        if (elementCount != other.elementCount) return false
        if (elementType != other.elementType) return false

        return true
    }

    override fun hashCode(): Int {
        var result = elementCount.hashCode()
        result = 31 * result + elementType.hashCode()
        return result
    }
}

object LlvmFunctionAddressType : LlvmType {
    override fun getRawInContext(context: LlvmContext) = context.rawPointer
}