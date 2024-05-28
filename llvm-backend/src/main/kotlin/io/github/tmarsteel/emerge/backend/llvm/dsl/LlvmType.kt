package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocatedValueBaseType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import java.math.BigInteger

/**
 * A type-safe wrapper around [LLVMTypeRef]
 * This should allow intrinsic types to be defined as kotlin objects, not class instances
 */
interface LlvmType {
    fun getRawInContext(context: LlvmContext): LlvmTypeRef
    fun isAssignableTo(other: LlvmType) = this == other
}

abstract class LlvmCachedType : LlvmType {
    private val byContext: MutableMap<LlvmContext, LlvmTypeRef> = MapMaker().weakKeys().makeMap()
    override fun getRawInContext(context: LlvmContext): LlvmTypeRef {
        return byContext.computeIfAbsent(context, this::computeRaw)
    }

    protected abstract fun computeRaw(context: LlvmContext): LlvmTypeRef
}

object LlvmVoidType : LlvmCachedType() {
    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        return Llvm.LLVMVoidTypeInContext(context.ref)
    }

    override fun toString() = "void"
}

interface LlvmIntegerType : LlvmType {
    fun getNBitsInContext(context: LlvmContext): Int
    fun getMaxUnsignedValueInContext(context: LlvmContext): BigInteger {
        val rawInContext = EmergeWordType.getRawInContext(context)
        val nBits = Llvm.LLVMSizeOfTypeInBits(context.targetData.ref, rawInContext)
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

    override fun getNBitsInContext(context: LlvmContext): Int = nBits

    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        return Llvm.LLVMIntTypeInContext(context.ref, nBits)
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
    override fun getRawInContext(context: LlvmContext): LlvmTypeRef = context.rawPointer

    override fun isAssignableTo(other: LlvmType): Boolean {
        if (other is LlvmPointerType<*>) {
            if (other.pointed == LlvmVoidType) {
                // any pointer can be assigned to a void-ptr
                return true
            }

            if (pointed is EmergeClassType && other.pointed == EmergeHeapAllocatedValueBaseType) {
                // any emerge class can be assigned to any
                return true
            }
        }

        return super.isAssignableTo(other)
    }

    override fun toString() = "*$pointed"

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
    val packed: Boolean,
) : LlvmCachedType() {
    protected var observed = false

    protected val membersInOrder = ArrayList<Member<*, *>>()

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

abstract class LlvmNamedStructType(
    val name: String,
    packed: Boolean = false,
) : LlvmStructType(packed) {
    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        observed = true
        val structType = Llvm.LLVMStructCreateNamed(context.ref, name)
        NativePointerArray.fromJavaPointers(membersInOrder.map { it.type.getRawInContext(context) }).use { elements ->
            Llvm.LLVMStructSetBody(structType, elements, membersInOrder.size, if (packed) 1 else 0)
        }

        return structType
    }

    override fun toString(): String = "%$name"

    final override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmNamedStructType) return false

        if (name != other.name) return false

        return true
    }

    final override fun hashCode(): Int {
        return name.hashCode()
    }
}

open class LlvmInlineStructType(
    packed: Boolean = false,
) : LlvmStructType(packed) {
    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        NativePointerArray.fromJavaPointers(membersInOrder.map { it.type.getRawInContext(context) }).use { memberTypesRaw ->
            return Llvm.LLVMStructTypeInContext(context.ref, memberTypesRaw, memberTypesRaw.length, if (packed) 1 else 0)
        }
    }

    override fun toString() = membersInOrder.joinToString(
        prefix = if (packed) "<{ " else "{ ",
        separator = ", ",
        postfix = if (packed) " }>" else " }",
    )

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmInlineStructType) return false

        if (membersInOrder != other.membersInOrder) return false
        if (packed != other.packed) return false

        return true
    }

    override fun hashCode(): Int {
        var result = membersInOrder.hashCode()
        result = 31 * result + packed.hashCode()
        return result
    }

    companion object {
        /**
         * Builds a constant struct (see [Llvm.LLVMConstStructInContext]) with an inline type
         * (as opposed to a named type) inferred from the members.
         */
        fun buildInlineTypedConstantIn(context: LlvmContext, vararg members: LlvmValue<*>, packed: Boolean = false): LlvmConstant<LlvmInlineStructType> {
            val type = object : LlvmInlineStructType(packed) {
                init {
                    members.forEach { structMember(it.type) }
                }
            }

            val constant = NativePointerArray.fromJavaPointers(members.map { it.raw }).use { rawMembers ->
                Llvm.LLVMConstStructInContext(context.ref, rawMembers, rawMembers.length, if (packed) 1 else 0)
            }

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

    override fun getRawInContext(context: LlvmContext): LlvmTypeRef {
        return Llvm.LLVMArrayType2(elementType.getRawInContext(context), elementCount)
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
    override fun toString() = "fn*"
    override fun getRawInContext(context: LlvmContext) = context.rawPointer
}

data class LlvmFunctionType<out R : LlvmType>(
    val returnType: R,
    val parameterTypes: List<LlvmType>,
) : LlvmCachedType() {
    override fun toString() = parameterTypes.joinToString(
        prefix = "(",
        transform = { it.toString() },
        separator = ", ",
        postfix = ") -> $returnType"
    )
    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        val returnTypeRaw = returnType.getRawInContext(context)
        NativePointerArray.fromJavaPointers(parameterTypes.map { it.getRawInContext(context) }).use { parameterTypesRaw ->
            return Llvm.LLVMFunctionType(
                returnTypeRaw,
                parameterTypesRaw,
                parameterTypesRaw.length,
                0,
            )
        }
    }
}