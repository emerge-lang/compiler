package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocatedValueBaseType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.JvmStackFrameIrSourceLocation
import io.github.tmarsteel.emerge.backend.llvm.jna.DwarfBaseTypeEncoding
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDiFlags
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativeI32FlagGroup
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import java.math.BigInteger
import kotlin.reflect.KProperty

/**
 * A type-safe wrapper around [LLVMTypeRef]
 * This should allow intrinsic types to be defined as kotlin objects, not class instances
 */
interface LlvmType {
    fun getRawInContext(context: LlvmContext): LlvmTypeRef
    fun isAssignableTo(other: LlvmType) = this == other

    /**
     * for debugging
     * @return true iff this value can be assigned to the given type __only according to LLVM!!__ e.g. for
     * pointers, this doesn't check the pointee-type; use [LlvmType.isAssignableTo] for that.
     */
    fun isLlvmAssignableTo(target: LlvmType) = this == target

    fun getDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type
}

abstract class LlvmCachedType : LlvmType {
    private val byContext: MutableMap<LlvmContext, LlvmTypeRef> = MapMaker().weakKeys().makeMap()
    override fun getRawInContext(context: LlvmContext): LlvmTypeRef {
        return byContext.computeIfAbsent(context, this::computeRaw)
    }

    protected abstract fun computeRaw(context: LlvmContext): LlvmTypeRef

    private val diTypeByBuilder: MutableMap<DiBuilder, LlvmDebugInfo.Type> = MapMaker().weakKeys().makeMap()
    final override fun getDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        diTypeByBuilder[diBuilder]?.let { return it }

        if (this is ForwardDeclared) {
            val fwDcl = createTemporaryForwardDeclaration(diBuilder)
            diTypeByBuilder[diBuilder] = fwDcl
            val properDeclared = computeDiType(diBuilder)
            diTypeByBuilder[diBuilder] = properDeclared
            Llvm.LLVMMetadataReplaceAllUsesWith(fwDcl.ref, properDeclared.ref)
            return properDeclared
        } else {
            val properDeclared = computeDiType(diBuilder)
            diTypeByBuilder[diBuilder] = properDeclared
            return properDeclared
        }
    }

    protected abstract fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type

    interface ForwardDeclared {
        fun createTemporaryForwardDeclaration(diBuilder: DiBuilder): LlvmDebugInfo.Type
    }
}

object LlvmVoidType : LlvmCachedType() {
    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        return Llvm.LLVMVoidTypeInContext(context.ref)
    }

    override fun toString() = "void"

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return diBuilder.createUnspecifiedType("void")
    }
}

interface LlvmIntegerType : LlvmType {
    val isSigned: Boolean
    fun getNBitsInContext(context: LlvmContext): UInt
    fun getMaxUnsignedValueInContext(context: LlvmContext): BigInteger
}

abstract class LlvmFixedIntegerType(
    val nBits: UInt,
    override val isSigned: Boolean,
    val name: String,
) : LlvmCachedType(), LlvmIntegerType {
    init {
        check(nBits > 0u)
    }

    final override fun getNBitsInContext(context: LlvmContext): UInt = nBits

    final override fun getMaxUnsignedValueInContext(context: LlvmContext): BigInteger {
        val nNonSignBits = getNBitsInContext(context).toInt() - if (isSigned) 1 else 0
        return BigInteger.TWO.pow(nNonSignBits) - BigInteger.ONE
    }

    override fun isLlvmAssignableTo(target: LlvmType): Boolean {
        if (target === this) {
            return true
        }
        if (target is LlvmFixedIntegerType) {
            return target.nBits == nBits
        }
        if (target is LlvmIntegerType) {
            // depends on the context, assume yes
            return true
        }

        return false
    }

    override fun isAssignableTo(other: LlvmType): Boolean {
        return isLlvmAssignableTo(other)
    }

    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        return Llvm.LLVMIntTypeInContext(context.ref, nBits.toInt())
    }

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return diBuilder.createBasicType(
            name,
            nBits.toULong(),
            if (isSigned) {
                DwarfBaseTypeEncoding.SIGNED
            } else {
                DwarfBaseTypeEncoding.UNSIGNED
            }
        )
    }

    override fun toString() = "i$nBits"

    final override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LlvmFixedIntegerType) return false

        if (nBits != other.nBits) return false
        if (isSigned != other.isSigned) return false

        return true
    }

    final override fun hashCode(): Int {
        var result = nBits.hashCode()
        result = 31 * result + isSigned.hashCode()

        return result
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

            return this.pointed.isAssignableTo(other.pointed)
        }

        if (other is EmergeFallibleCallResult.OfVoid) {
            return true
        }

        return super.isAssignableTo(other)
    }

    override fun isLlvmAssignableTo(target: LlvmType): Boolean {
        return target is LlvmPointerType<*> || target is EmergeFallibleCallResult.OfVoid
    }

    override fun getDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return diBuilder.createPointerType(pointed.getDiType(diBuilder))
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
        val declaredAt: IrSourceLocation,
    ) {
        init {
            check(indexInStruct >= 0)
        }

        override fun toString() = type.toString()
    }

    override fun isAssignableTo(other: LlvmType): Boolean {
        if (other === this) {
            return true
        }
        if (other !is LlvmStructType) return false
        if (other.packed != this.packed) return false
        if (other.nMembers != this.nMembers) return false
        return this.membersInOrder.zip(other.membersInOrder).all { (selfMember, otherMember) ->
            selfMember.type.isAssignableTo(otherMember.type)
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
            val declaredAt = JvmStackFrameIrSourceLocation(Thread.currentThread().stackTrace[2])
            val member = Member<S, T>(membersInOrder.size, type, declaredAt)
            membersInOrder.add(member)
            return ImmediateDelegate(member)
        }
    }
}

abstract class LlvmNamedStructType(
    val name: String,
    val declaredAt: IrSourceLocation? = null,
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

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return computeDiType(this, diBuilder, null, NativeI32FlagGroup())
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

    companion object {
        fun <S : LlvmNamedStructType> computeDiType(
            structType: S,
            diBuilder: DiBuilder,
            elements: List<KProperty<Member<S, *>>>?,
            flags: NativeI32FlagGroup<LlvmDiFlags> = NativeI32FlagGroup(),
        ): LlvmDebugInfo.Type {
            val rawStructType = structType.getRawInContext(diBuilder.context)
            return diBuilder.createStructType(
                structType.name,
                Llvm.LLVMSizeOfTypeInBits(diBuilder.context.targetData.ref, rawStructType).toULong(),
                Llvm.LLVMABIAlignmentOfType(diBuilder.context.targetData.ref, rawStructType).toUInt() * 8u,
                flags,
                elements?.map { memberProp ->
                    val member = memberProp.getter.call()
                    val memberDiType = member.type.getDiType(diBuilder)
                    diBuilder.createStructMember(
                        memberProp.name,
                        memberDiType.sizeInBits,
                        memberDiType.alignInBits,
                        Llvm.LLVMOffsetOfElement(diBuilder.context.targetData.ref, rawStructType, member.indexInStruct).toULong() * 8u,
                        memberDiType,
                        flags,
                        member.declaredAt,
                    )
                },
                structType.declaredAt,
            )
        }
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

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        throw CodeGenerationException("Cannot emit DWARF for inline struct types")
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

    override fun getDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return diBuilder.createArrayType(
            elementType.getDiType(diBuilder),
            elementCount.toULong(),
            Llvm.LLVMABIAlignmentOfType(diBuilder.context.targetData.ref, getRawInContext(diBuilder.context)).toUInt() * 8u,
        )
    }

    override fun isAssignableTo(other: LlvmType): Boolean {
        return isLlvmAssignableTo(other)
    }

    override fun isLlvmAssignableTo(target: LlvmType): Boolean {
        if (target !is LlvmArrayType<*>) {
            return false
        }

        if (!this.elementType.isAssignableTo(target.elementType)) {
            return false
        }

        return this.elementCount >= target.elementCount
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

object LlvmFunctionAddressType : LlvmCachedType() {
    override fun toString() = "fn*"
    override fun getRawInContext(context: LlvmContext) = context.rawPointer

    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        throw UnsupportedOperationException("not used, getRawInContext is overridden")
    }

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return diBuilder.createBasicType(toString(), diBuilder.context.targetData.pointerSizeInBits, DwarfBaseTypeEncoding.ADDRESS)
    }
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

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        throw CodeGenerationException("Cannot emit DWARF for function types (only declared/defined functions)")
    }
}