package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceFile
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmTarget
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.ArrayElementLayoutKind
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeReferenceArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeSliceArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arrayElementLayoutKindOf
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arrayTypeForLayoutKind
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.layoutKindOf
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.mockk.mockk
import java.nio.file.Paths

/**
 * The static choice of the array object type ([EmergeLlvmContext.getArrayObjectTypeOfExactElement]) and the
 * runtime choice through the layout kind in the typeinfo must agree, otherwise `Array.new::<T>` in generic code
 * creates arrays that the static accessors misread.
 */
class ArrayElementLayoutTest : FreeSpec({
    val expectations = mapOf(
        "S8" to ArrayElementLayoutKind.S8,
        "U8" to ArrayElementLayoutKind.U8,
        "S16" to ArrayElementLayoutKind.S16,
        "U16" to ArrayElementLayoutKind.U16,
        "S32" to ArrayElementLayoutKind.S32,
        "U32" to ArrayElementLayoutKind.U32,
        "S64" to ArrayElementLayoutKind.S64,
        "U64" to ArrayElementLayoutKind.U64,
        "SWord" to ArrayElementLayoutKind.SWORD,
        "UWord" to ArrayElementLayoutKind.UWORD,
        "Bool" to ArrayElementLayoutKind.BOOL,
        "Array" to ArrayElementLayoutKind.SLICE,
        "String" to ArrayElementLayoutKind.REFERENCE,
        "F32" to ArrayElementLayoutKind.REFERENCE,
    )

    "static and runtime layout choice agree" - {
        expectations.forEach { (typeName, expectedKind) ->
            typeName {
                EmergeLlvmContext.createDoAndDispose(LlvmTarget.fromTriple("x86_64-pc-linux-gnu"), false) { ctx ->
                    val baseType = LayoutMockCoreType(typeName)
                    val staticChoice = ctx.getArrayObjectTypeOfExactElement(baseType, isNullable = false)
                    val kind = ctx.arrayElementLayoutKindOf(baseType)
                    kind shouldBe expectedKind
                    layoutKindOf(staticChoice) shouldBe kind
                    arrayTypeForLayoutKind(kind) shouldBe staticChoice

                    val nullableChoice = ctx.getArrayObjectTypeOfExactElement(baseType, isNullable = true)
                    nullableChoice shouldBe (if (kind == ArrayElementLayoutKind.SLICE) EmergeSliceArrayType else EmergeReferenceArrayType)
                }
            }
        }
    }

    "ReflectionBaseType" {
        EmergeLlvmContext.createDoAndDispose(LlvmTarget.fromTriple("x86_64-pc-linux-gnu"), false) { ctx ->
            val baseType = LayoutMockClass(CanonicalElementName.BaseType(CanonicalElementName.Package(listOf("emerge", "core", "reflection")), "ReflectionBaseType"))
            val kind = ctx.arrayElementLayoutKindOf(baseType)
            kind shouldBe ArrayElementLayoutKind.TYPEINFO_PTR
            arrayTypeForLayoutKind(kind) shouldBe ctx.getArrayObjectTypeOfExactElement(baseType, isNullable = false)
        }
    }
})

private object LayoutMockSourceLocation : IrSourceLocation {
    override val file = object : IrSourceFile {
        override val path = Paths.get("/mock/file.em")
    }
    override val lineNumber: UInt = 1u
    override val columnNumber: UInt = 1u
}

private open class LayoutMockClass(override val canonicalName: CanonicalElementName.BaseType) : IrClass {
    override val supertypes = emptySet<IrInterface>()
    override val parameters = emptyList<IrBaseType.Parameter>()
    override val memberFunctions = emptyList<IrOverloadGroup<IrMemberFunction>>()
    override val memberVariables = emptyList<IrClass.MemberVariable>()
    override val fields = emptyList<IrClass.Field>()
    override val typeParameterFields = emptyMap<IrBaseType.Parameter, IrClass.Field>()
    override val constructor: IrFunction = mockk()
    override val destructor: IrFunction = mockk()
    override val declaredAt = LayoutMockSourceLocation
}

private class LayoutMockCoreType(simpleName: String) : LayoutMockClass(
    CanonicalElementName.BaseType(CanonicalElementName.Package(listOf("emerge", "core")), simpleName)
)
