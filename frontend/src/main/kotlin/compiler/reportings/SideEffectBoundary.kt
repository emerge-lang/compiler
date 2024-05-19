package compiler.reportings

import compiler.binding.BoundFunction
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor

sealed class SideEffectBoundary(
    val asString: String,
    /**
     * if true, the boundary is pure. If false it is readonly.
     */
    val isPure: Boolean,
) {
    override fun toString() = asString

    class Function(val function: BoundFunction) : SideEffectBoundary(
        run {
            val modifier = if (BoundFunction.Purity.PURE.contains(function.purity)) "pure" else "readonly"
            val kindAndName = if (function is BoundClassConstructor) "constructor of class ${function.classDef.simpleName}" else "function ${function.name}"
            "$modifier $kindAndName"
        },
        BoundFunction.Purity.PURE.contains(function.purity),
    )
    class ClassMemberInitializer(val member: BoundBaseTypeMemberVariable) : SideEffectBoundary("member variable initializer", true)
}