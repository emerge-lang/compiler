package compiler.binding.struct

import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.binding.BoundFunction
import compiler.binding.context.MutableCTContext
import compiler.reportings.Reporting

class StructConstructor(
    val struct: Struct,
) : BoundFunction() {
    override val context = MutableCTContext(struct.context)
    override val declaredAt = struct.declaration.declaredAt
    override val receiverType = null
    override val name = struct.simpleName
    override val modifiers = setOf(FunctionModifier.PURE)
    override val isPure = true
    override val isReadonly = true
    override val parameters = run {
        val astParameterList = ParameterList(struct.members.map { member ->
            VariableDeclaration(
                member.declaration.declaredAt,
                null,
                member.declaration.name,
                member.declaration.type,
                false,
                null,
            )
        })
        astParameterList.bindTo(context).also {
            it.semanticAnalysisPhase1()
        }
    }

    override val typeParameters: List<TypeParameter> = struct.parameters

    override val returnType = struct.baseReference(context).modifiedWith(TypeMutability.EXCLUSIVE)
    override val isGuaranteedToThrow = false
    override fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()
}