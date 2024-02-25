package compiler.binding.struct

import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundFunction
import compiler.binding.IrFunctionImpl
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction

class StructConstructor(
    val struct: Struct,
) : BoundFunction() {
    override val context = MutableExecutionScopedCTContext(struct.context)
    override val declaredAt = struct.declaration.declaredAt
    override val receiverType = null
    override val declaresReceiver = false
    override val name = struct.simpleName
    override val modifiers = setOf(FunctionModifier.Pure)
    override val isPure = true
    override val isReadonly = true
    override val returnsExclusiveValue = true
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

    override val typeParameters: List<BoundTypeParameter>
        get() = struct.typeParameters

    override val returnType = context.resolveType(
        TypeReference(
            struct.simpleName,
            TypeReference.Nullability.NOT_NULLABLE,
            TypeMutability.IMMUTABLE,
            struct.declaration.name,
            struct.typeParameters.map {
                TypeArgument(
                    TypeVariance.UNSPECIFIED,
                    TypeReference(it.astNode.name),
                )
            },
        ),
    )
    override val isGuaranteedToThrow = false
    override fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()

    private val backendIr by lazy { IrFunctionImpl(this) }
    override fun toBackendIr(): IrFunction = backendIr
}