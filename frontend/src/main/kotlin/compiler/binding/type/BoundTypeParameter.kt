package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.lexer.Span
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance

data class BoundTypeParameter(
    val astNode: TypeParameter,
    val context: CTContext,
) : SemanticallyAnalyzable, DefinitionWithVisibility {
    val name: String = astNode.name.value
    val variance: TypeVariance = astNode.variance
    override val visibility: BoundVisibility = context.visibility

    /**
     * Available after [semanticAnalysisPhase1].
     */
    lateinit var bound: BoundTypeReference
        private set

    private val _modifiedContext = MutableCTContext(context)
    val modifiedContext: CTContext = _modifiedContext
    init {
        _modifiedContext.addTypeParameter(this)
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        context.resolveType(TypeReference(name))
            .takeUnless { it is UnresolvedType }
            ?.let { preExistingType ->
                diagnosis.add(Diagnostic.typeParameterNameConflict(preExistingType, this))
            }
        bound = astNode.bound?.let(context::resolveType) ?: context.swCtx.typeParameterDefaultBound
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        bound.validate(TypeUseSite.Irrelevant(astNode.name.span, this), diagnosis)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        throw InternalCompilerError("This should not ever matter")
    }

    override fun toStringForErrorMessage() = "type parameter $name"

    private val _backendIr by lazy { IrTypeParameterImpl(name, variance, bound) }
    fun toBackendIr(): IrBaseType.Parameter = _backendIr

    override fun toString(): String {
        if (!this::bound.isInitialized) {
            return "[not validated; $astNode]"
        }
        var str = ""
        if (variance != TypeVariance.UNSPECIFIED) {
            str += variance.name.lowercase()
            str += " "
        }

        str += name

        str += " : "
        str += bound.toString()

        return str
    }

    companion object {
        fun List<TypeParameter>.chain(context: CTContext): Pair<List<BoundTypeParameter>, CTContext> {
            var carry = context
            val boundParams = ArrayList<BoundTypeParameter>(size)
            for (parameter in this) {
                val bound = parameter.bindTo(carry)
                boundParams.add(bound)
                carry = bound.modifiedContext
            }

            return Pair(boundParams, carry)
        }
    }
}

private class IrTypeParameterImpl(
    override val name: String,
    givenVariance: TypeVariance,
    givenBound: BoundTypeReference,
) : IrBaseType.Parameter {
    override val variance: IrTypeVariance = when(givenVariance) {
        TypeVariance.UNSPECIFIED -> IrTypeVariance.INVARIANT
        TypeVariance.IN -> IrTypeVariance.IN
        TypeVariance.OUT -> IrTypeVariance.OUT
    }

    override val bound = givenBound.toBackendIr()
}