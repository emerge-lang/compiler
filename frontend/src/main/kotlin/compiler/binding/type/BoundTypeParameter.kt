package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance

data class BoundTypeParameter(
    val astNode: TypeParameter,
    val context: CTContext,
) : SemanticallyAnalyzable {
    val name: String = astNode.name.value
    val variance: TypeVariance = astNode.variance

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

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        context.resolveType(TypeReference(name))
            .takeUnless { it is UnresolvedType }
            ?.let { preExistingType ->
                reportings.add(Reporting.typeParameterNameConflict(preExistingType, this))
            }
        bound = astNode.bound?.let(context::resolveType) ?: TYPE_PARAMETER_DEFAULT_BOUND
        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return bound.validate(TypeUseSite.Irrelevant(astNode.name.sourceLocation))
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return emptySet()
    }

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
        val TYPE_PARAMETER_DEFAULT_BOUND: BoundTypeReference = BuiltinAny.baseReference
            .withMutability(TypeMutability.READONLY)
            .withCombinedNullability(TypeReference.Nullability.NULLABLE)

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