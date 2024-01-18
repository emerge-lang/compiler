package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.ArrayLiteralExpression
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinAny
import compiler.binding.type.BuiltinArray
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUnification
import compiler.nullableOr
import compiler.reportings.Reporting

class BoundArrayLiteralExpression(
    override val context: CTContext,
    override val declaration: ArrayLiteralExpression,
    val elements: List<BoundExpression<*>>,
) : BoundExpression<ArrayLiteralExpression> {
    override val modifiedContext: CTContext = elements.lastOrNull()?.modifiedContext ?: context
    override val isGuaranteedToThrow: Boolean get() = elements.map { it.isGuaranteedToThrow }.reduceOrNull() { a, b -> a nullableOr b } ?: false
    private var expectedReturnType: BoundTypeReference? = null
    private var expectedElementType: BoundTypeReference? = null
    override var type: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return elements.flatMap { it.semanticAnalysisPhase1() }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = elements
            .flatMap { it.semanticAnalysisPhase2() }
            .toMutableSet()

        val elementType: BoundTypeReference
        if (expectedElementType != null) {
            elementType = expectedElementType!!
            elements.forEach { element ->
                element.type?.let {
                    val unification = elementType.unify(it, element.declaration.sourceLocation, TypeUnification.EMPTY)
                    reportings.addAll(unification.reportings)
                }
            }
        } else {
            elementType = elements
                .mapNotNull { it.type }
                .reduceOrNull(BoundTypeReference::closestCommonSupertypeWith)
                ?: BuiltinAny.baseReference
        }

        type = RootResolvedTypeReference(
            TypeReference(BuiltinArray.simpleName),
            BuiltinArray,
            listOf(BoundTypeArgument(
                TypeArgument(TypeVariance.UNSPECIFIED, TypeReference("_")),
                TypeVariance.UNSPECIFIED,
                elementType,
            ))
        )
        expectedReturnType?.let {
            type = type?.withMutability(it.mutability)
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return elements.flatMap { it.findReadsBeyond(boundary) }
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return elements.flatMap { it.findWritesBeyond(boundary) }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        expectedReturnType = type

        if (type !is RootResolvedTypeReference || type.baseType !== BuiltinArray) {
            // ignore
            return
        }

        expectedElementType = type.arguments.firstOrNull()?.type ?: return
        elements.forEach { it.setExpectedEvaluationResultType(expectedElementType!!) }
    }
}