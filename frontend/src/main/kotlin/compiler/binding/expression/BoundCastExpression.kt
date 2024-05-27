package compiler.binding.expression

import compiler.ast.Expression
import compiler.ast.expression.AstCastExpression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.reportings.Reporting

/**
 * Currently this is merely a way to specify the type of numeric literals
 * For that use case it is supposed to stay long term; i think this is much cleaner than suffixes
 *
 * TODO: But OFC this needs to support all the other casting usecases, too
 * That needs runtime type info and is a lot of work, do later
 */
class BoundCastExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstCastExpression,
    val value: BoundExpression<*>,
    val safeCast: Boolean,
) : BoundExpression<Expression> by value {
    override lateinit var type: BoundTypeReference
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        reportings.addAll(value.semanticAnalysisPhase1())

        val type = context.resolveType(declaration.toType)
        this.type = type

        reportings.addAll(type.validate(TypeUseSite.Irrelevant(declaration.span, null)))
        if (type !is UnresolvedType) {
            if (type !is RootResolvedTypeReference || type.isNullable || !type.baseType.isCoreNumericType) {
                reportings.add(Reporting.forbiddenCast(this, "Casting to anything but numeric types is not supported right now", declaration.toType.span ?: declaration.span))
            }
        }

        if (value !is BoundNumericLiteral) {
            reportings.add(Reporting.forbiddenCast(this, "Casting anything but integer literals is not supported right now", value.declaration.span))
        }

        if (safeCast) {
            reportings.add(Reporting.forbiddenCast(this, "Safe casts are not supported right now", declaration.operator.span))
        }

        value.setExpectedEvaluationResultType(type)

        return reportings
    }
}