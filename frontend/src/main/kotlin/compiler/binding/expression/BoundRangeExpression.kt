package compiler.binding.expression

import compiler.ast.Expression
import compiler.ast.expression.AstRangeExpression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.ErroneousType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnosis.Companion.doWithTransformedFindings
import compiler.diagnostic.FunctionMissingAttributeDiagnostic
import compiler.diagnostic.OperatorNotDeclaredDiagnostic
import compiler.diagnostic.UnresolvableFunctionOverloadDiagnostic

class BoundRangeExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstRangeExpression,
    val hiddenInvocation: BoundInvocationExpression,
) : BoundExpression<Expression> by hiddenInvocation {
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        val start = hiddenInvocation.receiverExpression!!
        if (start is BoundNumericLiteral) {
            // a literal as the receiver would default to S32. It takes the type of the end of the range instead;
            // if that isn't known yet (e.g. also a literal), ranges default to UWord, the type of array indices.
            val end = hiddenInvocation.valueArguments.single()
            val endType = if (end is BoundNumericLiteral) null else end.type?.takeUnless { it is ErroneousType }
            start.setExpectedEvaluationResultType(
                endType ?: context.swCtx.uword.getBoundReferenceAssertNoTypeParameters(declaration.span),
                diagnosis,
            )
        }

        diagnosis.doWithTransformedFindings(hiddenInvocation::semanticAnalysisPhase2) { diags ->
            diags.map { hiddenReporting ->
                if (hiddenReporting !is UnresolvableFunctionOverloadDiagnostic || hiddenReporting.functionNameReference != hiddenInvocation.functionNameToken) {
                    return@map hiddenReporting
                }

                OperatorNotDeclaredDiagnostic(
                    "Range operator ${declaration.operator.name} (function ${hiddenInvocation.functionNameToken.value}) not declared for type ${hiddenReporting.receiverType ?: "<unknown>"}",
                    declaration,
                )
            }
        }

        FunctionMissingAttributeDiagnostic.requireOperatorAttribute(
            hiddenInvocation,
            this,
            diagnosis,
        )
    }
}
