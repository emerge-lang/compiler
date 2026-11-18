package compiler.ast

import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.NullLiteralExpression
import compiler.binding.BoundCodeChunk
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundWhenExpression
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.whenBranchNeedsSubject
import compiler.lexer.*
import compiler.parser.InstanceOfExpressionPostfix
import io.github.tmarsteel.emerge.common.EmergeConstants

class AstWhenExpression(
    override val span: Span,
    val whenKeyword: KeywordToken,
    /** null for a `when` without a subject, where the value of each branch is a condition of its own */
    val subject: Expression?,
    /** if the subject is given a name (`when x = s { ... }`): declares that variable, initialized with [subject] */
    val namedSubject: VariableDeclaration?,
    val branches: List<Branch>,
    val elseBranch: ElseBranch?,
) : Expression {
    class Branch(
        val condition: Condition,
        arrow: OperatorToken,
        val code: Executable,
    ) {
        val span = arrow.span.deriveGenerated()

        sealed interface Condition {
            val span: Span
            fun build(subject: Expression?, branch: Branch, diagnosis: CollectingDiagnosis): Expression

            data class Value(val value: Expression) : Condition {
                override val span get()= value.span

                override fun build(subject: Expression?, branch: Branch, diagnosis: CollectingDiagnosis): Expression = if (subject == null) value else {
                    BinaryExpression(
                        subject,
                        AstSemanticOperator(OperatorToken(Operator.EQUALS, branch.span)),
                        value
                    )
                }
            }

            data class Binary(val operator: AstSemanticOperator, val rightHandSide: Expression) : Condition {
                override val span: Span get()= operator.token.span .. rightHandSide.span

                override fun build(subject: Expression?, branch: Branch, diagnosis: CollectingDiagnosis): Expression {
                    val subjectOrNullLiteral = subject ?: run {
                        diagnosis.whenBranchNeedsSubject(branch)
                        NullLiteralExpression(branch.span)
                    }

                    return BinaryExpression(subjectOrNullLiteral, operator, rightHandSide)
                }
            }

            data class InstanceOf(val value: InstanceOfExpressionPostfix) : Condition {
                override val span: Span get()= value.operator.span .. value.typeToCheck.span

                override fun build(subject: Expression?, branch: Branch, diagnosis: CollectingDiagnosis): Expression {
                    val subjectOrNullLiteral = subject ?: run {
                        diagnosis.whenBranchNeedsSubject(branch)
                        NullLiteralExpression(branch.span)
                    }

                    return value.modify(subjectOrNullLiteral)
                }
            }
        }
    }

    class ElseBranch(
        val elseKeyword: KeywordToken,
        val code: Executable,
    )

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        /*
        when is syntax sugar:

        when s {
            a -> X
            b -> Y
            else -> Z
        }

        gets rewritten to

        {
            __when_subject = s
            if __when_subject == a X else if __when_subject == b Y else Z
        }

        where __when_subject borrows s. If s is just an identifier, it is compared directly; there is no
        __when_subject then, so that the branches are free to mutate or capture s.

        If the subject is given a name (when x = s { ... }), that declaration takes the place of __when_subject.
        It is an ordinary local variable of the generated scope: the branches can use it, also to mutate or
        capture it, and it is gone after the when.

        Without a subject, the value of each branch is the condition as it is:

        when {
            a -> X
            b -> Y
            else -> Z
        }

        gets rewritten to

        {
            if a X else if b Y else Z
        }
         */
        val bindTimeDiagnosis = CollectingDiagnosis()
        val generatedSpan = whenKeyword.span.deriveGenerated()
        val subjectDeclaration: VariableDeclaration?
        val subjectName: IdentifierExpression?
        if (subject == null) {
            subjectDeclaration = null
            subjectName = null
        } else if (namedSubject != null) {
            subjectDeclaration = namedSubject
            subjectName = IdentifierExpression(namedSubject.name)
        } else if (subject is IdentifierExpression && branches.isNotEmpty()) {
            subjectDeclaration = null
            subjectName = IdentifierExpression(subject.identifier)
        } else {
            val subjectNameToken = IdentifierToken(
                "${EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX}when_subject_${whenKeyword.span.fromLineNumber}_${whenKeyword.span.fromColumnNumber}",
                subject.span.deriveGenerated(),
            )
            subjectDeclaration = VariableDeclaration(
                declaredAt = subjectNameToken.span,
                annotations = AstAnnotationSet.EMPTY,
                visibility = null,
                varToken = null,
                ownership = null,
                name = subjectNameToken,
                type = null,
                initializerExpression = subject,
            )
            subjectName = IdentifierExpression(subjectNameToken)
        }

        val chain: Executable? = branches.foldRight<Branch, Executable?>(elseBranch?.code) { branch, otherwise ->
            IfExpression(
                span = branch.condition.span .. branch.code.span,
                ifKeyword = whenKeyword,
                condition = branch.condition.build(subjectName, branch, bindTimeDiagnosis),
                thenCode = branch.code,
                elseCode = otherwise,
            )
        }

        val scope = MutableExecutionScopedCTContext.deriveNewScopeFrom(context)
        val boundSubject = subjectDeclaration?.bindToAsLocalVariable(scope)
        if (namedSubject == null) {
            boundSubject?.defaultOwnership = VariableOwnership.BORROWED
        }
        val boundChain = (chain as Statement?)?.bindTo(boundSubject?.modifiedContext ?: scope)

        return BoundWhenExpression(
            context,
            this,
            bindTimeDiagnosis,
            BoundCodeChunk(
                scope,
                AstCodeChunk(listOfNotNull(subjectDeclaration, chain), generatedSpan),
                listOfNotNull(boundSubject, boundChain),
            ),
        )
    }
}
