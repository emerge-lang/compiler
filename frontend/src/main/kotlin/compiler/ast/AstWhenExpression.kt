package compiler.ast

import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.NullLiteralExpression
import compiler.binding.BoundCodeChunk
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIfExpression
import compiler.binding.expression.BoundInstanceOfExpression
import compiler.binding.expression.BoundWhenExhaustivenessFallback
import compiler.binding.expression.BoundWhenExpression
import compiler.binding.expression.WhenExhaustiveness
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

                /** whether this is a `null -> ...` branch */
                val isNullBranch: Boolean get() = value is NullLiteralExpression

                override fun build(subject: Expression?, branch: Branch, diagnosis: CollectingDiagnosis): Expression = when {
                    subject == null -> value
                    // equality with null doesn't need an equals operator, and isNull tells the compiler that the
                    // subject isn't null in the other branches
                    isNullBranch -> InvocationExpression(
                        IdentifierExpression(IdentifierToken(EmergeConstants.CoreModule.IS_NULL_FN_NAME.simpleName, branch.span)),
                        null,
                        listOf(subject),
                        branch.span,
                    )
                    else -> BinaryExpression(
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

    /**
     * Takes the place of the `else` branch of a `when` with `is` branches that has none, see [BoundWhenExhaustivenessFallback].
     */
    class ExhaustivenessFallback(
        override val span: Span,
        private val exhaustiveness: WhenExhaustiveness,
    ) : Expression {
        override fun bindTo(context: ExecutionScopedCTContext): BoundWhenExhaustivenessFallback {
            return BoundWhenExhaustivenessFallback(context, this, exhaustiveness)
        }
    }

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

        /*
        Where there are `is` branches, the compiler may know all subtypes of the subject. If the branches cover all of
        them, there is no need for an else branch. This can only be determined after semantic analysis phase 2, though.
        So such a when gets an else branch in any case. If the when is exhaustive, that is unreachable code;
        otherwise, it does nothing, just like an absent else branch would.
         */
        val exhaustiveness = if (subjectName != null && branches.any { it.condition is Branch.Condition.InstanceOf }) {
            WhenExhaustiveness(hasNullBranch = branches.any { (it.condition as? Branch.Condition.Value)?.isNullBranch == true })
        } else null
        val elseCode: Executable? = elseBranch?.code ?: exhaustiveness?.let { ExhaustivenessFallback(generatedSpan, it) }

        val chain: Executable? = branches.foldRight<Branch, Executable?>(elseCode) { branch, otherwise ->
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
        if (exhaustiveness != null) {
            // the chain has exactly one if per branch; the else code (and whatever ifs it contains) comes after
            var boundIf = boundChain as BoundIfExpression?
            repeat(branches.size) {
                (boundIf!!.condition.expression as? BoundInstanceOfExpression)?.let(exhaustiveness::registerInstanceOfCheck)
                boundIf = boundIf.elseCode?.statements?.singleOrNull() as? BoundIfExpression
            }
        }

        return BoundWhenExpression(
            context,
            this,
            bindTimeDiagnosis,
            exhaustiveness,
            BoundCodeChunk(
                scope,
                AstCodeChunk(listOfNotNull(subjectDeclaration, chain), generatedSpan),
                listOfNotNull(boundSubject, boundChain),
            ),
        )
    }
}
