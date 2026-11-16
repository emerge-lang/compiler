package compiler.ast

import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.IdentifierExpression
import compiler.binding.BoundCodeChunk
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundWhenExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span
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
        val value: Expression,
        val arrow: OperatorToken,
        val code: Executable,
    )

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
        val generatedSpan = whenKeyword.span.deriveGenerated()
        val subjectDeclaration: VariableDeclaration?
        val subjectName: IdentifierToken?
        if (subject == null) {
            subjectDeclaration = null
            subjectName = null
        } else if (namedSubject != null) {
            subjectDeclaration = namedSubject
            subjectName = namedSubject.name
        } else if (subject is IdentifierExpression && branches.isNotEmpty()) {
            subjectDeclaration = null
            subjectName = subject.identifier
        } else {
            subjectName = IdentifierToken(
                "${EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX}when_subject_${whenKeyword.span.fromLineNumber}_${whenKeyword.span.fromColumnNumber}",
                subject.span.deriveGenerated(),
            )
            subjectDeclaration = VariableDeclaration(
                declaredAt = subjectName.span,
                annotations = AstAnnotationSet.EMPTY,
                visibility = null,
                varToken = null,
                ownership = null,
                name = subjectName,
                type = null,
                initializerExpression = subject,
            )
        }

        val chain: Executable? = branches.foldRight<Branch, Executable?>(elseBranch?.code) { branch, otherwise ->
            val branchSpan = branch.arrow.span.deriveGenerated()
            IfExpression(
                branch.value.span .. branch.code.span,
                whenKeyword,
                if (subjectName == null) branch.value else BinaryExpression(
                    IdentifierExpression(subjectName),
                    AstSemanticOperator(OperatorToken(Operator.EQUALS, branchSpan)),
                    branch.value,
                ),
                branch.code,
                otherwise,
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
            BoundCodeChunk(
                scope,
                AstCodeChunk(listOfNotNull(subjectDeclaration, chain), generatedSpan),
                listOfNotNull(boundSubject, boundChain),
            ),
        )
    }
}
