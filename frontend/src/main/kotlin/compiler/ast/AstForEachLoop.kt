package compiler.ast

import compiler.ast.expression.AstCatchBlockExpression
import compiler.ast.expression.AstInstanceOfExpression
import compiler.ast.expression.AstTryCatchExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.AstAbsoluteTypeReference
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.binding.BoundForEachLoop
import compiler.binding.BoundStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.type.BoundTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import io.github.tmarsteel.emerge.common.EmergeConstants

class AstForEachLoop(
    val foreachKeyword: KeywordToken,
    val cursorVariableName: IdentifierToken,
    val inKeyword: KeywordToken,
    val iterable: Expression,
    val body: AstCodeChunk,
) : Statement {
    override val span = foreachKeyword.span .. body.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        /*
        foreach is syntax sugar:

        foreach x in i {
            BODY
        }

        gets rewritten to

        __range0: mut _ = i.asRange()
        do {
            x = try {
                __range0.front()
            } catch __rangeFrontE0 {
                if __rangeFrontE0 is EmptyRangeException {
                    break
                }

                throw _rangeFrontE0
            }

            BODY

            __range0.popFront()
        } while true

        and any continue statements in BODY get amended with __range0.popFront()
         */

        // TODO: how to make sure that EmptyRangeException is imported??

        val generatedSpan = foreachKeyword.span.deriveGenerated()
        val rangeHolderDeclaration = VariableDeclaration(
            generatedSpan,
            null,
            null,
            null,
            IdentifierToken(context.findInternalVariableName("range"), generatedSpan),
            NamedTypeReference(
                BoundTypeReference.NAME_REQUESTING_TYPE_INFERENCE,
                mutability = TypeMutability.MUTABLE,
                span = generatedSpan
            ),
            InvocationExpression(
                MemberAccessExpression(
                    iterable,
                    OperatorToken(Operator.DOT, generatedSpan),
                    IdentifierToken(EmergeConstants.IterableContract.ITERABLE_AS_RANGE_FUNCTION_NAME, generatedSpan),
                ),
                null,
                emptyList(),
                generatedSpan
            )
        ).bindToAsLocalVariable(context)

        lateinit var boundForEachLoop: BoundForEachLoop
        val preBodyContext = MutableExecutionScopedCTContext.deriveNewLoopScopeFrom(rangeHolderDeclaration.modifiedContext, true, { boundForEachLoop })
        val frontExceptionVarName = IdentifierToken(context.findInternalVariableName("rangeFrontE"), generatedSpan)
        val cursorInBodyDeclaration = VariableDeclaration(
            cursorVariableName.span,
            null,
            null,
            null,
            cursorVariableName,
            null,
            AstTryCatchExpression(
                generatedSpan,
                InvocationExpression(
                    MemberAccessExpression(
                        IdentifierExpression(IdentifierToken(rangeHolderDeclaration.name, generatedSpan)),
                        OperatorToken(Operator.DOT, generatedSpan),
                        IdentifierToken(EmergeConstants.IterableContract.RANGE_FRONT_FUNCTION_NAME, generatedSpan),
                    ),
                    null,
                    emptyList(),
                    generatedSpan
                ),
                AstCatchBlockExpression(
                    generatedSpan,
                    frontExceptionVarName,
                    AstCodeChunk(listOf(
                        IfExpression(
                            generatedSpan,
                            AstInstanceOfExpression(
                                IdentifierExpression(frontExceptionVarName),
                                KeywordToken(Keyword.INSTANCEOF, span = generatedSpan),
                                AstAbsoluteTypeReference(EmergeConstants.IterableContract.EMPTY_RANGE_EXCEPTION_NAME, span = generatedSpan),
                            ),
                            AstBreakExpression(KeywordToken(Keyword.BREAK, span = generatedSpan)),
                            AstThrowExpression(
                                KeywordToken(Keyword.THROW, span = generatedSpan),
                                IdentifierExpression(frontExceptionVarName),
                            )
                        )
                    ), generatedSpan),
                )
            ),
        ).bindToAsLocalVariable(preBodyContext)

        val advanceRange = InvocationExpression(
            MemberAccessExpression(
                IdentifierExpression(IdentifierToken(rangeHolderDeclaration.name, generatedSpan)),
                OperatorToken(Operator.DOT, generatedSpan),
                IdentifierToken(EmergeConstants.IterableContract.RANGE_POP_FRONT_FUNCTION_NAME, generatedSpan),
            ),
            null,
            emptyList(),
            generatedSpan,
        ).bindTo(cursorInBodyDeclaration.modifiedContext)

        val boundBody = body.bindTo(cursorInBodyDeclaration.modifiedContext)

        val iterableExpression = rangeHolderDeclaration
            .let { it.initializerExpression as BoundInvocationExpression }
            .receiverExpression!!

        boundForEachLoop = BoundForEachLoop(
            context,
            this,
            iterableExpression,
            rangeHolderDeclaration,
            cursorInBodyDeclaration,
            advanceRange,
            boundBody,
        )

        return boundForEachLoop
    }
}