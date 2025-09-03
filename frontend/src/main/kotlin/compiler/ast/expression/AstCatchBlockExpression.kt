package compiler.ast.expression

import compiler.ast.AstCodeChunk
import compiler.ast.Statement
import compiler.ast.VariableDeclaration
import compiler.ast.type.AstAbsoluteTypeReference
import compiler.ast.type.TypeMutability
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundCatchBlockExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.EmergeConstants
import compiler.ast.Executable as AstExecutable
import compiler.ast.Expression as AstExpression

class AstCatchBlockExpression(
    override val span: Span,
    val throwableVariableNameToken: IdentifierToken,
    val catchBlock: AstExecutable,
) : AstExpression {
    override fun bindTo(context: ExecutionScopedCTContext): BoundCatchBlockExpression {
        val catchThrowableVariableDeclaration = VariableDeclaration(
            declaredAt = throwableVariableNameToken.span,
            visibility = null,
            varToken = null,
            ownership = null,
            name = throwableVariableNameToken,
            type = AstAbsoluteTypeReference(
                EmergeConstants.CoreModule.THROWABLE_TYPE_NAME,
                mutability = TypeMutability.MUTABLE,
                span = throwableVariableNameToken.span,
            ),
            initializerExpression = null,
        )
        val catchBlockAsChunk = when(catchBlock) {
            is AstCodeChunk -> catchBlock
            is Statement -> AstCodeChunk(listOf(catchBlock))
        }
        val catchContext = MutableExecutionScopedCTContext.deriveNewScopeFrom(context)
        val boundThrowableVariable = catchThrowableVariableDeclaration.bindToAsLocalVariable(context)
        catchContext.addVariable(boundThrowableVariable)

        return BoundCatchBlockExpression(
            context,
            catchContext,
            this,
            boundThrowableVariable,
            catchBlockAsChunk.bindTo(catchContext),
        )
    }
}