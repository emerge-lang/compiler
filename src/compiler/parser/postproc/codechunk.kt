package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.CodeChunk
import compiler.ast.Executable
import compiler.ast.ReturnStatement
import compiler.ast.expression.Expression
import compiler.ast.expression.StandaloneExpression
import compiler.lexer.KeywordToken
import compiler.lexer.OperatorToken
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun ReturnStatementPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<ReturnStatement> {
    return rule
        .flatten()
        .mapResult(::toAST_ReturnStatement)
}

private fun toAST_ReturnStatement(input: TransactionalSequence<Any, Position>): ReturnStatement {
    val keyword = input.next()!! as KeywordToken
    val expression = input.next()!! as Expression<*>

    return ReturnStatement(keyword, expression)
}

// ------

fun CodeChunkPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<CodeChunk> {
    return rule
        .flatten()
        .mapResult(::toAST_codeChunk)
}

private fun toAST_codeChunk(input: TransactionalSequence<Any, Position>): CodeChunk {
    val executables = mutableListOf<Executable<*>>()
    input.remainingToList()
        .filter { it !is OperatorToken }
        .forEach {
            if (it is Executable<*>) {
                executables.add(it)
            }
            else if (it is Expression<*>) {
                executables.add(StandaloneExpression(it))
            }
            else throw InternalCompilerError("How did this thing get into here?!")
        }

    return CodeChunk(executables)
}