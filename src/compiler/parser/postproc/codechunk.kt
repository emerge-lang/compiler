package compiler.parser.postproc

import compiler.ast.CodeChunk
import compiler.ast.Executable
import compiler.ast.ReturnStatement
import compiler.ast.expression.Expression
import compiler.lexer.KeywordToken
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun ReturnStatementPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<ReturnStatement> {
    return rule
        .flatten()
        .mapResult(::toAST_ReturnStatement)
}

private fun toAST_ReturnStatement(input: TransactionalSequence<Any, Position>): ReturnStatement {
    val keyword = input.next()!! as KeywordToken
    val expression = input.next()!! as Expression

    return ReturnStatement(keyword, expression)
}

// ------

fun CodeChunkPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<CodeChunk> {
    return rule
        .flatten()
        .mapResult(::toAST_codeChunk)
}

private fun toAST_codeChunk(input: TransactionalSequence<Any, Position>): CodeChunk {
    val executables = mutableListOf<Executable>()
    input.forEachRemaining {
        executables.add(it as Executable)
    }

    return CodeChunk(executables)
}