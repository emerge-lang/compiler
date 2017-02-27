package compiler.parser.postproc

import compiler.ast.FunctionDeclaration
import compiler.ast.FunctionSignature
import compiler.ast.ParameterList
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun FunctionPostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<FunctionDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): FunctionDeclaration {
    val declarationKeyword = tokens.next()!! as KeywordToken

    val name = tokens.next()!! as IdentifierToken
    val parameterList = tokens.next()!! as ParameterList

    var next = tokens.next()!!

    var type = compiler.ast.type.Unit.defaultReference

    if (next == OperatorToken(Operator.RETURNS)) {
        type = tokens.next()!! as TypeReference
    }

    return FunctionDeclaration(declarationKeyword.sourceLocation, name, parameterList, type)
}