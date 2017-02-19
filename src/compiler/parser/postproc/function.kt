package compiler.parser.postproc

import compiler.ast.FunctionDeclaration
import compiler.ast.ParameterList
import compiler.ast.types.TypeReference
import compiler.lexer.*
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

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

    var type = TypeReference(IdentifierToken("Unit"), false)

    if (next == OperatorToken(Operator.RETURNS)) {
        type = tokens.next()!! as TypeReference
    }

    return FunctionDeclaration(declarationKeyword, name, parameterList, type)
}