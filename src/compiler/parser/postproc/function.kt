package compiler.parser.postproc

import compiler.ast.FunctionDeclaration
import compiler.ast.ParameterList
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun StandaloneFunctionPostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<FunctionDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): FunctionDeclaration {
    val modifiers: MutableSet<FunctionModifier> = HashSet()
    var next = tokens.next()!!
    while (next is FunctionModifier) {
        modifiers.add(next)
        next = tokens.next()!!
    }

    val declarationKeyword = next as KeywordToken

    val receiverType: TypeReference?
    next = tokens.next()!!
    if (next is TypeReference) {
        receiverType = next
        // skip DOT
        tokens.next()

        next = tokens.next()!!
    }
    else {
        receiverType = null
    }

    val name = next as IdentifierToken
    val parameterList = tokens.next()!! as ParameterList

    next = tokens.next()!!

    var type = compiler.ast.type.Unit.reference

    if (next == OperatorToken(Operator.RETURNS)) {
        type = tokens.next()!! as TypeReference
    }

    return FunctionDeclaration(declarationKeyword.sourceLocation, modifiers, receiverType, name, parameterList, type)
}