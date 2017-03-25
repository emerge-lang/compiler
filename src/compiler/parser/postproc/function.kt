package compiler.parser.postproc

import compiler.ast.CodeChunk
import compiler.ast.FunctionDeclaration
import compiler.ast.ParameterList
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.binding.type.Unit
import compiler.lexer.*
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun StandaloneFunctionPostprocessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<FunctionDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): FunctionDeclaration {
    val modifiers: MutableSet<FunctionModifier> = HashSet()
    var next: Any? = tokens.next()!!
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

    var type: TypeReference = Unit.reference

    if (next == OperatorToken(Operator.RETURNS)) {
        type = tokens.next()!! as TypeReference
        next = tokens.next()
    }

    val code: CodeChunk?

    if (next == OperatorToken(Operator.CBRACE_OPEN)) {
        code = tokens.next()!! as CodeChunk
        // ignore trailing CBRACE_CLOSE
    }
    else code = null

    return FunctionDeclaration(declarationKeyword.sourceLocation, modifiers, receiverType, name, parameterList, type, code)
}