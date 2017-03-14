package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.Parameter
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.expression.Expression
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.lang.reflect.Type
import java.util.*

fun ParameterDeclarationPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Parameter> {
    return rule
        .flatten()
        .mapResult(::toAST_ParameterDeclaration)
}

private fun toAST_ParameterDeclaration(input: TransactionalSequence<Any, Position>): Parameter {
    var declarationKeyword: Keyword? = null
    var typeModifier: TypeModifier? = null
    var name: IdentifierToken
    var type: TypeReference? = null

    var next = input.next()!!

    if (next is KeywordToken) {
        declarationKeyword = next.keyword
        next = input.next()!!
    }

    if (next is TypeModifier) {
        typeModifier = next
        next = input.next()!!
    }

    name = next as IdentifierToken

    if (input.peek() == OperatorToken(Operator.COLON)) {
        input.next()
        type = input.next()!! as TypeReference
    }

    return Parameter(
        typeModifier,
        name,
        type,
        declarationKeyword == Keyword.VAR
    )
}

fun ParameterListPostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<ParameterList> {
    return rule
        .flatten()
        .mapResult(::toAST_ParameterList)
}

private fun toAST_ParameterList(tokens: TransactionalSequence<Any, Position>): ParameterList {
    // skip PARANT_OPEN
    tokens.next()!!

    val parameters: MutableList<Parameter> = LinkedList()

    while (tokens.hasNext()) {
        var next = tokens.next()!!
        if (next == OperatorToken(Operator.PARANT_CLOSE)) {
            return ParameterList(parameters)
        }

        parameters.add(next as Parameter)

        tokens.mark()

        next = tokens.next()!!
        if (next == OperatorToken(Operator.PARANT_CLOSE)) {
            tokens.commit()
            return ParameterList(parameters)
        }

        if (next == OperatorToken(Operator.COMMA)) {
            tokens.commit()
        }
        else if (next !is VariableDeclaration) {
            tokens.rollback()
            next as Token
            throw InternalCompilerError("Unexpected ${next.toStringWithoutLocation()} in parameter list, expecting OPERATOR PARANT_CLOSE or OPERATOR COMMA")
        }
    }

    throw InternalCompilerError("This line should never have been reached :(")
}
