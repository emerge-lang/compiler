package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.Parameter
import compiler.ast.ParameterList
import compiler.ast.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ParameterPostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<Parameter> {
    return rule
        .flatten()
        .mapResult(::toAST_Parameter)
}

fun toAST_Parameter(tokens: TransactionalSequence<Any,Position>): Parameter {
    val name = tokens.next()!! as IdentifierToken

    val type: TypeReference? = if (tokens.hasNext()) {
        // skip COLON
        tokens.next()

        tokens.next()!! as TypeReference
    }
    else null

    return Parameter(name, type)
}

fun ParameterListPostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<ParameterList> {
    return rule
        .flatten()
        .mapResult(::toAST_ParameterList)
}

fun toAST_ParameterList(tokens: TransactionalSequence<Any, Position>): ParameterList {
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
            return ParameterList(parameters)
        }

        if (next == OperatorToken(Operator.COMMA)) {
            tokens.commit()
        }

        if (next !is Parameter) {
            tokens.rollback()
            throw InternalCompilerError("Unexpected $next in parameter list, expecting OPERATOR PARANT_CLOSE or OPERATOR COMMA")
        }
    }

    throw InternalCompilerError("This line should never have been reached :(")
}
