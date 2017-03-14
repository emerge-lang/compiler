package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Token
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ParameterListPostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<ParameterList> {
    return rule
        .flatten()
        .mapResult(::toAST_ParameterList)
}

private fun toAST_ParameterList(tokens: TransactionalSequence<Any, Position>): ParameterList {
    // skip PARANT_OPEN
    tokens.next()!!

    val parameters: MutableList<VariableDeclaration> = LinkedList()

    while (tokens.hasNext()) {
        var next = tokens.next()!!
        if (next == OperatorToken(Operator.PARANT_CLOSE)) {
            return ParameterList(parameters)
        }

        parameters.add(next as VariableDeclaration)

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
