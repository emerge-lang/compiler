package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.*
import compiler.ast.expression.Expression
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.binding.type.Unit
import compiler.lexer.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun StandaloneFunctionPostprocessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<FunctionDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): FunctionDeclaration {
    val modifiers = mutableSetOf<FunctionModifier>()
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

    var type: TypeReference? = null

    if (next == OperatorToken(Operator.RETURNS)) {
        type = tokens.next()!! as TypeReference
        next = tokens.next()
    }

    if (next == OperatorToken(Operator.CBRACE_OPEN)) {
        val code = tokens.next()!! as CodeChunk
        // ignore trailing CBRACE_CLOSE

        return DefaultFunctionDeclaration(declarationKeyword.sourceLocation, modifiers, receiverType, name, parameterList, type, code)
    }
    else if (next == OperatorToken(Operator.ASSIGNMENT)) {
        val assignmentOp: OperatorToken = next as OperatorToken
        val singleExpression = tokens.next()!! as Expression<*>

        return SingleExpressionFunctionDeclaration(
            declarationKeyword.sourceLocation,
            modifiers,
            receiverType,
            name,
            parameterList,
            type,
            singleExpression
        )
    }
    else {
        throw InternalCompilerError("Unexpected token when building AST: expected ${OperatorToken(Operator.CBRACE_OPEN)} or ${OperatorToken(Operator.ASSIGNMENT)} but got $next")
    }
}