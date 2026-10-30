package compiler.parser.grammar

import compiler.ast.AstAnnotation
import compiler.ast.AstAnnotationSet
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.sequence
import compiler.ast.Expression as AstExpression

val Annotation = sequence("annotation") {
    operator(Operator.HASH)
    operator(Operator.SBRACE_OPEN)
    ref(Expression)
    operator(Operator.SBRACE_CLOSE)
    operator(Operator.NEWLINE)
}
    .astTransformation { tokens ->
        val hashOp = tokens.next() as OperatorToken
        tokens.next() as OperatorToken // sbrace_open
        val expression = tokens.next() as AstExpression
        val cbraceClose = tokens.next() as OperatorToken
        tokens.next() as OperatorToken // newline

        val span = hashOp.span .. cbraceClose.span
        AstAnnotation(expression, span)
    }

val AnnotationSet = sequence("annotation set") {
    repeating {
        ref(Annotation)
    }
}
    .astTransformation { tokens ->
        val annotations = tokens.takeWhileIsInstanceOf<AstAnnotation>()
        if (annotations.isEmpty()) {
            AstAnnotationSet.EMPTY
        } else {
            AstAnnotationSet(annotations)
        }
    }