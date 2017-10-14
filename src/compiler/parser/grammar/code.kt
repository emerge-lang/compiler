package compiler.parser.grammar

import VariableDeclaration
import compiler.ast.AssignmentStatement
import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty.*
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.*
import compiler.parser.rule.Rule

val ReturnStatement = sequence {
    keyword(Keyword.RETURN)
    certainty = MATCHED
    ref(Expression)
    certainty = DEFINITIVE
}
    .describeAs("return statement")
    .postprocess(::ReturnStatementPostProcessor)

val Assignable = sequence {
    eitherOf {
        ref(BinaryExpression)
        ref(UnaryExpression)
        sequence {
            ref(ParanthesisedExpression)
            certainty = MATCHED
            ref(ExpressionPostfix)
        }
        identifier()
    }
    certainty = MATCHED
    atLeast(0) {
        ref(ExpressionPostfix)
    }
    certainty = DEFINITIVE
}
    .postprocess(::ExpressionPostprocessor)

val AssignmentStatement: Rule<AssignmentStatement> = sequence {
    ref(Assignable)

    operator(Operator.ASSIGNMENT)
    certainty = MATCHED

    ref(Expression)
    certainty = DEFINITIVE
}
    .describeAs("assignment")
    .flatten()
    .mapResult(::toAST_AssignmentStatement)

val LineOfCode = sequence {
    eitherOf {
        ref(VariableDeclaration)
        ref(AssignmentStatement)
        ref(ReturnStatement)
        ref(Expression)
    }
    certainty = MATCHED

    atLeast(0) {
        operator(Operator.NEWLINE)
        certainty = MATCHED
    }
    certainty = DEFINITIVE
}

val CodeChunk = sequence {
    certainty = MATCHED
    optionalWhitespace()
    optional {
        certainty = MATCHED
        ref(LineOfCode)

        atLeast(0) {
            ref(LineOfCode)
            certainty = DEFINITIVE
        }
        certainty = DEFINITIVE
    }

    certainty = OPTIMISTIC
}
    .postprocess(::CodeChunkPostProcessor)