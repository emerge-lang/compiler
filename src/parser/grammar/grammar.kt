import lexer.Keyword
import lexer.Operator
import parser.grammar.rule

val Import = rule("Import") {
    keyword(Keyword.IMPORT)

    __definitive()

    atLeast(1) {
        identifier()
        operator(Operator.DOT)
    }
    firstOf {
        operator(Operator.ASTERISK)
        identifier()
    }
}