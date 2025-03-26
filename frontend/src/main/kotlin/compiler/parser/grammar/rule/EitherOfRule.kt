package compiler.parser.grammar.rule

import compiler.lexer.Token

class EitherOfRule(
    val options: List<Rule<Any>>,
    override val explicitName: String?
) : Rule<Any> {
    init {
        require(options.isNotEmpty())
    }

    override fun match(tokens: Array<Token>, atIndex: Int): Sequence<MatchingResult<Any>> {
        return options.asSequence()
            .flatMap { choice -> choice.match(tokens, atIndex) }
    }

    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitEitherOf(options)
    }

    override fun toString() = explicitName ?: super.toString()
}