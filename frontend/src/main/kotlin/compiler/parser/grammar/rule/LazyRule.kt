package compiler.parser.grammar.rule

import compiler.lexer.Token

class LazyRule<T : Any>(private val compute: () -> Rule<T>) : Rule<T> {
    private val rule by lazy(compute)

    override val explicitName get() = rule.explicitName
    override fun match(tokens: Array<Token>, atIndex: Int) = rule.match(tokens, atIndex)
    override fun toString() = rule.toString()
}