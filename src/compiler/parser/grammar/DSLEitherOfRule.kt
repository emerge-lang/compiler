package compiler.parser.grammar

import compiler.parser.rule.EitherOfRule
import compiler.parser.rule.Rule

class DSLEitherOfRule(
        override val subRules: MutableList<Rule<*>> = mutableListOf()
) : DSLCollectionRule<Any?>, EitherOfRule(subRules)