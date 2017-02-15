package parser.grammar

import parser.rule.EitherOfRule
import parser.rule.Rule

class DSLEitherOfRule(
        override val subRules: MutableList<Rule<*>> = mutableListOf()
) : DSLCollectionRule<Any?>, EitherOfRule(subRules)