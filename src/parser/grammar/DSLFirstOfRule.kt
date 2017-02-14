package parser.grammar

import parser.rule.FirstOfRule
import parser.rule.Rule

class DSLFirstOfRule(
        override val subRules: MutableList<Rule<*>> = mutableListOf()
) : DSLCollectionRule<Any>, FirstOfRule(subRules)