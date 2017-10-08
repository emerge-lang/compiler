package compiler.parser.grammar.dsl

import compiler.parser.Reporting

/**
 * To be thrown **ONLY** from functions defined in [GrammarReceiver] and [BaseMatchingGrammarReceiver].
 * Is "abused" to change the control flow from within a [Grammar] when it does not match the input. This may get
 * replaced by some low level coroutine magic later on.
 */
open class MatchingAbortedException(val reportings: Collection<Reporting>, message: String = "Matching aborted because a sub-rule did not match; see the reportings variable") : Exception(message)