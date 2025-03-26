package io.github.tmarsteel.emerge.treesitter

import compiler.lexer.DECIMAL_SEPARATOR
import compiler.lexer.IDENTIFIER_DELIMITER
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.STRING_DELIMITER
import compiler.lexer.Token
import compiler.parser.grammar.SourceFileGrammar
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.GrammarVisitor
import java.io.PrintStream
import kotlin.text.Typography.times

fun main(args: Array<String>) {
    System.out.println("{")
    TreeSitterOutputGrammarVisitor(IndentPrinter(System.out, initialIndentationLevel = 1u)).use { output ->
        output.tryGetReference(SourceFileGrammar)!!
    }
    System.out.println("}")
}

private class IndentPrinter(
    private val downstream: Appendable,
    initialIndentationLevel: UInt = 0u,
    private val singleIndentLevel: String = "  "
) {
    var indentationLevel = 0
        set(value) {
            check(value >= 0)
            field = value
        }
    init {
        indentationLevel = initialIndentationLevel.toInt()
    }

    private var currentLineIndented = false

    private fun assureIndented() {
        if (!currentLineIndented) {
            repeat(indentationLevel) {
                downstream.append(singleIndentLevel)
            }
            currentLineIndented = true
        }
    }

    fun println() {
        downstream.appendLine()
        currentLineIndented = false
    }

    fun print(text: String) {
        assureIndented()
        downstream.append(text)
    }

    fun println(text: String) {
        print(text)
        println()
    }

    inline fun withIndent(crossinline action: () -> Unit) {
        indentationLevel += 1
        try {
            action()
        }
        finally {
            indentationLevel -= 1
        }
    }
}

private class TreeSitterOutputGrammarVisitor(private val target: IndentPrinter) : GrammarVisitor<TreeSitterOutputGrammarVisitor.Reference>, AutoCloseable {
    private val referencesByTreeSitterName = HashMap<String, Reference>()
    private val queuedReferences = ArrayDeque<Reference>()

    private var closed = false

    override fun tryGetReference(rule: Rule<*>): Reference? {
        val treeSitterName = rule.explicitName?.treeSitterName ?: return null
        referencesByTreeSitterName[treeSitterName]?.let { return it }
        val reference = Reference(treeSitterName, rule)
        referencesByTreeSitterName[treeSitterName] = reference
        queuedReferences.add(reference)
        return reference
    }

    private fun visitComposite(treeSitterFnName: String, subRules: Iterable<Rule<*>>) {
        target.print(treeSitterFnName)
        target.println("(")
        target.withIndent {
            for (subRule in subRules) {
                subRule.visit(this)
                target.println(",")
            }
        }
        target.print(")")
    }

    override fun visitSequence(subRules: Iterable<Rule<*>>) {
        visitComposite("seq", subRules)
    }

    override fun visitEitherOf(choices: Iterable<Rule<*>>) {
        visitComposite("choice", choices)
    }

    override fun visitRepeating(
        repeated: Rule<*>,
        lowerBound: UInt,
        upperBound: UInt?,
    ) {
        when {
            lowerBound == 0u && upperBound == 1u -> visitComposite("optional", setOf(repeated))
            lowerBound == 1u && upperBound == 1u -> repeated.visit(this)
            else -> {
                check(upperBound == null)
                when (lowerBound) {
                    0u -> visitComposite("repeat", setOf(repeated))
                    1u -> visitComposite("repeat1", setOf(repeated))
                    else -> error("unsupported grammar")
                }
            }
        }
    }

    override fun visitReference(reference: Reference) {
        target.print("\$.${reference.treeSitterName}")
    }

    override fun visitDelimitedIdentifierContent() {
        target.print("new RustRegex('[^\\u${IDENTIFIER_DELIMITER.value.toString(16).padStart(4, '0')}]')")
    }

    override fun visitNonDelimitedIdentifier() {
        target.print("new RustRegex('\\w')")
    }

    override fun visitEndOfInput() {
        target.print("new RustRegex('\\$')")
    }

    override fun visitNumericLiteral() {
        target.print("$.numeric_literal")
    }

    override fun visitStringContent() {
        // TODO: this is not accurate, doesn't even support escaping
        target.print("new RustRegex('[^\\u${STRING_DELIMITER.value.toString(16).padStart(4, '0')}]+')")
    }

    override fun visitExpectedIdenticalToken(token: Token) {
        target.print(when (token) {
            is KeywordToken -> "new RustRegex('(?<=\\W)${token.keyword.text}(?=\\W)')"
            is OperatorToken -> when (token.operator) {
                Operator.NEWLINE -> "'\\n'"
                else -> "'${token.operator.text}'"
            }
            else -> error("unsupported grammar; token identical to ${token}")
        })
    }

    override fun close() {
        if (closed) {
            return
        }

        target.println("numeric_literal: $ => new RustRegex('-?\\d+(\\u${DECIMAL_SEPARATOR}\\d+)'),")

        while (true) {
            val queued = queuedReferences.removeFirstOrNull() ?: break
            target.print(queued.treeSitterName)
            target.print(": $ => ")
            queued.rule.visitNoReference(this)
            target.println(",")
        }

        closed = true
    }

    data class Reference(val treeSitterName: String, val rule: Rule<*>)
}

private val String.treeSitterName: String
    get() = this
        .lowercase()
        .replace(' ', '_')
        .replace('-', '_')
        .replace("(", "")
        .replace(")", "")