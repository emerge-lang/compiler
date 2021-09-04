/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

import compiler.binding.context.SoftwareContext
import compiler.binding.type.BuiltinType
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.grammar.Module
import compiler.parser.toTransactional
import compiler.reportings.Reporting
import java.time.Clock
import java.time.Duration

val testCode = """module testcode

pure fun a() {
    b()
}
val x = 3
fun b() {
    x
    a()
}
"""

fun main(args: Array<String>) {
    // setup context
    val measureClock = Clock.systemUTC()
    val startedAt = measureClock.instant()

    val swCtx = SoftwareContext()
    val builtinsModule = BuiltinType.getNewModule()
    builtinsModule.context.swCtx = swCtx
    swCtx.addModule(builtinsModule)

    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)
    val transactionalTokenSequence = tokens.toTransactional(source.toLocation(1, 1))
    val sourceInMemoryAt = measureClock.instant()
    println("Source in memory after ${Duration.between(startedAt, sourceInMemoryAt)}")

    val matched = Module.tryMatch(transactionalTokenSequence)
    val lexicalCompleteAt = measureClock.instant()
    println("Lexical analysis complete after ${Duration.between(startedAt, lexicalCompleteAt)}"
        + " (took ${Duration.between(sourceInMemoryAt, lexicalCompleteAt)})")

    println()
    println("Reportings:")
    println()

    matched.reportings.forEach { println(it); println(); println() }

    println("---")
    println()
    println()

    if (matched.reportings.containsErrors) {
        return
    }

    val parsedASTModule = matched.item!!

    swCtx.addModule(parsedASTModule.bindTo(swCtx))
    val semanticResults = swCtx.doSemanticAnalysis()
    val semanticCompleteAt = measureClock.instant()
    println("Semantic analysis complete after ${Duration.between(startedAt, semanticCompleteAt)}"
        + " (took ${Duration.between(lexicalCompleteAt, semanticCompleteAt)})")

    println()
    println("Reportings:")
    println()

    semanticResults.forEach { println(it); println(); println() }

    println("---")
}

val Iterable<Reporting>.containsErrors
    get() = map(Reporting::level).any { it.level >= Reporting.Level.ERROR.level }
