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

package compiler

import compiler.ast.ASTSourceFile
import compiler.lexer.ClasspathSourceFile
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import java.nio.file.Path
import java.nio.file.Paths
import java.util.IdentityHashMap

fun parseFromClasspath(path: String, packageName: CanonicalElementName.Package): ASTSourceFile = parseFromClasspath(Paths.get(path), packageName)

fun parseFromClasspath(path: Path, packageName: CanonicalElementName.Package): ASTSourceFile {
    val sourceFile = ClasspathSourceFile(
        path,
        packageName,
        ClassLoader.getSystemResource(path.toString())!!.readText(),
    )

    val matchResult = SourceFileRule.match(lex(sourceFile), sourceFile)

    if (matchResult.hasErrors) {
        System.err.println()
        System.err.println()
        System.err.println("----------------------------------")
        System.err.println("Errors while parsing from classpath:")
        matchResult.reportings.forEach(System.err::println)
    }

    return matchResult.item ?: throw InternalCompilerError("Failed to parse from classpath $path")
}

infix fun Boolean?.nullableOr(other: Boolean?): Boolean {
    if (this != null && this == true) {
        return true
    }

    if (other != null && other == true) {
        return true
    }

    return false
}

infix fun Boolean?.nullableAnd(other: Boolean?): Boolean {
    if (this != null && this == true && other != null && other == true) {
        return true
    }

    return false
}

/**
 * Arranges the given elements such that for any element `e` its index `i` in the output is greater than the index
 * of all of its dependencies according to `dependsOn`.
 * @param dependsOn returns `true` when `dependency` is a dependency of `element`, false otherwise.
 */
fun <T : Any> Iterable<T>.sortedTopologically(dependsOn: (element: T, dependency: T) -> Boolean): List<T> {
    val elementsToSort: MutableMap<T, List<T>> = this.associateWithTo(IdentityHashMap()) { element ->
        this.filter { possibleDependency -> possibleDependency !== element && dependsOn(element, possibleDependency) }
    }

    val sorted = ArrayList<T>(elementsToSort.size)
    while (elementsToSort.isNotEmpty()) {
        var anyRemoved = false
        val elementsIterator = elementsToSort.iterator()
        while (elementsIterator.hasNext()) {
            val (element, dependencies) = elementsIterator.next()
            if (dependencies.none { it in elementsToSort }) {
                // no dependency to be sorted -> all are sorted
                sorted.add(element)
                elementsIterator.remove()
                anyRemoved = true
            }
        }

        if (!anyRemoved) {
            throw RuntimeException("Cyclic dependency involving ${elementsToSort.firstNotNullOf { it.key }}")
        }
    }

    return sorted
}

/**
 * @return all the 0th, 1st, 2nd, ... elements of the sub-sequences in a list each
 */
fun <T : Any> Sequence<Sequence<T>>.pivot(): Sequence<List<T?>> {
    return object : Sequence<List<T?>> {
        override fun iterator(): Iterator<List<T?>> {
            val subSequenceIterators = this@pivot.mapIndexed { _, it -> it.iterator() }.toList()
            return object : Iterator<List<T?>> {
                private var next: List<T?>? = null

                private fun tryFindNext() {
                    if (next != null) {
                        return
                    }

                    next = subSequenceIterators
                        .map { if (it.hasNext()) it.next() else null }
                        .takeIf { it.any { e -> e != null }}
                }

                override fun hasNext(): Boolean {
                    tryFindNext()

                    return next != null
                }

                override fun next(): List<T?> {
                    tryFindNext()
                    val nextLocal = next ?: throw NoSuchElementException()
                    next = null
                    return nextLocal
                }
            }
        }
    }
}

fun <T> List<T>.twoElementPermutationsUnordered(): Sequence<Pair<T, T>> {
    require(this is RandomAccess)
    return sequence {
        for (outerIndex in 0..this@twoElementPermutationsUnordered.lastIndex) {
            for (innerIndex in outerIndex + 1 .. this@twoElementPermutationsUnordered.lastIndex) {
                yield(Pair(
                    this@twoElementPermutationsUnordered[outerIndex],
                    this@twoElementPermutationsUnordered[innerIndex],
                ))
            }
        }
    }
}

infix fun <Input, Intermediate, Result> ((Input) -> Intermediate).andThen(other: (Intermediate) -> Result): (Input) -> Result = { other(this(it)) }