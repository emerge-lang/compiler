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

import compiler.ast.ASTModule
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.TokenSequence
import compiler.parser.grammar.Module
import java.nio.file.Path
import java.nio.file.Paths
import javax.naming.OperationNotSupportedException
import kotlin.reflect.KProperty

public fun parseFromClasspath(path: String): ASTModule = parseFromClasspath(Paths.get(path))

public fun parseFromClasspath(path: Path): ASTModule {
    val sourceode = ClassLoader.getSystemResource(path.toString())!!.readText().lines()

    val sourceDescriptor = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "classpath:" + path
        override val sourceLines = sourceode
    }
    val matchResult = Module.tryMatch(TokenSequence(lex(sourceDescriptor).toList(), sourceDescriptor.toLocation(1, 1)))

    matchResult.reportings.forEach(::println)

    return matchResult.item ?: throw InternalCompilerError("Failed to parse from classpath $path")
}

/**
 * Like [lazy] but keeps invoking the initializer until it returns a non-null value.
 */
fun <T> retryUntilNotNull(initializer: () -> T?) = RetriesUntilNotNull(initializer)

fun <T> retryUntilNotNull(defaultValue: T, initializer: () -> T?) = RetriesUntilNotNullWithDefault(defaultValue, initializer)

class RetriesUntilNotNull<T>(private val initializer: () -> T?) {
    var value: T? = null

    operator fun getValue(thisRef: Any?, property: KProperty<*>): T? {
        if (value != null) return value
        value = initializer()
        return value
    }

    operator fun setValue(thisRef: Any?, property: KProperty<*>, value: T) {
        throw OperationNotSupportedException()
    }
}

class RetriesUntilNotNullWithDefault<T>(private val defaultValue: T, private val initializer: () -> T?) {
    var value: T? = null

    operator fun getValue(thisRef: Any?, property: KProperty<*>): T {
        if (value != null) return defaultValue
        value = initializer()
        return value ?: defaultValue
    }

    operator fun setValue(thisRef: Any?, property: KProperty<*>, value: T) {
        throw OperationNotSupportedException()
    }
}

fun <T, R> Iterable<T>.attachMap(transform: (T) -> R): Iterable<Pair<T, R>> = map{ it to transform(it) }

fun <T, R> Iterable<T>.attachMapNotNull(transform: (T) -> R?): Iterable<Pair<T, R>> {
    @Suppress("UNCHECKED_CAST")
    return attachMap(transform).filter { it.second != null } as Iterable<Pair<T, R>>
}

infix fun Boolean?.nullableOr(other: Boolean?): Boolean? {
    if (this != null && this == true) {
        return true
    }

    if (other != null && other == true) {
        return true
    }

    return false
}

infix fun Boolean?.nullableAnd(other: Boolean?): Boolean? {
    if (this != null && this == true && other != null && other == true) {
        return true
    }

    return false
}
