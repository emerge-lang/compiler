package compiler

import Module
import compiler.ast.context.Module
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.TokenSequence
import java.nio.file.Path
import java.nio.file.Paths
import javax.naming.OperationNotSupportedException
import kotlin.reflect.KProperty

public fun parseFromClasspath(path: String): Module = parseFromClasspath(Paths.get(path))

public fun parseFromClasspath(path: Path): Module {
    val sourceode = ClassLoader.getSystemResource(path.toString()).readText().lines()

    val sourceDescriptor = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "classpath:" + path
        override val sourceLines = sourceode
    }
    val matchResult = Module.tryMatch(TokenSequence(lex(sourceDescriptor).toList(), sourceDescriptor.toLocation(1, 1)))

    matchResult.reportings.forEach(::println)

    return matchResult.result ?: throw InternalCompilerError("Failed to parse from classpath $path")
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