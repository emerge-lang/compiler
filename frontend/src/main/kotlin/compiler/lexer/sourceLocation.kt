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

package compiler.lexer

import compiler.diagnostic.SourceHint
import compiler.diagnostic.rendering.createBufferedMonospaceCanvas
import compiler.diagnostic.rendering.widget
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceFile
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import io.github.tmarsteel.emerge.common.CanonicalElementName
import org.apache.commons.io.input.BOMInputStream
import java.nio.charset.Charset
import java.nio.file.Files
import java.nio.file.Path
import java.util.stream.Collectors
import kotlin.io.path.exists
import kotlin.io.path.extension
import kotlin.io.path.inputStream
import kotlin.io.path.isDirectory
import kotlin.io.path.isRegularFile
import kotlin.io.path.name
import kotlin.io.path.relativeTo

/**
 * A set of sources that are compiled together. This is usually one project / codebase, or
 * a module if it in case it's a modularized large codebase (compare maven reactor build)
 */
class SourceSet(
    val path: Path,
    val moduleName: CanonicalElementName.Package,
) {
    init {
        require(path.isAbsolute) { "SourceSet path $path must be absolute" }
        require(path.exists()) { "SourceSet directory $path does not exist" }
        require(path.isDirectory()) { "SourceSet $path must be a directory" }
    }

    companion object {
        fun load(sourceSetPath: Path, moduleName: CanonicalElementName.Package): Collection<LexerSourceFile> {
            val sourceSet = SourceSet(sourceSetPath, moduleName)

            return Files.walk(sourceSetPath)
                .parallel()
                .filter { it.isRegularFile() }
                .filter { it.extension == LexerSourceFile.EXTENSION }
                .map { sourceFilePath ->
                    val content = BOMInputStream.builder()
                        .setInputStream(sourceFilePath.inputStream())
                        .get()
                        .use { inStream ->
                            val charset = inStream.bom?.charsetName?.let(Charset::forName) ?: Charsets.UTF_8
                            inStream.reader(charset).readText()
                        }

                    DiskLexerSourceFile(
                        sourceSet,
                        sourceFilePath,
                        content,
                    )
                }
                .collect(Collectors.toList())
        }
    }
}

interface LexerSourceFile {
    val content: String
    val packageName: CanonicalElementName.Package
    val name: String
    val asBackendIr: IrSourceFile

    companion object {
        const val EXTENSION = "em"
    }
}

class ClasspathLexerSourceFile(
    val pathOnClasspath: Path,
    override val packageName: CanonicalElementName.Package,
    override val content: String,
) : LexerSourceFile {
    override val name: String = pathOnClasspath.name
    override fun toString() = "classpath:/$pathOnClasspath"
    override val asBackendIr = object : IrSourceFile {
        override val path = pathOnClasspath
    }
}

class DiskLexerSourceFile(
    val sourceSet: SourceSet,
    val sourceFilePath: Path,
    override val content: String,
) : LexerSourceFile {
    val pathRelativeToSourceSet: Path = try {
        sourceFilePath.relativeTo(sourceSet.path)
    } catch (ex: IllegalArgumentException) {
        throw IllegalArgumentException("Source file is not located in the given source-set!", ex)
    }

    override val name: String = sourceFilePath.name
    override val packageName = CanonicalElementName.Package(sourceSet.moduleName.components + (pathRelativeToSourceSet.parent?.segments() ?: emptyList()))
    override val asBackendIr = object : IrSourceFile {
        override val path = sourceFilePath
    }

    override fun toString(): String = sourceFilePath.toString()
}

/**
 * This is not actually a source file, its code from in memory.
 */
class MemoryLexerSourceFile(
    override val name: String,
    override val packageName: CanonicalElementName.Package,
    override val content: String
) : LexerSourceFile {
    override fun toString() = "memory:$name"
    override val asBackendIr = object : IrSourceFile {
        override val path = Path.of(toString())
    }
}

/**
 * Describes a location within a source text (line + column)
 */
data class Span(
    val sourceFile: LexerSourceFile,
    val fromLineNumber: UInt,
    val fromColumnNumber: UInt,
    val toLineNumber: UInt,
    val toColumnNumber: UInt,
    val generated: Boolean = false,
) : IrSourceLocation {
    constructor(sourceFile: LexerSourceFile, start: SourceSpot, end: SourceSpot) : this(
        sourceFile,
        start.lineNumber,
        start.columnNumber,
        end.lineNumber,
        end.columnNumber,
    )

    fun deriveGenerated() = copy(generated = true)

    override fun toString(): String {
        return if (generated) {
            "code generated from $fileLineColumnText"
        } else {
            val canvas = createBufferedMonospaceCanvas()
            widget(canvas) {
                sourceHint(SourceHint(this@Span))
            }
            canvas.toString()
        }
    }

    operator fun rangeTo(other: Span?): Span {
        if (other == null) {
            return this
        }

        check(sourceFile == other.sourceFile)
        return Span(
            sourceFile,
            this.fromLineNumber.coerceAtMost(other.fromLineNumber),
            this.fromColumnNumber.coerceAtMost(other.fromColumnNumber),
            this.toLineNumber.coerceAtLeast(other.toLineNumber),
            this.toColumnNumber.coerceAtLeast(other.toColumnNumber),
            this.generated || other.generated,
        )
    }

    val fileLineColumnText: String get() = "$sourceFile on line $fromLineNumber, column $fromColumnNumber"

    /* impl IrSourceFile */
    override val file get()= sourceFile.asBackendIr
    override val lineNumber = fromLineNumber
    override val columnNumber = fromColumnNumber

    companion object {
        val UNKNOWN = Span(MemoryLexerSourceFile("UNKNOWN", CanonicalElementName.Package(listOf("unknown")), ""), 1u, 1u, 1u, 1u)

        fun range(vararg spans: Span?): Span? {
            if (spans.all { it == null }) {
                return null
            }

            return spans
                .asSequence()
                .filterNotNull()
                .reduce(Span::rangeTo)
        }
    }
}

private fun Path.segments(): Iterable<String> = object : Iterable<String> {
    override fun iterator() = object : Iterator<String> {
        var index = 0
        override fun hasNext(): Boolean = nameCount > index

        override fun next(): String {
            if (!hasNext()) {
                throw NoSuchElementException()
            }

            return getName(index++).name
        }
    }
}