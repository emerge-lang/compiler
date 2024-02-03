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

import compiler.reportings.getIllustrationForHighlightedLines
import io.github.tmarsteel.emerge.backend.api.DotName
import org.apache.commons.io.input.BOMInputStream
import java.nio.charset.Charset
import java.nio.file.Files
import java.nio.file.LinkOption
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
    val moduleName: DotName,
) {
    init {
        require(path.isAbsolute) { "SourceSet path $path must be absolute" }
        require(path.exists()) { "SourceSet directory $path does not exist" }
        require(path.isDirectory()) { "SourceSet $path must be a directory" }
    }

    companion object {
        fun load(sourceSetPath: Path, moduleName: DotName): Collection<SourceFile> {
            val sourceSet = SourceSet(sourceSetPath, moduleName)

            return Files.walk(sourceSetPath)
                .parallel()
                .filter { it.isRegularFile(LinkOption.NOFOLLOW_LINKS) }
                .filter { it.extension == SourceFile.EXTENSION }
                .map { sourceFilePath ->
                    val content = BOMInputStream.builder()
                        .setInputStream(sourceFilePath.inputStream())
                        .get()
                        .use { inStream ->
                            val charset = inStream.bom?.charsetName?.let(Charset::forName) ?: Charsets.UTF_8
                            inStream.reader(charset).readText()
                        }

                    DiskSourceFile(
                        sourceSet,
                        sourceFilePath,
                        content,
                    )
                }
                .collect(Collectors.toList())
        }
    }
}

interface SourceFile {
    val content: String
    val packageName: DotName
    val name: String

    companion object {
        const val EXTENSION = "em"
    }
}

class ClasspathSourceFile(
    val pathOnClasspath: Path,
    override val packageName: DotName,
    override val content: String,
) : SourceFile {
    override val name: String = pathOnClasspath.name
    override fun toString() = "classpath:/$pathOnClasspath"
}

class DiskSourceFile(
    val sourceSet: SourceSet,
    val sourceFilePath: Path,
    override val content: String,
) : SourceFile {
    val pathRelativeToSourceSet: Path = try {
        sourceFilePath.relativeTo(sourceSet.path)
    } catch (ex: IllegalArgumentException) {
        throw IllegalArgumentException("Source file is not located in the given source-set!", ex)
    }

    override val name: String = sourceFilePath.name
    override val packageName = DotName(sourceSet.moduleName.components + (pathRelativeToSourceSet.parent?.segments() ?: emptyList()))

    override fun toString(): String = "${sourceSet.moduleName} $ ${pathRelativeToSourceSet}"
}

/**
 * This is not actually a source file, its code from in memory.
 */
class MemorySourceFile(
    override val name: String,
    override val packageName: DotName,
    override val content: String
) : SourceFile {
    override fun toString() = "memory:$name"
}

/**
 * Describes a location within a source text (line + column)
 *
 * TODO: rename to Span, naming stolen from rust nom
 */
data class SourceLocation(
    val file: SourceFile,
    val fromLineNumber: UInt,
    val fromColumnNumber: UInt,
    val toLineNumber: UInt,
    val toColumnNumber: UInt,
) {
    constructor(sourceFile: SourceFile, start: SourceSpot, end: SourceSpot) : this(
        sourceFile,
        start.lineNumber,
        start.columnNumber,
        end.lineNumber,
        end.columnNumber,
    )

    override fun toString() = "$file:\n${getIllustrationForHighlightedLines(setOf(this))}"

    val fileLineColumnText: String get() = "$file on line $fromLineNumber at column $fromColumnNumber"

    companion object {
        val UNKNOWN = SourceLocation(MemorySourceFile("UNKNOWN", DotName(listOf("unknown")), ""), 1u, 1u, 1u, 1u)
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