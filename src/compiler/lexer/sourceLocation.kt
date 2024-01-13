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

import org.apache.commons.io.input.BOMInputStream
import java.nio.charset.Charset
import java.nio.file.Files
import java.nio.file.Path
import java.util.stream.Collectors
import javax.xml.transform.Source
import kotlin.io.path.*

/**
 * A set of sources that are compiled together. This is usually one project / codebase, or
 * a module if it in case it's a modularized large codebase (compare maven reactor build)
 */
class SourceSet(
    val path: Path,
) {
    init {
        require(path.isAbsolute) { "SourceSet path must be absolute" }
        require(path.exists()) { "SourceSet directory does not exist" }
        require(path.isDirectory()) { "SourceSet must a directory" }
    }

    companion object {
        fun load(sourceSetPath: Path): Collection<SourceFile> {
            val sourceSet = SourceSet(sourceSetPath)

            return Files.walk(sourceSetPath)
                .parallel()
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
                        sourceFilePath.relativeTo(sourceSetPath),
                        content,
                    )
                }
                .collect(Collectors.toList())
        }
    }
}

interface SourceFile {
    val content: String
}

class ClasspathSourceFile(
    val pathOnClasspath: Path,
    override val content: String,
) : SourceFile {
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

    override fun toString(): String = pathRelativeToSourceSet.toString()
}

/**
 * This is not actually a source file, its code from in memory.
 */
class MemorySourceFile(
    val name: String,
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
    val fromSourceLineNumber: UInt,
    val fromColumnNumber: UInt,
    val toSourceLineNumber: UInt,
    val toColumnNumber: UInt,
) {
    constructor(sourceFile: SourceFile, start: SourceSpot, end: SourceSpot) : this(
        sourceFile,
        start.lineNumber,
        start.columnNumber,
        end.lineNumber,
        end.columnNumber,
    )

    override fun toString() = "$file $fromSourceLineNumber:$fromColumnNumber to $toSourceLineNumber:$toColumnNumber"

    val fileLineColumnText: String get() = "$file on line $fromSourceLineNumber at column $fromColumnNumber"

    companion object {
        val UNKNOWN = SourceLocation(MemorySourceFile("UNKNOWN", ""), 1u, 1u, 1u, 1u)
    }
}
