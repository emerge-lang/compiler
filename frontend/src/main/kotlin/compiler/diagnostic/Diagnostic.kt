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

package compiler.diagnostic

import compiler.diagnostic.rendering.CellBuilder
import compiler.diagnostic.rendering.MonospaceCanvas
import compiler.diagnostic.rendering.MonospaceWidget
import compiler.diagnostic.rendering.TextAlignment
import compiler.diagnostic.rendering.TextSpan
import compiler.diagnostic.rendering.createBufferedMonospaceCanvas
import compiler.diagnostic.rendering.widget
import compiler.lexer.Span

abstract class Diagnostic internal constructor(
    val severity: Severity,
    open val message: String,
    val span: Span
) : Comparable<Diagnostic>, MonospaceWidget {
    override fun compareTo(other: Diagnostic): Int {
        return severity.compareTo(other.severity)
    }

    context(builder: CellBuilder)
    open fun renderMessage() {
        with(builder) {
            text(message)
        }
    }

    context(builder: CellBuilder)
    open fun renderBody() {
        with(builder) {
            sourceHints(SourceHint(span, severity = severity))
        }
    }

    final override fun render(canvas: MonospaceCanvas) = widget(canvas) {
        horizontalLayout(spacing = TextSpan.whitespace(1)) {
            column {
                text("($severity)", when (severity) {
                    Severity.ERROR -> theme.severityTagError
                    Severity.WARNING -> theme.severityTagWarning
                    Severity.INFO -> theme.severityTagInfo
                    else -> TextSpan.DEFAULT_STYLE
                })
            }
            column(TextAlignment.LINE_START) {
                renderMessage()
            }
        }

        assureOnBlankLine()
        appendLineBreak()
        renderBody()
    }

    /**
     * TODO: make final, so that all subclasses are forced to utilize renderMessage() and renderBody()
     */
    override fun toString(): String {
        val canvas = createBufferedMonospaceCanvas()
        render(canvas)
        return canvas.toString()
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Diagnostic) return false

        if (javaClass != other.javaClass) return false
        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = span.hashCode()
        result = 31 * result + javaClass.hashCode()
        return result
    }

    enum class Severity(val level: Int) {
        CONSECUTIVE(0),
        INFO(10),
        WARNING(20),
        ERROR(30);
    }
}