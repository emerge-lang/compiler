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

    open fun CellBuilder.renderMessage() {
        text(message)
    }

    open fun CellBuilder.renderBody() {
        sourceSpans(span)
    }

    private fun CellBuilder.renderLevelAndMessage() {
        horizontalLayout {
            column {
                text("($severity)")
            }
            column(TextAlignment.LINE_START) {
                renderMessage()
            }
        }
    }

    final override fun render(canvas: MonospaceCanvas) = widget(canvas) {
        renderLevelAndMessage()
        renderBody()
    }

    protected val levelAndMessage: String get() {
        val canvas = createBufferedMonospaceCanvas()
        widget(canvas) {
            renderLevelAndMessage()
        }
        return canvas.toString()
    }

    /**
     * TODO: currently, all subclasses must override this with super.toString(), because `data` is needed to detect double-reporting the same problem
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