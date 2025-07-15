package compiler.diagnostic.rendering

import compiler.diagnostic.SourceHint
import compiler.lexer.Span
import compiler.util.groupRunsBy

@DslMarker
@Retention(AnnotationRetention.BINARY)
annotation class WidgetDsl

@WidgetDsl
interface CellBuilder : MonospaceCanvas {
    fun widget(widget: MonospaceWidget) {
        widget.render(this)
    }

    fun text(text: String) {
        text.split('\n').forEach {
            assureOnBlankLine()
            append(TextSpan(it))
        }
    }

    fun horizontalLayout(spacing: TextSpan = TextSpan.whitespace(1), columnsBuilder: ColumnsBuilder.() -> Unit)

    fun sourceSpans(vararg spans: Span) {
        sourceHints(*spans.map { SourceHint(it, null) }.toTypedArray())
    }
    fun sourceHints(vararg hints: SourceHint) {
        val hintGroups = hints
            .filter { it.relativeOrderMatters }
            .groupRunsBy { it.span.sourceFile }
            .map { (file, hints) -> Pair(file, hints.toMutableList()) }
            .toMutableList()

        hints
            .filterNot { it.relativeOrderMatters }
            .forEach { unorderedHint ->
                var lastGroupOfFile = hintGroups.lastOrNull { it.first == unorderedHint.span.sourceFile }
                if (lastGroupOfFile == null) {
                    lastGroupOfFile = Pair(unorderedHint.span.sourceFile, ArrayList())
                    hintGroups.add(lastGroupOfFile)
                }
                lastGroupOfFile.second.add(unorderedHint)
            }

        for ((file, hintsInGroup) in hintGroups) {
            val widget = SourceQuoteWidget(file)
            hintsInGroup.forEach(widget::addHint)
            widget.render(this)
        }
    }
}

@WidgetDsl
interface ColumnsBuilder {
    fun column(alignment: TextAlignment = TextAlignment.LINE_START, renderFn: CellBuilder.() -> Unit)
    fun column(widget: MonospaceWidget, alignment: TextAlignment = TextAlignment.LINE_START) {
        column(alignment, widget::render)
    }
}

private class ColumnsBuilderImpl(
    val spacing: TextSpan,
) : ColumnsBuilder {
    private data class Column(
        val renderFn: CellBuilder.() -> Unit,
        val alignment: TextAlignment = TextAlignment.LINE_START,
    )

    private val columns = mutableListOf<Column>()

    override fun column(alignment: TextAlignment, renderFn: CellBuilder.() -> Unit) {
        columns.add(Column(renderFn, alignment))
    }

    fun render(canvas: MonospaceCanvas) {
        canvas.assureOnBlankLine()

        val columnLines = columns.map { column ->
            val subCanvas = CellBuilderImpl(createBufferedMonospaceCanvas(canvas.renderTargetInfo))
            column.renderFn(subCanvas)
            subCanvas.lines.toList()
        }
        val nRows = columnLines.maxOf { it.size }
        val columnWidths = columnLines.map { linesOfColumn -> linesOfColumn.maxOf { lineInColumn -> lineInColumn.spans.sumOf { canvas.renderTargetInfo.computeCellWidth(it) } } }
        for (rowIndex in 0 until nRows) {
            for (columnIndex in columns.indices) {
                val rowOfColumn = columnLines[columnIndex].getOrNull(rowIndex)?.spans?.toMutableList() ?: mutableListOf(TextSpan.EMPTY)
                canvas.renderTargetInfo.alignInPlace(rowOfColumn, columnWidths[columnIndex], columns[columnIndex].alignment)
                rowOfColumn.forEach(canvas::append)
                if (columnIndex < columns.lastIndex) {
                    canvas.append(spacing)
                }
            }
            canvas.appendLineBreak()
        }
    }
}

private class CellBuilderImpl(val canvas: MonospaceCanvas) : MonospaceCanvas by canvas, CellBuilder {
    override fun horizontalLayout(spacing: TextSpan, columnsBuilder: ColumnsBuilder.() -> Unit) {
        val b = ColumnsBuilderImpl(spacing)
        b.columnsBuilder()
        b.render(canvas)
    }
}

fun widget(canvas: MonospaceCanvas, rowRenderFn: CellBuilder.() -> Unit) {
    CellBuilderImpl(canvas).rowRenderFn()
}
