package compiler.diagnostic.rendering

import java.util.Collections

fun createBufferedMonospaceCanvas(tabWidth: Int = 4): MonospaceCanvas {
    val beginNode = CanvasBeginNode()
    val endNode = CanvasEndNode()
    beginNode.next = endNode
    endNode.prev = beginNode
    val canvas = DoublyLinkedCanvas(
        MonospaceCanvas.RenderTargetInfo(tabWidth),
        beginNode,
        endNode,
    )

    return canvas
}

private abstract class CanvasNode {
    open lateinit var prev: CanvasNode
    open lateinit var next: CanvasNode

    private fun checkNotInitialized() {
        check(!this::prev.isInitialized && !this::next.isInitialized)
    }

    fun insertBefore(next: CanvasNode) {
        checkNotInitialized()

        this.prev = next.prev
        this.next = next
        next.prev.next = this
        next.prev = this
    }
}

private class CanvasBeginNode : CanvasNode() {
    override fun toString() = "CanvasBeginNode"
}

private class CanvasEndNode : CanvasNode() {
    override fun toString() = "CanvasEndNode"
}

private class LineNode : CanvasNode(), MonospaceCanvas.Line {
    private var _markers = mutableSetOf<Any>()
    override val markers: Set<Any> = Collections.unmodifiableSet(_markers)

    override fun mark(marker: Any) {
        _markers.add(marker)
    }

    val spans = ArrayList<TextSpan>()

    val isBlank: Boolean get()= spans.isEmpty() || spans.all { it.content.isEmpty() }

    override fun toString() = "LineNode[${spans.joinToString("", transform = { it.content })}]"
}

private class DoublyLinkedCanvas(
    override val renderTargetInfo: MonospaceCanvas.RenderTargetInfo,
    private val originalStart: CanvasNode,
    private val originalEnd: CanvasNode,
) : MonospaceCanvas {
    private var writeHead: LineNode? = null

    override fun createViewAppendingToBlankLine(): MonospaceCanvas {
        val newBegin = CanvasBeginNode()
        val newEnd = CanvasEndNode()
        newEnd.insertBefore(originalEnd)
        newBegin.insertBefore(newEnd)
        return DoublyLinkedCanvas(renderTargetInfo, newBegin, newEnd)
    }

    private fun assureCurrentLine(): LineNode {
        writeHead?.let { return it }
        val newWriteHead = LineNode()
        newWriteHead.insertBefore(originalEnd)
        writeHead = newWriteHead

        return newWriteHead
    }

    override fun append(span: TextSpan) {
        assureCurrentLine().spans.add(span)
    }

    override fun appendLineBreak() {
        val newWriteHead = LineNode()
        newWriteHead.insertBefore(originalEnd)
        writeHead = newWriteHead
    }

    override fun assureOnBlankLine() {
        val hadWriteHead = writeHead != null
        val localCurrentLine = assureCurrentLine()
        if (hadWriteHead && !localCurrentLine.isBlank) {
            appendLineBreak()
        }
    }

    override fun addMarkerToCurrentLine(marker: Any) {
        assureCurrentLine().mark(marker)
    }

    private val nodesSequence: Sequence<CanvasNode> = object : Sequence<CanvasNode> {
        override fun iterator(): Iterator<CanvasNode> = object : Iterator<CanvasNode> {
            var pivot = originalStart.next
            override fun hasNext() = pivot != originalEnd

            override fun next(): CanvasNode {
                val next = pivot
                if (next == originalEnd) {
                    throw NoSuchElementException()
                }

                pivot = pivot.next
                return next
            }
        }
    }
    private val lineSequence: Sequence<LineNode> = nodesSequence
        .mapNotNull { when (it) {
            is LineNode -> it
            else -> null
        } }

    override fun addColumnToLeftOfAllCurrentLines(
        alignment: TextAlignment,
        computeContent: (line: MonospaceCanvas.Line) -> TextSpan
    ) {
        val lines = lineSequence.toList()
        val columnContents = lines.map(computeContent)
        val columnWidth = columnContents.maxOf(renderTargetInfo::computeCellWidth)
        lines.zip(columnContents) { line, columnContent ->
            line.spans.addFirst(align(columnContent, columnWidth, alignment))
        }
    }

    private fun align(span: TextSpan, toWidth: Int, alignment: TextAlignment): TextSpan {
        val unpaddedCellWidth = renderTargetInfo.computeCellWidth(span)
        if (unpaddedCellWidth == toWidth) {
            return span
        }
        check(unpaddedCellWidth < toWidth)

        val paddedContent = when (alignment) {
            TextAlignment.LEFT -> span.content + " ".repeat(toWidth - unpaddedCellWidth)
            TextAlignment.RIGHT -> " ".repeat(toWidth - unpaddedCellWidth) + span.content
            TextAlignment.CENTER -> {
                val nPadding = toWidth - unpaddedCellWidth
                val nBefore = nPadding / 2
                val nAfter = nPadding - nBefore
                " ".repeat(nBefore) + span.content + " ".repeat(nAfter)
            }
        }

        return TextSpan(paddedContent)
    }

    override fun close() {
        // nothing to do, GC will take of everything
    }

    override fun toString(): String {
        val sb = StringBuilder()
        for (line in lineSequence) {
            for (span in line.spans) {
                sb.append(span.content)
            }
            sb.appendLine()
        }

        return sb.toString()

        /*return nodesSequence.joinToString(
            separator = "\n",
            prefix = "begin canvas @ ${System.identityHashCode(this).toString(16)}\n",
            postfix = "\nend canvas",
            transform = {
                it.toString().prependIndent("  ")
            },
        )*/
    }
}