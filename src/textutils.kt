fun String.indentByFromSecondLine(n: Int, what: String = " "): String {
    val lines = lines()

    val buf = StringBuilder()
    buf.append(lines.first())
    buf.append('\n')

    for (line in lines.subList(1, lines.lastIndex)) {
        buf.append(what.repeat(n))
        buf.append(line)
        buf.append("\n")
    }

    return buf.toString()
}
