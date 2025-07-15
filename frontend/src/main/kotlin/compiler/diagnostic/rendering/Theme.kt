package compiler.diagnostic.rendering

import com.github.ajalt.mordant.rendering.TextColors
import com.github.ajalt.mordant.rendering.TextStyle
import com.github.ajalt.mordant.rendering.TextStyles

data class Theme(
    val severityTagError: TextStyle,
    val severityTagWarning: TextStyle,
    val severityTagInfo: TextStyle,

    val sourceLocationPointerError: TextStyle,
    val sourceLocationPointerWarning: TextStyle,
    val sourceLocationPointerInfo: TextStyle,

    val lineNumbers: TextStyle,
) {
    companion object {
        val DEFAULT = Theme(
            severityTagError = TextColors.red + TextStyles.bold,
            severityTagWarning = TextColors.yellow + TextStyles.bold,
            severityTagInfo = TextColors.brightBlue + TextStyles.bold,

            sourceLocationPointerError = TextColors.red,
            sourceLocationPointerWarning = TextSpan.DEFAULT_STYLE,
            sourceLocationPointerInfo = TextSpan.DEFAULT_STYLE,

            lineNumbers = TextSpan.DEFAULT_STYLE,
        )
    }
}