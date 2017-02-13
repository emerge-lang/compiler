package lexer

fun <T> Not(pred: (T) -> Boolean): (T) -> Boolean = { o -> !pred(o) }

fun <T> Or(vararg preds: (T) -> Boolean): (T) -> Boolean = Combined(Boolean::or, *preds)

fun <T> Combined(reduction: (Boolean, Boolean) -> Boolean, vararg preds: (T) -> Boolean): (T) -> Boolean = { o ->
    preds.map { it.invoke(o) }.reduce(reduction)
}

infix fun <T> ((T) -> Boolean).or(pred2: (T) -> Boolean): (T) -> Boolean = Or(this, pred2)

val IsIdentifierChar: (Char) -> Boolean = Char::isLetter

val IsWhitespace: (Char) -> Boolean = { c -> c == ' ' || c == '\t' }

val IsOperatorChar: (Char) -> Boolean = { c-> Operator.values().any { o -> o.text.startsWith(c) } }

val IsIntegerLiteral: (String) -> Boolean = { str -> str.matches(Regex("^(\\d+(\\.\\d+)?|0x[a-fA-F0-9]+|0b[0|1]+|[0-7]+oct)$/")) }

val IsFloatingPointLiteral: (String) -> Boolean = { str -> str.matches(Regex("^\\d+(.\\d+)?(e-?\\d+)?(f|d)?$")) }