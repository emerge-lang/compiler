package compiler.lexer

fun <T> Not(pred: (T) -> Boolean): (T) -> Boolean = { o -> !pred(o) }

fun <T> Or(vararg preds: (T) -> Boolean): (T) -> Boolean = Combined(Boolean::or, *preds)

fun <T> Combined(reduction: (Boolean, Boolean) -> Boolean, vararg preds: (T) -> Boolean): (T) -> Boolean = { o ->
    preds.map { it.invoke(o) }.reduce(reduction)
}

infix fun <T> ((T) -> Boolean).or(pred2: (T) -> Boolean): (T) -> Boolean = Or(this, pred2)


val IsIdentifierChar: (Char) -> Boolean = Char::isLetter

val IsWhitespace: (Char) -> Boolean = { c -> c == ' ' || c == '\t' }