package compiler.lexer

enum class TokenType
{
    KEYWORD,
    IDENTIFIER,
    NUMERIC_LITERAL,
    OPERATOR
}

enum class Keyword(val text: String)
{
    IMPORT("import"),
    FUNCTION("fun"),
    VAL("val"),
    VAR("var"),
    MUTABLE("mutable"),
    READONLY("readonly"),
    IMMUTABLE("immutable")
}

enum class Operator(val text: String)
{
    PARANT_OPEN  ("("),
    PARANT_CLOSE (")"),
    CBRACE_OPEN  ("{"),
    CBRACE_CLOSE ("}"),
    DOT          ("."),
    ASTERISK     ("*"),
    COMMA        (","),
    SEMICOLON    (";"),
    COLON        (":"),
    NEWLINE      ("\n"),
    RETURNS      ("->"),
    PLUS         ("+"),
    MINUS        ("-"),
    TIMES        ("*"), // TODO: remove, duplicate of ASTERISK
    DIVIDE       ("/"),
    EQUALS       ("="), // TODO: rename to assignment, EQUALS is ==
    GREATER_THAN_OR_EQUALS(">="),
    LESS_THAN_OR_EQUALS("<="),
    GREATER_THAN (">"),
    LESS_THAN    ("<"),
    QUESTION_MARK("?"),
    NOTNULL      ("!!"), // find a better name for this...
    NEGATE       ("!")
}

abstract class Token
{
    abstract val type: TokenType
    abstract val sourceLocation: SourceLocation?

    override fun toString(): String {
        if (sourceLocation == null)
            return toStringWithoutLocation()
        else
            return toStringWithoutLocation() + " in " + sourceLocation!!.fileLineColumnText
    }

    open fun toStringWithoutLocation(): String = type.name
}

class KeywordToken(
        val keyword: Keyword,
        /** The actual CharSequence as it appears in the source code */
        val sourceText: String = keyword.text,
        override val sourceLocation: SourceLocation? = null
): Token()
{
    override val type = TokenType.KEYWORD

    override fun toStringWithoutLocation() = type.name + " " + keyword.name

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as KeywordToken

        if (keyword != other.keyword) return false
        if (type != other.type) return false

        return true
    }

    override fun hashCode(): Int {
        var result = keyword.hashCode()
        result = 31 * result + type.hashCode()
        return result
    }
}

class OperatorToken(
        val operator: Operator,
        override val sourceLocation: SourceLocation? = null
) : Token() {
    override val type = TokenType.OPERATOR

    override fun toStringWithoutLocation() = type.name + " " + operator.name

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as OperatorToken

        if (operator != other.operator) return false
        if (type != other.type) return false

        return true
    }

    override fun hashCode(): Int {
        var result = operator.hashCode()
        result = 31 * result + type.hashCode()
        return result
    }
}

class IdentifierToken(
        val value: String,
        override val sourceLocation: SourceLocation? = null
) : Token() {
    override val type = TokenType.IDENTIFIER

    override fun toStringWithoutLocation() = type.name + " " + value

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as IdentifierToken

        if (value != other.value) return false
        if (type != other.type) return false

        return true
    }

    override fun hashCode(): Int {
        var result = value.hashCode()
        result = 31 * result + type.hashCode()
        return result
    }
}

class NumericLiteralToken(
        override val sourceLocation: SourceLocation,
        val stringContent: String
): Token() {
    override val type = TokenType.NUMERIC_LITERAL
}