import lexer.*

val testCode = """

fun someFun(param: Type) -> ReturnType {
    let a = 3
    let b = a + 5
}

let a = (param: Type) -> ReturnType = 13f

"""

fun main(args: Array<String>) {
    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)

    tokens.forEach(::println)
}