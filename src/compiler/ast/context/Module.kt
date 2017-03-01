package compiler.ast.context

/**
 * A module, as declared by a source file.
 */
class Module(
    val name: Array<out String>,
    val context: MutableCTContext
)