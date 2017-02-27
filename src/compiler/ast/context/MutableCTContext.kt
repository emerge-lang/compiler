package compiler.ast.context

import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeReference
import java.util.*

/**
 * Mutable compile-time context; for explanation, see the doc of [CTContext].
 */
class MutableCTContext : CTContext {
    private val variables: MutableMap<String,Variable> = HashMap()

    /**
     * Adds the given variable to this context; possibly overriding its type with the given type.
     */
    fun addVariable(declaration: VariableDeclaration, overrideType: TypeReference? = null) {
        variables[declaration.name.value] = Variable(this, declaration, overrideType)
    }

    override fun withVariable(declaration: VariableDeclaration, overrideType: TypeReference?): CTContext {
        val copy = this.mutableCopy()
        copy.addVariable(declaration, overrideType)

        return copy
    }

    override fun resolveVariable(name: String): Variable? = variables[name]
    // TODO: parent scope lookup

    /** @return An unmodified copy of this context */
    fun mutableCopy(): MutableCTContext {
        val copy = MutableCTContext()

        copy.variables.putAll(this.variables)

        return copy
    }

    /** @return An unmodified copy of this context */
    fun copy(): CTContext = mutableCopy()
}
