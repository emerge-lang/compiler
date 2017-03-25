package compiler.binding

import compiler.parser.Reporting

/**
 * Binding parsed source to its (or a) [compiler.binding.context.CTContext] is supposed yield bound code
 * (e.g. [compiler.ast.FunctionDeclaration] yields [BoundFunction]). Alongside that, the process can yield semantic
 * [Reporting]s. This class models the result of a binding process (e.g. [compiler.ast.FunctionDeclaration.bindTo]).
 */
class BindingResult<out BoundType>(
    /**
     * The bound code
     */
    val bound: BoundType,

    /**
     * [Reporting]s on semantic
     */
    val reportings: Collection<Reporting>
)