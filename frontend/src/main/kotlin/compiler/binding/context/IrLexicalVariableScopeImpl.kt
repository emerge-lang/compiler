package compiler.binding.context

import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

class IrLexicalVariableScopeImpl : IrVariableDeclaration.Scope.Lexical {
    override val beginMarker: IrVariableDeclaration.Scope.Lexical.BeginMarker
    override val endMarker: IrVariableDeclaration.Scope.Lexical.EndMarker
    init {
        val marker = object : IrVariableDeclaration.Scope.Lexical.BeginMarker, IrVariableDeclaration.Scope.Lexical.EndMarker {
            override val scope = this@IrLexicalVariableScopeImpl
        }
        beginMarker = marker
        endMarker = marker
    }
}