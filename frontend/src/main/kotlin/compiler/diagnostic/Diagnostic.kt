/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.diagnostic

import compiler.ast.AstFunctionAttribute
import compiler.ast.AstPackageName
import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.Executable
import compiler.ast.Expression
import compiler.ast.FunctionDeclaration
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundAssignmentStatement
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.BoundImportDeclaration
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundParameter
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeEntry
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundDeclaredBaseTypeMemberFunction
import compiler.binding.basetype.BoundMixinStatement
import compiler.binding.basetype.BoundSupertypeDeclaration
import compiler.binding.basetype.InheritedBoundMemberFunction
import compiler.binding.basetype.PossiblyMixedInBoundMemberFunction
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.VariableLifetime
import compiler.binding.expression.*
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.lexer.IdentifierToken
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import compiler.lexer.Token
import io.github.tmarsteel.emerge.common.CanonicalElementName
import textutils.indentByFromSecondLine
import java.math.BigInteger

abstract class Diagnostic internal constructor(
    val severity: Severity,
    open val message: String,
    val span: Span
) : Comparable<Diagnostic>
{
    override fun compareTo(other: Diagnostic): Int {
        return severity.compareTo(other.severity)
    }

    protected val levelAndMessage: String get() = "($severity) $message".indentByFromSecondLine(2)

    /**
     * TODO: currently, all subclasses must override this with super.toString(), because `data` is needed to detect double-reporting the same problem
     */
    override fun toString() = "$levelAndMessage\nin $span"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Diagnostic) return false

        if (javaClass != other.javaClass) return false
        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = span.hashCode()
        result = 31 * result + javaClass.hashCode()
        return result
    }

    enum class Severity(val level: Int) {
        CONSECUTIVE(0),
        INFO(10),
        WARNING(20),
        ERROR(30);
    }
}