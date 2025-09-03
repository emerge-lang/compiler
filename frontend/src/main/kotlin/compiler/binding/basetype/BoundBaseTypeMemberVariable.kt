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

package compiler.binding.basetype

import compiler.ast.BaseTypeMemberDeclaration
import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.ast.type.TypeMutability
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.decoratingMemberVariableWithNonReadType
import compiler.diagnostic.decoratingMemberVariableWithoutConstructorInitialization
import compiler.diagnostic.quoteIdentifier
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundBaseTypeMemberVariable(
    private val typeRootContext: CTContext,
    private val boundLocalVariableInConstructorCode: BoundVariable?,
    override val visibility: BoundVisibility,
    val attributes: BoundBaseTypeMemberVariableAttributes,
    private val getTypeDef: () -> BoundBaseType,
    override val entryDeclaration: BaseTypeMemberVariableDeclaration,
) : BoundBaseTypeEntry<BaseTypeMemberDeclaration>, DefinitionWithVisibility {
    init {
        if (boundLocalVariableInConstructorCode == null) {
            check(entryDeclaration.variableDeclaration.type != null)
        }
    }
    val name = entryDeclaration.name.value
    override val declaredAt = entryDeclaration.span
    val isReAssignable = entryDeclaration.variableDeclaration.isReAssignable
    val isDecorated: Boolean = attributes.firstDecoratesAttribute != null
    val isConstructorParameterInitialized: Boolean = entryDeclaration.isConstructorParameterInitialized

    private val seanHelper = SeanHelper()

    /**
     * The type of this member in the context of the hosting data structure. It still needs to
     * be [BoundTypeReference.instantiateAllParameters]-ed with the type of the variable used to access
     * the hosting data structure.
     *
     * available after [semanticAnalysisPhase2]
     */
    var type: BoundTypeReference? by seanHelper.resultOfPhase2()
        private set

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        seanHelper.phase1(diagnosis) {
            visibility.validateOnElement(this, diagnosis)
            attributes.validate(diagnosis)
            if (isDecorated && !entryDeclaration.isConstructorParameterInitialized) {
                diagnosis.decoratingMemberVariableWithoutConstructorInitialization(this)
            }
            boundLocalVariableInConstructorCode?.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        seanHelper.phase2(diagnosis) {
            boundLocalVariableInConstructorCode?.semanticAnalysisPhase2(diagnosis)
            type = boundLocalVariableInConstructorCode?.typeAtDeclarationTime
                ?: entryDeclaration.variableDeclaration.type?.let(typeRootContext::resolveType)

            val typeUseSite = if (entryDeclaration.variableDeclaration.isReAssignable) {
                TypeUseSite.InvariantUsage(entryDeclaration.variableDeclaration.type?.span ?: entryDeclaration.span, this)
            } else {
                TypeUseSite.OutUsage(entryDeclaration.variableDeclaration.type?.span ?: entryDeclaration.span, this)
            }
            type?.validate(typeUseSite, diagnosis)

            if (isDecorated) {
                type?.mutability?.let { typeMutability ->
                    if (typeMutability != TypeMutability.READONLY) {
                        diagnosis.decoratingMemberVariableWithNonReadType(this, typeMutability)
                    }
                }
            }
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        seanHelper.phase3(diagnosis) {
            // the initializer expression is being analyzed by the ctor
        }
    }

    lateinit var field: BaseTypeField
        private set

    /**
     * Assures [field] is initialized. Must only be called after semantic analysis is successfully completed,
     * but before generating any IR.
     */
    fun assureFieldAllocated() {
        if (!this::field.isInitialized) {
            field = getTypeDef().allocateField(this.type!!)
        }
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        visibility.validateAccessFrom(location, this, diagnosis)
    }

    override fun toStringForErrorMessage() = "member variable ${name.quoteIdentifier()}"

    private val _backendIr by lazy {
        IrClassMemberVariableImpl(name, type!!.toBackendIr(), field.id, declaredAt)
    }
    fun toBackendIr(): IrClass.MemberVariable = _backendIr

    override fun toString() = getTypeDef().canonicalName.toString() + "." + name
}

private class IrClassMemberVariableImpl(
    override val name: String,
    override val type: IrType,
    private val fieldId: Int,
    override val declaredAt: IrSourceLocation,
) : IrClass.MemberVariable {
    override val readStrategy = object : IrClass.MemberVariable.AccessStrategy.BareField {
        override val fieldId: Int = this@IrClassMemberVariableImpl.fieldId
    }
    override val writeStrategy = readStrategy
}