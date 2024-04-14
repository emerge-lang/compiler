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

import compiler.OnceAction
import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.BaseTypeDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.CodeChunk
import compiler.binding.BoundElement
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVisibility
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import kotlinext.duplicatesBy

class BoundBaseTypeDefinition(
    private val fileContext: CTContext,
    private val typeRootContext: CTContext,
    val kind: Kind,
    override val visibility: BoundVisibility,
    override val typeParameters: List<BoundTypeParameter>,
    override val superTypes: BoundSupertypeList,
    override val declaration: BaseTypeDeclaration,
    val entries: List<BoundBaseTypeEntry<*>>,
) : BaseType, BoundElement<BaseTypeDeclaration> {
    private val onceAction = OnceAction()

    override val context: CTContext = fileContext
    override val canonicalName by lazy {
        CanonicalElementName.BaseType(context.sourceFile.packageName, declaration.name.value)
    }
    override val simpleName: String = declaration.name.value

    val memberVariables: List<BoundBaseTypeMemberVariable> = entries.filterIsInstance<BoundBaseTypeMemberVariable>()
    val declaredConstructors: Sequence<BoundClassConstructor> = entries.asSequence().filterIsInstance<BoundClassConstructor>()
    val declaredDestructors: Sequence<BoundClassDestructor> = entries.asSequence().filterIsInstance<BoundClassDestructor>()

    val memberFunctionsByName: Map<String, Collection<BoundOverloadSet<BoundMemberFunction>>> by lazy {
        entries.filterIsInstance<BoundDeclaredBaseTypeMemberFunction>()
            .groupBy { it.name }
            .mapValues { (name, overloadsSameName) ->
                overloadsSameName
                    .groupBy { it.parameters.parameters.size }
                    .map { (parameterCount, overloads) ->
                        val overloadSetCanonicalName = CanonicalElementName.Function(
                            this@BoundBaseTypeDefinition.canonicalName,
                            name,
                        )
                        BoundOverloadSet(overloadSetCanonicalName, parameterCount, overloads)
                    }
            }
    }

    /**
     * Always `null` if [Kind.hasCtorsAndDtors] is `false`. If `true`, is initialized in
     * [semanticAnalysisPhase1] to a given declaration or a generated one.
     */
    override var constructor: BoundClassConstructor? = null
        private set

    /**
     * Always `null` if [Kind.hasCtorsAndDtors] is `false`. If `true`, is initialized in
     * [semanticAnalysisPhase1] to a given declaration or a generated one.
     */
    override var destructor: BoundClassDestructor? = null
        private set

    override val memberFunctions: Collection<BoundOverloadSet<BoundMemberFunction>>
        get() = memberFunctionsByName.values.flatten()
    override fun resolveMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> = memberFunctionsByName[name] ?: emptySet()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            typeParameters.flatMap { it.semanticAnalysisPhase1() }.forEach(reportings::add)
            reportings.addAll(superTypes.semanticAnalysisPhase1())

            entries.forEach {
                reportings.addAll(it.semanticAnalysisPhase1())
            }
            memberFunctionsByName.values.asSequence().flatten().forEach {
                reportings.addAll(it.semanticAnalysisPhase1())
            }

            memberVariables.duplicatesBy(BoundBaseTypeMemberVariable::name).forEach { (_, dupMembers) ->
                reportings.add(Reporting.duplicateBaseTypeMembers(this, dupMembers))
            }
            if (!kind.allowsMemberVariables) {
                memberVariables.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
            }

            if (kind.hasCtorsAndDtors) {
                declaredConstructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> reportings.add(Reporting.multipleClassConstructors(list.map { it.declaration })) }

                declaredDestructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> reportings.add(Reporting.multipleClassDestructors(list.map { it.declaration })) }

                if (declaredConstructors.none()) {
                    val defaultCtorAst = BaseTypeConstructorDeclaration(emptyList(), IdentifierToken("constructor", declaration.declaredAt), CodeChunk(emptyList()))
                    // TODO: maybe has to be bound to fileContextWithTypeParameters
                    constructor = defaultCtorAst.bindTo(typeRootContext, typeParameters) { this }
                    reportings.addAll(constructor!!.semanticAnalysisPhase1())
                } else {
                    constructor = declaredConstructors.first()
                }
                if (declaredDestructors.none()) {
                    val defaultDtorAst = BaseTypeDestructorDeclaration(IdentifierToken("destructor", declaration.declaredAt), CodeChunk(emptyList()))
                    // TODO: maybe has to be bound to fileContextWithTypeParameters
                    destructor = defaultDtorAst.bindTo(typeRootContext, typeParameters) { this }
                    reportings.addAll(destructor!!.semanticAnalysisPhase1())
                } else {
                    destructor = declaredDestructors.first()
                }
            } else {
                declaredConstructors.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
                declaredDestructors.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
            }

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = entries.flatMap { it.semanticAnalysisPhase2() }.toMutableList()

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase2).forEach(reportings::addAll)
            reportings.addAll(superTypes.semanticAnalysisPhase2())
            entries.map(BoundBaseTypeEntry<*>::semanticAnalysisPhase2).forEach(reportings::addAll)
            memberFunctionsByName.values.asSequence().flatten().forEach {
                reportings.addAll(it.semanticAnalysisPhase2())
            }
            constructor?.semanticAnalysisPhase2()?.let(reportings::addAll)
            destructor?.semanticAnalysisPhase2()?.let(reportings::addAll)

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = entries.flatMap { it.semanticAnalysisPhase3() }.toMutableList()

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase3).forEach(reportings::addAll)
            reportings.addAll(superTypes.semanticAnalysisPhase3())
            entries.map(BoundBaseTypeEntry<*>::semanticAnalysisPhase3).forEach(reportings::addAll)
            memberFunctionsByName.values.asSequence().flatten().forEach {
                reportings.addAll(it.semanticAnalysisPhase3())
            }
            constructor?.semanticAnalysisPhase3()?.let(reportings::addAll)
            destructor?.semanticAnalysisPhase3()?.let(reportings::addAll)

            return@getResult reportings
        }
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "class $simpleName"

    override fun resolveMemberVariable(name: String): BoundBaseTypeMemberVariable? = memberVariables.find { it.name == name }

    private val backendIr by lazy { kind.toBackendIr(this) }
    override fun toBackendIr(): IrBaseType = backendIr

    enum class Kind(
        val namePlural: String,
        val hasCtorsAndDtors: Boolean,
        val allowsMemberVariables: Boolean,
        val memberFunctionsAbstractByDefault: Boolean,
    ) {
        CLASS("classes", hasCtorsAndDtors = true, allowsMemberVariables = true, memberFunctionsAbstractByDefault = false),
        INTERFACE("interfaces", hasCtorsAndDtors = false, allowsMemberVariables = false, memberFunctionsAbstractByDefault = true),
        ;

        fun toBackendIr(typeDef: BoundBaseTypeDefinition): IrBaseType = when(this) {
            CLASS -> IrClassImpl(typeDef)
            INTERFACE -> IrInterfaceImpl(typeDef)
        }
    }
}

private class IrInterfaceImpl(
    typeDef: BoundBaseTypeDefinition,
) : IrInterface {
    override val canonicalName: CanonicalElementName.BaseType = typeDef.canonicalName
    override val parameters = typeDef.typeParameters.map { it.toBackendIr() }
    override val memberFunctions by lazy { typeDef.memberFunctionsByName.values.flatten().map { it.toBackendIr() } }
}

private class IrClassImpl(
    typeDef: BoundBaseTypeDefinition,
) : IrClass {
    override val canonicalName: CanonicalElementName.BaseType = typeDef.canonicalName
    override val parameters = typeDef.typeParameters.map { it.toBackendIr() }
    override val memberVariables by lazy { typeDef.memberVariables.map { it.toBackendIr() } }
    override val memberFunctions by lazy { typeDef.memberFunctionsByName.values.flatten().map { it.toBackendIr() } }
    override val constructor by lazy { typeDef.constructor!!.toBackendIr() }
    override val destructor by lazy { typeDef.destructor!!.toBackendIr() }
}