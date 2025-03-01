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

    fun toException(): ReportingException = ReportingException(this)

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

    // convenience methods so that the bulky constructors of the reporting class do not have to be used
    companion object {
        fun consecutive(message: String, span: Span = Span.UNKNOWN)
            = ConsecutiveFaultDiagnostic(message, span)

        fun unexpectedEOI(expected: String, erroneousLocation: Span)
            = UnexpectedEndOfInputDiagnostic(erroneousLocation, expected)

        fun unknownType(erroneousRef: TypeReference)
            = UnknownTypeDiagnostic(erroneousRef)

        fun parsingMismatch(expected: String, actual: Token)
            = ParsingMismatchDiagnostic(listOf(expected), actual)

        fun parsingError(message: String, location: Span)
            = ParsingErrorDiagnostic(message, location)

        fun unsupported(message: String, location: Span)
            = UnsupportedFeatureDiagnostic(message, location)

        fun valueNotAssignable(targetType: BoundTypeReference, sourceType: BoundTypeReference, reason: String, assignmentLocation: Span)
            = ValueNotAssignableDiagnostic(targetType, sourceType, reason, assignmentLocation)

        fun undefinedIdentifier(expr: IdentifierToken, messageOverride: String? = null)
            = UndefinedIdentifierDiagnostic(expr, messageOverride)

        /**
         * @param acceptedDeclaration The declaration that is accepted by the compiler as the first / actual one
         * @param additionalDeclaration The erroneous declaration; is rejected (instead of accepted)
         */
        fun variableDeclaredMoreThanOnce(acceptedDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleVariableDeclarationsDiagnostic(acceptedDeclaration, additionalDeclaration)

        fun globalVariableNotInitialized(variable: BoundVariable)
            = GlobalVariableNotInitializedDiagnostic(variable.declaration)

        fun useOfUninitializedVariable(variable: BoundVariable, access: BoundIdentifierExpression, maybeInitialized: Boolean)
            = VariableAccessedBeforeInitializationDiagnostic(variable.declaration, access.declaration, maybeInitialized)

        fun parameterDeclaredMoreThanOnce(firstDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleParameterDeclarationsDiagnostic(firstDeclaration, additionalDeclaration)

        fun variableTypeNotDeclared(variable: BoundVariable)
            = MissingVariableTypeDiagnostic(variable.declaration, variable.kind)

        fun varianceOnFunctionTypeParameter(parameter: BoundTypeParameter)
            = VarianceOnFunctionTypeParameterDiagnostic(parameter.astNode)

        fun varianceOnInvocationTypeArgument(argument: BoundTypeArgument)
            = VarianceOnInvocationTypeArgumentDiagnostic(argument.astNode)

        fun missingTypeArgument(parameter: BoundTypeParameter, span: Span)
            = MissingTypeArgumentDiagnostic(parameter.astNode, span)

        fun superfluousTypeArguments(nExpectedArguments: Int, firstSuperfluousArgument: BoundTypeArgument)
            = SuperfluousTypeArgumentsDiagnostic(nExpectedArguments, firstSuperfluousArgument.astNode)

        fun typeArgumentVarianceMismatch(parameter: BoundTypeParameter, argument: BoundTypeArgument)
            = TypeArgumentVarianceMismatchDiagnostic(parameter.astNode, argument)

        fun typeArgumentVarianceSuperfluous(argument: BoundTypeArgument)
            = TypeArgumentVarianceSuperfluousDiagnostic(argument)

        fun typeArgumentOutOfBounds(parameter: BoundTypeParameter, argument: BoundTypeArgument, reason: String)
            = TypeArgumentOutOfBoundsDiagnostic(parameter.astNode, argument, reason)

        fun unsupportedTypeUsageVariance(useSite: TypeUseSite, erroneousVariance: TypeVariance)
            = UnsupportedTypeUsageVarianceDiagnostic(useSite, erroneousVariance)

        fun erroneousLiteralExpression(message: String, location: Span)
            = ErroneousLiteralExpressionDiagnostic(message, location)

        fun illegalAssignment(message: String, assignmentStatement: BoundAssignmentStatement)
            = IllegalAssignmentDiagnostic(message, assignmentStatement)

        fun illegalFunctionBody(function: FunctionDeclaration)
            = IllegalFunctionBodyDiagnostic(function)

        fun missingFunctionBody(function: FunctionDeclaration)
            = MissingFunctionBodyDiagnostic(function)

        fun inefficientAttributes(message: String, attributes: Collection<AstFunctionAttribute>)
            = ModifierInefficiencyDiagnostic(message, attributes)

        fun conflictingModifiers(attributes: Collection<AstFunctionAttribute>)
            = ConflictingFunctionModifiersDiagnostic(attributes)

        fun functionIsMissingDeclaredAttribute(fn: BoundDeclaredFunction, missingAttribute: AstFunctionAttribute, reason: String)
            = FunctionMissingDeclaredModifierDiagnostic(fn.declaration, missingAttribute, reason)

        fun toplevelFunctionWithOverrideAttribute(attr: AstFunctionAttribute.Override)
            = ToplevelFunctionWithOverrideAttributeDiagnostic(attr.attributeName)

        fun unsupportedCallingConvention(attr: AstFunctionAttribute.External, supportedConventions: Set<String>)
            = UnsupportedCallingConventionDiagnostic(attr, supportedConventions)

        fun unconventionalTypeName(name: IdentifierToken, convention: UnconventionalTypeNameDiagnostic.ViolatedConvention)
            = UnconventionalTypeNameDiagnostic(name, convention)

        fun illegalSupertype(ref: TypeReference, reason: String)
            = IllegalSupertypeDiagnostic(ref, reason)

        fun duplicateSupertype(ref: TypeReference)
            = DuplicateSupertypeDiagnostic(ref)

        fun cyclicInheritance(type: BoundBaseType, involvingSupertype: BoundSupertypeDeclaration)
            = CyclicInheritanceDiagnostic(type.declaration, involvingSupertype)

        fun duplicateBaseTypes(packageName: CanonicalElementName.Package, duplicates: List<BoundBaseType>)
            = DuplicateBaseTypesDiagnostic(packageName, duplicates.map { it.declaration })

        fun functionDoesNotOverride(function: BoundDeclaredFunction)
            = SuperFunctionForOverrideNotFoundDiagnostic(function.declaration)

        fun undeclaredOverride(function: BoundDeclaredFunction, onSupertype: BoundBaseType)
            = UndeclaredOverrideDiagnostic(function.declaration, onSupertype)

        fun staticFunctionDeclaredOverride(function: BoundDeclaredFunction)
            = StaticFunctionDeclaredOverrideDiagnostic(function.attributes.firstOverrideAttribute!!)

        fun memberFunctionImplementedOnInterface(function: BoundDeclaredBaseTypeMemberFunction)
            = MemberFunctionImplOnInterfaceDiagnostic(function.body!!.declaration.span)

        fun abstractInheritedFunctionNotImplemented(implementingType: BoundBaseType, functionToImplement: BoundMemberFunction)
            = AbstractInheritedFunctionNotImplementedDiagnostic(implementingType, functionToImplement)

        fun noMatchingFunctionOverload(functionNameReference: IdentifierToken, receiverType: BoundTypeReference?, valueArguments: List<BoundExpression<*>>, functionDeclaredAtAll: Boolean)
            = UnresolvableFunctionOverloadDiagnostic(functionNameReference, receiverType, valueArguments.map { it.type }, functionDeclaredAtAll)

        fun overloadSetHasNoDisjointParameter(overloadSet: BoundOverloadSet<*>): Diagnostic {
            val baseReporting = OverloadSetHasNoDisjointParameterDiagnostic(overloadSet)

            // hypothesis / edge case to find: the problem is created by (multiple) inheritance _only_
            val allMemberFns = overloadSet.overloads.filterIsInstance<BoundMemberFunction>()
            if (allMemberFns.size < overloadSet.overloads.size) {
                // there are top-level functions at play
                return baseReporting
            }

            val subtype = allMemberFns.first().ownerBaseType

            val onlyInheritedOverloads = allMemberFns.filter { it is InheritedBoundMemberFunction || it is PossiblyMixedInBoundMemberFunction }
            if (onlyInheritedOverloads.isEmpty() || BoundOverloadSet.areOverloadsDisjoint(onlyInheritedOverloads)) {
                // the member functions declared in the subtype clearly have an effect on the ambiguity of the overload-set
                return baseReporting
            }

            val overloadsImportedBySupertype: MutableMap<BoundBaseType?, List<BoundMemberFunction>> = allMemberFns
                .flatMap { subtypeMemberFn ->
                    if (subtypeMemberFn is InheritedBoundMemberFunction) {
                        setOf(subtypeMemberFn)
                    } else {
                        subtypeMemberFn.overrides ?: emptySet()
                    }

                }
                .groupBy { it.declaredOnType }
                .toMutableMap()
            overloadsImportedBySupertype.remove(null)
            @Suppress("UNCHECKED_CAST") // the remove(null) right before ensures exactly that
            overloadsImportedBySupertype as MutableMap<BoundBaseType, List<BoundMemberFunction>>

            val someSupertypeHasAmbiguity = overloadsImportedBySupertype.values.any {
                !BoundOverloadSet.areOverloadsDisjoint(it)
            }
            if (someSupertypeHasAmbiguity) {
                // the problem was inherited from one of the supertypes -> ignore, gets reported by the supertype
                return consecutive("overload disjoint problem inherited into ${subtype.canonicalName} from a supertype", baseReporting.span)
            }

            // the problem is created by multiple inheritance; find the subset of supertypes that creates the problem
            val supertypeOverloadsIterator = overloadsImportedBySupertype.iterator()
            while (supertypeOverloadsIterator.hasNext()) {
                val (supertype, _) = supertypeOverloadsIterator.next()
                val problemExistsWithoutThisSupertype = !BoundOverloadSet.areOverloadsDisjoint(
                    overloadsImportedBySupertype.entries.asSequence()
                        .filter { (k, _) -> k === supertype }
                        .map { (_, overloads) -> overloads }
                        .flatMap { it }
                )
                if (problemExistsWithoutThisSupertype) {
                    supertypeOverloadsIterator.remove()
                }
            }

            check(overloadsImportedBySupertype.isNotEmpty()) {
                "This means that the problem is indeed created by member functions in the subtype. But that should have been caught earlier! ${subtype.canonicalName}"
            }
            return MultipleInheritanceIssueDiagnostic(
                baseReporting,
                overloadsImportedBySupertype.keys,
                subtype,
            )
        }

        fun unresolvableConstructor(nameToken: IdentifierToken, valueArguments: List<BoundExpression<*>>, functionsWithNameAvailable: Boolean)
            = UnresolvableConstructorDiagnostic(nameToken, valueArguments.map { it.type }, functionsWithNameAvailable)

        fun unresolvableMemberVariable(accessExpression: BoundMemberAccessExpression, hostType: BoundTypeReference)
            = UnresolvedMemberVariableDiagnostic(accessExpression.declaration, hostType)

        fun unresolvablePackageName(name: CanonicalElementName.Package, location: Span)
            = UnresolvablePackageNameDiagnostic(name, location)

        fun unresolvableImport(import: BoundImportDeclaration)
            = UnresolvableImportDiagnostic(import)

        fun ambiguousImports(imports: Iterable<BoundImportDeclaration>)
            = AmbiguousImportsDiagnostic(imports.map { it.declaration }, imports.first().simpleName!!)

        fun implicitlyEvaluatingAStatement(statement: BoundExecutable<*>)
            = ImplicitlyEvaluatedStatementDiagnostic(statement.declaration)

        fun ambiguousInvocation(invocation: BoundInvocationExpression, candidates: List<BoundFunction>)
            = AmbiguousInvocationDiagnostic(invocation.declaration, candidates)

        fun typeDeductionError(message: String, location: Span)
            = TypeDeductionErrorDiagnostic(message, location)

        fun explicitInferTypeWithArguments(type: TypeReference)
            = ExplicitInferTypeWithArgumentsDiagnostic(type)

        fun explicitInferTypeNotAllowed(type: TypeReference)
            = ExplicitInferTypeNotAllowedDiagnostic(type)

        fun modifierError(message: String, location: Span)
            = ModifierErrorDiagnostic(message, location)

        fun operatorNotDeclared(message: String, expression: Expression)
            = OperatorNotDeclaredDiagnostic(message, expression)

        fun functionIsMissingAttribute(function: BoundFunction, usageRequiringModifier: Executable, missingAttribute: String)
            = FunctionMissingModifierDiagnostic(function, usageRequiringModifier, missingAttribute)

        fun externalMemberFunction(function: BoundDeclaredFunction)
            = ExternalMemberFunctionDiagnostic(function.declaration, function.attributes.externalAttribute!!.attributeName)

        fun notAllMemberVariablesInitialized(uninitializedMembers: Collection<BoundBaseTypeMemberVariable>, usedAt: Span): NotAllMemberVariablesInitializedDiagnostic {
            return NotAllMemberVariablesInitializedDiagnostic(
                uninitializedMembers.map { it.declaration },
                usedAt
            )
        }

        fun notAllMixinsInitialized(uninitializedMixins: Collection<BoundMixinStatement>, usedAt: Span)
            = ObjectUsedBeforeMixinInitializationDiagnostic(uninitializedMixins.minBy { it.declaration.span.fromLineNumber }.declaration, usedAt)

        fun useOfUninitializedMember(access: BoundMemberAccessExpression) = UseOfUninitializedClassMemberVariableDiagnostic(
            access.member!!.declaration,
            access.declaration.memberName.span,
        )

        fun constructorDeclaredAsModifying(constructor: BoundClassConstructor) = ConstructorDeclaredModifyingDiagnostic(
            constructor,
            constructor.attributes.firstModifyingAttribute!!.attributeName,
        )

        fun explicitOwnershipNotAllowed(variable: BoundVariable)
            = ExplicitOwnershipNotAllowedDiagnostic(variable.declaration.ownership!!.second)

        fun variableUsedAfterLifetime(variable: BoundVariable, read: BoundIdentifierExpression, deadState: VariableLifetime.State.Dead)
            = VariableUsedAfterLifetimeDiagnostic(variable.declaration, read.declaration.span, deadState.lifetimeEndedAt, deadState.maybe)

        fun lifetimeEndingCaptureInLoop(variable: BoundVariable, read: BoundIdentifierExpression)
            = LifetimeEndingCaptureInLoopDiagnostic(variable.declaration, read.declaration.span)

        fun borrowedVariableCaptured(variable: BoundVariable, capture: BoundIdentifierExpression)
            = BorrowedVariableCapturedDiagnostic(variable.declaration, capture.declaration.span)

        /**
         * An expression is used in a way that requires it to be non-null but the type of the expression is nullable.
         * @param nullableExpression The expression that could evaluate to null and thus case an NPE
         * @see BoundTypeReference.isExplicitlyNullable
         */
        fun unsafeObjectTraversal(nullableExpression: BoundExpression<*>, faultyAccessOperator: OperatorToken)
            = UnsafeObjectTraversalDiagnostic(nullableExpression, faultyAccessOperator)

        fun superfluousSafeObjectTraversal(nonNullExpression: BoundExpression<*>, superfluousSafeOperator: OperatorToken)
            = SuperfluousSafeObjectTraversal(nonNullExpression, superfluousSafeOperator)

        fun overrideAddsSideEffects(override: BoundMemberFunction, superFunction: BoundMemberFunction)
            = OverrideAddsSideEffectsDiagnostic(override, superFunction)

        fun overrideDropsNothrow(override: BoundMemberFunction, superFunction: BoundMemberFunction)
            = OverrideDropsNothrowDiagnostic(override, superFunction)

        fun overrideRestrictsVisibility(override: BoundMemberFunction, superFunction: BoundMemberFunction)
            = OverrideRestrictsVisibilityDiagnostic(override, superFunction)

        fun overridingParameterExtendsOwnership(override: BoundParameter, superParameter: BoundParameter)
            = ExtendingOwnershipOverrideDiagnostic(override, superParameter)

        fun nothrowViolatingInvocation(invocation: BoundInvocationExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary)
            = NothrowViolationDiagnostic.ThrowingInvocation(invocation, boundary)

        fun nothrowViolatingNotNullAssertion(assertion: BoundNotNullExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary)
            = NothrowViolationDiagnostic.NotNullAssertion(assertion.declaration, boundary)

        fun nothrowViolatingCast(cast: BoundCastExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary)
            = NothrowViolationDiagnostic.StrictCast(cast.declaration, boundary)

        fun throwStatementInNothrowContext(statement: BoundThrowExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary)
            = NothrowViolationDiagnostic.ThrowStatement(statement.declaration, boundary)

        fun constructorDeclaredNothrow(constructor: BoundClassConstructor)
            = ConstructorDeclaredNothrowDiagnostic(constructor.attributes.firstNothrowAttribute!!.sourceLocation)

        fun breakOutsideOfLoop(breakStatement: BoundBreakExpression)
            = BreakOutsideOfLoopDiagnostic(breakStatement.declaration)

        fun continueOutsideOfLoop(continueStatement: BoundContinueExpression)
            = ContinueOutsideOfLoopDiagnostic(continueStatement.declaration)

        fun missingReturnValue(returnStatement: BoundReturnExpression, expectedType: BoundTypeReference) = MissingReturnValueDiagnostic(
            returnStatement.declaration,
            expectedType,
        )

        fun uncertainTermination(function: BoundDeclaredFunction) =
            UncertainTerminationDiagnostic(function)

        fun conditionIsNotBoolean(condition: BoundExpression<*>): Diagnostic {
            val location = condition.declaration.span
            if (condition.type == null) {
                return consecutive("The condition must evaluate to Bool, cannot determine type", location)
            }

            return ConditionNotBooleanDiagnostic(condition, location)
        }

        fun typeParameterNameConflict(originalType: BoundTypeReference, conflicting: BoundTypeParameter)
            = TypeParameterNameConflictDiagnostic(originalType, conflicting)

        fun duplicateBaseTypeMembers(typeDef: BoundBaseType, duplicateMembers: Set<BoundBaseTypeMemberVariable>) =
            DuplicateBaseTypeMemberDiagnostic(typeDef, duplicateMembers)

        fun mutationInCondition(mutation: BoundExecutable<*>)
            = MutationInConditionDiagnostic(mutation.declaration)

        fun incorrectPackageDeclaration(name: AstPackageName, expected: CanonicalElementName.Package)
            = IncorrectPackageDeclarationDiagnostic(name, expected)

        fun integerLiteralOutOfRange(literal: Expression, expectedType: BoundBaseType, expectedRange: ClosedRange<BigInteger>)
            = IntegerLiteralOutOfRangeDiagnostic(literal, expectedType, expectedRange)

        fun multipleClassConstructors(additionalCtors: Collection<BaseTypeConstructorDeclaration>)
            = MultipleClassConstructorsDiagnostic(additionalCtors)

        fun mixinNotAllowed(mixin: BoundMixinStatement)
            = MixinNotAllowedDiagnostic(mixin.declaration)

        fun illegalMixinRepetition(mixin: BoundMixinStatement, repetition: ExecutionScopedCTContext.Repetition)
            = IllegalMixinRepetitionDiagnostic(mixin.declaration, repetition)

        fun unusedMixin(mixin: BoundMixinStatement)
            = UnusedMixinDiagnostic(mixin.declaration)

        fun multipleClassDestructors(additionalDtors: Collection<BaseTypeDestructorDeclaration>)
            = MultipleClassDestructorsDiagnostic(additionalDtors)

        fun entryNotAllowedOnBaseType(baseType: BoundBaseType, entry: BoundBaseTypeEntry<*>)
            = EntryNotAllowedInBaseTypeDiagnostic(baseType.kind, entry)

        fun elementNotAccessible(element: DefinitionWithVisibility, visibility: BoundVisibility, accessAt: Span)
            = ElementNotAccessibleDiagnostic(element, visibility, accessAt)

        fun missingModuleDependency(element: DefinitionWithVisibility, accessAt: Span, moduleOfAccessedElement: CanonicalElementName.Package, moduleOfAccess: CanonicalElementName.Package)
            = MissingModuleDependencyDiagnostic(element, accessAt, moduleOfAccessedElement, moduleOfAccess)

        fun visibilityTooBroad(owningModule: CanonicalElementName.Package, visibilityDeclaration: BoundVisibility.PackageScope)
            = PackageVisibilityTooBroadDiagnostic(owningModule, visibilityDeclaration.packageName, visibilityDeclaration.astNode.sourceLocation)

        fun visibilityNotAllowedOnVariable(variable: BoundVariable)
            = VisibilityNotAllowedOnVariableDiagnostic(variable)

        fun visibilityShadowed(element: DefinitionWithVisibility, contextVisibility: BoundVisibility)
            = ShadowedVisibilityDiagnostic(element, contextVisibility)

        fun hiddenTypeExposed(type: BoundBaseType, exposedBy: DefinitionWithVisibility, exposedAt: Span)
            = HiddenTypeExposedDiagnostic(type, exposedBy, exposedAt)

        fun forbiddenCast(castOp: BoundCastExpression, reason: String, span: Span = castOp.declaration.span)
            = ForbiddenCastDiagnostic(castOp.declaration, reason, span)

        fun unsupportedReflection(onType: BoundTypeReference)
            = UnsupportedTypeReflectionException(onType.span ?: Span.UNKNOWN)

        fun typeCheckOnVolatileTypeParameter(node: BoundExpression<*>, typeToCheck: BoundTypeReference)
            = TypeCheckOnVolatileTypeParameterDiagnostic(typeToCheck.span ?: node.declaration.span)

        fun nullCheckOnNonNullableValue(value: BoundExpression<*>)
            = NullCheckingNonNullableValueDiagnostic(value.declaration)

        fun readingPurityViolationToReporting(violation: BoundExpression<*>, boundary: PurityViolationDiagnostic.SideEffectBoundary): Diagnostic {
            if (violation is BoundIdentifierExpression) {
                return ReadInPureContextDiagnostic(violation, boundary)
            }
            check(violation is BoundInvocationExpression)
            return ImpureInvocationInPureContextDiagnostic(violation, boundary)
        }

        fun modifyingPurityViolationToReporting(violation: BoundExecutable<*>, boundary: PurityViolationDiagnostic.SideEffectBoundary): Diagnostic {
            if (violation is BoundAssignmentStatement) {
                return AssignmentOutsideOfPurityBoundaryDiagnostic(violation, boundary)
            }

            if (violation is BoundIdentifierExpression) {
                return MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic(violation, boundary)
            }

            check(violation is BoundInvocationExpression)
            if (violation.functionToInvoke?.purity?.contains(BoundFunction.Purity.MODIFYING) == true) {
                return ModifyingInvocationInReadonlyContextDiagnostic(violation, boundary)
            } else {
                return ImpureInvocationInPureContextDiagnostic(violation, boundary)
            }
        }
    }
}