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

package compiler.reportings

import compiler.ast.ASTPackageName
import compiler.ast.AstFunctionAttribute
import compiler.ast.ClassConstructorDeclaration
import compiler.ast.Expression
import compiler.ast.FunctionDeclaration
import compiler.ast.VariableDeclaration
import compiler.ast.expression.IdentifierExpression
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundAssignmentStatement
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.BoundImportDeclaration
import compiler.binding.BoundReturnStatement
import compiler.binding.BoundStatement
import compiler.binding.BoundVariable
import compiler.binding.classdef.BoundClassConstructor
import compiler.binding.classdef.BoundClassDefinition
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.binding.context.effect.VariableLifetime
import compiler.binding.expression.*
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.lexer.IdentifierToken
import compiler.lexer.OperatorToken
import compiler.lexer.SourceLocation
import compiler.lexer.Token
import io.github.tmarsteel.emerge.backend.api.DotName
import textutils.indentByFromSecondLine
import java.math.BigInteger

/**
 * TODO: rename to Diagnostic
 * TODO: replace the mutableSetOf(), addAll return shit with something actually efficient
 */
abstract class Reporting internal constructor(
    val level: Level,
    open val message: String,
    val sourceLocation: SourceLocation
) : Comparable<Reporting>
{
    override fun compareTo(other: Reporting): Int {
        return level.compareTo(other.level)
    }

    fun toException(): ReportingException = ReportingException(this)

    protected val levelAndMessage: String get() = "($level) $message".indentByFromSecondLine(2)

    /**
     * TODO: currently, all subclasses must override this with super.toString(), because `data` is needed to detect double-reporting the same problem
     */
    override fun toString() = "$levelAndMessage\nin $sourceLocation"

    enum class Level(val level: Int) {
        CONSECUTIVE(0),
        INFO(10),
        WARNING(20),
        ERROR(30);
    }

    // convenience methods so that the bulky constructors of the reporting class do not have to be used
    companion object {
        fun consecutive(message: String, sourceLocation: SourceLocation = SourceLocation.UNKNOWN)
            = ConsecutiveFaultReporting(message, sourceLocation)

        fun unexpectedEOI(expected: String, erroneousLocation: SourceLocation)
            = UnexpectedEndOfInputReporting(erroneousLocation, expected)

        fun unknownType(erroneousRef: TypeReference)
            = UnknownTypeReporting(erroneousRef)

        fun mismatch(expected: String, actual: String, location: SourceLocation)
            = ParsingMismatchReporting(expected, actual, location)

        fun mismatch(expected: String, actual: Token)
            = mismatch(expected, actual.toStringWithoutLocation(), actual.sourceLocation)

        fun parsingError(message: String, location: SourceLocation)
            = ParsingErrorReporting(message, location)

        fun unsupported(message: String, location: SourceLocation)
            = UnsupportedFeatureReporting(message, location)

        fun valueNotAssignable(targetType: BoundTypeReference, sourceType: BoundTypeReference, reason: String, assignmentLocation: SourceLocation)
            = ValueNotAssignableReporting(targetType, sourceType, reason, assignmentLocation)

        fun undefinedIdentifier(expr: IdentifierExpression, messageOverride: String? = null)
            = UndefinedIdentifierReporting(expr, messageOverride)

        /**
         * @param acceptedDeclaration The declaration that is accepted by the compiler as the first / actual one
         * @param additionalDeclaration The erroneous declaration; is rejected (instead of accepted)
         */
        fun variableDeclaredMoreThanOnce(acceptedDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleVariableDeclarationsReporting(acceptedDeclaration, additionalDeclaration)

        fun globalVariableNotInitialized(variable: BoundVariable)
            = GlobalVariableNotInitializedReporting(variable.declaration)

        fun useOfUninitializedVariable(variable: BoundVariable, access: BoundIdentifierExpression, maybeInitialized: Boolean)
            = VariableAccessedBeforeInitializationReporting(variable.declaration, access.declaration, maybeInitialized)

        fun parameterDeclaredMoreThanOnce(firstDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleParameterDeclarationsReporting(firstDeclaration, additionalDeclaration)

        fun variableTypeNotDeclared(variable: BoundVariable)
            = MissingVariableTypeReporting(variable.declaration, variable.kind)

        fun varianceOnFunctionTypeParameter(parameter: BoundTypeParameter)
            = VarianceOnFunctionTypeParameterReporting(parameter.astNode)

        fun missingTypeArgument(parameter: BoundTypeParameter, sourceLocation: SourceLocation)
            = MissingTypeArgumentReporting(parameter.astNode, sourceLocation)

        fun superfluousTypeArguments(nExpectedArguments: Int, firstSuperfluousArgument: BoundTypeArgument)
            = SuperfluousTypeArgumentsReporting(nExpectedArguments, firstSuperfluousArgument.astNode)

        fun typeArgumentVarianceMismatch(parameter: BoundTypeParameter, argument: BoundTypeArgument)
            = TypeArgumentVarianceMismatchReporting(parameter.astNode, argument)

        fun typeArgumentVarianceSuperfluous(argument: BoundTypeArgument)
            = TypeArgumentVarianceSuperfluousReporting(argument)

        fun typeArgumentOutOfBounds(parameter: BoundTypeParameter, argument: BoundTypeArgument, reason: String)
            = TypeArgumentOutOfBoundsReporting(parameter.astNode, argument, reason)

        fun unsupportedTypeUsageVariance(useSite: TypeUseSite, erroneousVariance: TypeVariance)
            = UnsupportedTypeUsageVarianceReporting(useSite, erroneousVariance)

        fun erroneousLiteralExpression(message: String, location: SourceLocation)
            = ErroneousLiteralExpressionReporting(message, location)

        fun illegalAssignment(message: String, assignmentStatement: BoundAssignmentStatement)
            = IllegalAssignmentReporting(message, assignmentStatement)

        fun illegalFunctionBody(function: FunctionDeclaration)
            = IllegalFunctionBodyReporting(function)

        fun missingFunctionBody(function: FunctionDeclaration)
            = MissingFunctionBodyReporting(function)

        fun inefficientAttributes(message: String, attributes: Collection<AstFunctionAttribute>)
            = ModifierInefficiencyReporting(message, attributes)

        fun conflictingModifiers(attributes: Collection<AstFunctionAttribute>)
            = ConflictingFunctionModifiersReporting(attributes)

        fun noMatchingFunctionOverload(functionNameReference: IdentifierToken, receiverType: BoundTypeReference?, valueArguments: List<BoundExpression<*>>, functionDeclaredAtAll: Boolean)
            = UnresolvableFunctionOverloadReporting(functionNameReference, receiverType, valueArguments.map { it.type }, functionDeclaredAtAll)

        fun unresolvableConstructor(nameToken: IdentifierToken, valueArguments: List<BoundExpression<*>>, functionsWithNameAvailable: Boolean)
            = UnresolvableConstructorReporting(nameToken, valueArguments.map { it.type }, functionsWithNameAvailable)

        fun unresolvableMemberVariable(accessExpression: BoundMemberAccessExpression, hostType: BoundTypeReference)
            = UnresolvedMemberVariableReporting(accessExpression.declaration, hostType)

        fun unresolvablePackageName(name: DotName, location: SourceLocation)
            = UnresolvablePackageNameReporting(name, location)

        fun unresolvableImport(import: BoundImportDeclaration)
            = UnresolvableImportReporting(import)

        fun ambiguousImports(imports: Iterable<BoundImportDeclaration>)
            = AmbiguousImportsReporting(imports.map { it.declaration }, imports.first().simpleName!!)

        fun implicitlyEvaluatingAStatement(statement: BoundStatement<*>)
            = ImplicitlyEvaluatedStatementReporting(statement.declaration)

        fun ambiguousInvocation(invocation: BoundInvocationExpression, candidates: List<BoundFunction>)
            = AmbiguousInvocationReporting(invocation.declaration, candidates)

        fun typeDeductionError(message: String, location: SourceLocation)
            = TypeDeductionErrorReporting(message, location)

        fun explicitInferTypeWithArguments(type: TypeReference)
            = ExplicitInferTypeWithArgumentsReporting(type)

        fun explicitInferTypeNotAllowed(type: TypeReference)
            = ExplicitInferTypeNotAllowedReporting(type)

        fun modifierError(message: String, location: SourceLocation)
            = ModifierErrorReporting(message, location)

        fun operatorNotDeclared(message: String, expression: Expression)
            = OperatorNotDeclaredReporting(message, expression)

        fun functionIsMissingAttribute(function: BoundFunction, usageRequiringModifier: Expression, missingAttribute: String)
            = FunctionMissingModifierReporting(function, usageRequiringModifier, missingAttribute)

        fun objectNotFullyInitialized(uninitializedMembers: Collection<BoundClassMemberVariable>, usedAt: SourceLocation): ObjectNotFullyInitializedReporting {
            return ObjectNotFullyInitializedReporting(
                uninitializedMembers.map { it.declaration },
                usedAt
            )
        }

        fun useOfUninitializedMember(access: BoundMemberAccessExpression) = UseOfUninitializedClassMemberVariableReporting(
            access.member!!.declaration,
            access.declaration.memberName.sourceLocation,
        )

        fun constructorDeclaredAsModifying(constructor: BoundClassConstructor) = ConstructorDeclaredModifyingReporting(
            constructor,
            constructor.attributes.firstModifyingAttribute!!.attributeName,
        )

        fun explicitOwnershipNotAllowed(variable: BoundVariable)
            = ExplicitOwnershipNotAllowedReporting(variable.declaration.ownership!!.second)

        fun variableUsedAfterLifetime(variable: BoundVariable, read: BoundIdentifierExpression, deadState: VariableLifetime.State.Dead)
            = VariableUsedAfterLifetimeReporting(variable.declaration, read.declaration.sourceLocation, deadState.lifetimeEndedAt, deadState.maybe)

        fun borrowedVariableCaptured(variable: BoundVariable, capture: BoundIdentifierExpression)
            = BorrowedVariableCapturedReporting(variable.declaration, capture.declaration.sourceLocation)

        /**
         * An expression is used in a way that requires it to be non-null but the type of the expression is nullable.
         * @param nullableExpression The expression that could evaluate to null and thus case an NPE
         * @see BoundTypeReference.isExplicitlyNullable
         */
        fun unsafeObjectTraversal(nullableExpression: BoundExpression<*>, faultyAccessOperator: OperatorToken)
            = UnsafeObjectTraversalReporting(nullableExpression, faultyAccessOperator)

        fun superfluousSafeObjectTraversal(nonNullExpression: BoundExpression<*>, superfluousSafeOperator: OperatorToken)
            = SuperfluousSafeObjectTraversal(nonNullExpression, superfluousSafeOperator)

        fun purityViolations(readingViolations: Collection<BoundExpression<*>>, writingViolations: Collection<BoundStatement<*>>, context: BoundFunction): Collection<Reporting> {
            val boundary = PurityViolationReporting.Boundary.Function(context)
            return readingViolations.map { readingPurityViolationToReporting(it, boundary) } + writingViolations.map { modifyingPurityViolationToReporting(it, boundary) }
        }

        fun purityViolations(readingViolations: Collection<BoundExpression<*>>, writingViolations: Collection<BoundStatement<*>>, context: BoundClassMemberVariable): Collection<Reporting> {
            val boundary = PurityViolationReporting.Boundary.ClassMemberInitializer(context)
            return readingViolations.map { readingPurityViolationToReporting(it, boundary) } + writingViolations.map { modifyingPurityViolationToReporting(it, boundary) }
        }

        fun readonlyViolations(writingViolations: Collection<BoundStatement<*>>, readonlyFunction: BoundFunction): Collection<Reporting> {
            return purityViolations(emptySet(), writingViolations, readonlyFunction)
        }

        fun missingReturnValue(returnStatement: BoundReturnStatement, expectedType: BoundTypeReference) = MissingReturnValueReporting(
            returnStatement.declaration,
            expectedType,
        )

        fun uncertainTermination(function: BoundFunction) =
            UncertainTerminationReporting(function)

        fun conditionIsNotBoolean(condition: BoundExpression<*>, location: SourceLocation): Reporting {
            if (condition.type == null) {
                return consecutive("The condition must evaluate to Boolean, cannot determine type", location)
            }

            return ConditionNotBooleanReporting(condition, location)
        }

        fun typeParameterNameConflict(originalType: BoundTypeReference, conflicting: BoundTypeParameter)
            = TypeParameterNameConflictReporting(originalType, conflicting)

        fun duplicateTypeMembers(classDef: BoundClassDefinition, duplicateMembers: Set<BoundClassMemberVariable>) =
            DuplicateClassMemberReporting(classDef, duplicateMembers)

        fun assignmentUsedAsExpression(assignment: BoundAssignmentStatement)
            = AssignmenUsedAsExpressionReporting(assignment.declaration)

        fun mutationInCondition(mutation: BoundExecutable<*>)
            = MutationInConditionReporting(mutation.declaration)

        fun incorrectPackageDeclaration(name: ASTPackageName, expected: DotName)
            = IncorrectPackageDeclarationReporting(name, expected)

        fun integerLiteralOutOfRange(literal: Expression, expectedType: BaseType, expectedRange: ClosedRange<BigInteger>)
            = IntegerLiteralOutOfRangeReporting(literal, expectedType, expectedRange)

        fun multipleClassConstructors(additionalCtors: Collection<ClassConstructorDeclaration>)
            = MultipleClassConstructorsReporting(additionalCtors)

        private fun readingPurityViolationToReporting(violation: BoundExpression<*>, boundary: PurityViolationReporting.Boundary): Reporting {
            if (violation is BoundIdentifierExpression) {
                return ReadInPureContextReporting(violation, boundary)
            }
            check(violation is BoundInvocationExpression)
            return ImpureInvocationInPureContextReporting(violation, boundary)
        }

        private fun modifyingPurityViolationToReporting(violation: BoundStatement<*>, boundary: PurityViolationReporting.Boundary): Reporting {
            if (violation is BoundAssignmentStatement) {
                return StateModificationOutsideOfPurityBoundaryReporting(violation, boundary)
            }

            check(violation is BoundInvocationExpression)
            if (violation.dispatchedFunction?.attributes?.isDeclaredReadonly == false) {
                return ModifyingInvocationInReadonlyContextReporting(violation, boundary)
            } else {
                return ImpureInvocationInPureContextReporting(violation, boundary)
            }
        }
    }
}