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

import compiler.InternalCompilerError
import compiler.ast.Executable
import compiler.ast.FunctionDeclaration
import compiler.ast.VariableDeclaration
import compiler.ast.expression.Expression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.expression.*
import compiler.binding.struct.Struct
import compiler.binding.struct.StructMember
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.ResolvedTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.OperatorToken
import compiler.lexer.SourceLocation
import compiler.lexer.Token
import textutils.indentByFromSecondLine

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

    override fun toString() = "($level) $message".indentByFromSecondLine(2) + "\nin $sourceLocation"

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

        fun valueNotAssignable(targetType: ResolvedTypeReference, sourceType: ResolvedTypeReference, reason: String, assignmentLocation: SourceLocation)
            = ValueNotAssignableReporting(targetType, sourceType, reason, assignmentLocation)

        fun undefinedIdentifier(expr: IdentifierExpression, messageOverride: String? = null)
            = UndefinedIdentifierReporting(expr, messageOverride)

        /**
         * @param acceptedDeclaration The declaration that is accepted by the compiler as the first / actual one
         * @param additionalDeclaration The erroneous declaration; is rejected (instead of accepted)
         */
        fun variableDeclaredMoreThanOnce(acceptedDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleVariableDeclarationsReporting(acceptedDeclaration, additionalDeclaration)

        fun variableDeclaredWithSplitType(declaration: VariableDeclaration)
            = VariableDeclaredWithSplitTypeReporting(declaration)

        fun parameterDeclaredMoreThanOnce(firstDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleParameterDeclarationsReporting(firstDeclaration, additionalDeclaration)

        fun parameterTypeNotDeclared(declaration: VariableDeclaration)
            = MissingParameterTypeReporting(declaration)

        fun varianceOnFunctionTypeParameter(parameter: TypeParameter)
            = VarianceOnFunctionTypeParameterReporting(parameter)

        fun typeArgumentCountMismatch(type: RootResolvedTypeReference)
            = TypeArgumentCountMismatchReporting(type, type.baseType)

        fun typeArgumentVarianceMismatch(parameter: TypeParameter, argument: BoundTypeArgument)
            = TypeArgumentVarianceMismatchReporting(parameter, argument)

        fun typeArgumentVarianceSuperfluous(argument: BoundTypeArgument)
            = TypeArgumentVarianceSuperfluousReporting(argument)

        fun typeArgumentOutOfBounds(parameter: TypeParameter, argument: BoundTypeArgument, reason: String)
            = TypeArgumentOutOfBoundsReporting(parameter, argument, reason)

        fun erroneousLiteralExpression(message: String, location: SourceLocation)
            = ErroneousLiteralExpressionReporting(message, location)

        fun illegalAssignment(message: String, assignmentStatement: BoundAssignmentExpression)
            = IllegalAssignmentReporting(message, assignmentStatement)

        fun illegalFunctionBody(function: FunctionDeclaration)
            = IllegalFunctionBodyReporting(function)

        fun missingFunctionBody(function: FunctionDeclaration)
            = MissingFunctionBodyReporting(function)

        fun inefficientModifiers(message: String, location: SourceLocation)
            = ModifierInefficiencyReporting(message, location)

        fun noMatchingFunctionOverload(functionNameReference: IdentifierToken, receiverType: ResolvedTypeReference?, forTypes: List<ResolvedTypeReference?>, functionDeclaredAtAll: Boolean)
            = UnresolvableFunctionOverloadReporting(functionNameReference, receiverType, forTypes, functionDeclaredAtAll)

        fun unresolvableConstructor(nameToken: IdentifierToken, parameterTypes: List<ResolvedTypeReference?>, functionsWithNameAvailable: Boolean)
            = UnresolvableConstructorReporting(nameToken, parameterTypes, functionsWithNameAvailable)

        fun unresolvableMemberVariable(accessExpression: BoundMemberAccessExpression, hostType: ResolvedTypeReference)
            = UnresolvedMemberVariableReporting(accessExpression.declaration, hostType)

        fun ambiguousInvocation(invocation: BoundInvocationExpression, candidates: List<BoundFunction>)
            = AmbiguousInvocationReporting(invocation.declaration, candidates)

        fun typeDeductionError(message: String, location: SourceLocation)
            = TypeDeductionErrorReporting(message, location)

        fun modifierError(message: String, location: SourceLocation)
            = ModifierErrorReporting(message, location)

        fun operatorNotDeclared(message: String, expression: Expression<*>)
            = OperatorNotDeclaredReporting(message, expression)

        fun functionIsMissingModifier(function: BoundFunction, usageRequiringModifier: Expression<*>, missingModifier: FunctionModifier)
            = FunctionMissingModifierReporting(function, usageRequiringModifier, missingModifier)

        /**
         * An expression is used in a way that requires it to be non-null but the type of the expression is nullable.
         * @param nullableExpression The expression that could evaluate to null and thus case an NPE
         * @see ResolvedTypeReference.isExplicitlyNullable
         */
        fun unsafeObjectTraversal(nullableExpression: BoundExpression<*>, faultyAccessOperator: OperatorToken)
            = UnsafeObjectTraversalException(nullableExpression, faultyAccessOperator)

        fun superfluousSafeObjectTraversal(nonNullExpression: BoundExpression<*>, superfluousSafeOperator: OperatorToken)
            = SuperfluousSafeObjectTraversal(nonNullExpression, superfluousSafeOperator)

        fun purityViolations(readingViolations: Collection<BoundExecutable<Executable<*>>>, writingViolations: Collection<BoundExecutable<Executable<*>>>, context: BoundFunction): Collection<Reporting> {
            return (readingViolations + writingViolations).map { purityOrReadonlyViolationToReporting(it, context) }
        }

        fun readonlyViolations(writingViolations: Collection<BoundExecutable<Executable<*>>>, readonlyFunction: BoundFunction): Collection<Reporting> {
            return writingViolations.map { violator ->
                purityOrReadonlyViolationToReporting(violator, readonlyFunction)
            }
        }

        fun uncertainTermination(function: BoundFunction) =
            UncertainTerminationReporting(function)

        fun conditionIsNotBoolean(condition: BoundExpression<*>, location: SourceLocation): Reporting {
            if (condition.type == null) {
                return consecutive("The condition must evaluate to Boolean, cannot determine type", location)
            }

            return ConditionNotBooleanReporting(condition, location)
        }

        fun duplicateTypeMembers(struct: Struct, duplicateMembers: Set<StructMember>) =
            DuplicateStructMemberReporting(struct, duplicateMembers)

        fun assignmentInCondition(assignment: BoundAssignmentExpression)
            = AssignmentInConditionReporting(assignment.declaration)

        fun mutationInCondition(mutation: BoundExecutable<*>)
            = MutationInConditionReporting(mutation.declaration)

        /**
         * Converts a violation of purity or readonlyness into an appropriate error.
         * @param violationIsWrite Whether the violiation is a writing violation or a reading violation (true = writing, false = reading)
         */
        private fun purityOrReadonlyViolationToReporting(violation: BoundExecutable<Executable<*>>, context: BoundFunction): Reporting {
            // violations can only be variable reads + writes as well as function invocations
            if (violation is BoundIdentifierExpression) {
                if (FunctionModifier.PURE !in context.modifiers) throw InternalCompilerError("This is not a purity violation")
                return ReadInPureContextReporting(violation, context)
            }
            else if (violation is BoundInvocationExpression) {
                if (FunctionModifier.PURE in context.modifiers) {
                    return ImpureInvocationInPureContextReporting(violation, context)
                }
                else {
                    return ModifyingInvocationInReadonlyContextReporting(violation, context)
                }
            }
            else if (violation is BoundAssignmentExpression) {
                return StateModificationOutsideOfPurityBoundaryReporting(violation, context)
            }

            throw InternalCompilerError("Cannot handle ${violation.javaClass.simpleName} as a purity or readonlyness violation")
        }
    }
}