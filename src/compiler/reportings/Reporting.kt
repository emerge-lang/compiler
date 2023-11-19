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
import compiler.ast.expression.InvocationExpression
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.binding.BoundAssignmentStatement
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.struct.Struct
import compiler.binding.struct.StructMember
import compiler.binding.type.BaseTypeReference
import compiler.lexer.OperatorToken
import compiler.lexer.SourceLocation
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

        fun parsingError(message: String, location: SourceLocation)
            = ParsingErrorReporting(message, location)

        fun unsupported(message: String, location: SourceLocation)
            = UnsupportedFeatureReporting(message, location)

        fun typeMismatch(targetType: BaseTypeReference, sourceType: BaseTypeReference, location: SourceLocation)
            = TypeMismatchReporting(targetType, sourceType, location)

        fun returnTypeMismatch(expectedReturnType: BaseTypeReference, returnedType: BaseTypeReference, location: SourceLocation)
            = ReturnTypeMismatchReporting(expectedReturnType, returnedType, location)

        fun undefinedIdentifier(expr: IdentifierExpression, messageOverride: String? = null)
            = UndefinedIdentifierReporting(expr, messageOverride)

        /**
         * @param acceptedDeclaration The declaration that is accepted by the compiler as the first / actual one
         * @param additionalDeclaration The erroneous declaration; is rejected (instead of accepted)
         */
        fun variableDeclaredMoreThanOnce(acceptedDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleVariableDeclarationsReporting(acceptedDeclaration, additionalDeclaration)

        fun parameterDeclaredMoreThanOnce(firstDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration)
            = MultipleParameterDeclarationsReporting(firstDeclaration, additionalDeclaration)

        fun parameterTypeNotDeclared(declaration: VariableDeclaration)
            = MissingParameterTypeReporting(declaration)

        fun erroneousLiteralExpression(message: String, location: SourceLocation)
            = ErroneousLiteralExpressionReporting(message, location)

        fun illegalAssignment(message: String, assignmentStatement: BoundAssignmentStatement)
            = IllegalAssignmentReporting(message, assignmentStatement)

        fun illegalFunctionBody(function: FunctionDeclaration)
            = IllegalFunctionBodyReporting(function)

        fun missingFunctionBody(function: FunctionDeclaration)
            = MissingFunctionBodyReporting(function)

        fun inefficientModifiers(message: String, location: SourceLocation)
            = ModifierInefficiencyReporting(message, location)

        fun unresolvableFunction(expr: BoundInvocationExpression): Reporting {
            // if the receiver type could not be inferred, this is might be a consecutive error
            if (expr.receiverExpression != null && expr.receiverExpression.type == null) {
                return ConsecutiveFaultReporting(
                    "Cannot resolve function ${expr.functionNameToken.value} on receiver of unknown type",
                    expr.declaration.sourceLocation
                )
            }
            else {
                return UnresolvableFunctionReporting.of(expr)
            }
        }

        fun semanticRecursion(message: String, location: SourceLocation)
            = SemanticRecursionReporting(message, location)

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
         * @see BaseTypeReference.isNullable
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
            else if (violation is BoundAssignmentStatement) {
                return StateModificationOutsideOfPurityBoundaryReporting(violation, context)
            }

            throw InternalCompilerError("Cannot handle ${violation.javaClass.simpleName} as a purity or readonlyness violation")
        }
    }
}