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
import compiler.binding.expression.BoundBreakExpression
import compiler.binding.expression.BoundCastExpression
import compiler.binding.expression.BoundContinueExpression
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.binding.expression.BoundNotNullExpression
import compiler.binding.expression.BoundReturnExpression
import compiler.binding.expression.BoundThrowExpression
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.lexer.IdentifierToken
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName
import java.math.BigInteger

fun Diagnosis.consecutive(message: String, span: Span = Span.UNKNOWN) {
    add(ConsecutiveFaultDiagnostic(message, span))
}

fun Diagnosis.unknownType(erroneousRef: TypeReference) {
    add(UnknownTypeDiagnostic(erroneousRef))
}

fun Diagnosis.valueNotAssignable(targetType: BoundTypeReference, sourceType: BoundTypeReference, reason: String, assignmentLocation: Span) {
    add(ValueNotAssignableDiagnostic(targetType, sourceType, reason, assignmentLocation))
}

fun Diagnosis.undefinedIdentifier(expr: IdentifierToken, messageOverride: String? = null) {
    add(UndefinedIdentifierDiagnostic(expr, messageOverride))
}

/**
 * @param acceptedDeclaration The declaration that is accepted by the compiler as the first / actual one
 * @param additionalDeclaration The erroneous declaration; is rejected (instead of accepted)
 */
fun Diagnosis.variableDeclaredMoreThanOnce(acceptedDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration) {
    add(MultipleVariableDeclarationsDiagnostic(acceptedDeclaration, additionalDeclaration))
}

fun Diagnosis.globalVariableNotInitialized(variable: BoundVariable) {
    add(GlobalVariableNotInitializedDiagnostic(variable.declaration))
}

fun Diagnosis.useOfUninitializedVariable(variable: BoundVariable, access: BoundIdentifierExpression, maybeInitialized: Boolean) {
    add(VariableAccessedBeforeInitializationDiagnostic(variable.declaration, access.declaration, maybeInitialized))
}

fun Diagnosis.parameterDeclaredMoreThanOnce(firstDeclaration: VariableDeclaration, additionalDeclaration: VariableDeclaration) {
    add(MultipleParameterDeclarationsDiagnostic(firstDeclaration, additionalDeclaration))
}

fun Diagnosis.variableTypeNotDeclared(variable: BoundVariable) {
    add(MissingVariableTypeDiagnostic(variable.declaration, variable.kind))
}

fun Diagnosis.varianceOnFunctionTypeParameter(parameter: BoundTypeParameter) {
    add(VarianceOnFunctionTypeParameterDiagnostic(parameter.astNode))
}

fun Diagnosis.varianceOnInvocationTypeArgument(argument: BoundTypeArgument) {
    add(VarianceOnInvocationTypeArgumentDiagnostic(argument.astNode))
}

fun Diagnosis.unsupportedTypeUsageVariance(useSite: TypeUseSite, erroneousVariance: TypeVariance) {
    add(UnsupportedTypeUsageVarianceDiagnostic(useSite, erroneousVariance))
}

fun Diagnosis.illegalAssignment(message: String, assignmentStatement: BoundAssignmentStatement) {
    add(IllegalAssignmentDiagnostic(message, assignmentStatement))
}

fun Diagnosis.illegalFunctionBody(function: FunctionDeclaration) {
    add(IllegalFunctionBodyDiagnostic(function))
}

fun Diagnosis.missingFunctionBody(function: FunctionDeclaration) {
    add(MissingFunctionBodyDiagnostic(function))
}

fun Diagnosis.inefficientAttributes(message: String, attributes: Collection<AstFunctionAttribute>) {
    add(ModifierInefficiencyDiagnostic(message, attributes))
}

fun Diagnosis.conflictingModifiers(attributes: Collection<AstFunctionAttribute>) {
    add(ConflictingFunctionModifiersDiagnostic(attributes))
}

fun Diagnosis.functionIsMissingDeclaredAttribute(fn: BoundDeclaredFunction, missingAttribute: AstFunctionAttribute, reason: String) {
    add(FunctionMissingDeclaredModifierDiagnostic(fn.declaration, missingAttribute, reason))
}

fun Diagnosis.toplevelFunctionWithOverrideAttribute(attr: AstFunctionAttribute.Override) {
    add(ToplevelFunctionWithOverrideAttributeDiagnostic(attr.attributeName))
}

fun Diagnosis.unsupportedCallingConvention(attr: AstFunctionAttribute.External, supportedConventions: Set<String>) {
    add(UnsupportedCallingConventionDiagnostic(attr, supportedConventions))
}

fun Diagnosis.unconventionalTypeName(name: IdentifierToken, convention: UnconventionalTypeNameDiagnostic.ViolatedConvention) {
    add(UnconventionalTypeNameDiagnostic(name, convention))
}

fun Diagnosis.illegalSupertype(ref: TypeReference, reason: String) {
    add(IllegalSupertypeDiagnostic(ref, reason))
}

fun Diagnosis.duplicateSupertype(ref: TypeReference) {
    add(DuplicateSupertypeDiagnostic(ref))
}

fun Diagnosis.cyclicInheritance(type: BoundBaseType, involvingSupertype: BoundSupertypeDeclaration) {
    add(CyclicInheritanceDiagnostic(type.declaration, involvingSupertype))
}

fun Diagnosis.duplicateBaseTypes(packageName: CanonicalElementName.Package, duplicates: List<BoundBaseType>) {
    add(DuplicateBaseTypesDiagnostic(packageName, duplicates.map { it.declaration }))
}

fun Diagnosis.functionDoesNotOverride(function: BoundDeclaredFunction) {
    add(SuperFunctionForOverrideNotFoundDiagnostic(function.declaration))
}

fun Diagnosis.undeclaredOverride(function: BoundDeclaredFunction, onSupertype: BoundBaseType) {
    add(UndeclaredOverrideDiagnostic(function.declaration, onSupertype))
}

fun Diagnosis.staticFunctionDeclaredOverride(function: BoundDeclaredFunction) {
    add(StaticFunctionDeclaredOverrideDiagnostic(function.attributes.firstOverrideAttribute!!))
}

fun Diagnosis.memberFunctionImplementedOnInterface(function: BoundDeclaredBaseTypeMemberFunction) {
    add(MemberFunctionImplOnInterfaceDiagnostic(function.body!!.declaration.span))
}

fun Diagnosis.abstractInheritedFunctionNotImplemented(implementingType: BoundBaseType, functionToImplement: BoundMemberFunction) {
    add(AbstractInheritedFunctionNotImplementedDiagnostic(implementingType, functionToImplement))
}

fun Diagnosis.noMatchingFunctionOverload(functionNameReference: IdentifierToken, receiverType: BoundTypeReference?, valueArguments: List<BoundExpression<*>>, functionDeclaredAtAll: Boolean) {
    add(UnresolvableFunctionOverloadDiagnostic(functionNameReference, receiverType, valueArguments.map { it.type }, functionDeclaredAtAll))
}

fun Diagnosis.overloadSetHasNoDisjointParameter(overloadSet: BoundOverloadSet<*>) {
    val baseReporting = OverloadSetHasNoDisjointParameterDiagnostic(overloadSet)

    // hypothesis / edge case to find: the problem is created by (multiple) inheritance _only_
    val allMemberFns = overloadSet.overloads.filterIsInstance<BoundMemberFunction>()
    if (allMemberFns.size < overloadSet.overloads.size) {
        // there are top-level functions at play
        add(baseReporting)
        return
    }

    val subtype = allMemberFns.first().ownerBaseType

    val onlyInheritedOverloads = allMemberFns.filter { it is InheritedBoundMemberFunction || it is PossiblyMixedInBoundMemberFunction }
    if (onlyInheritedOverloads.isEmpty() || BoundOverloadSet.areOverloadsDisjoint(onlyInheritedOverloads)) {
        // the member functions declared in the subtype clearly have an effect on the ambiguity of the overload-set
        add(baseReporting)
        return
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
        consecutive("overload disjoint problem inherited into ${subtype.canonicalName} from a supertype", baseReporting.span)
        return
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
    add(MultipleInheritanceIssueDiagnostic(
        baseReporting,
        overloadsImportedBySupertype.keys,
        subtype,
    ))
}

fun Diagnosis.unresolvableConstructor(nameToken: IdentifierToken, valueArguments: List<BoundExpression<*>>, functionsWithNameAvailable: Boolean) {
    add(UnresolvableConstructorDiagnostic(nameToken, valueArguments.map { it.type }, functionsWithNameAvailable))
}

fun Diagnosis.unresolvableMemberVariable(accessExpression: BoundMemberAccessExpression, hostType: BoundTypeReference) {
    add(UnresolvedMemberVariableDiagnostic(accessExpression.declaration, hostType))
}

fun Diagnosis.ambiguousImports(imports: Iterable<BoundImportDeclaration>) {
    add(AmbiguousImportsDiagnostic(imports.map { it.declaration }, imports.first().simpleName!!))
}

fun Diagnosis.implicitlyEvaluatingAStatement(statement: BoundExecutable<*>) {
    add(ImplicitlyEvaluatedStatementDiagnostic(statement.declaration))
}

fun Diagnosis.ambiguousInvocation(invocation: BoundInvocationExpression, candidates: List<BoundFunction>) {
    add(AmbiguousInvocationDiagnostic(invocation.declaration, candidates))
}

fun Diagnosis.typeDeductionError(message: String, location: Span) {
    add(TypeDeductionErrorDiagnostic(message, location))
}

fun Diagnosis.explicitInferTypeWithArguments(type: TypeReference) {
    add(ExplicitInferTypeWithArgumentsDiagnostic(type))
}

fun Diagnosis.explicitInferTypeNotAllowed(type: TypeReference) {
    add(ExplicitInferTypeNotAllowedDiagnostic(type))
}

fun Diagnosis.functionIsMissingAttribute(function: BoundFunction, usageRequiringModifier: Executable, missingAttribute: String) {
    add(FunctionMissingModifierDiagnostic(function, usageRequiringModifier, missingAttribute))
}

fun Diagnosis.externalMemberFunction(function: BoundDeclaredFunction) {
    add(ExternalMemberFunctionDiagnostic(function.declaration, function.attributes.externalAttribute!!.attributeName))
}

fun Diagnosis.notAllMemberVariablesInitialized(uninitializedMembers: Collection<BoundBaseTypeMemberVariable>, usedAt: Span) {
    add(NotAllMemberVariablesInitializedDiagnostic(
        uninitializedMembers.map { it.declaration },
        usedAt
    ))
}

fun Diagnosis.notAllMixinsInitialized(uninitializedMixins: Collection<BoundMixinStatement>, usedAt: Span) {
    add(ObjectUsedBeforeMixinInitializationDiagnostic(uninitializedMixins.minBy { it.declaration.span.fromLineNumber }.declaration, usedAt))
}

fun Diagnosis.useOfUninitializedMember(access: BoundMemberAccessExpression) {
    add(
        UseOfUninitializedClassMemberVariableDiagnostic(
            access.member!!.declaration,
            access.declaration.memberName.span,
        )
    )
}

fun Diagnosis.constructorDeclaredAsModifying(constructor: BoundClassConstructor) {
    add(ConstructorDeclaredModifyingDiagnostic(
        constructor,
        constructor.attributes.firstModifyingAttribute!!.attributeName,
    ))
}

fun Diagnosis.explicitOwnershipNotAllowed(variable: BoundVariable) {
    add(ExplicitOwnershipNotAllowedDiagnostic(variable.declaration.ownership!!.second))
}

fun Diagnosis.variableUsedAfterLifetime(variable: BoundVariable, read: BoundIdentifierExpression, deadState: VariableLifetime.State.Dead) {
    add(VariableUsedAfterLifetimeDiagnostic(variable.declaration, read.declaration.span, deadState.lifetimeEndedAt, deadState.maybe))
}

fun Diagnosis.lifetimeEndingCaptureInLoop(variable: BoundVariable, read: BoundIdentifierExpression) {
    add(LifetimeEndingCaptureInLoopDiagnostic(variable.declaration, read.declaration.span))
}

fun Diagnosis.borrowedVariableCaptured(variable: BoundVariable, capture: BoundIdentifierExpression) {
    add(BorrowedVariableCapturedDiagnostic(variable.declaration, capture.declaration.span))
}

/**
 * An expression is used in a way that requires it to be non-null but the type of the expression is nullable.
 * @param nullableExpression The expression that could evaluate to null and thus case an NPE
 * @see BoundTypeReference.isExplicitlyNullable
 */
fun Diagnosis.unsafeObjectTraversal(nullableExpression: BoundExpression<*>, faultyAccessOperator: OperatorToken) {
    add(UnsafeObjectTraversalDiagnostic(nullableExpression, faultyAccessOperator))
}

fun Diagnosis.superfluousSafeObjectTraversal(nonNullExpression: BoundExpression<*>, superfluousSafeOperator: OperatorToken) {
    add(SuperfluousSafeObjectTraversal(nonNullExpression, superfluousSafeOperator))
}

fun Diagnosis.overrideAddsSideEffects(override: BoundMemberFunction, superFunction: BoundMemberFunction) {
    add(OverrideAddsSideEffectsDiagnostic(override, superFunction))
}

fun Diagnosis.overrideDropsNothrow(override: BoundMemberFunction, superFunction: BoundMemberFunction) {
    add(OverrideDropsNothrowDiagnostic(override, superFunction))
}

fun Diagnosis.overrideRestrictsVisibility(override: BoundMemberFunction, superFunction: BoundMemberFunction) {
    add(OverrideRestrictsVisibilityDiagnostic(override, superFunction))
}

fun Diagnosis.overridingParameterExtendsOwnership(override: BoundParameter, superParameter: BoundParameter) {
    add(ExtendingOwnershipOverrideDiagnostic(override, superParameter))
}

fun Diagnosis.nothrowViolatingInvocation(invocation: BoundInvocationExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
    add(NothrowViolationDiagnostic.ThrowingInvocation(invocation, boundary))
}

fun Diagnosis.nothrowViolatingNotNullAssertion(assertion: BoundNotNullExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
    add(NothrowViolationDiagnostic.NotNullAssertion(assertion.declaration, boundary))
}

fun Diagnosis.nothrowViolatingCast(cast: BoundCastExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
    add(NothrowViolationDiagnostic.StrictCast(cast.declaration, boundary))
}

fun Diagnosis.throwStatementInNothrowContext(statement: BoundThrowExpression, boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
    add(NothrowViolationDiagnostic.ThrowStatement(statement.declaration, boundary))
}

fun Diagnosis.constructorDeclaredNothrow(constructor: BoundClassConstructor) {
    add(ConstructorDeclaredNothrowDiagnostic(constructor.attributes.firstNothrowAttribute!!.sourceLocation))
}

fun Diagnosis.breakOutsideOfLoop(breakStatement: BoundBreakExpression) {
    add(BreakOutsideOfLoopDiagnostic(breakStatement.declaration))
}

fun Diagnosis.continueOutsideOfLoop(continueStatement: BoundContinueExpression) {
    add(ContinueOutsideOfLoopDiagnostic(continueStatement.declaration))
}

fun Diagnosis.missingReturnValue(returnStatement: BoundReturnExpression, expectedType: BoundTypeReference) {
    add(MissingReturnValueDiagnostic(returnStatement.declaration, expectedType,))
}

fun Diagnosis.uncertainTermination(function: BoundDeclaredFunction) {
    add(UncertainTerminationDiagnostic(function))
}

fun Diagnosis.conditionIsNotBoolean(condition: BoundExpression<*>) {
    val location = condition.declaration.span
    if (condition.type == null) {
        return consecutive("The condition must evaluate to Bool, cannot determine type", location)
    }

    add(ConditionNotBooleanDiagnostic(condition, location))
}

fun Diagnosis.typeParameterNameConflict(originalType: BoundTypeReference, conflicting: BoundTypeParameter) {
    add(TypeParameterNameConflictDiagnostic(originalType, conflicting))
}

fun Diagnosis.duplicateBaseTypeMembers(typeDef: BoundBaseType, duplicateMembers: Set<BoundBaseTypeMemberVariable>) {
    add(DuplicateBaseTypeMemberDiagnostic(typeDef, duplicateMembers))
}

fun Diagnosis.mutationInCondition(conditionImpurity: PurityViolationDiagnostic.Impurity) {
    add(MutationInConditionDiagnostic(conditionImpurity))
}

fun Diagnosis.incorrectPackageDeclaration(name: AstPackageName, expected: CanonicalElementName.Package) {
    add(IncorrectPackageDeclarationDiagnostic(name, expected))
}

fun Diagnosis.integerLiteralOutOfRange(literal: Expression, expectedType: BoundBaseType, expectedRange: ClosedRange<BigInteger>) {
    add(IntegerLiteralOutOfRangeDiagnostic(literal, expectedType, expectedRange))
}

fun Diagnosis.multipleClassConstructors(additionalCtors: Collection<BaseTypeConstructorDeclaration>) {
    add(MultipleClassConstructorsDiagnostic(additionalCtors))
}

fun Diagnosis.mixinNotAllowed(mixin: BoundMixinStatement) {
    add(MixinNotAllowedDiagnostic(mixin.declaration))
}

fun Diagnosis.illegalMixinRepetition(mixin: BoundMixinStatement, repetition: ExecutionScopedCTContext.Repetition) {
    add(IllegalMixinRepetitionDiagnostic(mixin.declaration, repetition))
}

fun Diagnosis.unusedMixin(mixin: BoundMixinStatement) {
    add(UnusedMixinDiagnostic(mixin.declaration))
}

fun Diagnosis.multipleClassDestructors(additionalDtors: Collection<BaseTypeDestructorDeclaration>) {
    add(MultipleClassDestructorsDiagnostic(additionalDtors))
}

fun Diagnosis.entryNotAllowedOnBaseType(baseType: BoundBaseType, entry: BoundBaseTypeEntry<*>) {
    add(EntryNotAllowedInBaseTypeDiagnostic(baseType.kind, entry))
}

fun Diagnosis.elementNotAccessible(element: DefinitionWithVisibility, visibility: BoundVisibility, accessAt: Span) {
    add(ElementNotAccessibleDiagnostic(element, visibility, accessAt))
}

fun Diagnosis.missingModuleDependency(element: DefinitionWithVisibility, accessAt: Span, moduleOfAccessedElement: CanonicalElementName.Package, moduleOfAccess: CanonicalElementName.Package) {
    add(MissingModuleDependencyDiagnostic(element, accessAt, moduleOfAccessedElement, moduleOfAccess))
}

fun Diagnosis.visibilityTooBroad(owningModule: CanonicalElementName.Package, visibilityDeclaration: BoundVisibility.PackageScope) {
    add(PackageVisibilityTooBroadDiagnostic(owningModule, visibilityDeclaration.packageName, visibilityDeclaration.astNode.sourceLocation))
}

fun Diagnosis.visibilityNotAllowedOnVariable(variable: BoundVariable) {
    add(VisibilityNotAllowedOnVariableDiagnostic(variable))
}

fun Diagnosis.visibilityShadowed(element: DefinitionWithVisibility, contextVisibility: BoundVisibility) {
    add(ShadowedVisibilityDiagnostic(element, contextVisibility))
}

fun Diagnosis.hiddenTypeExposed(type: BoundBaseType, exposedBy: DefinitionWithVisibility, exposedAt: Span) {
    add(HiddenTypeExposedDiagnostic(type, exposedBy, exposedAt))
}

fun Diagnosis.forbiddenCast(castOp: BoundCastExpression, reason: String, span: Span = castOp.declaration.span) {
    add(ForbiddenCastDiagnostic(castOp.declaration, reason, span))
}

fun Diagnosis.unsupportedReflection(onType: BoundTypeReference) {
    add(UnsupportedTypeReflectionException(onType.span ?: Span.UNKNOWN))
}

fun Diagnosis.typeCheckOnVolatileTypeParameter(node: BoundExpression<*>, typeToCheck: BoundTypeReference) {
    add(TypeCheckOnVolatileTypeParameterDiagnostic(typeToCheck.span ?: node.declaration.span))
}

fun Diagnosis.nullCheckOnNonNullableValue(value: BoundExpression<*>) {
    add(NullCheckingNonNullableValueDiagnostic(value.declaration))
}

fun Diagnosis.purityViolation(
    impurity: PurityViolationDiagnostic.Impurity,
    boundary: PurityViolationDiagnostic.SideEffectBoundary
) {
    add(PurityViolationDiagnostic(impurity, boundary))
}