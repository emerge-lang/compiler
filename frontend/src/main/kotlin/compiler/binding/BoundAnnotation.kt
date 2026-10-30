package compiler.binding

import compiler.ast.AstAnnotation
import compiler.ast.type.TypeMutability
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.expression.BoundExpression
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.disallowedAnnotation
import compiler.diagnostic.invalidAnnotationMember
import compiler.diagnostic.purityViolation
import compiler.diagnostic.valueNotAnnotatable
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.EmergeConstants

class BoundAnnotation(
    val astNode: AstAnnotation,
    val expression: BoundExpression<*>,
    lazySubject: () -> Any,
) : SemanticallyAnalyzable {
    internal val subject by lazy(lazySubject)
    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        seanHelper.phase1(diagnosis) {
            validateSubject(subject, diagnosis)
            expression.semanticAnalysisPhase1(diagnosis)
        }
    }

    var type: BoundTypeReference? by seanHelper.resultOfPhase2(false)
        private set

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        seanHelper.phase2(diagnosis) {
            expression.semanticAnalysisPhase2(diagnosis)
            type = expression.type
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase3(diagnosis)
        val visitor = ImpurityVisitor { impurity ->
            diagnosis.purityViolation(impurity, PurityViolationDiagnostic.SideEffectBoundary.Annotation(this@BoundAnnotation))
        }
        expression.visitReadsBeyond(expression.context, visitor)
        expression.visitWritesBeyond(expression.context, visitor)

        validateSelfType(diagnosis)
        validateAnnotatableOnlyOnTrulyAnnotatableClasses(diagnosis)
    }

    private fun validateSubject(subject: Any, diagnosis: Diagnosis) {
        when (subject) {
            is BoundTopLevelFunction,
            is BoundBaseType,
            is BoundBaseTypeMemberVariable,
            is BoundMemberFunction, -> {
                // allowed
            }
            is BoundVariable -> when (subject.kind) {
                BoundVariable.Kind.CONSTRUCTOR_PARAMETER,
                    // these are BoundBaseTypeMemberVariable; this case only happens when the nested variable grammar
                    // for member vars picks up annotations; see the AnnotationErrors test
                BoundVariable.Kind.MEMBER_VARIABLE,
                BoundVariable.Kind.LOCAL_VARIABLE, -> {
                    diagnosis.disallowedAnnotation(this)
                }
                else -> { /* allowed */ }
            }
            else -> {
                // e.g. local variable
                diagnosis.disallowedAnnotation(this)
            }
        }
    }

    private fun validateSelfType(diagnosis: Diagnosis) {
        val localType = expression.type
        if (localType !is RootResolvedTypeReference || !localType.baseType.annotations.anyOfType(EmergeConstants.CoreModule.ANNOTATABLE_TYPE_NAME)) {
            diagnosis.valueNotAnnotatable(this@BoundAnnotation)
            return
        }

        localType.evaluateAssignabilityTo(
            expression.context.swCtx.getTopType(Span.UNKNOWN).withMutability(TypeMutability.IMMUTABLE),
            astNode.span,
        )?.let(diagnosis::add)
    }

    private fun validateAnnotatableOnlyOnTrulyAnnotatableClasses(diagnosis: Diagnosis) {
        val localType = type
        if (localType !is RootResolvedTypeReference || localType.baseType.canonicalName != EmergeConstants.CoreModule.ANNOTATABLE_TYPE_NAME) {
            return
        }

        val localSubject = subject
        if (localSubject !is BoundBaseType || localSubject.kind != BoundBaseType.Kind.CLASS) {
            diagnosis.disallowedAnnotation(this, "${EmergeConstants.CoreModule.ANNOTATABLE_TYPE_NAME} may only be annotated onto classes")
            return
        }

        localSubject.memberVariables.forEach { validateMemberOfAnnotatableClass(it, diagnosis) }
    }

    private fun validateMemberOfAnnotatableClass(member: BoundBaseTypeMemberVariable, diagnosis: Diagnosis) {
        if (member.isReAssignable) {
            diagnosis.invalidAnnotationMember(member, this, "members must be immutable", member.entryDeclaration.variableDeclaration.varToken?.span)
            return
        }

        val localType = member.type ?: return
        // if null the compilation errors because unknown type

        if (localType !is RootResolvedTypeReference || (!localType.baseType.isCoreScalar && localType.baseType.canonicalName != EmergeConstants.CoreModule.STRING_TYPE_NAME)) {
            diagnosis.invalidAnnotationMember(member, this, "members must be numbers, booleans or strings")
            return
        }

    }
}