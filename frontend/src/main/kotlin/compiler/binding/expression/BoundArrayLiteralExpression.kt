package compiler.binding.expression

import compiler.CoreIntrinsicsModule
import compiler.InternalCompilerError
import compiler.ast.Executable
import compiler.ast.expression.ArrayLiteralExpression
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinAny
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUnification
import compiler.nullableOr
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrArrayLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundArrayLiteralExpression(
    override val context: CTContext,
    override val declaration: ArrayLiteralExpression,
    val elements: List<BoundExpression<*>>,
) : BoundExpression<ArrayLiteralExpression> {
    override val modifiedContext: CTContext = elements.lastOrNull()?.modifiedContext ?: context
    override val isGuaranteedToThrow: Boolean get() = elements.map { it.isGuaranteedToThrow }.reduceOrNull() { a, b -> a nullableOr b } ?: false
    private var expectedReturnType: BoundTypeReference? = null
    private var expectedElementType: BoundTypeReference? = null
    override var type: BoundTypeReference? = null
        private set

    private val arrayType: BaseType = run {
        val corePackage = context.swCtx.getPackage(CoreIntrinsicsModule.NAME)
            ?: throw InternalCompilerError("The software context doesn't define the default package ${CoreIntrinsicsModule.NAME}")
        corePackage.resolveBaseType("Array")
            ?: throw InternalCompilerError("The software context doesn't define ${CoreIntrinsicsModule.NAME}.Array")
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return elements.flatMap { it.semanticAnalysisPhase1() }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = elements
            .flatMap { it.semanticAnalysisPhase2() }
            .toMutableSet()

        val elementType: BoundTypeReference
        if (expectedElementType != null) {
            elementType = expectedElementType!!
            elements.forEach { element ->
                element.type?.let {
                    val unification = elementType.unify(it, element.declaration.sourceLocation, TypeUnification.EMPTY)
                    reportings.addAll(unification.reportings)
                }
            }
        } else {
            elementType = elements
                .mapNotNull { it.type }
                .reduceOrNull(BoundTypeReference::closestCommonSupertypeWith)
                ?: BuiltinAny.baseReference
        }

        type = RootResolvedTypeReference(
            TypeReference(arrayType.simpleName),
            arrayType,
            listOf(BoundTypeArgument(
                TypeArgument(TypeVariance.UNSPECIFIED, TypeReference("_")),
                TypeVariance.UNSPECIFIED,
                elementType,
            ))
        )
        expectedReturnType?.let {
            type = type?.withMutability(it.mutability)
        }

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return elements.flatMap { it.semanticAnalysisPhase3() }
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return elements.flatMap { it.findReadsBeyond(boundary) }
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return elements.flatMap { it.findWritesBeyond(boundary) }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        expectedReturnType = type

        if (type !is RootResolvedTypeReference || type.baseType != arrayType) {
            // ignore
            return
        }

        expectedElementType = type.arguments.firstOrNull()?.type ?: return
        elements.forEach { it.setExpectedEvaluationResultType(expectedElementType!!) }
    }

    private val _backendIr by lazy {
        IrArrayLiteralExpressionImpl(
            type!!.toBackendIr(),
            (type as RootResolvedTypeReference).arguments.single().type.toBackendIr(),
            elements.map { it.toBackendIr() },
        )
    }
    override fun toBackendIr(): IrExpression = _backendIr
}

private class IrArrayLiteralExpressionImpl(
    override val evaluatesTo: IrType,
    override val elementType: IrType,
    override val elements: List<IrExpression>,
) : IrArrayLiteralExpression