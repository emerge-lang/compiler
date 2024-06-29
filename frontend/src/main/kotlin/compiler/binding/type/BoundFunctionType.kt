package compiler.binding.type

import compiler.ast.AstFunctionAttribute
import compiler.ast.type.AstFunctionType
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundCallableRef
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Span
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrFunctionType
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundFunctionType(
    val context: CTContext,
    val astNode: AstFunctionType,
    val attributes: BoundFunctionAttributeList,
    val parameterTypes: List<BoundTypeReference>,
    val returnType: BoundTypeReference,
    override val mutability: TypeMutability,
) : BoundTypeReference {
    override val isNullable = false
    override val span = astNode.span

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundFunctionType {
        // function types are always const because code cannot be changed
        return this
    }

    override fun withMutability(modifier: TypeMutability?): BoundFunctionType {
        // function types are always const because code cannot be changed; however const -> read is okay
        return when (modifier) {
            mutability -> this
            TypeMutability.READONLY -> BoundFunctionType(
                context,
                astNode,
                attributes,
                parameterTypes,
                returnType,
                modifier,
            )
            else -> this
        }
    }

    override fun withCombinedMutability(mutability: TypeMutability?): BoundFunctionType {
        val newMutability = this.mutability.combinedWith(mutability)
        return withMutability(newMutability)
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        if (nullability == TypeReference.Nullability.NULLABLE) {
            return NullableTypeReference(this)
        }
        return this
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        val useSiteWithVariance = forUsage.deriveIrrelevant() // function types impose variance upon all the constituent types
        return returnType.validate(useSiteWithVariance) + parameterTypes.flatMap { it.validate(useSiteWithVariance) }
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        if (other !is BoundFunctionType || other.parameterTypes.size != this.parameterTypes.size) {
            return context.swCtx.any.baseReference
        }

        val combinedNothrowAttr = if (this.attributes.isDeclaredNothrow && other.attributes.isDeclaredNothrow) {
            AstFunctionAttribute.Nothrow(
                KeywordToken(
                    keyword = this.attributes.firstNothrowAttribute!!.attributeName.keyword,
                    span = this.attributes.firstNothrowAttribute.sourceLocation.deriveGenerated(),
                )
            )
        } else null

        val combinedSideEffectAttr = null

        lateinit var superFnType: BoundFunctionType
        val superFnTypeForwardRef = BoundCallableRef.FunctionType { superFnType }
        superFnType = BoundFunctionType(
            context,
            astNode,
            BoundFunctionAttributeList(
                context,
                superFnTypeForwardRef,
                listOfNotNull(
                    combinedNothrowAttr,
                    combinedSideEffectAttr,
                )
            ),
            TODO("params, have in variance, this logic isn't determined yet"),
            this.returnType.closestCommonSupertypeWith(other.returnType),
            TypeMutability.IMMUTABLE,
        )
        return superFnType
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundFunctionType {
        return BoundFunctionType(
            context,
            astNode,
            attributes,
            parameterTypes.map { it.withTypeVariables(variables) },
            returnType.withTypeVariables(variables),
            mutability,
        )
    }

    override fun unify(
        assigneeType: BoundTypeReference,
        assignmentLocation: Span,
        carry: TypeUnification
    ): TypeUnification {
        if (assigneeType !is BoundFunctionType) {
            return carry.plusReporting(Reporting.valueNotAssignable(this, assigneeType, "cannot assign a named type to a function type", assignmentLocation))
        }

        var varCarry = carry
        if (assigneeType.parameterTypes.size != this.parameterTypes.size) {
            varCarry = varCarry.plusReporting(Reporting.valueNotAssignable(
                this,
                assigneeType,
                "must have the same number of parameters; expected ${this.parameterTypes.size}, trying to assign ${assigneeType.parameterTypes.size}",
                assignmentLocation
            ))
        }

        if (this.attributes.isDeclaredNothrow && !assigneeType.attributes.isDeclaredNothrow) {
            varCarry = varCarry.plusReporting(Reporting.valueNotAssignable(
                this,
                assigneeType,
                "a nothrow function is needed, got a potentially throwing one",
                assignmentLocation,
            ))
        }

        if (!this.attributes.purity.contains(assigneeType.attributes.purity)) {
            val selfPurity = (this.attributes.purityAttribute?.attributeName?.keyword ?: Keyword.PURE).text
            val assigneePurity = (assigneeType.attributes.purityAttribute?.attributeName?.keyword ?: Keyword.PURE).text
            varCarry = varCarry.plusReporting(Reporting.valueNotAssignable(
                this,
                assigneeType,
                "expected a $selfPurity function, this is a $assigneePurity function",
                assignmentLocation,
            ))
        }

        varCarry = BoundTypeArgument.unifyTypeArguments(
            this.returnType,
            TypeVariance.OUT,
            assigneeType.returnType,
            TypeVariance.OUT,
            assignmentLocation,
            varCarry
        )

        varCarry = this.parameterTypes.zip(assigneeType.parameterTypes).fold(varCarry) { innerCarry, (targetParamType, assigneeParamType) ->
            BoundTypeArgument.unifyTypeArguments(
                targetParamType,
                TypeVariance.IN,
                assigneeParamType,
                TypeVariance.IN,
                assignmentLocation,
                innerCarry,
            )
        }

        return varCarry
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundFunctionType {
        return BoundFunctionType(
            this.context,
            astNode,
            attributes,
            parameterTypes.map { it.instantiateAllParameters(context) },
            returnType.instantiateAllParameters(context),
            mutability,
        )
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return other is BoundFunctionType
            && other.parameterTypes.size == this.parameterTypes.size
            && other.attributes.purity == this.attributes.purity
            && other.attributes.isDeclaredNothrow == this.attributes.isDeclaredNothrow
    }

    override val inherentTypeBindings: TypeUnification = TypeUnification.EMPTY

    override val destructorThrowBehavior: SideEffectPrediction
        get() {
            /*
            technically, this is overly defensive. Only capturing lambda literals can throw on destruction, and ONLY
            if any of the captured values can throw on destruction. However, adding syntax to the language to model
            doesn't seem like its worth the effort at all.
             */
            return SideEffectPrediction.POSSIBLY
        }

    override fun toString(): String {
        val buffer = StringBuilder()
        attributes.firstNothrowAttribute?.let {
            buffer.append(it.attributeName.keyword.text)
            buffer.append(' ')
        }
        attributes.firstModifyingAttribute?.let {
            buffer.append(it.attributeName.keyword.text)
            buffer.append(' ')
        }

        buffer.append('(')
        parameterTypes.forEachIndexed { index, paramType ->
            buffer.append(paramType.toString())
            if (index != parameterTypes.lastIndex) {
                buffer.append(", ")
            }
        }
        buffer.append(") -> ")
        buffer.append(returnType.toString())

        return buffer.toString()
    }

    private val backendIr by lazy {
        IrFunctionTypeImpl(
            parameterTypes.map { it.toBackendIr() },
            returnType.toBackendIr(),
            false,
        )
    }
    override fun toBackendIr(): IrFunctionType {
        return backendIr
    }
}

internal class IrFunctionTypeImpl(
    override val parameterTypes: List<IrType>,
    override val returnType: IrType,
    override val isNullable: Boolean,
) : IrFunctionType {
    override fun asNullable(): IrFunctionType {
        return IrFunctionTypeImpl(parameterTypes, returnType, true)
    }
}