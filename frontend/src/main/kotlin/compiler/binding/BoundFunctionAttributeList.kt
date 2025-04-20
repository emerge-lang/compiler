package compiler.binding

import compiler.ast.AstFunctionAttribute
import compiler.ast.AstVisibility
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.conflictingAttributes
import compiler.diagnostic.functionIsMissingAttribute
import compiler.diagnostic.inefficientAttributes
import compiler.diagnostic.unsupportedCallingConvention
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.util.twoElementPermutationsUnordered

class BoundFunctionAttributeList(
    context: CTContext,
    /** forward reference to the function this list is located on, for diagnostics */
    private val getFunction: () -> BoundFunction,
    val attributes: List<AstFunctionAttribute>
) : SemanticallyAnalyzable {
    val firstModifyingAttribute: AstFunctionAttribute?
    private val firstReadonlyAttribute: AstFunctionAttribute?
    private val firstPureAttribute: AstFunctionAttribute?
    val externalAttribute: AstFunctionAttribute.External?
    val visibility: BoundVisibility = attributes
        .filterIsInstance<AstVisibility>()
        .firstOrNull()
        ?.bindTo(context)
        ?: BoundVisibility.default(context)

    val firstOverrideAttribute: AstFunctionAttribute.Override?
    val firstNothrowAttribute: AstFunctionAttribute?
    val firstAccessorAttribute: AstFunctionAttribute.Accessor?

    val impliesNoBody: Boolean
    var isDeclaredOperator: Boolean
        private set
    val isDeclaredNothrow: Boolean get() = firstNothrowAttribute != null

    init {
        val attrSequence = attributes.asSequence()
        impliesNoBody = attributes.any { it.impliesNoBody }
        isDeclaredOperator = attributes.any { it is AstFunctionAttribute.Operator }
        firstModifyingAttribute = attributes.firstOrNull {
            it is AstFunctionAttribute.EffectCategory && it.value == BoundFunction.Purity.MODIFYING
        }
        firstReadonlyAttribute = attributes.firstOrNull {
            it is AstFunctionAttribute.EffectCategory && it.value == BoundFunction.Purity.READONLY
        }
        firstPureAttribute = attributes.firstOrNull {
            it is AstFunctionAttribute.EffectCategory && it.value == BoundFunction.Purity.PURE
        }

        externalAttribute = attrSequence.filterIsInstance<AstFunctionAttribute.External>().firstOrNull()
        firstOverrideAttribute = attrSequence.filterIsInstance<AstFunctionAttribute.Override>().firstOrNull()
        firstNothrowAttribute = attributes.find { it is AstFunctionAttribute.Nothrow }
            ?: attributes.find { it is AstFunctionAttribute.External }
        firstAccessorAttribute = attrSequence.filterIsInstance<AstFunctionAttribute.Accessor>().firstOrNull()
    }

    private val seanHelper = SeanHelper()
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            if (firstPureAttribute != null) {
                diagnosis.inefficientAttributes(
                    "The attribute \"pure\" is superfluous, functions are pure by default.",
                    listOf(firstPureAttribute),
                )
            }

            attributes.groupBy { it }.values
                .filter { it.size > 1 }
                .forEach { attrs ->
                    diagnosis.inefficientAttributes(
                        "These attributes are redundant",
                        attrs,
                    )
                }

            attributes.twoElementPermutationsUnordered()
                .filter { (a, b) -> conflictsWith(a, b) }
                .forEach { (a, b) ->
                    diagnosis.conflictingAttributes(listOf(a, b))
                }

            attributes
                .filterIsInstance<AstFunctionAttribute.External>()
                .filter { it.ffiName.value !in SUPPORTED_EXTERNAL_CALLING_CONVENTIONS }
                .forEach {
                    diagnosis.unsupportedCallingConvention(it, SUPPORTED_EXTERNAL_CALLING_CONVENTIONS)
                }

            val externalAttr = attributes.filterIsInstance<AstFunctionAttribute.External>().firstOrNull()
            if (externalAttr != null && attributes.none { it is AstFunctionAttribute.Nothrow }) {
                // this should never occur on ctors or dtors
                val fn = getFunction() as BoundDeclaredFunction
                diagnosis.functionIsMissingAttribute(
                    fn,
                    externalAttr.sourceLocation,
                    AstFunctionAttribute.Nothrow(KeywordToken(Keyword.NOTHROW)),
                    "is declared external; external functions cannot throw exceptions."
                )
            }
        }
    }
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit

    /**
     * Whether this function is pure as per its declaration. Functions are pure by default, so this is the case
     * if neither [FunctionModifier.Readonly] nor [FunctionModifier.Modifying] is present.
     */
    private val isDeclaredPure: Boolean = firstPureAttribute != null || (firstReadonlyAttribute == null && firstModifyingAttribute == null)

    /**
     * Whether this function is readonly as per its declaration. Functions are pure by default, so this is `false`
     * by default. It is true iff the function is explicitly marked with [AstFunctionAttribute.EffectCategory.Category.READONLY].
     */
    private val isDeclaredReadonly: Boolean = firstReadonlyAttribute != null

    val purity: BoundFunction.Purity = when {
        isDeclaredPure -> BoundFunction.Purity.PURE
        isDeclaredReadonly -> BoundFunction.Purity.READONLY
        else -> BoundFunction.Purity.MODIFYING
    }

    val purityAttribute: AstFunctionAttribute? = when(purity) {
        BoundFunction.Purity.PURE -> firstPureAttribute
        BoundFunction.Purity.READONLY -> firstReadonlyAttribute
        BoundFunction.Purity.MODIFYING -> firstModifyingAttribute
    }

    companion object {
        val SUPPORTED_EXTERNAL_CALLING_CONVENTIONS = setOf("C")
        private fun conflictsWith(a: AstFunctionAttribute, b: AstFunctionAttribute): Boolean = when (a) {
            is AstVisibility -> b is AstVisibility && a != b
            is AstFunctionAttribute.EffectCategory -> {
                if (b is AstFunctionAttribute.EffectCategory) {
                    a.value != b.value
                    // if a == b it's an inefficiency, reported through the general inefficiency mechanism
                } else false
            }
            is AstFunctionAttribute.External -> {
                if (b is AstFunctionAttribute.External) {
                    a.ffiName != b.ffiName
                    // if a == b it's an inefficiency, reported through the general inefficiency mechanism
                } else false
            }
            is AstFunctionAttribute.Accessor -> {
                if (b is AstFunctionAttribute.Accessor) {
                    a.kind != b.kind
                    // if a == b it's an inefficiency, reported through the general inefficiency mechanism
                } else false
            }
            is AstFunctionAttribute.Override,
            is AstFunctionAttribute.Operator,
            is AstFunctionAttribute.Intrinsic,
            is AstFunctionAttribute.Nothrow -> false
        }
    }
}