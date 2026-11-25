package compiler.binding.context

import compiler.InternalCompilerError
import compiler.ast.expression.AstSharedValueExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundLoop
import compiler.binding.BoundVariable
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.basetype.BaseTypeField
import compiler.binding.basetype.BoundMixinStatement
import compiler.binding.basetype.DestructorCodeGenerator
import compiler.binding.context.effect.CallFrameExit
import compiler.binding.context.effect.EphemeralStateClass
import compiler.binding.context.effect.LoopJump
import compiler.binding.context.effect.SideEffect
import compiler.binding.context.effect.SingletonEphemeralStateClass
import compiler.binding.context.effect.SingletonEphemeralStateClass.Companion.getEphemeralState
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.mixinNotAllowed
import compiler.util.TakeWhileAndNextIterator.Companion.takeWhileAndNext
import compiler.util.takeWhileIsInstance
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import java.util.IdentityHashMap
import java.util.SequencedSet

/**
 * A [CTContext] that is also associated with an execution scope. All code that actually _does_
 * stuff lives in an [ExecutionScopedCTContext]; Pure [CTContext] is for declaration-only situations.
 */
interface ExecutionScopedCTContext : CTContext {
    /**
     * Whether this scope marks the boundary of a scope. A scope in this sense is a collection of
     * [BoundExecutable]s at which's end the deferred code will be executed by default.
     */
    val isScopeBoundary: Boolean

    /**
     * Whether this scope marks the root of a function. Deferred statements further up in the
     * tree of [CTContext]s will not be executed when this scope (or any of its child scopes)
     * exit.
     *
     * [isFunctionRoot] implies [isScopeBoundary]
     */
    val isFunctionRoot: Boolean

    /**
     * true for all contexts that introduce a new exception handling boundary (a try block). For now
     * that is only [TryBlockExecutionScopedCTContext].
     */
    val isTryContext: Boolean

    /**
     * true iff this context or any of its parents has [isTryContext] = `true`
     */
    val isInTryContext: Boolean

    /**
     * @return Whether this context contains the given variable. Only parent contexts up to and including the
     *         given `boundary` will be searched.
     */
    fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean

    /**
     * like [getRepetitionBehaviorRelativeTo] given the direct parent.
     */
    val repetitionRelativeToParent: Repetition

    /**
     * How often code in `this` [ExecutionScopedCTContext] may get executed __relative to__ [indirectParent].
     * @param indirectParent must be the direct or an indirect parent of `this`
     */
    fun getRepetitionBehaviorRelativeTo(indirectParent: CTContext): Repetition

    /**
     * `this` if it is a [LoopExecutionScopedCTContext], otherwise the closest parent that is; `null` if there is none.
     * This is the loop that a `break` or `continue` in this context refers to.
     */
    val innermostLoopContext: LoopExecutionScopedCTContext<*>?

    /**
     * If [isScopeBoundary], `this`, otherwise the closest parent that [isScopeBoundary].
     */
    val parentScopeContext: ExecutionScopedCTContext?

    /**
     * The value that `$` refers to in this context, see [IndexExecutionScopedCTContext]
     */
    val indexedValue: AstSharedValueExpression?

    /**
     * @return code that has been deferred in _this very_ [ExecutionScopedCTContext], in the **reverse** order
     * of how it was added to [MutableExecutionScopedCTContext.addDeferredCode].
     */
    fun getContextLocalDeferredCode(): Sequence<DeferrableExecutable>

    /**
     * @return all code that has been deferred in this [ExecutionScopedCTContext]s scope, in the
     * **reverse** order of how it was added to [addDeferredCode].
     */
    fun getScopeLocalDeferredCode(): Sequence<DeferrableExecutable>

    /**
     * If there is a parent context that has [isTryContext] = `true`, returns all deferred code up to and including
     * that context, in the **reverse** order of how it was added to [addDeferredCode].
     * If there is no parent context marked with [isTryContext], returns an empty sequence.
     */
    fun getExceptionHandlingLocalDeferredCode(): Sequence<DeferrableExecutable>

    /**
     * If there is a parent context that has [isTryContext] = `true`, returns an empty sequence. This range must
     * be covered by using the return value of [getExceptionHandlingLocalDeferredCode].
     * Otherwise, returns all deferred code starting with the parent context of the one that has [isTryContext] = `true`
     * up to the next parent with [isFunctionRoot] = `true`, in the **reverse** order of how it was added
     * via [addDeferredCode].
     */
    fun getDeferredCodeForThrow(): Sequence<DeferrableExecutable>

    /**
     * For a throwable that passes by the `catch` (an `emerge.core.Error`), and so leaves the function though it is
     * thrown inside a `try` block: all the deferred code that [getExceptionHandlingLocalDeferredCode] does not cover.
     * That is the code that was deferred in the parent of the closest context with [isTryContext] = `true`, up to and
     * including the next parent with [isFunctionRoot] = `true`, in the **reverse** order of how it was added
     * via [addDeferredCode]. If there is no context marked with [isTryContext], this is the same as [getDeferredCodeForThrow].
     */
    fun getDeferredCodeForUncatchableThrow(): Sequence<DeferrableExecutable>

    /**
     * @param loop the loop which is exited or continued; currently must be the [LoopExecutionScopedCTContext.loopNode]
     * of [innermostLoopContext]
     */
    fun getDeferredCodeForBreakOrContinue(loop: BoundLoop<*>): Sequence<DeferrableExecutable>

    /**
     * @return all code that has been deferred in this scope and all of its parent [ExecutionScopedCTContext]s up until
     * the [isFunctionRoot] context, in the **reverse** order of how it was added to
     * [addDeferredCode].
     */
    fun getFunctionDeferredCode(): Sequence<DeferrableExecutable>

    /**
     * Intended to be called solely by [BoundMixinStatement] during [SemanticallyAnalyzable.semanticAnalysisPhase2].
     * Registers this mixin in the parent class context.
     * @param type the type of the mixed-in object
     * @return the backing field in which to store the reference to the delegate during the objects lifetime.
     * `null` iff the mixin is not legal in this context. In that case, the reason has been added to [diagnosis]
     * by [registerMixin].
     */
    fun registerMixin(mixinStatement: BoundMixinStatement, type: BoundTypeReference, diagnosis: Diagnosis): MixinRegistration?

    /**
     * Adds code to be returned from [getScopeLocalDeferredCode] and [getFunctionDeferredCode]
     */
    fun addDeferredCode(code: DeferrableExecutable)

    /**
     * The IR object resembling this scope; throws an exception unless [isScopeBoundary].
     * This object is included into IR by [compiler.binding.BoundCodeChunk].
     */
    val irScope: IrVariableDeclaration.Scope

    /**
     * @see [ExecutionScopedCTContext.repetitionRelativeToParent]
     */
    enum class Repetition(
        /** whether code in this context could execute more than once */
        val mayRepeat: Boolean,
    ) {
        /** for simple, linear code inside a function */
        EXACTLY_ONCE(false),
        /** for branches of IF */
        MAYBE(false),
        /** loop bodies that cannot be proven at compile time to execute at least once */
        ZERO_OR_MORE(true),
        /** loop bodies that **can** be proven at compile time to execute at least once, e.g. do-while loop bodies */
        ONCE_OR_MORE(true),
        ;
    }

    interface MixinRegistration {
        /**
         * To be called during IR generation.
         * @return the field where the mixin can store the reference to the mixed-in object.
         */
        fun obtainField(): BaseTypeField

        fun addDestructingAction(action: DestructorCodeGenerator)
    }
}

open class MutableExecutionScopedCTContext protected constructor(
    parentContext: CTContext,
    final override val isScopeBoundary: Boolean,
    final override val isFunctionRoot: Boolean,
    override val repetitionRelativeToParent: ExecutionScopedCTContext.Repetition,
) : MutableCTContext(parentContext), ExecutionScopedCTContext {
    init {
        if (isFunctionRoot) {
            require(isScopeBoundary) { "Invariant violated" }
        }
    }

    private val hierarchy: Sequence<CTContext> = generateSequence(this as CTContext) {
        when (it) {
            is MutableCTContext -> it.parentContext
            is SingleBranchJoinExecutionScopedCTContext -> it.beforeBranch
            is MultiBranchJoinExecutionScopedCTContext -> it.beforeBranch
            is LoopExitJoinExecutionScopedCTContext -> it.beforeLoop
            is InvocationJoinExecutionScopedCTContext -> it.afterArguments
            else -> null
        }
    }

    override val indexedValue: AstSharedValueExpression?
        get() {
            val expiredIndexedValues = ArrayList<AstSharedValueExpression>()
            for (context in hierarchy) {
                when (context) {
                    is AfterIndexExecutionScopedCTContext -> expiredIndexedValues.add(context.valueIndexedBefore)
                    is IndexExecutionScopedCTContext -> if (expiredIndexedValues.none { it === context.valueIndexedHere }) {
                        return context.valueIndexedHere
                    }
                }
            }

            return null
        }

    override val parentScopeContext: ExecutionScopedCTContext? by lazy {
        val parent = hierarchy.drop(1)
            .filterIsInstance<ExecutionScopedCTContext>()
            .firstOrNull { it.isScopeBoundary }

        if (parent == null) {
            check(isScopeBoundary) {
                "This is an edge ${ExecutionScopedCTContext::class.simpleName} (topmost level), must be a scope boundary. But ${this::isScopeBoundary.name} is false."
            }
        }
        parent
    }

    private val parentFunctionContext: ExecutionScopedCTContext? by lazy {
        val parent = hierarchy.drop(1)
            .filterIsInstance<ExecutionScopedCTContext>()
            .firstOrNull { it.isFunctionRoot }

        if (parent == null) {
            check(isFunctionRoot) {
                "This is an edge ${ExecutionScopedCTContext::class.simpleName} (topmost level), must be a function root. But ${this::isFunctionRoot} is false."
            }
        }
        parent
    }

    /**
     * the closest context with [isTryContext] = `true`; that is `this` for the first statement of a `try` block
     */
    private val closestTryContext: ExecutionScopedCTContext? by lazy {
        hierarchy
            .filterIsInstance<ExecutionScopedCTContext>()
            .firstOrNull { it.isTryContext }
    }

    protected val parentLoopContext: LoopExecutionScopedCTContext<*>? by lazy {
        hierarchy.drop(1)
            .filterIsInstance<LoopExecutionScopedCTContext<*>>()
            .firstOrNull()
    }
    override val innermostLoopContext: LoopExecutionScopedCTContext<*>? get() = parentLoopContext

    override val isTryContext = false
    override val isInTryContext get() = closestTryContext != null

    private var localDeferredCode: ArrayList<DeferrableExecutable>? = null

    override fun addDeferredCode(code: DeferrableExecutable) {
        if (localDeferredCode == null) {
            localDeferredCode = ArrayList()
        }
        localDeferredCode!!.add(code)
    }

    private fun getDeferredCodeUpToIncluding(boundary: CTContext): Sequence<DeferrableExecutable> {
        return hierarchy
            .takeWhileAndNext { it !== boundary }
            .flatMap {
                (it as? MutableExecutionScopedCTContext)?.localDeferredCode?.asReversed() ?: emptyList()
            }
    }

    override fun getContextLocalDeferredCode(): Sequence<DeferrableExecutable> {
        return (localDeferredCode ?: emptyList()).asReversed().asSequence()
    }

    override fun getScopeLocalDeferredCode(): Sequence<DeferrableExecutable> {
        if (isScopeBoundary) {
            return getContextLocalDeferredCode()
        }

        return getDeferredCodeUpToIncluding(parentScopeContext ?: this)
    }

    override fun getExceptionHandlingLocalDeferredCode(): Sequence<DeferrableExecutable> {
        closestTryContext
            ?.let { return getDeferredCodeUpToIncluding(it) }

        return emptySequence()
    }

    override fun getDeferredCodeForThrow(): Sequence<DeferrableExecutable> {
        if (closestTryContext != null) {
            return emptySequence()
        }

        return getFunctionDeferredCode()
    }

    override fun getDeferredCodeForUncatchableThrow(): Sequence<DeferrableExecutable> {
        val tryContext = closestTryContext ?: return getFunctionDeferredCode()
        val functionContext = parentFunctionContext ?: this
        return hierarchy
            .dropWhile { it !== tryContext }
            .drop(1)
            .takeWhileAndNext { it !== functionContext }
            .flatMap {
                (it as? MutableExecutionScopedCTContext)?.localDeferredCode?.asReversed() ?: emptyList()
            }
    }

    override fun getDeferredCodeForBreakOrContinue(loop: BoundLoop<*>): Sequence<DeferrableExecutable> {
        val loopContext = innermostLoopContext
        check(loopContext != null)
        check(loopContext.loopNode === loop)

        return getDeferredCodeUpToIncluding(loopContext)
    }

    override fun getFunctionDeferredCode(): Sequence<DeferrableExecutable> {
        return getDeferredCodeUpToIncluding(parentFunctionContext ?: this)
    }

    override val irScope: IrVariableDeclaration.Scope by lazy {
        check(isScopeBoundary)

        IrLexicalVariableScopeImpl()
    }

    fun addVariable(boundVariable: BoundVariable) {
        if (boundVariable.context !in hierarchy) {
            throw InternalCompilerError("Cannot add a variable that has been bound to a different context")
        }

        _variables[boundVariable.name] = boundVariable
    }

    private val sideEffectsBySubjectAndClass: MutableMap<Any, MutableMap<EphemeralStateClass<*, *, *>, SequencedSet<SideEffect<*>>>> by lazy { IdentityHashMap() }
    fun trackSideEffect(effect: SideEffect<*>) {
        val byEffectClass = sideEffectsBySubjectAndClass.computeIfAbsent(effect.subject) { HashMap() }
        val effectList = byEffectClass.computeIfAbsent(effect.stateClass) { LinkedHashSet() }
        effectList.add(effect)
    }

    override fun <Subject : Any, State> getEphemeralState(stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        val stateOnEntry = stateOnEntry(parentContext.getEphemeralState(stateClass, subject), stateClass, subject)
        return applySelfEffects(stateOnEntry, stateClass, subject)
    }

    /**
     * @param stateFromParent the state as of the end of the parent context
     * @return the state when entering this context, before the [SideEffect]s tracked on this context
     */
    protected open fun <Subject : Any, State> stateOnEntry(
        stateFromParent: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State = stateFromParent

    override fun <Subject : Any, State> getEphemeralStateRelativeTo(
        ancestor: CTContext,
        stateInAncestor: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        if (this === ancestor) {
            return stateInAncestor
        }

        val parentState = parentContext.getEphemeralStateRelativeTo(ancestor, stateInAncestor, stateClass, subject)
        return applySelfEffects(stateOnEntry(parentState, stateClass, subject), stateClass, subject)
    }

    private fun <Subject : Any, State> applySelfEffects(parentState: State, stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        val selfEffects = sideEffectsBySubjectAndClass[subject]?.get(stateClass) ?: return parentState

        // trackSideEffect is responsible for the type safety!
        @Suppress("UNCHECKED_CAST")
        selfEffects as Iterable<SideEffect<Subject>>
        @Suppress("UNCHECKED_CAST")
        stateClass as EphemeralStateClass<Subject, State, in SideEffect<Subject>>

        return selfEffects.fold(parentState, stateClass::fold)
    }

    override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? {
        _variables[name]?.let { return it }

        val fromImport = if (fromOwnFileOnly) null else {
            imports
                .asSequence()
                .mapNotNull { it.getVariableOfName(name) }
                .firstOrNull()
        }

        return fromImport ?: parentContext.resolveVariable(name, fromOwnFileOnly)
    }

    override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean {
        if (_variables.containsValue(variable)) return true

        if (this === boundary) {
            return false
        }

        return (parentContext as? ExecutionScopedCTContext)?.containsWithinBoundary(variable, boundary) ?: false
    }

    override fun getRepetitionBehaviorRelativeTo(indirectParent: CTContext): ExecutionScopedCTContext.Repetition {
        return hierarchy
            .takeWhileIsInstance<ExecutionScopedCTContext>()
            .takeWhile { it != indirectParent }
            .map { it.repetitionRelativeToParent }
            .fold(ExecutionScopedCTContext.Repetition.EXACTLY_ONCE) { carry, repetition ->
                when (carry) {
                    ExecutionScopedCTContext.Repetition.EXACTLY_ONCE -> repetition
                    ExecutionScopedCTContext.Repetition.MAYBE -> when(repetition) {
                        ExecutionScopedCTContext.Repetition.EXACTLY_ONCE -> ExecutionScopedCTContext.Repetition.MAYBE
                        ExecutionScopedCTContext.Repetition.MAYBE -> ExecutionScopedCTContext.Repetition.MAYBE
                        ExecutionScopedCTContext.Repetition.ZERO_OR_MORE -> ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
                        ExecutionScopedCTContext.Repetition.ONCE_OR_MORE -> ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
                    }
                    ExecutionScopedCTContext.Repetition.ONCE_OR_MORE -> when(repetition) {
                        ExecutionScopedCTContext.Repetition.EXACTLY_ONCE -> carry
                        ExecutionScopedCTContext.Repetition.MAYBE -> ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
                        ExecutionScopedCTContext.Repetition.ONCE_OR_MORE -> ExecutionScopedCTContext.Repetition.ONCE_OR_MORE
                        ExecutionScopedCTContext.Repetition.ZERO_OR_MORE -> ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
                    }
                    ExecutionScopedCTContext.Repetition.ZERO_OR_MORE -> when(repetition) {
                        ExecutionScopedCTContext.Repetition.EXACTLY_ONCE -> carry
                        ExecutionScopedCTContext.Repetition.MAYBE -> ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
                        ExecutionScopedCTContext.Repetition.ONCE_OR_MORE -> ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
                        ExecutionScopedCTContext.Repetition.ZERO_OR_MORE -> ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
                    }
                }
            }
    }

    override fun registerMixin(mixinStatement: BoundMixinStatement, type: BoundTypeReference, diagnosis: Diagnosis): ExecutionScopedCTContext.MixinRegistration? {
        if (parentContext !is ExecutionScopedCTContext) {
            diagnosis.mixinNotAllowed(mixinStatement)
            return null
        }

        return parentContext.registerMixin(mixinStatement, type, diagnosis)
    }

    override fun toString(): String {
        var str = "MutExecCT["
        if (parentContext is ExecutionScopedCTContext) {
            str += "nested"
        } else {
            str += "root"
        }

        if (isFunctionRoot) {
            str += ", functionRoot"
        } else if (isScopeBoundary) {
            str += ", scopeBoundary"
        }

        str += "]"

        return str
    }

    companion object {
        fun functionRootIn(parentContext: CTContext): MutableExecutionScopedCTContext {
            return MutableExecutionScopedCTContext(parentContext, isScopeBoundary = true, isFunctionRoot = true, repetitionRelativeToParent = ExecutionScopedCTContext.Repetition.EXACTLY_ONCE)
        }

        fun deriveNewScopeFrom(
            parentContext: ExecutionScopedCTContext,
            repetitionRelativeToParent: ExecutionScopedCTContext.Repetition = ExecutionScopedCTContext.Repetition.EXACTLY_ONCE
        ): MutableExecutionScopedCTContext {
            return MutableExecutionScopedCTContext(parentContext, isScopeBoundary = true, isFunctionRoot = false, repetitionRelativeToParent)
        }

        fun <LoopNode : BoundLoop<*>> deriveNewLoopScopeFrom(
            parentContext: ExecutionScopedCTContext,
            isGuaranteedToExecuteAtLeastOnce: Boolean,
            getBoundLoopNode: () -> LoopNode,
        ): LoopExecutionScopedCTContext<LoopNode> {
            return LoopExecutionScopedCTContext(parentContext, isGuaranteedToExecuteAtLeastOnce, getBoundLoopNode)
        }

        fun deriveFrom(parentContext: ExecutionScopedCTContext): MutableExecutionScopedCTContext {
            return MutableExecutionScopedCTContext(parentContext, isScopeBoundary = false, isFunctionRoot = false, repetitionRelativeToParent = ExecutionScopedCTContext.Repetition.EXACTLY_ONCE)
        }

        /**
         * Like [deriveFrom], but the code in the new context may or may not be executed, e.g. the right-hand side
         * of `and`.
         */
        fun deriveConditionalFrom(parentContext: ExecutionScopedCTContext): MutableExecutionScopedCTContext {
            return MutableExecutionScopedCTContext(parentContext, isScopeBoundary = false, isFunctionRoot = false, repetitionRelativeToParent = ExecutionScopedCTContext.Repetition.MAYBE)
        }
    }
}

/**
 * Models the context after a conditional branch, where the branch may or may not be taken at runtime.
 * Information from [whenNotTaken] is definitely available and [SideEffect]s from [atEndOfBranch] are considered
 * using [EphemeralStateClass.combineMaybe].
 */
class SingleBranchJoinExecutionScopedCTContext(
    internal val beforeBranch: ExecutionScopedCTContext,
    private val atEndOfBranch: ExecutionScopedCTContext,
    /**
     * The context of the path where the branch is not taken, e.g. after the condition of an `if` without `else` was
     * false. Must be [beforeBranch] or derived from it.
     */
    private val whenNotTaken: ExecutionScopedCTContext = beforeBranch,
) : ExecutionScopedCTContext by beforeBranch {
    override fun <Subject : Any, State> getEphemeralState(
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        return join(beforeBranch.getEphemeralState(stateClass, subject), stateClass, subject)
    }

    override fun <Subject : Any, State> getEphemeralStateRelativeTo(
        ancestor: CTContext,
        stateInAncestor: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        if (this === ancestor) {
            return stateInAncestor
        }

        return join(beforeBranch.getEphemeralStateRelativeTo(ancestor, stateInAncestor, stateClass, subject), stateClass, subject)
    }

    private fun <Subject : Any, State> join(stateBeforeBranch: State, stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        val stateWhenNotTaken = whenNotTaken.getEphemeralStateRelativeTo(beforeBranch, stateBeforeBranch, stateClass, subject)
        if (stateClass.joinsOnlyBranchesThatCompleteNormally && !atEndOfBranch.canCompleteNormally(beforeBranch)) {
            return stateWhenNotTaken
        }

        val stateAfterBranch = atEndOfBranch.getEphemeralStateRelativeTo(beforeBranch, stateBeforeBranch, stateClass, subject)
        return stateClass.combineMaybe(stateWhenNotTaken, stateAfterBranch)
    }
}

/**
 * Models the context after a conditional branch where there are many choices, and it is guaranteed that
 * one of them is taken.
 * Information from [beforeBranch] is definitely available and [SideEffect]s from [atEndOfBranches] are considered
 * using [EphemeralStateClass.combineExclusiveBranches]
 */
class MultiBranchJoinExecutionScopedCTContext(
    internal val beforeBranch: ExecutionScopedCTContext,
    private val atEndOfBranches: Iterable<ExecutionScopedCTContext>,
) : ExecutionScopedCTContext by beforeBranch {
    override fun <Subject : Any, State> getEphemeralState(
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        return join(beforeBranch.getEphemeralState(stateClass, subject), stateClass, subject)
    }

    override fun <Subject : Any, State> getEphemeralStateRelativeTo(
        ancestor: CTContext,
        stateInAncestor: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        if (this === ancestor) {
            return stateInAncestor
        }

        return join(beforeBranch.getEphemeralStateRelativeTo(ancestor, stateInAncestor, stateClass, subject), stateClass, subject)
    }

    private fun <Subject : Any, State> join(stateBeforeBranch: State, stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        var branches = atEndOfBranches.asSequence()
        if (stateClass.joinsOnlyBranchesThatCompleteNormally) {
            branches = branches.filter { it.canCompleteNormally(beforeBranch) }
            if (branches.none()) {
                // the code after is unreachable
                return stateBeforeBranch
            }
        }

        return branches
            .map { it.getEphemeralStateRelativeTo(beforeBranch, stateBeforeBranch, stateClass, subject) }
            .reduce(stateClass::combineExclusiveBranches)
    }
}

/**
 * @receiver the context at the end of a branch
 * @return whether the code after the branch can be reached through it: `false` iff it is guaranteed to return, throw,
 * terminate the program, or to `break` or `continue`. The states at a `break` or `continue` reach the code after the
 * loop through [LoopExitJoinExecutionScopedCTContext] instead.
 */
private fun ExecutionScopedCTContext.canCompleteNormally(beforeBranch: ExecutionScopedCTContext): Boolean {
    if (getEphemeralState(CallFrameExit).isGuaranteedToReturnThrowOrTerminate) {
        return false
    }

    return !getEphemeralStateRelativeTo(beforeBranch, LoopJump.initialState, LoopJump, SingletonEphemeralStateClass.Subject).isGuaranteedToJump
}

/**
 * Models the context after a loop. The code after it is reached from [beforeLoop] (the body may not run at all; for a
 * `do-while` loop, that is a simplification), from [atEndOfBody] (the end of the last iteration) and from each `break`
 * and `continue` in [loopContext] (a `continue` leads to the check whether to run another iteration).
 *
 * For an [EphemeralStateClass.joinsOnlyBranchesThatCompleteNormally], the states at the `break`s and `continue`s are
 * not part of the state at [atEndOfBody], so they are joined in here. For all other state classes they are.
 */
class LoopExitJoinExecutionScopedCTContext(
    internal val beforeLoop: ExecutionScopedCTContext,
    private val atEndOfBody: ExecutionScopedCTContext,
    private val loopContext: LoopExecutionScopedCTContext<*>,
) : ExecutionScopedCTContext by beforeLoop {
    override fun <Subject : Any, State> getEphemeralState(
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        return join(beforeLoop.getEphemeralState(stateClass, subject), stateClass, subject)
    }

    override fun <Subject : Any, State> getEphemeralStateRelativeTo(
        ancestor: CTContext,
        stateInAncestor: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        if (this === ancestor) {
            return stateInAncestor
        }

        return join(beforeLoop.getEphemeralStateRelativeTo(ancestor, stateInAncestor, stateClass, subject), stateClass, subject)
    }

    private fun <Subject : Any, State> join(stateBeforeLoop: State, stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        val exits = if (stateClass.joinsOnlyBranchesThatCompleteNormally) {
            listOf(atEndOfBody).filter { it.canCompleteNormally(beforeLoop) } + loopContext.jumpOrigins
        } else {
            listOf(atEndOfBody)
        }

        val stateAtExit = exits
            .map { it.getEphemeralStateRelativeTo(beforeLoop, stateBeforeLoop, stateClass, subject) }
            .reduceOrNull(stateClass::combineExclusiveBranches)
            ?.let { stateClass.combineMaybe(stateBeforeLoop, it) }
            ?: stateBeforeLoop

        return stateClass.exitLoop(stateBeforeLoop, stateAtExit)
    }
}

/**
 * Models the context after an invocation has returned. [afterArguments] must be (an indirect child of)
 * [beforeInvocation]. The [SideEffect]s that happened between the two, while evaluating the arguments, are
 * considered using [EphemeralStateClass.endInvocation].
 */
class InvocationJoinExecutionScopedCTContext(
    private val beforeInvocation: ExecutionScopedCTContext,
    internal val afterArguments: ExecutionScopedCTContext,
) : ExecutionScopedCTContext by afterArguments {
    override fun <Subject : Any, State> getEphemeralState(
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        return join(beforeInvocation.getEphemeralState(stateClass, subject), stateClass, subject)
    }

    override fun <Subject : Any, State> getEphemeralStateRelativeTo(
        ancestor: CTContext,
        stateInAncestor: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        if (this === ancestor) {
            return stateInAncestor
        }

        return join(beforeInvocation.getEphemeralStateRelativeTo(ancestor, stateInAncestor, stateClass, subject), stateClass, subject)
    }

    private fun <Subject : Any, State> join(stateBeforeInvocation: State, stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        val stateAfterArguments = afterArguments.getEphemeralStateRelativeTo(beforeInvocation, stateBeforeInvocation, stateClass, subject)
        return stateClass.endInvocation(stateBeforeInvocation, stateAfterArguments)
    }
}

class LoopExecutionScopedCTContext<LoopNode : BoundLoop<*>>(
    parent: CTContext,
    isGuaranteedToExecuteAtLeastOnce: Boolean,
    private val getBoundLoopNode: () -> LoopNode,
) : MutableExecutionScopedCTContext(
    parent,
    true,
    false,
    if (isGuaranteedToExecuteAtLeastOnce) {
        ExecutionScopedCTContext.Repetition.ONCE_OR_MORE
    } else {
        ExecutionScopedCTContext.Repetition.ZERO_OR_MORE
    }
) {
    override val isTryContext = false
    val loopNode: LoopNode by lazy(getBoundLoopNode)

    override val innermostLoopContext: LoopExecutionScopedCTContext<*> get() = this

    private val _jumpOrigins = ArrayList<ExecutionScopedCTContext>()
    private var jumpOriginsQueried = false

    /**
     * The contexts right before each `break` and `continue` of this loop. See [trackJump].
     */
    val jumpOrigins: List<ExecutionScopedCTContext>
        get() {
            jumpOriginsQueried = true
            return _jumpOrigins
        }

    /**
     * Tracks a `break` or `continue` of this loop, from the context [from] right before it; the code after the loop
     * can be reached from there.
     *
     * Must be called before [jumpOrigins] is queried, so in [compiler.binding.SemanticallyAnalyzable.semanticAnalysisPhase1]:
     * the body of a loop completes phase 1 before its phase 2 starts.
     */
    fun trackJump(from: ExecutionScopedCTContext) {
        if (jumpOriginsQueried) {
            throw InternalCompilerError("The jumps of this loop have already been queried, cannot track another one")
        }
        _jumpOrigins.add(from)
    }

    /** the closest loop that encloses this one, if any */
    val outerLoopContext: LoopExecutionScopedCTContext<*>? get() = parentLoopContext

    private val sideEffectsInBodyBySubjectAndClass: MutableMap<Any, MutableMap<EphemeralStateClass<*, *, *>, SequencedSet<SideEffect<*>>>> by lazy { IdentityHashMap() }
    private val stateClassesQueriedOnEntry: MutableSet<EphemeralStateClass<*, *, *>> = HashSet()

    /**
     * Tracks a [SideEffect] that code in the body of this loop may have. Iterations can follow each other, so at the
     * start of each iteration, the effect may already have happened in a previous one; see [stateOnEntry]. That is
     * the back edge of the loop, which the [SideEffect]s tracked inside the body don't model.
     *
     * Must be called before the state of [SideEffect.stateClass] is queried on this context, so in
     * [compiler.binding.SemanticallyAnalyzable.semanticAnalysisPhase1]: the body of a loop completes phase 1 before
     * its phase 2 starts.
     */
    fun trackSideEffectInBody(effect: SideEffect<*>) {
        if (effect.stateClass in stateClassesQueriedOnEntry) {
            throw InternalCompilerError("${effect.stateClass} has already been queried on this loop context, cannot track $effect in the body anymore")
        }

        val byEffectClass = sideEffectsInBodyBySubjectAndClass.computeIfAbsent(effect.subject) { HashMap() }
        byEffectClass.computeIfAbsent(effect.stateClass) { LinkedHashSet() }.add(effect)

        // the body of the outer loop contains this one
        outerLoopContext?.trackSideEffectInBody(effect)
    }

    override fun <Subject : Any, State> stateOnEntry(
        stateFromParent: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        stateClassesQueriedOnEntry.add(stateClass)
        val effectsInBody = sideEffectsInBodyBySubjectAndClass[subject]?.get(stateClass) ?: return stateFromParent

        // trackSideEffectInBody is responsible for the type safety!
        @Suppress("UNCHECKED_CAST")
        effectsInBody as Iterable<SideEffect<Subject>>
        @Suppress("UNCHECKED_CAST")
        stateClass as EphemeralStateClass<Subject, State, in SideEffect<Subject>>

        val stateAfterPreviousIteration = effectsInBody.fold(stateFromParent, stateClass::fold)
        return stateClass.combineMaybe(stateFromParent, stateAfterPreviousIteration)
    }
}

class TryBlockExecutionScopedCTContext(
    parent: CTContext,
) : MutableExecutionScopedCTContext(
    parent,
    isScopeBoundary = true,
    isFunctionRoot = false,
    ExecutionScopedCTContext.Repetition.MAYBE,
) {
    override val isTryContext = true
}

/**
 * The context of an index expression, e.g. `i` in `array[i]`: here, `$` refers to the size of [valueIndexedHere].
 */
class IndexExecutionScopedCTContext(
    parent: ExecutionScopedCTContext,
    val valueIndexedHere: AstSharedValueExpression,
) : MutableExecutionScopedCTContext(
    parent,
    isScopeBoundary = false,
    isFunctionRoot = false,
    ExecutionScopedCTContext.Repetition.EXACTLY_ONCE,
)

/**
 * The context after the index expressions of [valueIndexedBefore]. Binding them derives contexts from
 * [IndexExecutionScopedCTContext], so all code bound after them has one as an ancestor; this context ends its effect.
 */
class AfterIndexExecutionScopedCTContext(
    parent: ExecutionScopedCTContext,
    val valueIndexedBefore: AstSharedValueExpression,
) : MutableExecutionScopedCTContext(
    parent,
    isScopeBoundary = false,
    isFunctionRoot = false,
    ExecutionScopedCTContext.Repetition.EXACTLY_ONCE,
)
