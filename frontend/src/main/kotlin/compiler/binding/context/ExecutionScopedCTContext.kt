package compiler.binding.context

import compiler.InternalCompilerError
import compiler.TakeWhileAndNextIterator.Companion.takeWhileAndNext
import compiler.ast.Statement
import compiler.ast.Statement.Companion.chain
import compiler.ast.VariableDeclaration
import compiler.binding.BoundExecutable
import compiler.binding.BoundVariable
import compiler.binding.context.effect.EphemeralStateClass
import compiler.binding.context.effect.SideEffect
import java.util.IdentityHashMap

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
     * @return Whether this context contains the given variable. Only parent contexts up to and including the
     *         given `boundary` will be searched.
     */
    fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean

    /**
     * @return code that has been deferred in _this very_ [ExecutionScopedCTContext], in the **reverse** order
     * of how it was added to [MutableExecutionScopedCTContext.addDeferredCode].
     */
    fun getContextLocalDeferredCode(): Sequence<BoundExecutable<*>>

    /**
     * @return all code that has been deferred in this [ExecutionScopedCTContext]s scope, in the
     * **reverse** order of how it was added to [MutableExecutionScopedCTContext.addDeferredCode].
     */
    fun getScopeLocalDeferredCode(): Sequence<BoundExecutable<*>>

    /**
     * @return all code that has been deferred in this scope and all of its parent [ExecutionScopedCTContext]s up until
     * the [isFunctionRoot] context, in the **reverse** order of how it was added to
     * [MutableExecutionScopedCTContext.addDeferredCode].
     */
    fun getFunctionDeferredCode(): Sequence<BoundExecutable<*>>
}

open class MutableExecutionScopedCTContext protected constructor(
    val parentContext: CTContext,
    final override val isScopeBoundary: Boolean,
    final override val isFunctionRoot: Boolean,
) : MutableCTContext(parentContext), ExecutionScopedCTContext {
    init {
        if (isFunctionRoot) {
            require(isScopeBoundary) { "Invariant violated" }
        }
    }

    private val hierarchy: Sequence<CTContext> = generateSequence(this as CTContext) { (it as? MutableExecutionScopedCTContext)?.parentContext }

    private val parentScopeContext: ExecutionScopedCTContext? by lazy {
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

    private var localDeferredCode: ArrayList<Statement>? = null

    /**
     * Adds code to be returned from [getScopeLocalDeferredCode] and [getFunctionDeferredCode]
     */
    open fun addDeferredCode(code: Statement) {
        if (localDeferredCode == null) {
            localDeferredCode = ArrayList()
        }
        localDeferredCode!!.add(code)
    }

    private fun getDeferredCodeUpToIncluding(boundary: CTContext): Sequence<BoundExecutable<*>> {
        return hierarchy
            .takeWhileAndNext { it !== boundary }
            .flatMap {
                (it as? MutableExecutionScopedCTContext)?.localDeferredCode?.asReversed() ?: emptyList()
            }
            .chain(this)
    }

    override fun getContextLocalDeferredCode(): Sequence<BoundExecutable<*>> {
        return (localDeferredCode ?: emptyList()).asReversed().chain(this)
    }

    override fun getScopeLocalDeferredCode(): Sequence<BoundExecutable<*>> {
        if (isScopeBoundary) {
            return getContextLocalDeferredCode()
        }

        return getDeferredCodeUpToIncluding(parentScopeContext ?: this)
    }

    override fun getFunctionDeferredCode(): Sequence<BoundExecutable<*>> {
        return getDeferredCodeUpToIncluding(parentFunctionContext ?: this)
    }

    /**
     * Adds the given variable to this context; possibly overriding its type with the given type.
     */
    fun addVariable(declaration: VariableDeclaration): BoundVariable {
        val bound = declaration.bindTo(this)

        return addVariable(bound)
    }

    fun addVariable(boundVariable: BoundVariable): BoundVariable {
        if (boundVariable.context in hierarchy) {
            _variables[boundVariable.name] = boundVariable
            return boundVariable
        }

        throw InternalCompilerError("Cannot add a variable that has been bound to a different context")
    }

    private val sideEffectsBySubjectAndClass: MutableMap<Any, MutableMap<EphemeralStateClass<*, *, *>, MutableList<SideEffect<*>>>> = IdentityHashMap()
    fun trackSideEffect(effect: SideEffect<*>) {
        val byEffectClass = sideEffectsBySubjectAndClass.computeIfAbsent(effect.subject) { HashMap() }
        val effectList = byEffectClass.computeIfAbsent(effect.stateClass) { ArrayList(2) }
        effectList.add(effect)
    }

    override fun <Subject : Any, State> getEphemeralState(stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        val parentState = parentContext.getEphemeralState(stateClass, subject)
        val selfEffects = sideEffectsBySubjectAndClass[subject]?.get(stateClass) ?: return parentState

        // trackSideEffect is responsible for the type safety!
        @Suppress("UNCHECKED_CAST")
        selfEffects as List<SideEffect<Subject>>
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

    companion object {
        fun functionRootIn(parentContext: CTContext): MutableExecutionScopedCTContext {
            return MutableExecutionScopedCTContext(parentContext, isScopeBoundary = true, isFunctionRoot = true)
        }

        fun deriveNewScopeFrom(parentContext: ExecutionScopedCTContext): MutableExecutionScopedCTContext {
            return MutableExecutionScopedCTContext(parentContext, isScopeBoundary = true, isFunctionRoot = false)
        }

        fun deriveFrom(parentContext: ExecutionScopedCTContext): MutableExecutionScopedCTContext {
            return MutableExecutionScopedCTContext(parentContext, isScopeBoundary = false, isFunctionRoot = false)
        }
    }
}

/**
 * Models the context after a conditional branch, where the branch may or may not be taken at runtime.
 * Information from [beforeBranch] is definitely available and [SideEffect]s from [atEndOfBranch] are considered
 * using [EphemeralStateClass.combineMaybe].
 */
class SingleBranchJoinExecutionScopedCTContext(
    private val beforeBranch: ExecutionScopedCTContext,
    private val atEndOfBranch: ExecutionScopedCTContext,
) : ExecutionScopedCTContext by beforeBranch {
    override fun <Subject : Any, State> getEphemeralState(
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        val stateBeforeBranch = beforeBranch.getEphemeralState(stateClass, subject)
        val stateAfterBranch = atEndOfBranch.getEphemeralState(stateClass, subject)
        return stateClass.combineMaybe(stateBeforeBranch, stateAfterBranch)
    }
}

/**
 * Models the context after a conditional branch where there are many choices, and it is guaranteed that
 * one of them is taken.
 * Information from [beforeBranch] is definitely available and [SideEffect]s from [atEndOfBranches] are considered
 * using [EphemeralStateClass.intersect]
 */
class MultiBranchJoinExecutionScopedCTContext(
    private val beforeBranch: ExecutionScopedCTContext,
    private val atEndOfBranches: Iterable<ExecutionScopedCTContext>,
) : ExecutionScopedCTContext by beforeBranch {
    override fun <Subject : Any, State> getEphemeralState(
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        val states = atEndOfBranches.map { it.getEphemeralState(stateClass, subject) }
        return states.reduce(stateClass::intersect)
    }
}