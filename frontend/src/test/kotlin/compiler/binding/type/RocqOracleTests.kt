package compiler.compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeVariance
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.SoftwareContext
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import io.kotest.core.spec.style.FreeSpec
import java.io.File

/**
 * Writes `type-system-proofs/theories/Generated/Grid.v`: the module of [TypeGrid] as an `Environment` of the model, the
 * types of the grid encoded, what [intersect] and [BoundTypeReference.closestCommonSupertypeWith] make of every pair of
 * them, and whether each is below each, as the frontend has it. `OracleGrid.v` evaluates the model on the same pairs.
 * Grid.v is a build product, not checked in: run this before `rocq.sh`.
 */
class RocqOracleTests : FreeSpec({
    "writes Grid.v" {
        val callerParameters = TypeGrid.ctxParameters.map { (TypeGrid.swCtx.parseTypeIn("Ctx", it) as GenericTypeReference).parameter }
        val generated = RocqGridEncoder(TypeGrid.swCtx).render(TypeGrid.types, callerParameters)
        val file = File("type-system-proofs/theories/Generated/Grid.v")
        file.parentFile.mkdirs()
        file.writeText(generated)
    }
})

internal class RocqGridEncoder(private val swCtx: SoftwareContext) {
    private val classIds = LinkedHashMap<BoundBaseType, String>()
    private val parameterIds = LinkedHashMap<BoundTypeParameter, Int>()
    private val commonSuperClasses = LinkedHashMap<List<String>, String>()
    private val pendingClasses = ArrayDeque<BoundBaseType>()
    private val pendingParameters = ArrayDeque<BoundTypeParameter>()
    private val nodes = LinkedHashMap<String, Int>()
    private val nodeTypes = mutableListOf<BoundTypeReference?>()
    private val classDeclarations = LinkedHashMap<String, String>()
    private val supertypes = LinkedHashMap<String, List<String>>()
    private val parameterizedSupertypes = LinkedHashMap<Pair<String, String>, String>()
    private val bounds = LinkedHashMap<Int, String>()

    private fun classOf(baseType: BoundBaseType): String = classIds.getOrPut(baseType) {
        pendingClasses.add(baseType)
        when (baseType) {
            swCtx.any -> "any"
            swCtx.nothing -> "nothing"
            else -> "(K ${classIds.keys.count { it != swCtx.any && it != swCtx.nothing } + 1})"
        }
    }

    private fun parameterOf(parameter: BoundTypeParameter): Int = parameterIds.getOrPut(parameter) {
        pendingParameters.add(parameter)
        parameterIds.size + 1
    }

    private fun mutability(m: TypeMutability?) = when (m) {
        null -> "None"
        TypeMutability.MUTABLE -> "mu"
        TypeMutability.READONLY -> "ro"
        TypeMutability.IMMUTABLE -> "im"
        TypeMutability.EXCLUSIVE -> "ex"
    }

    private fun variance(v: TypeVariance) = when (v) {
        TypeVariance.UNSPECIFIED -> "iv"
        TypeVariance.IN -> "ii"
        TypeVariance.OUT -> "oo"
    }

    private fun node(term: String, type: BoundTypeReference?) = name(nodes.getOrPut(term) { nodeTypes.add(type); nodes.size })

    private fun name(index: Int) = "t" + index.toString(36).uppercase()

    /**
     * The name of the definition of [t] in Grid.v, which defines each subterm once. [template]: the class whose
     * supertypes these are, its type parameters as type arguments of an ownership of their own (`Model.parameter_ownership`)
     */
    fun encode(t: BoundTypeReference, template: BoundBaseType? = null): String = node(term(t, template), t)

    private fun term(t: BoundTypeReference, template: BoundBaseType?): String = when (t) {
        is RootResolvedTypeReference -> "R ${mutability(t.explicitMutability ?: t.original?.mutability)} ${classOf(t.baseType)} " +
            "[${(t.arguments ?: emptyList()).joinToString("; ") { encode(it, template) }}]"
        is NullableTypeReference -> "N ${encode(t.nested, template)}"
        is GenericTypeReference -> {
            check(!t.hasTypeVariables) { "$t has type variables" }
            "G ${mutability(t.givenMutability)} ${t.isNarrowed} ${parameterOf(t.parameter)}"
        }
        is BoundTypeArgument -> {
            val type = t.type
            val ownership = if (template != null && type is GenericTypeReference && type.givenMutability == null && !type.isNarrowed
                && template.typeParameters.orEmpty().contains(type.parameter)) {
                "(po ${parameterOf(type.parameter)})"
            } else "rf"
            "A ${variance(t.variance)} $ownership ${encode(type, template)}"
        }
        is BoundIntersectionTypeReference -> {
            val baseTypes = t.components.map { it.baseTypeOfLowerBound }
            commonSuperClasses.getOrPut(baseTypes.map(::classOf)) { classOf(BoundBaseType.closestCommonSupertypeOf(baseTypes)) }
            "I [${t.components.joinToString("; ") { encode(it, template) }}]"
        }
        else -> error("no encoding of ${t::class.simpleName} $t")
    }

    private fun mutabilityLetter(m: TypeMutability) = when (m) {
        TypeMutability.MUTABLE -> "m"
        TypeMutability.READONLY -> "r"
        TypeMutability.IMMUTABLE -> "i"
        TypeMutability.EXCLUSIVE -> "e"
    }

    private fun classLetter(id: String) = when (id) {
        "any" -> "a"
        "nothing" -> "n"
        else -> id.removePrefix("(K ").removeSuffix(")").toInt().toString(36).uppercase()
    }

    /** of each node, what the frontend derives of it, which the model derives of its encoding: `Oracle.properties_of` */
    private fun properties(t: BoundTypeReference?): String = if (t == null) "-----" else
        mutabilityLetter(t.mutability) + mutabilityLetter(t.assignmentMutability) + (if (t.isNullable) "1" else "0") +
            (if (t.isNonNullableNothing) "1" else "0") + classLetter(classOf(t.baseTypeOfLowerBound))

    /** above that of every other parameter its bound mentions, as `Subtyping.bounds_deep_ranked` takes */
    private fun rankOf(parameter: BoundTypeParameter): Int =
        mentioned(parameter.bound).filter { it != parameter }.maxOfOrNull { rankOf(it) + 1 } ?: 0

    private fun mentioned(t: BoundTypeReference): Set<BoundTypeParameter> = when (t) {
        is RootResolvedTypeReference -> t.arguments.orEmpty().flatMap { mentioned(it.type) }.toSet()
        is NullableTypeReference -> mentioned(t.nested)
        is GenericTypeReference -> setOf(t.parameter)
        is BoundIntersectionTypeReference -> t.components.flatMap(::mentioned).toSet()
        is BoundTypeArgument -> mentioned(t.type)
        else -> emptySet()
    }

    private fun drain() {
        while (pendingClasses.isNotEmpty() || pendingParameters.isNotEmpty()) {
            pendingClasses.removeFirstOrNull()?.let { baseType ->
                val id = classOf(baseType)
                val parameters = baseType.typeParameters.orEmpty()
                parameters.forEach { parameterOf(it) }
                val kind = if (baseType.kind == BoundBaseType.Kind.CLASS) "class_kind" else "interface_kind"
                val declared = baseType.superTypes.clauses.mapNotNull { it.resolvedReference }.joinToString("; ") { encode(it, baseType) }
                classDeclarations[id] = "class_decl $kind ${baseType.isConst} [${parameters.joinToString("; ") { parameterOf(it).toString() }}] [$declared]"
                val transitive = baseType.superTypes.preprocessedInheritanceTree.parameterizedSupertypes.entries
                    .filter { it.key != swCtx.any }
                    .sortedBy { it.key.canonicalName.toString() }
                supertypes[id] = transitive.map { classOf(it.key) }
                transitive.forEach { (superType, parameterized) ->
                    parameterizedSupertypes[id to classOf(superType)] = encode(parameterized, baseType)
                }
            }
            pendingParameters.removeFirstOrNull()?.let { bounds[parameterOf(it)] = encode(it.bound) }
        }
    }

    fun render(grid: List<Pair<String, BoundTypeReference>>, callerParameters: List<BoundTypeParameter>): String {
        fun encodeResult(compute: () -> BoundTypeReference): String = try {
            encode(compute())
        } catch (e: Exception) {
            node("Error None ${string("threw ${e::class.simpleName} ${e.message}")}", null)
        }

        val allNodes = grid.map { (_, t) -> encode(t) }
        val allIntersections = grid.map { (_, a) -> grid.map { (_, b) -> encodeResult { a.intersect(b) } } }
        val allCommonSupertypes = grid.map { (_, a) -> grid.map { (_, b) -> encodeResult { a.closestCommonSupertypeWith(b) } } }
        val allBelow = grid.map { (_, a) -> grid.map { (_, b) -> a.isSubtypeOf(b) } }

        // types encoded alike are checked once; the frontend must not tell them apart, or the encoding would lose what does
        val firstOf = HashMap<String, Int>()
        val kept = grid.indices.filter { i -> firstOf.putIfAbsent(allNodes[i], i) == null }
        grid.indices.forEach { i ->
            val k = firstOf.getValue(allNodes[i])
            fun <T> List<List<T>>.alike() = this[i] == this[k] && all { it[i] == it[k] }
            check(allBelow.alike() && allIntersections.alike() && allCommonSupertypes.alike()) {
                "${grid[i].first} and ${grid[k].first} are encoded alike, but the frontend tells them apart"
            }
        }
        val gridNodes = kept.map { allNodes[it] }
        val intersections = kept.map { i -> kept.map { allIntersections[i][it] } }
        val commonSupertypes = kept.map { i -> kept.map { allCommonSupertypes[i][it] } }
        val below = kept.map { i -> kept.joinToString("") { if (allBelow[i][it]) "1" else "0" } }
        val names = kept.map { k -> grid.indices.filter { allNodes[it] == allNodes[k] }.joinToString(" = ") { grid[it].first } }
        val callerIds = callerParameters.map(::parameterOf)
        classOf(swCtx.any)
        classOf(swCtx.nothing)
        drain()
        val nodeProperties = mutableListOf<String>()
        while (nodeProperties.size < nodeTypes.size) {
            nodeProperties.add(properties(nodeTypes[nodeProperties.size]))
            drain()
        }

        return buildString {
            appendLine("(* Generated by frontend/src/test/kotlin/compiler/binding/type/RocqOracleTests.kt from TypeGrid; do not edit.")
            appendLine("   OracleGrid.v checks the model against it. Not under version control: a build product, rewritten by every run of that")
            appendLine("   test, see frontend/type-system-proofs/readme.md. *)")
            appendLine()
            appendLine("From Stdlib Require Import List String.")
            appendLine("Import ListNotations.")
            appendLine("From EmergeTypeSystem Require Import Model Subtyping Oracle.")
            appendLine("Import GridNotations.")
            appendLine("Local Open Scope string_scope.")
            appendLine()
            appendLine("(* every type below, each defined once: those of the grid, those intersect and closestCommonSupertypeWith make of")
            appendLine("   them, the bounds and the supertypes, and their parts *)")
            nodes.forEach { (term, index) -> appendLine("Definition ${name(index)} := $term.") }
            appendLine()
            appendLine("(* of each type above, in order: its mutability and assignment mutability, whether it is nullable and Nothing")
            appendLine("   without null, and its base type of the lower bound, as the frontend has them (Oracle.properties_of) *)")
            val chunks = nodes.values.chunked(200)
            chunks.forEachIndexed { c, chunk ->
                appendLine("Definition properties_$c: list EType * string := ([${chunk.joinToString("; ") { name(it) }}],")
                appendLine("    ${string(chunk.joinToString("") { nodeProperties[it] })}).")
            }
            appendLine("Definition frontend_properties: list (list EType * string) := [${chunks.indices.joinToString("; ") { "properties_$it" }}].")
            appendLine()
            appendLine("Definition class_names: list (Class * string) := [${classIds.entries.joinToString("; ") { (b, id) -> "($id, ${string(b.simpleName)})" }}].")
            appendLine("Definition parameter_names: list (TypeParameterId * string) := [${parameterIds.entries.joinToString("; ") { (p, id) -> "($id, ${string(p.name)})" }}].")
            appendLine()
            appendLine("Definition classes: list (Class * ClassDecl) := [")
            appendLine(classDeclarations.entries.joinToString(";\n") { (id, decl) -> "    ($id, $decl)" })
            appendLine("].")
            appendLine("Definition transitive_supertypes: list (Class * list Class) := [")
            appendLine(supertypes.entries.joinToString(";\n") { (id, sups) -> "    ($id, [${sups.joinToString("; ")}])" })
            appendLine("].")
            appendLine("Definition parameterized_supertypes: list ((Class * Class) * EType) := [")
            appendLine(parameterizedSupertypes.entries.joinToString(";\n") { (k, v) -> "    ((${k.first}, ${k.second}), $v)" })
            appendLine("].")
            appendLine("Definition common_super_classes: list (list Class * Class) := [")
            appendLine(commonSuperClasses.entries.joinToString(";\n") { (k, v) -> "    ([${k.joinToString("; ")}], $v)" })
            appendLine("].")
            appendLine("Definition bounds: list (TypeParameterId * EType) := [${bounds.entries.joinToString("; ") { (p, b) -> "($p, $b)" }}].")
            appendLine("Definition ranks: list (TypeParameterId * nat) := [${parameterIds.entries.joinToString("; ") { (p, id) -> "($id, ${rankOf(p)})" }}].")
            appendLine()
            appendLine("(* the types of the grid, by the names they are written with in TypeGrid; those encoded alike once *)")
            appendLine("Definition grid: list (string * EType) := [")
            appendLine(kept.indices.joinToString(";\n") { "    (${string(names[it])}, ${gridNodes[it]})" })
            appendLine("].")
            appendLine()
            appendLine("(* the type parameters of Ctx, which the types of the grid mention *)")
            appendLine("Definition caller_parameters: list TypeParameterId := [${callerIds.joinToString("; ")}].")
            appendLine()
            appendLine("(* row i, column j: intersect, closestCommonSupertypeWith of the i-th and the j-th type of the grid *)")
            appendLine("Definition intersections: list (list EType) := [")
            appendLine(intersections.joinToString(";\n") { row -> "    [${row.joinToString("; ")}]" })
            appendLine("].")
            appendLine("Definition common_supertypes: list (list EType) := [")
            appendLine(commonSupertypes.joinToString(";\n") { row -> "    [${row.joinToString("; ")}]" })
            appendLine("].")
            appendLine()
            appendLine("(* row i, column j: 1 where the i-th type of the grid is assignable to the j-th, as the frontend has it *)")
            appendLine("Definition frontend_below: list string := [")
            appendLine(below.joinToString(";\n") { "    \"$it\"" })
            appendLine("].")
            appendLine()
            appendLine("Definition env: Environment := oracle_environment classes transitive_supertypes common_super_classes")
            appendLine("    parameterized_supertypes bounds ranks (map snd grid) intersections common_supertypes.")
        }
    }

    private fun string(s: String) = "\"" + s.replace("\"", "\"\"") + "\""
}
