# Type system proofs

Machine-checked proofs about the Emerge type system, written in [Rocq](https://rocq-prover.org/)
(the prover formerly called Coq).

Nothing here is compiled into the compiler yet; the proofs are a specification of what the type
system implemented in `../src/main/kotlin/compiler/binding/type` is supposed to do, checked by a
machine instead of by review.

## The proofs

The model (`Model.v`, `Subtyping.v`) translates the Kotlin type references and
`BoundTypeReference.unify`; everything else proves properties of it. Each file's header says what
it shows and why; the tables below are the map.

### Files, in dependency order

| file                 | what it shows                                                                                   | headline results                                                        |
|----------------------|-------------------------------------------------------------------------------------------------|-------------------------------------------------------------------------|
| `Model.v`            | the types, mutabilities, variances, ownerships, and the `Environment` of class declarations     |                                                                         |
| `Subtyping.v`        | unify, the model of `BoundTypeReference.unify`, and instantiation                               | `unify_fuel_monotone`                                                   |
| `Ops.v`              | mutability and aliasing: references to a block make no conflicting promises                   | `references_are_conflict_free`, `assignability_respects_mutability`     |
| `Ownership.v`        | owned and ref slots (not implemented in the Kotlin frontend yet)                               | `no_conflicts_through_a_view`, `instantiation_preserves_ownership_assignability` |
| `Transitivity.v`     | well-formed environments; transitivity and reflexivity of unify on class types                  | `transitivity`, `reflexivity`                                           |
| `Fragment.v`         | the fragment of type parameters and intersections, as the frontend builds them                  |                                                                         |
| `Substitution.v`     | instantiating type parameters keeps assignability                                              | `substitution_lemma`                                                    |
| `MemberAccess.v`     | reading and writing members through a reference of variant type arguments                       | `member_read_sound`, `member_write_sound`                               |
| `Inference.v`        | inference with type variables bound exactly (explicit type arguments, a captured receiver)      | `member_call_sound`                                                     |
| `States.v`           | unify on types without type variables doesn't touch the variable states                       | `unify_free`, `unify_keeps_exact`                                       |
| `Constraints.v`      | inference with lower and upper bounds, and the final values it picks                            | `invocation_sound`, `final_values_satisfy`                              |
| `MemberCalls.v`      | calling a member function with type parameters of its own                                       | `member_call_through_subtypes_sound`                                    |
| `Generics.v`         | transitivity with type parameters and intersections, in the form of never rejecting            | `transitivity_never_fails`                                              |
| `Conjectures.v`      | the conjectures below, and what follows from them directly                                     | `transitivity_terminating`                                              |
| `FinalValues.v`      | member calls are sound whatever the final values of inference are                               | `member_call_with_any_final_values_sound`                               |
| `SubstitutionTerminating.v` | substitution with intersections as assignees, where unify terminates                      | `substitution_terminating`                                              |
| `SubstitutionWide.v` | substitution with intersections in type arguments, where unify terminates                       | `substitution_wide`                                                     |
| `GenericArguments.v` | inference with the type parameters of the caller in the arguments: calls in generic code       | `member_call_in_generic_code_sound`                                     |
| `WithinBounds.v`     | type arguments within their declared bounds are within the effective bounds of references       | `bound_in_derived`                                                      |
| `GenericCode.v`      | calls in generic code stay sound with the type parameters of the caller instantiated            | `member_call_in_generic_code_instantiated`                              |
| `GenericReceivers.v` | calls in generic code on receivers mentioning the type parameters of the caller, at run time      | `member_call_on_generic_receiver`                                       |

### Fragments

Most results hold for a fragment of the types, a boolean predicate on `EType`:

| fragment      | defined in        | admits                                                                                                  |
|---------------|-------------------|---------------------------------------------------------------------------------------------------------|
| `in_fragment` | `Transitivity.v`  | class types with as many type arguments as type parameters, of any variance and ownership; nullable class types |
| `gfrag`       | `Fragment.v`      | `in_fragment`, plus references to type parameters and non-empty intersections of class types and non-null references, as `ofComponents` builds them; well-formed references are `refs_wf` (`Generics.v`) |
| `sfrag`       | `Substitution.v`  | the types instantiated by the substitution: class types (Nothing only as `exclusive Nothing`), nullable class types, and references to type parameters with their own mutability and nullability (`T`, `m T`, `T!`) or nullable (`T?`), bounded by such a type or an intersection of them, nullable or not; the bound may mention other type parameters |
| `tfrag`       | `Substitution.v`  | the types instantiated at the top, rather than in a type argument: `sfrag`, and intersections of class types and non-null references of it, nullable or not, as `ofComponents` builds them |
| `cfrag`       | `Substitution.v`  | what the types of `tfrag` become: `in_fragment`, and intersections of class types of it, nullable or not |
| `wtfrag`      | `SubstitutionWide.v` | `tfrag`, with intersections in type arguments, too (`Box<A & T>`)                                     |
| `ground`      | `SubstitutionWide.v` | what the types of `wtfrag` become: `gfrag` without type parameters                                   |
| `ifrag`       | `Inference.v`     | the types of parameters during inference: `sfrag`, with type variables in place of type parameters, bounded by types without type parameters |
| `afrag`       | `Inference.v`     | the types of arguments: `in_fragment`, with Nothing only as `exclusive Nothing`                        |
| `yfrag`       | `GenericArguments.v` | the types of arguments in generic code: `gfrag`, Nothing only as `exclusive Nothing` (`bottom_only`), the type parameters of the caller none of those inferred |
| `caller_type` | `GenericCode.v`   | the types of generic code: `wtfrag`, the references to the type parameters of the caller |

### What the proofs assume

Nothing is an axiom (`./rocq.sh check` gates on that). What the proofs assume, they take as premises
of the theorems, mostly bundled in records:

| assumption                                     | where             | what it says                                                                                       |
|------------------------------------------------|-------------------|----------------------------------------------------------------------------------------------------|
| `wellformed`                                   | `Transitivity.v`  | the class declarations of a program: supertypes transitive and acyclic, type arguments of supertypes as templates that compose, exact (no variance on the type arguments of declared supertypes, as the frontend enforces), mentioning no type variables, and Nothing only as `exclusive Nothing`; the declared bounds of type parameters mention no type variables; at their top, outside of type arguments, only type parameters of a lower rank (`bounds_ranked`), and in type arguments those and the parameter itself (`bounds_deep_ranked`), as F-bounds do (`T : Comparable<T>`) |
| `bounds_wellformed`                            | `Generics.v`      | the declared bounds of type parameters are of `gfrag`, and the components of an intersection in them are assigned as the same mutability, as `ofComponents` makes them (`uniform`) |
| `supertypes_repeat_prescriptions`              | `Transitivity.v`  | for `prescriptions_carry_over_to_supertypes` only: supertypes repeat prescribed ownerships        |
| `inference_types`                              | `Constraints.v`   | what inference takes of the types variables are replaced with and of their bounds; among it, what `intersect` and `closestCommonSupertypeWith` are assumed to be for those. `class_types_for_inference` gives it for class types |
| `intersect_stays_in_fragment`, `closest_common_supertype_stays_in_fragment` | `Conjectures.v` | conjecture: both functions build types of `gfrag` from types of it |
| `intersect_is_below_both`, `closest_common_supertype_is_above_both` | `Conjectures.v` | conjecture: the intersection is below both types, the closest common supertype above both |
| `intersect_stays_in_generic_code`, `closest_common_supertype_stays_in_generic_code` | `GenericCode.v` | conjecture: both functions build types of generic code (`caller_type`) from types of it |
| `unify_terminates`                             | `Conjectures.v`   | conjecture: unify terminates on `gfrag` where inheritance isn't expansive (`non_expansive`, which the frontend enforces in `ExpansiveInheritance.kt`) and the class table is finite. Kennedy and Pierce show subtyping decidable there |

The functions `intersect` and `closestCommonSupertypeWith` are fields of the `Environment`, which Rocq
lets be anything; so the conjectures about them are properties of an environment that a theorem
takes as a premise, never axioms, which would be false of some environment and so let Rocq prove
anything. `unify_terminates` is a claim about the model alone, a theorem yet to be proven.

Proving `unify_terminates` is not straightforward (no size of the types decreases, see `Conjectures.v`),
so it stays a conjecture. Were it false, the frontend would not finish on, and so reject, programs where
it runs unify itself. The theorems resting on it are about unifications it never runs: of instances of
generic code and of final values of inference. For those, unify never rejecting is proven without it;
only that it also accepts rests on it. That is a gap in the proof, not a known way to accept an unsound
program.

### Not covered yet

- Inference with F-bounded type variables.
- Declaration-site variance, which emerge doesn't have.

## Running the proofs

Rocq runs out of the official `rocq/rocq-prover` Docker image, so the only prerequisite is a
working Docker (on Windows: Docker Desktop, and run the script from Git Bash).

```sh
./rocq.sh          # compile all proofs, then check them
./rocq.sh build    # compile only - the fast inner loop while writing a proof
./rocq.sh check    # re-check the compiled proofs, and gate on unproven claims
./rocq.sh clean    # delete the build directory
./rocq.sh repl     # a Rocq REPL with the compiled theory on its load path
./rocq.sh shell    # a shell inside the container
```

The first run pulls the image (~1 GB). CI runs `./rocq.sh verify` too — the same script, the same
container — so a green run here means a green run there.

`ROCQ_IMAGE` overrides the image, `JOBS` the number of parallel compile jobs. The Rocq version is
pinned in `rocq.sh`; bumping it there is the whole upgrade, CI included.

Every artifact of the build lands in `_build/`, so the source tree stays free of `.vo` clutter and
`./rocq.sh clean` is just a directory removal.

## What "check" checks

**`rocqchk`**, Rocq's separate — and much smaller, hence more trustworthy — proof checker,
re-verifies the compiled proofs from the `.vo` files and reports everything they assume rather than
prove: axioms, uses of type-in-type, unsafe fixpoints and assumed positivity. It only *reports*; it
never fails over what it finds. Read its `CONTEXT SUMMARY` in the build log when you want to know
what a proof actually rests on.

**A grep for unproven claims** is what turns that into a gate, because compiling proves less than
it looks like: a theorem closed with `Admitted` compiles without complaint and merely becomes an
axiom, so "it builds" says nothing about whether anything was proven. So `check` also fails on
`Admitted`, `Axiom`, `Conjecture` and the `admit` tactic anywhere under `theories/`. When an
assumption is deliberate, mark the line and it is allowed through:

```coq
Axiom subtyping_is_decidable : ... (* allow-axiom: proof in progress, see #123 *)
```

It is blunt — it cannot see axioms inherited from an imported library, which is why the `rocqchk`
report above it is worth reading — but it reads our own sources rather than Rocq's console output,
so it cannot quietly stop working when a future Rocq rephrases a message. (`Parameter`,
`Hypothesis` and `Variable` are deliberately not flagged: inside sections and module types they are
discharged rather than assumed.)

`rocqchk` re-checks the whole dependency closure including the parts of the standard library in
use, so `check` is noticeably slower than `build` and gets slower as the proofs grow. That is the
price of the second, independent kernel; use `build` while iterating.

## Layout

| path                                     | what                                                |
|------------------------------------------|-----------------------------------------------------|
| [`theories/`](theories)                  | the proofs                                          |
| [`theories/dune`](theories/dune)         | build configuration: theory name and dependencies   |
| [`dune-project`](dune-project)           | dune version and the Rocq build language it uses    |
| [`_CoqProject`](_CoqProject)             | load path **for editors only**, not for the build   |
| [`rocq.sh`](rocq.sh)                     | host entry point, deals with Docker                 |
| [`tools/verify.sh`](tools/verify.sh)     | the build and the checks, run inside the container   |

`theories/Foo/Bar.v` is the module `EmergeTypeSystem.Foo.Bar` and is imported as
`From EmergeTypeSystem Require Import Foo.Bar.`. New files under `theories/` are picked up
automatically — dune discovers them, so nothing needs registering.

The theory name is unfortunately stated twice, in `theories/dune` for the build and in
`_CoqProject` for editors; renaming it means changing both.

Note that the standard library is a separate package since Rocq 9, so its modules are imported as
`From Stdlib Require Import List.`, not `Require Import Coq.Lists.List.`.

## Editor support

Any Rocq IDE picks up `_CoqProject` for the load path, but needs a local Rocq installation to talk
to — the Docker image only serves the command line. For VS Code that is
[VsRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq), which expects
`rocq-language-server`; install Rocq 9.2 via opam to match the pinned image. Such an IDE compiles
in place rather than into `_build/`, which is why `.gitignore` covers `.vo` files next to the
sources as well. dune refuses to build while those exist, so `./rocq.sh` builds a copy of the
sources and leaves them alone.

The IDE only compiles the file that is open, though, never the files it requires: after changing
`Foo.v`, compile it before working in a file that requires it, e.g. with
`rocq compile -Q theories EmergeTypeSystem theories/Foo.v`.

With a local Rocq and dune, `dune rocq top theories/Foo.v` opens a REPL set up for exactly that
file, which `./rocq.sh repl` cannot do from inside the container.

## Generating Kotlin from the proofs

The eventual goal is to derive parts of the Kotlin implementation from the proven definitions, so
that the code the compiler runs is the code that was proven correct. Rocq has no Kotlin backend, so
this will take some work. The options, most promising first:

1. **Extract to JSON, emit Kotlin from that.** `Extraction Language JSON` (verified present in
   9.2) dumps the extracted program as a declaration tree — inductives, constructors, fixpoints,
   matches. A Kotlin emitter for that tree could live in this repo as a small tool and is plain
   data processing, no Rocq plugin needed. The catch is that extraction erases types down to an
   ML-ish core, so the generated Kotlin would need its types reconstructed to be idiomatic.
2. **Pretty-print Kotlin inside Rocq.** Deep-embed the fragment of Kotlin that is needed as an
   inductive type, write the emitter as a Rocq function and `Compute` the result into a `.kt` file.
   More upfront work, but the emitter itself becomes provable, and full control over the output.
3. **A Rocq plugin with a Kotlin extraction backend**, in OCaml, alongside the existing OCaml and
   Haskell ones. Most faithful, by far the most work, and ties the project to Rocq internals.

Until one of these lands, the proofs and the Kotlin implementation are connected by review only,
and the definitions in `theories/` should be kept recognisably close to their Kotlin counterparts
to keep that review tractable.
