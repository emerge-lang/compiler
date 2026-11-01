# Type system proofs

Machine-checked proofs about the Emerge type system, written in [Rocq](https://rocq-prover.org/)
(the prover formerly called Coq).

Nothing here is compiled into the compiler yet; the proofs are a specification of what the type
system implemented in `../src/main/kotlin/compiler/binding/type` is supposed to do, checked by a
machine instead of by review. The model is also the executable specification the frontend is checked
against, by computation, over a grid of types: see [the model as an oracle](#the-model-as-an-oracle).

That makes the proofs a regression harness of the type checker. Every change to unify, intersections,
inference or overrides, in the frontend or the model, keeps `./rocq.sh` green and the oracle agreeing:
after a change to the frontend's type system or to `TypeGrid`, run `RocqOracleTests` once, then
`./rocq.sh`, and commit `theories/Generated/Grid.v` with the change. Known divergences are allowed only
through the allowlist in `OracleGrid.v` (`unify_excuses`, and the excuses of each check), each owned by an
item of [`coverage.md`](coverage.md).

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
| `MemberAccess.v`     | reading and writing members through a reference of variant type arguments (members typed `T`, `m T`, `T!`, `T?`, class types of those) | `member_read_sound`, `member_write_sound`                               |
| `Inference.v`        | inference with type variables bound exactly (explicit type arguments, a captured receiver)      | `member_call_sound`                                                     |
| `States.v`           | unify on types without type variables doesn't touch the variable states                       | `unify_free`, `unify_keeps_exact`                                       |
| `Constraints.v`      | inference with lower and upper bounds, and the final values it picks                            | `invocation_sound`, `final_values_satisfy`                              |
| `MemberCalls.v`      | calling a member function with type parameters of its own                                       | `member_call_through_subtypes_sound`                                    |
| `FreeInstances.v`    | instantiating only the type variables (`instantiateFreeVariables`), for types of generic code  | `free_unmentioned`, `free_candidate`                                    |
| `Generics.v`         | transitivity with type parameters and intersections, in the form of never rejecting            | `transitivity_never_fails`                                              |
| `Conjectures.v`      | the conjectures below, and what follows from them directly; imports `Inference.v` for `without_contravariance` | `transitivity_terminating`                                              |
| `Examples.v`         | the headline theorems instantiated on one program, so their premises are known satisfiable; the refutation of `unify_always_terminates` | `invocation_instance`, `unify_always_terminates_is_false` |
| `FinalValues.v`      | member calls are sound whatever the final values of inference are                               | `member_call_with_any_final_values_sound`                               |
| `SubstitutionTerminating.v` | substitution with intersections as assignees, where unify terminates                      | `substitution_terminating`                                              |
| `SubstitutionWide.v` | substitution with intersections in type arguments, where unify terminates                       | `substitution_wide`                                                     |
| `GenericArguments.v` | inference with the type parameters of the caller in the arguments: calls in generic code, also of functions whose bounds mention type variables, the final values as Kotlin picks them, also of variables without a lower bound | `member_call_in_generic_code_sound`, `generic_invocation_with_bounded_variables_sound`, `generic_member_call_with_bounded_variables_sound`, `member_call_with_any_final_values_and_intersections_sound` |
| `MemberIntersections.v` | reading and writing members typed as intersections (`A & T`), where unify terminates     | `intersection_member_read_sound`, `intersection_member_write_sound`     |
| `WithinBounds.v`     | type arguments within their declared bounds are within the effective bounds of references       | `bound_in_derived`                                                      |
| `Overrides.v`        | what a call is checked against holds of the override dynamic dispatch runs                      | `override_parameter`, `override_return`, `override_receiver`            |
| `GenericCode.v`      | calls in generic code stay sound with the type parameters of the caller instantiated            | `member_call_in_generic_code_instantiated`, `generic_member_call_with_bounded_variables_instantiated` |
| `GenericReceivers.v` | calls in generic code on receivers mentioning the type parameters of the caller, at run time      | `member_call_on_generic_receiver`, `generic_receiver_with_bounded_variables_sound` |
| `Composition.v`      | instantiating twice is instantiating once with the bindings instantiated: member access in generic code, overrides | `generic_member_read_sound`, `generic_member_write_sound`, `override_parameter_composed`, `override_return_composed` |
| `FBounded.v`         | inference with type variables bounded by type variables (`B : List<A>`, `T : A & Comparable<T>`), for free and member functions, also of classes whose type parameters are bounded so (`class Node<T : Ord<in T>>`) | `invocation_with_bounded_variables_sound`, `member_call_with_bounded_variables_sound` |
| `Explicit.v`         | explicit type arguments for a function whose type parameters are bounded by types mentioning them, bound in turn and checked against their bounds | `explicit_invocation_with_bounded_variables_sound` |
| `Oracle.v`           | the machinery of the oracle: an `Environment` made of the frontend's tables, the comparison of answers, the checks of the conjectures, each shown to be the conjecture restricted to a grid | `report_sound`, `checked`, `mentions_only_b_iff` |
| `Generated/Grid.v`   | generated by `RocqOracleTests`: `TypeGrid` as an `Environment`, and the frontend's answers over it | |
| `OracleGrid.v`       | the model evaluated on the grid, against the frontend; the allowlist of known divergences | `unify_agrees`, `conjectures_checked`, `encoding_agrees` |

### Fragments

Most results hold for a fragment of the types, a boolean predicate on `EType`:

| fragment      | defined in        | admits                                                                                                  |
|---------------|-------------------|---------------------------------------------------------------------------------------------------------|
| `in_fragment` | `Transitivity.v`  | class types with as many type arguments as type parameters, of any variance and ownership; nullable class types |
| `gfrag`       | `Fragment.v`      | `in_fragment`, plus references to type parameters and non-empty intersections of class types and non-null references, or of components that keep their nullability (`A? & P` with `P : Any?`), as `ofComponents` builds them: the components assigned as the same mutability; well-formed references are `refs_wf` (`Generics.v`) |
| `sfrag`       | `Substitution.v`  | the types instantiated by the substitution: class types (Nothing of any mutability), nullable class types, and references to type parameters with their own mutability and nullability (`T`, `m T`, `T!`) or nullable (`T?`), bounded by such a type or an intersection of them, nullable or not; the bound may mention other type parameters |
| `tfrag`       | `Substitution.v`  | the types instantiated at the top, rather than in a type argument: `sfrag`, and intersections of class types and non-null references of it, nullable or not, as `ofComponents` builds them |
| `cfrag`       | `Substitution.v`  | what the types of `tfrag` become: `in_fragment`, and intersections of class types of it, nullable or not |
| `wtfrag`      | `SubstitutionWide.v` | `tfrag`, with intersections in type arguments, too (`Box<A & T>`, `Box<A? & P>`)                      |
| `ktfrag`      | `SubstitutionWide.v` | `wtfrag`, and intersections whose components keep their nullability (`A? & P` with `P : Any?`), nullable or not |
| `ground`      | `SubstitutionWide.v` | what the types of `ktfrag` become: `gfrag` without type parameters                                   |
| `ifrag`       | `Inference.v`     | the types of parameters during inference: `sfrag`, with type variables in place of type parameters, plain at the top, and in type arguments also of a mutability given to them, narrowed, or made nullable (`Box<mut T>`, `Box<T!>`, `Box<T?>`: `nfrag`). Theorems narrow it: FBounded takes the final values to be class types where type variables in type arguments aren't plain (`args_plain`); in generic code, those made nullable are narrowed or of non-null bounds (`args_narrowed`; of bounds, the bounded variable among them, `bplain`) |
| `pfrag`       | `Inference.v`     | the types of parameters at their top: `ifrag`, and a type variable of a mutability given to it and narrowed or not (`x: mut T`, `x: T!`), or made nullable (`x: T?`, `x: mut T?`), narrowed where its bound is nullable, as the compiler builds `T?` |
| `qfrag`       | `Inference.v`     | the types of parameters of the call theorems: `pfrag`, and intersections, nullable or not, of components of `compfrag` assigned as one mutability, as `ofComponents` builds them (`x: T & A`, `x: T? & A?`) |
| `kqfrag`      | `Inference.v`     | the types of parameters of the theorems on calls outside generic code (`Constraints.invocation_sound`, `FBounded`, `MemberCalls`, `Explicit`, `Inference.member_call_sound`) and in it (`GenericArguments.generic_invocation_sound`, `member_call_in_generic_code_sound`): `qfrag`, and intersections whose components keep their nullability, of nullable class types and type variables whose bound may be null (`x: A? & T`) |
| `compfrag`    | `Inference.v`     | the components of intersections in bounds: `ifrag`, and a type variable of a mutability given to it or narrowed (`A & mut U`, `A & U!`), as `ofComponents` gives every component the common mutability and narrows one whose bound is nullable |
| `afrag`       | `Inference.v`     | the types of arguments: `in_fragment`                                                                    |
| `yfrag`       | `GenericArguments.v` | the types of arguments in generic code: `gfrag`, Nothing only as `Nothing`, not as an intersection or a type parameter bounded by it (`bottom_only`), the type parameters of the caller none of those inferred |
| `caller_type` | `GenericCode.v`   | the types of generic code: `ktfrag`, the references to the type parameters of the caller |

### What the proofs assume

Nothing is an axiom (`./rocq.sh check` gates on that). What the proofs assume, they take as premises
of the theorems, mostly bundled in records:

| assumption                                     | where             | what it says                                                                                       |
|------------------------------------------------|-------------------|----------------------------------------------------------------------------------------------------|
| `wellformed`                                   | `Transitivity.v`  | the class declarations of a program: supertypes transitive and acyclic, type arguments of supertypes as templates that compose, exact (no variance on the type arguments of declared supertypes, as the frontend enforces), mentioning no type variables; Nothing without type parameters, and const, as the frontend declares it (`class Nothing : const Any`); the declared bounds of type parameters mention no type variables; at their top, outside of type arguments, only type parameters of a lower rank (`bounds_ranked`), and in type arguments those and the parameter itself (`bounds_deep_ranked`), as F-bounds do (`T : Comparable<T>`) |
| `bounds_wellformed`                            | `Generics.v`      | the declared bounds of type parameters are of `gfrag`, whose intersections have their components assigned as the same mutability, as `ofComponents` makes them. `FBounded.static_bound` takes the same of the static upper bounds |
| `supertypes_repeat_prescriptions`              | `Transitivity.v`  | for `prescriptions_carry_over_to_supertypes` only: supertypes repeat prescribed ownerships        |
| `inference_types`                              | `Constraints.v`   | what inference takes of the types variables are replaced with and of their bounds; among it, what `intersect` and `closestCommonSupertypeWith` are assumed to be for those, and that a reference to a variable, of a mutability given to it or narrowed, takes what the variable takes, and stays within the bound so applied (`it_reference_assigns`, `it_reference_within`). `class_types_for_inference` gives it for class types |
| `intersect_stays_in_fragment`, `closest_common_supertype_stays_in_fragment` | `Conjectures.v` | conjecture: both functions build types of `gfrag` from types of it; `intersect` where the operands don't keep their nullability (`keeps_nullability`: both may be null, one a reference to a type parameter of a nullable bound as it is), as of `A?` and `P : Any?` it makes `A? & P` (coverage #15) |
| `intersect_always_stays_in_fragment`           | `Conjectures.v`   | conjecture: `intersect` builds types of `gfrag` from all types of it, `A? & P` among them (coverage #15); the theorems of generic code (`GenericArguments`, `GenericCode`, `GenericReceivers`) take it |
| `intersect_makes_no_bare_nullable`, `closest_common_supertype_makes_no_bare_nullable` | `Conjectures.v` | conjecture: neither function makes a reference to a type parameter of a nullable bound, as it is, nor an intersection that keeps the nullability of its components, of types that aren't. With it, the bounds of the variables of non-generic code never are, and so never keep their nullability with another (`FinalValues.bound_fragment`) |
| `intersect_is_below_both`, `closest_common_supertype_is_above_both` | `Conjectures.v` | conjecture: the intersection is below both types, the closest common supertype above both. `OracleGrid.v` checks these and the other conjectures about the two functions over the types of `TypeGrid` (`conjectures_checked`), and `CommonTypesTests` the first instantiated |
| `intersect_stays_in_generic_code`, `closest_common_supertype_stays_in_generic_code` | `GenericCode.v` | conjecture: both functions build types of generic code (`caller_type`) from types of it, `A? & P` among them (coverage #15) |
| `closest_common_supertype_keeps_bottom_only`   | `GenericArguments.v` | conjecture: of two types that are Nothing only as `Nothing` (`bottom_only`), the closest common supertype mentions it only so. Lower bounds of variables stay so, as checking them against static upper bounds with type variables takes |
| `closest_common_supertype_of_classes`          | `Constraints.v`   | conjecture: the closest common supertype of two class types without contravariance (`Inference.without_contravariance`: no in-variant type argument, nested ones included) is a class type without it: lower bounds of variables stay of the types of the arguments, checked against static upper bounds with type variables. Of class types with contravariance it is false, `Box<in A> ⊔ Box<in B> = Box<in A & B>` (coverage #17) |
| `arguments_without_contravariance`             | `Constraints.v`   | premise of a call to a function with a bound that mentions type variables (`FBounded`, `Explicit`): its arguments and explicit type arguments are without contravariance, and the program has `supertypes_without_contravariance`. Calls to other functions take neither (`Constraints.strict`) |
| `supertypes_without_contravariance`            | `Inference.v`     | about the program, taken as part of the one above, so only of calls to functions with bounds that mention type variables: no supertype declaration has an in-variant type argument, nested ones included (`class H<T> : Base<Consumer<in T>>` has one), so normalizing an argument to a supertype keeps it without contravariance. Part of `tame_inheritance`, too |
| dispatch finds a function                      | `Overrides.v`     | not a premise, as the model has no dispatch: a class overrides every function it inherits, or a mixin provides it. The compiler reports `AbstractInheritedFunctionNotImplementedDiagnostic` otherwise (`PossiblyMixedInBoundMemberFunction.semanticAnalysisPhase3`) |
| `unify_terminates_on`                          | `Conjectures.v`   | premise about the environment at hand: unify terminates on `gfrag` in it. The claim that it does wherever inheritance isn't expansive (`non_expansive`, which the frontend enforces in `ExpansiveInheritance.kt`) and the type arguments of supertypes are without contravariance (`tame_inheritance`), `unify_always_terminates`, is false: with `fn f<T : Cn<Cn<in T>>>(t: T)`, deciding `T` below `Cn<in T>` decides it again (`Examples.unify_always_terminates_is_false`); the frontend fails such a goal, the model doesn't (coverage #16) |

The functions `intersect` and `closestCommonSupertypeWith` are fields of the `Environment`, which Rocq
lets be anything; so the conjectures about them are properties of an environment that a theorem
takes as a premise, never axioms, which would be false of some environment and so let Rocq prove
anything. `unify_terminates_on` is about the model alone, but a premise all the same: the claim about every
environment with tame inheritance was refuted (`Examples.v`).

Which environments satisfy `unify_terminates_on` is open (no size of the types decreases, see `Conjectures.v`).
Where a program doesn't, the frontend fails a goal that comes up again, and so rejects the program; it never
accepts one for it. The theorems resting on it are about unifications it never runs: of instances of
generic code and of final values of inference. For those, unify never rejecting is proven without it;
only that it also accepts rests on it. That is a gap in the proof, not a known way to accept an unsound
program.

### Coverage

What the proofs cover and what they don't, area by area, is in [`coverage.md`](coverage.md).

### Names of binders

Binders are short, as is usual in proofs, and a short name always stands for the same kind of thing, in every
file: `n` is fuel wherever it occurs. `./rocq.sh` checks the statements of all lemmas against this table
(`tools/binder_names.py`, from what Rocq prints of them, so binders whose type the source leaves to inference
are checked too). Where nothing fits, a descriptive name of four letters or more is always allowed (`arguments`,
`targs`, `sigma`).

| name                         | stands for                                                                  |
|------------------------------|-----------------------------------------------------------------------------|
| `n`                          | fuel                                                                        |
| `d`                          | depth, or fuel added to another (`fuel * S (S d0) + d1`)                    |
| `k`                          | rank (`parameter_rank`)                                                     |
| `i`, `j`                     | index into a list                                                           |
| `t`, `a`                     | the target and the assignee of `unify`; an argument of a call is its assignee |
| `x`, `y`, `z`                | other types, in order: `x` below `y` below `z`, the operands of `intersect` |
| `C`                          | a component of an intersection                                              |
| `P`, `A`                     | a parameter type and an argument type of a call                             |
| `B`                          | a bound                                                                     |
| `V`                          | the declared type of a member                                               |
| `xs`, `ys`, `zs`, `cs`       | lists of types; `cs` the components of an intersection                      |
| `Ps`, `As`                   | the parameter types and the argument types of a call                        |
| `ps`, `vs`                   | lists of type parameters; `vs` the type variables of a `GenericRef`         |
| `c`, `sub`                   | a class; `sub` one below another                                            |
| `m`, `ms`                    | a mutability, given or not (`option Mutability`); a list of them            |
| `o`, `v`                     | an ownership, a variance                                                    |
| `g`, and `gm nn p vs`        | a `GenericRef`, and its fields: given mutability, narrowed, parameter, variables |
| `p`, `q`                     | type parameters                                                             |
| `b`                          | bindings                                                                    |
| `s`, `st`                    | variable states; one variable state                                         |
| `u`, `uf`                    | a `Unification`; a `UnifyFn`                                                |
| `f`                          | a function                                                                  |
| `Q`, `R`, `W`                | a predicate on types or type parameters, a relation, a predicate on states  |
| `r`, `rs`                    | an alias, an aliasing (`Ops.v`)                                             |
| `T`, `l`                     | the `Type` and a list of a polymorphic lemma (its elements `x`, `y`)        |
| `env`, `declared`            | the environment, the declared bounds                                        |

Kept on purpose: `x y z` for types in order rather than longer names, and the one-letter predicates `Q R W`.

On top of the table:

- **digits** tell apart values of the same stage: `n0 n1`, `s0 s1`, `m0 m1` (`union m0 m1 = union m1 m0`);
- **primes** mark a value derived from another: `n'` is fuel found from `n`, `s'` the states `unify` makes of `s`,
  `s''` those made of `s'`;
- a concept letter followed by a **role letter** is that concept of the role: `ma`, `mt` the mutabilities of the
  assignee and the target, `ct` the class of the target, `vb`, `ob` the variance and ownership of a bound, `mx`
  the mutability of `x`, `Qa`, `Qb` predicates on assignees and on bounds. Concepts are `m c v o g Q`, roles `t`
  (target), `a` (assignee), `r` (receiver), `b` (bound) and `x y z`.

Hypotheses are named after what they are about: `H<name>` is a fact about `<name>` (`Hx: in_fragment env x =
true`), `E<name>` an equation, mostly from `destruct ... eqn:` (`Ex: lookup_binding b p = Some x`), `IH` an
induction hypothesis. The check doesn't look inside proofs: names a tactic chooses, and those a proof gives to
what it takes apart, are as the proof needs them.

## The model as an oracle

The proofs are about the model; that the model is the frontend is review. To check that by
computation too, the model's answers are compared with the frontend's over a grid of types, and the
conjectures about `intersect` and `closestCommonSupertypeWith` are checked of the frontend's results,
both by Rocq, as part of `./rocq.sh`:

1. `RocqOracleTests` (`../src/test/kotlin/compiler/binding/type/RocqOracleTests.kt`) encodes the program
   of `TypeGrid` (`grid.kt`) as an `Environment` of the model: its classes, their type parameters,
   supertypes and parameterized supertypes, the bounds of the type parameters, ranked as the model
   takes them. It encodes every type of the grid as an `EType`, every subterm defined once, and records
   what the frontend makes of each pair: whether one is assignable to the other
   (`evaluateAssignabilityTo`), and the results of `intersect` and `closestCommonSupertypeWith`, which
   become the two lookup tables the `Environment` takes those functions from. Of every type encoded, it
   records what the frontend derives of it: mutability, assignment mutability, nullability, whether it
   is Nothing without null, the base type of its lower bound. Types the encoding makes alike are kept
   once, after checking that the frontend doesn't tell them apart either. It writes all of it to
   `theories/Generated/Grid.v`, which is checked in, and fails when the file was stale, having rewritten
   it: commit the new one.
2. `OracleGrid.v` evaluates the model on the same inputs with `vm_compute`, and fails on any
   difference:
   - `encoding_agrees`: the model derives of every encoded type what the frontend does. An encoding that
     drops what those take into account (an explicit mutability, a `!`, the nullability of a component)
     shows here, rather than as an agreement that means nothing.
   - `unify_agrees`: `is_assignable_to` with a fuel of 200 gives the frontend's answer for every pair.
     Where unify gives no answer with the fuel, that is reported as such (`model := None`), not taken
     for either answer.
   - `conjectures_checked`: every conjecture about `intersect` and `closestCommonSupertypeWith` of
     `Conjectures.v`, `GenericCode.v`, `GenericArguments.v` and `Constraints.v`, over every pair of the
     grid in its fragments. The theorems after it (`intersect_is_below_both_on_grid` and the like) are
     those conjectures, restricted to the grid; the checks are shown to decide them (`Oracle.v`), so
     no Kotlin mirror of a fragment is involved. The conjectures of generic code hold for every list of
     type parameters of the caller: the check takes the least one, and covers the others by
     monotonicity (`mentions_only_mentioned`, `mentions_only_b_mono`).
   - `grid_covers_the_fragments`, `tables_are_found`: the grid has types of every fragment, and the
     `Environment` finds the frontend's result of every pair.

A failure names the pair, as `TypeGrid` writes the types, with both answers or why the conjecture
fails of it, e.g.:

```text
Error: Unable to unify "([], [])" with
 "([{| assignee := "A"; target := "B"; model := Some false; frontend := true |}], [])".
```

**The allowlist** of known divergences is at the top of `OracleGrid.v`: `unify_excuses` for
assignability, and the excuses of each check for the conjectures. Each is named after the item of
[`coverage.md`](coverage.md) that owns it, and says exactly which pairs it explains. An excuse that no
longer explains anything fails the check as well (the second component of each report is the list of
those), so it is removed once the divergence is gone. Don't add one to make a disagreement go away: a
disagreement is a question of which side is right, the model or the frontend.

After changing the frontend's type system, or `TypeGrid`:

1. run `RocqOracleTests` once (from `compiler/`: `mvn -pl frontend -am test -Dkotest.filter.specs='*RocqOracleTests'`);
   it fails, having rewritten `Grid.v`, where that changed; a second run passes;
2. run `./rocq.sh`, and settle every disagreement it reports (or, having widened the grid, update the list
   of `grid_covers_the_fragments`);
3. commit `Grid.v` with the change.

The oracle is most of the cost of `./rocq.sh`: from clean, 7.5 minutes with it, 1 without (2026-10-31, on a
desktop); `OracleGrid.v` compiles in a minute and a half, and `rocqchk` computes it all again.

In CI, the proofs run only after the maven build (`.github/workflows/build-emerge.yaml`), whose tests fail
on a stale `Grid.v`, so a forgotten regeneration shows as that test failing, not as a proof against
outdated answers.

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

**The names of binders**, last: `check` has Rocq print every statement (`Print Module`, which spells out the
type of each binder) and `tools/binder_names.py` fails on a short binder name used for something the
[scheme](#names-of-binders) gives another name.

`rocqchk` re-checks the whole dependency closure including the parts of the standard library in
use, so `check` is noticeably slower than `build` and gets slower as the proofs grow. That is the
price of the second, independent kernel; use `build` while iterating.

## Layout

| path                                     | what                                                |
|------------------------------------------|-----------------------------------------------------|
| [`theories/`](theories)                  | the proofs                                          |
| [`coverage.md`](coverage.md)             | what the proofs cover, and what they don't         |
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

Until one of these lands, the proofs and the Kotlin implementation are connected by review, and by
the oracle over the types of `TypeGrid`; the definitions in `theories/` should be kept recognisably
close to their Kotlin counterparts to keep that review tractable.
