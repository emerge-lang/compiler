From Stdlib Require Import List String Bool.
Import ListNotations.
From EmergeTypeSystem Require Import Model Subtyping Transitivity Fragment Conjectures Inference Substitution SubstitutionWide GenericArguments
    Oracle.
From EmergeTypeSystem.Generated Require Import Grid.
Local Open Scope string_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The model, checked against the frontend over TypeGrid                                           *)
(*                                                                                                *)
(* Generated/Grid.v has what the frontend makes of the types of TypeGrid (frontend/src/test/kotlin/ *)
(* compiler/binding/type/grid.kt): whether each is assignable to each (frontend_below), and what   *)
(* intersect and closestCommonSupertypeWith make of each pair, which are the Environment's         *)
(* (Oracle.oracle_environment). This evaluates the model on the same pairs:                        *)
(*                                                                                                *)
(* - unify_agrees: is_assignable_to gives the frontend's answer for every pair, but where an excuse *)
(*   below explains the difference. A pair on which unify gives no answer with the fuel is reported *)
(*   as that (model := None), not as either answer. A disagreement makes the proof fail, and the     *)
(*   error shows it: the names of the two types, as TypeGrid writes them, and both answers.          *)
(* - conjectures_checked: the conjectures about intersect and closestCommonSupertypeWith of         *)
(*   Conjectures.v, GenericCode.v, GenericArguments.v and Constraints.v, over every pair of the grid *)
(*   in their fragments; the theorems after it state them, of the grid.                              *)
(*                                                                                                *)
(* The excuses are the known divergences, each owned by an item of coverage.md. One that explains   *)
(* nothing fails the proof as well (the second component of each report), so that it is removed    *)
(* once the divergence is gone. Everything is computed with vm_compute; Rocq's kernel computes it   *)
(* again at Qed.                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Definition fuel: nat := 200.

Definition name: EType -> string := show class_names parameter_names.

(* ---------------------------------------------------------------------------------------------- *)
(* The known divergences                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

Definition step_14: string :=
    "coverage step 14: the frontend takes an intersection of disjoint classes for Nothing, below every type (BoundIntersectionTypeReference.flippedUnify); the model's intersection_flipped_unify doesn't yet".

Definition blind_spot_18: string :=
    "coverage #18: the closest common supertype of Box<P> and Box<in Nothing?> is Box<in P & Nothing?>, whose in-variant type argument is Nothing without null".

Definition unify_excuses: list Excuse := [
    (step_14, fun a _ model frontend => disjoint_intersection env a && option_bool_eqb model (Some false) && frontend)
].

(* ---------------------------------------------------------------------------------------------- *)
(* The grid                                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* An intersection with a component that keeps its nullability, `A? & P` with `P : Any?` (coverage #15) *)
Definition keeps_nullable_components (t: EType): bool :=
    match t with Intersection cs | Nullable (Intersection cs) => existsb (is_nullable env) cs | _ => false end.

(* The grid has types of each fragment the conjectures are about: all of them of gfrag and of the
   generic code of Ctx (GenericCode.caller_type), more than ten class types without contravariance
   (Inference.afrag, without_contravariance), and class types with it, which closest_common_supertype_of_classes
   leaves out (coverage #17), and these intersections whose components keep their nullability *)
Lemma grid_covers_the_fragments:
    forallb (fun t => gfrag env t && ktfrag env t && mentions_only_b env caller_parameters t) (grid_types grid) = true
    /\ Nat.ltb 10 (List.length (filter (fun t => afrag env t && closed t && without_contravariance t) (grid_types grid))) = true
    /\ existsb (fun t => afrag env t && closed t && negb (without_contravariance t)) (grid_types grid) = true
    /\ map fst (filter (fun x => keeps_nullable_components (snd x)) grid) = [
        "A? & P"; "P & R"; "Nothing? & P"; "A? & R? & P"; "A? & B? & P"; "P & R & A?"; "R & B?"; "mut R & mut B?";
        "D? & P"; "U & R"; "A? & U"; "U & P"].
Proof. vm_compute. repeat split. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Assignability                                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma answers_are_shaped: answers_shaped grid frontend_below = true.
Proof. vm_compute. reflexivity. Qed.

(* The Environment finds the frontend's intersect and closestCommonSupertypeWith of every pair *)
Lemma tables_are_found: tables_found env grid intersections common_supertypes = true.
Proof. vm_compute. reflexivity. Qed.

(* Of every type in Grid.v, its parts among them, the model derives what the frontend does: the
   encoding keeps what those take into account (mutability, nullability, Nothing, base types) *)
Lemma encoding_agrees: flat_map (fun '(types, properties) => property_mismatches env name types properties) frontend_properties = [].
Proof. vm_compute. reflexivity. Qed.

Lemma unify_agrees: comparison env fuel grid unify_excuses frontend_below = ([], []).
Proof. vm_compute. reflexivity. Qed.

(* No value that may be a token is assignable to a type that cannot be one: it is not forgotten, and
   not frozen *)
Lemma tokens_stay_visible: tokens_forgotten env fuel grid = [].
Proof. vm_compute. reflexivity. Qed.

(* Whatever the frontend accepts, unify without the token rules accepts *)
Lemma token_rules_only_reject: accepted_by_the_token_rules_only env fuel grid = [].
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The conjectures about intersect and closestCommonSupertypeWith                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Definition intersect_in_fragment: Check := check "Conjectures.intersect_stays_in_fragment" (intersect_in_fragment_check env name) [].
Definition intersect_always_in_fragment: Check :=
    check "Conjectures.intersect_always_stays_in_fragment" (intersect_always_in_fragment_check env name) [].
Definition intersect_no_bare_nullable: Check :=
    check "Conjectures.intersect_makes_no_bare_nullable" (intersect_no_bare_nullable_check env name) [].
Definition supertype_no_bare_nullable: Check :=
    check "Conjectures.closest_common_supertype_makes_no_bare_nullable" (supertype_no_bare_nullable_check env name) [].
Definition supertype_in_fragment: Check :=
    check "Conjectures.closest_common_supertype_stays_in_fragment" (supertype_in_fragment_check env name) [].
Definition intersect_below: Check := check "Conjectures.intersect_is_below_both" (intersect_below_check env fuel name) [].
(* the closest common supertype of `N & M` with another type is that type, which the model's unify
   doesn't take `N & M` below *)
Definition supertype_above: Check :=
    check "Conjectures.closest_common_supertype_is_above_both" (supertype_above_check env fuel name)
        [(step_14, fun a b _ _ => disjoint_intersection env a || disjoint_intersection env b)].
Definition intersect_in_generic_code: Check :=
    check "GenericCode.intersect_stays_in_generic_code" (intersect_in_generic_code_check env name) [].
Definition supertype_in_generic_code: Check :=
    check "GenericCode.closest_common_supertype_stays_in_generic_code" (supertype_in_generic_code_check env name) [].
(* false of the frontend: excused where only intersections as in-variant type arguments are in the way *)
Definition keeps_bottom_only: Check :=
    check "GenericArguments.closest_common_supertype_keeps_bottom_only" (bottom_only_check env name)
        [(blind_spot_18, fun _ _ _ s => GenericArguments.bottom_only env (without_contravariant_intersections s))].
Definition of_classes: Check := check "Constraints.closest_common_supertype_of_classes" (of_classes_check env name) [].

Definition checks: list Check := [
    intersect_in_fragment; intersect_always_in_fragment; intersect_no_bare_nullable; supertype_no_bare_nullable;
    supertype_in_fragment; intersect_below; supertype_above; intersect_in_generic_code; supertype_in_generic_code;
    keeps_bottom_only; of_classes
].

Lemma conjectures_checked: report env grid checks = ([], []).
Proof. vm_compute. reflexivity. Qed.

Definition reported: fst (report env grid checks) = [] := f_equal fst conjectures_checked.

Ltac member := cbn [In checks]; repeat (first [left; reflexivity | right]).

(* Each conjecture, of the pairs of the grid; of those its excuses don't take out *)

Theorem intersect_stays_in_fragment_on_grid: on_grid env grid intersect_in_fragment (intersect_in_fragment_on env).
Proof. exact (checked env grid checks intersect_in_fragment _ reported ltac:(member) (intersect_in_fragment_checked env name)). Qed.

Theorem intersect_always_stays_in_fragment_on_grid:
    on_grid env grid intersect_always_in_fragment (intersect_always_in_fragment_on env).
Proof. exact (checked env grid checks intersect_always_in_fragment _ reported ltac:(member) (intersect_always_in_fragment_checked env name)). Qed.

Theorem intersect_makes_no_bare_nullable_on_grid: on_grid env grid intersect_no_bare_nullable (intersect_no_bare_nullable_on env).
Proof. exact (checked env grid checks intersect_no_bare_nullable _ reported ltac:(member) (intersect_no_bare_nullable_checked env name)). Qed.

Theorem closest_common_supertype_makes_no_bare_nullable_on_grid:
    on_grid env grid supertype_no_bare_nullable (supertype_no_bare_nullable_on env).
Proof. exact (checked env grid checks supertype_no_bare_nullable _ reported ltac:(member) (supertype_no_bare_nullable_checked env name)). Qed.

Theorem closest_common_supertype_stays_in_fragment_on_grid: on_grid env grid supertype_in_fragment (supertype_in_fragment_on env).
Proof. exact (checked env grid checks supertype_in_fragment _ reported ltac:(member) (supertype_in_fragment_checked env name)). Qed.

Theorem intersect_is_below_both_on_grid: on_grid env grid intersect_below (intersect_below_on env).
Proof. exact (checked env grid checks intersect_below _ reported ltac:(member) (intersect_below_checked env fuel name)). Qed.

Theorem closest_common_supertype_is_above_both_on_grid: on_grid env grid supertype_above (supertype_above_on env).
Proof. exact (checked env grid checks supertype_above _ reported ltac:(member) (supertype_above_checked env fuel name)). Qed.

Theorem intersect_stays_in_generic_code_on_grid:
    on_grid env grid intersect_in_generic_code (in_generic_code_on env (intersect env)).
Proof.
    exact (checked env grid checks intersect_in_generic_code _ reported ltac:(member) (fun a b => in_generic_code_checked env name (intersect env) a b)).
Qed.

Theorem closest_common_supertype_stays_in_generic_code_on_grid:
    on_grid env grid supertype_in_generic_code (in_generic_code_on env (closest_common_supertype_with env)).
Proof.
    exact (checked env grid checks supertype_in_generic_code _ reported ltac:(member)
        (fun a b => in_generic_code_checked env name (closest_common_supertype_with env) a b)).
Qed.

Theorem closest_common_supertype_keeps_bottom_only_on_grid: on_grid env grid keeps_bottom_only (bottom_only_on env).
Proof. exact (checked env grid checks keeps_bottom_only _ reported ltac:(member) (bottom_only_checked env name)). Qed.

Theorem closest_common_supertype_of_classes_on_grid: on_grid env grid of_classes (of_classes_on env).
Proof. exact (checked env grid checks of_classes _ reported ltac:(member) (of_classes_checked env name)). Qed.
