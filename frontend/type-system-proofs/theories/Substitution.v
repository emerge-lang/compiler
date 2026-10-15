From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The substitution lemma                                                                         *)
(*                                                                                                *)
(* Instantiating the type parameters keeps assignability: if a type is assignable to another, it  *)
(* still is with the type parameters in both replaced by type arguments. This is what makes       *)
(* checking generic code once enough: at run time, every type parameter stands for one exact      *)
(* type.                                                                                          *)
(* So the type parameters are instantiated with exact type arguments here: invariant, owned or    *)
(* ref, of types of the fragment of Transitivity.v (bindings_in_fragment). The facts about        *)
(* instantiating that don't need that (bound_in) take types of the fragment of Fragment.v as      *)
(* well, as the final values of inference can be (FinalValues.v).                                 *)
(* The types instantiated are                                                                     *)
(* - class types, whose type arguments are of any variance and ownership, and contain types of    *)
(*   the fragment; Nothing only as `exclusive Nothing`;                                           *)
(* - nullable class types;                                                                        *)
(* - references to type parameters, `T`, `m T` or `T!`, the mutability and `!` written or applied *)
(*   (as_written), and nullable ones, `T?`, whose bound is such a type or an intersection of      *)
(*   them, nullable or not; it may mention other type parameters (`<U, T : Box<U>>`);             *)
(* - at the top, rather than in a type argument, intersections of class types and non-null        *)
(*   references, nullable or not, as ofComponents builds them (tfrag); as the assignee, they take *)
(*   SubstitutionTerminating.v;                                                                   *)
(* - without type inference (no type variables), intersections in type arguments (they take       *)
(*   SubstitutionWide.v) or erroneous types.                                                      *)
(* Bound exactly, a type parameter is the type it is bound to (TypeUnification.getFinalTypeFor):  *)
(* a reference becomes that type, with the mutability and nullability of the reference applied    *)
(* (inst_ref); an intersection, the intersection of the instances of its components, which are    *)
(* class types (cfrag). inst_nested says so shape by shape; it is what instantiate makes of the   *)
(* types (inst_nested_instantiate). The instance of a reference is within the bound of the        *)
(* reference, instantiated (binds_ref): for `T`, the type argument is within the bound of T with  *)
(* the type parameters in it replaced by their type arguments, which is how Kotlin checks type    *)
(* arguments. With T bound to a const class, `mut T` is immutable, as its references are; its     *)
(* values fit `mut` all the same (assignment_mutability).                                         *)
(* A type parameter accepts a non-nullable Nothing of a mutability that fits its bound, also one  *)
(* an instantiation of it doesn't accept: of the bound `read Any`, it takes `mut Nothing`, which  *)
(* isn't a `const C`. Nothing is never instantiated, though, so that doesn't matter for the       *)
(* soundness; hence `exclusive Nothing` only, also in the type arguments of supertypes            *)
(* (supertypes_mention_nothing_as_bottom).                                                        *)
(*                                                                                                *)
(* A reference assigned to a class type, or to a reference to another type parameter, needs the   *)
(* transitivity of unify: the instance is assignable to the bound, instantiated, which is         *)
(* assignable to the target, instantiated; for a bound that is an intersection, through the       *)
(* component of it that the target takes (via_intersection). Two references to the same type      *)
(* parameter are the same type argument, with mutabilities and nullabilities applied that are     *)
(* ordered as their bounds are (same_parameter). A subclass assigned to its superclass needs      *)
(* instantiating the supertype to commute with instantiating the type parameters                  *)
(* (supertype_arguments_commute). An intersection as the target takes what each of its components *)
(* takes; instantiated, the components are of the mutability common to them, which the instance   *)
(* of the assignee fits (substitution_into_intersection).                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma existsb_ext_in: forall {A: Type} (f g: A -> bool) l, (forall a, In a l -> f a = g a) -> existsb f l = existsb g l.
Proof.
    intros A f g l H. induction l as [|a l IH]; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Section Substitution.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.

Definition is_exact_ownership (o: Ownership): bool :=
    match o with owned | ref => true | _ => false end.

Let supertypes_mention_nothing_as_bottom := wf_supertypes_mention_nothing_as_bottom env wf.

(* Without type parameters *)
Fixpoint closed (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb closed arguments
    | Nullable n => closed n
    | TypeArgument _ o n => negb (is_parameter_ownership o) && closed n
    | _ => false
    end.

Definition is_generic (t: EType): bool :=
    match t with Generic _ => true | _ => false end.

(* A reference to a type parameter as written, or as the compiler applied a mutability or `!` to it:
   its effective bound is assigned as no more than the mutability given to it (`mut T`), as that or
   as exclusive where the bound is const, and the `!` that narrowed it made the effective bound
   non-nullable *)
Definition as_written (given: option Mutability) (narrowed: bool) (bound: EType): bool :=
    match given with Some m => Model.is_subtype_of (assignment_mutability env bound) m | None => true end
    && (negb narrowed || negb (is_nullable env bound)).

(* A component of an intersection: a non-null class type, or a non-null reference to a type parameter *)
Definition is_component_shape (c: EType): bool := (is_class c || is_generic c) && negb (is_nullable env c).

(* A reference without type variables in its bound, as there are none without type inference *)
Definition no_type_variables (g: GenericRef): bool := match variables_of g with [] => true | _ => false end.

(* The types instantiated, taking whether the effective bound of a reference is of the fragment from
   bound_tfrag (see Subtyping.through) *)
Fixpoint sfrag_h (bound_tfrag: GenericRef -> bool) (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        if class_eqb c nothing then is_bottom m arguments else
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with TypeArgument _ _ n => sfrag_h bound_tfrag n | _ => false end) arguments
    | Nullable n => (is_class n || is_generic n) && sfrag_h bound_tfrag n
    | Generic g => bound_tfrag g && as_written (given_mutability g) (is_narrowed g) (effective_bound env g) && no_type_variables g
    | _ => false
    end.

Definition tfrag_h (bound_tfrag: GenericRef -> bool) (t: EType): bool :=
    match t with
    | Intersection cs | Nullable (Intersection cs) =>
        Nat.leb 2 (length cs) && forallb (fun c => is_component_shape c && sfrag_h bound_tfrag c) cs
    | _ => sfrag_h bound_tfrag t
    end.

(* The effective bound of a reference is of the fragment; it may be an intersection, nullable or not *)
Definition bound_tfrag (g: GenericRef): bool := through env tfrag_h false g.

Fixpoint sfrag (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        if class_eqb c nothing then is_bottom m arguments else
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with TypeArgument _ _ n => sfrag n | _ => false end) arguments
    | Nullable n => (is_class n || is_generic n) && sfrag n
    | Generic g => bound_tfrag g && as_written (given_mutability g) (is_narrowed g) (effective_bound env g) && no_type_variables g
    | _ => false
    end.

(* Intersections of types of the fragment, as ofComponents builds them: of two components or more *)
Definition components_sfrag (cs: list EType): bool :=
    Nat.leb 2 (length cs) && forallb (fun c => is_component_shape c && sfrag c) cs.

(* The types instantiated at the top, rather than in a type argument: also intersections *)
Definition tfrag (t: EType): bool :=
    match t with
    | Intersection cs | Nullable (Intersection cs) => components_sfrag cs
    | _ => sfrag t
    end.

Definition argument_sfrag (a: EType): bool :=
    match a with TypeArgument _ _ n => sfrag n | _ => false end.

Definition generic_sfrag (g: GenericRef): Prop :=
    tfrag (effective_bound env g) = true /\ as_written (given_mutability g) (is_narrowed g) (effective_bound env g) = true
    /\ no_type_variables g = true.

(* The depth of a type, through the effective bounds of references, taking theirs from bound_depth *)
Fixpoint sdepth_h (bound_depth: GenericRef -> nat) (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments =>
        S (list_max (map (fun a => match a with TypeArgument _ _ n => S (sdepth_h bound_depth n) | _ => 0 end) arguments))
    | Nullable n => S (sdepth_h bound_depth n)
    | Generic g => S (bound_depth g)
    | Intersection components => S (list_max (map (sdepth_h bound_depth) components))
    | _ => 0
    end.

Definition bound_depth (g: GenericRef): nat := through env sdepth_h 0 g.

Fixpoint sdepth (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments =>
        S (list_max (map (fun a => match a with TypeArgument _ _ n => S (sdepth n) | _ => 0 end) arguments))
    | Nullable n => S (sdepth n)
    | Generic g => S (bound_depth g)
    | Intersection components => S (list_max (map sdepth components))
    | _ => 0
    end.

Definition argument_sdepth (a: EType): nat :=
    match a with TypeArgument _ _ n => S (sdepth n) | _ => 0 end.

(* The type argument x of a reference's type parameter, with the mutability of the reference applied *)
Definition inst_fit (g: GenericRef) (x: EType): EType :=
    match given_mutability g with
    | Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x
    | None => x
    end.

(* What a reference to a type parameter becomes, the type parameter bound to x: x, with the
   mutability and the nullability of the reference applied (GenericTypeReference.instantiateAllParameters) *)
Definition inst_ref (g: GenericRef) (x: EType): EType :=
    if is_narrowed g then without_null env (inst_fit g x) else inst_fit g x.

(* A component of an intersection, instantiated: a reference to a type parameter is the instance of
   the type in its type argument, as below *)
Definition inst_component (b: Bindings) (c: EType): EType :=
    match c with
    | Generic g =>
        match lookup_binding b (param_of g) with
        | Some (TypeArgument _ _ x) => inst_ref g x
        | _ => c
        end
    | _ => instantiate env b c
    end.

Definition inst_intersection (b: Bindings) (cs: list EType): EType :=
    of_components env (flat_map intersected_components (map (inst_component b) cs)).

(* What a type in a type argument becomes, when instantiated: a reference to a type parameter, the
   instance of the type in its type argument; an intersection, the intersection of the instances of
   its components *)
Definition inst_nested (b: Bindings) (n: EType): EType :=
    match n with
    | Generic g =>
        match lookup_binding b (param_of g) with
        | Some (TypeArgument _ _ x) => inst_ref g x
        | _ => n
        end
    | Nullable (Generic g) =>
        match lookup_binding b (param_of g) with
        | Some (TypeArgument _ _ x) => rewrap_nullable (inst_ref g x)
        | _ => n
        end
    | Intersection cs => inst_intersection b cs
    | Nullable (Intersection cs) => rewrap_nullable (inst_intersection b cs)
    | _ => instantiate env b n
    end.

(* `V!` for the reference V: GenericTypeReference.withCombinedNullability(NOT_NULLABLE), which narrows
   it where its bound is nullable *)
Definition narrow_ref (g: GenericRef): GenericRef :=
    mkGenericRef (given_mutability g) (is_narrowed g || is_nullable env (Generic g)) (param_of g) (variables_of g).

Lemma without_null_generic: forall g, without_null env (Generic g) = Generic (narrow_ref g).
Proof. intros [gm nn p vs]. reflexivity. Qed.

Lemma tfrag_top: forall t, tfrag t = tfrag_h bound_tfrag t.
Proof.
    assert (Hs: forall t, sfrag t = sfrag_h bound_tfrag t).
    { fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; simpl; try reflexivity.
      - destruct (class_eqb c nothing); [reflexivity|]. f_equal. induction args as [|a args IHa]; [reflexivity|]. simpl.
        rewrite IHa. destruct a as [| | | | v o n| |]; try reflexivity. rewrite (IH n). reflexivity.
      - rewrite (IH n). reflexivity. }
    intros [m c args|n|g|me msg|v o n|g|cs]; unfold tfrag, tfrag_h; try apply Hs.
    - destruct n as [| | | | | |cs]; try apply Hs. unfold components_sfrag. f_equal.
      induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite Hs, IHc. reflexivity.
    - unfold components_sfrag. f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite Hs, IHc. reflexivity.
Qed.

Lemma sfrag_h_agree: forall k U1 U2, (forall g, rank_of env g < k -> U1 g = U2 g) ->
    forall t, ranked_below env k t = true -> sfrag_h U1 t = sfrag_h U2 t.
Proof.
    intros k U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity.
    - destruct (class_eqb c nothing); [reflexivity|]. f_equal. induction args as [|a args IHa]; [reflexivity|].
      simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has]. rewrite (IHa Has).
      destruct a as [| | | | v o n| |]; try reflexivity. rewrite (IH n Ha). reflexivity.
    - rewrite (IH n Ht). reflexivity.
    - rewrite (HU g (ref_ranked env k g Ht)). reflexivity.
Qed.

Lemma tfrag_h_agree: forall k U1 U2, (forall g, rank_of env g < k -> U1 g = U2 g) ->
    forall t, ranked_below env k t = true -> tfrag_h U1 t = tfrag_h U2 t.
Proof.
    intros k U1 U2 HU t Ht. pose proof (sfrag_h_agree k U1 U2 HU) as Hs.
    destruct t as [m c args|[m c args|n|g|me msg|v o n|g|cs]|g|me msg|v o n|g|cs]; unfold tfrag_h; try (apply Hs; exact Ht).
    all: f_equal; simpl in Ht; induction cs as [|c cs IHc]; try reflexivity; simpl in Ht |- *;
         apply andb_true_iff in Ht; destruct Ht as [Hc Hcs]; rewrite (Hs c Hc), (IHc Hcs); reflexivity.
Qed.

Lemma bound_tfrag_eq: forall g, bound_tfrag g = tfrag (effective_bound env g).
Proof.
    intros g. rewrite tfrag_top. unfold bound_tfrag at 1. rewrite (through_eq env ranked); [reflexivity|exact tfrag_h_agree].
Qed.

Lemma sfrag_generic: forall g,
    sfrag (Generic g) = tfrag (effective_bound env g) && as_written (given_mutability g) (is_narrowed g) (effective_bound env g) && no_type_variables g.
Proof.
    intros g. change (sfrag (Generic g)) with (bound_tfrag g && as_written (given_mutability g) (is_narrowed g) (effective_bound env g) && no_type_variables g).
    rewrite bound_tfrag_eq. reflexivity.
Qed.

Lemma sfrag_generic_iff: forall g, sfrag (Generic g) = true <-> generic_sfrag g.
Proof.
    intros g. rewrite sfrag_generic. unfold generic_sfrag. rewrite !andb_true_iff. tauto.
Qed.

Lemma sdepth_h_agree: forall k U1 U2, (forall g, rank_of env g < k -> U1 g = U2 g) ->
    forall t, ranked_below env k t = true -> sdepth_h U1 t = sdepth_h U2 t.
Proof.
    intros k U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity.
    - f_equal. f_equal. induction args as [|a args IHa]; [reflexivity|].
      simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has]. rewrite (IHa Has).
      destruct a as [| | | | v o n| |]; try reflexivity. rewrite (IH n Ha). reflexivity.
    - rewrite (IH n Ht). reflexivity.
    - rewrite (HU g (ref_ranked env k g Ht)). reflexivity.
    - f_equal. f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma sdepth_top: forall t, sdepth t = sdepth_h bound_depth t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; simpl; try reflexivity.
    - f_equal. f_equal. induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite IHa.
      destruct a as [| | | | v o n| |]; try reflexivity. rewrite (IH n). reflexivity.
    - rewrite (IH n). reflexivity.
    - f_equal. f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma sdepth_bound: forall g, sdepth (Generic g) = S (sdepth (effective_bound env g)).
Proof.
    intros g. change (sdepth (Generic g)) with (S (bound_depth g)). rewrite sdepth_top. unfold bound_depth at 1.
    rewrite (through_eq env ranked); [reflexivity|exact sdepth_h_agree].
Qed.

Lemma generic_sfrag_sfrag: forall g, generic_sfrag g -> sfrag (Generic g) = true.
Proof. intros g H. apply sfrag_generic_iff, H. Qed.

Lemma sfrag_tfrag: forall t, sfrag t = true -> tfrag t = true.
Proof. intros [| [] | | | | |] H; try exact H; discriminate H. Qed.

Lemma mutability_generic: forall g, assignment_mutability env (Generic g) = assignment_mutability env (effective_bound env g).
Proof. exact (assignment_mutability_generic env ranked). Qed.

Lemma nullable_generic: forall g, is_nullable env (Generic g) = is_nullable env (effective_bound env g).
Proof. exact (is_nullable_generic env ranked). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Class types of another mutability, or without null                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma in_fragment_with_mutability: forall k x, in_fragment env x = true -> in_fragment env (with_mutability env k x) = true.
Proof. intros k x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]]; exact H. Qed.

Lemma in_fragment_without_null: forall x, in_fragment env x = true -> in_fragment env (without_null env x) = true.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]]; [exact H|exact H']. Qed.

Lemma in_fragment_rewrap: forall x, in_fragment env x = true -> in_fragment env (rewrap_nullable x) = true.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]]; exact H. Qed.

Lemma without_null_non_null: forall x, in_fragment env x = true -> is_nullable env x = false -> without_null env x = x.
Proof. intros x H Hn. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; [reflexivity|discriminate Hn]. Qed.

Lemma without_null_idempotent: forall x, in_fragment env x = true -> without_null env (without_null env x) = without_null env x.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma without_null_not_nullable: forall x, in_fragment env x = true -> is_nullable env (without_null env x) = false.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma rewrap_without_null: forall x, in_fragment env x = true -> rewrap_nullable x = Nullable (without_null env x).
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma assignment_mutability_of_without_null: forall x, in_fragment env x = true -> assignment_mutability env (without_null env x) = assignment_mutability env x.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma nullable_with_mutability: forall k x, in_fragment env x = true -> is_nullable env (with_mutability env k x) = is_nullable env x.
Proof. intros k x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

(* A class type takes the mutability given; one of a const class stays immutable, and is assigned as exclusive *)
Lemma with_mutability_cases: forall x, in_fragment env x = true ->
    (forall k, assignment_mutability env (with_mutability env k x) = k)
    \/ (forall k, assignment_mutability env (with_mutability env k x) = assignment_mutability env x).
Proof.
    intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        (destruct (is_const (declaration_of env c)) eqn:E; [right|left]); intros k; simpl; rewrite E; reflexivity.
Qed.

(* A class type of a mutability below its own is assigned as no more than it *)
Lemma with_mutability_below: forall k x, in_fragment env x = true -> Model.is_subtype_of k (mutability_of env x) = true ->
    Model.is_subtype_of (assignment_mutability env (with_mutability env k x)) (assignment_mutability env x) = true.
Proof.
    intros k x H Hk. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        simpl in Hk |- *; destruct (is_const (declaration_of env c)); first [reflexivity|exact Hk].
Qed.

(* The same class type, of another mutability *)
Definition remut (t t': EType): Prop :=
    (exists m m' c args, t = RootResolved m c args /\ t' = RootResolved m' c args)
    \/ (exists m m' c args, t = Nullable (RootResolved m c args) /\ t' = Nullable (RootResolved m' c args)).

Lemma remut_refl: forall x, in_fragment env x = true -> remut x x.
Proof.
    intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        [left|right]; exists m, m, c, args; split; reflexivity.
Qed.

Lemma remut_with_mutability: forall k x, in_fragment env x = true -> remut x (with_mutability env k x).
Proof.
    intros k x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        [left|right]; do 2 eexists; exists c, args; split; reflexivity.
Qed.

Lemma unify_remut_classes: forall f md md' cd dargs mx mx' cx xargs s r,
    Model.is_subtype_of (assignment_mutability env (RootResolved mx' cx xargs)) (assignment_mutability env (RootResolved md' cd dargs)) = true ->
    unify env f (RootResolved md cd dargs) (RootResolved mx cx xargs) (Ongoing s) = Some (Ongoing r) ->
    unify env f (RootResolved md' cd dargs) (RootResolved mx' cx xargs) (Ongoing s) = Some (Ongoing r).
Proof.
    intros [|f] md md' cd dargs mx mx' cx xargs s r Hm H; [discriminate H|].
    rewrite unify_classes in H |- *. rewrite Hm.
    destruct (base_type_is_subtype_of env cx cd); [|discriminate H].
    destruct (Model.is_subtype_of _ _) in H; [exact H|discriminate H].
Qed.

(* Assignability between class types depends on their mutabilities only in that of the assignee
   fitting that of the target *)
Lemma unify_remut: forall f D D' x x' s r, remut D D' -> remut x x' ->
    Model.is_subtype_of (assignment_mutability env x') (assignment_mutability env D') = true ->
    unify env f D x (Ongoing s) = Some (Ongoing r) -> unify env f D' x' (Ongoing s) = Some (Ongoing r).
Proof.
    intros [|f] D D' x x' s r HD Hx Hm H; [discriminate H|].
    destruct HD as [[md [md' [cd [dargs [-> ->]]]]]|[md [md' [cd [dargs [-> ->]]]]]];
    destruct Hx as [[mx [mx' [cx [xargs [-> ->]]]]]|[mx [mx' [cx [xargs [-> ->]]]]]].
    - exact (unify_remut_classes (S f) md md' cd dargs mx mx' cx xargs s r Hm H).
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite unify_nullable_class in H |- *. exact (unify_remut_classes f md md' cd dargs mx mx' cx xargs s r Hm H).
    - rewrite unify_nullable_nullable in H |- *. exact (unify_remut_classes f md md' cd dargs mx mx' cx xargs s r Hm H).
Qed.

(* Without null on both sides, what is accepted stays accepted *)
Lemma unify_without_null: forall f D x s r, in_fragment env D = true -> in_fragment env x = true ->
    unify env f D x (Ongoing s) = Some (Ongoing r) -> unify env f (without_null env D) (without_null env x) (Ongoing s) = Some (Ongoing r).
Proof.
    intros [|f] D x s r HD Hx H; [discriminate H|].
    destruct (fragment_cases env D HD) as [[md [cd [dargs ->]]]|[md [cd [dargs [-> _]]]]];
    destruct (fragment_cases env x Hx) as [[mx [cx [xargs ->]]]|[mx [cx [xargs [-> _]]]]].
    - exact H.
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite unify_nullable_class in H. exact (unify_fuel_monotone env f (S f) _ _ _ _ ltac:(lia) H).
    - rewrite unify_nullable_nullable in H. exact (unify_fuel_monotone env f (S f) _ _ _ _ ltac:(lia) H).
Qed.

(* An assignee without null is accepted where it is with null *)
Lemma unify_without_null_assignee: forall f T y s r, in_fragment env T = true -> in_fragment env y = true ->
    unify env f T y (Ongoing s) = Some (Ongoing r) -> unify env f T (without_null env y) (Ongoing s) = Some (Ongoing r).
Proof.
    intros [|f] T y s r HT Hy H; [discriminate H|].
    destruct (fragment_cases env y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]]; [exact H|].
    destruct (fragment_cases env T HT) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> _]]]]].
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite unify_nullable_nullable in H. cbn [without_null]. rewrite unify_nullable_class. exact H.
Qed.

Lemma accepted_mutability_classes: forall f D y s r, in_fragment env D = true -> in_fragment env y = true ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env D) = true.
Proof.
    intros [|f] D y s r HD Hy H; [discriminate H|].
    assert (Hc: forall f' md cd dargs my cy yargs,
        unify env f' (RootResolved md cd dargs) (RootResolved my cy yargs) (Ongoing s) = Some (Ongoing r) ->
        Model.is_subtype_of (assignment_mutability env (RootResolved my cy yargs)) (assignment_mutability env (RootResolved md cd dargs)) = true).
    { intros [|f'] md cd dargs my cy yargs E; [discriminate E|]. rewrite unify_classes in E.
      destruct (base_type_is_subtype_of env cy cd); [|discriminate E]. destruct (Model.is_subtype_of _ _); [reflexivity|discriminate E]. }
    destruct (fragment_cases env D HD) as [[md [cd [dargs ->]]]|[md [cd [dargs [-> _]]]]];
    destruct (fragment_cases env y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]].
    - exact (Hc _ _ _ _ _ _ _ H).
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite unify_nullable_class in H. exact (Hc _ _ _ _ _ _ _ H).
    - rewrite unify_nullable_nullable in H. exact (Hc _ _ _ _ _ _ _ H).
Qed.

Lemma accepted_non_null: forall f D y s r, in_fragment env D = true -> in_fragment env y = true -> is_nullable env D = false ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> is_nullable env y = false.
Proof.
    intros [|f] D y s r HD Hy Hn H; [discriminate H|].
    destruct (fragment_cases env D HD) as [[md [cd [dargs ->]]]|[md [cd [dargs [-> _]]]]]; [|discriminate Hn].
    destruct (fragment_cases env y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]]; [reflexivity|].
    rewrite unify_class_nullable in H. discriminate H.
Qed.

Lemma unify_rewrap: forall f T y s r, in_fragment env T = true -> in_fragment env y = true ->
    unify env f T y (Ongoing s) = Some (Ongoing r) -> unify env (S f) (rewrap_nullable T) (rewrap_nullable y) (Ongoing s) = Some (Ongoing r).
Proof.
    intros f T y s r HT Hy H. rewrite (rewrap_without_null T HT), (rewrap_without_null y Hy), unify_nullable_nullable.
    exact (unify_without_null f T y s r HT Hy H).
Qed.

Lemma unify_into_nullable: forall f T y s r, in_fragment env y = true ->
    unify env f T (without_null env y) (Ongoing s) = r -> unify env (S f) (Nullable T) y (Ongoing s) = r.
Proof.
    intros f T y s r Hy H. destruct (fragment_cases env y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]].
    - rewrite unify_nullable_class. exact H.
    - rewrite unify_nullable_nullable. exact H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Intersections of class types                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Definition class_components (ys: list EType): bool :=
    Nat.leb 2 (length ys) && forallb (fun y => is_class y && in_fragment env y) ys.

(* What the types of tfrag become: types of the fragment of Transitivity.v, and intersections of
   class types of it, nullable or not *)
Definition cfrag (t: EType): bool :=
    match t with
    | Intersection ys | Nullable (Intersection ys) => class_components ys
    | _ => in_fragment env t
    end.

Lemma class_components_facts: forall ys, class_components ys = true ->
    2 <= length ys /\ forall y, In y ys -> is_class y = true /\ in_fragment env y = true.
Proof.
    intros ys H. unfold class_components in H. apply andb_true_iff in H. destruct H as [Hl H].
    split; [apply Nat.leb_le, Hl|]. intros y Hy. rewrite forallb_forall in H. apply andb_true_iff, H, Hy.
Qed.

Lemma cfrag_cases: forall t, cfrag t = true ->
    in_fragment env t = true
    \/ (exists ys, t = Intersection ys /\ class_components ys = true)
    \/ (exists ys, t = Nullable (Intersection ys) /\ class_components ys = true).
Proof.
    intros t H. destruct t as [m c args|[m c args|n|g|me msg|v o n|g|ys]|g|me msg|v o n|g|ys];
        try (left; exact H).
    - right. right. exists ys. split; [reflexivity|exact H].
    - right. left. exists ys. split; [reflexivity|exact H].
Qed.

Lemma in_fragment_cfrag: forall t, in_fragment env t = true -> cfrag t = true.
Proof. intros t H. destruct (fragment_cases env t H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact H. Qed.

Lemma class_components_not_variables: forall ys, class_components ys = true ->
    forall y, In y ys -> is_type_variable y = false.
Proof.
    intros ys H y Hy. destruct (proj2 (class_components_facts ys H) y Hy) as [Hc _].
    destruct y; first [reflexivity|discriminate Hc].
Qed.

Lemma no_variables_filter: forall ys, (forall y, In y ys -> is_type_variable y = false) ->
    filter is_type_variable ys = [] /\ filter (fun c => negb (is_type_variable c)) ys = ys.
Proof.
    induction ys as [|y ys IH]; intros H; [split; reflexivity|]. simpl.
    destruct (IH (fun y' Hy' => H y' (or_intror Hy'))) as [H1 H2]. rewrite (H y (or_introl eq_refl)), H1, H2.
    split; reflexivity.
Qed.

(* A fold of unify over components that keep the states: it succeeds where each component does *)
Lemma fold_each: forall f y l s r,
    (forall c u, In c l -> unify env f c y (Ongoing s) = Some (Ongoing u) -> u = s) ->
    fold_unify (fun inner c => unify env f c y inner) l (Ongoing s) = Some (Ongoing r) ->
    r = s /\ forall c, In c l -> unify env f c y (Ongoing s) = Some (Ongoing s).
Proof.
    intros f y l. induction l as [|c l IH]; intros s r Hk H; simpl in H.
    - injection H as <-. split; [reflexivity|intros c []].
    - destruct (unify env f c y (Ongoing s)) as [[u|]|] eqn:E; try discriminate H.
      + pose proof (Hk c u (or_introl eq_refl) E) as ->.
        destruct (IH s r (fun c' u' Hc' => Hk c' u' (or_intror Hc')) H) as [-> Hl]. split; [reflexivity|].
        intros c' [<-|Hc']; [exact E|exact (Hl c' Hc')].
      + rewrite fold_unify_stays_failed in H. discriminate H.
Qed.

Lemma fold_all_succeed: forall f y l s,
    (forall c, In c l -> unify env f c y (Ongoing s) = Some (Ongoing s)) ->
    fold_unify (fun inner c => unify env f c y inner) l (Ongoing s) = Some (Ongoing s).
Proof.
    intros f y l s. induction l as [|c l IH]; intros H; simpl; [reflexivity|].
    rewrite (H c (or_introl eq_refl)). apply IH. intros c' Hc'. apply H. right. exact Hc'.
Qed.

(* An intersection without type variables as the target, of components that keep the states: each
   takes the assignee *)
Lemma intersection_target: forall f cs a s r,
    (forall c, In c cs -> is_type_variable c = false) -> cs <> [] ->
    match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    (forall c u, In c cs -> unify env f c a (Ongoing s) = Some (Ongoing u) -> u = s) ->
    unify env (S f) (Intersection cs) a (Ongoing s) = Some (Ongoing r) ->
    r = s /\ forall c, In c cs -> unify env f c a (Ongoing s) = Some (Ongoing s).
Proof.
    intros f cs a s r Hnv Hne Hshape Hk H. destruct (no_variables_filter cs Hnv) as [Hvar Hnonvar].
    change (unify env (S f) (Intersection cs) a (Ongoing s))
        with (unify_intersection env (unify env f) (Intersection cs) cs a s) in H.
    destruct cs as [|c1 cs']; [exfalso; exact (Hne eq_refl)|].
    destruct a as [| | | | | |]; try contradiction.
    all: unfold unify_intersection in H; cbn zeta in H; rewrite Hvar, Hnonvar in H.
    all: destruct (fold_unify _ (c1 :: cs') (Ongoing s)) as [[s2|]|] eqn:Ef in H; try discriminate H.
    all: destruct (fold_each f _ (c1 :: cs') s s2 Hk Ef) as [-> Hall].
    all: cbn [find_first] in H; rewrite (Hall c1 (or_introl eq_refl)) in H.
    all: simpl in H; injection H as <-; split; [reflexivity|exact Hall].
Qed.

Lemma intersection_target_takes: forall f cs a s,
    (forall c, In c cs -> is_type_variable c = false) -> cs <> [] ->
    match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    (forall c, In c cs -> unify env f c a (Ongoing s) = Some (Ongoing s)) ->
    unify env (S f) (Intersection cs) a (Ongoing s) = Some (Ongoing s).
Proof.
    intros f cs a s Hnv Hne Hshape Hall. destruct (no_variables_filter cs Hnv) as [Hvar Hnonvar].
    change (unify env (S f) (Intersection cs) a (Ongoing s))
        with (unify_intersection env (unify env f) (Intersection cs) cs a s).
    destruct cs as [|c1 cs']; [exfalso; exact (Hne eq_refl)|].
    destruct a as [| | | | | |]; try contradiction.
    all: unfold unify_intersection; cbn zeta; rewrite Hvar, Hnonvar.
    all: rewrite (fold_all_succeed f _ (c1 :: cs') s Hall); cbn [find_first].
    all: rewrite (Hall c1 (or_introl eq_refl)); reflexivity.
Qed.

(* An intersection of class types takes a class type that each of its components takes *)
Lemma inter_accepts: forall f ys y s r, class_components ys = true -> in_fragment env y = true ->
    unify env (S f) (Intersection ys) y (Ongoing s) = Some (Ongoing r) ->
    r = s /\ is_nullable env y = false /\ forall c, In c ys -> unify env f c y (Ongoing s) = Some (Ongoing s).
Proof.
    intros f ys y s r Hys Hy H. destruct (class_components_facts ys Hys) as [Hl Hc].
    destruct (fragment_cases env y Hy) as [[m [cy [args ->]]]|[m [cy [args [-> _]]]]]; [|simpl in H; discriminate H].
    destruct (intersection_target f ys (RootResolved m cy args) s r (class_components_not_variables ys Hys)
        ltac:(intros ->; simpl in Hl; lia) I
        (fun c u Hin E => proj1 (keeps_states_with_arguments env wf f) c _ s u (proj2 (Hc c Hin)) Hy E) H) as [-> Hall].
    split; [reflexivity|split; [reflexivity|exact Hall]].
Qed.

Lemma inter_takes: forall f ys y s, class_components ys = true -> in_fragment env y = true -> is_nullable env y = false ->
    (forall c, In c ys -> unify env f c y (Ongoing s) = Some (Ongoing s)) ->
    unify env (S f) (Intersection ys) y (Ongoing s) = Some (Ongoing s).
Proof.
    intros f ys y s Hys Hy Hn Hall. destruct (class_components_facts ys Hys) as [Hl _].
    destruct (fragment_cases env y Hy) as [[m [cy [args ->]]]|[m [cy [args [-> _]]]]]; [|discriminate Hn].
    exact (intersection_target_takes f ys (RootResolved m cy args) s (class_components_not_variables ys Hys) ltac:(intros ->; simpl in Hl; lia) I Hall).
Qed.

(* A type that takes an intersection as the assignee, takes one of its components *)
Lemma unify_into_components: forall n t cs s u,
    unify env (S n) t (Intersection cs) (Ongoing s) = Some (Ongoing u) -> (is_class t || is_generic t) = true ->
    exists c, In c cs /\ unify env n t c (Ongoing s) = Some (Ongoing u).
Proof.
    intros n [m c args| |[gm nn p bound]| | | |] cs s u H Ht; try discriminate Ht;
        exact (intersection_flipped_unify_found env n _ cs s u H).
Qed.

Lemma unify_nullable_target: forall f T y s, in_fragment env y = true ->
    unify env (S f) (Nullable T) y (Ongoing s) = unify env f T (without_null env y) (Ongoing s).
Proof. intros f T y s Hy. apply unify_into_nullable; [exact Hy|reflexivity]. Qed.

Lemma cfrag_keeps: forall f D y s r, cfrag D = true -> in_fragment env y = true ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> r = s.
Proof.
    intros [|f] D y s r HD Hy H; [discriminate H|].
    destruct (cfrag_cases D HD) as [HD'|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - exact (proj1 (keeps_states_with_arguments env wf (S f)) D y s r HD' Hy H).
    - exact (proj1 (inter_accepts f ys y s r Hys Hy H)).
    - rewrite unify_nullable_target in H by exact Hy. destruct f as [|f]; [discriminate H|].
      exact (proj1 (inter_accepts f ys _ s r Hys (in_fragment_without_null _ Hy) H)).
Qed.

Lemma cfrag_mutability: forall f D y s r, cfrag D = true -> in_fragment env y = true ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env D) = true.
Proof.
    assert (Hi: forall f ys y s r, class_components ys = true -> in_fragment env y = true ->
        unify env f (Intersection ys) y (Ongoing s) = Some (Ongoing r) ->
        Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env (Intersection ys)) = true).
    { intros [|f] ys y s r Hys Hy H; [discriminate H|].
      destruct (inter_accepts f ys y s r Hys Hy H) as [_ [_ Hall]]. destruct (class_components_facts ys Hys) as [_ Hc].
      rewrite (intersection_assignment_mutability env). apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
      intros m Hm. apply in_map_iff in Hm. destruct Hm as [c [<- Hin]].
      exact (accepted_mutability_classes f c y s s (proj2 (Hc c Hin)) Hy (Hall c Hin)). }
    intros f D y s r HD Hy H. destruct (cfrag_cases D HD) as [HD'|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - exact (accepted_mutability_classes f D y s r HD' Hy H).
    - exact (Hi f ys y s r Hys Hy H).
    - destruct f as [|f]; [discriminate H|]. rewrite unify_nullable_target in H by exact Hy.
      rewrite <- (assignment_mutability_of_without_null y Hy). exact (Hi f ys _ s r Hys (in_fragment_without_null _ Hy) H).
Qed.

Lemma cfrag_non_null: forall f D y s r, cfrag D = true -> in_fragment env y = true -> is_nullable env D = false ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> is_nullable env y = false.
Proof.
    intros f D y s r HD Hy Hn H. destruct (cfrag_cases D HD) as [HD'|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - exact (accepted_non_null f D y s r HD' Hy Hn H).
    - destruct f as [|f]; [discriminate H|]. exact (proj1 (proj2 (inter_accepts f ys y s r Hys Hy H))).
    - discriminate Hn.
Qed.

Lemma cfrag_without_null: forall f D x s r, cfrag D = true -> in_fragment env x = true ->
    unify env f D x (Ongoing s) = Some (Ongoing r) -> unify env f (without_null env D) (without_null env x) (Ongoing s) = Some (Ongoing r).
Proof.
    intros f D x s r HD Hx H. destruct (cfrag_cases D HD) as [HD'|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - exact (unify_without_null f D x s r HD' Hx H).
    - rewrite (without_null_non_null x Hx (cfrag_non_null f _ x s r HD Hx eq_refl H)). exact H.
    - destruct f as [|f]; [discriminate H|]. rewrite unify_nullable_target in H by exact Hx.
      apply (unify_fuel_monotone env f); [lia|exact H].
Qed.

Lemma cfrag_without_null_non_null: forall D, cfrag D = true -> is_nullable env D = false -> without_null env D = D.
Proof.
    intros D HD Hn. destruct (cfrag_cases D HD) as [HD'|[[ys [-> _]]|[ys [-> _]]]];
        [exact (without_null_non_null D HD' Hn)|reflexivity|discriminate Hn].
Qed.

Lemma without_null_rewrap: forall t, without_null env (rewrap_nullable t) = without_null env t.
Proof. intros [| | | | | |]; reflexivity. Qed.

(* A class type, of a mutability below its own, takes what it takes *)
Lemma with_mutability_accepts: forall f k y x s r, in_fragment env y = true -> in_fragment env x = true ->
    Model.is_subtype_of k (mutability_of env y) = true ->
    unify env f (with_mutability env k y) x (Ongoing s) = Some (Ongoing r) -> unify env f y x (Ongoing s) = Some (Ongoing r).
Proof.
    intros f k y x s r Hy Hx Hk H.
    assert (Hm: Model.is_subtype_of (assignment_mutability env x) (assignment_mutability env y) = true).
    { pose proof (accepted_mutability_classes f _ x s r (in_fragment_with_mutability k y Hy) Hx H) as Ha.
      exact (mutability_subtype_trans _ _ _ Ha (with_mutability_below k y Hy Hk)). }
    apply (unify_remut f (with_mutability env k y) y x x s r); [|apply remut_refl, Hx|exact Hm|exact H].
    destruct (remut_with_mutability k y Hy) as [[m [m' [c [args [E1 E2]]]]]|[m [m' [c [args [E1 E2]]]]]];
        rewrite E2, E1; [left|right]; exists m', m, c, args; split; reflexivity.
Qed.

Lemma accepts_with_mutability: forall f k y x s r, in_fragment env y = true -> in_fragment env x = true ->
    Model.is_subtype_of (assignment_mutability env x) k = true ->
    unify env f y x (Ongoing s) = Some (Ongoing r) -> unify env f (with_mutability env k y) x (Ongoing s) = Some (Ongoing r).
Proof.
    intros f k y x s r Hy Hx Hk H. apply (unify_remut f y _ x x s r (remut_with_mutability k y Hy) (remut_refl x Hx)); [|exact H].
    destruct (with_mutability_cases y Hy) as [Hc|Hc]; rewrite Hc; [exact Hk|exact (accepted_mutability_classes f y x s r Hy Hx H)].
Qed.

Definition common_mutability (ys: list EType): Mutability := fold_left intersect_mutability (map (assignment_mutability env) ys) readonly.

(* Of their common mutability, the components of an intersection are all assigned as it: where one
   is a const class, that is exclusive *)
Lemma with_common_mutability: forall ys y, In y ys -> in_fragment env y = true ->
    assignment_mutability env (with_mutability env (common_mutability ys) y) = common_mutability ys.
Proof.
    intros ys y Hin Hy. pose proof (fold_intersect_below_element (map (assignment_mutability env) ys) readonly _ (in_map _ _ _ Hin)) as Hk.
    fold (common_mutability ys) in Hk.
    destruct (fragment_cases env y Hy) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; simpl in Hk |- *;
        destruct (is_const (declaration_of env c)); try reflexivity;
        symmetry; exact (mutability_subtype_of_exclusive _ Hk).
Qed.

Lemma common_class_mutability: forall ys y, In y ys -> is_class y = true ->
    assignment_mutability env (with_mutability env (common_mutability ys) y) = common_mutability ys.
Proof.
    intros ys y Hin Hy. pose proof (fold_intersect_below_element (map (assignment_mutability env) ys) readonly _ (in_map _ _ _ Hin)) as Hk.
    fold (common_mutability ys) in Hk. destruct y as [m c args| | | | | |]; try discriminate Hy. simpl in Hk |- *.
    destruct (is_const (declaration_of env c)); [symmetry; exact (mutability_subtype_of_exclusive _ Hk)|reflexivity].
Qed.

Lemma flat_map_classes: forall ys, (forall y, In y ys -> is_class y = true) -> flat_map intersected_components ys = ys.
Proof.
    induction ys as [|y ys IH]; intros H; [reflexivity|]. simpl. rewrite IH by (intros y' Hy'; apply H; right; exact Hy').
    pose proof (H y (or_introl eq_refl)) as Hy. destruct y; try discriminate Hy. reflexivity.
Qed.

Lemma of_components_many: forall ys, 2 <= length ys -> forallb (is_nullable env) ys = false ->
    of_components env ys = Intersection (map (fun c => with_mutability env (common_mutability ys) (without_null env c)) ys).
Proof. intros [|y1 [|y2 ys']] Hl Hn; simpl in Hl; try lia. unfold of_components. rewrite Hn. reflexivity. Qed.

(* Of class types, ofComponents makes their intersection, each of their common mutability *)
Lemma of_classes: forall ys, 2 <= length ys -> (forall y, In y ys -> is_class y = true /\ in_fragment env y = true) ->
    of_components env (flat_map intersected_components ys) = Intersection (map (with_mutability env (common_mutability ys)) ys)
    /\ class_components (map (with_mutability env (common_mutability ys)) ys) = true.
Proof.
    intros ys Hl H. rewrite flat_map_classes by (intros y Hy; apply H, Hy). split.
    - rewrite of_components_many; [|exact Hl|].
      + f_equal. apply map_ext_in. intros y Hy. pose proof (proj1 (H y Hy)) as Hc. destruct y; try discriminate Hc. reflexivity.
      + destruct ys as [|y1 ys']; [simpl in Hl; lia|]. pose proof (proj1 (H y1 (or_introl eq_refl))) as Hc.
        destruct y1; try discriminate Hc. reflexivity.
    - unfold class_components. rewrite length_map. apply andb_true_iff. split; [apply Nat.leb_le, Hl|].
      apply forallb_forall. intros y' Hy'. apply in_map_iff in Hy'. destruct Hy' as [y [<- Hy]].
      destruct (H y Hy) as [Hc Hf]. destruct y; try discriminate Hc. apply andb_true_iff. split; [reflexivity|].
      apply in_fragment_with_mutability, Hf.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Instances of references to type parameters                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma inst_fit_in_fragment: forall g x, in_fragment env x = true -> in_fragment env (inst_fit g x) = true.
Proof. intros g x H. unfold inst_fit. destruct (given_mutability g); [apply in_fragment_with_mutability|]; exact H. Qed.

Lemma inst_ref_in_fragment: forall g x, in_fragment env x = true -> in_fragment env (inst_ref g x) = true.
Proof.
    intros g x H. unfold inst_ref. destruct (is_narrowed g); [apply in_fragment_without_null|]; apply inst_fit_in_fragment, H.
Qed.

Lemma remut_inst_fit: forall g x, in_fragment env x = true -> remut x (inst_fit g x).
Proof. intros g x H. unfold inst_fit. destruct (given_mutability g); [apply remut_with_mutability|apply remut_refl]; exact H. Qed.

Lemma inst_fit_mutability_below: forall g x, in_fragment env x = true ->
    Model.is_subtype_of (assignment_mutability env (inst_fit g x)) (assignment_mutability env x) = true.
Proof.
    intros g x H. unfold inst_fit. destruct (given_mutability g) as [m|]; [|apply mutability_is_subtype_of_refl].
    apply with_mutability_below; [exact H|apply intersect_mutability_left].
Qed.

Lemma mutability_inst_ref: forall g x, in_fragment env x = true -> assignment_mutability env (inst_ref g x) = assignment_mutability env (inst_fit g x).
Proof.
    intros g x H. unfold inst_ref. destruct (is_narrowed g); [|reflexivity].
    apply assignment_mutability_of_without_null, inst_fit_in_fragment, H.
Qed.

Lemma nullable_inst_fit: forall g x, in_fragment env x = true -> is_nullable env (inst_fit g x) = is_nullable env x.
Proof. intros g x H. unfold inst_fit. destruct (given_mutability g); [apply nullable_with_mutability, H|reflexivity]. Qed.

(* Without null, a reference and its `!` are the same *)
Lemma narrow_ref_inst: forall g x, in_fragment env x = true ->
    without_null env (inst_ref (narrow_ref g) x) = without_null env (inst_ref g x).
Proof.
    intros g x H. pose proof (without_null_idempotent _ (inst_fit_in_fragment g x H)) as Hi.
    unfold inst_ref. cbn [is_narrowed narrow_ref]. unfold inst_fit. cbn [given_mutability narrow_ref]. fold (inst_fit g x).
    destruct (is_narrowed g), (is_nullable env (Generic g)); cbn [orb]; first [exact Hi|reflexivity|symmetry; exact Hi].
Qed.

Lemma inst_ref_not_variable: forall g x, gfrag env x = true -> is_type_variable (inst_ref g x) = false.
Proof.
    intros [[k|] [|] p bound] x Hx; unfold inst_ref, inst_fit; cbn [given_mutability is_narrowed];
        (destruct x as [m c args|n|[gm nn q bq]|me msg|v o n|g|cs]; simpl in Hx; try discriminate Hx; try reflexivity;
         destruct n as [| |[]| | | |]; simpl in Hx; try discriminate Hx; reflexivity).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify with references to type parameters, one step                                             *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma unify_root_generic: forall n m c args g s,
    unify env (S n) (RootResolved m c args) (Generic g) (Ongoing s) = unify env n (RootResolved m c args) (effective_bound env g) (Ongoing s).
Proof. intros n m c args [gm nn q bound] s. reflexivity. Qed.

Lemma unify_generic_root: forall n g m c args s,
    unify env (S n) (Generic g) (RootResolved m c args) (Ongoing s)
    = if class_eqb c nothing && Model.is_subtype_of (assignment_mutability env (RootResolved m c args)) (assignment_mutability env (effective_bound env g))
      then Some (Ongoing s) else Some Failed.
Proof. intros n g m c args s. rewrite <- (assignment_mutability_generic env ranked). destruct g. reflexivity. Qed.

Lemma unify_generic_nullable: forall n g na s, unify env (S n) (Generic g) (Nullable na) (Ongoing s) = Some Failed.
Proof. intros n [gm nn p bound] na s. reflexivity. Qed.

Lemma unify_nullable_generic_step: forall n t ga s,
    unify env (S n) (Nullable t) (Generic ga) (Ongoing s) = unify env n t (Generic (narrow_ref ga)) (Ongoing s).
Proof. intros n t [gm nn p bound] s. reflexivity. Qed.

Lemma unify_generic_generic_step: forall n gt ga s,
    unify env (S n) (Generic gt) (Generic ga) (Ongoing s) =
    if param_eqb (param_of ga) (param_of gt)
    then if Model.is_subtype_of (assignment_mutability env (effective_bound env ga)) (assignment_mutability env (effective_bound env gt))
            && (negb (is_nullable env (effective_bound env ga)) || is_nullable env (effective_bound env gt))
         then Some (Ongoing s) else Some Failed
    else unify env n (Generic gt) (effective_bound env ga) (Ongoing s).
Proof.
    intros n gt ga s. rewrite <- !(assignment_mutability_generic env ranked), <- !(is_nullable_generic env ranked).
    destruct gt, ga. reflexivity.
Qed.

Section Bindings.

(* The bindings, and the fuel and states with which their type arguments are assignable to the
   bounds of the type parameters *)
Variable b: Bindings.
Variable K: nat.
Variable s: VariableStates.

Definition respects (x bound: EType): bool :=
    match unify env K bound x (Ongoing s) with Some (Ongoing _) => true | _ => false end.

(* The type parameter p is bound exactly, to a type of the fragment of Fragment.v that is
   assignable to `bound` *)
Definition binds_exactly (p: TypeParameterId) (bound: EType): bool :=
    match lookup_binding b p with
    | Some (TypeArgument Model.invariant o x) => is_exact_ownership o && gfrag env x && respects x bound
    | _ => false
    end.

(* The type parameter of the reference is bound exactly, to a type of the fragment of Fragment.v
   whose instance by the reference is assignable to its bound, instantiated *)
Definition binds_ref (g: GenericRef): bool :=
    match lookup_binding b (param_of g) with
    | Some (TypeArgument Model.invariant o x) =>
        is_exact_ownership o && gfrag env x && respects (inst_ref g x) (inst_nested b (effective_bound env g))
    | _ => false
    end.

(* The type parameters are bound to types of the fragment of Transitivity.v *)
Definition bindings_in_fragment: Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> in_fragment env x = true.

Definition ownership_bound (o: Ownership): bool :=
    match o with
    | parameter_ownership p =>
        match lookup_binding b p with
        | Some (TypeArgument Model.invariant o' _) => is_exact_ownership o'
        | _ => false
        end
    | _ => true
    end.

(* Every type parameter in the type is bound exactly, also those in the effective bounds of references,
   whose bound_in takes that from bound_bound_in (see Subtyping.through) *)
Fixpoint bound_in_h (bound_bound_in: GenericRef -> bool) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb (bound_in_h bound_bound_in) arguments
    | Nullable n => bound_in_h bound_bound_in n
    | Generic g => binds_ref g && bound_bound_in g
    | TypeArgument _ o n => ownership_bound o && bound_in_h bound_bound_in n
    | Intersection components => forallb (bound_in_h bound_bound_in) components
    | _ => true
    end.

Definition bound_bound_in (g: GenericRef): bool := through env bound_in_h true g.

Fixpoint bound_in (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb bound_in arguments
    | Nullable n => bound_in n
    | Generic g => binds_ref g && bound_bound_in g
    | TypeArgument _ o n => ownership_bound o && bound_in n
    | Intersection components => forallb bound_in components
    | _ => true
    end.

Lemma bound_in_h_agree: forall k U1 U2, (forall g, rank_of env g < k -> U1 g = U2 g) ->
    forall t, ranked_below env k t = true -> bound_in_h U1 t = bound_in_h U2 t.
Proof.
    intros k U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has].
      rewrite (IH a Ha), (IHa Has). reflexivity.
    - exact (IH n Ht).
    - rewrite (HU g (ref_ranked env k g Ht)). reflexivity.
    - rewrite (IH n Ht). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma bound_in_top: forall t, bound_in t = bound_in_h bound_bound_in t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; simpl; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite (IH a), IHa. reflexivity.
    - exact (IH n).
    - rewrite (IH n). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma bound_in_generic: forall g, bound_in (Generic g) = binds_ref g && bound_in (effective_bound env g).
Proof.
    intros g. change (bound_in (Generic g)) with (binds_ref g && bound_bound_in g). f_equal.
    rewrite bound_in_top. unfold bound_bound_in at 1. rewrite (through_eq env ranked); [reflexivity|exact bound_in_h_agree].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about the fragment                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma sfrag_cases: forall t, sfrag t = true ->
    (exists m c arguments, t = RootResolved m c arguments /\ class_eqb c nothing = false
        /\ length arguments = length (parameter_ids env c) /\ forall a, In a arguments -> argument_sfrag a = true)
    \/ t = bottom_type
    \/ (exists m c arguments, t = Nullable (RootResolved m c arguments) /\ sfrag (RootResolved m c arguments) = true)
    \/ (exists g, t = Generic g /\ generic_sfrag g)
    \/ (exists g, t = Nullable (Generic g) /\ generic_sfrag g).
Proof.
    assert (Hg: forall g, bound_tfrag g && as_written (given_mutability g) (is_narrowed g) (effective_bound env g) && no_type_variables g = true -> generic_sfrag g).
    { intros g H. apply sfrag_generic_iff. exact H. }
    intros [m c args|[m c args| |g| | | |]| g | | | |] H; simpl in H; try discriminate H.
    - destruct (class_eqb c nothing) eqn:Hc.
      + right. left. apply class_eqb_true in Hc. subst c.
        destruct m as [[]|], args; simpl in H; try discriminate H. reflexivity.
      + left. apply andb_true_iff in H. destruct H as [Hl Ha]. exists m, c, args.
        split; [reflexivity|]. split; [exact Hc|]. split; [apply Nat.eqb_eq, Hl|]. apply forallb_forall, Ha.
    - right. right. left. exists m, c, args. split; [reflexivity|exact H].
    - right. right. right. right. exists g. split; [reflexivity|]. exact (Hg g H).
    - right. right. right. left. exists g. split; [reflexivity|]. exact (Hg g H).
Qed.

Lemma bound_in_root: forall m c arguments,
    bound_in (RootResolved m c arguments) = true -> forall a, In a arguments -> bound_in a = true.
Proof. intros m c arguments H. apply forallb_forall, H. Qed.

Lemma tfrag_cases: forall t, tfrag t = true ->
    sfrag t = true
    \/ (exists cs, t = Intersection cs /\ components_sfrag cs = true)
    \/ (exists cs, t = Nullable (Intersection cs) /\ components_sfrag cs = true).
Proof.
    intros t H. destruct t as [m c args|[m c args|n|g|me msg|v o n|g|cs]|g|me msg|v o n|g|cs];
        try (left; exact H).
    - right. right. exists cs. split; [reflexivity|exact H].
    - right. left. exists cs. split; [reflexivity|exact H].
Qed.

Lemma components_sfrag_facts: forall cs, components_sfrag cs = true ->
    2 <= length cs /\ forall c, In c cs -> is_component_shape c = true /\ sfrag c = true.
Proof.
    intros cs H. unfold components_sfrag in H. apply andb_true_iff in H. destruct H as [Hl H].
    split; [apply Nat.leb_le, Hl|]. intros c Hc. rewrite forallb_forall in H. apply andb_true_iff, H, Hc.
Qed.

Lemma component_non_null: forall c, is_component_shape c = true -> is_nullable env c = false.
Proof. intros c H. unfold is_component_shape in H. apply andb_true_iff in H. apply negb_true_iff, H. Qed.

Lemma sdepth_component: forall cs c, In c cs -> S (sdepth c) <= sdepth (Intersection cs).
Proof.
    intros cs c Hc. change (S (sdepth c) <= S (list_max (map sdepth cs))).
    assert (H: Forall (fun k => k <= list_max (map sdepth cs)) (map sdepth cs)) by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (sdepth c) (in_map _ _ _ Hc)). lia.
Qed.

Lemma bound_in_component: forall cs c, bound_in (Intersection cs) = true -> In c cs -> bound_in c = true.
Proof. intros cs c H Hc. change (forallb bound_in cs = true) in H. rewrite forallb_forall in H. exact (H c Hc). Qed.

Lemma inst_component_nested: forall c, is_component_shape c = true -> inst_component b c = inst_nested b c.
Proof. intros [m c args|n|g|me msg|v o n|g|cs] H; try discriminate H; reflexivity. Qed.


Lemma sdepth_below: forall m c arguments a,
    In a arguments -> S (argument_sdepth a) <= sdepth (RootResolved m c arguments).
Proof.
    intros m c arguments a Ha. change (S (argument_sdepth a) <= S (list_max (map argument_sdepth arguments))).
    assert (H: Forall (fun k => k <= list_max (map argument_sdepth arguments)) (map argument_sdepth arguments))
        by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (argument_sdepth a) (in_map _ _ _ Ha)). lia.
Qed.

Lemma sdepth_generic: forall g, 1 <= sdepth (Generic g).
Proof. intros g. simpl. lia. Qed.

Lemma top_in_sfrag: sfrag top_type = true.
Proof.
    change ((is_class (RootResolved (Some readonly) any []) || is_generic (RootResolved (Some readonly) any []))
        && sfrag (RootResolved (Some readonly) any []) = true).
    simpl. rewrite (wf_any_has_no_type_parameters env wf). reflexivity.
Qed.

Lemma bottom_in_sfrag: sfrag bottom_type = true.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Types without type parameters                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma closed_facts: forall k,
    (forall t, sdepth t <= k -> sfrag t = true -> closed t = true ->
        in_fragment env t = true /\ instantiate env b t = t /\ bound_in t = true
        /\ mentions_loosely_bound b t = false)
    /\ (forall a, argument_sdepth a <= k -> argument_sfrag a = true -> closed a = true ->
        argument_in_fragment env a = true /\ instantiate env b a = a /\ bound_in a = true
        /\ mentions_loosely_bound b a = false).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht Hc. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
            simpl in Hd, Hc; try discriminate Hc; lia.
      - intros [| | | |v o n| |] Hd Ha _; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    assert (Hroot: forall m c args, sdepth (RootResolved m c args) <= S k -> sfrag (RootResolved m c args) = true ->
        closed (RootResolved m c args) = true ->
        in_fragment env (RootResolved m c args) = true /\ instantiate env b (RootResolved m c args) = RootResolved m c args
        /\ bound_in (RootResolved m c args) = true /\ mentions_loosely_bound b (RootResolved m c args) = false).
    { intros m c args Hd Ht Hc. change (forallb closed args = true) in Hc. rewrite forallb_forall in Hc.
      destruct (sfrag_cases _ Ht) as [[m' [c' [args' [Heq [Hcn [Hl Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
          try discriminate Heq.
      - injection Heq as <- <- <-.
        assert (Hall: forall a, In a args -> argument_in_fragment env a = true /\ instantiate env b a = a
            /\ bound_in a = true /\ mentions_loosely_bound b a = false).
        { intros a Ha. pose proof (sdepth_below m c args a Ha). apply IHa; [lia|apply Hargs, Ha|apply Hc, Ha]. }
        repeat split.
        + change (Nat.eqb (length args) (length (parameter_ids env c)) && forallb (argument_in_fragment env) args = true).
          rewrite Hl, Nat.eqb_refl. apply forallb_forall. intros a Ha. apply Hall, Ha.
        + simpl. f_equal. rewrite <- map_id. apply map_ext_in. intros a Ha. apply Hall, Ha.
        + apply forallb_forall. intros a Ha. apply Hall, Ha.
        + apply not_true_iff_false. intros H. change (existsb (mentions_loosely_bound b) args = true) in H.
          apply existsb_exists in H. destruct H as [a [Ha H]]. rewrite (proj2 (proj2 (proj2 (Hall a Ha)))) in H.
          discriminate H.
      - unfold bottom_type in Heq. injection Heq as -> -> ->. repeat split.
        change (Nat.eqb 0 (length (parameter_ids env nothing)) && forallb (argument_in_fragment env) [] = true).
        rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
    split.
    - intros t Hd Ht Hc. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> _]]|[g [-> _]]]]]].
      + exact (Hroot _ _ _ Hd Ht Hc).
      + exact (Hroot _ _ _ Hd Ht Hc).
      + assert (Hd': sdepth (RootResolved m c args) <= S k) by (simpl in Hd |- *; lia).
        destruct (Hroot m c args Hd' Ht' Hc) as [Hf [Hi [Hb Hm]]]. repeat split.
        * exact Hf.
        * change (rewrap_nullable (instantiate env b (RootResolved m c args)) = Nullable (RootResolved m c args)).
          rewrite Hi. reflexivity.
        * exact Hb.
        * exact Hm.
      + discriminate Hc.
      + discriminate Hc.
    - intros [| | | |v o n| |] Hd Ha Hc; simpl in Ha; try discriminate Ha. simpl in Hd.
      change (negb (is_parameter_ownership o) && closed n = true) in Hc. apply andb_true_iff in Hc. destruct Hc as [Ho Hc].
      destruct (IHt n ltac:(lia) Ha Hc) as [Hf [Hi [Hb Hm]]].
      assert (Ho': instantiate_ownership b o = o /\ ownership_bound o = true) by (destruct o; split; first [reflexivity|discriminate Ho]).
      destruct Ho' as [Hio Hob]. repeat split.
      + exact Hf.
      + destruct (sfrag_cases n Ha) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]].
        * simpl in Hi, Hm |- *. injection Hi as Hi. rewrite Hm, Hio, Hi. reflexivity.
        * simpl. rewrite Hio. reflexivity.
        * simpl in Hi, Hm |- *. injection Hi as Hi. rewrite Hm, Hio, Hi. reflexivity.
        * discriminate Hc.
        * discriminate Hc.
      + simpl. rewrite Hob. exact Hb.
      + exact Hm.
Qed.

Lemma closed_in_fragment: forall t, sfrag t = true -> closed t = true -> in_fragment env t = true.
Proof. intros t Ht Hc. exact (proj1 (proj1 (closed_facts (sdepth t)) t (le_n _) Ht Hc)). Qed.

(* A type without type parameters is its own instance *)
Lemma inst_nested_closed: forall t, sfrag t = true -> closed t = true -> inst_nested b t = t.
Proof.
    intros t Ht Hc. destruct (proj1 (closed_facts (sdepth t)) t (le_n _) Ht Hc) as [_ [Hi _]].
    destruct (sfrag_cases t Ht) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[? [-> _]]|[? [-> _]]]]]];
        [exact Hi|exact Hi|exact Hi|discriminate Hc|discriminate Hc].
Qed.

(* For a reference bounded by a type without type parameters, it is the type argument within that *)
Lemma binds_ref_closed: forall p, sfrag (parameter_bound env p) = true -> closed (parameter_bound env p) = true ->
    bound_in (Generic (mkGenericRef None false p [])) = binds_exactly p (parameter_bound env p).
Proof.
    intros p Hf Hc. destruct (proj1 (closed_facts (sdepth _)) _ (le_n _) Hf Hc) as [_ [_ [Hb _]]].
    rewrite bound_in_generic, (effective_bound_plain env ranked), Hb, andb_true_r. unfold binds_ref. cbn [param_of].
    rewrite (effective_bound_plain env ranked), (inst_nested_closed _ Hf Hc). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating with exact type arguments                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma binds_exactly_some: forall p bound, binds_exactly p bound = true ->
    exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ gfrag env x = true /\ respects x bound = true.
Proof.
    intros p bound H. unfold binds_exactly in H. destruct (lookup_binding b p) as [a|]; [|discriminate H].
    destruct a as [| | | |v o x| |]; try discriminate H. destruct v; try discriminate H.
    apply andb_true_iff in H. destruct H as [H Hr]. apply andb_true_iff in H. destruct H as [Ho Hx].
    exists o, x. auto.
Qed.

Lemma binds_ref_some: forall g, bound_in (Generic g) = true ->
    exists o x, lookup_binding b (param_of g) = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ gfrag env x = true
        /\ respects (inst_ref g x) (inst_nested b (effective_bound env g)) = true /\ bound_in (effective_bound env g) = true.
Proof.
    intros g Hb. assert (H': binds_ref g = true /\ bound_in (effective_bound env g) = true)
        by (rewrite bound_in_generic in Hb; apply andb_true_iff in Hb; exact Hb).
    destruct H' as [H Hbe]. unfold binds_ref in H. destruct (lookup_binding b (param_of g)) as [a|]; [|discriminate H].
    destruct a as [| | | |v o x| |]; try discriminate H. destruct v; try discriminate H.
    apply andb_true_iff in H. destruct H as [H Hr]. apply andb_true_iff in H. destruct H as [Ho Hx].
    exists o, x. auto.
Qed.

Lemma inst_nested_generic: forall g v o x,
    lookup_binding b (param_of g) = Some (TypeArgument v o x) -> inst_nested b (Generic g) = inst_ref g x.
Proof. intros g v o x H. unfold inst_nested. rewrite H. reflexivity. Qed.

Lemma inst_nested_nullable_generic: forall g v o x,
    lookup_binding b (param_of g) = Some (TypeArgument v o x) -> inst_nested b (Nullable (Generic g)) = rewrap_nullable (inst_ref g x).
Proof. intros g v o x H. unfold inst_nested. rewrite H. reflexivity. Qed.

(* A type of the fragment of Fragment.v, with a mutability or `!` applied, is no type argument *)
Lemma gfrag_inst_ref_flat: forall g x, gfrag env x = true -> nests_argument (inst_ref g x) = false.
Proof.
    intros g x Hx. unfold inst_ref, inst_fit.
    destruct (gfrag_cases env x Hx) as [[m [c [args ->]]]|[[n [-> [Hn _]]]|[[gm [nn [p [bound [-> _]]]]]|[cs ->]]]];
        destruct (given_mutability g), (is_narrowed g); try reflexivity;
        destruct n as [| | [] | | | |]; simpl in Hn; try discriminate Hn; reflexivity.
Qed.

(* Bound exactly, a reference instantiates to the instance of the reference *)
Lemma instantiate_exact_generic: forall g o' x,
    lookup_binding b (param_of g) = Some (TypeArgument Model.invariant o' x) -> is_exact_ownership o' = true ->
    gfrag env x = true -> instantiate env b (Generic g) = inst_ref g x /\ mentions_loosely_bound b (Generic g) = false.
Proof.
    intros [gm nn p bound] o' x E Ho Hx. cbn [param_of] in E.
    assert (Hn: nests_argument x = false) by (pose proof (gfrag_inst_ref_flat (mkGenericRef None false p bound) x Hx) as H; exact H).
    assert (Hl: is_loose (TypeArgument Model.invariant o' x) = false) by (destruct o'; first [reflexivity|discriminate Ho]).
    simpl. rewrite E. unfold final_argument. rewrite Hl, Hn. split; [|reflexivity]. unfold inst_ref, inst_fit. reflexivity.
Qed.

(* A type argument whose type, instantiated, is no type argument, and mentions nothing bound loosely *)
Lemma instantiate_argument_plain: forall v o n y, instantiate env b n = y -> mentions_loosely_bound_in_arguments b n = false ->
    nests_argument y = false -> instantiate env b (TypeArgument v o n) = TypeArgument v (instantiate_ownership b o) y.
Proof.
    intros v o n y Hi Hm Hn. simpl. rewrite Hi, Hm.
    destruct y as [| [] | | | | |]; try discriminate Hn; reflexivity.
Qed.

(* A reference, instantiated in a type argument, takes the place of the type in it *)
Lemma instantiate_generic_argument: forall v o g o' x,
    lookup_binding b (param_of g) = Some (TypeArgument Model.invariant o' x) -> is_exact_ownership o' = true -> gfrag env x = true ->
    instantiate env b (TypeArgument v o (Generic g)) = TypeArgument v (instantiate_ownership b o) (inst_ref g x)
    /\ instantiate env b (TypeArgument v o (Nullable (Generic g))) = TypeArgument v (instantiate_ownership b o) (rewrap_nullable (inst_ref g x)).
Proof.
    intros v o g o' x E Ho Hx. destruct (instantiate_exact_generic g o' x E Ho Hx) as [Hi _].
    pose proof (gfrag_inst_ref_flat g x Hx) as Hn. split.
    - exact (instantiate_argument_plain v o _ _ Hi eq_refl Hn).
    - apply instantiate_argument_plain; [change (rewrap_nullable (instantiate env b (Generic g)) = rewrap_nullable (inst_ref g x)); rewrite Hi; reflexivity|reflexivity|].
      destruct (inst_ref g x) as [| [] | | | | |]; first [reflexivity|discriminate Hn].
Qed.

(* Within the fragment, the instance is what the frontend instantiates the type to *)
Lemma inst_nested_instantiate: forall t, tfrag t = true -> bound_in t = true -> inst_nested b t = instantiate env b t.
Proof.
    assert (Hgen: forall g, bound_in (Generic g) = true -> inst_nested b (Generic g) = instantiate env b (Generic g)).
    { intros g Hb. destruct (binds_ref_some g Hb) as [o [x [E [Ho [Hx _]]]]].
      rewrite (inst_nested_generic g _ o x E). symmetry. exact (proj1 (instantiate_exact_generic g o x E Ho Hx)). }
    assert (Hinter: forall cs, components_sfrag cs = true -> bound_in (Intersection cs) = true ->
        inst_nested b (Intersection cs) = instantiate env b (Intersection cs)).
    { intros cs Hcs Hb. destruct (components_sfrag_facts cs Hcs) as [_ Hc].
      change (inst_nested b (Intersection cs)) with (inst_intersection b cs). unfold inst_intersection.
      change (instantiate env b (Intersection cs)) with (of_components env (flat_map intersected_components (map (instantiate env b) cs))).
      f_equal. f_equal. apply map_ext_in. intros c Hin. rewrite (inst_component_nested c (proj1 (Hc c Hin))).
      pose proof (proj1 (Hc c Hin)) as Hsh.
      destruct c as [m d args|n|g|me msg|v o n|g|cs']; try discriminate Hsh; [reflexivity|].
      exact (Hgen g (bound_in_component cs _ Hb Hin)). }
    intros t Ht Hb. destruct (tfrag_cases t Ht) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (sfrag_cases t Hs) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]]; try reflexivity.
      + exact (Hgen g Hb).
      + destruct (binds_ref_some g Hb) as [o [x [E [Ho [Hx _]]]]]. rewrite (inst_nested_nullable_generic g _ o x E).
        change (instantiate env b (Nullable (Generic g))) with (rewrap_nullable (instantiate env b (Generic g))).
        rewrite (proj1 (instantiate_exact_generic g o x E Ho Hx)). reflexivity.
    - exact (Hinter cs Hcs Hb).
    - change (inst_nested b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested b (Intersection cs))).
      change (instantiate env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate env b (Intersection cs))).
      rewrite (Hinter cs Hcs Hb). reflexivity.
Qed.

(* Nothing is bound loosely, so instantiating widens no type argument *)
Lemma no_loose: forall k,
    (forall t, sdepth t <= k -> sfrag t = true -> bound_in t = true -> mentions_loosely_bound b t = false)
    /\ (forall a, argument_sdepth a <= k -> argument_sfrag a = true -> bound_in a = true -> mentions_loosely_bound b a = false).
Proof.
    assert (Hgen: forall g, bound_in (Generic g) = true -> mentions_loosely_bound b (Generic g) = false).
    { intros g Hb. destruct (binds_ref_some g Hb) as [o [x [E [Ho _]]]].
      destruct g as [gm nn p bound]. simpl in E |- *. rewrite E. destruct o; try discriminate Ho; reflexivity. }
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht _. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
            first [pose proof (sdepth_generic g); lia|simpl in Hd; lia].
      - intros [| | | |v o n| |] Hd Ha _; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    assert (Hroot: forall m c args, sdepth (RootResolved m c args) <= S k -> sfrag (RootResolved m c args) = true ->
        bound_in (RootResolved m c args) = true -> mentions_loosely_bound b (RootResolved m c args) = false).
    { intros m c args Hd Ht Hb.
      destruct (sfrag_cases _ Ht) as [[m' [c' [args' [Heq [_ [_ Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
          try discriminate Heq.
      - injection Heq as <- <- <-. apply not_true_iff_false. intros H.
        change (existsb (mentions_loosely_bound b) args = true) in H.
        apply existsb_exists in H. destruct H as [a [Ha H]]. pose proof (sdepth_below m c args a Ha).
        rewrite (IHa a ltac:(lia) (Hargs a Ha) (bound_in_root m c args Hb a Ha)) in H. discriminate H.
      - unfold bottom_type in Heq. injection Heq as -> -> ->. reflexivity. }
    split.
    - intros t Hd Ht Hb. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> _]]|[g [-> _]]]]]].
      + exact (Hroot _ _ _ Hd Ht Hb).
      + exact (Hroot _ _ _ Hd Ht Hb).
      + assert (Hd': sdepth (RootResolved m c args) <= S k) by (simpl in Hd |- *; lia). exact (Hroot _ _ _ Hd' Ht' Hb).
      + exact (Hgen g Hb).
      + exact (Hgen g Hb).
    - intros [| | | |v o n| |] Hd Ha Hb; simpl in Ha; try discriminate Ha. simpl in Hd, Hb |- *.
      apply andb_true_iff in Hb. apply IHt; [lia|exact Ha|apply Hb].
Qed.

Lemma no_loose_type: forall t, sfrag t = true -> bound_in t = true -> mentions_loosely_bound b t = false.
Proof. intros t. apply (proj1 (no_loose (sdepth t))). lia. Qed.

(* A type argument, instantiated, is of the same variance, and has the instantiated type in it *)
Lemma instantiate_bound_argument: forall v o n, sfrag n = true -> bound_in n = true ->
    instantiate env b (TypeArgument v o n) = TypeArgument v (instantiate_ownership b o) (inst_nested b n).
Proof.
    intros v o n Hn Hb. pose proof (no_loose_type n Hn Hb) as Hm.
    destruct (sfrag_cases n Hn) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]].
    - simpl in Hm |- *. rewrite Hm. reflexivity.
    - reflexivity.
    - simpl in Hm |- *. rewrite Hm. reflexivity.
    - destruct (binds_ref_some g Hb) as [o' [x [E [Ho [Hx _]]]]].
      rewrite (inst_nested_generic g _ o' x E). exact (proj1 (instantiate_generic_argument v o g o' x E Ho Hx)).
    - destruct (binds_ref_some g Hb) as [o' [x [E [Ho [Hx _]]]]].
      rewrite (inst_nested_nullable_generic g _ o' x E). exact (proj2 (instantiate_generic_argument v o g o' x E Ho Hx)).
Qed.

Lemma bound_in_argument: forall v o n, bound_in (TypeArgument v o n) = true -> ownership_bound o = true /\ bound_in n = true.
Proof. intros v o n H. simpl in H. apply andb_true_iff in H. exact H. Qed.

(* Instantiated with types of the fragment of Transitivity.v, a type is of it *)
Lemma instances_in_fragment: bindings_in_fragment -> forall k,
    (forall t, sdepth t <= k -> sfrag t = true -> bound_in t = true -> in_fragment env (inst_nested b t) = true)
    /\ (forall a, argument_sdepth a <= k -> argument_sfrag a = true -> bound_in a = true ->
        argument_in_fragment env (instantiate env b a) = true).
Proof.
    intros Hbf. induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht _. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
            first [pose proof (sdepth_generic g); lia|simpl in Hd; lia].
      - intros [| | | |v o n| |] Hd Ha _; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    assert (Hroot: forall m c args, sdepth (RootResolved m c args) <= S k -> sfrag (RootResolved m c args) = true ->
        bound_in (RootResolved m c args) = true -> in_fragment env (RootResolved m c (map (instantiate env b) args)) = true).
    { intros m c args Hd Ht Hb.
      destruct (sfrag_cases _ Ht) as [[m' [c' [args' [Heq [_ [Hl Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
          try discriminate Heq.
      - injection Heq as <- <- <-.
        change (Nat.eqb (length (map (instantiate env b) args)) (length (parameter_ids env c))
            && forallb (argument_in_fragment env) (map (instantiate env b) args) = true).
        rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
        destruct Ha' as [a [<- Ha]]. pose proof (sdepth_below m c args a Ha).
        apply IHa; [lia|apply Hargs, Ha|apply (bound_in_root m c args Hb a Ha)].
      - unfold bottom_type in Heq. injection Heq as -> -> ->.
        change (Nat.eqb 0 (length (parameter_ids env nothing)) && forallb (argument_in_fragment env) [] = true).
        rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
    split.
    - intros t Hd Ht Hb. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> _]]|[g [-> _]]]]]].
      + exact (Hroot _ _ _ Hd Ht Hb).
      + exact (Hroot _ _ _ Hd Ht Hb).
      + assert (Hd': sdepth (RootResolved m c args) <= S k) by (simpl in Hd |- *; lia).
        change (is_class (RootResolved m c (map (instantiate env b) args))
            && in_fragment env (RootResolved m c (map (instantiate env b) args)) = true).
        rewrite (Hroot _ _ _ Hd' Ht' Hb). reflexivity.
      + destruct (binds_ref_some g Hb) as [o [x [E _]]]. rewrite (inst_nested_generic g _ o x E).
        apply inst_ref_in_fragment. exact (Hbf _ o x E).
      + destruct (binds_ref_some g Hb) as [o [x [E _]]]. rewrite (inst_nested_nullable_generic g _ o x E).
        apply in_fragment_rewrap, inst_ref_in_fragment. exact (Hbf _ o x E).
    - intros [| | | |v o n| |] Hd Ha Hb; simpl in Ha; try discriminate Ha. simpl in Hd.
      destruct (bound_in_argument v o n Hb) as [_ Hb'].
      rewrite (instantiate_bound_argument v o n Ha Hb'). apply IHt; [lia|exact Ha|exact Hb'].
Qed.

Lemma instance_in_fragment: bindings_in_fragment ->
    forall t, sfrag t = true -> bound_in t = true -> in_fragment env (inst_nested b t) = true.
Proof. intros Hbf t. apply (proj1 (instances_in_fragment Hbf (sdepth t))). lia. Qed.

Lemma argument_instance_in_fragment: bindings_in_fragment ->
    forall a, argument_sfrag a = true -> bound_in a = true -> argument_in_fragment env (instantiate env b a) = true.
Proof. intros Hbf a. apply (proj2 (instances_in_fragment Hbf (argument_sdepth a))). lia. Qed.

Lemma instance_not_variable: forall t, sfrag t = true -> bound_in t = true -> is_type_variable (inst_nested b t) = false.
Proof.
    intros t Ht Hb. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
        try reflexivity.
    - destruct (binds_ref_some g Hb) as [o [x [E [_ [Hx _]]]]]. rewrite (inst_nested_generic g _ o x E).
      exact (inst_ref_not_variable g x Hx).
    - destruct (binds_ref_some g Hb) as [o [x [E _]]]. rewrite (inst_nested_nullable_generic g _ o x E).
      unfold rewrap_nullable. destruct (inst_ref g x); reflexivity.
Qed.

(* Instantiating keeps a type argument loose or not *)
Lemma instance_loose: forall a, argument_sfrag a = true -> bound_in a = true -> is_loose (instantiate env b a) = is_loose a.
Proof.
    intros [| | | |v o n| |] Ha Hb; simpl in Ha; try discriminate Ha.
    destruct (bound_in_argument v o n Hb) as [Ho Hb'].
    rewrite (instantiate_bound_argument v o n Ha Hb'). simpl.
    destruct o as [| | |q]; try reflexivity. simpl in Ho |- *.
    destruct (lookup_binding b q) as [[| | | |v' o' x| |]|]; try discriminate Ho. destruct v'; try discriminate Ho.
    destruct o'; try discriminate Ho; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Supertypes: instantiating commutes with instantiating the templates                            *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma nothing_is_bottom_root: forall m c args, nothing_is_bottom (RootResolved m c args) = true ->
    (class_eqb c nothing = true -> is_bottom m args = true) /\ forall a, In a args -> nothing_is_bottom a = true.
Proof.
    intros m c args H. simpl in H. apply andb_true_iff in H. destruct H as [Hc Ha]. split.
    - intros E. rewrite E in Hc. exact Hc.
    - apply forallb_forall, Ha.
Qed.

Lemma instance_is_type_argument: forall a, argument_sfrag a = true -> bound_in a = true ->
    is_type_argument (instantiate env b a) = true.
Proof.
    intros [| | | |v o n| |] Ha Hb; simpl in Ha; try discriminate Ha.
    rewrite (instantiate_bound_argument v o n Ha (proj2 (bound_in_argument v o n Hb))). reflexivity.
Qed.

Lemma inst_nested_class_shaped: forall x, class_shaped x -> inst_nested b x = instantiate env b x.
Proof. intros x [[m [c [args ->]]]|[m [c [args ->]]]]; reflexivity. Qed.

Section Templates.

Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> argument_sfrag y = true /\ bound_in y = true.

Let bS := bindings_of env sub ys.
Let bL := bindings_of env sub (map (instantiate env b) ys).

Lemma Hys_type_argument: forall y, In y ys -> is_type_argument y = true.
Proof.
    intros y Hy. destruct (Hys y Hy) as [Ha _]. destruct y as [| | | |v o n| |]; try discriminate Ha. reflexivity.
Qed.

(* A template, instantiated with ys, is of the fragment *)
Lemma template_instances: forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> nothing_is_bottom t = true ->
        sfrag (instantiate env bS t) = true /\ bound_in (instantiate env bS t) = true)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> nothing_is_bottom r = true ->
        argument_sfrag (instantiate env bS r) = true /\ bound_in (instantiate env bS r) = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht _; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true -> nothing_is_bottom (RootResolved m c targs) = true ->
        sfrag (RootResolved m c (map (instantiate env bS) targs)) = true
        /\ bound_in (RootResolved m c (map (instantiate env bS) targs)) = true).
    { intros m c targs Hd Ht Hn. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      destruct (nothing_is_bottom_root m c targs Hn) as [Hc Hnargs].
      assert (Hall: forall a, In a targs -> argument_sfrag (instantiate env bS a) = true /\ bound_in (instantiate env bS a) = true).
      { intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha|apply Hnargs, Ha]. }
      split.
      - simpl. destruct (class_eqb c nothing) eqn:Ec.
        + specialize (Hc eq_refl). destruct m as [[]|], targs; simpl in Hc; try discriminate Hc. reflexivity.
        + rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
          destruct Ha' as [a [<- Ha]]. apply Hall, Ha.
      - change (forallb bound_in (map (instantiate env bS) targs) = true). apply forallb_forall.
        intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. apply Hall, Ha. }
    split.
    - intros t Hd Ht Hn. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite instantiate_class. exact (Hroot m c targs Hd Ht Hn).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class.
        destruct (Hroot m c targs ltac:(lia) Ht' Hn) as [Hf Hb]. split; [|exact Hb].
        change ((is_class (RootResolved m c (map (instantiate env bS) targs)) || is_generic (RootResolved m c (map (instantiate env bS) targs)))
            && sfrag (RootResolved m c (map (instantiate env bS) targs)) = true). rewrite Hf. reflexivity.
    - intros r Hd Hr Hn. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        unfold bS. rewrite (selects env wf sub ys p bp i y Hi Hy (Hys_type_argument y (nth_error_In _ _ Hy))).
        apply Hys. eapply nth_error_In. exact Hy.
      + simpl in Hd, Hn. destruct (IHt n ltac:(lia) Hn' Hn) as [Hf Hb].
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        assert (Hob: ownership_bound o = true) by (destruct o; first [reflexivity|discriminate Ho]).
        destruct (mentions_loosely_bound bS n); [destruct v|]; simpl; rewrite ?Hob, ?Hf, ?Hb; split; reflexivity.
Qed.

(* Templates are loose where they are instantiated with ys exactly where with ys instantiated *)
Lemma template_looseness: forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        mentions_loosely_bound bL t = mentions_loosely_bound bS t)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        mentions_loosely_bound bL r = mentions_loosely_bound bS r).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        existsb (mentions_loosely_bound bL) targs = existsb (mentions_loosely_bound bS) targs).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs]. apply existsb_ext_in.
      intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite !mentions_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite !mentions_nullable, !mentions_class. exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map (instantiate env b) ys) i = Some (instantiate env b y))
            by (rewrite nth_error_map, Hy; reflexivity).
        unfold bL, bS. rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub _ i p _ Hi Hy')).
        rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub ys i p y Hi Hy)).
        destruct (Hys y (nth_error_In _ _ Hy)) as [Ha Hb]. apply instance_loose; assumption.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn'].
Qed.

(* Instantiating a template with ys, then with b, is instantiating it with ys instantiated *)
Lemma template_commutes: forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> nothing_is_bottom t = true ->
        instantiate env b (instantiate env bS t) = instantiate env bL t)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> nothing_is_bottom r = true ->
        instantiate env b (instantiate env bS r) = instantiate env bL r).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht _; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true -> nothing_is_bottom (RootResolved m c targs) = true ->
        map (instantiate env b) (map (instantiate env bS) targs) = map (instantiate env bL) targs).
    { intros m c targs Hd Ht Hn. destruct (root_template env sub m c targs Ht) as [_ Htargs].
      destruct (nothing_is_bottom_root m c targs Hn) as [_ Hnargs].
      rewrite map_map. apply map_ext_in. intros a Ha. pose proof (argument_depth_below m c targs a Ha).
      apply IHa; [lia|apply Htargs, Ha|apply Hnargs, Ha]. }
    split.
    - intros t Hd Ht Hn. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite !instantiate_class, (Hroot m c targs Hd Ht Hn). reflexivity.
      + rewrite depth_nullable in Hd. rewrite !instantiate_nullable_class, (Hroot m c targs ltac:(lia) Ht' Hn). reflexivity.
    - intros r Hd Hr Hn. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map (instantiate env b) ys) i = Some (instantiate env b y))
            by (rewrite nth_error_map, Hy; reflexivity).
        destruct (Hys y (nth_error_In _ _ Hy)) as [Ha Hb].
        unfold bS, bL. rewrite (selects env wf sub ys p bp i y Hi Hy (Hys_type_argument y (nth_error_In _ _ Hy))).
        rewrite (selects env wf sub _ p bp i _ Hi Hy' (instance_is_type_argument y Ha Hb)). reflexivity.
      + simpl in Hd, Hn.
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        rewrite (instantiate_template_argument env bL v o n Ho (template_shape env sub n Hn')).
        rewrite (proj1 (template_looseness (depth n)) n (le_n _) Hn').
        destruct (proj1 (template_instances (depth n)) n (le_n _) Hn' Hn) as [Hf Hb].
        assert (Hio: instantiate_ownership b o = o) by (destruct o; first [reflexivity|discriminate Ho]).
        pose proof (template_instance_shape env sub bS n Hn') as Hshape.
        destruct (mentions_loosely_bound bS n); [destruct v; cbn beta iota|];
            first [ rewrite (instantiate_bound_argument _ o bottom_type bottom_in_sfrag eq_refl), Hio; reflexivity
                  | rewrite (instantiate_bound_argument _ o _ Hf Hb), Hio, (inst_nested_class_shaped _ Hshape),
                        (IHt n ltac:(lia) Hn' Hn); reflexivity ].
Qed.

End Templates.

(* The type arguments of a supertype, normalized from those of a subclass, are of the fragment, and
   instantiating them is normalizing the instantiated type arguments *)
Lemma supertype_arguments_commute: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> argument_sfrag y = true /\ bound_in y = true) ->
    parameterized_supertype_arguments env sub (map (instantiate env b) ys) super
        = map (instantiate env b) (parameterized_supertype_arguments env sub ys super)
    /\ forall a, In a (parameterized_supertype_arguments env sub ys super) -> argument_sfrag a = true /\ bound_in a = true.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite !parameterized_supertype_arguments_eq. split.
    - rewrite map_map. apply map_ext_in. intros r Hr. symmetry.
      apply (proj2 (template_commutes sub ys Hl Hys (argument_depth r))); [lia|apply Ht, Hr|].
      exact (supertypes_mention_nothing_as_bottom sub super r Hr).
    - intros a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      apply (proj2 (template_instances sub ys Hl Hys (argument_depth r))); [lia|apply Ht, Hr|].
      exact (supertypes_mention_nothing_as_bottom sub super r Hr).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify on the fragment, one step                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma respects_unify: forall x bound, in_fragment env x = true -> cfrag bound = true -> respects x bound = true ->
    unify env K bound x (Ongoing s) = Some (Ongoing s).
Proof.
    intros x bound Hx Hb H. unfold respects in H. destruct (unify env K bound x (Ongoing s)) as [[w|]|] eqn:Eu; try discriminate H.
    rewrite (cfrag_keeps K bound x s w Hb Hx Eu). reflexivity.
Qed.

(* `exclusive Nothing` is assignable to every type of the fragment of Transitivity.v *)
Lemma below_all: forall x f, in_fragment env x = true -> 2 <= f -> unify env f x bottom_type (Ongoing s) = Some (Ongoing s).
Proof.
    intros x f Hx Hf. apply (below_bottom env wf 1 bottom_type s); [exact (bottom_in_fragment env wf)| |exact Hx|exact Hf].
    apply (proj1 (reflexivity_with_arguments env 1)); [exact (bottom_in_fragment env wf)|simpl; lia].
Qed.

Lemma fold_pairs: forall n n' targs aargs u,
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing u) ->
    (forall t a u0, In t targs -> In a aargs -> unify env n t a (Ongoing s) = Some (Ongoing u0) ->
        u0 = s /\ unify env n' (instantiate env b t) (instantiate env b a) (Ongoing s) = Some (Ongoing s)) ->
    u = s /\ fold_unify (fun inner '(t, a) => unify env n' t a inner)
        (combine (map (instantiate env b) targs) (map (instantiate env b) aargs)) (Ongoing s) = Some (Ongoing s).
Proof.
    intros n n' targs. induction targs as [|t targs IH]; intros aargs u H Hpair;
        destruct aargs as [|a aargs]; simpl in *; try (injection H as <-; auto).
    destruct (unify env n t a (Ongoing s)) as [[s1|]|] eqn:E1; try discriminate H.
    - destruct (Hpair t a s1 (or_introl eq_refl) (or_introl eq_refl) E1) as [-> Hinst].
      rewrite Hinst. apply (IH aargs u H). intros t' a' u0 Ht Ha. apply Hpair; right; assumption.
    - rewrite fold_stays_failed in H. discriminate H.
Qed.


(* Two references to the same type parameter, the one's bound below the other's: their instances
   are, too. The instance of the assignee is assignable to B, its bound instantiated, which is of no
   more mutability than the bound, and non-null where it is. The mutability given to the one fits
   that given to the other; where only the target is narrowed, the bounds are non-null, and so are
   the instances. *)
Lemma same_parameter: forall f gt ga x B, in_fragment env x = true -> cfrag B = true ->
    unify env f x x (Ongoing s) = Some (Ongoing s) -> generic_sfrag gt ->
    unify env K B (inst_ref ga x) (Ongoing s) = Some (Ongoing s) ->
    Model.is_subtype_of (assignment_mutability env B) (assignment_mutability env (effective_bound env ga)) = true ->
    (is_nullable env (effective_bound env ga) = false -> is_nullable env B = false) ->
    Model.is_subtype_of (assignment_mutability env (effective_bound env ga)) (assignment_mutability env (effective_bound env gt)) = true ->
    negb (is_nullable env (effective_bound env ga)) || is_nullable env (effective_bound env gt) = true ->
    unify env f (inst_ref gt x) (inst_ref ga x) (Ongoing s) = Some (Ongoing s).
Proof.
    intros f gt ga x B Hx HB Hrefl [_ [Hwt _]] Hra HmB HnB Hm Hn.
    pose proof (inst_ref_in_fragment ga x Hx) as HIa.
    pose proof (mutability_subtype_trans _ _ _ (cfrag_mutability _ _ _ _ _ HB HIa Hra) HmB) as Hma.
    unfold as_written in Hwt. apply andb_true_iff in Hwt. destruct Hwt as [Hwtm Hwtn].
    (* the type argument, with the mutabilities applied *)
    assert (Hfit: unify env f (inst_fit gt x) (inst_fit ga x) (Ongoing s) = Some (Ongoing s)).
    { apply (unify_remut f x _ x _ s s (remut_inst_fit gt x Hx) (remut_inst_fit ga x Hx)); [|exact Hrefl].
      destruct (with_mutability_cases x Hx) as [Hk|Hk].
      - unfold inst_fit at 2. destruct (given_mutability gt) as [m|] eqn:Eg.
        + rewrite Hk. apply intersect_mutability_greatest.
          * eapply mutability_subtype_trans; [apply inst_fit_mutability_below, Hx|apply (assignment_mutability_below env ranked)].
          * rewrite <- (mutability_inst_ref ga x Hx). exact (mutability_subtype_trans _ _ _ (mutability_subtype_trans _ _ _ Hma Hm) Hwtm).
        + apply inst_fit_mutability_below, Hx.
      - assert (Hfx: forall g, assignment_mutability env (inst_fit g x) = assignment_mutability env x).
        { intros g. unfold inst_fit. destruct (given_mutability g); [apply Hk|reflexivity]. }
        rewrite !Hfx. apply mutability_is_subtype_of_refl. }
    pose proof (inst_fit_in_fragment gt x Hx) as HIft. pose proof (inst_fit_in_fragment ga x Hx) as HIfa.
    unfold inst_ref. destruct (is_narrowed gt) eqn:Ent, (is_narrowed ga) eqn:Ena.
    - exact (unify_without_null f _ _ s s HIft HIfa Hfit).
    - (* the target is narrowed, so the bounds and the assignee are non-null *)
      cbn [negb orb] in Hwtn. apply negb_true_iff in Hwtn. rewrite Hwtn, orb_false_r in Hn. apply negb_true_iff in Hn.
      pose proof (cfrag_non_null _ _ _ _ _ HB HIa (HnB Hn) Hra) as Hna. unfold inst_ref in Hna. rewrite Ena in Hna.
      rewrite <- (without_null_non_null _ HIfa Hna). exact (unify_without_null f _ _ s s HIft HIfa Hfit).
    - exact (unify_without_null_assignee f _ _ s s HIft HIfa Hfit).
    - exact Hfit.
Qed.

(* Without null, a type of the fragment is of it, of the same mutability, and non-null *)
Lemma tfrag_without_null: forall k t, sdepth t <= k -> tfrag t = true ->
    tfrag (without_null env t) = true /\ assignment_mutability env (without_null env t) = assignment_mutability env t
    /\ is_nullable env (without_null env t) = false.
Proof.
    induction k as [|k IH].
    { intros t Hd Ht. destruct (tfrag_cases t Ht) as [Hs|[[cs [-> _]]|[cs [-> _]]]]; [|simpl in Hd; lia|simpl in Hd; lia].
      destruct (sfrag_cases t Hs) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
          first [pose proof (sdepth_generic g); lia|simpl in Hd; lia]. }
    assert (Hgen: forall g, sdepth (Generic g) <= S k -> generic_sfrag g ->
        sfrag (Generic (narrow_ref g)) = true /\ assignment_mutability env (Generic (narrow_ref g)) = assignment_mutability env (Generic g)
        /\ is_nullable env (Generic (narrow_ref g)) = false).
    { intros [gm nn p vs] Hd [Hf [Hw Hv]]. destruct vs; [|discriminate Hv]. rewrite sdepth_bound in Hd.
      destruct (IH (effective_bound env (mkGenericRef gm nn p [])) ltac:(lia) Hf) as [Hf' [Hm' Hn']].
      unfold narrow_ref. cbn [given_mutability is_narrowed param_of variables_of].
      rewrite sfrag_generic, !mutability_generic, (nullable_generic (mkGenericRef gm (nn || is_nullable env (Generic (mkGenericRef gm nn p []))) p [])),
          !(effective_bound_narrowed env ranked), Hf', Hm', Hn'.
      split; [|split; reflexivity]. cbn [given_mutability is_narrowed variables_of no_type_variables].
      unfold as_written in Hw |- *. cbn [given_mutability is_narrowed] in Hw |- *. rewrite ?Hm', ?Hn'.
      apply andb_true_iff in Hw. destruct Hw as [Hwm _]. rewrite Hwm, ?orb_true_r. reflexivity. }
    intros t Hd Ht. destruct (tfrag_cases t Ht) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (sfrag_cases t Hs) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + split; [exact Ht|split; reflexivity].
      + split; [reflexivity|split; reflexivity].
      + split; [exact Ht'|split; reflexivity].
      + rewrite without_null_generic. exact (Hgen g Hd Hg).
      + change (without_null env (Nullable (Generic g))) with (without_null env (Generic g)). rewrite without_null_generic.
        change (assignment_mutability env (Nullable (Generic g))) with (assignment_mutability env (Generic g)).
        apply Hgen; [change (S (sdepth (Generic g)) <= S k) in Hd; lia|exact Hg].
    - split; [exact Hcs|split; reflexivity].
    - split; [exact Hcs|split; reflexivity].
Qed.

Section Instances.

Hypothesis Hbf: bindings_in_fragment.

(* An intersection, instantiated: the intersection of the instances of its components, which are
   class types, each of their common mutability *)
Lemma intersection_instance: forall cs, components_sfrag cs = true -> bound_in (Intersection cs) = true ->
    (forall c, In c cs -> is_nullable env (inst_nested b c) = false) ->
    inst_nested b (Intersection cs)
        = Intersection (map (with_mutability env (common_mutability (map (inst_nested b) cs))) (map (inst_nested b) cs))
    /\ class_components (map (with_mutability env (common_mutability (map (inst_nested b) cs))) (map (inst_nested b) cs)) = true
    /\ forall c, In c cs -> in_fragment env (inst_nested b c) = true
        /\ Model.is_subtype_of (common_mutability (map (inst_nested b) cs)) (mutability_of env (inst_nested b c)) = true.
Proof.
    intros cs Hcs Hb Hn. destruct (components_sfrag_facts cs Hcs) as [Hl Hc].
    assert (Hy: forall c, In c cs -> in_fragment env (inst_nested b c) = true /\ is_class (inst_nested b c) = true).
    { intros c Hin. destruct (Hc c Hin) as [_ Hs].
      pose proof (instance_in_fragment Hbf c Hs (bound_in_component cs c Hb Hin)) as Hf. split; [exact Hf|].
      pose proof (Hn c Hin) as Hn'.
      destruct (fragment_cases env _ Hf) as [[m [d [args Ed]]]|[m [d [args [Ed _]]]]]; rewrite Ed in Hn' |- *;
          [reflexivity|discriminate Hn']. }
    assert (Hys: forall y, In y (map (inst_nested b) cs) -> is_class y = true /\ in_fragment env y = true).
    { intros y Hin. apply in_map_iff in Hin. destruct Hin as [c [<- Hin]]. destruct (Hy c Hin) as [Hf Hcl]. split; assumption. }
    assert (Hly: 2 <= length (map (inst_nested b) cs)) by (rewrite length_map; exact Hl).
    destruct (of_classes _ Hly Hys) as [Heq Hcc].
    assert (Hmap: map (inst_component b) cs = map (inst_nested b) cs)
        by (apply map_ext_in; intros c Hin; apply inst_component_nested, (Hc c Hin)).
    split; [|split; [exact Hcc|]].
    - change (inst_nested b (Intersection cs)) with (inst_intersection b cs). unfold inst_intersection. rewrite Hmap. exact Heq.
    - intros c Hin. split; [apply Hy, Hin|]. eapply mutability_subtype_trans; [apply fold_intersect_below_element, in_map, in_map, Hin|apply (assignment_mutability_below env ranked)].
Qed.

(* Instantiated, a type is of cfrag, of no more mutability than it is, and non-null where it is *)
Lemma instance_facts: forall k t, sdepth t <= k -> tfrag t = true -> bound_in t = true ->
    cfrag (inst_nested b t) = true
    /\ Model.is_subtype_of (assignment_mutability env (inst_nested b t)) (assignment_mutability env t) = true
    /\ (is_nullable env t = false -> is_nullable env (inst_nested b t) = false).
Proof.
    induction k as [|k IH].
    { intros t Hd Ht _. destruct (tfrag_cases t Ht) as [Hs|[[cs [-> _]]|[cs [-> _]]]]; [|simpl in Hd; lia|simpl in Hd; lia].
      destruct (sfrag_cases t Hs) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
          first [pose proof (sdepth_generic g); lia|simpl in Hd; lia]. }
    (* an intersection *)
    assert (Hinter: forall cs, sdepth (Intersection cs) <= S k -> components_sfrag cs = true -> bound_in (Intersection cs) = true ->
        (exists ys, inst_nested b (Intersection cs) = Intersection ys /\ class_components ys = true)
        /\ Model.is_subtype_of (assignment_mutability env (inst_nested b (Intersection cs))) (assignment_mutability env (Intersection cs)) = true).
    { intros cs Hd Hcs Hb. destruct (components_sfrag_facts cs Hcs) as [_ Hc].
      assert (Hfacts: forall c, In c cs -> Model.is_subtype_of (assignment_mutability env (inst_nested b c)) (assignment_mutability env c) = true
          /\ is_nullable env (inst_nested b c) = false).
      { intros c Hin. destruct (Hc c Hin) as [Hsh Hs]. pose proof (sdepth_component cs c Hin) as Hdc.
        destruct (IH c ltac:(lia) (sfrag_tfrag c Hs) (bound_in_component cs c Hb Hin)) as [_ [Hm Hn]].
        split; [exact Hm|apply Hn, component_non_null, Hsh]. }
      destruct (intersection_instance cs Hcs Hb (fun c Hin => proj2 (Hfacts c Hin))) as [Heq [Hcc Hcomp]].
      rewrite Heq. split; [eexists; split; [reflexivity|exact Hcc]|].
      rewrite (intersection_assignment_mutability env cs). apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
      intros mc Hmc. apply in_map_iff in Hmc. destruct Hmc as [c [<- Hin]].
      destruct (Hcomp c Hin) as [Hf Hk]. destruct (Hfacts c Hin) as [Hm _].
      eapply mutability_subtype_trans; [apply intersection_assignment_mutability_below_component, in_map, in_map, Hin|].
      exact (mutability_subtype_trans _ _ _ (with_mutability_below _ _ Hf Hk) Hm). }
    (* a reference *)
    assert (Hgen: forall g, sdepth (Generic g) <= S k -> generic_sfrag g -> bound_in (Generic g) = true ->
        Model.is_subtype_of (assignment_mutability env (inst_nested b (Generic g))) (assignment_mutability env (Generic g)) = true
        /\ (is_nullable env (Generic g) = false -> is_nullable env (inst_nested b (Generic g)) = false)).
    { intros g Hd [Hf _] Hb. destruct (binds_ref_some g Hb) as [o [x [Ex [_ [_ [Hr Hbe]]]]]].
      pose proof (inst_ref_in_fragment g x (Hbf _ o x Ex)) as HI.
      assert (Hde: sdepth (effective_bound env g) <= k) by (rewrite sdepth_bound in Hd; lia).
      destruct (IH _ Hde Hf Hbe) as [HB [Hm Hn]].
      pose proof (respects_unify _ _ HI HB Hr) as Hra.
      rewrite (inst_nested_generic g _ o x Ex), mutability_generic, nullable_generic. split.
      - exact (mutability_subtype_trans _ _ _ (cfrag_mutability _ _ _ _ _ HB HI Hra) Hm).
      - intros Hn0. exact (cfrag_non_null _ _ _ _ _ HB HI (Hn Hn0) Hra). }
    intros t Hd Ht Hb. destruct (tfrag_cases t Ht) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - split; [apply in_fragment_cfrag, (instance_in_fragment Hbf t Hs Hb)|].
      destruct (sfrag_cases t Hs) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + split; [apply mutability_is_subtype_of_refl|intros _; reflexivity].
      + split; [apply mutability_is_subtype_of_refl|intros _; reflexivity].
      + split; [apply mutability_is_subtype_of_refl|intros H0; discriminate H0].
      + exact (Hgen g Hd Hg Hb).
      + destruct (binds_ref_some g Hb) as [o [x [Ex _]]]. pose proof (inst_ref_in_fragment g x (Hbf _ o x Ex)) as HI.
        rewrite (inst_nested_nullable_generic g _ o x Ex), (rewrap_without_null _ HI). split; [|intros H0; discriminate H0].
        change (Model.is_subtype_of (assignment_mutability env (without_null env (inst_ref g x))) (assignment_mutability env (Generic g)) = true).
        rewrite (assignment_mutability_of_without_null _ HI), <- (inst_nested_generic g _ o x Ex).
        exact (proj1 (Hgen g ltac:(change (S (sdepth (Generic g)) <= S k) in Hd; lia) Hg Hb)).
    - destruct (Hinter cs Hd Hcs Hb) as [[ys [Heq Hys]] Hm]. rewrite Heq in Hm |- *.
      split; [exact Hys|split; [exact Hm|intros _; reflexivity]].
    - destruct (Hinter cs ltac:(simpl in Hd |- *; lia) Hcs Hb) as [[ys [Heq Hys]] Hm].
      change (inst_nested b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested b (Intersection cs))).
      rewrite Heq in Hm |- *. split; [exact Hys|split; [exact Hm|intros H0; discriminate H0]].
Qed.

(* Made non-null, a type is bound in, and its instance is its instance made non-null *)
Lemma narrow_facts: forall k t, sdepth t <= k -> tfrag t = true -> bound_in t = true ->
    bound_in (without_null env t) = true /\ inst_nested b (without_null env t) = without_null env (inst_nested b t).
Proof.
    induction k as [|k IH].
    { intros t Hd Ht _. destruct (tfrag_cases t Ht) as [Hs|[[cs [-> _]]|[cs [-> _]]]]; [|simpl in Hd; lia|simpl in Hd; lia].
      destruct (sfrag_cases t Hs) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
          first [pose proof (sdepth_generic g); lia|simpl in Hd; lia]. }
    assert (Hgen: forall g, sdepth (Generic g) <= S k -> generic_sfrag g -> bound_in (Generic g) = true ->
        bound_in (Generic (narrow_ref g)) = true /\ inst_nested b (Generic (narrow_ref g)) = without_null env (inst_nested b (Generic g))).
    { intros g Hd [Hf [Hw Hv]] Hb. destruct (binds_ref_some g Hb) as [o [x [Ex [Ho [Hx [Hr Hbe]]]]]].
      pose proof (Hbf _ o x Ex) as HFx. pose proof (inst_ref_in_fragment g x HFx) as HI.
      destruct (instance_facts _ _ (le_n _) Hf Hbe) as [HB [_ HnB]].
      assert (Eeff: effective_bound env (narrow_ref g) = without_null env (effective_bound env g)).
      { destruct g as [gm nn p [|v vs]]; [|discriminate Hv]. exact (effective_bound_narrowed env ranked gm nn p). }
      assert (Hde: sdepth (effective_bound env g) <= k) by (rewrite sdepth_bound in Hd; lia).
      destruct (IH _ Hde Hf Hbe) as [Hbn Hin].
      (* the instance of the narrowed reference is that of the reference, made non-null *)
      assert (Hni: inst_ref (narrow_ref g) x = without_null env (inst_ref g x)).
      { pose proof (without_null_idempotent _ (inst_fit_in_fragment g x HFx)) as Hidem.
        pose proof (cfrag_non_null K _ _ s s HB HI) as Hacc. pose proof (respects_unify _ _ HI HB Hr) as Hra.
        unfold inst_ref in *. change (inst_fit (narrow_ref g) x) with (inst_fit g x). cbn [is_narrowed narrow_ref].
        rewrite <- nullable_generic in HnB.
        destruct (is_nullable env (Generic g)) eqn:En; destruct (is_narrowed g); cbn [orb];
            try (symmetry; exact Hidem); try reflexivity.
        symmetry. exact (without_null_non_null _ (inst_fit_in_fragment g x HFx) (Hacc (HnB eq_refl) Hra)). }
      split.
      - rewrite bound_in_generic, Eeff, Hbn, andb_true_r.
        unfold binds_ref. change (param_of (narrow_ref g)) with (param_of g). rewrite Eeff, Ex.
        change (is_exact_ownership o && gfrag env x
            && respects (inst_ref (narrow_ref g) x) (inst_nested b (without_null env (effective_bound env g))) = true).
        rewrite Ho, Hx, Hni, Hin. cbn [andb]. unfold respects in *.
        destruct (unify env K (inst_nested b (effective_bound env g)) (inst_ref g x) (Ongoing s)) as [[w|]|] eqn:Eu; try discriminate Hr.
        rewrite (cfrag_without_null K _ _ s w HB HI Eu). reflexivity.
      - rewrite (inst_nested_generic (narrow_ref g) _ o x Ex), (inst_nested_generic g _ o x Ex). exact Hni. }
    intros t Hd Ht Hb. destruct (tfrag_cases t Ht) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (sfrag_cases t Hs) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + split; [exact Hb|reflexivity].
      + split; reflexivity.
      + split; [exact Hb|reflexivity].
      + rewrite without_null_generic. exact (Hgen g Hd Hg Hb).
      + change (without_null env (Nullable (Generic g))) with (without_null env (Generic g)). rewrite without_null_generic.
        destruct (Hgen g ltac:(change (S (sdepth (Generic g)) <= S k) in Hd; lia) Hg Hb) as [Hbn Hin]. split; [exact Hbn|].
        rewrite Hin. destruct (binds_ref_some g Hb) as [o [x [Ex _]]].
        rewrite (inst_nested_generic g _ o x Ex), (inst_nested_nullable_generic g _ o x Ex).
        pose proof (inst_ref_in_fragment g x (Hbf _ o x Ex)) as HI. rewrite (rewrap_without_null _ HI).
        change (without_null env (Nullable (without_null env (inst_ref g x)))) with (without_null env (without_null env (inst_ref g x))).
        symmetry. apply without_null_idempotent, HI.
    - split; [exact Hb|]. destruct (instance_facts _ _ (le_n _) Ht Hb) as [HB [_ Hn]].
      change (without_null env (Intersection cs)) with (Intersection cs).
      symmetry. exact (cfrag_without_null_non_null _ HB (Hn eq_refl)).
    - change (without_null env (Nullable (Intersection cs))) with (Intersection cs). split; [exact Hb|].
      destruct (instance_facts _ (Intersection cs) (le_n _) Hcs Hb) as [HB [_ Hn]].
      change (inst_nested b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested b (Intersection cs))).
      rewrite without_null_rewrap. symmetry. exact (cfrag_without_null_non_null _ HB (Hn eq_refl)).
Qed.

Lemma narrow_generic: forall g, generic_sfrag g -> bound_in (Generic g) = true ->
    sfrag (Generic (narrow_ref g)) = true /\ bound_in (Generic (narrow_ref g)) = true
    /\ inst_nested b (Generic (narrow_ref g)) = without_null env (inst_nested b (Generic g)).
Proof.
    intros g Hg Hb. pose proof (sfrag_tfrag _ (generic_sfrag_sfrag g Hg)) as Hf.
    destruct (tfrag_without_null _ _ (le_n _) Hf) as [Hfn _]. destruct (narrow_facts _ _ (le_n _) Hf Hb) as [Hbn Hin].
    rewrite without_null_generic in Hfn, Hbn, Hin. repeat split; assumption.
Qed.

(* A reference to a type parameter bounded by an intersection, assigned to t: generically, t takes a
   component of the bound; so the instance of that component takes the type argument, and the
   instance of t takes the instance of the component *)
Lemma via_intersection: forall n F t cs u x,
    (forall t a u, sfrag t = true -> sfrag a = true -> bound_in t = true -> bound_in a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env F (inst_nested b t) (inst_nested b a) (Ongoing s) = Some (Ongoing s)) ->
    sfrag t = true -> bound_in t = true -> in_fragment env x = true ->
    components_sfrag cs = true -> bound_in (Intersection cs) = true ->
    (unify env n t (Intersection cs) (Ongoing s) = Some (Ongoing u)
        /\ unify env K (inst_nested b (Intersection cs)) x (Ongoing s) = Some (Ongoing s))
    \/ (unify env n t (Nullable (Intersection cs)) (Ongoing s) = Some (Ongoing u)
        /\ unify env K (inst_nested b (Nullable (Intersection cs))) x (Ongoing s) = Some (Ongoing s)) ->
    u = s /\ unify env (S (K + F)) (inst_nested b t) x (Ongoing s) = Some (Ongoing s).
Proof.
    intros n F t cs u x IH Ht Hbt Hx Hcs Hb Hcase. destruct (components_sfrag_facts cs Hcs) as [_ Hc].
    assert (Hn: forall c, In c cs -> is_nullable env (inst_nested b c) = false).
    { intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      apply (proj2 (proj2 (instance_facts _ c (le_n _) (sfrag_tfrag c Hs) (bound_in_component cs c Hb Hin)))).
      apply component_non_null, Hsh. }
    destruct (intersection_instance cs Hcs Hb Hn) as [Heq [Hcc Hcomp]].
    pose proof (in_fragment_without_null x Hx) as Hxn.
    (* the instance of each component takes x without null *)
    assert (Hx': exists K', K' <= K /\ (forall c, In c cs -> unify env K' (inst_nested b c) (without_null env x) (Ongoing s) = Some (Ongoing s))
        /\ ((unify env n t (Intersection cs) (Ongoing s) = Some (Ongoing u) /\ without_null env x = x)
            \/ unify env n t (Nullable (Intersection cs)) (Ongoing s) = Some (Ongoing u))).
    { destruct Hcase as [[Hu Hk]|[Hu Hk]].
      - rewrite Heq in Hk. destruct K as [|K']; [discriminate Hk|].
        destruct (inter_accepts K' _ x s s Hcc Hx Hk) as [_ [Hnx Hall]].
        rewrite (without_null_non_null x Hx Hnx). exists K'. split; [lia|]. split; [|left; split; [exact Hu|reflexivity]].
        intros c Hin. destruct (Hcomp c Hin) as [Hf Hm].
        exact (with_mutability_accepts K' _ _ x s s Hf Hx Hm (Hall _ (in_map _ _ _ (in_map _ _ _ Hin)))).
      - change (inst_nested b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested b (Intersection cs))) in Hk.
        rewrite Heq in Hk. cbn [rewrap_nullable] in Hk.
        destruct K as [|K']; [discriminate Hk|]. rewrite unify_nullable_target in Hk by exact Hx.
        destruct K' as [|K'']; [discriminate Hk|].
        destruct (inter_accepts K'' _ _ s s Hcc Hxn Hk) as [_ [_ Hall]].
        exists K''. split; [lia|]. split; [|right; exact Hu].
        intros c Hin. destruct (Hcomp c Hin) as [Hf Hm].
        exact (with_mutability_accepts K'' _ _ _ s s Hf Hxn Hm (Hall _ (in_map _ _ _ (in_map _ _ _ Hin)))). }
    destruct Hx' as [K' [HK' [Hall Hcase']]].
    (* the component that t takes, generically *)
    assert (Hgen: exists c, In c cs /\ (
        (unify env n t c (Ongoing s) = Some (Ongoing u) /\ without_null env x = x)
        \/ exists t0, t = Nullable t0 /\ sfrag t0 = true /\ unify env n t0 c (Ongoing s) = Some (Ongoing u))).
    { destruct Hcase' as [[Hu Hwx]|Hu]; destruct n as [|n']; try discriminate Hu.
      - destruct (sfrag_cases t Ht) as [[m [ct [args [-> _]]]]|[->|[[m [ct [args [-> Ht0]]]]|[[g [-> _]]|[g [-> Hg]]]]]].
        + destruct (unify_into_components n' _ cs s u Hu eq_refl) as [c [Hin Hi]].
          exists c. split; [exact Hin|left; split; [|exact Hwx]]. apply (unify_fuel_monotone env n'); [lia|exact Hi].
        + destruct (unify_into_components n' _ cs s u Hu eq_refl) as [c [Hin Hi]].
          exists c. split; [exact Hin|left; split; [|exact Hwx]]. apply (unify_fuel_monotone env n'); [lia|exact Hi].
        + change (unify env (S n') (Nullable (RootResolved m ct args)) (Intersection cs) (Ongoing s))
              with (unify env n' (RootResolved m ct args) (Intersection cs) (Ongoing s)) in Hu.
          destruct n' as [|n'']; [discriminate Hu|].
          destruct (unify_into_components n'' _ cs s u Hu eq_refl) as [c [Hin Hi]].
          exists c. split; [exact Hin|right]. exists (RootResolved m ct args). split; [reflexivity|split; [exact Ht0|]].
          apply (unify_fuel_monotone env n''); [lia|exact Hi].
        + destruct (unify_into_components n' _ cs s u Hu eq_refl) as [c [Hin Hi]].
          exists c. split; [exact Hin|left; split; [|exact Hwx]]. apply (unify_fuel_monotone env n'); [lia|exact Hi].
        + change (unify env (S n') (Nullable (Generic g)) (Intersection cs) (Ongoing s))
              with (unify env n' (Generic g) (Intersection cs) (Ongoing s)) in Hu.
          destruct n' as [|n'']; [discriminate Hu|].
          destruct (unify_into_components n'' _ cs s u Hu eq_refl) as [c [Hin Hi]].
          exists c. split; [exact Hin|right]. exists (Generic g). split; [reflexivity|split; [exact (generic_sfrag_sfrag g Hg)|]].
          apply (unify_fuel_monotone env n''); [lia|exact Hi].
      - destruct (sfrag_cases t Ht) as [[m [ct [args [-> _]]]]|[->|[[m [ct [args [-> Ht0]]]]|[[g [-> _]]|[g [-> Hg]]]]]].
        + rewrite unify_class_nullable in Hu. discriminate Hu.
        + unfold bottom_type in Hu. rewrite unify_class_nullable in Hu. discriminate Hu.
        + rewrite unify_nullable_nullable in Hu. destruct n' as [|n'']; [discriminate Hu|].
          destruct (unify_into_components n'' _ cs s u Hu eq_refl) as [c [Hin Hi]].
          exists c. split; [exact Hin|right]. exists (RootResolved m ct args). split; [reflexivity|split; [exact Ht0|]].
          apply (unify_fuel_monotone env n''); [lia|exact Hi].
        + rewrite unify_generic_nullable in Hu. discriminate Hu.
        + rewrite unify_nullable_nullable in Hu. destruct n' as [|n'']; [discriminate Hu|].
          destruct (unify_into_components n'' _ cs s u Hu eq_refl) as [c [Hin Hi]].
          exists c. split; [exact Hin|right]. exists (Generic g). split; [reflexivity|split; [exact (generic_sfrag_sfrag g Hg)|]].
          apply (unify_fuel_monotone env n''); [lia|exact Hi]. }
    destruct Hgen as [c [Hin [[Hu Hwx]|[t0 [-> [Hs0 Hu]]]]]]; destruct (Hc c Hin) as [_ Hsc].
    - destruct (IH t c u Ht Hsc Hbt (bound_in_component cs c Hb Hin) Hu) as [-> Hi]. split; [reflexivity|].
      pose proof (Hall c Hin) as Hcx. rewrite Hwx in Hcx.
      apply (unify_fuel_monotone env (K' + F)); [lia|].
      apply (proj1 (transitivity_with_arguments env wf (K' + F)) x (inst_nested b c) (inst_nested b t) K' F s (le_n _));
          [exact Hx|exact (proj1 (Hcomp c Hin))|exact (instance_in_fragment Hbf t Ht Hbt)|exact Hcx|exact Hi].
    - change (bound_in (Nullable t0)) with (bound_in t0) in Hbt.
      destruct (IH t0 c u Hs0 Hsc Hbt (bound_in_component cs c Hb Hin) Hu) as [-> Hi]. split; [reflexivity|].
      pose proof (instance_in_fragment Hbf t0 Hs0 Hbt) as HT0.
      assert (Ht0: unify env (K' + F) (inst_nested b t0) (without_null env x) (Ongoing s) = Some (Ongoing s))
          by (apply (proj1 (transitivity_with_arguments env wf (K' + F)) _ (inst_nested b c) _ K' F s (le_n _));
              [exact Hxn|exact (proj1 (Hcomp c Hin))|exact HT0|exact (Hall c Hin)|exact Hi]).
      apply (unify_fuel_monotone env (S (K' + F))); [lia|].
      (* the nullable type is a nullable class type or reference *)
      destruct (sfrag_cases _ Ht) as [[? [? [? [Et _]]]]|[Et|[[mt [ct [targs [Et _]]]]|[[g [Et _]]|[g [Et Hg]]]]]];
          try discriminate Et; injection Et as ->.
      + change (inst_nested b (Nullable (RootResolved mt ct targs))) with (Nullable (inst_nested b (RootResolved mt ct targs))).
        apply unify_into_nullable; [exact Hx|exact Ht0].
      + destruct (binds_ref_some g Hbt) as [o [x0 [Ex _]]]. rewrite (inst_nested_nullable_generic g _ o x0 Ex).
        rewrite (inst_nested_generic g _ o x0 Ex) in Ht0.
        pose proof (inst_ref_in_fragment g x0 (Hbf _ o x0 Ex)) as HIg. rewrite (rewrap_without_null _ HIg).
        apply unify_into_nullable; [exact Hx|].
        rewrite <- (without_null_idempotent x Hx). exact (unify_without_null _ _ _ s s HIg Hxn Ht0).
Qed.

End Instances.

Section Main.

(* The fuel it takes to unify a type argument of the bindings with itself, and one to spare *)
Variable E: nat.
Hypothesis HE2: 2 <= E.
Hypothesis HE: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> depth x <= E.
Hypothesis Hbf: bindings_in_fragment.

Lemma substitution_with_arguments: forall n,
    (forall t a u, sfrag t = true -> sfrag a = true -> bound_in t = true -> bound_in a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + E) (inst_nested b t) (inst_nested b a) (Ongoing s) = Some (Ongoing s))
    /\ (forall t a u, argument_sfrag t = true -> argument_sfrag a = true -> bound_in t = true -> bound_in a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + E) (instantiate env b t) (instantiate env b a) (Ongoing s) = Some (Ongoing s)).
Proof.
    induction n as [|n [IHt IHa]].
    { split; intros t a u _ _ _ _ H; discriminate H. }
    rewrite Nat.mul_succ_l. remember (n * S (S K)) as P eqn:HP. clear HP.
    replace (P + S (S K) + E) with (S (P + E + S K)) by lia.
    split.
    - intros t a u Ht Ha Hbt Hba H.
      (* a type parameter assigned to a type: its instance is assignable to its bound *)
      assert (Hvia: forall ga, generic_sfrag ga -> bound_in (Generic ga) = true ->
          unify env n t (effective_bound env ga) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (P + E + S K)) (inst_nested b t) (inst_nested b (Generic ga)) (Ongoing s) = Some (Ongoing s)).
      { intros ga [Hfb _] Hbq Hu.
        destruct (binds_ref_some ga Hbq) as [o [x [Ex [_ [_ [Hr Hbe]]]]]]. pose proof (Hbf _ o x Ex) as Hx.
        pose proof (inst_ref_in_fragment ga x Hx) as HI. destruct (instance_facts Hbf _ _ (le_n _) Hfb Hbe) as [HTb _].
        pose proof (respects_unify _ _ HI HTb Hr) as Hra.
        rewrite (inst_nested_generic ga _ o x Ex).
        destruct (tfrag_cases _ Hfb) as [Hsb|[[cs [Eb Hcs]]|[cs [Eb Hcs]]]].
        - destruct (IHt t _ u Ht Hsb Hbt Hbe Hu) as [-> Hi]. split; [reflexivity|].
          apply (unify_fuel_monotone env (K + (P + E))); [lia|].
          apply (proj1 (transitivity_with_arguments env wf (K + (P + E)))
              (inst_ref ga x) (inst_nested b (effective_bound env ga)) (inst_nested b t) K (P + E) s (le_n _));
              [exact HI|exact (instance_in_fragment Hbf _ Hsb Hbe)|exact (instance_in_fragment Hbf t Ht Hbt)|exact Hra|exact Hi].
        (* bounded by an intersection *)
        - rewrite Eb in Hu, Hra, Hbe.
          destruct (via_intersection Hbf n (P + E) t cs u _ IHt Ht Hbt HI Hcs Hbe (or_introl (conj Hu Hra))) as [-> Hi].
          split; [reflexivity|]. apply (unify_fuel_monotone env (S (K + (P + E)))); [lia|exact Hi].
        - rewrite Eb in Hu, Hra, Hbe.
          destruct (via_intersection Hbf n (P + E) t cs u _ IHt Ht Hbt HI Hcs Hbe (or_intror (conj Hu Hra))) as [-> Hi].
          split; [reflexivity|]. apply (unify_fuel_monotone env (S (K + (P + E)))); [lia|exact Hi]. }
      (* two class types *)
      assert (Hroot: forall mt ct targs ma ca aargs,
          sfrag (RootResolved mt ct targs) = true -> sfrag (RootResolved ma ca aargs) = true ->
          bound_in (RootResolved mt ct targs) = true -> bound_in (RootResolved ma ca aargs) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (P + E + S K)) (RootResolved mt ct (map (instantiate env b) targs))
              (RootResolved ma ca (map (instantiate env b) aargs)) (Ongoing s) = Some (Ongoing s)).
      { intros mt ct targs ma ca aargs Hft Hfa Hbt' Hba' Hu.
        rewrite unify_classes in Hu |- *.
        rewrite (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs),
            (assignment_mutability_of_class env ma ca (map (instantiate env b) aargs) aargs).
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _); [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn; [injection Hu as <-; auto|].
        destruct (sfrag_cases _ Hfa) as [[ma' [ca' [aargs' [Heq [_ [Hla Haargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
            try discriminate Heq;
            [injection Heq as <- <- <-|unfold bottom_type in Heq; injection Heq as _ -> _; rewrite class_eqb_refl in Hcn; discriminate Hcn].
        assert (Htargs: forall a, In a targs -> argument_sfrag a = true).
        { destruct (sfrag_cases _ Hft) as [[mt' [ct' [targs' [Heq [_ [_ Htargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
              try discriminate Heq.
          - injection Heq as <- <- <-. exact Htargs.
          - unfold bottom_type in Heq. injection Heq as _ _ ->. intros a0 []. }
        unfold unify_arguments in Hu |- *.
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        - rewrite class_eqb_refl in Hu |- *.
          apply (fold_pairs n (P + E + S K) targs aargs u Hu).
          intros t' a' u0 Ht' Ha' E'.
          destruct (IHa t' a' u0 (Htargs t' Ht') (Haargs a' Ha') (bound_in_root _ _ _ Hbt' t' Ht') (bound_in_root _ _ _ Hba' a' Ha') E')
              as [-> Hi].
          split; [reflexivity|]. apply (unify_fuel_monotone env (P + E)); [lia|exact Hi].
        - rewrite (class_eqb_false _ _ Hne) in Hu |- *.
          assert (Hys: forall y, In y aargs -> argument_sfrag y = true /\ bound_in y = true)
              by (intros y Hy; split; [apply Haargs, Hy|apply (bound_in_root _ _ _ Hba' y Hy)]).
          destruct (supertype_arguments_commute ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Hys) as [Hcomm Hnorm].
          rewrite Hcomm.
          apply (fold_pairs n (P + E + S K) targs _ u Hu).
          intros t' a' u0 Ht' Ha' E'. destruct (Hnorm a' Ha') as [Hfa' Hba''].
          destruct (IHa t' a' u0 (Htargs t' Ht') Hfa' (bound_in_root _ _ _ Hbt' t' Ht') Hba'' E') as [-> Hi].
          split; [reflexivity|]. apply (unify_fuel_monotone env (P + E)); [lia|exact Hi]. }
      destruct (sfrag_cases t Ht) as [[mt [ct [targs [-> _]]]]|[->|[[mt [ct [targs [-> Ht']]]]|[[gt [-> Hgt]]|[gt [-> Hgt]]]]]];
      destruct (sfrag_cases a Ha) as [[ma [ca [aargs [-> [Hca _]]]]]|[->|[[ma [ca [aargs [-> Ha']]]]|[[ga [-> Hga]]|[ga [-> Hga]]]]]];
          unfold bottom_type in *.
      (* a class type: of a class type, or of a type parameter by its bound *)
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_root_generic in H. exact (Hvia ga Hga Hba H).
      + rewrite unify_class_nullable in H. discriminate H.
      (* Nothing *)
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_root_generic in H. exact (Hvia ga Hga Hba H).
      + rewrite unify_class_nullable in H. discriminate H.
      (* a nullable class type *)
      + rewrite unify_nullable_class in H. destruct (IHt _ _ u Ht' Ha Hbt Hba H) as [-> Hi]. split; [reflexivity|].
        change (inst_nested b (Nullable (RootResolved mt ct targs))) with (instantiate env b (Nullable (RootResolved mt ct targs))).
        rewrite instantiate_nullable_class.
        change (inst_nested b (RootResolved ma ca aargs)) with (RootResolved ma ca (map (instantiate env b) aargs)).
        rewrite unify_nullable_class. apply (unify_fuel_monotone env (P + E)); [lia|exact Hi].
      + rewrite unify_nullable_class in H. destruct (IHt _ _ u Ht' Ha Hbt Hba H) as [-> Hi]. split; [reflexivity|].
        change (inst_nested b (Nullable (RootResolved mt ct targs))) with (instantiate env b (Nullable (RootResolved mt ct targs))).
        rewrite instantiate_nullable_class.
        change (inst_nested b (RootResolved (Some exclusive) nothing [])) with (RootResolved (Some exclusive) nothing (@nil EType)).
        rewrite unify_nullable_class. apply (unify_fuel_monotone env (P + E)); [lia|exact Hi].
      + rewrite unify_nullable_nullable in H. destruct (IHt _ _ u Ht' Ha' Hbt Hba H) as [-> Hi]. split; [reflexivity|].
        change (inst_nested b (Nullable (RootResolved mt ct targs))) with (instantiate env b (Nullable (RootResolved mt ct targs))).
        change (inst_nested b (Nullable (RootResolved ma ca aargs))) with (instantiate env b (Nullable (RootResolved ma ca aargs))).
        rewrite !instantiate_nullable_class, unify_nullable_nullable. apply (unify_fuel_monotone env (P + E)); [lia|exact Hi].
      + rewrite unify_nullable_generic_step in H. destruct (narrow_generic Hbf ga Hga Hba) as [Hfn [Hbn Hin]].
        destruct (IHt _ _ u Ht' Hfn Hbt Hbn H) as [-> Hi]. split; [reflexivity|]. rewrite Hin in Hi.
        change (inst_nested b (Nullable (RootResolved mt ct targs))) with (Nullable (inst_nested b (RootResolved mt ct targs))).
        apply unify_into_nullable; [exact (instance_in_fragment Hbf _ Ha Hba)|].
        apply (unify_fuel_monotone env (P + E)); [lia|exact Hi].
      + rewrite unify_nullable_nullable in H. destruct (binds_ref_some ga Hba) as [o [x [Ex _]]].
        destruct (IHt _ _ u Ht' (generic_sfrag_sfrag ga Hga) Hbt Hba H) as [-> Hi]. split; [reflexivity|].
        rewrite (inst_nested_generic ga _ o x Ex) in Hi. rewrite (inst_nested_nullable_generic ga _ o x Ex).
        change (inst_nested b (Nullable (RootResolved mt ct targs))) with (rewrap_nullable (inst_nested b (RootResolved mt ct targs))).
        apply (unify_fuel_monotone env (S (P + E))); [lia|].
        apply unify_rewrap; [exact (instance_in_fragment Hbf _ Ht' Hbt)|apply inst_ref_in_fragment, (Hbf _ o x Ex)|exact Hi].
      (* a type parameter: of Nothing, or of a reference to a type parameter *)
      + rewrite unify_generic_root, Hca in H. cbn [andb] in H. discriminate H.
      + rewrite unify_generic_root, class_eqb_refl in H. cbn [andb] in H.
        destruct (Model.is_subtype_of _ _); [|discriminate H]. injection H as <-. split; [reflexivity|].
        destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]]. rewrite (inst_nested_generic gt _ o x Ex).
        apply below_all; [apply inst_ref_in_fragment, (Hbf _ o x Ex)|lia].
      + rewrite unify_generic_nullable in H. discriminate H.
      + rewrite unify_generic_generic_step in H. destruct (param_eqb (param_of ga) (param_of gt)) eqn:Ep.
        * (* the same type parameter: the instances are ordered as the bounds are *)
          apply param_eqb_eq in Ep. destruct (_ && _) eqn:Ec in H; [|discriminate H]. injection H as <-.
          split; [reflexivity|]. apply andb_true_iff in Ec. destruct Ec as [Hm Hn].
          destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]].
          destruct (binds_ref_some ga Hba) as [o' [x' [Ea [_ [_ [Hra Hbe]]]]]].
          rewrite Ep, Ex in Ea. injection Ea as <- <-.
          pose proof (Hbf _ o x Ex) as Hx. pose proof (proj1 Hga) as Hfa.
          destruct (instance_facts Hbf _ _ (le_n _) Hfa Hbe) as [HB [HmB HnB]].
          rewrite (inst_nested_generic gt _ o x Ex), (inst_nested_generic ga _ o x (eq_trans (f_equal (lookup_binding b) Ep) Ex)).
          apply (unify_fuel_monotone env E); [lia|].
          apply (same_parameter E gt ga x _ Hx HB); [|exact Hgt| |exact HmB|exact HnB|exact Hm|exact Hn].
          -- apply (proj1 (reflexivity_with_arguments env E)); [exact Hx|exact (HE _ o x Ex)].
          -- apply respects_unify; [apply inst_ref_in_fragment, Hx|exact HB|exact Hra].
        * (* another one: by the bound of the assignee *)
          exact (Hvia ga Hga Hba H).
      + rewrite unify_generic_nullable in H. discriminate H.
      (* a nullable type parameter: the same, and what is nullable of it *)
      + rewrite unify_nullable_class in H. destruct n as [|n']; [discriminate H|].
        rewrite unify_generic_root, Hca in H. cbn [andb] in H. discriminate H.
      + rewrite unify_nullable_class in H. destruct n as [|n']; [discriminate H|].
        rewrite unify_generic_root, class_eqb_refl in H. cbn [andb] in H.
        destruct (Model.is_subtype_of _ _); [|discriminate H]. injection H as <-. split; [reflexivity|].
        destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]]. rewrite (inst_nested_nullable_generic gt _ o x Ex).
        apply below_all; [apply in_fragment_rewrap, inst_ref_in_fragment, (Hbf _ o x Ex)|lia].
      + rewrite unify_nullable_nullable in H. destruct n as [|n']; [discriminate H|].
        rewrite unify_generic_root in H. destruct (class_eqb ca nothing) eqn:Hcn; [|discriminate H]. cbn [andb] in H.
        destruct (Model.is_subtype_of _ _); [|discriminate H]. injection H as <-. split; [reflexivity|].
        apply class_eqb_true in Hcn. subst ca. simpl in Ha'. destruct ma as [[]|], aargs; simpl in Ha'; try discriminate Ha'.
        destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]]. rewrite (inst_nested_nullable_generic gt _ o x Ex).
        pose proof (inst_ref_in_fragment gt x (Hbf _ o x Ex)) as HI. rewrite (rewrap_without_null _ HI).
        change (inst_nested b (Nullable (RootResolved (Some exclusive) nothing []))) with (Nullable bottom_type).
        rewrite unify_nullable_nullable. apply below_all; [apply in_fragment_without_null, HI|lia].
      + rewrite unify_nullable_generic_step in H. destruct (narrow_generic Hbf ga Hga Hba) as [Hfn [Hbn Hin]].
        destruct (IHt _ _ u (generic_sfrag_sfrag gt Hgt) Hfn Hbt Hbn H) as [-> Hi]. split; [reflexivity|].
        rewrite Hin in Hi. destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]].
        pose proof (inst_ref_in_fragment gt x (Hbf _ o x Ex)) as HIt. pose proof (instance_in_fragment Hbf _ Ha Hba) as HIa.
        rewrite (inst_nested_generic gt _ o x Ex) in Hi. rewrite (inst_nested_nullable_generic gt _ o x Ex).
        rewrite (rewrap_without_null _ HIt). apply unify_into_nullable; [exact HIa|].
        pose proof (unify_without_null _ _ _ s s HIt (in_fragment_without_null _ HIa) Hi) as Hi'.
        rewrite (without_null_idempotent _ HIa) in Hi'.
        apply (unify_fuel_monotone env (P + E)); [lia|exact Hi'].
      + rewrite unify_nullable_nullable in H.
        destruct (IHt _ _ u (generic_sfrag_sfrag gt Hgt) (generic_sfrag_sfrag ga Hga) Hbt Hba H) as [-> Hi]. split; [reflexivity|].
        destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]]. destruct (binds_ref_some ga Hba) as [o' [x' [Ea _]]].
        rewrite (inst_nested_generic gt _ o x Ex), (inst_nested_generic ga _ o' x' Ea) in Hi.
        rewrite (inst_nested_nullable_generic gt _ o x Ex), (inst_nested_nullable_generic ga _ o' x' Ea).
        apply (unify_fuel_monotone env (S (P + E))); [lia|].
        apply unify_rewrap; [apply inst_ref_in_fragment, (Hbf _ o x Ex)|apply inst_ref_in_fragment, (Hbf _ o' x' Ea)|exact Hi].
    - intros [| | | |vt ot nt| |] [| | | |va oa na| |] u Ht Ha Hbt Hba H; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha.
      destruct (bound_in_argument vt ot nt Hbt) as [_ Hbnt]. destruct (bound_in_argument va oa na Hba) as [_ Hbna].
      rewrite (instantiate_bound_argument vt ot nt Ht Hbnt), (instantiate_bound_argument va oa na Ha Hbna).
      rewrite unify_type_arguments in H |- * by first
          [ apply (fragment_not_variable env); apply instance_in_fragment; assumption
          | destruct (sfrag_cases nt Ht) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[? [-> _]]|[? [-> _]]]]]]; reflexivity ].
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      rewrite (instantiation_preserves_ownership_assignability b oa ot Ho).
      destruct (proj1 (closed_facts (sdepth top_type)) top_type (le_n _) top_in_sfrag eq_refl) as [_ [Hitop [Hbtop _]]].
      destruct vt, va; unfold compare_variances in H |- *; try discriminate H.
      1: { (* both ways *)
        destruct (unify env n nt na (Ongoing s)) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
        destruct (IHt nt na w Ht Ha Hbnt Hbna E1) as [-> Hi1].
        destruct (IHt na nt u Ha Ht Hbna Hbnt H) as [-> Hi2].
        split; [reflexivity|].
        rewrite (unify_fuel_monotone env (P + E) (P + E + S K) _ _ _ _ ltac:(lia) Hi1).
        apply (unify_fuel_monotone env (P + E)); [lia|exact Hi2]. }
      all: first
          [ destruct (IHt nt na u Ht Ha Hbnt Hbna H) as [-> Hi]
          | destruct (IHt na nt u Ha Ht Hbna Hbnt H) as [-> Hi]
          | destruct (IHt nt top_type u Ht top_in_sfrag Hbnt Hbtop H) as [-> Hi];
            change (inst_nested b top_type) with (instantiate env b top_type) in Hi; rewrite Hitop in Hi
          | destruct (IHt bottom_type nt u bottom_in_sfrag Ht eq_refl Hbnt H) as [-> Hi];
            change (inst_nested b bottom_type) with bottom_type in Hi ];
          split; [reflexivity|]; apply (unify_fuel_monotone env (P + E)); [lia|exact Hi].
Qed.

(* An intersection as the target: each component takes the assignee, and so each instance of a
   component takes the instance of the assignee, also of their common mutability *)
Lemma substitution_into_intersection: forall n cs a u, components_sfrag cs = true -> sfrag a = true ->
    bound_in (Intersection cs) = true -> bound_in a = true ->
    unify env (S n) (Intersection cs) a (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (S (n * S (S K) + E)) (inst_nested b (Intersection cs)) (inst_nested b a) (Ongoing s) = Some (Ongoing s).
Proof.
    intros n cs a u Hcs Ha Hb Hba H. destruct (components_sfrag_facts cs Hcs) as [Hl Hc].
    pose proof (proj1 (substitution_with_arguments n)) as IH.
    assert (Hnv: forall c, In c cs -> is_type_variable c = false).
    { intros c Hin. destruct (Hc c Hin) as [Hsh _]. destruct c; first [reflexivity|discriminate Hsh]. }
    assert (Hne: cs <> []) by (intros ->; simpl in Hl; lia).
    (* a possibly null value is no intersection's *)
    assert (Hshape: match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end).
    { destruct (sfrag_cases a Ha) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[? [-> _]]|[? [-> _]]]]]];
          first [exact I|simpl in H; discriminate H]. }
    assert (Hk: forall c u', In c cs -> unify env n c a (Ongoing s) = Some (Ongoing u') -> u' = s)
        by (intros c u' Hin E'; exact (proj1 (IH c a u' (proj2 (Hc c Hin)) Ha (bound_in_component cs c Hb Hin) Hba E'))).
    destruct (intersection_target n cs a s u Hnv Hne Hshape Hk H) as [-> Hall]. split; [reflexivity|].
    (* the instances *)
    assert (Hinst: forall c, In c cs ->
        unify env (n * S (S K) + E) (inst_nested b c) (inst_nested b a) (Ongoing s) = Some (Ongoing s))
        by (intros c Hin; exact (proj2 (IH c a s (proj2 (Hc c Hin)) Ha (bound_in_component cs c Hb Hin) Hba (Hall c Hin)))).
    assert (Hn: forall c, In c cs -> is_nullable env (inst_nested b c) = false).
    { intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      apply (proj2 (proj2 (instance_facts Hbf _ c (le_n _) (sfrag_tfrag c Hs) (bound_in_component cs c Hb Hin)))).
      apply component_non_null, Hsh. }
    destruct (intersection_instance Hbf cs Hcs Hb Hn) as [Heq [Hcc Hcomp]]. rewrite Heq.
    pose proof (instance_in_fragment Hbf a Ha Hba) as HA.
    assert (HnA: is_nullable env (inst_nested b a) = false).
    { destruct cs as [|c1 cs']; [exfalso; exact (Hne eq_refl)|].
      exact (accepted_non_null _ _ _ _ _ (proj1 (Hcomp c1 (or_introl eq_refl))) HA (Hn c1 (or_introl eq_refl))
          (Hinst c1 (or_introl eq_refl))). }
    apply inter_takes; [exact Hcc|exact HA|exact HnA|].
    intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]].
    apply accepts_with_mutability; [exact (proj1 (Hcomp c Hin))|exact HA| |exact (Hinst c Hin)].
    apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
    intros m Hm. apply in_map_iff in Hm. destruct Hm as [y [<- Hy]]. apply in_map_iff in Hy. destruct Hy as [c' [<- Hin']].
    exact (accepted_mutability_classes _ _ _ _ _ (proj1 (Hcomp c' Hin')) HA (Hinst c' Hin')).
Qed.

(* A nullable intersection as the target: the intersection takes the assignee, without null *)
Lemma substitution_into_nullable_intersection: forall n cs a u, components_sfrag cs = true -> sfrag a = true ->
    bound_in (Intersection cs) = true -> bound_in a = true ->
    unify env (S n) (Nullable (Intersection cs)) a (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (S (n * S (S K) + E)) (inst_nested b (Nullable (Intersection cs))) (inst_nested b a) (Ongoing s)
        = Some (Ongoing s).
Proof.
    intros n cs a u Hcs Ha Hb Hba H. destruct (components_sfrag_facts cs Hcs) as [_ Hc].
    assert (Hn: forall c, In c cs -> is_nullable env (inst_nested b c) = false).
    { intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      apply (proj2 (proj2 (instance_facts Hbf _ c (le_n _) (sfrag_tfrag c Hs) (bound_in_component cs c Hb Hin)))).
      apply component_non_null, Hsh. }
    destruct (intersection_instance Hbf cs Hcs Hb Hn) as [Heq [Hcc _]].
    pose proof (instance_in_fragment Hbf a Ha Hba) as HA.
    change (inst_nested b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested b (Intersection cs))).
    rewrite Heq. cbn [rewrap_nullable]. rewrite unify_nullable_target by exact HA.
    assert (HI: cfrag (inst_nested b (Intersection cs)) = true) by (rewrite Heq; exact Hcc).
    (* the intersection takes what a is, without null *)
    assert (Hinto: forall a0, sfrag a0 = true -> bound_in a0 = true -> without_null env (inst_nested b a) = inst_nested b a0 ->
        unify env n (Intersection cs) a0 (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + E) (Intersection (map (with_mutability env (common_mutability (map (inst_nested b) cs)))
            (map (inst_nested b) cs))) (without_null env (inst_nested b a)) (Ongoing s) = Some (Ongoing s)).
    { intros a0 Ha0 Hb0 Ew H0. destruct n as [|n']; [discriminate H0|].
      destruct (substitution_into_intersection n' cs a0 u Hcs Ha0 Hb Hb0 H0) as [-> Hi]. split; [reflexivity|].
      rewrite Ew, <- Heq. apply (unify_fuel_monotone env (S (n' * S (S K) + E))); [simpl; lia|exact Hi]. }
    destruct (sfrag_cases a Ha) as [[ma [ca [aargs [-> _]]]]|[->|[[ma [ca [aargs [-> Ha']]]]|[[ga [-> Hga]]|[ga [-> Hga]]]]]];
        unfold bottom_type in *.
    - rewrite unify_nullable_class in H. exact (Hinto _ Ha Hba eq_refl H).
    - rewrite unify_nullable_class in H. exact (Hinto _ Ha Hba eq_refl H).
    - rewrite unify_nullable_nullable in H. exact (Hinto _ Ha' Hba eq_refl H).
    - rewrite unify_nullable_generic_step in H. destruct (narrow_generic Hbf ga Hga Hba) as [Hfn [Hbn Hin]].
      exact (Hinto _ Hfn Hbn (eq_sym Hin) H).
    - rewrite unify_nullable_nullable in H. destruct (binds_ref_some ga Hba) as [o [x [Ex _]]].
      pose proof (inst_ref_in_fragment ga x (Hbf _ o x Ex)) as HIg.
      destruct n as [|n']; [discriminate H|].
      destruct (substitution_into_intersection n' cs (Generic ga) u Hcs (generic_sfrag_sfrag ga Hga) Hb Hba H) as [-> Hi].
      split; [reflexivity|]. rewrite (inst_nested_nullable_generic ga _ o x Ex), without_null_rewrap.
      rewrite (inst_nested_generic ga _ o x Ex) in Hi. rewrite Heq in HI, Hi.
      apply (unify_fuel_monotone env (S (n' * S (S K) + E))); [simpl; lia|].
      exact (cfrag_without_null _ _ _ s s HI HIg Hi).
Qed.

End Main.

End Bindings.

(*
 * The substitution lemma: within the fragment, a type that is assignable to another stays so, with
 * the type parameters in both instantiated exactly, the instances of the references within their
 * bounds (with fuel K). The fuel it takes grows by the fuel the bounds take, and by the depth of the
 * type arguments (E).
 *)
Theorem substitution_lemma: forall b K E fuel t a,
    2 <= E -> (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> depth x <= E) ->
    bindings_in_fragment b ->
    tfrag t = true -> sfrag a = true -> bound_in b K [] t = true -> bound_in b K [] a = true ->
    is_assignable_to env fuel a t = Some true ->
    is_assignable_to env (fuel * S (S K) + E) (instantiate env b a) (instantiate env b t) = Some true.
Proof.
    intros b K E fuel t a HE2 HE Hbf Ht Ha Hbt Hba H.
    rewrite <- (inst_nested_instantiate b K [] t Ht Hbt), <- (inst_nested_instantiate b K [] a (sfrag_tfrag a Ha) Hba).
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel t a (Ongoing [])) as [[u|]|] eqn:Eu; try discriminate H.
    destruct (tfrag_cases t Ht) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (proj1 (substitution_with_arguments b K [] E HE2 HE Hbf fuel) t a u Hs Ha Hbt Hba Eu) as [_ Hi].
      rewrite Hi. reflexivity.
    - destruct fuel as [|n]; [discriminate Eu|].
      destruct (substitution_into_intersection b K [] E HE2 HE Hbf n cs a u Hcs Ha Hbt Hba Eu) as [_ Hi].
      rewrite (unify_fuel_monotone env (S (n * S (S K) + E)) (S n * S (S K) + E) _ _ _ _ ltac:(simpl; lia) Hi). reflexivity.
    - destruct fuel as [|n]; [discriminate Eu|].
      destruct (substitution_into_nullable_intersection b K [] E HE2 HE Hbf n cs a u Hcs Ha Hbt Hba Eu) as [_ Hi].
      rewrite (unify_fuel_monotone env (S (n * S (S K) + E)) (S n * S (S K) + E) _ _ _ _ ltac:(simpl; lia) Hi). reflexivity.
Qed.

End Substitution.
