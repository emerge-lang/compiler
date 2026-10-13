From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The substitution lemma                                                                           *)
(*                                                                                                *)
(* Instantiating the type parameters keeps assignability: if a type is assignable to another, it  *)
(* still is with the type parameters in both replaced by type arguments. This is what makes        *)
(* checking generic code once enough: at run time, every type parameter stands for one exact type. *)
(* So the type parameters are instantiated with exact type arguments here: invariant, owned or ref,*)
(* of types of the fragment of Transitivity.v (bindings_in_fragment). The facts about instantiating*)
(* that don't need that (bound_in) take types of the fragment of Fragment.v as well, as the final  *)
(* values of inference can be (FinalValues.v).                                                     *)
(* The types instantiated are                                                                      *)
(* - class types, whose type arguments are of any variance and ownership, and contain types of     *)
(*   the fragment; Nothing only as `exclusive Nothing`;                                            *)
(* - nullable class types;                                                                         *)
(* - references to type parameters, `T`, `m T` or `T!`, the mutability and `!` written or applied *)
(*   (as_written), and nullable ones, `T?`, whose bound is such a type without type parameters;   *)
(* - without type inference (no type variables), intersections or erroneous types.               *)
(* A reference becomes the type argument with the mutability and nullability of the reference      *)
(* applied (inst_ref), as a type of its own; in a type argument, it becomes the type in it          *)
(* (inst_nested). That instance is within the bound of the reference (binds_ref): for `T`, the type  *)
(* argument is within the bound of T. Not so for `mut T` with T bound to a scalar, whose values are *)
(* immutable whatever the mutability; `mut T` takes no value then, but Nothing.                    *)
(* A type parameter accepts a non-nullable Nothing of a mutability that fits its bound, also one an *)
(* instantiation of it doesn't accept: of the bound `read Any`, it takes `mut Nothing`, which isn't  *)
(* a `const C`. Nothing is never instantiated, though, so that doesn't matter for the soundness;   *)
(* hence `exclusive Nothing` only, also in the type arguments of supertypes                       *)
(* (supertypes_mention_nothing_as_bottom).                                                         *)
(*                                                                                                *)
(* A type parameter assigned to a class type needs the transitivity of unify: the instance is      *)
(* assignable to the bound, which is assignable to the class type. Two references to the same type  *)
(* parameter are the same type argument, with mutabilities and nullabilities applied that are        *)
(* ordered as their bounds are (same_parameter). A subclass assigned to its superclass needs         *)
(* instantiating the supertype to commute with instantiating the type parameters                   *)
(* (supertype_arguments_commute).                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma existsb_ext_in: forall {A: Type} (f g: A -> bool) l, (forall a, In a l -> f a = g a) -> existsb f l = existsb g l.
Proof.
    intros A f g l H. induction l as [|a l IH]; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Section Substitution.

Variable env: Environment.
Hypothesis wf: wellformed env.

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
   the mutability given to it (`mut T`) is that of its effective bound, and the `!` that narrowed it
   made the effective bound non-nullable *)
Definition as_written (given: option Mutability) (narrowed: bool) (bound: EType): bool :=
    match given with Some m => Mutability_beq (mutability_of env bound) m | None => true end
    && (negb narrowed || negb (is_nullable bound)).

(* The types instantiated *)
Fixpoint sfrag (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        if class_eqb c nothing then is_bottom m arguments else
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with TypeArgument _ _ n => sfrag n | _ => false end) arguments
    | Nullable n => (is_class n || is_generic n) && sfrag n
    | Generic (mkGenericRef given narrowed _ bound) => sfrag bound && closed bound && as_written given narrowed bound
    | _ => false
    end.

Definition argument_sfrag (a: EType): bool :=
    match a with TypeArgument _ _ n => sfrag n | _ => false end.

Definition generic_sfrag (g: GenericRef): Prop :=
    sfrag (effective_bound g) = true /\ closed (effective_bound g) = true
    /\ as_written (given_mutability g) (is_narrowed g) (effective_bound g) = true.

Fixpoint sdepth (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments =>
        S (list_max (map (fun a => match a with TypeArgument _ _ n => S (sdepth n) | _ => 0 end) arguments))
    | Nullable n => S (sdepth n)
    | Generic (mkGenericRef _ _ _ bound) => S (sdepth bound)
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
    if is_narrowed g then without_null (inst_fit g x) else inst_fit g x.

(* What a type in a type argument becomes, when instantiated: a reference to a type parameter, the
   instance of the type in its type argument *)
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
    | _ => instantiate env b n
    end.

(* `V!` for the reference V: GenericTypeReference.withCombinedNullability(NOT_NULLABLE) *)
Definition narrow_ref (g: GenericRef): GenericRef :=
    mkGenericRef (given_mutability g) (is_narrowed g || is_nullable (effective_bound g)) (param_of g)
        (without_null (effective_bound g)).

Lemma without_null_generic: forall g, without_null (Generic g) = Generic (narrow_ref g).
Proof. intros [gm nn p bound]. reflexivity. Qed.

Lemma generic_sfrag_sfrag: forall g, generic_sfrag g -> sfrag (Generic g) = true.
Proof. intros [gm nn p bound] [Hf [Hc Hw]]. simpl in *. rewrite Hf, Hc, Hw. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Class types of another mutability, or without null                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma in_fragment_with_mutability: forall k x, in_fragment env x = true -> in_fragment env (with_mutability env k x) = true.
Proof. intros k x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]]; exact H. Qed.

Lemma in_fragment_without_null: forall x, in_fragment env x = true -> in_fragment env (without_null x) = true.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]]; [exact H|exact H']. Qed.

Lemma in_fragment_rewrap: forall x, in_fragment env x = true -> in_fragment env (rewrap_nullable x) = true.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]]; exact H. Qed.

Lemma without_null_non_null: forall x, in_fragment env x = true -> is_nullable x = false -> without_null x = x.
Proof. intros x H Hn. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; [reflexivity|discriminate Hn]. Qed.

Lemma without_null_idempotent: forall x, in_fragment env x = true -> without_null (without_null x) = without_null x.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma without_null_not_nullable: forall x, in_fragment env x = true -> is_nullable (without_null x) = false.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma rewrap_without_null: forall x, in_fragment env x = true -> rewrap_nullable x = Nullable (without_null x).
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma mutability_of_without_null: forall x, in_fragment env x = true -> mutability_of env (without_null x) = mutability_of env x.
Proof. intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma nullable_with_mutability: forall k x, in_fragment env x = true -> is_nullable (with_mutability env k x) = is_nullable x.
Proof. intros k x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

(* A class type takes the mutability given, unless it is a scalar, which stays immutable *)
Lemma with_mutability_cases: forall x, in_fragment env x = true ->
    (forall k, mutability_of env (with_mutability env k x) = k)
    \/ (forall k, mutability_of env (with_mutability env k x) = mutability_of env x).
Proof.
    intros x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        (destruct (is_core_scalar (declaration_of env c)) eqn:E; [right|left]); intros k; simpl; rewrite E; reflexivity.
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
    Model.is_subtype_of (mutability_of env (RootResolved mx' cx xargs)) (mutability_of env (RootResolved md' cd dargs)) = true ->
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
    Model.is_subtype_of (mutability_of env x') (mutability_of env D') = true ->
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
    unify env f D x (Ongoing s) = Some (Ongoing r) -> unify env f (without_null D) (without_null x) (Ongoing s) = Some (Ongoing r).
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
    unify env f T y (Ongoing s) = Some (Ongoing r) -> unify env f T (without_null y) (Ongoing s) = Some (Ongoing r).
Proof.
    intros [|f] T y s r HT Hy H; [discriminate H|].
    destruct (fragment_cases env y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]]; [exact H|].
    destruct (fragment_cases env T HT) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> _]]]]].
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite unify_nullable_nullable in H. cbn [without_null]. rewrite unify_nullable_class. exact H.
Qed.

Lemma accepted_mutability_classes: forall f D y s r, in_fragment env D = true -> in_fragment env y = true ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> Model.is_subtype_of (mutability_of env y) (mutability_of env D) = true.
Proof.
    intros [|f] D y s r HD Hy H; [discriminate H|].
    assert (Hc: forall f' md cd dargs my cy yargs,
        unify env f' (RootResolved md cd dargs) (RootResolved my cy yargs) (Ongoing s) = Some (Ongoing r) ->
        Model.is_subtype_of (mutability_of env (RootResolved my cy yargs)) (mutability_of env (RootResolved md cd dargs)) = true).
    { intros [|f'] md cd dargs my cy yargs E; [discriminate E|]. rewrite unify_classes in E.
      destruct (base_type_is_subtype_of env cy cd); [|discriminate E]. destruct (Model.is_subtype_of _ _); [reflexivity|discriminate E]. }
    destruct (fragment_cases env D HD) as [[md [cd [dargs ->]]]|[md [cd [dargs [-> _]]]]];
    destruct (fragment_cases env y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]].
    - exact (Hc _ _ _ _ _ _ _ H).
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite unify_nullable_class in H. exact (Hc _ _ _ _ _ _ _ H).
    - rewrite unify_nullable_nullable in H. exact (Hc _ _ _ _ _ _ _ H).
Qed.

Lemma accepted_non_null: forall f D y s r, in_fragment env D = true -> in_fragment env y = true -> is_nullable D = false ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> is_nullable y = false.
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
    unify env f T (without_null y) (Ongoing s) = r -> unify env (S f) (Nullable T) y (Ongoing s) = r.
Proof.
    intros f T y s r Hy H. destruct (fragment_cases env y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]].
    - rewrite unify_nullable_class. exact H.
    - rewrite unify_nullable_nullable. exact H.
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
    Model.is_subtype_of (mutability_of env (inst_fit g x)) (mutability_of env x) = true.
Proof.
    intros g x H. unfold inst_fit. destruct (given_mutability g) as [m|]; [|apply mutability_is_subtype_of_refl].
    destruct (with_mutability_cases x H) as [Hk|Hk]; rewrite Hk; [apply intersect_mutability_left|apply mutability_is_subtype_of_refl].
Qed.

Lemma mutability_inst_ref: forall g x, in_fragment env x = true -> mutability_of env (inst_ref g x) = mutability_of env (inst_fit g x).
Proof.
    intros g x H. unfold inst_ref. destruct (is_narrowed g); [|reflexivity].
    apply mutability_of_without_null, inst_fit_in_fragment, H.
Qed.

Lemma nullable_inst_fit: forall g x, in_fragment env x = true -> is_nullable (inst_fit g x) = is_nullable x.
Proof. intros g x H. unfold inst_fit. destruct (given_mutability g); [apply nullable_with_mutability, H|reflexivity]. Qed.

(* Without null, a reference and its `!` are the same *)
Lemma narrow_ref_inst: forall g x, in_fragment env x = true ->
    without_null (inst_ref (narrow_ref g) x) = without_null (inst_ref g x).
Proof.
    intros g x H. pose proof (without_null_idempotent _ (inst_fit_in_fragment g x H)) as Hi.
    unfold inst_ref. cbn [is_narrowed narrow_ref]. unfold inst_fit. cbn [given_mutability narrow_ref]. fold (inst_fit g x).
    destruct (is_narrowed g), (is_nullable (effective_bound g)); cbn [orb]; first [exact Hi|reflexivity|symmetry; exact Hi].
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
    unify env (S n) (RootResolved m c args) (Generic g) (Ongoing s) = unify env n (RootResolved m c args) (effective_bound g) (Ongoing s).
Proof. intros n m c args [gm nn q bound] s. reflexivity. Qed.

Lemma unify_generic_root: forall n g m c args s,
    unify env (S n) (Generic g) (RootResolved m c args) (Ongoing s)
    = if class_eqb c nothing && Model.is_subtype_of (mutability_of env (RootResolved m c args)) (mutability_of env (effective_bound g))
      then Some (Ongoing s) else Some Failed.
Proof. intros n [gm nn p bound] m c args s. reflexivity. Qed.

Lemma unify_generic_nullable: forall n g na s, unify env (S n) (Generic g) (Nullable na) (Ongoing s) = Some Failed.
Proof. intros n [gm nn p bound] na s. reflexivity. Qed.

Lemma unify_nullable_generic_generic: forall n gt ga s,
    unify env (S n) (Nullable (Generic gt)) (Generic ga) (Ongoing s) = unify env n (Generic gt) (Generic (narrow_ref ga)) (Ongoing s).
Proof. intros n gt [gm nn p bound] s. reflexivity. Qed.

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
   whose instance by the reference is assignable to its bound *)
Definition binds_ref (g: GenericRef): bool :=
    match lookup_binding b (param_of g) with
    | Some (TypeArgument Model.invariant o x) => is_exact_ownership o && gfrag env x && respects (inst_ref g x) (effective_bound g)
    | _ => false
    end.

Lemma binds_ref_plain: forall p bound, binds_ref (mkGenericRef None false p bound) = binds_exactly p bound.
Proof. reflexivity. Qed.

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

(* Every type parameter in the type is bound exactly *)
Fixpoint bound_in (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb bound_in arguments
    | Nullable n => bound_in n
    | Generic g => binds_ref g
    | TypeArgument _ o n => ownership_bound o && bound_in n
    | _ => true
    end.

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
    assert (Hg: forall gm nn p bound, sfrag (Generic (mkGenericRef gm nn p bound)) = true -> generic_sfrag (mkGenericRef gm nn p bound)).
    { intros gm nn p bound H. simpl in H. apply andb_true_iff in H. destruct H as [H Hw]. apply andb_true_iff in H.
      destruct H as [Hf Hc]. split; [exact Hf|]. split; [exact Hc|exact Hw]. }
    intros [m c args|[m c args| |g| | | |]| g | | | |] H; simpl in H; try discriminate H.
    - destruct (class_eqb c nothing) eqn:Hc.
      + right. left. apply class_eqb_true in Hc. subst c.
        destruct m as [[]|], args; simpl in H; try discriminate H. reflexivity.
      + left. apply andb_true_iff in H. destruct H as [Hl Ha]. exists m, c, args.
        split; [reflexivity|]. split; [exact Hc|]. split; [apply Nat.eqb_eq, Hl|]. apply forallb_forall, Ha.
    - right. right. left. exists m, c, args. split; [reflexivity|exact H].
    - right. right. right. right. exists g. split; [reflexivity|]. destruct g as [gm nn p bound]. exact (Hg gm nn p bound H).
    - right. right. right. left. exists g. split; [reflexivity|]. destruct g as [gm nn p bound]. exact (Hg gm nn p bound H).
Qed.

Lemma bound_in_root: forall m c arguments,
    bound_in (RootResolved m c arguments) = true -> forall a, In a arguments -> bound_in a = true.
Proof. intros m c arguments H. apply forallb_forall, H. Qed.

Lemma sdepth_below: forall m c arguments a,
    In a arguments -> S (argument_sdepth a) <= sdepth (RootResolved m c arguments).
Proof.
    intros m c arguments a Ha. change (S (argument_sdepth a) <= S (list_max (map argument_sdepth arguments))).
    assert (H: Forall (fun k => k <= list_max (map argument_sdepth arguments)) (map argument_sdepth arguments))
        by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (argument_sdepth a) (in_map _ _ _ Ha)). lia.
Qed.

Lemma sdepth_generic: forall g, 1 <= sdepth (Generic g).
Proof. intros [gm nn p bound]. simpl. lia. Qed.

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

Lemma binds_ref_some: forall g, binds_ref g = true ->
    exists o x, lookup_binding b (param_of g) = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ gfrag env x = true /\ respects (inst_ref g x) (effective_bound g) = true.
Proof.
    intros g H. unfold binds_ref in H. destruct (lookup_binding b (param_of g)) as [a|]; [|discriminate H].
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

(* A reference, instantiated in a type argument, takes the place of the type in it *)
Lemma instantiate_generic_argument: forall v o g o' x,
    lookup_binding b (param_of g) = Some (TypeArgument Model.invariant o' x) ->
    instantiate env b (TypeArgument v o (Generic g)) = TypeArgument v (instantiate_ownership b o) (inst_ref g x)
    /\ instantiate env b (TypeArgument v o (Nullable (Generic g))) = TypeArgument v (instantiate_ownership b o) (rewrap_nullable (inst_ref g x)).
Proof.
    intros v o [[m|] [|] p bound] o' x E; simpl in E |- *; rewrite E; destruct v; split; reflexivity.
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
    - destruct (binds_ref_some g Hb) as [o' [x [E _]]].
      rewrite (inst_nested_generic g _ o' x E). exact (proj1 (instantiate_generic_argument v o g o' x E)).
    - destruct (binds_ref_some g Hb) as [o' [x [E _]]].
      rewrite (inst_nested_nullable_generic g _ o' x E). exact (proj2 (instantiate_generic_argument v o g o' x E)).
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

(* A reference, made non-null, to the class type; that is, its bound, which is closed *)
Lemma unify_nullable_generic: forall n m c args g u, sfrag (effective_bound g) = true -> closed (effective_bound g) = true ->
    unify env (S n) (Nullable (RootResolved m c args)) (Generic g) (Ongoing s) = Some u ->
    unify env n (Nullable (RootResolved m c args)) (effective_bound g) (Ongoing s) = Some u.
Proof.
    intros n m c args [gm nn q bound] u Hf Hc H. cbn [effective_bound] in Hf, Hc |- *.
    rewrite unify_step_once in H. unfold unify_step, unify_nullable in H.
    cbn [without_null] in H. destruct n as [|n]; [discriminate H|]. rewrite unify_root_generic in H. cbn [effective_bound] in H.
    destruct (sfrag_cases bound Hf) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[? [-> _]]|[? [-> _]]]]]];
        [exact H|exact H|exact H|discriminate Hc|discriminate Hc].
Qed.

(* A reference, whose bound is no type parameter, is assignable to another of the same type
   parameter, of a bound above, and to nothing else but where it is bounded by Nothing *)
Lemma unify_generic_generic: forall n gt ga u, sfrag (effective_bound ga) = true -> closed (effective_bound ga) = true ->
    unify env (S n) (Generic gt) (Generic ga) (Ongoing s) = Some (Ongoing u) -> u = s /\
    ((param_of ga = param_of gt
        /\ Model.is_subtype_of (mutability_of env (effective_bound ga)) (mutability_of env (effective_bound gt)) = true
        /\ negb (is_nullable (effective_bound ga)) || is_nullable (effective_bound gt) = true)
     \/ effective_bound ga = bottom_type).
Proof.
    intros n [gmt nnt p bt] [gma nna q bq] u Hf Hc H. cbn [effective_bound param_of] in Hf, Hc |- *.
    rewrite unify_step_once in H. unfold unify_step, unify_generic in H.
    destruct (param_eqb q p) eqn:E.
    - apply param_eqb_eq in E. subst q.
      destruct (_ && _) eqn:Ec in H; [|discriminate H]. injection H as <-. apply andb_true_iff in Ec. destruct Ec as [Ecm Ecn].
      split; [reflexivity|]. left. split; [reflexivity|]. split; [exact Ecm|exact Ecn].
    - destruct n as [|n]; [discriminate H|]. rewrite unify_step_once in H. unfold unify_step, unify_generic in H.
      destruct (sfrag_cases bq Hf) as [[? [? [? [-> [Hcn _]]]]]|[->|[[? [? [? [-> _]]]]|[[? [-> _]]|[? [-> _]]]]]];
          [|split; [|right; reflexivity]|discriminate H|discriminate Hc|discriminate Hc].
      + simpl in H. rewrite Hcn in H. discriminate H.
      + destruct (_ && _) in H; [injection H; auto|discriminate H].
Qed.


Lemma respects_unify: forall x bound, in_fragment env x = true -> in_fragment env bound = true -> respects x bound = true ->
    unify env K bound x (Ongoing s) = Some (Ongoing s).
Proof.
    intros x bound Hx Hb H. unfold respects in H. destruct (unify env K bound x (Ongoing s)) as [[w|]|] eqn:Eu; try discriminate H.
    assert (w = s) by exact (proj1 (keeps_states_with_arguments env wf K) bound x s w Hb Hx Eu). subst w. reflexivity.
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
   are, too. The mutability given to the one fits that given to the other; where only the target is
   narrowed, the bounds are non-null, and so are the instances. *)
Lemma same_parameter: forall f gt ga x, in_fragment env x = true ->
    unify env f x x (Ongoing s) = Some (Ongoing s) ->
    generic_sfrag gt -> generic_sfrag ga -> respects (inst_ref ga x) (effective_bound ga) = true ->
    Model.is_subtype_of (mutability_of env (effective_bound ga)) (mutability_of env (effective_bound gt)) = true ->
    negb (is_nullable (effective_bound ga)) || is_nullable (effective_bound gt) = true ->
    unify env f (inst_ref gt x) (inst_ref ga x) (Ongoing s) = Some (Ongoing s).
Proof.
    intros f gt ga x Hx Hrefl [Hft [Hct Hwt]] [Hfa [Hca Hwa]] Hr Hm Hn.
    pose proof (closed_in_fragment _ Hfa Hca) as HFa.
    pose proof (inst_ref_in_fragment ga x Hx) as HIa.
    pose proof (respects_unify _ _ HIa HFa Hr) as Hra.
    pose proof (accepted_mutability_classes _ _ _ _ _ HFa HIa Hra) as Hma.
    unfold as_written in Hwt. apply andb_true_iff in Hwt. destruct Hwt as [Hwtm Hwtn].
    (* the type argument, with the mutabilities applied *)
    assert (Hfit: unify env f (inst_fit gt x) (inst_fit ga x) (Ongoing s) = Some (Ongoing s)).
    { apply (unify_remut f x _ x _ s s (remut_inst_fit gt x Hx) (remut_inst_fit ga x Hx)); [|exact Hrefl].
      destruct (with_mutability_cases x Hx) as [Hk|Hk].
      - unfold inst_fit at 2. destruct (given_mutability gt) as [m|] eqn:Eg.
        + rewrite Hk. apply intersect_mutability_greatest; [apply inst_fit_mutability_below, Hx|].
          apply mutability_beq_eq in Hwtm. rewrite <- Hwtm, <- (mutability_inst_ref ga x Hx).
          exact (mutability_subtype_trans _ _ _ Hma Hm).
        + apply inst_fit_mutability_below, Hx.
      - assert (Hfx: forall g, mutability_of env (inst_fit g x) = mutability_of env x).
        { intros g. unfold inst_fit. destruct (given_mutability g); [apply Hk|reflexivity]. }
        rewrite !Hfx. apply mutability_is_subtype_of_refl. }
    pose proof (inst_fit_in_fragment gt x Hx) as HIft. pose proof (inst_fit_in_fragment ga x Hx) as HIfa.
    unfold inst_ref. destruct (is_narrowed gt) eqn:Ent, (is_narrowed ga) eqn:Ena.
    - exact (unify_without_null f _ _ s s HIft HIfa Hfit).
    - (* the target is narrowed, so the bounds and the assignee are non-null *)
      cbn [negb orb] in Hwtn. apply negb_true_iff in Hwtn. rewrite Hwtn, orb_false_r in Hn. apply negb_true_iff in Hn.
      pose proof (accepted_non_null _ _ _ _ _ HFa HIa Hn Hra) as Hna. unfold inst_ref in Hna. rewrite Ena in Hna.
      rewrite <- (without_null_non_null _ HIfa Hna). exact (unify_without_null f _ _ s s HIft HIfa Hfit).
    - exact (unify_without_null_assignee f _ _ s s HIft HIfa Hfit).
    - exact Hfit.
Qed.

Lemma narrow_generic_sfrag: forall g, generic_sfrag g -> generic_sfrag (narrow_ref g).
Proof.
    intros g [Hf [Hc Hw]]. pose proof (closed_in_fragment _ Hf Hc) as HF.
    unfold generic_sfrag, narrow_ref, as_written in *. cbn [effective_bound given_mutability is_narrowed] in *.
    apply andb_true_iff in Hw. destruct Hw as [Hwm _].
    rewrite (mutability_of_without_null _ HF), (without_null_not_nullable _ HF), Hwm.
    change (negb false) with true. rewrite orb_true_r.
    destruct (sfrag_cases _ Hf) as [[m [c [args [E _]]]]|[E|[[m [c [args [E Hf']]]]|[[g' [E _]]|[g' [E _]]]]]];
        rewrite E in *; try (simpl in Hc; discriminate Hc); repeat split; first [exact Hf | exact Hc | exact Hf' | reflexivity].
Qed.

Section Main.

(* The fuel it takes to unify a type argument of the bindings with itself, and one to spare *)
Variable E: nat.
Hypothesis HE2: 2 <= E.
Hypothesis HE: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> depth x <= E.
Hypothesis Hbf: bindings_in_fragment.

Lemma narrow_binds_ref: forall g, generic_sfrag g -> binds_ref g = true -> binds_ref (narrow_ref g) = true.
Proof.
    intros g [Hf [Hc _]] Hb. destruct (binds_ref_some g Hb) as [o [x [Ex [Ho [Hx Hr]]]]].
    pose proof (Hbf _ o x Ex) as HFx. pose proof (closed_in_fragment _ Hf Hc) as HF.
    pose proof (inst_ref_in_fragment g x HFx) as HI.
    unfold binds_ref. change (param_of (narrow_ref g)) with (param_of g).
    change (effective_bound (narrow_ref g)) with (without_null (effective_bound g)). rewrite Ex.
    change (is_exact_ownership o && gfrag env x && respects (inst_ref (narrow_ref g) x) (without_null (effective_bound g)) = true).
    rewrite Ho, Hx. cbn [andb]. unfold respects in *.
    destruct (unify env K (effective_bound g) (inst_ref g x) (Ongoing s)) as [[w|]|] eqn:Eu; try discriminate Hr.
    destruct (is_nullable (effective_bound g)) eqn:En.
    - assert (Hi: inst_ref (narrow_ref g) x = without_null (inst_ref g x)).
      { unfold inst_ref. change (inst_fit (narrow_ref g) x) with (inst_fit g x). cbn [is_narrowed narrow_ref]. rewrite En, orb_true_r.
        destruct (is_narrowed g); [symmetry; apply without_null_idempotent, inst_fit_in_fragment, HFx|reflexivity]. }
      rewrite Hi, (unify_without_null K _ _ s w HF HI Eu). reflexivity.
    - assert (Hi: inst_ref (narrow_ref g) x = inst_ref g x).
      { unfold inst_ref. change (inst_fit (narrow_ref g) x) with (inst_fit g x). cbn [is_narrowed narrow_ref].
        rewrite En, orb_false_r. reflexivity. }
      rewrite Hi, (without_null_non_null _ HF En), Eu. reflexivity.
Qed.

(* A reference assigned to a reference: of the same type parameter, the instances are ordered as the
   bounds are; of another one, it is bounded by Nothing *)
Lemma generic_generic: forall f gt ga u, generic_sfrag gt -> generic_sfrag ga ->
    binds_ref gt = true -> binds_ref ga = true ->
    unify env f (Generic gt) (Generic ga) (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (K + E) (inst_nested b (Generic gt)) (inst_nested b (Generic ga)) (Ongoing s) = Some (Ongoing s).
Proof.
    intros [|f] gt ga u Hgt Hga Hbt Hba H; [discriminate H|]. pose proof Hga as [Hfa [Hca _]].
    destruct (binds_ref_some gt Hbt) as [o [x [Et _]]]. destruct (binds_ref_some ga Hba) as [o' [x' [Ea [_ [_ Hra]]]]].
    pose proof (Hbf _ o x Et) as Hx. pose proof (Hbf _ o' x' Ea) as Hx'.
    rewrite (inst_nested_generic gt _ o x Et), (inst_nested_generic ga _ o' x' Ea).
    destruct (unify_generic_generic f gt ga u Hfa Hca H) as [-> [[Hp [Hm Hn]]|Hbot]]; split; try reflexivity.
    - rewrite Hp, Et in Ea. injection Ea as <- <-.
      apply (unify_fuel_monotone env E); [lia|].
      apply (same_parameter E gt ga x Hx); [|exact Hgt|exact Hga|exact Hra|exact Hm|exact Hn].
      apply (proj1 (reflexivity_with_arguments env E)); [exact Hx|exact (HE _ o x Et)].
    - pose proof (inst_ref_in_fragment gt x Hx) as HIt. pose proof (inst_ref_in_fragment ga x' Hx') as HIa.
      rewrite Hbot in Hra.
      apply (unify_fuel_monotone env (K + 2)); [lia|].
      apply (proj1 (transitivity_with_arguments env wf (K + 2)) (inst_ref ga x') bottom_type (inst_ref gt x) K 2 s (le_n _));
          [exact HIa|exact (bottom_in_fragment env wf)|exact HIt| |apply below_all; [exact HIt|lia]].
      apply respects_unify; [exact HIa|exact (bottom_in_fragment env wf)|exact Hra].
Qed.

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
      assert (Hvia: forall ga, generic_sfrag ga -> binds_ref ga = true ->
          unify env n t (effective_bound ga) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (P + E + S K)) (inst_nested b t) (inst_nested b (Generic ga)) (Ongoing s) = Some (Ongoing s)).
      { intros ga [Hfb [Hcb _]] Hbq Hu.
        destruct (proj1 (closed_facts (sdepth (effective_bound ga))) _ (le_n _) Hfb Hcb) as [HTb [_ [Hbb _]]].
        destruct (IHt t _ u Ht Hfb Hbt Hbb Hu) as [-> Hi].
        rewrite (inst_nested_closed _ Hfb Hcb) in Hi.
        destruct (binds_ref_some ga Hbq) as [o [x [Ex [_ [_ Hr]]]]]. pose proof (Hbf _ o x Ex) as Hx.
        pose proof (inst_ref_in_fragment ga x Hx) as HI.
        rewrite (inst_nested_generic ga _ o x Ex). split; [reflexivity|].
        apply (unify_fuel_monotone env (K + (P + E))); [lia|].
        apply (proj1 (transitivity_with_arguments env wf (K + (P + E))) (inst_ref ga x) (effective_bound ga) (inst_nested b t) K (P + E) s (le_n _));
            [exact HI|exact HTb|exact (instance_in_fragment Hbf t Ht Hbt)|apply respects_unify; assumption|exact Hi]. }
      (* two class types *)
      assert (Hroot: forall mt ct targs ma ca aargs,
          sfrag (RootResolved mt ct targs) = true -> sfrag (RootResolved ma ca aargs) = true ->
          bound_in (RootResolved mt ct targs) = true -> bound_in (RootResolved ma ca aargs) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (P + E + S K)) (RootResolved mt ct (map (instantiate env b) targs))
              (RootResolved ma ca (map (instantiate env b) aargs)) (Ongoing s) = Some (Ongoing s)).
      { intros mt ct targs ma ca aargs Hft Hfa Hbt' Hba' Hu.
        rewrite unify_classes in Hu |- *.
        rewrite (mutability_of_class env mt ct (map (instantiate env b) targs) targs),
            (mutability_of_class env ma ca (map (instantiate env b) aargs) aargs).
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
      + apply unify_nullable_generic in H; [|exact (proj1 Hga)|exact (proj1 (proj2 Hga))]. exact (Hvia ga Hga Hba H).
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
      + destruct (generic_generic (S n) gt ga u Hgt Hga Hbt Hba H) as [-> Hi]. split; [reflexivity|].
        apply (unify_fuel_monotone env (K + E)); [lia|exact Hi].
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
      + rewrite unify_nullable_generic_generic in H.
        destruct (generic_generic n gt (narrow_ref ga) u Hgt (narrow_generic_sfrag ga Hga) Hbt (narrow_binds_ref ga Hga Hba) H)
            as [-> Hi].
        split; [reflexivity|].
        destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]]. destruct (binds_ref_some ga Hba) as [o' [x' [Ea _]]].
        pose proof (inst_ref_in_fragment gt x (Hbf _ o x Ex)) as HIt. pose proof (inst_ref_in_fragment ga x' (Hbf _ o' x' Ea)) as HIa.
        rewrite (inst_nested_generic gt _ o x Ex), (inst_nested_generic (narrow_ref ga) _ o' x' Ea) in Hi.
        rewrite (inst_nested_nullable_generic gt _ o x Ex), (inst_nested_generic ga _ o' x' Ea).
        rewrite (rewrap_without_null _ HIt). apply unify_into_nullable; [exact HIa|].
        rewrite <- (narrow_ref_inst ga x' (Hbf _ o' x' Ea)).
        apply (unify_fuel_monotone env (K + E)); [lia|].
        apply unify_without_null; [exact HIt|apply inst_ref_in_fragment, (Hbf _ o' x' Ea)|exact Hi].
      + rewrite unify_nullable_nullable in H.
        destruct (generic_generic n gt ga u Hgt Hga Hbt Hba H) as [-> Hi]. split; [reflexivity|].
        destruct (binds_ref_some gt Hbt) as [o [x [Ex _]]]. destruct (binds_ref_some ga Hba) as [o' [x' [Ea _]]].
        rewrite (inst_nested_generic gt _ o x Ex), (inst_nested_generic ga _ o' x' Ea) in Hi.
        rewrite (inst_nested_nullable_generic gt _ o x Ex), (inst_nested_nullable_generic ga _ o' x' Ea).
        apply (unify_fuel_monotone env (S (K + E))); [lia|].
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
    sfrag t = true -> sfrag a = true -> bound_in b K [] t = true -> bound_in b K [] a = true ->
    is_assignable_to env fuel a t = Some true ->
    is_assignable_to env (fuel * S (S K) + E) (inst_nested b a) (inst_nested b t) = Some true.
Proof.
    intros b K E fuel t a HE2 HE Hbf Ht Ha Hbt Hba H. unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel t a (Ongoing [])) as [[u|]|] eqn:Eu; try discriminate H.
    destruct (proj1 (substitution_with_arguments b K [] E HE2 HE Hbf fuel) t a u Ht Ha Hbt Hba Eu) as [_ Hi].
    rewrite Hi. reflexivity.
Qed.

End Substitution.
