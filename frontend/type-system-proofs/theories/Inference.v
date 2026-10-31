From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Substitution.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Inference, with type variables bound exactly                                                     *)
(*                                                                                                *)
(* An invocation unifies the types of the parameters, in which the type parameters of the function *)
(* are type variables, with the types of the arguments. A type variable bound exactly, to a type    *)
(* argument, stands for each type the type argument does: `out B` for B and its subtypes; it is     *)
(* bound so by the explicit type arguments of an invocation, and by capturing the type arguments of *)
(* the receiver (Subtyping.capturable). Whatever unify accepts with the variables bound so, it      *)
(* accepts with the variables replaced by any of the types they stand for                          *)
(* (inference_with_arguments). Unifying the receiver parameter of a member function with the       *)
(* receiver binds the type parameters of the class so (receiver_captures), which makes calling a   *)
(* member function sound, where the function has no type parameters of its own (member_call_sound). *)
(* Type variables that aren't bound exactly, with lower and upper bounds, are left for later.       *)
(*                                                                                                *)
(* The types of the parameters are those of Substitution.v, with type variables in place of the    *)
(* type parameters (to_generic relates the two); the types of the arguments are those of            *)
(* Transitivity.v (in_fragment), Nothing of any mutability: it is const (wf_nothing_is_const), so   *)
(* every `m Nothing` is assigned as `exclusive Nothing`, and there are no values of type Nothing.   *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma existsb_map_ext: forall {A B: Type} (f: B -> bool) (g: A -> bool) (h: A -> B) l,
    (forall a, In a l -> f (h a) = g a) -> existsb f (map h l) = existsb g l.
Proof.
    intros A B f g h l H. induction l as [|a l IH]; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros a' Ha'. apply H. right. exact Ha'.
Qed.

(* No in-variant type argument, nested ones included *)
Fixpoint without_contravariance (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb without_contravariance arguments
    | Nullable n => without_contravariance n
    | TypeArgument v _ n => negb (Variance_beq v input) && without_contravariance n
    | Intersection components => forallb without_contravariance components
    | _ => true
    end.

(* The type arguments of supertypes are without contravariance: no supertype declaration has an
   in-variant type argument, nested ones included (`class K : Cn<Cn<in K>>` has one). With them, unify
   needn't terminate (Conjectures.v); and normalizing a type without contravariance to a supertype may
   make one with it (Constraints.v, which takes this where the arguments must be without it). *)
Definition supertypes_without_contravariance (env: Environment): Prop :=
    forall sub super, forallb without_contravariance (supertype_arguments env sub super) = true.

Section Inference.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.

(* The type parameters of a type, as type variables *)
Fixpoint to_generic (t: EType): EType :=
    match t with
    | RootResolved m c arguments => RootResolved m c (map to_generic arguments)
    | Nullable n => Nullable (to_generic n)
    | TypeVariable g => Generic g
    | TypeArgument v o n => TypeArgument v o (to_generic n)
    | Intersection components => Intersection (map to_generic components)
    | _ => t
    end.

(* A type variable as a type argument, of a mutability given to it, narrowed or made nullable
   (`Box<mut T>`, `Box<T!>`, `Box<T?>`) *)
Definition nested_ref (t: EType): bool :=
    match t with
    | TypeVariable (mkGenericRef _ _ _ []) | Nullable (TypeVariable (mkGenericRef _ _ _ [])) => true
    | _ => false
    end.

(* No type parameters but as type variables, of no mutability of their own but as type arguments *)
Fixpoint no_generics (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb no_generics arguments
    | Nullable n => is_class n && no_generics n
    | TypeVariable (mkGenericRef None false p []) => true
    | TypeArgument _ _ n => no_generics n || nested_ref n
    | _ => false
    end.

(* The types of the parameters *)
Definition ifrag (t: EType): bool := sfrag env (to_generic t) && no_generics t.

(* The types of the type arguments in them *)
Definition nfrag (t: EType): bool := sfrag env (to_generic t) && (no_generics t || nested_ref t).

(* The type variables as type arguments are plain, or made nullable (`Box<T>`, `Box<T?>`), not of a
   mutability given to them nor narrowed *)
Fixpoint args_plain (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb args_plain arguments
    | Nullable n => args_plain n
    | TypeArgument _ _ n =>
        match n with
        | TypeVariable g | Nullable (TypeVariable g) => match g with mkGenericRef None false _ _ => true | _ => false end
        | _ => args_plain n
        end
    | Intersection components => forallb args_plain components
    | _ => true
    end.

(* A type variable made nullable is narrowed, or of a non-null bound (`Box<T?>`, of a nullable bound
   narrowed, as the compiler builds it) *)
Fixpoint nullable_narrowed (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb nullable_narrowed arguments
    | Nullable (TypeVariable (mkGenericRef _ nn p _)) => nn || negb (is_nullable env (Generic (mkGenericRef None false p [])))
    | Nullable n => nullable_narrowed n
    | TypeArgument _ _ n => nullable_narrowed n
    | Intersection components => forallb nullable_narrowed components
    | _ => true
    end.

(* ... in the type arguments of a type *)
Definition args_narrowed (t: EType): bool :=
    match t with TypeVariable _ | Nullable (TypeVariable _) => true | _ => nullable_narrowed t end.

Lemma narrowed_content: forall v o n, nullable_narrowed (TypeArgument v o n) = true -> args_narrowed n = true.
Proof. intros v o [m c args|[| | | | |g|]|g|me msg|v' o' n'|g|cs] H; cbn [nullable_narrowed args_narrowed] in H |- *; first [exact H|reflexivity]. Qed.

Lemma args_narrowed_root: forall m c args, args_narrowed (RootResolved m c args) = true -> forall a, In a args -> args_narrowed a = true.
Proof.
    intros m c args H a Ha. change (forallb nullable_narrowed args = true) in H. rewrite forallb_forall in H.
    destruct a as [|[| | | | | |]| | | | |]; try reflexivity; exact (H _ Ha).
Qed.

Lemma no_vars_narrowed: forall t, no_vars t = true -> nullable_narrowed t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; cbn [no_vars] in H; cbn [nullable_narrowed]; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. cbn [forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - pose proof (IH n) as IHn. clear IH. destruct n as [m c args|n'|g|me msg|v o n'|g|cs]; try discriminate H; exact (IHn H).
    - exact (IH n H).
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

Lemma args_plain_argument: forall v o n, args_plain (TypeArgument v o n) = true -> args_plain n = true.
Proof. intros v o [m c args|[| | | | |g|]|g|me msg|v' o' n'|g|cs] H; cbn [args_plain] in H |- *; first [exact H|reflexivity]. Qed.

Lemma no_vars_args_plain: forall t, no_vars t = true -> args_plain t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; cbn [no_vars] in H; cbn [args_plain]; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. cbn [forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - pose proof (IH n) as IHn. clear IH.
      destruct n as [m c args|[| | | | |g|]|g|me msg|v' o' n'|g|cs]; try discriminate H; exact (IHn H).
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

(* What a reference to a type parameter makes of the type argument x it is bound to: the mutability
   given to it applied, and without null where it is narrowed (Substitution.inst_ref) *)
Definition ref_apply (gm: option Mutability) (nn: bool) (x: EType): EType :=
    let y := match gm with Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x | None => x end in
    if nn then without_null env y else y.

(* The bound x of a type parameter, as a reference to it makes its effective bound *)
Definition bound_apply (gm: option Mutability) (nn: bool) (x: EType): EType :=
    let y := match gm with Some m => with_mutability env m x | None => x end in
    if nn then without_null env y else y.

(* The type parameters in place of the type variables; a type variable at the top of a type as the
   plain reference to its type parameter: neither the mutability given to the variable nor whether it
   is narrowed changes which bindings it takes *)
Definition pgeneric (t: EType): EType :=
    match t with
    | TypeVariable (mkGenericRef _ _ p []) => Generic (mkGenericRef None false p [])
    | Nullable (TypeVariable (mkGenericRef _ _ p [])) => Nullable (Generic (mkGenericRef None false p []))
    | _ => to_generic t
    end.

(* A type variable as the top of the type of a parameter, of a mutability given to it and narrowed or
   not (`mut T`, `T!`), or made nullable (`T?`, `mut T?`), narrowed where the bound of the type
   parameter is nullable, as the compiler builds `T?` (NullableTypeReference) *)
Definition reference_variable (t: EType): bool :=
    match t with
    | TypeVariable (mkGenericRef gm nn p []) | Nullable (TypeVariable (mkGenericRef gm nn p [])) =>
        sfrag env (Generic (mkGenericRef gm nn p [])) && sfrag env (Generic (mkGenericRef None false p []))
    | _ => false
    end.

(* The types of the parameters, at their top *)
Definition pfrag (t: EType): bool := ifrag t || reference_variable t.

(* The components of an intersection: types of the parameters, or a type variable of a mutability given
   to it or narrowed (`A & mut U`, `A & U!`), as ofComponents gives the components their common
   mutability and narrows a component whose bound is nullable *)
Definition compfrag (t: EType): bool :=
    ifrag t || match t with TypeVariable (mkGenericRef _ _ _ []) => reference_variable t | _ => false end.

(* The types of the arguments *)
Definition afrag (t: EType): bool := in_fragment env t.

Fixpoint vsize (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments => S (list_max (map vsize arguments))
    | Nullable n => S (vsize n)
    | TypeArgument _ _ n => S (vsize n)
    | _ => 0
    end.

Lemma vsize_below: forall m c arguments a, In a arguments -> vsize a < vsize (RootResolved m c arguments).
Proof.
    intros m c arguments a Ha. change (vsize a < S (list_max (map vsize arguments))).
    assert (H: Forall (fun k => k <= list_max (map vsize arguments)) (map vsize arguments)) by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (vsize a) (in_map _ _ _ Ha)). lia.
Qed.

Lemma fragment_no_vars: forall k,
    (forall t, depth t <= k -> in_fragment env t = true -> no_vars t = true)
    /\ (forall a, argument_depth a <= k -> argument_in_fragment env a = true -> no_vars a = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; simpl in Hd; lia.
      - intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    split.
    - intros t Hd Ht. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> Ht']]]]].
      + destruct (root_in_fragment env _ _ _ Ht) as [_ Hargs]. simpl. apply forallb_forall. intros a Ha.
        pose proof (argument_depth_below m c args a Ha). apply IHa; [lia|apply Hargs, Ha].
      + rewrite depth_nullable in Hd. simpl.
        destruct (root_in_fragment env _ _ _ Ht') as [_ Hargs]. apply forallb_forall. intros a Ha.
        pose proof (argument_depth_below m c args a Ha). apply IHa; [lia|apply Hargs, Ha].
    - intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd |- *. apply IHt; [lia|exact Ha].
Qed.

Lemma in_fragment_no_vars: forall t, in_fragment env t = true -> no_vars t = true.
Proof. intros t. apply (proj1 (fragment_no_vars (depth t))). lia. Qed.

Lemma argument_in_fragment_no_vars: forall a, argument_in_fragment env a = true -> no_vars a = true.
Proof. intros a. apply (proj2 (fragment_no_vars (argument_depth a))). lia. Qed.

(* A bound without type variables is the upper bound a variable starts with *)
Lemma initial_closed: forall bound, no_vars bound = true -> initial_upper_bound bound = bound.
Proof. intros bound H. unfold initial_upper_bound. rewrite H. reflexivity. Qed.

Lemma initial_in_fragment: forall bound, in_fragment env bound = true -> initial_upper_bound bound = bound.
Proof. intros bound H. exact (initial_closed bound (in_fragment_no_vars bound H)). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Type variables and type parameters instantiate alike                                            *)
(* ---------------------------------------------------------------------------------------------- *)

(* The type variables of the type have bindings: those without one stay as they are, where the type
   parameter in their place would be replaced by its bound *)
Fixpoint bound_vars (b: Bindings) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb (bound_vars b) arguments
    | Nullable n => bound_vars b n
    | TypeVariable (mkGenericRef _ _ p _) => match lookup_binding b p with Some _ => true | None => false end
    | TypeArgument _ _ n => bound_vars b n
    | _ => true
    end.

Lemma nested_ref_facts: forall t, nested_ref t = true ->
    (forall b, mentions_loosely_bound b (to_generic t) = mentions_loosely_bound b t)
    /\ (forall b, mentions_loosely_bound_in_arguments b (to_generic t) = mentions_loosely_bound_in_arguments b t)
    /\ mutability_of env (to_generic t) = mutability_of env t
    /\ (forall b, bound_vars b t = true -> instantiate env b (to_generic t) = instantiate env b t).
Proof.
    intros [|[| | | | |[gm nn p []]|]| | | |[gm nn p []]|] H; try discriminate H;
        (split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]); intros b Hb; cbn [bound_vars] in Hb; cbn [to_generic instantiate];
        destruct (lookup_binding b p); first [reflexivity|discriminate Hb].
Qed.

Lemma to_generic_facts: forall k t, vsize t <= k -> no_generics t = true ->
    (forall b, mentions_loosely_bound b (to_generic t) = mentions_loosely_bound b t)
    /\ (forall b, mentions_loosely_bound_in_arguments b (to_generic t) = mentions_loosely_bound_in_arguments b t)
    /\ mutability_of env (to_generic t) = mutability_of env t
    /\ (forall b, bound_vars b t = true -> instantiate env b (to_generic t) = instantiate env b t).
Proof.
    induction k as [|k IH]; intros t Hk Ht.
    - destruct t as [| |[]| | |[[|] [|] p []]|]; simpl in Hk, Ht; try lia; try discriminate Ht.
      repeat split; try reflexivity. intros b Hb. simpl in Hb |- *. destruct (lookup_binding b p); [reflexivity|discriminate Hb].
    - destruct t as [m c args|n|[]|m msg|v o n|[[|] [|] p []]|cs]; simpl in Ht; try discriminate Ht.
      + assert (Hall: forall a, In a args -> (forall b, mentions_loosely_bound b (to_generic a) = mentions_loosely_bound b a)
            /\ (forall b, bound_vars b a = true -> instantiate env b (to_generic a) = instantiate env b a)).
        { intros a Ha. pose proof (vsize_below m c args a Ha).
          rewrite forallb_forall in Ht. destruct (IH a ltac:(lia) (Ht a Ha)) as [H1 [_ [_ H4]]]. auto. }
        repeat split; [intros b; simpl..|].
        * apply existsb_map_ext. intros a Ha. apply Hall, Ha.
        * apply existsb_map_ext. intros a Ha. apply Hall, Ha.
        * intros b Hb. simpl. rewrite map_map. f_equal. apply map_ext_in. intros a Ha. apply Hall; [exact Ha|].
          change (forallb (bound_vars b) args = true) in Hb. rewrite forallb_forall in Hb. exact (Hb a Ha).
      + simpl in Hk. destruct (IH n ltac:(lia) (proj2 (proj1 (andb_true_iff _ _) Ht))) as [H1 [H2 [H3 H4]]].
        repeat split; [intros; simpl; rewrite ?H1, ?H2, ?H3; reflexivity..|].
        intros b Hb. simpl. rewrite (H4 b Hb), ?H1, ?H2. reflexivity.
      + simpl in Hk. apply orb_true_iff in Ht.
        assert (Hn: (forall b, mentions_loosely_bound b (to_generic n) = mentions_loosely_bound b n)
            /\ (forall b, mentions_loosely_bound_in_arguments b (to_generic n) = mentions_loosely_bound_in_arguments b n)
            /\ mutability_of env (to_generic n) = mutability_of env n
            /\ (forall b, bound_vars b n = true -> instantiate env b (to_generic n) = instantiate env b n))
            by (destruct Ht as [Ht|Ht]; [exact (IH n ltac:(lia) Ht)|exact (nested_ref_facts n Ht)]).
        destruct Hn as [H1 [H2 [H3 H4]]].
        repeat split; [intros; simpl; rewrite ?H1, ?H2, ?H3; reflexivity..|].
        intros b Hb. simpl. rewrite (H4 b Hb), ?H1, ?H2. reflexivity.
      + repeat split; try reflexivity. intros b Hb. simpl in Hb |- *. destruct (lookup_binding b p); [reflexivity|discriminate Hb].
Qed.

Lemma instantiate_to_generic: forall b t, no_generics t = true -> bound_vars b t = true -> instantiate env b (to_generic t) = instantiate env b t.
Proof. intros b t H Hb. exact (proj2 (proj2 (proj2 (to_generic_facts (vsize t) t (le_n _) H))) b Hb). Qed.

(* Where the type parameters in place of the type variables are bound, so are the variables *)
Lemma bound_vars_of: forall b K s t, no_generics t = true -> bound_in env b K s (to_generic t) = true -> bound_vars b t = true.
Proof.
    intros b K s. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] Hn Hb; try reflexivity; try discriminate Hn.
    - simpl in Hn, Hb |- *. induction args as [|a args IHa]; [reflexivity|]. simpl in Hn, Hb |- *. apply andb_true_iff in Hn, Hb.
      rewrite (IH a (proj1 Hn) (proj1 Hb)), (IHa (proj2 Hn) (proj2 Hb)). reflexivity.
    - simpl in Hn, Hb |- *. apply andb_true_iff in Hn. exact (IH n (proj2 Hn) Hb).
    - simpl in Hn, Hb |- *. apply andb_true_iff in Hb. apply orb_true_iff in Hn. destruct Hn as [Hn|Hn]; [exact (IH n Hn (proj2 Hb))|].
      destruct Hb as [_ Hb]. clear IH.
      destruct n as [|[| | | | |[gm nn p []]|]| | | |[gm nn p []]|]; try discriminate Hn; cbn [to_generic bound_in] in Hb; cbn [bound_vars];
          destruct (binds_ref_some env wf b K s _ Hb) as [o1 [x1 [E _]]]; cbn [param_of] in E; rewrite E; reflexivity.
    - simpl. destruct (lookup_binding b p) as [a|] eqn:E; [reflexivity|]. change (bound_in env b K s (Generic (mkGenericRef gm nn p vs)) = true) in Hb.
      cbn [bound_in] in Hb. rewrite !andb_true_iff in Hb. destruct Hb as [[[Hr _] _] _]. unfold binds_ref in Hr. cbn [param_of] in Hr.
      rewrite E in Hr. discriminate Hr.
Qed.

Lemma mentions_to_generic: forall b t, no_generics t = true -> mentions_loosely_bound b (to_generic t) = mentions_loosely_bound b t.
Proof. intros b t H. exact (proj1 (to_generic_facts (vsize t) t (le_n _) H) b). Qed.

Lemma loose_to_generic: forall a, is_loose (to_generic a) = is_loose a.
Proof. intros [| | | |v o n| |]; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Supertypes of types with type variables                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Section Templates.

Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> is_type_argument y = true.

(* Templates are loose where they are instantiated with ys exactly where with ys mapped by a function
   that keeps type arguments loose or not *)
Lemma template_looseness_map: forall (f: EType -> EType),
    (forall y, In y ys -> is_loose (f y) = is_loose y) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        mentions_loosely_bound (bindings_of env sub (map f ys)) t = mentions_loosely_bound (bindings_of env sub ys) t)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        mentions_loosely_bound (bindings_of env sub (map f ys)) r = mentions_loosely_bound (bindings_of env sub ys) r).
Proof.
    intros f Hf k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        existsb (mentions_loosely_bound (bindings_of env sub (map f ys))) targs
        = existsb (mentions_loosely_bound (bindings_of env sub ys)) targs).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs]. apply existsb_ext_in.
      intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite !mentions_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite !mentions_nullable, !mentions_class. exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map f ys) i = Some (f y)) by (rewrite nth_error_map, Hy; reflexivity).
        rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub _ i p _ Hi Hy')).
        rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub ys i p y Hi Hy)).
        apply Hf. eapply nth_error_In. exact Hy.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn'].
Qed.

(* A template, instantiated with ys: with type variables as type parameters, it is instantiated with
   ys as type parameters; it has no type parameters but those in ys, and Nothing as bottom type if
   ys do *)
Lemma template_bridge: forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        to_generic (instantiate env (bindings_of env sub ys) t) = instantiate env (bindings_of env sub (map to_generic ys)) t
        /\ ((forall y, In y ys -> no_generics y = true) -> no_generics (instantiate env (bindings_of env sub ys) t) = true))
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        to_generic (instantiate env (bindings_of env sub ys) r) = instantiate env (bindings_of env sub (map to_generic ys)) r
        /\ ((forall y, In y ys -> no_generics y = true) -> no_generics (instantiate env (bindings_of env sub ys) r) = true)).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    set (bS := bindings_of env sub ys). set (bG := bindings_of env sub (map to_generic ys)).
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        to_generic (instantiate env bS (RootResolved m c targs)) = instantiate env bG (RootResolved m c targs)
        /\ ((forall y, In y ys -> no_generics y = true) -> no_generics (instantiate env bS (RootResolved m c targs)) = true)).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      assert (Hall: forall a, In a targs -> _) by (intros a Ha; pose proof (argument_depth_below m c targs a Ha);
          exact (IHa a ltac:(lia) (Htargs a Ha))).
      rewrite !instantiate_class. repeat split.
      - simpl. rewrite map_map. f_equal. apply map_ext_in. intros a Ha. apply (Hall a Ha).
      - intros Hng. change (forallb no_generics (map (instantiate env bS) targs) = true).
        apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        apply (Hall a Ha), Hng. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. destruct (Hroot m c targs ltac:(lia) Ht') as [H1 H2].
        rewrite instantiate_nullable_class, <- instantiate_class in *. rewrite (instantiate_nullable_class env bG), <- instantiate_class.
        repeat split.
        * simpl. f_equal. exact H1.
        * exact H2.
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map to_generic ys) i = Some (to_generic y)) by (rewrite nth_error_map, Hy; reflexivity).
        pose proof (Hys y (nth_error_In _ _ Hy)) as Hty.
        unfold bS, bG. rewrite (selects env wf sub ys p bp i y Hi Hy Hty).
        rewrite (selects env wf sub _ p bp i _ Hi Hy'); [|destruct y; try discriminate Hty; reflexivity].
        split; [reflexivity|]. intros H. apply H. eapply nth_error_In. exact Hy.
      + simpl in Hd. destruct (IHt n ltac:(lia) Hn') as [H1 H2].
        unfold bS, bG in *.
        rewrite (instantiate_template_argument env (bindings_of env sub ys) v o n Ho (template_shape env sub n Hn')).
        rewrite (instantiate_template_argument env (bindings_of env sub (map to_generic ys)) v o n Ho (template_shape env sub n Hn')).
        rewrite (proj1 (template_looseness_map to_generic (fun y _ => loose_to_generic y) (depth n)) n (le_n _) Hn').
        destruct (mentions_loosely_bound (bindings_of env sub ys) n); [destruct v|]; cbn [to_generic no_generics];
            rewrite ?H1; repeat split; try reflexivity; intros;
            first [apply H2; assumption|apply orb_true_iff; left; apply H2; assumption].
Qed.

(* A template, instantiated with types without type parameters, has none *)
Lemma template_closed: forall k, (forall y, In y ys -> closed y = true) ->
    (forall t, depth t <= k -> template_type env sub t = true -> closed (instantiate env (bindings_of env sub ys) t) = true)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> closed (instantiate env (bindings_of env sub ys) r) = true).
Proof.
    intros k Hc. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        closed (instantiate env (bindings_of env sub ys) (RootResolved m c targs)) = true).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs]. rewrite instantiate_class.
      change (forallb closed (map (instantiate env (bindings_of env sub ys)) targs) = true). apply forallb_forall.
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (argument_depth_below m c targs a Ha).
      apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class, <- instantiate_class.
        exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        rewrite (selects env wf sub ys p bp i y Hi Hy (Hys y (nth_error_In _ _ Hy))). apply Hc. eapply nth_error_In. exact Hy.
      + simpl in Hd. rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn')).
        destruct (mentions_loosely_bound _ n); [destruct v|]; cbn [closed]; rewrite Ho; cbn [negb andb];
            first [reflexivity | apply IHt; [lia|exact Hn']].
Qed.

(* A template, instantiated with type arguments of the fragment of Substitution.v, is of it *)
Lemma template_sfrag: (forall y, In y ys -> argument_sfrag env y = true) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        sfrag env (instantiate env (bindings_of env sub ys) t) = true)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        argument_sfrag env (instantiate env (bindings_of env sub ys) r) = true).
Proof.
    intros Hsf k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    set (bS := bindings_of env sub ys) in *.
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        sfrag env (RootResolved m c (map (instantiate env bS) targs)) = true).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      assert (Hall: forall a, In a targs -> argument_sfrag env (instantiate env bS a) = true).
      { intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha]. }
      simpl. rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
      destruct Ha' as [a [<- Ha]]. apply Hall, Ha. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite instantiate_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class.
        pose proof (Hroot m c targs ltac:(lia) Ht') as Hf.
        change ((is_class (RootResolved m c (map (instantiate env bS) targs)) || is_generic (RootResolved m c (map (instantiate env bS) targs)))
            && sfrag env (RootResolved m c (map (instantiate env bS) targs)) = true). rewrite Hf. reflexivity.
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        unfold bS. rewrite (selects env wf sub ys p bp i y Hi Hy (Hys y (nth_error_In _ _ Hy))).
        apply Hsf. eapply nth_error_In. exact Hy.
      + simpl in Hd. pose proof (IHt n ltac:(lia) Hn') as Hf.
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        destruct (mentions_loosely_bound bS n); [destruct v|]; simpl; rewrite ?Hf, ?(wf_nothing_has_no_type_parameters env wf); reflexivity.
Qed.

(* ... and with type arguments whose type variables made nullable are narrowed, has them narrowed *)
Lemma template_narrowed: (forall y, In y ys -> nullable_narrowed y = true) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> nullable_narrowed (instantiate env (bindings_of env sub ys) t) = true)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> nullable_narrowed (instantiate env (bindings_of env sub ys) r) = true).
Proof.
    intros Hny k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        nullable_narrowed (RootResolved m c (map (instantiate env (bindings_of env sub ys)) targs)) = true).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs].
      change (forallb nullable_narrowed (map (instantiate env (bindings_of env sub ys)) targs) = true). apply forallb_forall.
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (argument_depth_below m c targs a Ha).
      apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite instantiate_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class. exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        rewrite (selects env wf sub ys p bp i y Hi Hy (Hys y (nth_error_In _ _ Hy))). apply Hny. eapply nth_error_In. exact Hy.
      + simpl in Hd. rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn')).
        destruct (mentions_loosely_bound _ n); [destruct v|]; cbn [nullable_narrowed];
            first [reflexivity | apply IHt; [lia|exact Hn']].
Qed.

(* A template without contravariance, instantiated with type arguments without it, is without it: a type
   argument widened where a type parameter in it is bound loosely becomes out-variant *)
Lemma template_without_contravariance: forall k, (forall y, In y ys -> without_contravariance y = true) ->
    (forall t, depth t <= k -> template_type env sub t = true -> without_contravariance t = true ->
        without_contravariance (instantiate env (bindings_of env sub ys) t) = true)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> without_contravariance r = true ->
        without_contravariance (instantiate env (bindings_of env sub ys) r) = true).
Proof.
    intros k Hc. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true -> without_contravariance (RootResolved m c targs) = true ->
        without_contravariance (instantiate env (bindings_of env sub ys) (RootResolved m c targs)) = true).
    { intros m c targs Hd Ht Hw. destruct (root_template env sub m c targs Ht) as [_ Htargs]. rewrite instantiate_class.
      change (forallb without_contravariance targs = true) in Hw. rewrite forallb_forall in Hw.
      change (forallb without_contravariance (map (instantiate env (bindings_of env sub ys)) targs) = true). apply forallb_forall.
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (argument_depth_below m c targs a Ha).
      apply IHa; [lia|apply Htargs, Ha|apply Hw, Ha]. }
    split.
    - intros t Hd Ht Hw. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + exact (Hroot m c targs Hd Ht Hw).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class, <- instantiate_class.
        exact (Hroot m c targs ltac:(lia) Ht' Hw).
    - intros r Hd Hr Hw. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        rewrite (selects env wf sub ys p bp i y Hi Hy (Hys y (nth_error_In _ _ Hy))). apply Hc. eapply nth_error_In. exact Hy.
      + simpl in Hd. cbn [without_contravariance] in Hw. apply andb_true_iff in Hw. destruct Hw as [Hv Hwn].
        assert (Hn: without_contravariance (instantiate env (bindings_of env sub ys) n) = true) by (apply IHt; [lia|exact Hn'|exact Hwn]).
        rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn')).
        destruct (mentions_loosely_bound _ n); [destruct v; [| simpl in Hv; discriminate Hv |]|]; cbn [without_contravariance];
            rewrite Hn, ?andb_true_r; first [reflexivity | exact Hv].
Qed.

End Templates.

Lemma supertype_arguments_narrowed: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> is_type_argument y = true) ->
    (forall y, In y ys -> nullable_narrowed y = true) ->
    forall a, In a (parameterized_supertype_arguments env sub ys super) -> nullable_narrowed a = true.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys Hny a Ha.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
    exact (proj2 (template_narrowed sub ys Hl Hys Hny (argument_depth r)) r (le_n _) (Ht r Hr)).
Qed.

(* The type arguments of a supertype, normalized from those of a subclass with type variables, with
   type variables as type parameters *)
Lemma supertype_arguments_to_generic: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> is_type_argument y = true) ->
    parameterized_supertype_arguments env sub (map to_generic ys) super = map to_generic (parameterized_supertype_arguments env sub ys super)
    /\ ((forall y, In y ys -> no_generics y = true) ->
        forall a, In a (parameterized_supertype_arguments env sub ys super) -> no_generics a = true)
    /\ ((forall y, In y ys -> closed y = true) ->
        forall a, In a (parameterized_supertype_arguments env sub ys super) -> closed a = true).
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite !parameterized_supertype_arguments_eq. repeat split.
    - rewrite map_map. apply map_ext_in. intros r Hr. symmetry.
      exact (proj1 (proj2 (template_bridge sub ys Hl Hys (argument_depth r)) r (le_n _) (Ht r Hr))).
    - intros Hng a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      exact (proj2 (proj2 (template_bridge sub ys Hl Hys (argument_depth r)) r (le_n _) (Ht r Hr)) Hng).
    - intros Hc a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      exact (proj2 (template_closed sub ys Hl Hys (argument_depth r) Hc) r (le_n _) (Ht r Hr)).
Qed.

(* The type arguments of a supertype, normalized from those of a subclass without contravariance, are
   without it, where those of supertypes are *)
Lemma supertype_arguments_without_contravariance: forall sub super ys,
    supertypes_without_contravariance env ->
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> is_type_argument y = true) ->
    (forall y, In y ys -> without_contravariance y = true) ->
    forall a, In a (parameterized_supertype_arguments env sub ys super) -> without_contravariance a = true.
Proof.
    intros sub super ys Hsw Hne Hn Hbase Hl Hys Hw a Ha.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
    pose proof (Hsw sub super) as Hr'. rewrite forallb_forall in Hr'.
    exact (proj2 (template_without_contravariance sub ys Hl Hys (argument_depth r) Hw) r (le_n _) (Ht r Hr) (Hr' r Hr)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The fragment                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Definition argument_ifrag (a: EType): bool := match a with TypeArgument _ _ n => nfrag n | _ => false end.

Lemma argument_ifrag_parts: forall a, argument_ifrag a = true ->
    is_type_argument a = true /\ argument_sfrag env (to_generic a) = true /\ no_generics a = true.
Proof.
    intros [| | | |v o n| |] H; try discriminate H. unfold argument_ifrag, nfrag in H. apply andb_true_iff in H.
    destruct H as [H1 H2]. split; [reflexivity|]. split; [exact H1|exact H2].
Qed.

Lemma argument_ifrag_intro: forall a, is_type_argument a = true -> argument_sfrag env (to_generic a) = true -> no_generics a = true ->
    argument_ifrag a = true.
Proof. intros [| | | |v o n| |] H1 H2 H3; try discriminate H1. unfold argument_ifrag, nfrag. simpl in H2, H3. rewrite H2, H3. reflexivity. Qed.

Lemma ifrag_nfrag: forall t, ifrag t = true -> nfrag t = true.
Proof. intros t H. unfold ifrag, nfrag in *. apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1, H2. reflexivity. Qed.

Lemma nfrag_sfrag: forall t, nfrag t = true -> sfrag env (to_generic t) = true.
Proof. intros t H. unfold nfrag in H. apply andb_true_iff in H. apply H. Qed.

Lemma nfrag_argument: forall v o t, nfrag t = true -> no_generics (TypeArgument v o t) = true.
Proof. intros v o t H. unfold nfrag in H. apply andb_true_iff in H. apply H. Qed.

(* A type argument is of the types of the parameters, or a type variable of a mutability given to
   it, narrowed or made nullable *)
Lemma nfrag_cases: forall t, nfrag t = true -> ifrag t = true
    \/ (exists gm nn p, (t = TypeVariable (mkGenericRef gm nn p []) \/ t = Nullable (TypeVariable (mkGenericRef gm nn p [])))
        /\ sfrag env (Generic (mkGenericRef gm nn p [])) = true).
Proof.
    intros t H. unfold nfrag in H. apply andb_true_iff in H. destruct H as [Hs Hn]. apply orb_true_iff in Hn.
    destruct Hn as [Hn|Hn]; [left; unfold ifrag; rewrite Hs, Hn; reflexivity|right].
    destruct t as [|[| | | | |[gm nn p []]|]| | | |[gm nn p []]|]; try discriminate Hn; exists gm, nn, p.
    - split; [right; reflexivity|]. cbn [to_generic sfrag] in Hs. apply andb_true_iff in Hs. exact (proj2 Hs).
    - split; [left; reflexivity|exact Hs].
Qed.

Lemma ifrag_cases: forall t, ifrag t = true ->
    (exists m c args, t = RootResolved m c args /\ class_eqb c nothing = false
        /\ length args = length (parameter_ids env c) /\ forall a, In a args -> argument_ifrag a = true)
    \/ (exists m, t = RootResolved m nothing [])
    \/ (exists m c args, t = Nullable (RootResolved m c args) /\ ifrag (RootResolved m c args) = true)
    \/ (exists p, t = TypeVariable (mkGenericRef None false p []) /\ sfrag env (Generic (mkGenericRef None false p [])) = true).
Proof.
    intros t H. unfold ifrag in H. apply andb_true_iff in H. destruct H as [Hs Hn].
    destruct t as [m c args|n|[gm0 nn0 p0 bnd0]|m msg|v o n|[[gm|] [|] p [|w ws]]|cs]; simpl in Hn; try discriminate Hn;
        try (simpl in Hs; discriminate Hs).
    - destruct (sfrag_cases env wf _ Hs) as [[m' [c' [args' [Heq [Hc [Hl Hargs]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
          try discriminate Heq.
      + injection Heq as <- <- Hargs'. left. exists m, c, args. split; [reflexivity|]. split; [exact Hc|].
        split; [rewrite <- Hargs', length_map in Hl; exact Hl|].
        intros a Ha. assert (Ha': argument_sfrag env (to_generic a) = true)
            by (apply Hargs; rewrite <- Hargs'; apply in_map, Ha).
        rewrite forallb_forall in Hn. pose proof (Hn a Ha) as Hna.
        apply argument_ifrag_intro; [|exact Ha'|exact Hna]. destruct a; try discriminate Ha'. reflexivity.
      + injection Heq as _ -> Hargs'. destruct args; [|discriminate Hargs'].
        right. left. exists m. reflexivity.
    - change ((is_class (to_generic n) || is_generic (to_generic n)) && sfrag env (to_generic n) = true) in Hs.
      apply andb_true_iff in Hs. destruct Hs as [Hc Hs].
      destruct n as [m c args| | | | | |]; try discriminate Hn.
      apply andb_true_iff in Hn. destruct Hn as [_ Hn].
      right. right. left. exists m, c, args. split; [reflexivity|]. unfold ifrag. rewrite Hs, Hn. reflexivity.
    - right. right. right. exists p. split; [reflexivity|exact Hs].
Qed.

Lemma ifrag_root_args: forall m c args, ifrag (RootResolved m c args) = true ->
    no_generics (RootResolved m c args) = true /\ forall a, In a args -> no_generics a = true.
Proof.
    intros m c args H. unfold ifrag in H. apply andb_true_iff in H. destruct H as [_ H]. split; [exact H|].
    change (forallb no_generics args = true) in H. apply forallb_forall, H.
Qed.

Lemma ifrag_no_generics: forall t, ifrag t = true -> no_generics t = true.
Proof. intros t H. unfold ifrag in H. apply andb_true_iff in H. apply H. Qed.

Lemma ifrag_sfrag: forall t, ifrag t = true -> sfrag env (to_generic t) = true.
Proof. intros t H. unfold ifrag in H. apply andb_true_iff in H. apply H. Qed.

Lemma bound_vars_nfrag: forall b K s t, nfrag t = true -> bound_in env b K s (to_generic t) = true -> bound_vars b t = true.
Proof.
    intros b K s t H Hb. destruct (nfrag_cases t H) as [H'|[gm [nn [p [[-> | ->] _]]]]].
    - exact (bound_vars_of b K s t (ifrag_no_generics t H') Hb).
    - cbn [to_generic] in Hb. destruct (binds_ref_some env wf b K s _ Hb) as [o [x [E _]]]. cbn [param_of] in E.
      cbn [bound_vars]. rewrite E. reflexivity.
    - cbn [to_generic bound_in] in Hb. destruct (binds_ref_some env wf b K s _ Hb) as [o [x [E _]]]. cbn [param_of] in E.
      cbn [bound_vars]. rewrite E. reflexivity.
Qed.

Lemma pfrag_cases: forall t, pfrag t = true -> ifrag t = true
    \/ (exists gm nn p, t = TypeVariable (mkGenericRef gm nn p [])
        /\ sfrag env (Generic (mkGenericRef gm nn p [])) = true /\ sfrag env (Generic (mkGenericRef None false p [])) = true)
    \/ (exists gm nn p, t = Nullable (TypeVariable (mkGenericRef gm nn p []))
        /\ sfrag env (Generic (mkGenericRef gm nn p [])) = true /\ sfrag env (Generic (mkGenericRef None false p [])) = true).
Proof.
    intros t H. unfold pfrag in H. apply orb_true_iff in H. destruct H as [H|H]; [left; exact H|right].
    destruct t as [| [| | | | |[gm nn p [|w ws]]|] | | | |[gm nn p [|w ws]]|]; try discriminate H;
        apply andb_true_iff in H; destruct H as [H1 H2]; [right|left]; exists gm, nn, p; auto.
Qed.

Lemma pgeneric_ifrag: forall t, ifrag t = true -> pgeneric t = to_generic t.
Proof.
    intros t H. destruct (ifrag_cases t H) as [[m [c [args [-> _]]]]|[[m_bot ->]|[[m [c [args [-> _]]]]|[p [-> _]]]]]; reflexivity.
Qed.

Lemma compfrag_cases: forall t, compfrag t = true -> ifrag t = true
    \/ (exists gm nn p, t = TypeVariable (mkGenericRef gm nn p [])
        /\ sfrag env (Generic (mkGenericRef gm nn p [])) = true /\ sfrag env (Generic (mkGenericRef None false p [])) = true).
Proof.
    intros t H. unfold compfrag in H. apply orb_true_iff in H. destruct H as [H|H]; [left; exact H|right].
    destruct t as [m c args|n|g|me msg|v o n|[gm nn p [|w ws]]|cs]; try discriminate H.
    exists gm, nn, p. unfold reference_variable in H. apply andb_true_iff in H. split; [reflexivity|exact H].
Qed.

Lemma compfrag_pfrag: forall t, compfrag t = true -> pfrag t = true.
Proof.
    intros t H. destruct (compfrag_cases t H) as [H'|[gm [nn [p [-> Hs]]]]]; unfold pfrag; [rewrite H'; reflexivity|].
    unfold reference_variable. destruct Hs as [Hs1 Hs2]. rewrite Hs1, Hs2, orb_true_r. reflexivity.
Qed.

Lemma compfrag_ifrag: forall t, compfrag t = true -> is_type_variable t = false -> ifrag t = true.
Proof. intros t H Hv. destruct (compfrag_cases t H) as [H'|[gm [nn [p [-> _]]]]]; [exact H'|discriminate Hv]. Qed.

(* A type variable component of a mutability given to it is assigned as no more than that *)
Lemma compfrag_given: forall gm nn p m, compfrag (TypeVariable (mkGenericRef gm nn p [])) = true -> gm = Some m ->
    Model.is_subtype_of (assignment_mutability env (TypeVariable (mkGenericRef gm nn p []))) m = true.
Proof.
    intros gm nn p m H ->. destruct (compfrag_cases _ H) as [Hi|[gm' [nn' [p' [E [Hs _]]]]]].
    - unfold ifrag in Hi. cbn [no_generics] in Hi. rewrite andb_false_r in Hi. discriminate Hi.
    - injection E as <- <- <-. rewrite (assignment_mutability_type_variable env ranked).
      rewrite (sfrag_generic env) in Hs. unfold as_written in Hs. cbn [given_mutability is_narrowed] in Hs.
      rewrite !andb_true_iff in Hs. destruct Hs as [[[[Hw _] _] _] _]. exact Hw.
Qed.

Lemma pfrag_sfrag: forall t, pfrag t = true -> sfrag env (pgeneric t) = true.
Proof.
    intros t H. destruct (pfrag_cases t H) as [H'|[[gm [nn [p [-> [_ Hs]]]]]|[gm [nn [p [-> [_ Hs]]]]]]]; [|exact Hs|exact Hs].
    rewrite (pgeneric_ifrag t H'). exact (ifrag_sfrag t H').
Qed.

Lemma ifrag_pfrag: forall t, ifrag t = true -> pfrag t = true.
Proof. intros t H. unfold pfrag. rewrite H. reflexivity. Qed.

(* The components of an intersection that is the type of a parameter (`x: T & A`, `x: T? & A?`), as
   ofComponents builds it: of compfrag, of the fragment, assigned as one mutability *)
Definition param_components (cs: list EType): bool :=
    forallb compfrag cs && components_sfrag env (map to_generic cs)
    && forallb (fun c => Mutability_beq (assignment_mutability env c) (assignment_mutability env (Intersection cs))) cs.

(* The types of the parameters: pfrag, and intersections, nullable or not *)
Definition qfrag (t: EType): bool :=
    pfrag t || match t with Intersection cs | Nullable (Intersection cs) => param_components cs | _ => false end.

Lemma qfrag_cases: forall t, qfrag t = true -> pfrag t = true
    \/ exists cs, (t = Intersection cs \/ t = Nullable (Intersection cs)) /\ (forall C, In C cs -> compfrag C = true)
        /\ components_sfrag env (map to_generic cs) = true
        /\ forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs).
Proof.
    intros t H. unfold qfrag in H. apply orb_true_iff in H. destruct H as [H|H]; [left; exact H|right].
    assert (Hcs: forall cs, param_components cs = true -> (forall C, In C cs -> compfrag C = true)
        /\ components_sfrag env (map to_generic cs) = true
        /\ forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)).
    { intros cs Hp. unfold param_components in Hp. apply andb_true_iff in Hp. destruct Hp as [Hp Hu]. apply andb_true_iff in Hp.
      destruct Hp as [Hc Hs]. rewrite forallb_forall in Hc, Hu. split; [exact Hc|]. split; [exact Hs|].
      intros C HC. apply internal_Mutability_dec_bl, Hu, HC. }
    destruct t as [m c args|[| | | | | |cs]|g|me msg|v o n|g|cs]; try discriminate H;
        exists cs; [split; [right; reflexivity|exact (Hcs cs H)]|split; [left; reflexivity|exact (Hcs cs H)]].
Qed.

Lemma pfrag_qfrag: forall t, pfrag t = true -> qfrag t = true.
Proof. intros t H. unfold qfrag. rewrite H. reflexivity. Qed.

Lemma qfrag_tfrag: forall t, qfrag t = true -> tfrag env (pgeneric t) = true.
Proof.
    intros t H. destruct (qfrag_cases t H) as [Hp|[cs [[->| ->] [_ [Hs _]]]]]; [exact (sfrag_tfrag env _ (pfrag_sfrag t Hp))|exact Hs|exact Hs].
Qed.

(* A component of an intersection that keeps the nullability of its components, as the type of a
   parameter (`x: A? & T` with `T : Any?`): a nullable class type, or a type variable, not narrowed, whose
   bound may be null *)
Definition kept_param_component (C: EType): bool :=
    match C with
    | Nullable (RootResolved _ _ _) => ifrag C
    | TypeVariable (mkGenericRef _ false p []) => reference_variable C && is_nullable env (Generic (mkGenericRef None false p []))
    | _ => false
    end.

(* Such an intersection, as ofComponents makes it where each component may be null but not each is `X?` *)
Definition kept_param_components (cs: list EType): bool :=
    Nat.leb 2 (length cs) && forallb kept_param_component cs && negb (forallb is_nullable_type cs).

(* The types of the parameters of the theorems outside generic code: qfrag, and such intersections *)
Definition kqfrag (t: EType): bool :=
    qfrag t || match t with Intersection cs => kept_param_components cs | _ => false end.

Lemma kqfrag_cases: forall t, kqfrag t = true -> qfrag t = true \/ exists cs, t = Intersection cs /\ kept_param_components cs = true.
Proof.
    intros t H. unfold kqfrag in H. apply orb_true_iff in H. destruct H as [H|H]; [left; exact H|right].
    destruct t; try discriminate H. eexists; split; [reflexivity|exact H].
Qed.

Lemma qfrag_kqfrag: forall t, qfrag t = true -> kqfrag t = true.
Proof. intros t H. unfold kqfrag. rewrite H. reflexivity. Qed.

(* The shapes of the components of an intersection as the type of a parameter *)
Definition param_shape (C: EType): Prop :=
    (exists m cl args, C = RootResolved m cl args \/ C = Nullable (RootResolved m cl args))
    \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q [])).

Lemma kept_param_facts: forall cs, kept_param_components cs = true ->
    2 <= length cs /\ forall C, In C cs -> compfrag C = true /\ param_shape C /\ sfrag env (to_generic C) = true.
Proof.
    intros cs H. unfold kept_param_components in H. apply andb_true_iff in H. destruct H as [H _]. apply andb_true_iff in H.
    destruct H as [Hl H]. rewrite forallb_forall in H. split; [apply Nat.leb_le, Hl|]. intros C HC. pose proof (H C HC) as Hk.
    destruct C as [m0 c0 a0|[m cl args| | | | | |]|g|me msg|v o n|[gm [] p [|w ws]]|cs'];
        cbn [kept_param_component] in Hk; try discriminate Hk.
    - split; [unfold compfrag; rewrite Hk; reflexivity|]. split; [left; exists m, cl, args; right; reflexivity|].
      exact (ifrag_sfrag _ Hk).
    - apply andb_true_iff in Hk. destruct Hk as [Hr _].
      split; [unfold compfrag; rewrite Hr, orb_true_r; reflexivity|]. split; [right; exists gm, false, p; reflexivity|].
      unfold reference_variable in Hr. apply andb_true_iff in Hr. exact (proj1 Hr).
Qed.

(* Either way, an intersection, nullable or not, has components of compfrag *)
Lemma kqfrag_components: forall t, kqfrag t = true -> pfrag t = true
    \/ exists cs, (t = Intersection cs \/ t = Nullable (Intersection cs)) /\ forall C, In C cs -> compfrag C = true.
Proof.
    intros t H. destruct (kqfrag_cases t H) as [HQ|[cs [-> Hk]]].
    - destruct (qfrag_cases t HQ) as [Hp|[cs [EP [HSi _]]]]; [left; exact Hp|right; exists cs; exact (conj EP HSi)].
    - right. exists cs. split; [left; reflexivity|]. intros C HC. exact (proj1 (proj2 (kept_param_facts cs Hk) C HC)).
Qed.

Lemma inst_ref_apply: forall gm nn p vs x, inst_ref env (mkGenericRef gm nn p vs) x = ref_apply gm nn x.
Proof. intros [m|] [] p vs x; reflexivity. Qed.

(* A narrowed reference of the fragment is non-null *)
Lemma narrowed_not_nullable: forall gm p, sfrag env (Generic (mkGenericRef gm true p [])) = true ->
    is_nullable env (TypeVariable (mkGenericRef gm true p [])) = false.
Proof.
    intros gm p H. destruct (sfrag_cases env wf _ H) as [[? [? [? [E _]]]]|[[m_bot E]|[[? [? [? [E _]]]]|[[g [E Hg]]|[? [E _]]]]]];
        try discriminate E.
    injection E as <-. destruct Hg as [_ [Hw _]]. unfold as_written in Hw. cbn [given_mutability is_narrowed] in Hw.
    apply andb_true_iff in Hw. destruct Hw as [_ Hw]. cbn [negb orb] in Hw.
    rewrite (is_nullable_type_variable env ranked). apply negb_true_iff. exact Hw.
Qed.

Lemma variable_condition: forall (gf nA nS nS0: bool) (K: option Unification) u, (nS = true -> nS0 = true) ->
    (if gf && (negb nA || nS) then K else Some Failed) = Some (Ongoing u) ->
    (if true && (negb nA || nS0) then K else Some Failed) = Some (Ongoing u) /\ gf = true /\ (nA = true -> nS = true).
Proof. intros [] [] [] [] K u Hs H; cbn in H |- *; try discriminate H; auto. specialize (Hs eq_refl). discriminate Hs. Qed.

Lemma variable_condition_nullable: forall (gf nS nS0: bool) (K: option Unification) u, (nS = true -> nS0 = true) ->
    (if negb gf then Some Failed else if nS then K else Some Failed) = Some (Ongoing u) ->
    (if negb true then Some Failed else if nS0 then K else Some Failed) = Some (Ongoing u) /\ gf = true /\ nS = true.
Proof. intros [] [] [] K u Hs H; cbn in H |- *; try discriminate H; auto. specialize (Hs eq_refl). discriminate Hs. Qed.

(* A type variable of a mutability given to it, narrowed or not, takes what the plain variable takes,
   where it fits that mutability, and is nullable where what it takes is *)
Lemma unify_variable_given: forall n gm nn p A s u, match A with Error _ _ | TypeVariable _ => False | _ => True end ->
    unify env (S n) (TypeVariable (mkGenericRef gm nn p [])) A (Ongoing s) = Some (Ongoing u) ->
    unify env (S n) (TypeVariable (mkGenericRef None false p [])) A (Ongoing s) = Some (Ongoing u)
    /\ (forall m, gm = Some m -> Model.is_subtype_of (assignee_mutability env A) m = true)
    /\ (is_nullable env A = true -> is_nullable env (TypeVariable (mkGenericRef gm nn p [])) = true).
Proof.
    intros n gm nn p A s u HA H.
    assert (Hself: is_nullable env (TypeVariable (mkGenericRef gm nn p [])) = true ->
        is_nullable env (TypeVariable (mkGenericRef None false p [])) = true).
    { rewrite !(is_nullable_type_variable env ranked), !(effective_bound_eq env ranked).
      cbn [with_type_variables variables_of given_mutability is_narrowed param_of]. intros E.
      destruct (is_nullable env (parameter_bound env p)) eqn:Eb; [reflexivity|]. exfalso.
      destruct gm as [m|]; destruct nn.
      - rewrite (proj2 (proj2 (with_mutability_keeps env ranked m _))), (without_null_unchanged env _ Eb), Eb in E. discriminate E.
      - rewrite (proj1 (proj2 (with_mutability_keeps env ranked m _))), Eb in E. discriminate E.
      - rewrite (without_null_unchanged env _ Eb), Eb in E. discriminate E.
      - rewrite Eb in E. discriminate E. }
    cbn [unify unify_step unify_type_variable] in H |- *.
    destruct A as [ma ca aa|an|ga|me msg|va oa na|ga|cs]; try contradiction.
    2: { destruct (variable_condition_nullable _ _ _ _ _ Hself H) as [H1 [H2 H3]].
         split; [exact H1|]. split; [intros m0 Em0; subst gm; exact H2|intros _; exact H3]. }
    all: destruct (variable_condition _ _ _ _ _ _ Hself H) as [H1 [H2 H3]];
        (split; [exact H1|]); (split; [intros m0 Em0; subst gm; exact H2|exact H3]).
Qed.

(* A nullable type takes a class type where what it wraps takes the class type without null *)
Lemma unify_rewrap_target: forall f x A s r, in_fragment env A = true ->
    unify env f x (without_null env A) (Ongoing s) = Some r -> unify env (S f) (rewrap_nullable x) A (Ongoing s) = Some r.
Proof.
    intros f x A s r HA H.
    assert (Hy: forall y A', unify env f (Nullable y) A' (Ongoing s) = Some r -> is_class A' = true -> unify env f y A' (Ongoing s) = Some r).
    { intros y [m c args| | | | | |] H' Hc; try discriminate Hc. destruct f as [|f]; [discriminate H'|].
      rewrite unify_nullable_class in H'. apply (unify_fuel_monotone env f (S f)); [lia|exact H']. }
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]].
    - change (without_null env (RootResolved m c args)) with (RootResolved m c args) in H.
      destruct x as [| y | | | | |]; cbn [rewrap_nullable]; rewrite unify_nullable_class; try exact H. exact (Hy y _ H eq_refl).
    - change (without_null env (Nullable (RootResolved m c args))) with (RootResolved m c args) in H.
      destruct x as [| y | | | | |]; cbn [rewrap_nullable]; rewrite unify_nullable_nullable; try exact H. exact (Hy y _ H eq_refl).
Qed.

(* What a class type takes, it takes with a mutability given to it, and without null, where that fits *)
Lemma class_reference_takes: forall f gm (nn: bool) x A s, in_fragment env x = true -> in_fragment env A = true ->
    (forall m, gm = Some m -> Model.is_subtype_of (assignment_mutability env A) m = true) ->
    (nn = true -> is_nullable env A = false) ->
    unify env f x A (Ongoing s) = Some (Ongoing s) -> unify env f (ref_apply gm nn x) A (Ongoing s) = Some (Ongoing s).
Proof.
    intros f gm nn x A s Hx HA Hgm Hnn H.
    assert (Hown: Model.is_subtype_of (assignment_mutability env x) (mutability_of env x) = true).
    { destruct (fragment_cases env x Hx) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; cbn [assignment_mutability mutability_of];
          destruct (is_const (declaration_of env c)); first [reflexivity|apply mutability_is_subtype_of_refl]. }
    set (y := match gm with Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x | None => x end).
    assert (Hy: in_fragment env y = true /\ unify env f y A (Ongoing s) = Some (Ongoing s)).
    { unfold y. destruct gm as [m|]; [|exact (conj Hx H)].
      split; [exact (in_fragment_with_mutability env _ x Hx)|].
      apply (accepts_with_mutability env f _ x A s s Hx HA); [|exact H].
      apply intersect_mutability_greatest; [|exact (Hgm m eq_refl)].
      exact (mutability_trans _ _ _ (accepted_mutability_classes env f x A s s Hx HA H) Hown). }
    unfold ref_apply. cbn zeta. fold y. destruct nn; [|exact (proj2 Hy)].
    rewrite <- (without_null_non_null env A HA (Hnn eq_refl)). exact (unify_without_null env f y A s s (proj1 Hy) HA (proj2 Hy)).
Qed.

(* What is assignable to a class type, the class type with a mutability given to it, or without null,
   is assignable to *)
Lemma reference_takes_assignee: forall f gm (nn: bool) x A s, in_fragment env x = true -> in_fragment env A = true ->
    unify env f A x (Ongoing s) = Some (Ongoing s) -> unify env f A (ref_apply gm nn x) (Ongoing s) = Some (Ongoing s).
Proof.
    intros f gm nn x A s Hx HA H.
    set (y := match gm with Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x | None => x end).
    assert (Hy: in_fragment env y = true /\ unify env f A y (Ongoing s) = Some (Ongoing s)).
    { unfold y. destruct gm as [m|]; [|exact (conj Hx H)].
      split; [exact (in_fragment_with_mutability env _ x Hx)|].
      apply (unify_remut env f A A x _ s s (remut_refl env A HA) (remut_with_mutability env _ x Hx)); [|exact H].
      apply (mutability_trans _ _ _ (with_mutability_below env _ x Hx (intersect_mutability_left _ _))).
      exact (accepted_mutability_classes env f A x s s HA Hx H). }
    unfold ref_apply. cbn zeta. fold y. destruct nn; [|exact (proj2 Hy)].
    exact (unify_without_null_assignee env f A y s s HA (proj1 Hy) (proj2 Hy)).
Qed.

(* What a class type takes, it takes of a mutability given to both, and without null on both sides *)
Lemma class_reference_within: forall f gm (nn: bool) x B s, in_fragment env x = true -> in_fragment env B = true ->
    unify env f B x (Ongoing s) = Some (Ongoing s) -> unify env f (bound_apply gm nn B) (ref_apply gm nn x) (Ongoing s) = Some (Ongoing s).
Proof.
    intros f gm nn x B s Hx HB H.
    set (y := match gm with Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x | None => x end).
    set (B' := match gm with Some m => with_mutability env m B | None => B end).
    assert (Hy: in_fragment env y = true /\ in_fragment env B' = true /\ unify env f B' y (Ongoing s) = Some (Ongoing s)).
    { unfold y, B'. destruct gm as [m|]; [|exact (conj Hx (conj HB H))].
      split; [exact (in_fragment_with_mutability env _ x Hx)|]. split; [exact (in_fragment_with_mutability env _ B HB)|].
      apply (unify_remut env f B _ x _ s s (remut_with_mutability env m B HB) (remut_with_mutability env _ x Hx)); [|exact H].
      pose proof (accepted_mutability_classes env f B x s s HB Hx H) as Hax.
      destruct (fragment_cases env x Hx) as [[mx [cx [ax ->]]]|[mx [cx [ax [-> _]]]]];
      destruct (fragment_cases env B HB) as [[mb [cb [ab ->]]]|[mb [cb [ab [-> _]]]]];
          cbn [with_mutability rewrap_nullable assignment_mutability mutability_of] in Hax |- *;
          destruct (is_const (declaration_of env cx)), (is_const (declaration_of env cb));
          destruct mx as [[]|], mb as [[]|], m; cbn in Hax |- *; first [reflexivity|discriminate Hax]. }
    destruct Hy as [Hy [HB' Hu]]. unfold bound_apply, ref_apply. cbn zeta. fold y B'. destruct nn; [|exact Hu].
    exact (unify_without_null env f B' y s s HB' Hy Hu).
Qed.

Lemma bound_apply_in_fragment: forall gm nn x, in_fragment env x = true -> in_fragment env (bound_apply gm nn x) = true.
Proof.
    intros [m|] [] x Hx; unfold bound_apply; cbn zeta; first [apply (in_fragment_without_null env)|idtac];
        first [apply (in_fragment_with_mutability env)|idtac]; exact Hx.
Qed.

Lemma ref_apply_in_fragment: forall gm nn x, in_fragment env x = true -> in_fragment env (ref_apply gm nn x) = true.
Proof.
    intros [m|] [] x Hx; unfold ref_apply; cbn zeta; first [apply (in_fragment_without_null env)|idtac];
        first [apply (in_fragment_with_mutability env)|idtac]; exact Hx.
Qed.

(* The type arguments of a supertype, of type arguments of the fragment *)
Lemma supertype_arguments_ifrag: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> argument_ifrag y = true) ->
    forall a, In a (parameterized_supertype_arguments env sub ys super) -> argument_ifrag a = true.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys a Ha.
    assert (Hta: forall y, In y ys -> is_type_argument y = true)
        by (intros y Hy; pose proof (Hys y Hy) as E; destruct y; try discriminate E; reflexivity).
    assert (Hng: forall y, In y ys -> no_generics y = true)
        by (intros y Hy; exact (proj2 (proj2 (argument_ifrag_parts y (Hys y Hy))))).
    destruct (supertype_arguments_to_generic sub super ys Hne Hn Hbase Hl Hta) as [Htg [Hng' _]].
    assert (Hl': length (map to_generic ys) = length (parameter_ids env sub)) by (rewrite length_map; exact Hl).
    assert (Hta': forall y, In y (map to_generic ys) -> is_type_argument y = true).
    { intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. pose proof (Hta y' Hy') as E. destruct y'; try discriminate E. reflexivity. }
    assert (Hsf: forall y, In y (map to_generic ys) -> argument_sfrag env y = true).
    { intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. exact (proj1 (proj2 (argument_ifrag_parts y' (Hys y' Hy')))). }
    assert (Hs: argument_sfrag env (to_generic a) = true).
    { assert (Hin: In (to_generic a) (parameterized_supertype_arguments env sub (map to_generic ys) super))
          by (rewrite Htg; apply in_map, Ha).
      destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
      rewrite parameterized_supertype_arguments_eq in Hin. apply in_map_iff in Hin. destruct Hin as [r [<- Hr]].
      exact (proj2 (template_sfrag sub (map to_generic ys) Hl' Hta' Hsf (argument_depth r)) r (le_n _) (Ht r Hr)). }
    pose proof (Hng' Hng a Ha) as Hna.
    apply argument_ifrag_intro; [destruct a; try discriminate Hs; reflexivity|exact Hs|exact Hna].
Qed.

Lemma afrag_in_fragment: forall t, afrag t = true -> in_fragment env t = true.
Proof. intros t H. exact H. Qed.

(* The without-null form of a type of the arguments, as unify takes it for a nullable target *)
Lemma without_null_afrag: forall A, afrag A = true -> afrag (without_null env A) = true /\ closed (without_null env A) = closed A.
Proof.
    intros A HA.
    destruct (fragment_cases env A HA) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HR]]]]]; [exact (conj HA eq_refl)|].
    split; [|reflexivity]. exact HR.
Qed.

Lemma without_null_without_contravariance: forall A, afrag A = true -> without_contravariance A = true ->
    without_contravariance (without_null env A) = true.
Proof. intros A HA Hw. destruct (fragment_cases env A HA) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]]; exact Hw. Qed.

(* A type of the arguments, as a reference to a type parameter bound to it makes it *)
Lemma ref_apply_afrag: forall gm nn x, afrag x = true -> afrag (ref_apply gm nn x) = true /\ closed (ref_apply gm nn x) = closed x.
Proof.
    intros gm nn x Hx. pose proof (afrag_in_fragment x Hx) as Hf.
    assert (Hm: forall k, afrag (with_mutability env (intersect_mutability (mutability_of env x) k) x) = true
        /\ closed (with_mutability env (intersect_mutability (mutability_of env x) k) x) = closed x).
    { intros k. unfold afrag. split; [exact (in_fragment_with_mutability env _ x Hf)|].
      destruct (fragment_cases env x Hf) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
          cbn [with_mutability rewrap_nullable mutability_of closed]; reflexivity. }
    destruct gm as [k|]; destruct nn; unfold ref_apply; cbn zeta.
    - destruct (Hm k) as [H1 H2]. destruct (without_null_afrag _ H1) as [H3 H4]. split; [exact H3|]. rewrite H4. exact H2.
    - exact (Hm k).
    - exact (without_null_afrag x Hx).
    - split; [exact Hx|reflexivity].
Qed.

(* A reference to a type parameter with a binding, instantiated, and one without *)
Lemma instantiate_reference: forall b gm nn p bnd a, lookup_binding b p = Some a ->
    instantiate env b (TypeVariable (mkGenericRef gm nn p bnd)) = ref_apply gm nn (final_argument a).
Proof. intros b gm nn p bnd a H. cbn [instantiate]. rewrite H. destruct gm, nn; reflexivity. Qed.

Lemma instantiate_unbound_variable: forall b g, lookup_binding b (param_of g) = None -> instantiate env b (TypeVariable g) = TypeVariable g.
Proof. intros b [gm nn p bnd] H. cbn [instantiate]. cbn [param_of] in H. rewrite H. reflexivity. Qed.

Lemma instantiate_nullable_any: forall b t, instantiate env b (Nullable t) = rewrap_nullable (instantiate env b t).
Proof. reflexivity. Qed.

Lemma top_in_afrag: afrag top_type = true.
Proof. unfold afrag. rewrite (top_in_fragment env wf). reflexivity. Qed.

Lemma bottom_in_afrag: afrag bottom_type = true.
Proof. unfold afrag. rewrite (bottom_in_fragment env wf). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Without type variables, the variable states don't matter                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma fold_of_pairs: forall n (targs aargs: list EType) s',
    Forall2 (fun a t => unify env n t a (Ongoing s') = Some (Ongoing s')) aargs targs ->
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s') = Some (Ongoing s').
Proof.
    intros n targs aargs s' H. revert targs H. induction aargs as [|a aargs IH]; intros targs H; inversion H; subst; [reflexivity|].
    simpl. match goal with E: unify env n ?t a _ = _ |- _ => rewrite E end. apply IH. assumption.
Qed.

Lemma states_irrelevant: forall n,
    (forall t a s s', in_fragment env t = true -> in_fragment env a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s'))
    /\ (forall t a s s', argument_in_fragment env t = true -> argument_in_fragment env a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s')).
Proof.
    induction n as [|n [IHt IHa]]; [split; intros t a s s' _ _ H; discriminate H|].
    split.
    - intros t a s s' Ht Ha H.
      destruct (fragment_cases env t Ht) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> Ht']]]]];
      destruct (fragment_cases env a Ha) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> Ha']]]]];
          try (rewrite unify_class_nullable in H |- *; discriminate H).
      + destruct (root_in_fragment env _ _ _ Ht) as [Hlt Htargs]. destruct (root_in_fragment env _ _ _ Ha) as [Hla Haargs].
        rewrite unify_classes in H |- *.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hb; [|discriminate H].
        destruct (Model.is_subtype_of _ _); [|discriminate H].
        destruct (class_eqb ca nothing) eqn:Hcn; [reflexivity|].
        assert (Hfold: forall aargs', length aargs' = length targs -> (forall x, In x aargs' -> argument_in_fragment env x = true) ->
            unify_arguments (unify env n) targs aargs' s = Some (Ongoing s) ->
            unify_arguments (unify env n) targs aargs' s' = Some (Ongoing s')).
        { intros aargs' Hl' Hf' E. pose proof (pairwise_of_arguments env n targs aargs' s ltac:(lia)
              (fun t0 a0 w Ht0 Ha0 E0 => proj2 (keeps_states_with_arguments env wf n) t0 a0 s w (Htargs t0 Ht0) (Hf' a0 Ha0) E0) E) as Hp.
          unfold unify_arguments. apply fold_of_pairs.
          apply (Forall2_impl_in _ _ _ _ Hp). intros a0 t0 Ha0 Ht0 E0. exact (IHa t0 a0 s s' (Htargs t0 Ht0) (Hf' a0 Ha0) E0). }
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        * rewrite class_eqb_refl in H |- *. apply Hfold; [lia|exact Haargs|exact H].
        * rewrite (class_eqb_false _ _ Hne) in H |- *.
          destruct (supertype_arguments_in_fragment env wf ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hb Hla Haargs) as [Hln Hfn].
          apply Hfold; [lia|exact Hfn|exact H].
      + rewrite unify_nullable_class in H |- *. exact (IHt _ _ s s' Ht' Ha H).
      + rewrite unify_nullable_nullable in H |- *. exact (IHt _ _ s s' Ht' Ha' H).
    - intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' Ht Ha H; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha.
      rewrite (unify_type_arguments env n vt ot nt va oa na s (fragment_not_variable env nt Ht)) in H.
      rewrite (unify_type_arguments env n vt ot nt va oa na s' (fragment_not_variable env nt Ht)).
      destruct (ownership_is_assignable_to oa ot); [|discriminate H].
      destruct vt, va; unfold compare_variances in H |- *; try discriminate H.
      1: { apply (both_ways (unify env n) nt na s) in H;
               [|apply unify_keeps_failure|intros w; exact (proj1 (keeps_states_with_arguments env wf n) nt na s w Ht Ha)].
           destruct H as [H1 H2]. rewrite (IHt nt na s s' Ht Ha H1). exact (IHt na nt s s' Ha Ht H2). }
      all: first
          [ exact (IHt _ _ s s' Ht Ha H) | exact (IHt _ _ s s' Ha Ht H)
          | exact (IHt _ _ s s' Ht (top_in_fragment env wf) H) | exact (IHt _ _ s s' (bottom_in_fragment env wf) Ht H) ].
Qed.

Lemma cfrag_states_irrelevant: forall n t a s s', cfrag env t = true -> in_fragment env a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s').
Proof.
    assert (Hi: forall n ys a s s', class_components env ys = true -> in_fragment env a = true ->
        unify env n (Intersection ys) a (Ongoing s) = Some (Ongoing s) -> unify env n (Intersection ys) a (Ongoing s') = Some (Ongoing s')).
    { intros [|n] ys a s s' Hys Ha H; [discriminate H|].
      destruct (inter_accepts env wf n ys a s s Hys Ha H) as [_ [Hn Hall]].
      apply (inter_takes env n ys a s' Hys Ha Hn). intros c Hc.
      exact (proj1 (states_irrelevant n) c a s s' (proj2 (proj2 (class_components_facts env ys Hys) c Hc)) Ha (Hall c Hc)). }
    intros n t a s s' Ht Ha H. destruct (cfrag_cases env t Ht) as [Ht'|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - exact (proj1 (states_irrelevant n) t a s s' Ht' Ha H).
    - exact (Hi n ys a s s' Hys Ha H).
    - destruct n as [|n]; [discriminate H|]. rewrite (unify_nullable_target env) in H |- * by exact Ha.
      exact (Hi n ys _ s s' Hys (in_fragment_without_null env _ Ha) H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Type variables bound exactly                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)
(* Intersections as the types of parameters, of class types                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma any_afrag: forall m, afrag (RootResolved (Some m) any []) = true /\ closed (RootResolved (Some m) any []) = true.
Proof.
    intros m. split; [|reflexivity]. unfold afrag. cbn [in_fragment]. rewrite (wf_any_has_no_type_parameters env wf). reflexivity.
Qed.

(* A class type is assignable to Any of a mutability its own is below *)
Lemma below_any: forall m ma ca aargs, Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) m = true ->
    unify env 1 (RootResolved (Some m) any []) (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing []).
Proof.
    intros m ma ca aargs Hm. rewrite unify_classes.
    assert (Hb: base_type_is_subtype_of env ca any = true).
    { unfold base_type_is_subtype_of. destruct (class_eqb any ca); [reflexivity|].
      unfold class_eqb at 1. destruct (Class_eq_dec any any) as [_|C]; [reflexivity|exfalso; exact (C eq_refl)]. }
    assert (Ha: assignment_mutability env (RootResolved (Some m) any []) = m).
    { cbn [assignment_mutability]. rewrite (wf_any_is_not_const env wf). reflexivity. }
    rewrite Hb, Ha, Hm. destruct (class_eqb ca nothing); reflexivity.
Qed.

Lemma assigned_below_own: forall t, is_class t = true -> Model.is_subtype_of (assignment_mutability env t) (mutability_of env t) = true.
Proof.
    intros [m c args| | | | | |] H; try discriminate H. cbn [assignment_mutability mutability_of].
    destruct (is_const (declaration_of env c)); [reflexivity|]. destruct m as [[]|]; reflexivity.
Qed.

(* Through a class type in between *)
Lemma through_class: forall c y x f1 f2, in_fragment env c = true -> in_fragment env y = true -> in_fragment env x = true ->
    unify env f1 y c (Ongoing []) = Some (Ongoing []) -> unify env f2 x y (Ongoing []) = Some (Ongoing []) ->
    exists f, unify env f x c (Ongoing []) = Some (Ongoing []).
Proof.
    intros c y x f1 f2 Hc Hy Hx E1 E2.
    assert (A1: is_assignable_to env f1 c y = Some true) by (unfold is_assignable_to, empty_unification; rewrite E1; reflexivity).
    assert (A2: is_assignable_to env f2 y x = Some true) by (unfold is_assignable_to, empty_unification; rewrite E2; reflexivity).
    pose proof (Transitivity.transitivity env wf f1 f2 c y x Hc Hy Hx A1 A2) as A. unfold is_assignable_to, empty_unification in A.
    destruct (unify env (f1 + f2) x c (Ongoing [])) as [[u|]|] eqn:E; try discriminate A.
    exists (f1 + f2). pose proof (proj1 (keeps_states_with_arguments env wf (f1 + f2)) x c [] u Hx Hc E) as ->.
    exact E.
Qed.

(* The components of an intersection as the type of a parameter: class types, and type variables *)
Lemma param_component_cases: forall cs C, (forall C, In C cs -> compfrag C = true) ->
    components_sfrag env (map to_generic cs) = true -> In C cs ->
    (exists m cl args, C = RootResolved m cl args) \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q [])).
Proof.
    intros cs C HSi Hcs Hin. destruct (components_sfrag_facts env _ Hcs) as [_ Hc].
    destruct (Hc (to_generic C) (in_map _ _ _ Hin)) as [Hsh _].
    destruct (compfrag_cases C (HSi C Hin)) as [Hif|[gm [nn [q [-> _]]]]]; [|right; exists gm, nn, q; reflexivity].
    destruct (ifrag_cases C Hif) as [[m [cl [args [-> _]]]]|[[m_bot ->]|[[m [cl [args [-> _]]]]|[q [-> _]]]]].
    - left. eauto.
    - left. unfold bottom_type. eauto.
    - simpl in Hsh. discriminate Hsh.
    - right. exists None, false, q. reflexivity.
Qed.

Lemma uniform_fuel_list: forall {A: Type} (l: list A) (Q: nat -> A -> Prop),
    (forall f f' x, f <= f' -> Q f x -> Q f' x) -> (forall x, In x l -> exists f, Q f x) ->
    exists f, forall x, In x l -> Q f x.
Proof.
    intros A l Q Hm. induction l as [|x l IH]; intros H; [exists 0; intros _ []|].
    destruct (H x (or_introl eq_refl)) as [f1 H1]. destruct (IH (fun y Hy => H y (or_intror Hy))) as [f2 H2].
    exists (max f1 f2). intros y [<-|Hy]; [apply (Hm f1); [lia|exact H1]|apply (Hm f2); [lia|exact (H2 y Hy)]].
Qed.

Lemma param_shape_of: forall cs C, (forall C, In C cs -> compfrag C = true) ->
    components_sfrag env (map to_generic cs) = true -> In C cs -> param_shape C.
Proof.
    intros cs C HSi Hcs HC. destruct (param_component_cases cs C HSi Hcs HC) as [[m [cl [args ->]]]|[gm [nn [q ->]]]];
        [left; exists m, cl, args; left; reflexivity|right; exists gm, nn, q; reflexivity].
Qed.

(* ofComponents of class types, nullable or not: the intersection of them without null, of their common
   mutability, nullable where each of them is *)
Lemma of_components_flat: forall ys, 2 <= length ys -> (forall y, In y ys -> in_fragment env y = true) ->
    of_components env ys = (if forallb (is_nullable env) ys then Nullable else fun t => t)
        (Intersection (map (with_mutability env (common_mutability env (map (without_null env) ys))) (map (without_null env) ys))).
Proof.
    intros ys Hl Hys.
    assert (E: map (assignment_mutability env) (map (without_null env) ys) = map (assignment_mutability env) ys).
    { rewrite map_map. apply map_ext_in. intros y Hy. exact (assignment_mutability_of_without_null env y (Hys y Hy)). }
    unfold common_mutability. rewrite E, map_map.
    unfold of_components. destruct ys as [|y1 [|y2 ys']]; [simpl in Hl; lia|simpl in Hl; lia|]. cbv beta iota zeta.
    destruct (forallb (is_nullable env) (y1 :: y2 :: ys')) eqn:En; cbn [negb]; [|reflexivity].
    replace (forallb is_nullable_type (y1 :: y2 :: ys')) with true; [reflexivity|]. symmetry. apply forallb_forall.
    intros y Hy. rewrite forallb_forall in En. pose proof (En y Hy) as Ey.
    destruct (fragment_cases env y (Hys y Hy)) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; [discriminate Ey|reflexivity].
Qed.

(* ... which takes what each of them takes *)
Lemma below_flat_components: forall ys a, 2 <= length ys -> (forall y, In y ys -> in_fragment env y = true) ->
    in_fragment env a = true -> (forall y, In y ys -> exists f, unify env f y a (Ongoing []) = Some (Ongoing [])) ->
    exists f, unify env f (of_components env (flat_map intersected_components ys)) a (Ongoing []) = Some (Ongoing []).
Proof.
    intros ys a Hl Hys Ha Hall.
    assert (Hflat: flat_map intersected_components ys = ys).
    { clear -Hys. induction ys as [|y ys IH]; [reflexivity|]. cbn [flat_map].
      rewrite (IH (fun y' Hy' => Hys y' (or_intror Hy'))).
      destruct (fragment_cases env y (Hys y (or_introl eq_refl))) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. }
    rewrite Hflat, (of_components_flat ys Hl Hys).
    destruct (uniform_fuel_list ys (fun f y => unify env f y a (Ongoing []) = Some (Ongoing []))) as [f Hf].
    { intros f f' y Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { exact Hall. }
    (* each of them without null takes the argument without null *)
    assert (Hws: forall w, In w (map (without_null env) ys) -> is_class w = true /\ in_fragment env w = true
        /\ unify env f w (without_null env a) (Ongoing []) = Some (Ongoing [])
        /\ Model.is_subtype_of (assignment_mutability env a) (assignment_mutability env w) = true).
    { intros w Hw. apply in_map_iff in Hw. destruct Hw as [y [<- Hy]]. pose proof (Hf y Hy) as E.
      pose proof (accepted_mutability_classes env f y a [] [] (Hys y Hy) Ha E) as Hm.
      destruct (fragment_cases env y (Hys y Hy)) as [[m [c [args Ey]]]|[m [c [args [Ey Hc]]]]]; subst y.
      - pose proof (accepted_non_null env f _ a [] [] (Hys _ Hy) Ha eq_refl E) as Hna.
        rewrite (without_null_unchanged env a Hna). split; [reflexivity|]. split; [exact (Hys _ Hy)|]. split; [exact E|exact Hm].
      - destruct f as [|f']; [discriminate E|]. rewrite (unify_nullable_target env f' _ a [] Ha) in E.
        split; [reflexivity|]. split; [exact Hc|]. split; [exact (unify_fuel_monotone env f' (S f') _ _ _ _ ltac:(lia) E)|exact Hm]. }
    set (ws := map (without_null env) ys) in *.
    assert (Hne: ws <> []) by (unfold ws; destruct ys; [simpl in Hl; lia|discriminate]).
    assert (Hlw: length ws = length ys) by (unfold ws; apply length_map).
    assert (HN: unify env (S f) (Intersection (map (with_mutability env (common_mutability env ws)) ws)) (without_null env a) (Ongoing [])
        = Some (Ongoing [])).
    { apply (inter_takes env).
      - unfold class_components. rewrite length_map, Hlw.
        apply andb_true_iff. split; [apply andb_true_iff; split; [apply Nat.leb_le; exact Hl|]|].
        + apply forallb_forall. intros y Hy. apply in_map_iff in Hy. destruct Hy as [w [<- Hw]].
          destruct (Hws w Hw) as [Hc [Hfw _]]. destruct w; try discriminate Hc.
          rewrite (in_fragment_with_mutability env (common_mutability env ws) _ Hfw). reflexivity.
        + exact (common_classes_uniform env ws Hne (fun w Hw => proj1 (Hws w Hw))).
      - exact (in_fragment_without_null env a Ha).
      - destruct (fragment_cases env a Ha) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; reflexivity.
      - intros y Hy. apply in_map_iff in Hy. destruct Hy as [w [<- Hw]]. destruct (Hws w Hw) as [_ [Hfw [E _]]].
        apply (accepts_with_mutability env); [exact Hfw|exact (in_fragment_without_null env a Ha)| |exact E].
        unfold common_mutability. apply Ops.fold_intersect_greatest; [apply Ops.mutability_subtype_of_readonly|].
        intros m Hm'. apply in_map_iff in Hm'. destruct Hm' as [w' [<- Hw']].
        rewrite (assignment_mutability_of_without_null env a Ha). exact (proj2 (proj2 (proj2 (Hws w' Hw')))). }
    destruct (forallb (is_nullable env) ys) eqn:En; cbn beta iota.
    - exists (S (S f)). rewrite (unify_nullable_target env (S f) _ a [] Ha). exact HN.
    - (* one of them is non-null, and so is the argument *)
      exists (S f).
      assert (Hex: exists y, In y ys /\ is_nullable env y = false).
      { clear -En. induction ys as [|y ys IH]; [discriminate En|]. cbn [forallb] in En.
        destruct (is_nullable env y) eqn:Ey; [destruct (IH En) as [y' [Hy' Ey']]; exists y'; split; [right; exact Hy'|exact Ey']|].
        exists y. split; [left; reflexivity|exact Ey]. }
      destruct Hex as [y [Hy Ey]].
      pose proof (accepted_non_null env f y a [] [] (Hys y Hy) Ha Ey (Hf y Hy)) as Hna.
      rewrite (without_null_unchanged env a Hna) in HN. exact HN.
Qed.

(* Below the instance of each component of an intersection, a class type is below the instance of the
   intersection, its type parameters bound to class types *)
Lemma below_intersection_instance: forall b K cs x, bindings_in_fragment env b -> components_sfrag env cs = true ->
    bex env b (Intersection cs) = true ->
    (forall c, In c cs -> bound_in_top_h env b K [] (top_bound_in env b K []) c = true) ->
    in_fragment env x = true ->
    (forall c, In c cs -> exists f, unify env f (inst_nested env b c) x (Ongoing []) = Some (Ongoing [])) ->
    exists f, unify env f (inst_nested env b (Intersection cs)) x (Ongoing []) = Some (Ongoing []).
Proof.
    intros b K cs x Hbf Hcs Hbx Htop Hx Hall.
    destruct (components_sfrag_facts env cs Hcs) as [Hl Hc].
    assert (Hn: forall c, In c cs -> is_nullable env (inst_nested env b c) = false).
    { intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      apply (proj2 (proj2 (instance_facts_ex env wf b K [] Hbf _ c (le_n _) (sfrag_tfrag env c Hs) (bex_component env b cs c Hbx Hin) (Htop c Hin)))).
      apply (component_non_null env), Hsh. }
    destruct (intersection_instance_ex env wf b Hbf cs Hcs Hbx Hn) as [Heq [Hcc Hcomp]]. rewrite Heq.
    destruct (uniform_fuel_list cs (fun f c => unify env f (inst_nested env b c) x (Ongoing []) = Some (Ongoing []))) as [f Hf].
    { intros f f' c Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { exact Hall. }
    assert (Hne: cs <> []) by (intros ->; simpl in Hl; lia).
    assert (HnA: is_nullable env x = false).
    { destruct cs as [|c1 cs']; [exfalso; exact (Hne eq_refl)|].
      exact (accepted_non_null env _ _ _ _ _ (proj1 (Hcomp c1 (or_introl eq_refl))) Hx (Hn c1 (or_introl eq_refl)) (Hf c1 (or_introl eq_refl))). }
    exists (S f). apply (inter_takes env); [exact Hcc|exact Hx|exact HnA|].
    intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]].
    apply (accepts_with_mutability env); [exact (proj1 (Hcomp c Hin))|exact Hx| |exact (Hf c Hin)].
    apply Ops.fold_intersect_greatest; [apply Ops.mutability_subtype_of_readonly|].
    intros m Hm. apply in_map_iff in Hm. destruct Hm as [y [<- Hy]]. apply in_map_iff in Hy. destruct Hy as [c' [<- Hin']].
    exact (accepted_mutability_classes env _ _ _ _ _ (proj1 (Hcomp c' Hin')) Hx (Hf c' Hin')).
Qed.

Section Exact.

(* The types the type variables are replaced with (exact type arguments), the fuel with which they
   are within the bounds of the type parameters and the type arguments the variables are bound to,
   and the variable states of the unification *)
Variable b: Bindings.
Variable K: nat.
Variable s: VariableStates.

(* Each type variable replaced is bound exactly, to a type argument that stands for its replacement *)
Hypothesis Hcover: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    exists st vb ob X, lookup_state s p = Some st /\ is_exact st = true
        /\ upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
        /\ in_fragment env X = true
        /\ unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s).
Hypothesis Hbf: bindings_in_fragment env b.

Definition inst (t: EType): EType := inst_nested env b (to_generic t).

Lemma inst_root: forall m c args, no_generics (RootResolved m c args) = true -> bound_vars b (RootResolved m c args) = true ->
    inst (RootResolved m c args) = RootResolved m c (map (instantiate env b) args).
Proof.
    intros m c args H Hb. unfold inst. change (instantiate env b (to_generic (RootResolved m c args)) = RootResolved m c (map (instantiate env b) args)).
    rewrite (instantiate_to_generic b _ H Hb). apply instantiate_class.
Qed.

Lemma inst_nullable: forall m c args, no_generics (RootResolved m c args) = true -> bound_vars b (RootResolved m c args) = true ->
    inst (Nullable (RootResolved m c args)) = Nullable (RootResolved m c (map (instantiate env b) args)).
Proof.
    intros m c args H Hb. unfold inst. change (instantiate env b (to_generic (Nullable (RootResolved m c args))) = Nullable (RootResolved m c (map (instantiate env b) args))).
    rewrite (instantiate_to_generic b (Nullable (RootResolved m c args)) H Hb). apply instantiate_nullable_class.
Qed.

(* The bindings of the type variables of an inst_root or inst_nullable, from bound_in *)
Local Ltac bvars := eapply bound_vars_of; [eapply ifrag_no_generics; eassumption|];
    match goal with H: bound_in _ _ _ _ _ = true |- _ => exact H end.

Lemma inst_variable: forall p bound v o x, lookup_binding b p = Some (TypeArgument v o x) ->
    inst (TypeVariable (mkGenericRef None false p bound)) = x.
Proof. intros p bound v o x H. unfold inst. simpl. rewrite H. reflexivity. Qed.

Lemma inst_reference: forall gm nn p bound v o x, lookup_binding b p = Some (TypeArgument v o x) ->
    inst (TypeVariable (mkGenericRef gm nn p bound)) = ref_apply gm nn x
    /\ inst (Nullable (TypeVariable (mkGenericRef gm nn p bound))) = rewrap_nullable (ref_apply gm nn x).
Proof. intros gm nn p bound v o x H. unfold inst. cbn [to_generic inst_nested param_of]. rewrite H, !inst_ref_apply. split; reflexivity. Qed.

Lemma instantiate_argument: forall v o n, nfrag n = true -> bound_in env b K s (to_generic n) = true ->
    instantiate env b (TypeArgument v o n) = TypeArgument v (instantiate_ownership b o) (inst n).
Proof.
    intros v o n Hn Hb. rewrite <- (instantiate_to_generic b (TypeArgument v o n)) by
        first [exact (nfrag_argument v o n Hn)|exact (bound_vars_nfrag b K s n Hn Hb)].
    exact (instantiate_bound_argument env wf b K s v o (to_generic n) (nfrag_sfrag n Hn) Hb).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify, one step                                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma unify_type_arguments_exact: forall n vt ot nt va oa na,
    capturable nt s = None ->
    unify env (S n) (TypeArgument vt ot nt) (TypeArgument va oa na) (Ongoing s) =
    if ownership_is_assignable_to oa ot then compare_variances (unify env n) vt va nt na s else Some Failed.
Proof.
    intros n vt ot nt va oa na Hc. rewrite unify_step_once. unfold unify_step, unify_type_argument. cbn beta iota zeta.
    destruct (ownership_is_assignable_to oa ot); [|reflexivity]. rewrite Hc. destruct vt, va; reflexivity.
Qed.

Lemma bound_variable: forall p bound, bound_in env b K s (Generic (mkGenericRef None false p bound)) = true ->
    exists o x st vb ob X, lookup_binding b p = Some (TypeArgument Model.invariant o x) /\ in_fragment env x = true
        /\ lookup_state s p = Some st /\ is_exact st = true
        /\ upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X /\ in_fragment env X = true
        /\ unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s).
Proof.
    intros p bound H. destruct (binds_ref_some env wf b K s (mkGenericRef None false p bound) H) as [o [x [E _]]]. cbn [param_of] in E. pose proof (Hbf p o x E) as Hx.
    destruct (Hcover p o x E) as [st [vb [ob [X [Hl [He [Hu [Hlo [HX Hc]]]]]]]]].
    exists o, x, st, vb, ob, X. repeat split; assumption.
Qed.

Lemma variable_not_capturable: forall p bound st, lookup_state s p = Some st -> is_exact st = true ->
    capturable (TypeVariable (mkGenericRef None false p bound)) s = None.
Proof. intros p bound st Hl He. simpl. rewrite Hl, He, andb_false_r. reflexivity. Qed.

Lemma ifrag_not_capturable: forall t, ifrag t = true -> bound_in env b K s (to_generic t) = true -> capturable t s = None.
Proof.
    intros t Ht Hb. destruct (ifrag_cases t Ht) as [[m [c [args [-> _]]]]|[[m_bot ->]|[[m [c [args [-> _]]]]|[p [-> _]]]]];
        try reflexivity.
    destruct (bound_variable p [] Hb) as [o [x [st [vb [ob [X [_ [_ [Hl [He _]]]]]]]]]].
    exact (variable_not_capturable p [] st Hl He).
Qed.

Lemma nfrag_not_capturable: forall t, nfrag t = true -> bound_in env b K s (to_generic t) = true -> capturable t s = None.
Proof.
    intros t Ht Hb. destruct (nfrag_cases t Ht) as [H|[gm [nn [p [[-> | ->] _]]]]]; [exact (ifrag_not_capturable t H Hb)| |reflexivity].
    destruct (binds_ref_some env wf b K s _ Hb) as [o [x [E _]]]. cbn [param_of] in E.
    destruct (Hcover p o x E) as [st [_ [_ [_ [Hl [He _]]]]]]. simpl. rewrite Hl, He, andb_false_r. reflexivity.
Qed.

(* A type variable bound exactly as the target: its binding *)
Lemma unify_variable_target: forall n p bound st A u, lookup_state s p = Some st -> is_exact st = true ->
    in_fragment env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bound)) A (Ongoing s) = Some (Ongoing u) ->
    unify env n (lower_bound st) A (Ongoing s) = Some (Ongoing u).
Proof.
    intros n p bound st A u Hl He HA H. rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_type_variable, plus_supertype_constraint in H.
    - rewrite Hl, He in H. exact H.
    - destruct (is_nullable env _); [|discriminate H]. rewrite Hl, He in H. exact H.
Qed.

(* ... and as the assignee *)
Lemma unify_variable_assignee: forall n gm nn p bound st A u, lookup_state s p = Some st -> is_exact st = true ->
    in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef gm nn p bound)) (Ongoing s) = Some (Ongoing u) ->
    unify env n A (upper_bound st) (Ongoing s) = Some (Ongoing u).
Proof.
    intros n gm nn p bound st A u Hl He HA H. rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_root_resolved, unify_nullable, type_variable_flipped_unify, plus_subtype_constraint in H;
        rewrite Hl, He in H; exact H.
Qed.

(* A value assigned to a type argument, and a type argument assigned to a reference *)
Lemma unify_value_argument: forall n A v o t, in_fragment env A = true ->
    unify env (S n) A (TypeArgument v o t) (Ongoing s) = unify env n A (read_type v t) (Ongoing s).
Proof. intros n A v o t HA. destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma unify_argument_with_value: forall n v o t V, in_fragment env V = true ->
    unify env (S n) (TypeArgument v o t) V (Ongoing s) =
    if Variance_beq v output then (if is_non_nullable_nothing env V then Some (Ongoing s) else Some Failed)
    else unify env n t V (Ongoing s).
Proof.
    intros n v o t V HV. destruct (fragment_cases env V HV) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; destruct v; reflexivity.
Qed.

Lemma keeps: forall n t a u, in_fragment env t = true -> in_fragment env a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s.
Proof. intros n t a u Ht Ha H. exact (proj1 (keeps_states_with_arguments env wf n) t a s u Ht Ha H). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The type a variable stands for, where the variable is assigned to or assigned                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* Whatever can be assigned to the type argument, a variable is bound to, can be assigned to each of
   the types it stands for *)
Lemma write_leaf: forall n vb ob X o x A u, in_fragment env X = true -> in_fragment env x = true -> afrag A = true ->
    unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s) ->
    unify env n (TypeArgument vb ob X) A (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (n + K + 1) x A (Ongoing s) = Some (Ongoing s).
Proof.
    intros n vb ob X o x A u HX Hx HA Hc H. pose proof (afrag_in_fragment A HA) as HA'.
    destruct n as [|n]; [discriminate H|].
    rewrite (unify_type_arguments env K vb ob X Model.invariant o x s (fragment_not_variable env X HX)) in Hc.
    destruct (ownership_is_assignable_to o ob); [|discriminate Hc].
    rewrite (unify_argument_with_value n vb ob X A HA') in H.
    destruct vb; cbn [Variance_beq] in H.
    - (* invariant: x is X *)
      unfold compare_variances in Hc. apply (both_ways (unify env K) X x s) in Hc;
          [|apply unify_keeps_failure|intros w; exact (keeps K X x w HX Hx)].
      destruct Hc as [_ Hc]. pose proof (keeps n X A u HX HA' H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (n + K)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (n + K)) A X x n K s (le_n _) HA' HX Hx H Hc).
    - (* in: x is above X *)
      unfold compare_variances in Hc. pose proof (keeps n X A u HX HA' H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (n + K)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (n + K)) A X x n K s (le_n _) HA' HX Hx H Hc).
    - (* out: nothing but Nothing, which is the bottom type *)
      destruct (is_non_nullable_nothing env A) eqn:En; [|discriminate H]. injection H as <-. split; [reflexivity|].
      destruct (fragment_cases env A HA') as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; [|discriminate En].
      simpl in En. apply class_eqb_true in En. subst c.
      rewrite (nothing_fragment_arguments env wf m args HA').
      apply (below_all env wf s x); [exact Hx|lia].
Qed.

(* Whatever the type argument a variable is bound to can be assigned to, each of the types it stands
   for can be assigned to *)
Lemma read_leaf: forall n vb ob X o x A u, in_fragment env X = true -> in_fragment env x = true -> in_fragment env A = true ->
    unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s) ->
    unify env n A (TypeArgument vb ob X) (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (n + K + 1) A x (Ongoing s) = Some (Ongoing s).
Proof.
    intros n vb ob X o x A u HX Hx HA Hc H.
    destruct n as [|n]; [discriminate H|].
    rewrite (unify_type_arguments env K vb ob X Model.invariant o x s (fragment_not_variable env X HX)) in Hc.
    destruct (ownership_is_assignable_to o ob); [|discriminate Hc].
    rewrite (unify_value_argument n A vb ob X HA) in H.
    destruct vb; cbn [read_type] in H; unfold compare_variances in Hc.
    - apply (both_ways (unify env K) X x s) in Hc; [|apply unify_keeps_failure|intros w; exact (keeps K X x w HX Hx)].
      destruct Hc as [Hc _]. pose proof (keeps n A X u HA HX H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (K + n)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (K + n)) x X A K n s (le_n _) Hx HX HA Hc H).
    - (* in: reads as read Any?, which is above everything *)
      pose proof (keeps n A top_type u HA (top_in_fragment env wf) H) as ->. split; [reflexivity|].
      apply (above_top env wf n A s HA H x); [exact Hx|lia].
    - pose proof (keeps n A X u HA HX H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (K + n)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (K + n)) x X A K n s (le_n _) Hx HX HA Hc H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Supertypes, and pairs of type arguments                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma supertype_commute_variables: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) ->
    (forall y, In y ys -> argument_ifrag y = true /\ bound_in env b K s (to_generic y) = true) ->
    parameterized_supertype_arguments env sub (map (instantiate env b) ys) super
        = map (instantiate env b) (parameterized_supertype_arguments env sub ys super)
    /\ forall a, In a (parameterized_supertype_arguments env sub ys super) ->
        argument_ifrag a = true /\ bound_in env b K s (to_generic a) = true.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    assert (Hta: forall y, In y ys -> is_type_argument y = true)
        by (intros y Hy; destruct (Hys y Hy) as [H _]; destruct y; try discriminate H; reflexivity).
    assert (Hng: forall y, In y ys -> no_generics y = true)
        by (intros y Hy; exact (proj2 (proj2 (argument_ifrag_parts y (proj1 (Hys y Hy)))))).
    destruct (supertype_arguments_to_generic sub super ys Hne Hn Hbase Hl Hta) as [Htg [Hng' _]].
    assert (Hys': forall y, In y (map to_generic ys) -> argument_sfrag env y = true /\ bound_in env b K s y = true).
    { intros y' Hy'. apply in_map_iff in Hy'. destruct Hy' as [y [<- Hy]]. destruct (Hys y Hy) as [Hf Hb]. split; [|exact Hb].
      exact (proj1 (proj2 (argument_ifrag_parts y Hf))). }
    destruct (supertype_arguments_commute env wf b K s sub super (map to_generic ys)
        Hne Hn Hbase ltac:(rewrite length_map; exact Hl) Hys') as [Hcomm Hnorm].
    split.
    - replace (map (instantiate env b) ys) with (map (instantiate env b) (map to_generic ys))
          by (rewrite map_map; apply map_ext_in; intros y Hy; apply instantiate_to_generic; [apply Hng, Hy|];
              apply (bound_vars_of b K s y (Hng y Hy)), Hys, Hy).
      rewrite Hcomm, Htg, map_map. apply map_ext_in. intros a Ha. apply instantiate_to_generic; [exact (Hng' Hng a Ha)|].
      apply (bound_vars_of b K s a (Hng' Hng a Ha)). rewrite Htg in Hnorm. exact (proj2 (Hnorm (to_generic a) (in_map _ _ _ Ha))).
    - intros a Ha. rewrite Htg in Hnorm. destruct (Hnorm (to_generic a) (in_map _ _ _ Ha)) as [Hf Hb]. split; [|exact Hb].
      apply argument_ifrag_intro; [destruct a; try discriminate Hf; reflexivity|exact Hf|exact (Hng' Hng a Ha)].
Qed.

Lemma fold_map: forall n n' (f g: EType -> EType) targs aargs u,
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing u) ->
    (forall t a u0, In t targs -> In a aargs -> unify env n t a (Ongoing s) = Some (Ongoing u0) ->
        u0 = s /\ unify env n' (f t) (g a) (Ongoing s) = Some (Ongoing s)) ->
    u = s /\ fold_unify (fun inner '(t, a) => unify env n' t a inner) (combine (map f targs) (map g aargs)) (Ongoing s)
        = Some (Ongoing s).
Proof.
    intros n n' f g targs. induction targs as [|t targs IH]; intros aargs u H Hpair;
        destruct aargs as [|a aargs]; simpl in *; try (injection H as <-; auto).
    destruct (unify env n t a (Ongoing s)) as [[s1|]|] eqn:E1; try discriminate H.
    - destruct (Hpair t a s1 (or_introl eq_refl) (or_introl eq_refl) E1) as [-> Hinst].
      rewrite Hinst. apply (IH aargs u H). intros t' a' u0 Ht Ha. apply Hpair; right; assumption.
    - rewrite fold_stays_failed in H. discriminate H.
Qed.

(* The parts of a class type of the fragment *)
Lemma root_parts: forall m c args, ifrag (RootResolved m c args) = true ->
    bound_in env b K s (to_generic (RootResolved m c args)) = true ->
    forall a, In a args -> argument_ifrag a = true /\ bound_in env b K s (to_generic a) = true.
Proof.
    intros m c args Hf Hb a Ha. split.
    - destruct (ifrag_cases _ Hf) as [[m' [c' [args' [Heq [_ [_ Hargs]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
          try discriminate Heq.
      + injection Heq as <- <- <-. exact (Hargs a Ha).
      + unfold bottom_type in Heq. injection Heq as _ _ ->. destruct Ha.
    - apply (bound_in_root env b K s m c (map to_generic args) Hb). apply in_map, Ha.
Qed.

Lemma closed_parts: forall m c args, closed (RootResolved m c args) = true -> forall a, In a args -> closed a = true.
Proof. intros m c args H. change (forallb closed args = true) in H. apply forallb_forall, H. Qed.

Lemma closed_argument: forall v o n, closed (TypeArgument v o n) = true -> is_parameter_ownership o = false /\ closed n = true.
Proof.
    intros v o n H. change (negb (is_parameter_ownership o) && closed n = true) in H. apply andb_true_iff in H.
    destruct H as [Ho Hn]. split; [destruct (is_parameter_ownership o); [discriminate Ho|reflexivity]|exact Hn].
Qed.

Lemma ownership_not_instantiated: forall o, is_parameter_ownership o = false -> instantiate_ownership b o = o.
Proof. intros [| | |p] H; [reflexivity..|discriminate H]. Qed.

(* A type variable of a mutability given to it, narrowed or made nullable, as the target: the type it
   stands for takes what its binding takes, of that mutability and nullability *)
Lemma reference_target: forall n gm nn p o x P A u, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    sfrag env (Generic (mkGenericRef gm nn p [])) = true ->
    (P = TypeVariable (mkGenericRef gm nn p []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn p []))) ->
    afrag A = true -> unify env n P A (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (n * S (S K) + 2) (inst P) A (Ongoing s) = Some (Ongoing s).
Proof.
    intros n gm nn p o x P A u Ex Hs HP HA H. pose proof (afrag_in_fragment A HA) as HA'.
    pose proof (Hbf p o x Ex) as Hx.
    destruct (Hcover p o x Ex) as [st [vb [ob [X [Hl [He [Hup [Hlo [HX Hc]]]]]]]]].
    destruct (inst_reference gm nn p [] _ _ _ Ex) as [Ei Ein].
    (* the variable takes A0: the plain variable does, and the type it stands for takes A0 *)
    assert (Hstep: forall k A0, afrag A0 = true ->
        unify env (S k) (TypeVariable (mkGenericRef gm nn p [])) A0 (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (k + K + 1) (ref_apply gm nn x) A0 (Ongoing s) = Some (Ongoing s)).
    { intros k A0 HA0 H0; pose proof (afrag_in_fragment A0 HA0) as HA0'.
      destruct (fragment_cases env A0 HA0') as [[ma [ca [aa E0]]]|[ma [ca [aa [E0 _]]]]]; subst A0;
          (destruct ((fun HS => unify_variable_given k gm nn p _ s u HS H0) I) as [H1 [Hgm Hnul]];
           apply (unify_variable_target k p [] st _ u Hl He HA0') in H1; rewrite Hlo in H1;
           destruct (write_leaf k vb ob X o x _ u HX Hx HA0 Hc H1) as [-> Hw]; split; [reflexivity|];
           apply (class_reference_takes _ gm nn x _ s Hx HA0'); [exact Hgm| |exact Hw];
           intros En; subst nn; destruct (is_nullable env _) eqn:EA; [|reflexivity];
           rewrite (narrowed_not_nullable gm p Hs) in Hnul; discriminate (Hnul eq_refl)). }
    destruct HP as [->| ->].
    - (* the variable itself *)
      destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [-> Hw]. split; [reflexivity|].
      rewrite Ei. apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hw].
    - (* made nullable: it takes the argument without null *)
      destruct n as [|n]; [discriminate H|].
      assert (H0: unify env n (TypeVariable (mkGenericRef gm nn p [])) (without_null env A) (Ongoing s) = Some (Ongoing u)).
      { destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [rewrite unify_nullable_class in H|rewrite unify_nullable_nullable in H]; exact H. }
      assert (HA0: afrag (without_null env A) = true).
      { destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HR]]]]]; [exact HA|].
        exact HR. }
      destruct n as [|n]; [discriminate H0|].
      destruct (Hstep n _ HA0 H0) as [-> Hw]. split; [reflexivity|].
      rewrite Ein. replace (S (S n) * S (S K) + 2) with (S (S (S n) * S (S K) + 1)) by lia.
      apply (unify_rewrap_target _ _ A s _ HA'). apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hw].
Qed.

(* ... and as the assignee: what takes the type it stands for takes it of that mutability, without
   null, or made nullable where it takes null *)
Lemma reference_assignee: forall n gm nn p o x P A u, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    (P = TypeVariable (mkGenericRef gm nn p []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn p []))) ->
    in_fragment env A = true -> unify env n A P (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (n * S (S K) + 2) A (inst P) (Ongoing s) = Some (Ongoing s).
Proof.
    intros n gm nn p o x P A u Ex HP HA H. pose proof (Hbf p o x Ex) as Hx.
    destruct (Hcover p o x Ex) as [st [vb [ob [X [Hl [He [Hup [Hlo [HX Hc]]]]]]]]].
    destruct (inst_reference gm nn p [] _ _ _ Ex) as [Ei Ein].
    assert (Hstep: forall k A0, in_fragment env A0 = true ->
        unify env (S k) A0 (TypeVariable (mkGenericRef gm nn p [])) (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (k + K + 1) A0 (ref_apply gm nn x) (Ongoing s) = Some (Ongoing s)).
    { intros k A0 HA0 H0. apply (unify_variable_assignee k gm nn p [] st A0 u Hl He HA0) in H0. rewrite Hup in H0.
      destruct (read_leaf k vb ob X o x A0 u HX Hx HA0 Hc H0) as [-> Hr]. split; [reflexivity|].
      exact (reference_takes_assignee _ gm nn x A0 s Hx HA0 Hr). }
    destruct HP as [->| ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [-> Hw]. split; [reflexivity|].
      rewrite Ei. apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hw].
    - destruct n as [|n]; [discriminate H|].
      destruct (fragment_cases env A HA) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HR]]]]].
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_nullable in H. destruct n as [|n]; [discriminate H|].
        destruct (Hstep n _ HR H) as [-> Hw]. split; [reflexivity|].
        (* the instance, of a class type that takes it, is a class type *)
        destruct (fragment_cases env _ (ref_apply_in_fragment gm nn x Hx)) as [[my [cy [yargs Ey]]]|[my [cy [yargs [Ey _]]]]];
            rewrite Ey in Hw.
        * rewrite Ein, Ey. cbn [rewrap_nullable]. replace (S (S n) * S (S K) + 2) with (S (S (S n) * S (S K) + 1)) by lia.
          rewrite unify_nullable_nullable. apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hw].
        * replace (n + K + 1) with (S (n + K)) in Hw by lia. rewrite unify_class_nullable in Hw. discriminate Hw.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Soundness                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma inference_with_arguments: forall n,
    (forall P A u, ifrag P = true -> afrag A = true -> closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n P A (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) (inst P) A (Ongoing s) = Some (Ongoing s))
    /\ (forall P A u, ifrag P = true -> afrag A = true -> closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n A P (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) A (inst P) (Ongoing s) = Some (Ongoing s))
    /\ (forall P A u, argument_ifrag P = true -> argument_in_fragment env A = true ->
        closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n P A (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) (instantiate env b P) A (Ongoing s) = Some (Ongoing s))
    /\ (forall P A u, argument_ifrag P = true -> argument_in_fragment env A = true ->
        closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n A P (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) A (instantiate env b P) (Ongoing s) = Some (Ongoing s)).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A u; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    (* the type of a type argument, also a type variable of a mutability given to it, narrowed or made nullable *)
    assert (IHnt: forall P A u, nfrag P = true -> afrag A = true -> closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n P A (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) (inst P) A (Ongoing s) = Some (Ongoing s)).
    { intros P A u HP HA HcA Hb H. destruct (nfrag_cases P HP) as [HP'|[gm [nn [p [EP Hs]]]]]; [exact (IHt P A u HP' HA HcA Hb H)|].
      assert (Hb': bound_in env b K s (Generic (mkGenericRef gm nn p [])) = true) by (destruct EP as [-> | ->]; exact Hb).
      destruct (binds_ref_some env wf b K s _ Hb') as [o [x [Ex _]]]. cbn [param_of] in Ex.
      exact (reference_target n gm nn p o x P A u Ex Hs EP HA H). }
    assert (IHna: forall P A u, nfrag P = true -> afrag A = true -> closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n A P (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) A (inst P) (Ongoing s) = Some (Ongoing s)).
    { intros P A u HP HA HcA Hb H. destruct (nfrag_cases P HP) as [HP'|[gm [nn [p [EP Hs]]]]]; [exact (IHa P A u HP' HA HcA Hb H)|].
      assert (Hb': bound_in env b K s (Generic (mkGenericRef gm nn p [])) = true) by (destruct EP as [-> | ->]; exact Hb).
      destruct (binds_ref_some env wf b K s _ Hb') as [o [x [Ex _]]]. cbn [param_of] in Ex.
      exact (reference_assignee n gm nn p o x P A u Ex EP (afrag_in_fragment A HA) H). }
    clear IHt IHa. rename IHnt into IHt, IHna into IHa.
    assert (HPn: n <= n * S (S K)) by (rewrite Nat.mul_succ_r; lia).
    rewrite Nat.mul_succ_l. remember (n * S (S K)) as F eqn:HF. clear HF.
    replace (F + S (S K) + 2) with (S (F + 2 + S K)) by lia.
    assert (Hmono: forall t a, unify env (F + 2) t a (Ongoing s) = Some (Ongoing s) ->
        unify env (F + 2 + S K) t a (Ongoing s) = Some (Ongoing s))
        by (intros t a E; apply (unify_fuel_monotone env (F + 2)); [lia|exact E]).
    (* the parts of the types of the arguments *)
    assert (Hargs: forall ma ca aargs, in_fragment env (RootResolved ma ca aargs) = true ->
        closed (RootResolved ma ca aargs) = true ->
        length aargs = length (parameter_ids env ca) /\ forall a, In a aargs ->
            argument_in_fragment env a = true /\ closed a = true).
    { intros ma ca aargs Hf Hc. destruct (root_in_fragment env ma ca aargs Hf) as [Hl Ha]. split; [exact Hl|].
      intros a Hin. split; [exact (Ha a Hin)|]. exact (closed_parts ma ca aargs Hc a Hin). }
    (* the same, as normalized to a supertype *)
    assert (Hnorm: forall ca ct aargs, ca <> ct -> ca <> nothing -> base_type_is_subtype_of env ca ct = true ->
        length aargs = length (parameter_ids env ca) ->
        (forall a, In a aargs -> argument_in_fragment env a = true /\ closed a = true) ->
        forall a, In a (parameterized_supertype_arguments env ca aargs ct) ->
            argument_in_fragment env a = true /\ closed a = true).
    { intros ca ct aargs Hne Hcn Hbase Hl Ha a Hin.
      assert (Hta: forall y, In y aargs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Ha, Hy).
      destruct (supertype_arguments_to_generic ca ct aargs Hne Hcn Hbase Hl Hta) as [_ [_ Hcl]].
      destruct (supertype_arguments_in_fragment env wf ca ct aargs Hne Hcn Hbase Hl (fun y Hy => proj1 (Ha y Hy))) as [_ Hf].
      split; [exact (Hf a Hin)|]. apply Hcl; [intros y Hy; apply Ha, Hy|exact Hin]. }
    split; [|split; [|split]].
    - (* a type with type variables as the target *)
      intros P A u HP HA HcA Hb H. pose proof (afrag_in_fragment A HA) as HA'.
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag (RootResolved mt ct targs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K s (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (F + 2 + S K)) (inst (RootResolved mt ct targs)) (RootResolved ma ca aargs) (Ongoing s)
              = Some (Ongoing s)).
      { intros mt ct targs ma ca aargs Hft Hfa Hca Hbt Hu.
        rewrite (inst_root mt ct targs (ifrag_no_generics _ Hft) ltac:(bvars)).
        pose proof (root_parts mt ct targs Hft Hbt) as Htargs.
        destruct (Hargs ma ca aargs Hfa Hca) as [Hla Haargs].
        rewrite unify_classes in Hu |- *.
        rewrite (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs).
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _); [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn; [injection Hu as <-; auto|].
        unfold unify_arguments in Hu |- *.
        assert (Hpair: forall aargs', (forall a, In a aargs' -> argument_in_fragment env a = true /\ closed a = true) ->
            fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs') (Ongoing s) = Some (Ongoing u) ->
            u = s /\ fold_unify (fun inner '(t, a) => unify env (F + 2 + S K) t a inner)
                (combine (map (instantiate env b) targs) aargs') (Ongoing s) = Some (Ongoing s)).
        { intros aargs' Ha' Hf. rewrite <- (map_id aargs').
          apply (fold_map n (F + 2 + S K) (instantiate env b) (fun a => a) targs aargs' u Hf).
          intros t a u0 Ht Ha E. destruct (Htargs t Ht) as [Hft' Hbt']. destruct (Ha' a Ha) as [Hfa' Hca'].
          destruct (IHat t a u0 Hft' Hfa' Hca' Hbt' E) as [-> Hi]. split; [reflexivity|exact (Hmono _ _ Hi)]. }
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        - rewrite class_eqb_refl in Hu |- *. exact (Hpair aargs Haargs Hu).
        - rewrite (class_eqb_false _ _ Hne) in Hu |- *.
          exact (Hpair _ (Hnorm ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs) Hu). }
      destruct (ifrag_cases P HP) as [[mt [ct [targs [-> _]]]]|[[m_bot ->]|[[mt [ct [targs [-> HP']]]]|[p [-> Hfb]]]]];
          [| unfold bottom_type in * | |].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + rewrite (inst_nullable mt ct targs (ifrag_no_generics _ HP') ltac:(bvars)).
        assert (Hb': bound_in env b K s (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
        destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]].
        * rewrite unify_nullable_class in H |- *.
          destruct (IHt _ _ u (ifrag_nfrag _ HP') HA HcA Hb' H) as [-> Hi]. split; [reflexivity|].
          rewrite (inst_root mt ct targs (ifrag_no_generics _ HP') ltac:(bvars)) in Hi. exact (Hmono _ _ Hi).
        * rewrite unify_nullable_nullable in H |- *.
          assert (HA2: afrag (RootResolved ma ca aargs) = true) by exact HA''.
          destruct (IHt _ _ u (ifrag_nfrag _ HP') HA2 HcA Hb' H) as [-> Hi]. split; [reflexivity|].
          rewrite (inst_root mt ct targs (ifrag_no_generics _ HP') ltac:(bvars)) in Hi. exact (Hmono _ _ Hi).
      + (* a type variable: the type it stands for takes what its binding takes *)
        destruct (bound_variable p [] Hb) as [o [x [st [vb [ob [X [Ex [Hx [Hl [He [Hup [Hlo [HX Hc]]]]]]]]]]]]].
        apply (unify_variable_target n p [] st A u Hl He HA') in H. rewrite Hlo in H.
        destruct (write_leaf n vb ob X o x A u HX Hx HA Hc H) as [-> Hw]. split; [reflexivity|].
        rewrite (inst_variable p [] _ _ _ Ex). apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hw].
    - (* a type with type variables as the assignee *)
      intros P A u HP HA HcA Hb H. pose proof (afrag_in_fragment A HA) as HA'.
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag (RootResolved mp cp pargs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K s (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (F + 2 + S K)) (RootResolved ma ca aargs) (inst (RootResolved mp cp pargs)) (Ongoing s)
              = Some (Ongoing s)).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hca Hbp Hu.
        rewrite (inst_root mp cp pargs (ifrag_no_generics _ Hfp) ltac:(bvars)).
        pose proof (root_parts mp cp pargs Hfp Hbp) as Hpargs.
        destruct (Hargs ma ca aargs Hfa Hca) as [_ Haargs].
        rewrite unify_classes in Hu |- *.
        rewrite (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs).
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _); [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn; [injection Hu as <-; auto|].
        unfold unify_arguments in Hu |- *.
        assert (Hpair: forall pargs', (forall a, In a pargs' -> argument_ifrag a = true /\ bound_in env b K s (to_generic a) = true) ->
            fold_unify (fun inner '(t, a) => unify env n t a inner) (combine aargs pargs') (Ongoing s) = Some (Ongoing u) ->
            u = s /\ fold_unify (fun inner '(t, a) => unify env (F + 2 + S K) t a inner)
                (combine aargs (map (instantiate env b) pargs')) (Ongoing s) = Some (Ongoing s)).
        { intros pargs' Hp' Hf. rewrite <- (map_id aargs).
          apply (fold_map n (F + 2 + S K) (fun a => a) (instantiate env b) aargs pargs' u Hf).
          intros t a u0 Ht Ha E. destruct (Hp' a Ha) as [Hfa' Hba']. destruct (Haargs t Ht) as [Hft' Hct'].
          destruct (IHaa a t u0 Hfa' Hft' Hct' Hba' E) as [-> Hi]. split; [reflexivity|exact (Hmono _ _ Hi)]. }
        destruct (Class_eq_dec cp ca) as [<-|Hne].
        - rewrite class_eqb_refl in Hu |- *. exact (Hpair pargs Hpargs Hu).
        - rewrite (class_eqb_false _ _ Hne) in Hu |- *.
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          destruct (supertype_commute_variables cp ca pargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          rewrite Hcomm. exact (Hpair _ Hnormp Hu). }
      destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]];
      destruct (ifrag_cases P HP) as [[mp [cp [pargs [-> _]]]]|[[m_bot ->]|[[mp [cp [pargs [-> HP']]]]|[p [-> Hfb]]]]];
          try (unfold bottom_type in *).
      + exact (Hroot _ _ _ _ _ _ HP HA' HcA Hb H).
      + exact (Hroot _ _ _ _ _ _ HP HA' HcA Hb H).
      + rewrite unify_class_nullable in H. discriminate H.
      + destruct (bound_variable p [] Hb) as [o [x [st [vb [ob [X [Ex [Hx [Hl [He [Hup [Hlo [HX Hc]]]]]]]]]]]]].
        apply (unify_variable_assignee n None false p [] st _ u Hl He HA') in H. rewrite Hup in H.
        destruct (read_leaf n vb ob X o x _ u HX Hx HA' Hc H) as [-> Hr]. split; [reflexivity|].
        rewrite (inst_variable p [] _ _ _ Ex). apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hr].
      + assert (HA2: afrag (RootResolved ma ca aargs) = true) by exact HA''.
        rewrite unify_nullable_class in H. destruct (IHa _ _ u (ifrag_nfrag _ HP) HA2 HcA Hb H) as [-> Hi]. split; [reflexivity|].
        rewrite (inst_root mp cp pargs (ifrag_no_generics _ HP) ltac:(bvars)) in Hi |- *. rewrite unify_nullable_class. exact (Hmono _ _ Hi).
      + assert (HA2: afrag (RootResolved ma ca aargs) = true) by exact HA''.
        rewrite unify_nullable_class in H. destruct (IHa _ _ u (ifrag_nfrag _ HP) HA2 HcA Hb H) as [-> Hi]. split; [reflexivity|].
        rewrite (inst_root _ _ _ (ifrag_no_generics _ HP) ltac:(bvars)) in Hi |- *. rewrite unify_nullable_class. exact (Hmono _ _ Hi).
      + assert (HA2: afrag (RootResolved ma ca aargs) = true) by exact HA''.
        assert (Hb': bound_in env b K s (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
        rewrite unify_nullable_nullable in H. destruct (IHa _ _ u (ifrag_nfrag _ HP') HA2 HcA Hb' H) as [-> Hi]. split; [reflexivity|].
        rewrite (inst_root mp cp pargs (ifrag_no_generics _ HP') ltac:(bvars)) in Hi. rewrite (inst_nullable mp cp pargs (ifrag_no_generics _ HP') ltac:(bvars)).
        rewrite unify_nullable_nullable. exact (Hmono _ _ Hi).
      + destruct (bound_variable p [] Hb) as [o [x [st [vb [ob [X [Ex [Hx [Hl [He [Hup [Hlo [HX Hc]]]]]]]]]]]]].
        apply (unify_variable_assignee n None false p [] st _ u Hl He HA') in H. rewrite Hup in H.
        destruct (read_leaf n vb ob X o x _ u HX Hx HA' Hc H) as [-> Hr]. split; [reflexivity|].
        rewrite (inst_variable p [] _ _ _ Ex). apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hr].
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] u HP HA HcA Hb H; try discriminate HP; try discriminate HA.
      simpl in HP, HA. destruct (bound_in_argument env b K s vt ot (to_generic nt) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag na = true) by exact HA.
      rewrite (instantiate_argument vt ot nt HP Hbn).
      rewrite (unify_type_arguments_exact n vt ot nt va oa na (nfrag_not_capturable nt HP Hbn)) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      assert (Hfi: in_fragment env (inst nt) = true) by exact (instance_in_fragment env wf b K s Hbf (to_generic nt) (nfrag_sfrag nt HP) Hbn).
      rewrite (unify_type_arguments env (F + 2 + S K) vt _ (inst nt) va oa na s (fragment_not_variable env _ Hfi)).
      pose proof (instantiation_preserves_ownership_assignability b oa ot Ho) as Ho'.
      rewrite (ownership_not_instantiated oa Hoa) in Ho'. rewrite Ho'.
      destruct vt, va; unfold compare_variances in H |- *; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHt nt na w HP HAf Hcn Hbn E1) as [-> Hi1].
           destruct (IHa nt na u HP HAf Hcn Hbn H) as [-> Hi2]. split; [reflexivity|].
           rewrite (Hmono _ _ Hi1). exact (Hmono _ _ Hi2). }
      all: first
          [ destruct (IHt nt na u HP HAf Hcn Hbn H) as [-> Hi]
          | destruct (IHa nt na u HP HAf Hcn Hbn H) as [-> Hi]
          | destruct (IHt nt top_type u HP top_in_afrag eq_refl Hbn H) as [-> Hi]
          | destruct (IHa nt bottom_type u HP bottom_in_afrag eq_refl Hbn H) as [-> Hi] ];
          split; [reflexivity|exact (Hmono _ _ Hi)].
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] u HP HA HcA Hb H; try discriminate HP; try discriminate HA.
      simpl in HP, HA. destruct (bound_in_argument env b K s vp op (to_generic np) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag na = true) by exact HA.
      rewrite (instantiate_argument vp op np HP Hbn).
      rewrite (unify_type_arguments env n va oa na vp op np s (fragment_not_variable env _ HA)) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      rewrite (unify_type_arguments env (F + 2 + S K) va oa na vp _ (inst np) s (fragment_not_variable env _ HA)).
      pose proof (instantiation_preserves_ownership_assignability b op oa Ho) as Ho'.
      rewrite (ownership_not_instantiated oa Hoa) in Ho'. rewrite Ho'.
      destruct va, vp; unfold compare_variances in H |- *; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHa np na w HP HAf Hcn Hbn E1) as [-> Hi1].
           destruct (IHt np na u HP HAf Hcn Hbn H) as [-> Hi2]. split; [reflexivity|].
           rewrite (Hmono _ _ Hi1). exact (Hmono _ _ Hi2). }
      all: first
          [ destruct (IHa np na u HP HAf Hcn Hbn H) as [-> Hi]; split; [reflexivity|exact (Hmono _ _ Hi)]
          | destruct (IHt np na u HP HAf Hcn Hbn H) as [-> Hi]; split; [reflexivity|exact (Hmono _ _ Hi)]
          | match type of H with unify env ?k ?x ?y _ = _ =>
              let Hx := fresh "Hx" in let Hy := fresh "Hy" in
              assert (Hx: in_fragment env x = true) by first [exact HA|exact (top_in_fragment env wf)|exact (bottom_in_fragment env wf)];
              assert (Hy: in_fragment env y = true) by first [exact HA|exact (top_in_fragment env wf)|exact (bottom_in_fragment env wf)];
              pose proof (keeps k x y u Hx Hy H) as ->;
              split; [reflexivity|apply (unify_fuel_monotone env k); [lia|exact H]]
            end ].
Qed.

(* A parameter whose type is a type variable of a mutability given to it, narrowed or made nullable,
   takes what the type it stands for takes, of that mutability and nullability *)
Lemma exact_parameter: forall n P A u, pfrag P = true -> afrag A = true -> closed A = true ->
    bound_in env b K s (pgeneric P) = true -> unify env n P A (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (n * S (S K) + 2) (inst P) A (Ongoing s) = Some (Ongoing s).
Proof.
    intros n P A u HP HA HcA Hb H. destruct (pfrag_cases P HP) as [HP'|[[gm [nn [p [EP [Hs _]]]]]|[gm [nn [p [EP [Hs _]]]]]]].
    { rewrite (pgeneric_ifrag P HP') in Hb. exact (proj1 (inference_with_arguments n) P A u HP' HA HcA Hb H). }
    all: subst P; destruct (binds_ref_some env wf b K s (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]; cbn [param_of] in Ex.
    - exact (reference_target n gm nn p o x _ A u Ex Hs (or_introl eq_refl) HA H).
    - exact (reference_target n gm nn p o x _ A u Ex Hs (or_intror eq_refl) HA H).
Qed.

Lemma inst_pfrag_in_fragment: forall P, pfrag P = true -> bound_in env b K s (pgeneric P) = true -> in_fragment env (inst P) = true.
Proof.
    intros P HP Hb. destruct (pfrag_cases P HP) as [HP'|[[gm [nn [p [-> _]]]]|[gm [nn [p [-> _]]]]]].
    - rewrite (pgeneric_ifrag P HP') in Hb. exact (instance_in_fragment env wf b K s Hbf (to_generic P) (ifrag_sfrag P HP') Hb).
    - destruct (binds_ref_some env wf b K s (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj1 (inst_reference gm nn p [] _ _ _ Ex)). exact (ref_apply_in_fragment gm nn x (Hbf p o x Ex)).
    - destruct (binds_ref_some env wf b K s (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj2 (inst_reference gm nn p [] _ _ _ Ex)). apply (in_fragment_rewrap env).
      exact (ref_apply_in_fragment gm nn x (Hbf p o x Ex)).
Qed.

(* An intersection, not nullable, as the type of a parameter: each component takes the argument, its
   instance a class type, the type variables among them what unify gives them to take *)
(* The instance of a component of an intersection that is the type of a parameter, of the fragment *)
Lemma inst_compfrag_in_fragment: forall C, compfrag C = true -> bound_in env b K s (to_generic C) = true -> in_fragment env (inst C) = true.
Proof.
    intros C HC HbC. destruct (compfrag_cases C HC) as [Hif|[gm [nn [q [-> [Hsq _]]]]]].
    - assert (HpC: pfrag C = true) by (unfold pfrag; rewrite Hif; reflexivity).
      apply (inst_pfrag_in_fragment C HpC). rewrite (pgeneric_ifrag C Hif). exact HbC.
    - destruct (binds_ref_some env wf b K s (mkGenericRef gm nn q []) HbC) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj1 (inst_reference gm nn q [] _ _ _ Ex)). exact (ref_apply_in_fragment gm nn x (Hbf q o x Ex)).
Qed.

Lemma inst_component_shape: forall C, param_shape C -> inst_component env b (to_generic C) = inst C.
Proof. intros C [[m [cl [args [-> | ->]]]]|[gm [nn [q ->]]]]; reflexivity. Qed.

(* An intersection as the type of a parameter, of components of the shapes above: of an argument that may
   be null, one whose components keep their nullability; each component takes the argument *)
Lemma exact_components: forall n cs a u, (forall C, In C cs -> compfrag C = true) -> (forall C, In C cs -> param_shape C) ->
    afrag a = true -> closed a = true -> bound_in env b K s (Intersection (map to_generic cs)) = true ->
    unify env n (Intersection cs) a (Ongoing s) = Some (Ongoing u) ->
    u = s /\ forall C, In C cs -> exists f, unify env f (inst C) a (Ongoing []) = Some (Ongoing []).
Proof.
    intros n cs a u HSi Hcase Ha HaC Hb H.
    (* each component takes what unify lets it take, its instance of the fragment *)
    assert (Hone: forall C, In C cs -> forall k a' u', afrag a' = true -> closed a' = true ->
        unify env k C a' (Ongoing s) = Some (Ongoing u') ->
        u' = s /\ in_fragment env (inst C) = true /\ exists f, unify env f (inst C) a' (Ongoing []) = Some (Ongoing [])).
    { intros C HC k a' u' Ha' HcA' E.
      pose proof (bound_in_component env b K s _ _ Hb (in_map to_generic _ _ HC)) as HbC.
      destruct (compfrag_cases C (HSi C HC)) as [Hif|[gm [nn [q [-> [Hsq _]]]]]].
      - assert (HpC: pfrag C = true) by (unfold pfrag; rewrite Hif; reflexivity).
        assert (HbC': bound_in env b K s (pgeneric C) = true) by (rewrite (pgeneric_ifrag C Hif); exact HbC).
        destruct (exact_parameter k C a' u' HpC Ha' HcA' HbC' E) as [-> Hi].
        pose proof (inst_pfrag_in_fragment C HpC HbC') as HfI.
        split; [reflexivity|]. split; [exact HfI|]. exists (k * S (S K) + 2).
        exact (proj1 (states_irrelevant _) _ _ s [] HfI (afrag_in_fragment a' Ha') Hi).
      - destruct (binds_ref_some env wf b K s (mkGenericRef gm nn q []) HbC) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (reference_target k gm nn q o x _ a' u' Ex Hsq (or_introl eq_refl) Ha' E) as [-> Hi].
        assert (HfI: in_fragment env (inst (TypeVariable (mkGenericRef gm nn q []))) = true).
        { rewrite (proj1 (inst_reference gm nn q [] _ _ _ Ex)). exact (ref_apply_in_fragment gm nn x (Hbf q o x Ex)). }
        split; [reflexivity|]. split; [exact HfI|]. exists (k * S (S K) + 2).
        exact (proj1 (states_irrelevant _) _ _ s [] HfI (afrag_in_fragment a' Ha') Hi). }
    assert (Hfailed: forall (g: Unification -> EType -> option Unification) l, (forall x, g Failed x = Some Failed) ->
        fold_unify g l Failed = Some Failed).
    { intros g l Hg. induction l as [|x l IH]; [reflexivity|]. simpl. rewrite Hg. simpl. exact IH. }
    destruct n as [|n1]; [discriminate H|].
    pose proof (afrag_in_fragment a Ha) as Hcf.
    (* the body of the intersection: of a nullable argument, only where the intersection may be null *)
    assert (Hbody: intersection_body env (unify env n1) cs a s = Some (Ongoing u)).
    { rewrite unify_step_once in H. unfold unify_step, unify_intersection in H.
      destruct (fragment_cases env a Hcf) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]]; [exact H|].
      destruct (negb (is_nullable env (Intersection cs))); [discriminate H|exact H]. }
    clear H. rename Hbody into H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) cs) in H.
    set (vs := filter is_type_variable cs) in H.
    (* the components that are no type variables *)
    assert (Hns: forall l t, (forall C, In C l -> In C cs) ->
        fold_unify (fun inner component => unify env n1 component a inner) l (Ongoing s) = Some (Ongoing t) ->
        t = s /\ forall C, In C l -> exists f, unify env f (inst C) a (Ongoing []) = Some (Ongoing [])).
    { induction l as [|C l IH]; intros t Hl E; simpl in E.
      - injection E as <-. split; [reflexivity|intros _ []].
      - destruct (unify env n1 C a (Ongoing s)) as [[t1|]|] eqn:E1; simpl in E.
        + destruct (Hone C (Hl C (or_introl eq_refl)) n1 _ t1 Ha HaC E1) as [-> [_ HC]].
          destruct (IH t (fun C' H' => Hl C' (or_intror H')) E) as [-> Hall]. split; [reflexivity|].
          intros C' [<-|H']; [exact HC|exact (Hall C' H')].
        + rewrite Hfailed in E; [discriminate E|]. intros x. apply unify_keeps_failure.
        + discriminate E. }
    destruct (fold_unify (fun inner component => unify env n1 component a inner) ns (Ongoing s))
        as [[s2|]|] eqn:E2; cbn beta iota in H; try discriminate H.
    destruct (Hns ns s2 (fun C HC => proj1 (proj1 (filter_In _ C cs) HC)) E2) as [-> Hnsall].
    (* the type variables among them, given what the covering component leaves them, or the argument *)
    assert (Hvs: forall na l t, afrag na = true -> closed na = true ->
        (forall y f, in_fragment env y = true -> unify env f y na (Ongoing []) = Some (Ongoing []) ->
            exists f', unify env f' y a (Ongoing []) = Some (Ongoing [])) ->
        (forall C, In C l -> In C cs) ->
        fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component a inner
            | r => r
            end) l (Ongoing s) = Some (Ongoing t) ->
        t = s /\ forall C, In C l -> exists f, unify env f (inst C) a (Ongoing []) = Some (Ongoing [])).
    { intros na l. induction l as [|C l IH]; intros t Hna HcNa Hthrough Hl E; simpl in E.
      - injection E as <-. split; [reflexivity|intros _ []].
      - assert (HC: In C cs) by exact (Hl C (or_introl eq_refl)).
        destruct (unify env n1 C na (Ongoing s)) as [[t1|]|] eqn:E1; simpl in E.
        + destruct (Hone C HC n1 na t1 Hna HcNa E1) as [-> [HfI [f Hf]]].
          destruct (Hthrough _ f HfI Hf) as [f' Hf'].
          destruct (IH t Hna HcNa Hthrough (fun C' H' => Hl C' (or_intror H')) E) as [-> Hall]. split; [reflexivity|].
          intros C' [<-|H']; [exists f'; exact Hf'|exact (Hall C' H')].
        + destruct (unify env n1 C a (Ongoing s)) as [[t2|]|] eqn:E2'; simpl in E.
          * destruct (Hone C HC n1 _ t2 Ha HaC E2') as [-> [_ HC']].
            destruct (IH t Hna HcNa Hthrough (fun C' H' => Hl C' (or_intror H')) E) as [-> Hall]. split; [reflexivity|].
            intros C' [<-|H']; [exact HC'|exact (Hall C' H')].
          * rewrite Hfailed in E; [discriminate E|]. intros x. rewrite !unify_keeps_failure. reflexivity.
          * discriminate E.
        + discriminate E. }
    assert (Hvl: forall C, In C vs -> In C cs) by (intros C HC; exact (proj1 (proj1 (filter_In _ C cs) HC))).
    assert (Hdone: (forall C, In C vs -> exists f, unify env f (inst C) a (Ongoing []) = Some (Ongoing [])) ->
        forall C, In C cs -> exists f, unify env f (inst C) a (Ongoing []) = Some (Ongoing [])).
    { intros Hvsall C HC. destruct (is_type_variable C) eqn:Ev.
      - apply Hvsall. apply filter_In. split; [exact HC|exact Ev].
      - apply Hnsall. apply filter_In. split; [exact HC|]. rewrite Ev. reflexivity. }
    destruct (find_first (fun component => unify env n1 component a (Ongoing s)) ns)
        as [[[cov s3]|]|] eqn:E3; cbn beta iota in H; [| |discriminate H].
    - (* covered: the variables take Any of the mutability of the argument, as far as the covering component allows *)
      destruct (Ops.find_first_found _ _ _ _ E3) as [Hcov Ecov].
      destruct (Hone cov (proj1 (proj1 (filter_In _ cov cs) Hcov)) n1 _ s3 Ha HaC Ecov) as [-> _].
      apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
      assert (Hm': Model.is_subtype_of (assignment_mutability env a) (intersect_mutability (mutability_of env a) (mutability_of env cov)) = true).
      { apply Ops.intersect_mutability_greatest.
        - destruct (fragment_cases env a Hcf) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
              exact (assigned_below_own (RootResolved ma ca aargs) eq_refl).
        - destruct (Hcase cov Hcov) as [[mc [cl1 [argsc [-> | ->]]]]|[gm [nn [q ->]]]]; [| |discriminate Hv].
          + destruct n1 as [|n2]; [discriminate Ecov|].
            destruct (fragment_cases env a Hcf) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
                [|rewrite unify_class_nullable in Ecov; discriminate Ecov].
            rewrite unify_classes in Ecov. destruct (base_type_is_subtype_of env ca cl1); [|discriminate Ecov].
            destruct (Model.is_subtype_of _ _) eqn:Em; [|discriminate Ecov].
            exact (mutability_trans _ _ _ Em (assigned_below_own (RootResolved mc cl1 argsc) eq_refl)).
          + destruct n1 as [|n2]; [discriminate Ecov|]. rewrite (unify_nullable_target env n2 _ a s Hcf) in Ecov.
            destruct n2 as [|n3]; [discriminate Ecov|].
            destruct (fragment_cases env a Hcf) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]]; cbn [without_null] in Ecov;
                rewrite unify_classes in Ecov; (destruct (base_type_is_subtype_of env ca cl1); [|discriminate Ecov]);
                (destruct (Model.is_subtype_of _ _) eqn:Em; [|discriminate Ecov]);
                exact (mutability_trans _ _ _ Em (assigned_below_own (RootResolved mc cl1 argsc) eq_refl)). }
      set (m' := intersect_mutability (mutability_of env a) (mutability_of env cov)) in H, Hm'.
      (* what the variables take: Any of that mutability, nullable where the argument is *)
      assert (Hna: afrag (if is_nullable env a then Nullable (RootResolved (Some m') any []) else RootResolved (Some m') any []) = true
          /\ closed (if is_nullable env a then Nullable (RootResolved (Some m') any []) else RootResolved (Some m') any []) = true
          /\ exists f1, unify env f1 (if is_nullable env a then Nullable (RootResolved (Some m') any []) else RootResolved (Some m') any [])
              a (Ongoing []) = Some (Ongoing [])).
      { destruct (any_afrag m') as [Haf Hac].
        destruct (fragment_cases env a Hcf) as [[ma [ca [aargs Ea]]]|[ma [ca [aargs [Ea _]]]]]; rewrite Ea in Hm' |- *; cbn [is_nullable].
        - split; [exact Haf|]. split; [exact Hac|]. exists 1. apply below_any. exact Hm'.
        - split; [exact Haf|]. split; [exact Hac|]. exists 2.
          rewrite (unify_nullable_target env 1 _ (Nullable (RootResolved ma ca aargs)) [] ltac:(rewrite <- Ea; exact Hcf)).
          cbn [without_null]. apply below_any. exact Hm'. }
      set (na := if is_nullable env a then Nullable (RootResolved (Some m') any []) else RootResolved (Some m') any []) in H, Hna.
      destruct Hna as [Haf [Hac [f1 E1]]].
      assert (Hth: forall y f, in_fragment env y = true -> unify env f y na (Ongoing []) = Some (Ongoing []) ->
          exists f', unify env f' y a (Ongoing []) = Some (Ongoing [])).
      { intros y f Hy Ey. exact (through_class a na y f1 f Hcf (afrag_in_fragment _ Haf) Hy E1 Ey). }
      destruct (Hvs _ vs u Haf Hac Hth Hvl H) as [-> Hvsall]. split; [reflexivity|exact (Hdone Hvsall)].
    - (* nothing covers: the variables take the argument *)
      assert (Hth: forall y f, in_fragment env y = true -> unify env f y a (Ongoing []) = Some (Ongoing []) ->
          exists f', unify env f' y a (Ongoing []) = Some (Ongoing []))
          by (intros y f _ Ey; exists f; exact Ey).
      destruct (Hvs _ vs u Ha HaC Hth Hvl H) as [-> Hvsall]. split; [reflexivity|exact (Hdone Hvsall)].
Qed.

(* A parameter whose type is an intersection, nullable or not, or of pfrag, takes what its instance takes *)
Lemma exact_qparameter: forall n P A u, kqfrag P = true -> afrag A = true -> closed A = true ->
    bound_in env b K s (pgeneric P) = true -> bound_in env b K [] (pgeneric P) = true ->
    unify env n P A (Ongoing s) = Some (Ongoing u) ->
    u = s /\ exists f, unify env f (inst P) A (Ongoing []) = Some (Ongoing []).
Proof.
    intros n P A u HK HA HcA Hb Hb0 H. destruct (kqfrag_cases P HK) as [HQ|[cs [-> Hk]]].
    2: { (* an intersection whose components keep their nullability: ofComponents of the instances of the
           components, class types, nullable or not, which each take the argument *)
      destruct (kept_param_facts cs Hk) as [Hl Hcs].
      destruct (exact_components n cs A u (fun C HC => proj1 (Hcs C HC)) (fun C HC => proj1 (proj2 (Hcs C HC))) HA HcA Hb H)
          as [-> Hall].
      split; [reflexivity|].
      change (inst (Intersection cs)) with (of_components env (flat_map intersected_components (map (inst_component env b) (map to_generic cs)))).
      apply below_flat_components; [rewrite !length_map; exact Hl| |exact (afrag_in_fragment A HA)|].
      - intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]]. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
        rewrite (inst_component_shape C (proj1 (proj2 (Hcs C HC)))).
        exact (inst_compfrag_in_fragment C (proj1 (Hcs C HC)) (bound_in_component env b K s _ _ Hb (in_map _ _ _ HC))).
      - intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]]. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
        rewrite (inst_component_shape C (proj1 (proj2 (Hcs C HC)))). exact (Hall C HC). }
    destruct (qfrag_cases P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]].
    - destruct (exact_parameter n P A u HP HA HcA Hb H) as [-> Hi]. split; [reflexivity|]. exists (n * S (S K) + 2).
      exact (proj1 (states_irrelevant _) _ _ s [] (inst_pfrag_in_fragment P HP Hb) (afrag_in_fragment A HA) Hi).
    - assert (Hb': bound_in env b K s (Intersection (map to_generic cs)) = true) by (destruct EP as [-> | ->]; exact Hb).
      assert (Hb0': bound_in env b K [] (Intersection (map to_generic cs)) = true) by (destruct EP as [-> | ->]; exact Hb0).
      destruct (bound_in_weak env wf b K [] _ Hb0') as [Hbx Htop].
      assert (Hbelow: forall a, in_fragment env a = true ->
          (forall C, In C cs -> exists f, unify env f (inst C) a (Ongoing []) = Some (Ongoing [])) ->
          exists f, unify env f (inst_nested env b (Intersection (map to_generic cs))) a (Ongoing []) = Some (Ongoing [])).
      { intros a Ha Hall. apply (below_intersection_instance b K (map to_generic cs) a Hbf Hcs Hbx); [|exact Ha|].
        - intros c Hc. cbn [bound_in_top_h] in Htop. rewrite forallb_forall in Htop. exact (Htop c Hc).
        - intros c Hc. apply in_map_iff in Hc. destruct Hc as [C [<- HC]]. exact (Hall C HC). }
      destruct EP as [-> | ->].
      + destruct (exact_components n cs A u HSi (fun C HC => param_shape_of cs C HSi Hcs HC) HA HcA Hb' H) as [-> Hall].
        split; [reflexivity|].
        exact (Hbelow A (afrag_in_fragment A HA) Hall).
      + pose proof (afrag_in_fragment A HA) as HA'.
        destruct n as [|n]; [discriminate H|]. rewrite (unify_nullable_target env n _ A s HA') in H.
        destruct (without_null_afrag A HA) as [HA0 HcA0]. rewrite <- HcA0 in HcA.
        destruct (exact_components n cs _ u HSi (fun C HC => param_shape_of cs C HSi Hcs HC) HA0 HcA Hb' H) as [-> Hall].
        split; [reflexivity|].
        destruct (Hbelow _ (afrag_in_fragment _ HA0) Hall) as [f Hf].
        change (inst (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection (map to_generic cs)))).
        exists (S f). exact (unify_rewrap_target _ _ A [] _ HA' Hf).
Qed.

End Exact.

(* ---------------------------------------------------------------------------------------------- *)
(* Capturing the type arguments of a receiver                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* The type of the receiver parameter of a member function: its class, with the type parameters of
   the class as type variables. Kotlin has no ownership yet; any ownership takes them all. *)
Definition receiver_leaf (v: TypeParameterId * EType): EType :=
    TypeArgument Model.invariant any_ownership (TypeVariable (mkGenericRef None false (fst v) [])).

(* The variable states for inferring the type parameters of the class of a receiver: none bound yet,
   all may be captured *)
Definition receiver_states (vars: list (TypeParameterId * EType)): VariableStates :=
    map (fun '(p, bound) => (p, mkVariableState bound (initial_upper_bound bound) bottom_type false true)) vars.

Lemma receiver_states_for_inference: forall vars,
    for_inference_of vars (map fst vars) = Ongoing (receiver_states vars).
Proof.
    intros vars. unfold for_inference_of, receiver_states. f_equal. apply map_ext_in. intros [p bound] Hin.
    replace (existsb (param_eqb p) (map fst vars)) with true; [reflexivity|].
    symmetry. apply existsb_exists. exists p. split; [apply (in_map fst _ _ Hin)|apply param_eqb_refl].
Qed.

Lemma lookup_receiver_states: forall vars p bound, NoDup (map fst vars) -> In (p, bound) vars ->
    lookup_state (receiver_states vars) p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true).
Proof.
    intros vars. induction vars as [|[q bq] rest IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_filter_other: forall (st: VariableStates) p q, p <> q ->
    lookup_state (filter (fun '(p', _) => negb (param_eqb p p')) st) q = lookup_state st q.
Proof.
    intros st p q Hne. induction st as [|[p' v'] rest IH]; [reflexivity|]. simpl.
    destruct (param_eqb p p') eqn:E1; simpl.
    - apply param_eqb_eq in E1. subst p'. destruct (param_eqb q p) eqn:E2; [apply param_eqb_eq in E2; congruence|exact IH].
    - destruct (param_eqb q p'); [reflexivity|exact IH].
Qed.

Lemma lookup_set_same: forall st p v, lookup_state (set_state st p v) p = Some v.
Proof. intros. unfold set_state. simpl. rewrite param_eqb_refl. reflexivity. Qed.

Lemma lookup_set_other: forall st p q v, p <> q -> lookup_state (set_state st p v) q = lookup_state st q.
Proof.
    intros st p q v Hne. unfold set_state. simpl. destruct (param_eqb q p) eqn:E; [apply param_eqb_eq in E; congruence|].
    exact (lookup_filter_other st p q Hne).
Qed.

(* One type argument of the receiver, captured *)
Lemma capture_step: forall n p bound s y u,
    lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true) ->
    in_fragment env bound = true -> argument_in_fragment env y = true ->
    unify env n (receiver_leaf (p, bound)) y (Ongoing s) = Some (Ongoing u) ->
    u = set_state s p (mkVariableState bound y y true true).
Proof.
    intros n p bound s [| | | |vy oy Y| |] u Hl Hb Hy H; simpl in Hy; try discriminate Hy.
    destruct n as [|n]; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_type_argument, receiver_leaf in H. cbn beta iota zeta in H.
    replace (ownership_is_assignable_to oy any_ownership) with true in H by (destruct oy; reflexivity).
    cbn [negb fst snd] in H. unfold capturable in H. cbn beta iota in H. rewrite Hl in H. cbn [is_capturable is_exact negb andb] in H.
    unfold plus_exact_binding in H. rewrite Hl in H. cbn [upper_bound lower_bound static_upper_bound is_capturable] in H.
    rewrite (initial_in_fragment bound Hb) in H. unfold plus_binding_check, plus_static_check in H. cbn [static_upper_bound] in H. rewrite (in_fragment_no_vars bound Hb) in H.
    destruct (unify env n bound Y (Ongoing s)) as [[w|]|] eqn:E1; try discriminate H.
    destruct (unify env n (TypeArgument vy oy Y) bottom_type (Ongoing s)) as [[w'|]|] eqn:E2; try discriminate H.
    assert (H': Some (Ongoing (set_state w' p (mkVariableState bound (TypeArgument vy oy Y) (TypeArgument vy oy Y) true true)))
        = Some (Ongoing u)) by (destruct vy; exact H).
    injection H' as <-. f_equal.
    destruct n as [|n]; [discriminate E2|].
    destruct vy; rewrite unify_step_once in E2; unfold unify_step, unify_type_argument in E2; cbn beta iota zeta in E2;
        try (injection E2 as <-; reflexivity).
    - exact (proj1 (keeps_states_with_arguments env wf n) Y bottom_type s w' Hy (bottom_in_fragment env wf) E2).
    - exact (proj1 (keeps_states_with_arguments env wf n) Y bottom_type s w' Hy (bottom_in_fragment env wf) E2).
Qed.

(* All of them *)
Lemma capture_arguments: forall n vars ys s u,
    NoDup (map fst vars) -> length ys = length vars ->
    (forall y, In y ys -> argument_in_fragment env y = true) ->
    (forall p bound, In (p, bound) vars ->
        lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true) /\ in_fragment env bound = true) ->
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine (map receiver_leaf vars) ys) (Ongoing s) = Some (Ongoing u) ->
    (forall i p bound y, nth_error vars i = Some (p, bound) -> nth_error ys i = Some y ->
        lookup_state u p = Some (mkVariableState bound y y true true))
    /\ (forall q, ~ In q (map fst vars) -> lookup_state u q = lookup_state s q).
Proof.
    intros n vars. induction vars as [|[p bound] rest IH]; intros [|y ys] s u Hnd Hl Hys Hvars H; simpl in Hl; try discriminate Hl.
    - simpl in H. injection H as <-. split; [intros [|i]; discriminate|reflexivity].
    - inversion Hnd as [|? ? Hnotin Hnd']. subst.
      simpl in H. destruct (unify env n (receiver_leaf (p, bound)) y (Ongoing s)) as [[s1|]|] eqn:E; [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      destruct (Hvars p bound (or_introl eq_refl)) as [Hlp Hbp].
      pose proof (capture_step n p bound s y s1 Hlp Hbp (Hys y (or_introl eq_refl)) E) as ->.
      destruct (IH ys (set_state s p (mkVariableState bound y y true true)) u Hnd' ltac:(lia) (fun y' Hy' => Hys y' (or_intror Hy'))) as [IH1 IH2]; [|exact H|].
      + intros q bq Hin. destruct (Hvars q bq (or_intror Hin)) as [Hlq Hbq]. split; [|exact Hbq].
        rewrite lookup_set_other; [exact Hlq|]. intros ->. apply Hnotin. exact (in_map fst _ _ Hin).
      + split.
        * intros [|i] q bq y' Hq Hy'.
          -- simpl in Hq, Hy'. injection Hq as <- <-. injection Hy' as <-. rewrite (IH2 p Hnotin). apply lookup_set_same.
          -- exact (IH1 i q bq y' Hq Hy').
        * intros q Hq. simpl in Hq. rewrite (IH2 q (fun H' => Hq (or_intror H'))). apply lookup_set_other.
          intros ->. apply Hq. left. reflexivity.
Qed.

(* Unifying the receiver parameter with the receiver binds each type parameter of the class exactly
   to the type argument of the receiver in its place *)
Lemma receiver_captures: forall n mr c vars ma ys u,
    c <> nothing -> map fst vars = parameter_ids env c ->
    (forall p bound, In (p, bound) vars -> in_fragment env bound = true) ->
    in_fragment env (RootResolved ma c ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf vars)) (RootResolved ma c ys) (Ongoing (receiver_states vars))
        = Some (Ongoing u) ->
    forall i p bound y, nth_error vars i = Some (p, bound) -> nth_error ys i = Some y ->
        lookup_state u p = Some (mkVariableState bound y y true true).
Proof.
    intros n mr c vars ma ys u Hc Hids Hbounds Hf H. destruct n as [|n]; [discriminate H|].
    destruct (root_in_fragment env ma c ys Hf) as [Hl Hys].
    assert (Hnd: NoDup (map fst vars)) by (rewrite Hids; apply (wf_parameter_ids_are_distinct env wf)).
    rewrite unify_classes in H.
    replace (base_type_is_subtype_of env c c) with true in H by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
    destruct (Model.is_subtype_of _ _); [|discriminate H].
    rewrite (class_eqb_false c nothing Hc), class_eqb_refl in H. unfold unify_arguments in H.
    refine (proj1 (capture_arguments n vars ys (receiver_states vars) u Hnd _ Hys _ H)).
    - rewrite Hl, <- Hids, length_map. reflexivity.
    - intros p bound Hin. split; [exact (lookup_receiver_states vars p bound Hnd Hin)|exact (Hbounds p bound Hin)].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Member calls                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma bound_in_transfer: forall b K s K' s', bindings_in_fragment env b -> K <= K' -> forall t, tfrag env t = true ->
    bound_in env b K s t = true -> bound_in env b K' s' t = true.
Proof.
    intros b K s K' s' Hbf HK. apply (bound_in_lift env wf b K s b K' s'); [|intros o Ho; exact Ho].
    intros g Hs Hb. destruct (bound_in_generic env wf b K s g Hb) as [Hr Hbe]. pose proof (generic_bound_tfrag env wf g Hs) as Hfb.
    set (bd := effective_bound env g) in *.
    unfold binds_ref, respects in Hr |- *. change (effective_bound env g) with bd in Hr |- *.
    destruct (lookup_binding b (param_of g)) as [[| | | |[] o x| |]|] eqn:Ex; try discriminate Hr.
    apply andb_true_iff in Hr. destruct Hr as [Ho Hr]. rewrite Ho.
    pose proof (inst_ref_in_fragment env g x (Hbf _ o x Ex)) as Hx.
    destruct (unify env K (inst_nested env b bd) (inst_ref env g x) (Ongoing s)) as [[w|]|] eqn:E; try discriminate Hr.
    pose proof (proj1 (instance_facts env wf b K s Hbf _ bd (le_n _) Hfb Hbe)) as HFb.
    pose proof (cfrag_keeps env wf K _ _ s w HFb Hx E) as ->.
    rewrite (unify_fuel_monotone env K K' _ _ (Ongoing s') (Ongoing s') HK (cfrag_states_irrelevant K _ _ s s' HFb Hx E)).
    reflexivity.
Qed.

Lemma kqfrag_transfer: forall b K s K' s', bindings_in_fragment env b -> K <= K' -> forall P, kqfrag P = true ->
    bound_in env b K s (pgeneric P) = true -> bound_in env b K' s' (pgeneric P) = true.
Proof.
    intros b K s K' s' Hbf HK P HP Hb. destruct (kqfrag_cases P HP) as [HQ|[cs [-> Hk]]].
    - exact (bound_in_transfer b K s K' s' Hbf HK _ (qfrag_tfrag P HQ) Hb).
    - destruct (kept_param_facts cs Hk) as [_ Hcs].
      change (forallb (bound_in env b K' s') (map to_generic cs) = true). apply forallb_forall. intros c Hc.
      apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
      apply (bound_in_transfer b K s K' s' Hbf HK _ (sfrag_tfrag env _ (proj2 (proj2 (Hcs C HC))))).
      exact (bound_in_component env b K s _ _ Hb (in_map _ _ _ HC)).
Qed.

Lemma lookup_combine_nth: forall (ids: list TypeParameterId) (xs: list EType) p a,
    lookup_binding (combine ids xs) p = Some a -> exists i, nth_error ids i = Some p /\ nth_error xs i = Some a.
Proof.
    intros ids. induction ids as [|q ids IH]; intros [|x xs] p a H; simpl in H; try discriminate H.
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. injection H as <-. exists 0. split; reflexivity.
    - destruct (IH xs p a H) as [i [Hi Hx]]. exists (S i). split; assumption.
Qed.

(* The type arguments of a class type of the fragment, as bindings, are of the fragment *)
Lemma bindings_of_in_fragment: forall c xs, (forall x, In x xs -> argument_in_fragment env x = true) ->
    bindings_in_fragment env (bindings_of env c xs).
Proof.
    intros c xs Hxs p o x E. destruct (lookup_combine_nth _ _ p _ E) as [i [_ Hx]].
    exact (Hxs _ (nth_error_In _ _ Hx)).
Qed.

Definition exact_argument (x: EType): bool :=
    match x with
    | TypeArgument Model.invariant o n => is_exact_ownership o && in_fragment env n
    | _ => false
    end.

(*
 * Calling a member function is sound, where the class of the receiver is the class the function is
 * declared in, and the function has no type parameters of its own: unifying the receiver parameter
 * with the receiver binds the type parameters of the class exactly to the type arguments of the
 * receiver, capturing those of a variance. Whatever argument is then accepted for a parameter fits
 * the parameter with the type parameters of the class replaced by the type arguments of the object
 * actually called on: those of any object the receiver may be. (The return value is read, as a
 * member is: see MemberAccess.member_read_sound.)
 *)
Theorem member_call_sound: forall n mr c vars ma ys u mo xs n0 K P A fuel u',
    c <> nothing -> map fst vars = parameter_ids env c ->
    (forall p bound, In (p, bound) vars -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma c ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf vars)) (RootResolved ma c ys) (Ongoing (receiver_states vars))
        = Some (Ongoing u) ->
    (* the object it is, of exact type arguments within the bounds of the type parameters *)
    length xs = length (parameter_ids env c) -> (forall x, In x xs -> exact_argument x = true) ->
    is_assignable_to env n0 (RootResolved mo c xs) (RootResolved ma c ys) = Some true ->
    (* a parameter and an argument for it, accepted *)
    kqfrag P = true -> afrag A = true -> closed A = true -> bound_in env (bindings_of env c xs) K [] (pgeneric P) = true ->
    unify env fuel P A (Ongoing u) = Some (Ongoing u') ->
    exists fuel', is_assignable_to env fuel' A (inst (bindings_of env c xs) P) = Some true.
Proof.
    intros n mr c vars ma ys u mo xs n0 K P A fuel u' Hc Hids Hbounds Hfy Hrec Hlx Hxs Hobj HP HA HcA Hb H.
    destruct (root_in_fragment env ma c ys Hfy) as [Hly Hys].
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true).
    { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o nx| |]; try discriminate E.
      simpl in E |- *. apply andb_true_iff in E. apply E. }
    assert (Hfo: in_fragment env (RootResolved mo c xs) = true).
    { change (Nat.eqb (length xs) (length (parameter_ids env c)) && forallb (argument_in_fragment env) xs = true).
      rewrite Hlx, Nat.eqb_refl. apply forallb_forall, Hfxs. }
    (* the type arguments of the object, assignable to those of the receiver *)
    unfold is_assignable_to, empty_unification in Hobj.
    destruct (unify env n0 (RootResolved ma c ys) (RootResolved mo c xs) (Ongoing [])) as [[w|]|] eqn:Eo; try discriminate Hobj.
    pose proof (proj1 (keeps_states_with_arguments env wf n0) _ _ [] w Hfy Hfo Eo) as ->.
    destruct n0 as [|n0]; [discriminate Eo|].
    rewrite unify_classes in Eo.
    replace (base_type_is_subtype_of env c c) with true in Eo by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
    destruct (Model.is_subtype_of _ _); [|discriminate Eo].
    rewrite (class_eqb_false c nothing Hc), class_eqb_refl in Eo.
    pose proof (pairwise_of_arguments env n0 ys xs [] ltac:(lia)
        (fun t a w0 Ht Ha E => proj2 (keeps_states_with_arguments env wf n0) t a [] w0 (Hys t Ht) (Hfxs a Ha) E) Eo) as Hp.
    (* each type variable is bound exactly, to the type argument of the receiver *)
    set (K' := K + n0).
    assert (Hcover: forall p o x, lookup_binding (bindings_of env c xs) p = Some (TypeArgument Model.invariant o x) ->
        exists st vb ob X, lookup_state u p = Some st /\ is_exact st = true
            /\ upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
            /\ in_fragment env X = true
            /\ unify env (S K') (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing u) = Some (Ongoing u)).
    { intros p o x E. destruct (lookup_combine_nth _ _ p _ E) as [i [Hi Hx]].
      change (nth_error (parameter_ids env c) i = Some p) in Hi. rewrite <- Hids, nth_error_map in Hi.
      destruct (nth_error vars i) as [[p' bound]|] eqn:Ev; [|discriminate Hi]. simpl in Hi. injection Hi as ->.
      destruct (nth_error_same_length xs ys i _ ltac:(lia) Hx) as [y Hy].
      pose proof (receiver_captures n mr c vars ma ys u Hc Hids Hbounds Hfy Hrec i p bound y Ev Hy) as Hst.
      pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy'.
      destruct y as [| | | |vb ob X| |]; try discriminate Hfy'.
      exists (mkVariableState bound (TypeArgument vb ob X) (TypeArgument vb ob X) true true), vb, ob, X.
      repeat split; try reflexivity; [exact Hst|exact Hfy'|].
      pose proof (Forall2_nth_error _ xs ys i _ _ Hp Hx Hy) as Ex.
      apply (unify_fuel_monotone env n0); [unfold K'; lia|].
      exact (proj2 (states_irrelevant n0) _ _ [] u Hfy' (Hfxs _ (nth_error_In _ _ Hx)) Ex). }
    pose proof (bindings_of_in_fragment c xs Hfxs) as Hbf.
    assert (Hb': bound_in env (bindings_of env c xs) K' u (pgeneric P) = true)
        by exact (kqfrag_transfer _ K [] K' u Hbf ltac:(unfold K'; lia) P HP Hb).
    assert (Hb0: bound_in env (bindings_of env c xs) K' [] (pgeneric P) = true)
        by exact (kqfrag_transfer _ K [] K' [] Hbf ltac:(unfold K'; lia) P HP Hb).
    destruct (exact_qparameter (bindings_of env c xs) K' u Hcover Hbf fuel P A u' HP HA HcA Hb' Hb0 H) as [_ [f Hf]].
    exists f. unfold is_assignable_to, empty_unification. rewrite Hf. reflexivity.
Qed.

End Inference.

(* The bindings of the type variables of an inst_root or inst_nullable, from bound_in *)
Ltac solve_bound_vars := match goal with
    | H: bound_in ?e ?b ?K ?s _ = true |- bound_vars ?b ?t = true =>
        refine (bound_vars_of e _ b K s t (ifrag_no_generics e t _) H); assumption
    end.
