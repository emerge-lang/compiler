From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The substitution lemma, for the invariant fragment                                             *)
(*                                                                                                *)
(* Instantiating the type parameters keeps assignability: if a type is assignable to another, it  *)
(* still is with the type parameters in both replaced by type arguments. This is proven for a     *)
(* fragment of the types:                                                                          *)
(* - class types, never Nothing, whose type arguments are invariant, of any ownership, and contain *)
(*   a type of the fragment;                                                                       *)
(* - type parameters, without a mutability of their own, whose bound isn't a type parameter;      *)
(* - comparing a class type to a type of the same class, at the top;                               *)
(* - instantiating with invariant type arguments of fragment types;                                *)
(* - without type inference (no type variables).                                                  *)
(* Beyond it, the lemma needs more:                                                                *)
(* - Nothing: a type parameter accepts any non-nullable Nothing, also one whose mutability an     *)
(*   instantiation of it doesn't accept (`mut Nothing` isn't a `const C`). Nothing is never        *)
(*   instantiated, though, so that doesn't matter for the soundness.                              *)
(* - in and out variance, and a class type assigned a type parameter: assignability to the bound   *)
(*   has to carry over to what the type parameter is instantiated with, which takes the            *)
(*   transitivity of unify.                                                                        *)
(* - a subclass assigned to its superclass: instantiating the supertype has to compose with the    *)
(*   instantiation.                                                                                *)
(* Within the fragment, invariance demands assignability both ways, so for type arguments, the     *)
(* classes must be the same (in an acyclic class hierarchy), and type parameters must be the same   *)
(* parameter; instantiating that one makes both sides the same type.                               *)
(* ---------------------------------------------------------------------------------------------- *)

Section Substitution.

Variable env: Environment.

Definition is_generic (t: EType): bool :=
    match t with Generic _ => true | _ => false end.

Fixpoint in_fragment (t: EType): bool :=
    match t with
    | RootResolved _ c arguments =>
        negb (class_eqb c nothing) && forallb (fun a =>
            match a with
            | TypeArgument Model.invariant _ n => in_fragment n
            | _ => false
            end) arguments
    | Generic (mkGenericRef None _ bound) => negb (is_generic bound)
    | _ => false
    end.

Definition argument_in_fragment (a: EType): bool :=
    match a with
    | TypeArgument Model.invariant _ n => in_fragment n
    | _ => false
    end.

(* Every type parameter in the type is bound, to an invariant type argument of a fragment type *)
Fixpoint bound_in (b: Bindings) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments =>
        forallb (fun a => match a with TypeArgument _ _ n => bound_in b n | _ => true end) arguments
    | Generic (mkGenericRef _ p _) =>
        match lookup_binding b p with
        | Some (TypeArgument Model.invariant _ x) => in_fragment x
        | _ => false
        end
    | _ => true
    end.

Definition argument_bound_in (b: Bindings) (a: EType): bool :=
    match a with TypeArgument _ _ n => bound_in b n | _ => true end.

(* How much fuel unify needs at most, to unify a type with itself *)
Fixpoint udepth (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments =>
        S (S (list_max (map (fun a => match a with TypeArgument _ _ n => udepth n | _ => 0 end) arguments)))
    | _ => 1
    end.

Definition argument_depth (a: EType): nat :=
    match a with TypeArgument _ _ n => udepth n | _ => 0 end.

Fixpoint bindings_depth (b: Bindings): nat :=
    match b with
    | [] => 0
    | (_, a) :: rest => max (argument_depth a) (bindings_depth rest)
    end.

(* The class hierarchy has no cycles *)
Definition acyclic: Prop :=
    forall c c', base_type_is_subtype_of env c c' = true -> base_type_is_subtype_of env c' c = true -> c = c'.

(* What a type in a type argument becomes, when instantiated *)
Definition instantiate_nested (b: Bindings) (n: EType): EType :=
    match n with
    | Generic (mkGenericRef _ p _) =>
        match lookup_binding b p with
        | Some (TypeArgument _ _ x) => x
        | _ => n
        end
    | _ => instantiate env b n
    end.

(* The two types are of the same class, or both type parameters *)
Definition same_shape (t a: EType): Prop :=
    match t, a with
    | RootResolved _ c _, RootResolved _ c' _ => c = c'
    | Generic _, Generic _ => True
    | _, _ => False
    end.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about the fragment                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma root_in_fragment: forall m c arguments,
    in_fragment (RootResolved m c arguments) = true ->
    class_eqb c nothing = false /\ forall a, In a arguments -> argument_in_fragment a = true.
Proof.
    intros m c arguments H. change (negb (class_eqb c nothing) && forallb argument_in_fragment arguments = true) in H.
    apply andb_true_iff in H. destruct H as [Hc Ha]. split.
    - destruct (class_eqb c nothing); [discriminate Hc|reflexivity].
    - apply forallb_forall, Ha.
Qed.

Lemma root_bound_in: forall b m c arguments,
    bound_in b (RootResolved m c arguments) = true -> forall a, In a arguments -> argument_bound_in b a = true.
Proof.
    intros b m c arguments H. change (forallb (argument_bound_in b) arguments = true) in H.
    apply forallb_forall, H.
Qed.

Lemma argument_depth_below: forall m c arguments a,
    In a arguments -> S (S (argument_depth a)) <= udepth (RootResolved m c arguments).
Proof.
    intros m c arguments a Ha. change (S (S (argument_depth a)) <= S (S (list_max (map argument_depth arguments)))).
    assert (H: Forall (fun k => k <= list_max (map argument_depth arguments)) (map argument_depth arguments))
        by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (argument_depth a) (in_map _ _ _ Ha)). lia.
Qed.

Lemma lookup_depth: forall b p a, lookup_binding b p = Some a -> argument_depth a <= bindings_depth b.
Proof.
    intros b p a. induction b as [|[p' a'] rest IH]; simpl; [discriminate|].
    destruct (param_eqb p p'); intros H.
    - injection H as <-. lia.
    - specialize (IH H). lia.
Qed.

(* The type parameters are all bound invariantly, so instantiating widens no type argument *)
Lemma bound_invariantly: forall b k t,
    udepth t <= k -> in_fragment t = true -> bound_in b t = true -> mentions_variantly_bound b t = false.
Proof.
    intros b k. induction k as [|k IH]; intros t Hd Hf Hb.
    { destruct t; simpl in Hd; lia. }
    destruct t as [m c args|n|[gm p bnd]|m msg|v o n|g|cs]; simpl in Hf; try discriminate Hf.
    - destruct (root_in_fragment m c args Hf) as [_ Hargs].
      apply not_true_iff_false. intros H. change (existsb (mentions_variantly_bound b) args = true) in H.
      apply existsb_exists in H. destruct H as [a [Ha Hm]].
      specialize (Hargs a Ha). pose proof (root_bound_in b m c args Hb a Ha) as Hba.
      pose proof (argument_depth_below m c args a Ha) as Hda.
      destruct a as [| | | |v o n| |]; simpl in Hargs, Hba; try discriminate Hargs. destruct v; try discriminate Hargs.
      cbn [argument_depth] in Hda. simpl in Hm. rewrite (IH n) in Hm; [discriminate Hm|lia|exact Hargs|exact Hba].
    - simpl in Hb |- *. destruct (lookup_binding b p) as [a|]; [|discriminate Hb].
      destruct a as [| | | |v' o_p x| |]; try discriminate Hb. destruct v'; try discriminate Hb. reflexivity.
Qed.

Lemma instantiate_type_argument: forall b o n,
    in_fragment n = true -> bound_in b n = true ->
    instantiate env b (TypeArgument Model.invariant o n)
    = TypeArgument Model.invariant (instantiate_ownership b o) (instantiate_nested b n).
Proof.
    intros b o [m c args|n|[gm p bnd]|m msg|v o' n|g|cs] Hf Hb; simpl in Hf; try discriminate Hf.
    - assert (Hv: mentions_variantly_bound_in_arguments b (RootResolved m c args) = false)
          by exact (bound_invariantly b _ (RootResolved m c args) (le_n _) Hf Hb).
      change (instantiate env b (TypeArgument Model.invariant o (RootResolved m c args)))
          with (if mentions_variantly_bound_in_arguments b (RootResolved m c args)
                then TypeArgument output (instantiate_ownership b o) (RootResolved m c (map (instantiate env b) args))
                else TypeArgument Model.invariant (instantiate_ownership b o) (RootResolved m c (map (instantiate env b) args))).
      rewrite Hv. reflexivity.
    - destruct gm; [discriminate Hf|]. simpl in Hb.
      destruct (lookup_binding b p) as [a|] eqn:E; [|discriminate Hb].
      destruct a as [| | | |v' o_p x| |]; try discriminate Hb. destruct v'; try discriminate Hb.
      cbn. rewrite E. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about unify on the fragment                                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma fold_unify_pairs_stay_failed: forall n l,
    fold_unify (fun inner '(t, a) => unify env n t a inner) l Failed = Some Failed.
Proof. intros n l. induction l as [|[t a] rest IH]; simpl; [reflexivity|]. rewrite unify_keeps_failure. exact IH. Qed.

(* Each pair of arguments keeps the states, and each pair of instantiated arguments succeeds *)
Lemma fold_unify_pairs: forall n n' b targs aargs s u,
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing u) ->
    (forall t a s0 s1, In t targs -> In a aargs ->
        unify env n t a (Ongoing s0) = Some (Ongoing s1) ->
        s1 = s0 /\ unify env n' (instantiate env b t) (instantiate env b a) (Ongoing s0) = Some (Ongoing s0)) ->
    u = s /\ fold_unify (fun inner '(t, a) => unify env n' t a inner)
        (combine (map (instantiate env b) targs) (map (instantiate env b) aargs)) (Ongoing s) = Some (Ongoing s).
Proof.
    intros n n' b targs. induction targs as [|t targs IH]; intros aargs s u H Hpair;
        destruct aargs as [|a aargs]; simpl in *; try (injection H as <-; auto).
    destruct (unify env n t a (Ongoing s)) as [[s1|]|] eqn:E; try discriminate H.
    - destruct (Hpair t a s s1 (or_introl eq_refl) (or_introl eq_refl) E) as [-> Hinst].
      rewrite Hinst. apply (IH aargs s u H). intros t' a' s0 s2 Ht Ha. apply Hpair; right; assumption.
    - rewrite fold_unify_pairs_stay_failed in H. discriminate H.
Qed.

Lemma fold_unify_pairs_reflexive: forall n args s,
    (forall a s0, In a args -> unify env n a a (Ongoing s0) = Some (Ongoing s0)) ->
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine args args) (Ongoing s) = Some (Ongoing s).
Proof.
    intros n args. induction args as [|a args IH]; intros s H; simpl; [reflexivity|].
    rewrite (H a s (or_introl eq_refl)). apply IH. intros a' s0 Ha'. apply H. right. exact Ha'.
Qed.

(* unify on two class types of the same class, one step *)
Lemma unify_same_class: forall n mt ma c targs aargs s,
    class_eqb c nothing = false ->
    unify env (S n) (RootResolved mt c targs) (RootResolved ma c aargs) (Ongoing s) =
    if Model.is_subtype_of (mutability_of env (RootResolved ma c aargs)) (mutability_of env (RootResolved mt c targs))
    then unify_arguments (unify env n) targs aargs s
    else Some Failed.
Proof.
    intros n mt ma c targs aargs s Hc. rewrite unify_step_once. unfold unify_step, unify_root_resolved, base_type_is_subtype_of.
    rewrite class_eqb_refl. cbn [negb]. destruct (Model.is_subtype_of _ _); [|reflexivity]. cbn [negb].
    rewrite Hc. reflexivity.
Qed.

(* unify on two invariant type arguments, one step *)
Lemma unify_invariant_arguments: forall n ot nt oa na s,
    unify env (S n) (TypeArgument Model.invariant ot nt) (TypeArgument Model.invariant oa na) (Ongoing s) =
    if ownership_is_assignable_to oa ot then
        match unify env n nt na (Ongoing s) with
        | Some u => unify env n na nt u
        | None => None
        end
    else Some Failed.
Proof.
    intros. rewrite unify_step_once. unfold unify_step, unify_type_argument.
    destruct (ownership_is_assignable_to oa ot); reflexivity.
Qed.

Lemma class_unify_base: forall n mt ct targs ma ca aargs s u,
    unify env n (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing u) ->
    base_type_is_subtype_of env ca ct = true.
Proof.
    intros [|n] mt ct targs ma ca aargs s u H; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_root_resolved in H.
    destruct (base_type_is_subtype_of env ca ct); [reflexivity|]. discriminate H.
Qed.

Lemma generic_rejects_class: forall n g m c args s u,
    class_eqb c nothing = false ->
    unify env n (Generic g) (RootResolved m c args) (Ongoing s) <> Some (Ongoing u).
Proof.
    intros [|n] [gm p bnd] m c args s u Hc H; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_generic in H. cbn [is_non_nullable_nothing] in H.
    rewrite Hc in H. discriminate H.
Qed.

Lemma generic_unify_same_parameter: forall n p bp q bq s u,
    is_generic bq = false ->
    unify env n (Generic (mkGenericRef None p bp)) (Generic (mkGenericRef None q bq)) (Ongoing s) = Some (Ongoing u) ->
    q = p /\ u = s.
Proof.
    intros [|n] p bp q bq s u Hbq H; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_generic in H. cbn [generic_is_subtype_of] in H.
    destruct (param_eqb q p) eqn:E.
    - apply param_eqb_eq in E. split; [exact E|]. destruct (Model.is_subtype_of _ _); injection H; auto. discriminate.
    - destruct bq as [| |[]| | | |]; simpl in Hbq; try discriminate Hbq; cbn in H; discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Reflexivity                                                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma unify_reflexive_with_arguments: forall n,
    (forall t s, in_fragment t = true -> udepth t <= n -> unify env n t t (Ongoing s) = Some (Ongoing s))
    /\ (forall a s, argument_in_fragment a = true -> S (argument_depth a) <= n -> unify env n a a (Ongoing s) = Some (Ongoing s)).
Proof.
    induction n as [|n [IHt IHa]].
    - split.
        + intros [] s Hf Hd; simpl in Hd; lia.
        + intros a s Hf Hd. lia.
    - split.
        + intros [m c args|nn|[gm p bnd]|m msg|v o nn|g|cs] s Hf Hd; simpl in Hf; try discriminate Hf.
            * destruct (root_in_fragment m c args Hf) as [Hc Hargs].
              rewrite unify_same_class by exact Hc. rewrite mutability_is_subtype_of_refl.
              unfold unify_arguments. apply fold_unify_pairs_reflexive. intros a s0 Ha.
              apply IHa; [apply Hargs, Ha|]. pose proof (argument_depth_below m c args a Ha). lia.
            * apply generic_unifies_with_itself.
        + intros [| | | |v o nn| |] s Hf Hd; simpl in Hf; try discriminate Hf. destruct v; try discriminate Hf.
          simpl in Hd. rewrite unify_invariant_arguments, ownership_is_assignable_to_itself.
          rewrite IHt; [|exact Hf|lia]. apply IHt; [exact Hf|lia].
Qed.

Lemma unify_reflexive: forall n t s,
    in_fragment t = true -> udepth t <= n -> unify env n t t (Ongoing s) = Some (Ongoing s).
Proof. intros n. apply (unify_reflexive_with_arguments n). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The substitution lemma                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma instantiated_generic: forall b gm p bnd,
    bound_in b (Generic (mkGenericRef gm p bnd)) = true ->
    exists x, (forall gm' bnd', instantiate_nested b (Generic (mkGenericRef gm' p bnd')) = x)
        /\ in_fragment x = true /\ udepth x <= bindings_depth b.
Proof.
    intros b gm p bnd Hb. simpl in Hb.
    destruct (lookup_binding b p) as [a|] eqn:E; [|discriminate Hb].
    destruct a as [| | | |v o x| |]; try discriminate Hb. destruct v; try discriminate Hb.
    exists x. split; [intros; simpl; rewrite E; reflexivity|]. split; [exact Hb|]. apply (lookup_depth b p _ E).
Qed.

Lemma substitution_with_arguments: forall b, acyclic -> forall n,
    (forall t a s u,
        in_fragment t = true -> in_fragment a = true -> bound_in b t = true -> bound_in b a = true ->
        same_shape t a ->
        unify env n t a (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n + bindings_depth b) (instantiate_nested b t) (instantiate_nested b a) (Ongoing s) = Some (Ongoing s))
    /\ (forall t a s u,
        argument_in_fragment t = true -> argument_in_fragment a = true ->
        argument_bound_in b t = true -> argument_bound_in b a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n + bindings_depth b) (instantiate env b t) (instantiate env b a) (Ongoing s) = Some (Ongoing s)).
Proof.
    intros b Hacyclic n. induction n as [|n [IHt IHa]].
    { split; intros t a s u _ _ _ _; [intros _|]; intros H; discriminate H. }
    split.
    - intros [mt ct targs|tn|[tg p tb]|tm tmsg|tv to tn|tg|tcs] [ma ca aargs|an|[ag q ab]|am amsg|av ao an|ag|acs]
          s u Hft Hfa Hbt Hba Hshape H; simpl in Hshape; try contradiction.
      + (* two class types of the same class *)
        subst ca. destruct (root_in_fragment mt ct targs Hft) as [Hc Htargs].
        destruct (root_in_fragment ma ct aargs Hfa) as [_ Haargs].
        rewrite unify_same_class in H by exact Hc.
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate H].
        unfold unify_arguments in H.
        destruct (fold_unify_pairs n (n + bindings_depth b) b targs aargs s u H) as [-> Hargs].
        { intros t a s0 s1 Ht Ha Hta. apply IHa; auto.
          - apply (root_bound_in b mt ct targs Hbt t Ht).
          - apply (root_bound_in b ma ct aargs Hba a Ha). }
        split; [reflexivity|].
        change (S n + bindings_depth b) with (S (n + bindings_depth b)).
        change (instantiate_nested b (RootResolved mt ct targs)) with (RootResolved mt ct (map (instantiate env b) targs)).
        change (instantiate_nested b (RootResolved ma ct aargs)) with (RootResolved ma ct (map (instantiate env b) aargs)).
        rewrite unify_same_class by exact Hc. cbn [mutability_of] in *. rewrite Hm. exact Hargs.
      + (* two type parameters: the same one, instantiated with the same type *)
        destruct tg; [discriminate Hft|]. destruct ag; [discriminate Hfa|].
        simpl in Hfa. apply negb_true_iff in Hfa.
        destruct (generic_unify_same_parameter (S n) p tb q ab s u Hfa H) as [-> ->]. split; [reflexivity|].
        destruct (instantiated_generic b None p tb Hbt) as [x [Hx [Hfx Hdx]]]. rewrite !Hx.
        apply unify_reflexive; [exact Hfx|lia].
    - intros [| | | |tv ot nt| |] [| | | |av oa na| |] s u Hft Hfa Hbt Hba H; simpl in Hft, Hfa; try discriminate Hft; try discriminate Hfa.
      destruct tv; try discriminate Hft. destruct av; try discriminate Hfa.
      simpl in Hbt, Hba.
      rewrite unify_invariant_arguments in H. destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
      (* both ways succeed, so the shapes are the same *)
      assert (Hshape: same_shape nt na).
      { destruct nt as [mt ct targs|tn|tg|tm tmsg|tv to tn|tg|tcs]; destruct na as [ma ca aargs|an|ag|am amsg|av ao an|ag|acs];
            simpl in Hft, Hfa; try discriminate Hft; try discriminate Hfa; simpl; try exact I.
        - apply Hacyclic; [eapply class_unify_base; exact H|eapply class_unify_base; exact E1].
        - destruct (root_in_fragment mt ct targs Hft) as [Hc _]. exfalso. eapply generic_rejects_class; [exact Hc|exact H].
        - destruct (root_in_fragment ma ca aargs Hfa) as [Hc _]. exfalso. eapply generic_rejects_class; [exact Hc|exact E1]. }
      destruct (IHt nt na s s1 Hft Hfa Hbt Hba Hshape E1) as [-> Hinst1].
      assert (Hshape': same_shape na nt) by (destruct nt, na; simpl in *; auto).
      destruct (IHt na nt s u Hfa Hft Hba Hbt Hshape' H) as [-> Hinst2].
      split; [reflexivity|].
      rewrite (instantiate_type_argument b ot nt Hft Hbt), (instantiate_type_argument b oa na Hfa Hba).
      change (S n + bindings_depth b) with (S (n + bindings_depth b)).
      rewrite unify_invariant_arguments, (instantiation_preserves_ownership_assignability b oa ot Ho).
      rewrite Hinst1. exact Hinst2.
Qed.

(*
 * The substitution lemma: within the fragment, a type that is assignable to another of the same class
 * stays so, with all its type parameters instantiated. Extra fuel is needed for the types the type
 * parameters are instantiated with.
 *)
Theorem substitution_lemma: forall b fuel mt c targs ma aargs,
    acyclic ->
    in_fragment (RootResolved mt c targs) = true -> in_fragment (RootResolved ma c aargs) = true ->
    bound_in b (RootResolved mt c targs) = true -> bound_in b (RootResolved ma c aargs) = true ->
    is_assignable_to env fuel (RootResolved ma c aargs) (RootResolved mt c targs) = Some true ->
    is_assignable_to env (fuel + bindings_depth b)
        (instantiate env b (RootResolved ma c aargs)) (instantiate env b (RootResolved mt c targs)) = Some true.
Proof.
    intros b fuel mt c targs ma aargs Hacyclic Hft Hfa Hbt Hba H.
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel (RootResolved mt c targs) (RootResolved ma c aargs) (Ongoing [])) as [[u|]|] eqn:E;
        try discriminate H.
    destruct (proj1 (substitution_with_arguments b Hacyclic fuel) _ _ [] u Hft Hfa Hbt Hba eq_refl E) as [_ Hinst].
    change (instantiate_nested b (RootResolved mt c targs)) with (instantiate env b (RootResolved mt c targs)) in Hinst.
    change (instantiate_nested b (RootResolved ma c aargs)) with (instantiate env b (RootResolved ma c aargs)) in Hinst.
    rewrite Hinst. reflexivity.
Qed.

End Substitution.
