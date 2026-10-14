From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Ops.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The transitivity of unify, with type parameters and intersections                              *)
(*                                                                                                *)
(* Transitivity.v proves unify transitive for class types. This extends the fragment (gfrag, in    *)
(* Fragment.v) by references to type parameters and by intersections, as the frontend builds them:  *)
(* - a reference to a type parameter has an effective bound: the declared bound of the parameter,  *)
(*   with a mutability applied (BoundTypeReference.withMutability), and maybe made non-null (`V!`,  *)
(*   withCombinedNullability(NOT_NULLABLE)); see refs_wf. Kotlin compares two references to the     *)
(*   same parameter by their mutability and nullability only, which is sound for exactly that       *)
(*   reason: their bounds are ordered the same way (bounds_ordered, same_parameter_bounds);         *)
(* - the components of an intersection are class types and non-null references to type parameters  *)
(*   (BoundIntersectionTypeReference.ofComponents);                                                 *)
(* - a nullable type wraps a non-null one (NullableTypeReference.invoke).                           *)
(* Assumed, beyond Transitivity.v (bounds_wellformed): the declared bounds of type parameters are   *)
(* of the fragment, and                                                                            *)
(* applying a mutability to one gives it that mutability (no const class, nor one in an            *)
(* intersection that is a bound); the bounds aren't F-bounded, as a declared bound here is a      *)
(* finite type of the fragment.                                                                   *)
(* Since a value of an intersection type is assigned through the first of its components that is   *)
(* assignable, unify must come to an answer on the components before it, which it may not: what is  *)
(* proven is that unify never rejects (transitivity_never_fails, which explains this).              *)
(* ---------------------------------------------------------------------------------------------- *)

(* The declared bounds of the type parameters: types of the fragment, each of the mutability applied
   to it (no const class, nor one in an intersection that is a bound) *)
Record bounds_wellformed (env: Environment) (declared: TypeParameterId -> EType): Prop := {
    bw_gfrag: forall p, gfrag env (declared p) = true;
    bw_mutability: forall p m, mutability_of env (with_mutability env m (declared p)) = m;
}.

Section Generics.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

(* ---------------------------------------------------------------------------------------------- *)
(* The fragment                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Local Abbreviation gfrag := (Fragment.gfrag env).
Local Abbreviation argument_gfrag := (Fragment.argument_gfrag env).
Let root_gfrag := Fragment.root_gfrag env.
Let make_root_gfrag := Fragment.make_root_gfrag env.
Let intersection_gfrag := Fragment.intersection_gfrag env.
Let gfrag_cases := Fragment.gfrag_cases env.
Let component_cases := Fragment.component_cases env.
Let in_fragment_gfrag := Fragment.in_fragment_gfrag env.
Let gfrag_not_variable := Fragment.gfrag_not_variable env.

Lemma gfrag_no_vars: forall t, gfrag t = true -> no_vars t = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [m c args|n|[gm nn p bound]|me msg|v o n|g|cs]; simpl in H |- *; try discriminate H.
    - apply forallb_forall. intros a Ha. pose proof (esize_in args a Ha) as Hs.
      destruct (root_gfrag m c args H) as [_ Hargs]. specialize (Hargs a Ha).
      destruct a as [| | | |va oa na| |]; simpl in Hargs |- *; try discriminate Hargs.
      cbn [esize] in Hs. apply (IH (esize na)); [cbn [esize]; lia|reflexivity|exact Hargs].
    - apply andb_true_iff in H. apply (IH (esize n)); [cbn [esize]; lia|reflexivity|apply H].
    - apply (IH (esize bound)); [cbn [esize]; lia|reflexivity|exact H].
    - apply forallb_forall. intros c Hc. pose proof (esize_in cs c Hc).
      destruct (intersection_gfrag cs H) as [_ Hcs]. apply (IH (esize c)); [cbn [esize]; lia|reflexivity|apply Hcs, Hc].
Qed.

Lemma argument_gfrag_no_vars: forall a, argument_gfrag a = true -> no_vars a = true.
Proof. intros [| | | |v o n| |] H; simpl in H |- *; try discriminate H. apply gfrag_no_vars, H. Qed.

Lemma bottom_gfrag: gfrag bottom_type = true.
Proof. apply (proj1 (in_fragment_gfrag 1)); [simpl; lia|exact (bottom_in_fragment env wf)]. Qed.

Lemma top_gfrag: gfrag top_type = true.
Proof. apply (proj1 (in_fragment_gfrag 2)); [simpl; lia|exact (top_in_fragment env wf)]. Qed.

(* On the fragment, unify keeps the variable states, whatever they are *)
Lemma gkeeps: forall n t a s u, gfrag t = true -> gfrag a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s.
Proof.
    intros n t a s u Ht Ha H.
    pose proof (unify_free env wf n t a s s _ (gfrag_no_vars t Ht) (gfrag_no_vars a Ha) H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

Lemma gkeeps_arguments: forall n t a s u, argument_gfrag t = true -> argument_gfrag a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s.
Proof.
    intros n t a s u Ht Ha H.
    pose proof (unify_free env wf n t a s s _ (argument_gfrag_no_vars t Ht)
        (argument_gfrag_no_vars a Ha) H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

Lemma gat_states: forall n t a s s', no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s').
Proof. intros n t a s s' Ht Ha H. exact (unify_free env wf n t a s s' _ Ht Ha H). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Supertypes of class types of the fragment                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma template_instances_gfrag: forall sub ys,
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> argument_gfrag y = true) ->
    forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> gfrag (instantiate env (bindings_of env sub ys) t) = true)
    /\ (forall a, argument_depth a <= k -> template_argument env sub a = true ->
        argument_gfrag (instantiate env (bindings_of env sub ys) a) = true).
Proof.
    intros sub ys Hl Hys k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c arguments, depth (RootResolved m c arguments) <= S k ->
        template_type env sub (RootResolved m c arguments) = true ->
        gfrag (instantiate env (bindings_of env sub ys) (RootResolved m c arguments)) = true).
    { intros m c arguments Hd Ht. destruct (root_template env sub m c arguments Ht) as [Hla Hargs].
      rewrite instantiate_class. apply make_root_gfrag; [rewrite length_map; exact Hla|].
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
      pose proof (argument_depth_below m c arguments a Ha). apply IHa; [lia|apply Hargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> Ht']]]]].
      + exact (Hroot m c arguments Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class, <- instantiate_class.
        change (true && gfrag (instantiate env (bindings_of env sub ys) (RootResolved m c arguments)) = true).
        rewrite (Hroot m c arguments); [reflexivity|lia|exact Ht'].
    - intros a Hd Ha. destruct (template_kind env sub a Ha) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hl) Hi) as [y Hy].
        pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy.
        rewrite (selects env wf sub ys p bp i y Hi Hy); [exact Hfy|].
        destruct y as [| | | | | |]; try discriminate Hfy. reflexivity.
      + simpl in Hd. rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn)).
        destruct (mentions_loosely_bound _ n); [destruct v|]; simpl;
            first [exact bottom_gfrag | apply IHt; [lia|exact Hn]].
Qed.

Lemma supertype_arguments_gfrag: forall sub super xs,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids env sub) -> (forall x, In x xs -> argument_gfrag x = true) ->
    length (parameterized_supertype_arguments env sub xs super) = length (parameter_ids env super)
    /\ forall a, In a (parameterized_supertype_arguments env sub xs super) -> argument_gfrag a = true.
Proof.
    intros sub super xs Hne Hn Hb Hl Hxs. destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hb) as [Hlt Ht].
    rewrite parameterized_supertype_arguments_eq. split; [rewrite length_map; exact Hlt|].
    intros a Ha. apply in_map_iff in Ha. destruct Ha as [t [<- Hin]].
    exact (proj2 (template_instances_gfrag sub xs Hl Hxs _) t (le_n _) (Ht t Hin)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One step of unify, for the shapes of the fragment                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma step_root_generic: forall n m c args gm nn q b s,
    unify env (S n) (RootResolved m c args) (Generic (mkGenericRef gm nn q b)) (Ongoing s) = unify env n (RootResolved m c args) b (Ongoing s).
Proof. reflexivity. Qed.

Lemma step_root_inter: forall n m c args cs s,
    unify env (S n) (RootResolved m c args) (Intersection cs) (Ongoing s)
    = intersection_flipped_unify (unify env n) (RootResolved m c args) cs s.
Proof. reflexivity. Qed.

Lemma step_nullable_generic: forall n zn g s,
    unify env (S n) (Nullable zn) (Generic g) (Ongoing s) = unify env n zn (without_null (Generic g)) (Ongoing s).
Proof. reflexivity. Qed.

Lemma step_nullable_inter: forall n zn cs s,
    unify env (S n) (Nullable zn) (Intersection cs) (Ongoing s) = unify env n zn (Intersection cs) (Ongoing s).
Proof. reflexivity. Qed.

Lemma step_generic_root: forall n gm nn p b m c args s,
    unify env (S n) (Generic (mkGenericRef gm nn p b)) (RootResolved m c args) (Ongoing s) =
    if is_non_nullable_nothing env (RootResolved m c args)
        && is_subtype_of (assignment_mutability env (RootResolved m c args)) (assignment_mutability env (Generic (mkGenericRef gm nn p b)))
    then Some (Ongoing s) else Some Failed.
Proof. reflexivity. Qed.

Lemma step_generic_nullable: forall n g a s, unify env (S n) (Generic g) (Nullable a) (Ongoing s) = Some Failed.
Proof. intros n [] a s. reflexivity. Qed.

Lemma step_generic_generic: forall n gm nn p b gq nq q bq s,
    unify env (S n) (Generic (mkGenericRef gm nn p b)) (Generic (mkGenericRef gq nq q bq)) (Ongoing s) =
    if param_eqb q p
    then if is_subtype_of (assignment_mutability env bq) (assignment_mutability env b) && (negb (is_nullable bq) || is_nullable b)
         then Some (Ongoing s) else Some Failed
    else unify env n (Generic (mkGenericRef gm nn p b)) bq (Ongoing s).
Proof. reflexivity. Qed.

Lemma step_generic_inter: forall n g cs s,
    unify env (S n) (Generic g) (Intersection cs) (Ongoing s) = intersection_flipped_unify (unify env n) (Generic g) cs s.
Proof. intros n [] cs s. reflexivity. Qed.

Lemma step_inter_nullable: forall n cs a s, unify env (S n) (Intersection cs) (Nullable a) (Ongoing s) = Some Failed.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Never failing                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* unify never rejects assigning a to t: with whatever fuel and states, it either accepts or runs out
   of fuel (see transitivity_never_fails for why this is what transitivity is about) *)
Definition never_fails (t a: EType): Prop := forall f s, unify env f t a (Ongoing s) <> Some Failed.

Lemma never_fails_step: forall t a, (forall f s, unify env (S f) t a (Ongoing s) <> Some Failed) -> never_fails t a.
Proof. intros t a H [|f] s; [discriminate|apply H]. Qed.

Lemma success_never_fails: forall n t a s, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> never_fails t a.
Proof.
    intros n t a s Ht Ha H f s' E. pose proof (gat_states n t a s s' Ht Ha H) as H'.
    destruct (Nat.le_ge_cases f n) as [Hle|Hge].
    - pose proof (unify_fuel_monotone env f n t a _ _ Hle E) as E'. congruence.
    - pose proof (unify_fuel_monotone env n f t a _ _ Hge H') as E'. congruence.
Qed.

Lemma gsuccess_never_fails: forall n t a s, gfrag t = true -> gfrag a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> never_fails t a.
Proof. intros n t a s Ht Ha. apply success_never_fails; apply gfrag_no_vars; assumption. Qed.

(* A unification on no type variables that doesn't fail, keeps the states *)
Lemma free_result: forall n t a s, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) <> Some Failed ->
    unify env n t a (Ongoing s) = None \/ unify env n t a (Ongoing s) = Some (Ongoing s).
Proof.
    intros n t a s Ht Ha H. destruct (unify env n t a (Ongoing s)) as [[u|]|] eqn:E; [|congruence|left; reflexivity].
    right. pose proof (unify_free env wf n t a s s _ Ht Ha E) as E'. rewrite E in E'.
    exact E'.
Qed.

Lemma fold_never_fails: forall (g: EType -> Unification -> option Unification) (l: list EType) s,
    (forall c, In c l -> g c (Ongoing s) = None \/ g c (Ongoing s) = Some (Ongoing s)) ->
    fold_unify (fun inner c => g c inner) l (Ongoing s) = None \/ fold_unify (fun inner c => g c inner) l (Ongoing s) = Some (Ongoing s).
Proof.
    intros g l s. induction l as [|c l IH]; intros H; simpl; [right; reflexivity|].
    destruct (H c (or_introl eq_refl)) as [E|E]; rewrite E; [left; reflexivity|].
    apply IH. intros c' Hc'. apply H. right. exact Hc'.
Qed.

Lemma fold_all: forall (g: EType -> Unification -> option Unification) (l: list EType) s r,
    (forall c, g c Failed = Some Failed) ->
    (forall c u, In c l -> g c (Ongoing s) = Some (Ongoing u) -> u = s) ->
    fold_unify (fun inner c => g c inner) l (Ongoing s) = Some (Ongoing r) ->
    forall c, In c l -> g c (Ongoing s) = Some (Ongoing s).
Proof.
    intros g l s r Hf Hk. induction l as [|c l IH]; intros H c' Hc'; [destruct Hc'|]. simpl in H.
    destruct (g c (Ongoing s)) as [[u|]|] eqn:E.
    - pose proof (Hk c u (or_introl eq_refl) E). subst u.
      destruct Hc' as [<-|Hc']; [exact E|]. apply (IH (fun c0 u0 Hc0 => Hk c0 u0 (or_intror Hc0)) H c' Hc').
    - exfalso. clear -H Hf. induction l as [|x l IHl]; simpl in H; [discriminate H|]. rewrite Hf in H. exact (IHl H).
    - discriminate H.
Qed.

(* An intersection as the target: every component takes the assignee *)
Lemma inter_target_all: forall n cs a s r, forallb no_vars cs = true -> no_vars a = true ->
    match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    unify env (S n) (Intersection cs) a (Ongoing s) = Some (Ongoing r) ->
    forall c, In c cs -> unify env n c a (Ongoing s) = Some (Ongoing s).
Proof.
    intros n cs a s r Hcs Ha Hshape H. rewrite unify_step_once in H. unfold unify_step, unify_intersection in H.
    destruct (no_vars_filter cs Hcs) as [Hvar Hnonvar].
    assert (Hk: forall c u, In c cs -> unify env n c a (Ongoing s) = Some (Ongoing u) -> u = s).
    { intros c u Hc E. rewrite forallb_forall in Hcs.
      pose proof (unify_free env wf n c a s s _ (Hcs c Hc) Ha E) as E'. rewrite E in E'.
      injection E' as ->. reflexivity. }
    destruct a as [| | | | | |]; try contradiction; cbn zeta in H; rewrite Hvar, Hnonvar in H;
        destruct (fold_unify (fun inner c => unify env n c _ inner) cs (Ongoing s)) as [[s2|]|] eqn:E; try discriminate H;
        exact (fold_all (fun c inner => unify env n c _ inner) cs s s2 (fun c => unify_keeps_failure env n c _) Hk E).
Qed.

Lemma inter_target_never_fails: forall cs a, forallb no_vars cs = true -> no_vars a = true ->
    match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    (forall c, In c cs -> never_fails c a) -> never_fails (Intersection cs) a.
Proof.
    intros cs a Hcs Ha Hshape H. apply never_fails_step. intros f s E.
    rewrite unify_step_once in E. unfold unify_step, unify_intersection in E.
    destruct (no_vars_filter cs Hcs) as [Hvar Hnonvar]. rewrite forallb_forall in Hcs.
    assert (Hfold: fold_unify (fun inner c => unify env f c a inner) cs (Ongoing s) = None
        \/ fold_unify (fun inner c => unify env f c a inner) cs (Ongoing s) = Some (Ongoing s)).
    { apply (fold_never_fails (fun c inner => unify env f c a inner)).
      intros c Hc. apply free_result; [exact (Hcs c Hc)|exact Ha|apply H, Hc]. }
    destruct a as [| | | | | |]; try contradiction; cbn zeta in E; rewrite Hvar, Hnonvar in E;
        destruct Hfold as [Hfold|Hfold]; rewrite Hfold in E; try discriminate E;
        destruct (find_first _ cs) as [[[c' s3]|]|]; discriminate E.
Qed.

(* An intersection as the assignee: one of its components is taken *)
Lemma flipped_some: forall n target cs s u,
    intersection_flipped_unify (unify env n) target cs s = Some (Ongoing u) ->
    exists c, In c cs /\ unify env n target c (Ongoing s) = Some (Ongoing u).
Proof. exact (intersection_flipped_unify_found env). Qed.

Lemma flipped_never_fails: forall n target cs s c, In c cs ->
    unify env n target c (Ongoing s) <> Some Failed -> intersection_flipped_unify (unify env n) target cs s <> Some Failed.
Proof.
    intros n target cs s c Hc H. unfold intersection_flipped_unify.
    induction cs as [|x cs IH]; [destruct Hc|]. simpl.
    destruct (unify env n target x (Ongoing s)) as [[w|]|] eqn:E; try discriminate.
    destruct Hc as [<-|Hc]; [congruence|]. exact (IH Hc).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about the fragment and what unify accepts                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma gfrag_component: forall cs c, gfrag (Intersection cs) = true -> In c cs -> gfrag c = true.
Proof. intros cs c H Hc. exact (proj2 (proj2 (intersection_gfrag cs H) c Hc)). Qed.

Lemma gfrag_components_no_vars: forall cs, gfrag (Intersection cs) = true -> forallb no_vars cs = true.
Proof. intros cs H. apply forallb_forall. intros c Hc. apply gfrag_no_vars, (gfrag_component cs c H Hc). Qed.

Lemma gfrag_without_null: forall t, gfrag t = true -> gfrag (without_null t) = true.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p b]|me msg|v o n|g|cs] H; simpl in H |- *; try exact H; try discriminate H.
    - apply andb_true_iff in H. exact (IH n (proj2 H)).
    - exact (IH b H).
Qed.

(* Removing null from a non-null type changes nothing *)
Lemma without_null_id: forall t, gfrag t = true -> is_nullable t = false -> without_null t = t.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p b]|me msg|v o n|g|cs] H Hn; simpl in H, Hn |- *; try reflexivity; try discriminate.
    rewrite (IH b H Hn), Hn, orb_false_r. reflexivity.
Qed.

Lemma without_null_not_nullable: forall t, gfrag t = true -> is_nullable (without_null t) = false.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p b]|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try discriminate H.
    - apply andb_true_iff in H. exact (IH n (proj2 H)).
    - exact (IH b H).
Qed.

Lemma mutability_without_null: forall t, mutability_of env (without_null t) = mutability_of env t.
Proof. intros t. exact (proj1 (without_null_keeps env t)). Qed.

Lemma assignment_mutability_without_null: forall t, assignment_mutability env (without_null t) = assignment_mutability env t.
Proof. exact (without_null_keeps_assignment_mutability env). Qed.

(* Whether the type is a const class, or the values of it are of one: an intersection with such a
   component, a reference to a type parameter bounded by one *)
Fixpoint top_const (t: EType): bool :=
    match t with
    | RootResolved _ c _ => is_const (declaration_of env c)
    | Nullable n | TypeArgument _ _ n => top_const n
    | Generic (mkGenericRef _ _ _ b) | TypeVariable (mkGenericRef _ _ _ b) => top_const b
    | Error _ _ => false
    | Intersection cs => existsb top_const cs
    end.

(* Other than those, a value is assigned as its mutability *)
Lemma not_top_const: forall t, top_const t = false -> assignment_mutability env t = mutability_of env t.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [m c args|n|[gm nn p b]|me msg|v o n|[gm nn p b]|cs]; simpl in H |- *.
    - rewrite H. reflexivity.
    - exact (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl H).
    - exact (IH (esize b) ltac:(cbn [esize]; lia) b eq_refl H).
    - reflexivity.
    - exact (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl H).
    - exact (IH (esize b) ltac:(cbn [esize]; lia) b eq_refl H).
    - f_equal. apply map_ext_in. intros c Hc. pose proof (esize_in cs c Hc).
      apply (IH (esize c) ltac:(cbn [esize]; lia) c eq_refl).
      destruct (top_const c) eqn:E; [|reflexivity]. rewrite <- H. symmetry. apply existsb_exists. exists c. split; assumption.
Qed.

Lemma top_const_mutability: forall t, top_const t = true -> is_subtype_of (mutability_of env t) immutable = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [m c args|n|[gm nn p b]|me msg|v o n|[gm nn p b]|cs]; simpl in H |- *.
    - rewrite H. reflexivity.
    - exact (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl H).
    - exact (IH (esize b) ltac:(cbn [esize]; lia) b eq_refl H).
    - discriminate H.
    - exact (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl H).
    - exact (IH (esize b) ltac:(cbn [esize]; lia) b eq_refl H).
    - apply existsb_exists in H. destruct H as [c [Hc Hct]]. pose proof (esize_in cs c Hc).
      eapply mutability_subtype_trans; [apply fold_intersect_below_element, in_map, Hc|].
      exact (IH (esize c) ltac:(cbn [esize]; lia) c eq_refl Hct).
Qed.

Lemma top_const_with_mutability: forall m t, top_const (with_mutability env m t) = top_const t.
Proof.
    intros m t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t ->.
    destruct t as [mt c args|n|[gm nn p b]|me msg|v o n|[gm nn p b]|cs]; cbn [with_mutability top_const].
    - reflexivity.
    - rewrite <- (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl). destruct (with_mutability env m n); reflexivity.
    - exact (IH (esize b) ltac:(cbn [esize]; lia) b eq_refl).
    - reflexivity.
    - exact (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl).
    - exact (IH (esize b) ltac:(cbn [esize]; lia) b eq_refl).
    - assert (Hall: forall c, In c cs -> top_const (with_mutability env m c) = top_const c).
      { intros c Hc. pose proof (esize_in cs c Hc). apply (IH (esize c) ltac:(cbn [esize]; lia) c eq_refl). }
      clear -Hall. induction cs as [|c cs IHc]; simpl; [reflexivity|].
      rewrite (Hall c (or_introl eq_refl)), IHc; [reflexivity|]. intros c' Hc'. apply Hall. right. exact Hc'.
Qed.

Lemma component_not_nullable: forall c, is_component c = true -> is_nullable c = false.
Proof. intros [| |[gm nn p b]| | | |] H; simpl in H |- *; try discriminate H; try reflexivity. apply negb_true_iff, H. Qed.

(* The mutability of what is assigned fits that of the target *)
Lemma accepted_mutability: forall n t a s, gfrag t = true -> gfrag a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> is_subtype_of (assignment_mutability env a) (assignment_mutability env t) = true.
Proof.
    induction n as [|n IH]; intros t a s Ht Ha H; [discriminate H|].
    destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> [Htn Ht']]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]].
    - destruct (gfrag_cases a Ha) as [[ma [ca [aargs ->]]]|[[an [-> [Han Ha']]]|[[ga [nga [pa [ba [-> Hba]]]]]|[acs ->]]]].
      + rewrite unify_classes in H. destruct (base_type_is_subtype_of env ca ct); [|discriminate H].
        destruct (is_subtype_of _ _) eqn:E; [reflexivity|discriminate H].
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite step_root_generic in H. exact (IH _ _ s Ht Hba H).
      + rewrite step_root_inter in H. destruct (flipped_some n _ acs s s H) as [c [Hc Hu]].
        eapply mutability_subtype_trans; [apply (intersection_assignment_mutability_below_component env), Hc|].
        exact (IH _ c s Ht (gfrag_component acs c Ha Hc) Hu).
    - change (assignment_mutability env (Nullable tn)) with (assignment_mutability env tn).
      destruct (gfrag_cases a Ha) as [[ma [ca [aargs ->]]]|[[an [-> [Han Ha']]]|[[ga [nga [pa [ba [-> Hba]]]]]|[acs ->]]]].
      + rewrite unify_nullable_class in H. exact (IH tn _ s Ht' Ha H).
      + rewrite unify_nullable_nullable in H. exact (IH tn an s Ht' Ha' H).
      + rewrite step_nullable_generic in H. rewrite <- assignment_mutability_without_null.
        exact (IH tn _ s Ht' (gfrag_without_null _ Ha) H).
      + rewrite step_nullable_inter in H. exact (IH tn _ s Ht' Ha H).
    - destruct (gfrag_cases a Ha) as [[ma [ca [aargs ->]]]|[[an [-> [Han Ha']]]|[[ga [nga [pa [ba [-> Hba]]]]]|[acs ->]]]].
      + rewrite step_generic_root in H. destruct (_ && _) eqn:E in H; [|discriminate H]. apply andb_true_iff in E. apply E.
      + rewrite step_generic_nullable in H. discriminate H.
      + rewrite step_generic_generic in H. destruct (param_eqb pa pt).
        * destruct (_ && _) eqn:E in H; [|discriminate H]. apply andb_true_iff in E. apply E.
        * exact (IH _ _ s Ht Hba H).
      + rewrite step_generic_inter in H. destruct (flipped_some n _ acs s s H) as [c [Hc Hu]].
        eapply mutability_subtype_trans; [apply (intersection_assignment_mutability_below_component env), Hc|].
        exact (IH _ c s Ht (gfrag_component acs c Ha Hc) Hu).
    - rewrite (intersection_assignment_mutability env). apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
      intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]].
      destruct (gfrag_cases a Ha) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [pa [ba [-> _]]]]]|[acs ->]]]];
          [| rewrite step_inter_nullable in H; discriminate H| |];
          exact (IH c _ s (gfrag_component tcs c Ht Hc) Ha
              (inter_target_all n tcs _ s s (gfrag_components_no_vars tcs Ht) (gfrag_no_vars _ Ha) I H c Hc)).
Qed.

(* What a non-null type takes is non-null *)
Lemma accepted_not_nullable: forall n t a s, gfrag t = true -> gfrag a = true -> is_nullable t = false ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> is_nullable a = false.
Proof.
    induction n as [|n IH]; intros t a s Ht Ha Hn H; [discriminate H|].
    destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> [Htn Ht']]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]];
        [|discriminate Hn| |];
        destruct (gfrag_cases a Ha) as [[ma [ca [aargs ->]]]|[[an [-> [Han Ha']]]|[[ga [nga [pa [ba [-> Hba]]]]]|[acs ->]]]];
        try reflexivity.
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite step_root_generic in H. exact (IH _ _ s Ht Hba Hn H).
    - rewrite step_generic_nullable in H. discriminate H.
    - rewrite step_generic_generic in H. simpl in Hn |- *. destruct (param_eqb pa pt).
      + destruct (_ && _) eqn:E in H; [|discriminate H]. apply andb_true_iff in E. destruct E as [_ E].
        rewrite Hn, orb_false_r in E. apply negb_true_iff, E.
      + exact (IH _ _ s Ht Hba Hn H).
    - rewrite step_inter_nullable in H. discriminate H.
    - destruct (intersection_gfrag tcs Ht) as [Hne Hcs]. destruct tcs as [|c0 tcs']; [contradiction|].
      destruct (Hcs c0 (or_introl eq_refl)) as [Hc0 Hf0].
      apply (IH c0 _ s Hf0 Ha (component_not_nullable c0 Hc0)).
      exact (inter_target_all n (c0 :: tcs') _ s s (gfrag_components_no_vars _ Ht) (gfrag_no_vars _ Ha) I H c0 (or_introl eq_refl)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Effective bounds                                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

(* The effective bound of a reference to a type parameter, from its declared bound: with the
   mutability of the reference (BoundTypeReference.withMutability) and, for `V!` and in
   intersections and nullable types, without null (withCombinedNullability(NOT_NULLABLE)) *)
Definition adjust (m: Mutability) (nn: bool) (d: EType): EType :=
    if nn then without_null (with_mutability env m d) else with_mutability env m d.

(* The same type, of mutabilities that are no more than those of the other, and maybe without null *)
Fixpoint vle (t' t: EType) {struct t}: Prop :=
    match t with
    | RootResolved _ c args =>
        match t' with
        | RootResolved _ c' args' => c' = c /\ args' = args /\ is_subtype_of (mutability_of env t') (mutability_of env t) = true
        | _ => False
        end
    | Nullable n => match t' with Nullable n' => vle n' n | _ => vle t' n end
    | Generic (mkGenericRef _ _ p b) =>
        match t' with Generic (mkGenericRef _ _ p' b') => p' = p /\ vle b' b | _ => False end
    | Intersection cs =>
        match t' with
        | Intersection cs' =>
            (fix go (l' l: list EType) {struct l}: Prop :=
                match l', l with
                | [], [] => True
                | x' :: r', x :: r => vle x' x /\ go r' r
                | _, _ => False
                end) cs' cs
        | _ => False
        end
    | _ => False
    end.

Lemma vle_inter: forall cs' cs, vle (Intersection cs') (Intersection cs) -> Forall2 vle cs' cs.
Proof.
    intros cs'. induction cs' as [|x' r' IH]; intros [|x r] H; simpl in H; try contradiction; constructor.
    - apply H.
    - apply IH. apply H.
Qed.

Lemma forall2_right: forall {A: Type} (R: A -> A -> Prop) l' l x, Forall2 R l' l -> In x l -> exists x', In x' l' /\ R x' x.
Proof.
    intros A R l' l x H. induction H as [|a b l' l Hab H IH]; intros Hx; [destruct Hx|].
    destruct Hx as [<-|Hx]; [exists a; split; [left; reflexivity|exact Hab]|].
    destruct (IH Hx) as [x' [Hin HR]]. exists x'. split; [right; exact Hin|exact HR].
Qed.

Lemma intersect_mutability_mono: forall a' a b' b, is_subtype_of a' a = true -> is_subtype_of b' b = true ->
    is_subtype_of (intersect_mutability a' b') (intersect_mutability a b) = true.
Proof. intros [] [] [] [] H1 H2; simpl in *; first [reflexivity|discriminate]. Qed.

Lemma fold_intersect_mono: forall l' l acc' acc, Forall2 (fun x' x => is_subtype_of x' x = true) l' l ->
    is_subtype_of acc' acc = true ->
    is_subtype_of (fold_left intersect_mutability l' acc') (fold_left intersect_mutability l acc) = true.
Proof.
    intros l' l acc' acc H. revert acc' acc. induction H as [|x' x l' l Hx H IH]; intros acc' acc Hacc; simpl; [exact Hacc|].
    apply IH. apply intersect_mutability_mono; assumption.
Qed.

Lemma forall2_map: forall {A B: Type} (R: A -> A -> Prop) (S: B -> B -> Prop) (f: A -> B) l' l,
    Forall2 R l' l -> (forall x' x, In x l -> R x' x -> S (f x') (f x)) -> Forall2 S (map f l') (map f l).
Proof.
    intros A B R S f l' l H. induction H as [|x' x l' l Hx H IH]; intros Himpl; simpl; constructor.
    - apply Himpl; [left; reflexivity|exact Hx].
    - apply IH. intros a' a Ha. apply Himpl. right. exact Ha.
Qed.

Lemma vle_mutability: forall t t', vle t' t -> is_subtype_of (assignment_mutability env t') (assignment_mutability env t) = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> t' H.
    destruct t as [m c args|n|[gm nn p b]|me msg|v o n|g|cs]; simpl in H; try contradiction.
    - destruct t' as [m' c' args'| | | | | |]; try contradiction. destruct H as [-> [-> H]]. simpl in H |- *.
      destruct (is_const (declaration_of env c)); [reflexivity|exact H].
    - destruct t' as [m' c' a'|n'|g'|me' msg'|v' o' n'|g'|cs'];
          first [exact (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl _ H)
                |exact (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl n' H)].
    - destruct t' as [| |[gm' nn' p' b']| | | |]; try contradiction. destruct H as [_ H].
      exact (IH (esize b) ltac:(cbn [esize]; lia) b eq_refl b' H).
    - destruct t' as [| | | | | |cs']; try contradiction. apply vle_inter in H.
      rewrite !(intersection_assignment_mutability env). apply fold_intersect_mono; [|apply mutability_is_subtype_of_refl].
      apply (forall2_map vle _ (assignment_mutability env) cs' cs H). intros x' x Hx Hv.
      pose proof (esize_in cs x Hx). exact (IH (esize x) ltac:(cbn [esize]; lia) x eq_refl x' Hv).
Qed.

Lemma vle_nullable: forall t t', vle t' t -> is_nullable t' = true -> is_nullable t = true.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p b]|me msg|v o n|g|cs] t' H Hn; simpl in H |- *; try contradiction; try reflexivity.
    - destruct t' as [| | | | | |]; try contradiction. discriminate Hn.
    - destruct t' as [| |[gm' nn' p' b']| | | |]; try contradiction. destruct H as [_ H]. exact (IH b b' H Hn).
    - destruct t' as [| | | | | |]; try contradiction. discriminate Hn.
Qed.

Lemma vle_without_null: forall t t', gfrag t = true -> gfrag t' = true -> vle t' t -> vle (without_null t') (without_null t).
Proof.
    fix IH 1. intros [m c args|n|[gm nn p b]|me msg|v o n|g|cs] t' Ht Ht' H; simpl in H, Ht; try contradiction.
    - destruct t' as [| | | | | |]; try contradiction. exact H.
    - apply andb_true_iff in Ht. destruct Ht as [Hn Hfn].
      change (without_null (Nullable n)) with (without_null n). rewrite (without_null_id n Hfn (non_null_not_nullable n Hn)).
      destruct t' as [m' c' a'|n'|[gm' nn' p' b']|me' msg'|v' o' n'|g'|cs']; simpl in H, Ht' |- *; try discriminate Ht'; try exact H.
      { apply andb_true_iff in Ht'. rewrite (without_null_id n' (proj2 Ht') (non_null_not_nullable n' (proj1 Ht'))). exact H. }
      assert (Hb': is_nullable b' = false).
      { apply not_true_iff_false. intros E.
        pose proof (vle_nullable n (Generic (mkGenericRef gm' nn' p' b')) H E) as Ex. rewrite (non_null_not_nullable n Hn) in Ex. discriminate Ex. }
      rewrite (without_null_id b' Ht' Hb'), Hb', orb_false_r. exact H.
    - destruct t' as [| |[gm' nn' p' b']| | | |]; try contradiction. destruct H as [-> H]. simpl. split; [reflexivity|].
      exact (IH b b' Ht Ht' H).
    - destruct t' as [| | | | | |]; try contradiction. exact H.
Qed.

Lemma is_nullable_with_mutability: forall m t, is_nullable (with_mutability env m t) = is_nullable t.
Proof.
    fix IH 2. intros m [mt c args|n|[gm nn p b]|me msg|v o n|[gm nn p b]|cs]; simpl; try reflexivity.
    - destruct (with_mutability env m n); reflexivity.
    - apply IH.
    - apply IH.
    - apply IH.
Qed.

Lemma with_mutability_shape: forall m t, gfrag t = true ->
    match t with
    | RootResolved _ c args => exists m', with_mutability env m t = RootResolved m' c args
    | Nullable n => with_mutability env m t = Nullable (with_mutability env m n)
    | Generic (mkGenericRef gm nn p b) => with_mutability env m t = Generic (mkGenericRef (Some m) nn p (with_mutability env m b))
    | Intersection cs => with_mutability env m t = Intersection (map (with_mutability env m) cs)
    | _ => False
    end.
Proof.
    intros m [mt c args|n|[gm nn p b]|me msg|v o n|g|cs] H; simpl in H; try discriminate H; try reflexivity.
    - eexists. reflexivity.
    - apply andb_true_iff in H. destruct H as [Hn _]. simpl.
      destruct (with_mutability env m n) eqn:E; try reflexivity.
      exfalso. pose proof (is_nullable_with_mutability m n) as Hnn. rewrite E in Hnn. simpl in Hnn.
      rewrite (non_null_not_nullable n Hn) in Hnn. discriminate Hnn.
Qed.

Lemma gfrag_with_mutability: forall m t, gfrag t = true -> gfrag (with_mutability env m t) = true.
Proof.
    intros m t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    pose proof (with_mutability_shape m t H) as Hs.
    destruct t as [mt c args|n|[gm nn p b]|me msg|v o n|g|cs]; try contradiction.
    - destruct Hs as [m' ->]. destruct (root_gfrag mt c args H) as [Hl Ha]. apply make_root_gfrag; assumption.
    - rewrite Hs. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hn Hfn].
      assert (Hf: gfrag (with_mutability env m n) = true) by (apply (IH (esize n)); [cbn [esize]; lia|reflexivity|exact Hfn]).
      rewrite Hf, andb_true_r.
      destruct (gfrag_cases n Hfn) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; simpl in Hn |- *;
          try discriminate Hn; try reflexivity.
      rewrite is_nullable_with_mutability. exact Hn.
    - rewrite Hs. simpl in H |- *. apply (IH (esize b)); [cbn [esize]; lia|reflexivity|exact H].
    - rewrite Hs. destruct (intersection_gfrag cs H) as [Hne Hcs]. simpl.
      apply andb_true_iff. split; [destruct cs; [contradiction|reflexivity]|].
      apply forallb_forall. intros c' Hc'. apply in_map_iff in Hc'. destruct Hc' as [c [<- Hc]].
      destruct (Hcs c Hc) as [Hcc Hcf]. pose proof (esize_in cs c Hc).
      assert (Hf: gfrag (with_mutability env m c) = true) by (apply (IH (esize c)); [cbn [esize]; lia|reflexivity|exact Hcf]).
      rewrite Hf, andb_true_r.
      destruct (component_cases c Hcc Hcf) as [[? [? [? ->]]]|[? [? [? [? [-> [Hnb _]]]]]]]; simpl; [reflexivity|].
      rewrite is_nullable_with_mutability, Hnb. reflexivity.
Qed.

Lemma gfrag_adjust: forall m nn t, gfrag t = true -> gfrag (adjust m nn t) = true.
Proof.
    intros m [] t H; unfold adjust; [apply gfrag_without_null|]; apply gfrag_with_mutability; exact H.
Qed.

(* Effective bounds of the same declared bound, of mutabilities in order, are in order *)
Lemma adjust_vle: forall d m1 nn1 m2 nn2, gfrag d = true -> is_subtype_of m1 m2 = true ->
    (is_nullable (adjust m1 nn1 d) = true -> is_nullable (adjust m2 nn2 d) = true) ->
    vle (adjust m1 nn1 d) (adjust m2 nn2 d).
Proof.
    intros d. remember (esize d) as k eqn:Hk. revert d Hk. induction k as [k IH] using lt_wf_ind.
    intros d -> m1 nn1 m2 nn2 H Hm Hn.
    pose proof (with_mutability_shape m1 d H) as Hs1. pose proof (with_mutability_shape m2 d H) as Hs2.
    unfold adjust in *.
    destruct d as [mt c args|n|[gm nn p b]|me msg|v o n|g|cs]; try contradiction.
    - cbn [with_mutability]. destruct (is_const (declaration_of env c)) eqn:Ec;
          destruct nn1, nn2; cbn [without_null vle]; (split; [reflexivity|]); (split; [reflexivity|]);
          cbn [mutability_of or_readonly]; rewrite Ec; first [reflexivity|exact Hm].
    - simpl in H. apply andb_true_iff in H. destruct H as [Hnn Hfn].
      assert (Hnot: forall m, is_nullable (with_mutability env m n) = false)
          by (intros m; rewrite is_nullable_with_mutability; exact (non_null_not_nullable n Hnn)).
      assert (IHn: vle (with_mutability env m1 n) (with_mutability env m2 n)).
      { apply (IH (esize n)) with (nn1 := false) (nn2 := false); [cbn [esize]; lia|reflexivity|exact Hfn|exact Hm|].
        unfold adjust. rewrite Hnot. discriminate. }
      assert (Hid: forall m, without_null (with_mutability env m n) = with_mutability env m n)
          by (intros m; exact (without_null_id _ (gfrag_with_mutability m n Hfn) (Hnot m))).
      rewrite Hs1, Hs2 in *. destruct nn1, nn2; simpl in Hn |- *.
      + rewrite !Hid. exact IHn.
      + rewrite Hid. destruct (with_mutability env m1 n) eqn:E; try exact IHn; pose proof (Hnot m1) as Hx; rewrite E in Hx; discriminate Hx.
      + rewrite Hid, (Hnot m2) in Hn. discriminate (Hn eq_refl).
      + exact IHn.
    - simpl in H. rewrite Hs1, Hs2. destruct nn1, nn2; simpl; (split; [reflexivity|]);
          [apply (IH (esize b)) with (nn1 := true) (nn2 := true)
          |apply (IH (esize b)) with (nn1 := true) (nn2 := false)
          |apply (IH (esize b)) with (nn1 := false) (nn2 := true)
          |apply (IH (esize b)) with (nn1 := false) (nn2 := false)];
          try (cbn [esize]; lia); try reflexivity; try exact H; try exact Hm;
          unfold adjust; rewrite Hs1, Hs2 in Hn; simpl in Hn; exact Hn.
    - rewrite Hs1, Hs2. destruct (intersection_gfrag cs H) as [_ Hcs].
      assert (Hall: forall c, In c cs -> vle (with_mutability env m1 c) (with_mutability env m2 c)).
      { intros c Hc. destruct (Hcs c Hc) as [Hcc Hcf]. pose proof (esize_in cs c Hc).
        apply (IH (esize c)) with (nn1 := false) (nn2 := false); [cbn [esize]; lia|reflexivity|exact Hcf|exact Hm|].
        unfold adjust. rewrite is_nullable_with_mutability, (component_not_nullable c Hcc). discriminate. }
      destruct nn1, nn2; simpl; clear -Hall; induction cs as [|c cs IHc]; simpl; try exact I;
          (split; [apply Hall; left; reflexivity|apply IHc; intros c' Hc'; apply Hall; right; exact Hc']).
Qed.

(* Whatever takes a type, never rejects one of the same, of mutabilities no more than its own, maybe
   without null: Kotlin compares two references to the same type parameter by their mutability and
   nullability, which is sound because their bounds are such *)
Lemma vle_root: forall t' m c args, vle t' (RootResolved m c args) ->
    exists m', t' = RootResolved m' c args /\ is_subtype_of (assignment_mutability env t') (assignment_mutability env (RootResolved m c args)) = true.
Proof.
    intros [m' c' a'| | | | | |] m c args H; simpl in H; try contradiction. destruct H as [-> [-> H]].
    exists m'. split; [reflexivity|]. simpl in H |- *. destruct (is_const (declaration_of env c)); [reflexivity|exact H].
Qed.

Lemma vle_generic: forall t' gm nn p b, vle t' (Generic (mkGenericRef gm nn p b)) ->
    exists gm' nn' b', t' = Generic (mkGenericRef gm' nn' p b') /\ vle b' b.
Proof. intros [| |[gm' nn' p' b']| | | |] gm nn p b H; simpl in H; try contradiction. destruct H as [-> H]. exists gm', nn', b'. auto. Qed.

Lemma vle_intersection: forall t' cs, vle t' (Intersection cs) -> exists cs', t' = Intersection cs' /\ Forall2 vle cs' cs.
Proof. intros [| | | | | |cs'] cs H; simpl in H; try contradiction. exists cs'. split; [reflexivity|]. apply vle_inter, H. Qed.

Lemma gfrag_bound: forall gm nn p b, gfrag (Generic (mkGenericRef gm nn p b)) = true -> gfrag b = true.
Proof. intros gm nn p b H. exact H. Qed.

Lemma bounds_ordered: forall n z t t' s, gfrag z = true -> gfrag t = true -> gfrag t' = true -> vle t' t ->
    unify env n z t (Ongoing s) = Some (Ongoing s) -> never_fails z t'.
Proof.
    induction n as [|n IH]; intros z t t' s Hz Ht Ht' Hv H; [discriminate H|].
    destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> [Hzn Hz']]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]].
    - destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> [Htn Ht'']]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]].
      + (* class types *)
        destruct (vle_root t' mt ct targs Hv) as [m' [-> Hmv]].
        apply never_fails_step. intros f s' E.
        pose proof (gsuccess_never_fails _ _ _ _ Hz Ht H (S f) s') as Ht0.
        rewrite unify_classes in H, E, Ht0.
        destruct (base_type_is_subtype_of env ct cz); [|discriminate H].
        destruct (is_subtype_of (assignment_mutability env (RootResolved mt ct targs)) _) eqn:Em; [|discriminate H].
        rewrite (mutability_trans _ _ _ Hmv Em) in E. exact (Ht0 E).
      + rewrite unify_class_nullable in H. discriminate H.
      + destruct (vle_generic t' gt ngt pt bt Hv) as [gt' [ngt' [bt' [-> Hbv]]]].
        rewrite step_root_generic in H. apply never_fails_step. intros f s' E. rewrite step_root_generic in E.
        exact (IH _ _ _ s Hz Hbt (gfrag_bound _ _ _ _ Ht') Hbv H f s' E).
      + destruct (vle_intersection t' tcs Hv) as [tcs' [-> Hcv]].
        rewrite step_root_inter in H. destruct (flipped_some n _ tcs s s H) as [c [Hc Hu]].
        destruct (forall2_right vle tcs' tcs c Hcv Hc) as [c' [Hc' Hcv']].
        apply never_fails_step. intros f s' E. rewrite step_root_inter in E.
        eapply (flipped_never_fails f _ tcs' s' c' Hc'); [|exact E].
        exact (IH _ _ _ s Hz (gfrag_component tcs c Ht Hc) (gfrag_component tcs' c' Ht' Hc') Hcv' Hu f s').
    - destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> [Htn Ht'']]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]].
      + destruct (vle_root t' mt ct targs Hv) as [m' [-> _]].
        rewrite unify_nullable_class in H. apply never_fails_step. intros f s' E. rewrite unify_nullable_class in E.
        exact (IH _ _ _ s Hz' Ht Ht' Hv H f s' E).
      + rewrite unify_nullable_nullable in H. apply never_fails_step. intros f s' E. simpl in Hv.
        destruct (gfrag_cases t' Ht') as [[m' [c' [a' ->]]]|[[n' [-> [Hn' Hfn']]]|[[g' [ng' [p' [b' [-> Hb']]]]]|[cs' ->]]]].
        * rewrite unify_nullable_class in E. exact (IH _ _ _ s Hz' Ht'' Ht' Hv H f s' E).
        * rewrite unify_nullable_nullable in E. exact (IH _ _ _ s Hz' Ht'' Hfn' Hv H f s' E).
        * rewrite step_nullable_generic in E. rewrite (without_null_id _ Ht') in E.
          -- exact (IH _ _ _ s Hz' Ht'' Ht' Hv H f s' E).
          -- apply not_true_iff_false. intros En. pose proof (vle_nullable tn _ Hv En) as Ex.
             rewrite (non_null_not_nullable tn Htn) in Ex. discriminate Ex.
        * rewrite step_nullable_inter in E. exact (IH _ _ _ s Hz' Ht'' Ht' Hv H f s' E).
      + destruct (vle_generic t' gt ngt pt bt Hv) as [gt' [ngt' [bt' [-> _]]]].
        rewrite step_nullable_generic in H. apply never_fails_step. intros f s' E. rewrite step_nullable_generic in E.
        exact (IH _ _ _ s Hz' (gfrag_without_null _ Ht) (gfrag_without_null _ Ht')
            (vle_without_null _ _ Ht Ht' Hv) H f s' E).
      + destruct (vle_intersection t' tcs Hv) as [tcs' [-> _]].
        rewrite step_nullable_inter in H. apply never_fails_step. intros f s' E. rewrite step_nullable_inter in E.
        exact (IH _ _ _ s Hz' Ht Ht' Hv H f s' E).
    - destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> [Htn Ht'']]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]].
      + (* a class type to a type parameter: Nothing *)
        destruct (vle_root t' mt ct targs Hv) as [m' [-> Hmv]].
        rewrite step_generic_root in H. apply never_fails_step. intros f s' E. rewrite step_generic_root in E.
        destruct (_ && _) eqn:E1 in H; [|discriminate H]. apply andb_true_iff in E1. destruct E1 as [Hn Hm].
        pose proof (mutability_trans _ _ _ Hmv Hm) as Hm'. simpl in Hn.
        change (is_non_nullable_nothing env (RootResolved m' ct targs)) with (class_eqb ct nothing) in E.
        rewrite Hn, Hm' in E. discriminate E.
      + rewrite step_generic_nullable in H. discriminate H.
      + destruct (vle_generic t' gt ngt pt bt Hv) as [gt' [ngt' [bt' [-> Hbv]]]].
        rewrite step_generic_generic in H. apply never_fails_step. intros f s' E. rewrite step_generic_generic in E.
        destruct (param_eqb pt pz).
        * destruct (_ && _) eqn:E1 in H; [|discriminate H]. apply andb_true_iff in E1. destruct E1 as [Hm Hn].
          rewrite (mutability_trans _ _ _ (vle_mutability bt bt' Hbv) Hm) in E.
          destruct (is_nullable bt') eqn:Ebt'; [|discriminate E].
          rewrite (vle_nullable bt bt' Hbv Ebt') in Hn. simpl in Hn. rewrite Hn, orb_true_r in E. discriminate E.
        * exact (IH _ _ _ s Hz Hbt (gfrag_bound _ _ _ _ Ht') Hbv H f s' E).
      + destruct (vle_intersection t' tcs Hv) as [tcs' [-> Hcv]].
        rewrite step_generic_inter in H. destruct (flipped_some n _ tcs s s H) as [c [Hc Hu]].
        destruct (forall2_right vle tcs' tcs c Hcv Hc) as [c' [Hc' Hcv']].
        apply never_fails_step. intros f s' E. rewrite step_generic_inter in E.
        eapply (flipped_never_fails f _ tcs' s' c' Hc'); [|exact E].
        exact (IH _ _ _ s Hz (gfrag_component tcs c Ht Hc) (gfrag_component tcs' c' Ht' Hc') Hcv' Hu f s').
    - (* an intersection as the target *)
      destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> _]]|[[gt [ngt [pt [bt [-> _]]]]]|[tcs ->]]]];
          [destruct (vle_root t' mt ct targs Hv) as [m' [-> _]]
          |rewrite step_inter_nullable in H; discriminate H
          |destruct (vle_generic t' gt ngt pt bt Hv) as [gt' [ngt' [bt' [-> _]]]]
          |destruct (vle_intersection t' tcs Hv) as [tcs' [-> _]]];
          (apply inter_target_never_fails; [exact (gfrag_components_no_vars zcs Hz)|exact (gfrag_no_vars _ Ht')|exact I|]);
          intros c Hc; apply (IH c _ _ s (gfrag_component zcs c Hz Hc) Ht Ht' Hv);
          exact (inter_target_all n zcs _ s s (gfrag_components_no_vars zcs Hz) (gfrag_no_vars _ Ht) I H c Hc).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* References to type parameters, as the frontend makes them                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* The declared bound of each type parameter (BoundTypeParameter.bound). Applying a mutability to it
   gives it that mutability: it is no const class (whose references are always immutable), nor has
   one as a component. *)
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Let declared_gfrag := bw_gfrag env declared declared_wf.
Let declared_mutability := bw_mutability env declared declared_wf.

(* Every reference to a type parameter in the type has an effective bound made from the declared
   one, as GenericTypeReference and MappedEffectiveBoundGenericTypeReference make them *)
Fixpoint refs_wf (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => refs_wf a /\ acc) True arguments
    | Nullable n => refs_wf n
    | Generic (mkGenericRef _ _ p bound) => refs_wf bound /\ exists m nn, bound = adjust m nn (declared p)
    | TypeArgument _ _ n => refs_wf n
    | Intersection cs => fold_right (fun c acc => refs_wf c /\ acc) True cs
    | _ => True
    end.

Lemma refs_wf_root: forall m c args, refs_wf (RootResolved m c args) -> forall a, In a args -> refs_wf a.
Proof. intros m c args H. exact (fold_and_in refs_wf args H). Qed.

Lemma refs_wf_make_root: forall m c args, (forall a, In a args -> refs_wf a) -> refs_wf (RootResolved m c args).
Proof.
    intros m c args H. simpl. induction args as [|a args IH]; [exact I|]. split; [apply H; left; reflexivity|].
    apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma refs_wf_components: forall cs, refs_wf (Intersection cs) -> forall c, In c cs -> refs_wf c.
Proof. intros cs H. exact (fold_and_in refs_wf cs H). Qed.

Lemma mutability_adjust: forall p m nn, mutability_of env (adjust m nn (declared p)) = m.
Proof. intros p m [|]; unfold adjust; [rewrite mutability_without_null|]; apply declared_mutability. Qed.

(* Taking any mutability applied to it, a declared bound is no const class, nor has one as a
   component: its values are assigned as the mutability applied *)
Lemma declared_assignment_mutability: forall p m, assignment_mutability env (with_mutability env m (declared p)) = m.
Proof.
    intros p m. assert (Hd: top_const (declared p) = false).
    { destruct (top_const (declared p)) eqn:E; [|reflexivity]. exfalso.
      rewrite <- (top_const_with_mutability readonly) in E. pose proof (top_const_mutability _ E) as H.
      rewrite declared_mutability in H. discriminate H. }
    rewrite not_top_const; [apply declared_mutability|]. rewrite top_const_with_mutability. exact Hd.
Qed.

Lemma assignment_mutability_adjust: forall p m nn, assignment_mutability env (adjust m nn (declared p)) = m.
Proof. intros p m [|]; unfold adjust; [rewrite assignment_mutability_without_null|]; apply declared_assignment_mutability. Qed.

(* Two references to the same type parameter: one of a mutability and nullability that fit the
   other's has a bound below the other's *)
Lemma same_parameter_bounds: forall g1 n1 p b1 g2 n2 b2,
    refs_wf (Generic (mkGenericRef g1 n1 p b1)) -> refs_wf (Generic (mkGenericRef g2 n2 p b2)) ->
    is_subtype_of (assignment_mutability env b1) (assignment_mutability env b2) = true -> (is_nullable b1 = true -> is_nullable b2 = true) ->
    vle b1 b2.
Proof.
    intros g1 n1 p b1 g2 n2 b2 [_ [m1 [nn1 E1]]] [_ [m2 [nn2 E2]]] Hm Hn. subst b1 b2.
    rewrite !assignment_mutability_adjust in Hm. exact (adjust_vle (declared p) m1 nn1 m2 nn2 (declared_gfrag p) Hm Hn).
Qed.

Lemma without_null_twice: forall t, gfrag t = true -> without_null (without_null t) = without_null t.
Proof.
    intros t H. apply without_null_id; [apply gfrag_without_null, H|apply without_null_not_nullable, H].
Qed.

Lemma refs_wf_without_null: forall t, gfrag t = true -> refs_wf t -> refs_wf (without_null t).
Proof.
    fix IH 1. intros [m c args|n|[gm nn p b]|me msg|v o n|g|cs] H Hr; simpl in H, Hr |- *; try exact Hr; try discriminate H.
    { apply andb_true_iff in H. exact (IH n (proj2 H) Hr). }
    destruct Hr as [Hb [m [nn0 E]]]. split; [exact (IH b H Hb)|]. exists m, true. rewrite E.
    unfold adjust. destruct nn0; [|reflexivity].
    apply without_null_twice, gfrag_with_mutability, declared_gfrag.
Qed.

(* Instances of templates are made of the type arguments they are instantiated with *)
Lemma template_instances_refs_wf: forall sub ys,
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> is_type_argument y = true) ->
    (forall y, In y ys -> refs_wf y) ->
    forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> refs_wf (instantiate env (bindings_of env sub ys) t))
    /\ (forall a, argument_depth a <= k -> template_argument env sub a = true ->
        refs_wf (instantiate env (bindings_of env sub ys) a)).
Proof.
    intros sub ys Hl Hta Hys k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c arguments, depth (RootResolved m c arguments) <= S k ->
        template_type env sub (RootResolved m c arguments) = true ->
        refs_wf (instantiate env (bindings_of env sub ys) (RootResolved m c arguments))).
    { intros m c arguments Hd Ht. destruct (root_template env sub m c arguments Ht) as [_ Hargs].
      rewrite instantiate_class. apply refs_wf_make_root.
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
      pose proof (argument_depth_below m c arguments a Ha). apply IHa; [lia|apply Hargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> Ht']]]]].
      + exact (Hroot m c arguments Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class, <- instantiate_class.
        exact (Hroot m c arguments ltac:(lia) Ht').
    - intros a Hd Ha. destruct (template_kind env sub a Ha) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hl) Hi) as [y Hy].
        rewrite (selects env wf sub ys p bp i y Hi Hy (Hta y (nth_error_In _ _ Hy))). exact (Hys y (nth_error_In _ _ Hy)).
      + simpl in Hd. rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn)).
        destruct (mentions_loosely_bound _ n); [destruct v|]; simpl; first [exact I | apply IHt; [lia|exact Hn]].
Qed.

Lemma supertype_arguments_refs_wf: forall sub super xs,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids env sub) -> (forall x, In x xs -> is_type_argument x = true) ->
    (forall x, In x xs -> refs_wf x) ->
    forall a, In a (parameterized_supertype_arguments env sub xs super) -> refs_wf a.
Proof.
    intros sub super xs Hne Hn Hb Hl Hta Hxs. destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hb) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq. intros a Ha. apply in_map_iff in Ha. destruct Ha as [t [<- Hin]].
    exact (proj2 (template_instances_refs_wf sub xs Hl Hta Hxs _) t (le_n _) (Ht t Hin)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Without null                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma find_first_ext: forall (g h: EType -> option Unification) l, (forall c, In c l -> g c = h c) -> find_first g l = find_first h l.
Proof.
    intros g h l. induction l as [|c l IH]; intros H; [reflexivity|]. simpl. rewrite (H c (or_introl eq_refl)).
    destruct (h c) as [[s|]|]; try reflexivity. apply IH. intros c' Hc'. apply H. right. exact Hc'.
Qed.

(* A type parameter as the target takes what is non-null whatever its bound, as long as the mutability
   stays the same *)
Lemma generic_target_bound_irrelevant: forall n g n1 n2 p b1 b2 a s,
    assignment_mutability env b1 = assignment_mutability env b2 -> gfrag a = true -> is_nullable a = false ->
    unify env n (Generic (mkGenericRef g n1 p b1)) a (Ongoing s) = unify env n (Generic (mkGenericRef g n2 p b2)) a (Ongoing s).
Proof.
    induction n as [|n IH]; intros g n1 n2 p b1 b2 a s Hm Ha Hn; [reflexivity|].
    destruct (gfrag_cases a Ha) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [pa [ba [-> Hba]]]]]|[acs ->]]]].
    - rewrite !step_generic_root. simpl assignment_mutability at 2 4. rewrite Hm. reflexivity.
    - discriminate Hn.
    - rewrite !step_generic_generic. simpl in Hn. rewrite Hn, Hm. destruct (param_eqb pa p); [reflexivity|].
      exact (IH g n1 n2 p b1 b2 ba s Hm Hba Hn).
    - rewrite !step_generic_inter. unfold intersection_flipped_unify.
      rewrite (find_first_ext (fun c => unify env n (Generic (mkGenericRef g n1 p b1)) c (Ongoing s))
          (fun c => unify env n (Generic (mkGenericRef g n2 p b2)) c (Ongoing s))); [reflexivity|].
      intros c Hc. destruct (proj2 (intersection_gfrag acs Ha) c Hc) as [Hcc Hcf].
      exact (IH g n1 n2 p b1 b2 c s Hm Hcf (component_not_nullable c Hcc)).
Qed.

(* Without null on both sides, what is accepted stays accepted *)
Lemma accepted_without_null: forall n y x s, gfrag y = true -> gfrag x = true ->
    match y with Nullable _ => False | _ => True end ->
    unify env n y x (Ongoing s) = Some (Ongoing s) -> unify env n (without_null y) (without_null x) (Ongoing s) = Some (Ongoing s).
Proof.
    induction n as [|n IH]; intros y x s Hy Hx Hshape H; [discriminate H|].
    destruct (gfrag_cases y Hy) as [[my [cy [yargs ->]]]|[[yn [-> _]]|[[gy [ngy [py [by' [-> Hby]]]]]|[ycs ->]]]];
        [| contradiction | |].
    - rewrite (without_null_id x Hx); [exact H|].
      exact (accepted_not_nullable (S n) _ x s Hy Hx eq_refl H).
    - destruct (is_nullable x) eqn:Ex.
      + destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]];
            try discriminate Ex.
        * rewrite step_generic_nullable in H. discriminate H.
        * cbn [without_null]. rewrite step_generic_generic in H |- *. simpl in Ex. destruct (param_eqb px py).
          -- destruct (_ && _) eqn:E in H; [|discriminate H]. apply andb_true_iff in E. destruct E as [Hm _].
             rewrite !assignment_mutability_without_null, Hm. simpl. rewrite (without_null_not_nullable bx Hbx). reflexivity.
          -- destruct (gfrag_cases bx Hbx) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
                 [simpl in Ex; discriminate Ex|destruct n; [discriminate H|rewrite step_generic_nullable in H; discriminate H]| |simpl in Ex; discriminate Ex].
             exact (IH _ _ s Hy Hbx I H).
      + rewrite (without_null_id x Hx Ex). cbn [without_null].
        rewrite (generic_target_bound_irrelevant (S n) gy _ ngy py (without_null by') by' x s (assignment_mutability_without_null by') Hx Ex).
        exact H.
    - rewrite (without_null_id x Hx); [exact H|].
      exact (accepted_not_nullable (S n) _ x s Hy Hx eq_refl H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Type arguments                                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma keeps_nv: forall n t a s w, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing w) -> w = s.
Proof.
    intros n t a s w Ht Ha H. pose proof (unify_free env wf n t a s s _ Ht Ha H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

Lemma gunify_type_arguments: forall n vt ot nt va oa na s, gfrag nt = true ->
    unify env (S n) (TypeArgument vt ot nt) (TypeArgument va oa na) (Ongoing s) =
    if ownership_is_assignable_to oa ot then compare_variances (unify env n) vt va nt na s else Some Failed.
Proof. intros n vt ot nt va oa na s Hnt. apply unify_type_arguments. exact (gfrag_not_variable nt Hnt). Qed.

(* Comparing variances never fails, where the comparisons it makes don't *)
Lemma compare_variances_never_fails: forall f vt va t a s, no_vars t = true -> no_vars a = true ->
    (match vt, va with
     | Model.invariant, Model.invariant => never_fails t a /\ never_fails a t
     | Model.invariant, _ => False
     | output, input => never_fails t top_type
     | output, _ => never_fails t a
     | input, output => never_fails bottom_type t
     | input, _ => never_fails a t
     end) ->
    compare_variances (unify env f) vt va t a s <> Some Failed.
Proof.
    intros f vt va t a s Ht Ha H. destruct vt, va; unfold compare_variances; try contradiction; try apply H.
    destruct H as [H1 H2]. destruct (free_result f t a s Ht Ha (H1 f s)) as [E|E]; rewrite E; [discriminate|apply H2].
Qed.

(* What comparing variances that succeeded says *)
Lemma compare_variances_facts: forall n vt va t a s, no_vars t = true -> no_vars a = true ->
    compare_variances (unify env n) vt va t a s = Some (Ongoing s) ->
    match vt, va with
    | Model.invariant, Model.invariant => unify env n t a (Ongoing s) = Some (Ongoing s) /\ unify env n a t (Ongoing s) = Some (Ongoing s)
    | Model.invariant, _ => False
    | output, input => unify env n t top_type (Ongoing s) = Some (Ongoing s)
    | output, _ => unify env n t a (Ongoing s) = Some (Ongoing s)
    | input, output => unify env n bottom_type t (Ongoing s) = Some (Ongoing s)
    | input, _ => unify env n a t (Ongoing s) = Some (Ongoing s)
    end.
Proof.
    intros n vt va t a s Ht Ha H. destruct vt, va; unfold compare_variances in H; try discriminate H; try exact H.
    apply both_ways in H; [exact H|apply unify_keeps_failure|intros w; apply (keeps_nv n t a s w Ht Ha)].
Qed.

(* A type argument that isn't loose stands in for nothing but its equals *)
Lemma gexact_symmetric: forall f x y s, argument_gfrag x = true -> argument_gfrag y = true ->
    unify env f y x (Ongoing s) = Some (Ongoing s) -> is_loose y = false -> unify env f x y (Ongoing s) = Some (Ongoing s).
Proof.
    intros [|f] [| | | |vx ox X| |] [| | | |vy oy Y| |] s Hx Hy H Hl; simpl in Hx, Hy; try discriminate.
    rewrite gunify_type_arguments in H |- * by assumption.
    destruct vy; simpl in Hl; try discriminate Hl.
    destruct (ownership_is_assignable_to ox oy) eqn:Ho; [|discriminate H].
    destruct vx; unfold compare_variances in H |- *; try discriminate H.
    assert (Hoo: ox = oy).
    { destruct ox as [| | |p], oy as [| | |q]; simpl in Hl, Ho; try discriminate; try reflexivity.
      apply param_eqb_eq in Ho. congruence. }
    subst oy. rewrite ownership_is_assignable_to_itself.
    apply both_ways in H; [|apply unify_keeps_failure|intros w; apply (keeps_nv f Y X s w); apply gfrag_no_vars; assumption].
    destruct H as [H1 H2]. rewrite H2. exact H1.
Qed.

(* A loose type argument can only stand in for a loose one *)
Lemma gloose_monotone: forall f x y s, argument_gfrag x = true -> argument_gfrag y = true ->
    unify env f y x (Ongoing s) = Some (Ongoing s) -> is_loose x = true -> is_loose y = true.
Proof.
    intros [|f] [| | | |vx ox X| |] [| | | |vy oy Y| |] s Hx Hy H Hl; simpl in Hx, Hy; try discriminate.
    rewrite gunify_type_arguments in H by assumption. destruct vy; [|reflexivity|reflexivity].
    destruct (ownership_is_assignable_to ox oy) eqn:Ho; [|discriminate H].
    destruct vx; unfold compare_variances in H; try discriminate H.
    destruct ox as [| | |p], oy as [| | |q]; simpl in Hl, Ho |- *; congruence.
Qed.

(* `exclusive Nothing` and what is below it is below everything *)
Lemma below_bottom_never_fails: forall n z s, gfrag z = true ->
    unify env n bottom_type z (Ongoing s) = Some (Ongoing s) -> forall t, gfrag t = true -> never_fails t z.
Proof.
    induction n as [|n IHn]; intros z s Hz H; [discriminate H|].
    assert (Hmz: assignment_mutability env z = exclusive).
    { pose proof (accepted_mutability (S n) bottom_type z s bottom_gfrag Hz H) as Hm.
      unfold bottom_type in Hm. cbn [assignment_mutability or_readonly] in Hm. rewrite (wf_nothing_is_not_const env wf) in Hm.
      apply mutability_subtype_of_exclusive, Hm. }
    assert (Hnz: is_nullable z = false) by exact (accepted_not_nullable (S n) bottom_type z s bottom_gfrag Hz eq_refl H).
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IHk] using lt_wf_ind. intros t -> Ht.
    apply never_fails_step. intros f s' E.
    destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> [Htn Ht']]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]].
    - destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> _]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]].
      + unfold bottom_type in H. rewrite unify_classes in H.
        destruct (base_type_is_subtype_of env cz nothing) eqn:Hb; [|discriminate H].
        apply (only_nothing_is_below_nothing env) in Hb. subst cz.
        rewrite unify_classes, (nothing_is_below_all env wf), Hmz, class_eqb_refl in E. cbn in E. discriminate E.
      + discriminate Hnz.
      + rewrite step_root_generic in E. unfold bottom_type in H. rewrite step_root_generic in H.
        exact (IHn bz s Hbz H _ Ht f s' E).
      + rewrite step_root_inter in E. unfold bottom_type in H. rewrite step_root_inter in H.
        destruct (flipped_some n _ zcs s s H) as [c [Hc Hu]].
        eapply (flipped_never_fails f _ zcs s' c Hc); [|exact E].
        exact (IHn c s (gfrag_component zcs c Hz Hc) Hu _ Ht f s').
    - assert (Hz': unify env f tn (without_null z) (Ongoing s') <> Some Failed).
      { rewrite (without_null_id z Hz Hnz). apply (IHk (esize tn)); [cbn [esize]; lia|reflexivity|exact Ht']. }
      destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> _]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]].
      + rewrite unify_nullable_class in E. exact (Hz' E).
      + discriminate Hnz.
      + rewrite step_nullable_generic in E. exact (Hz' E).
      + rewrite step_nullable_inter in E. exact (Hz' E).
    - destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> _]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]].
      + unfold bottom_type in H. rewrite unify_classes in H.
        destruct (base_type_is_subtype_of env cz nothing) eqn:Hb; [|discriminate H].
        apply (only_nothing_is_below_nothing env) in Hb. subst cz.
        rewrite step_generic_root, Hmz in E. cbn in E. discriminate E.
      + discriminate Hnz.
      + rewrite step_generic_generic in E. destruct (param_eqb pz pt).
        * simpl in Hmz, Hnz. rewrite Hmz, Hnz in E. discriminate E.
        * unfold bottom_type in H. rewrite step_root_generic in H. exact (IHn bz s Hbz H _ Ht f s' E).
      + rewrite step_generic_inter in E. unfold bottom_type in H. rewrite step_root_inter in H.
        destruct (flipped_some n _ zcs s s H) as [c [Hc Hu]].
        eapply (flipped_never_fails f _ zcs s' c Hc); [|exact E].
        exact (IHn c s (gfrag_component zcs c Hz Hc) Hu _ Ht f s').
    - destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> _]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]];
          [| discriminate Hnz | |];
          (apply (inter_target_never_fails tcs _ (gfrag_components_no_vars tcs Ht) (gfrag_no_vars _ Hz) I) with (f := S f) (s := s'); [|exact E]);
          intros c Hc; pose proof (esize_in tcs c Hc);
          exact (IHk (esize c) ltac:(cbn [esize]; lia) c eq_refl (gfrag_component tcs c Ht Hc)).
Qed.

(* `read Any` takes everything non-null *)
Lemma any_never_fails: forall m t, assignment_mutability env (RootResolved m any []) = readonly -> gfrag t = true -> is_nullable t = false ->
    never_fails (RootResolved m any []) t.
Proof.
    intros m t Hm. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Ht Hn.
    apply never_fails_step. intros f s E.
    destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> _]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]].
    - rewrite unify_classes in E.
      replace (base_type_is_subtype_of env ct any) with true in E
          by (unfold base_type_is_subtype_of; destruct (class_eqb any ct); [reflexivity|rewrite class_eqb_refl; reflexivity]).
      rewrite Hm, mutability_subtype_of_readonly in E.
      destruct (class_eqb ct nothing); [discriminate E|]. unfold unify_arguments in E. simpl in E. discriminate E.
    - discriminate Hn.
    - rewrite step_root_generic in E. exact (IH (esize bt) ltac:(cbn [esize]; lia) bt eq_refl Hbt Hn f s E).
    - rewrite step_root_inter in E. destruct (intersection_gfrag tcs Ht) as [Hne Hcs].
      destruct tcs as [|c0 tcs']; [contradiction|]. destruct (Hcs c0 (or_introl eq_refl)) as [Hc0 Hf0].
      eapply (flipped_never_fails f _ (c0 :: tcs') s c0 (or_introl eq_refl)); [|exact E].
      exact (IH (esize c0) ltac:(cbn [esize]; simpl; lia) c0 eq_refl Hf0 (component_not_nullable c0 Hc0) f s).
Qed.

Lemma takes_any_root: forall n mz cz zargs s, gfrag (RootResolved mz cz zargs) = true ->
    unify env n (RootResolved mz cz zargs) (RootResolved (Some readonly) any []) (Ongoing s) = Some (Ongoing s) ->
    forall t, gfrag t = true -> is_nullable t = false -> never_fails (RootResolved mz cz zargs) t.
Proof.
    intros [|n] mz cz zargs s Hz H t Ht Hn; [discriminate H|].
    rewrite unify_classes in H.
    destruct (base_type_is_subtype_of env any cz) eqn:Hb; [|discriminate H].
    assert (Hcz: cz = any).
    { apply base_type_is_subtype_of_iff in Hb. destruct Hb as [Hb|[Hb|[_ [Hb|Hb]]]]; auto; [discriminate Hb|].
      rewrite (wf_any_has_no_supertypes env wf) in Hb. contradiction. }
    subst cz. destruct (root_gfrag mz any zargs Hz) as [Hlz _]. rewrite (wf_any_has_no_type_parameters env wf) in Hlz.
    destruct zargs; [|discriminate Hlz].
    destruct (is_subtype_of _ _) eqn:Hm in H; [|discriminate H].
    apply any_never_fails; [|exact Ht|exact Hn].
    cbn [assignment_mutability or_readonly] in Hm |- *. rewrite (wf_any_is_not_const env wf) in Hm |- *.
    destruct mz as [[]|]; simpl in Hm |- *; try discriminate Hm; reflexivity.
Qed.

Lemma takes_any: forall n z s, gfrag z = true ->
    unify env n z (RootResolved (Some readonly) any []) (Ongoing s) = Some (Ongoing s) ->
    forall t, gfrag t = true -> is_nullable t = false -> never_fails z t.
Proof.
    induction n as [|n IH]; intros z s Hz H t Ht Hn; [discriminate H|].
    destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> [_ Hzn]]]|[[gz [ngz [pz [bz [-> _]]]]]|[zcs ->]]]].
    - exact (takes_any_root (S n) mz cz zargs s Hz H t Ht Hn).
    - rewrite unify_nullable_class in H. apply never_fails_step. intros f s' E.
      pose proof (IH zn s Hzn H t Ht Hn f s') as Hz'.
      destruct (gfrag_cases t Ht) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [rewrite unify_nullable_class in E|discriminate Hn|rewrite step_nullable_generic, (without_null_id _ Ht Hn) in E
          |rewrite step_nullable_inter in E]; exact (Hz' E).
    - rewrite step_generic_root in H. simpl in H. discriminate H.
    - apply inter_target_never_fails; [exact (gfrag_components_no_vars zcs Hz)|exact (gfrag_no_vars _ Ht)| |].
      + destruct (gfrag_cases t Ht) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; try exact I. discriminate Hn.
      + intros c Hc. destruct (intersection_gfrag zcs Hz) as [_ Hcs]. destruct (Hcs c Hc) as [Hcc Hcf].
        pose proof (inter_target_all n zcs (RootResolved (Some readonly) any []) s s (gfrag_components_no_vars zcs Hz) eq_refl I H c Hc) as Hu.
        destruct (gfrag_cases c Hcf) as [[mc [cc [cargs ->]]]|[[? [-> _]]|[[gc [ngc [pc [bc [-> _]]]]]|[? ->]]]];
            [| simpl in Hcc; discriminate Hcc | |simpl in Hcc; discriminate Hcc].
        * exact (takes_any_root n mc cc cargs s Hcf Hu t Ht Hn).
        * destruct n; [discriminate Hu|]. rewrite step_generic_root in Hu. simpl in Hu. discriminate Hu.
Qed.

(* `read Any?`, and what is above it, is above everything *)
Lemma above_top_never_fails: forall n z s, gfrag z = true ->
    unify env n z top_type (Ongoing s) = Some (Ongoing s) -> forall t, gfrag t = true -> never_fails z t.
Proof.
    intros [|n] z s Hz H t Ht; [discriminate H|].
    destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> [Hzn Hz']]]|[[gz [ngz [pz [bz [-> _]]]]]|[zcs ->]]]];
        unfold top_type in H.
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite unify_nullable_nullable in H. apply never_fails_step. intros f s' E.
      destruct (gfrag_cases t Ht) as [[mt [ct [targs ->]]]|[[tn [-> [Htn Ht']]]|[[gt [ngt [pt [bt [-> Hbt]]]]]|[tcs ->]]]].
      + rewrite unify_nullable_class in E. exact (takes_any n zn s Hz' H _ Ht eq_refl f s' E).
      + rewrite unify_nullable_nullable in E. exact (takes_any n zn s Hz' H tn Ht' (non_null_not_nullable tn Htn) f s' E).
      + rewrite step_nullable_generic in E.
        exact (takes_any n zn s Hz' H _ (gfrag_without_null _ Ht) (without_null_not_nullable _ Ht) f s' E).
      + rewrite step_nullable_inter in E. exact (takes_any n zn s Hz' H _ Ht eq_refl f s' E).
    - rewrite step_generic_nullable in H. discriminate H.
    - rewrite step_inter_nullable in H. discriminate H.
Qed.

Lemma arguments_never_fail: forall f (ts as': list EType) s,
    length ts = length as' -> forallb no_vars ts = true -> forallb no_vars as' = true ->
    Forall2 never_fails ts as' -> unify_arguments (unify env f) ts as' s <> Some Failed.
Proof.
    intros f ts as' s _ Hts Has H. unfold unify_arguments. revert Hts Has. induction H as [|t a ts as' Hta H IH]; intros Hts Has;
        simpl; [discriminate|].
    simpl in Hts, Has. apply andb_true_iff in Hts, Has.
    destruct (free_result f t a s (proj1 Hts) (proj1 Has) (Hta f s)) as [E|E]; rewrite E; [discriminate|].
    exact (IH (proj2 Hts) (proj2 Has)).
Qed.

(* A type argument in place of another as the assignee, by what comparing their variances takes *)
Lemma ta_lift: forall n vz oz Z vY vX o Yn Xn s, gfrag Z = true -> gfrag Yn = true -> gfrag Xn = true ->
    unify env (S n) (TypeArgument vz oz Z) (TypeArgument vY o Yn) (Ongoing s) = Some (Ongoing s) ->
    (compare_variances (unify env n) vz vY Z Yn s = Some (Ongoing s) ->
        match vz, vX with
        | Model.invariant, Model.invariant => never_fails Z Xn /\ never_fails Xn Z
        | Model.invariant, _ => False
        | output, input => never_fails Z top_type
        | output, _ => never_fails Z Xn
        | input, output => never_fails bottom_type Z
        | input, _ => never_fails Xn Z
        end) ->
    never_fails (TypeArgument vz oz Z) (TypeArgument vX o Xn).
Proof.
    intros n vz oz Z vY vX o Yn Xn s HZ HYn HXn H Hc.
    rewrite gunify_type_arguments in H by exact HZ. destruct (ownership_is_assignable_to o oz) eqn:Ho; [|discriminate H].
    apply never_fails_step. intros f s' E. rewrite gunify_type_arguments in E by exact HZ. rewrite Ho in E.
    exact (compare_variances_never_fails f vz vX Z Xn s' (gfrag_no_vars Z HZ) (gfrag_no_vars Xn HXn) (Hc H) E).
Qed.

(* ... and as the target *)
Lemma ta_lift_back: forall n vY o Yn Xn vz oz Z s, gfrag Yn = true -> gfrag Xn = true -> gfrag Z = true ->
    unify env (S n) (TypeArgument vY o Yn) (TypeArgument vz oz Z) (Ongoing s) = Some (Ongoing s) ->
    (compare_variances (unify env n) vY vz Yn Z s = Some (Ongoing s) ->
        match vY, vz with
        | Model.invariant, Model.invariant => never_fails Xn Z /\ never_fails Z Xn
        | Model.invariant, _ => False
        | output, input => never_fails Xn top_type
        | output, _ => never_fails Xn Z
        | input, output => never_fails bottom_type Xn
        | input, _ => never_fails Z Xn
        end) ->
    never_fails (TypeArgument vY o Xn) (TypeArgument vz oz Z).
Proof.
    intros n vY o Yn Xn vz oz Z s HYn HXn HZ H Hc.
    rewrite gunify_type_arguments in H by exact HYn. destruct (ownership_is_assignable_to oz o) eqn:Ho; [|discriminate H].
    apply never_fails_step. intros f s' E. rewrite gunify_type_arguments in E by exact HXn. rewrite Ho in E.
    exact (compare_variances_never_fails f vY vz Xn Z s' (gfrag_no_vars Xn HXn) (gfrag_no_vars Z HZ) (Hc H) E).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Lifting: instantiated templates, compared                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* x can stand in for y as an assignee wherever y can with fuel up to m *)
Definition glifts (frag: EType -> bool) (m: nat) (s: VariableStates) (x y: EType): Prop :=
    forall z m', m' <= m -> frag z = true -> refs_wf z -> unify env m' z y (Ongoing s) = Some (Ongoing s) -> never_fails z x.

(* ... and as a target *)
Definition glifts_back (frag: EType -> bool) (m: nat) (s: VariableStates) (x y: EType): Prop :=
    forall z m', m' <= m -> frag z = true -> refs_wf z -> unify env m' y z (Ongoing s) = Some (Ongoing s) -> never_fails x z.

Definition gleaves_lift (m: nat) (s: VariableStates) (xs ys: list EType): Prop :=
    Forall2 (fun x y => glifts argument_gfrag m s x y
        /\ (is_loose y = false -> is_loose x = false /\ glifts_back argument_gfrag m s x y)) xs ys.

Lemma gleaves_lift_weaken: forall m s xs ys, gleaves_lift (S m) s xs ys -> gleaves_lift m s xs ys.
Proof.
    intros m s xs ys H. eapply Forall2_impl; [|exact H]. intros x y [Hf Hb]. split.
    - intros z m' Hm. apply Hf. lia.
    - intros Hl. destruct (Hb Hl) as [Hx Hback]. split; [exact Hx|]. intros z m' Hm. apply Hback. lia.
Qed.

Lemma forall2_chain: forall {A: Type} (R1 R2 Q: A -> A -> Prop) xs ys zs,
    Forall2 R1 ys zs -> Forall2 R2 xs ys ->
    (forall x y z, In x xs -> In y ys -> In z zs -> R2 x y -> R1 y z -> Q z x) -> Forall2 Q zs xs.
Proof.
    intros A R1 R2 Q xs ys zs H1 H2. revert zs H1. induction H2 as [|x y xs ys Hxy H2 IH]; intros zs H1 Himpl;
        inversion H1 as [|y' z ys' zs' Hyz H1']; subst; constructor.
    - exact (Himpl x y z (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) Hxy Hyz).
    - apply IH; [exact H1'|]. intros x' y' z' Hx Hy Hz. exact (Himpl x' y' z' (or_intror Hx) (or_intror Hy) (or_intror Hz)).
Qed.

Lemma forall2_flip: forall {A B: Type} (R: A -> B -> Prop) l l', Forall2 R l l' -> Forall2 (fun b a => R a b) l' l.
Proof. intros A B R l l' H. induction H; constructor; assumption. Qed.

Lemma forall2_length: forall {A B: Type} (R: A -> B -> Prop) l l', Forall2 R l l' -> length l = length l'.
Proof. intros A B R l l' H. induction H; simpl; congruence. Qed.

(* The pairs of type arguments that a unification of class types, which succeeded, compared *)
Lemma gpairs: forall n targs aargs s, length targs = length aargs ->
    (forall t, In t targs -> argument_gfrag t = true) -> (forall a, In a aargs -> argument_gfrag a = true) ->
    unify_arguments (unify env n) targs aargs s = Some (Ongoing s) ->
    Forall2 (fun a t => unify env n t a (Ongoing s) = Some (Ongoing s)) aargs targs.
Proof.
    intros n targs aargs s Hl Ht Ha H. apply (pairwise_of_arguments env n targs aargs s Hl); [|exact H].
    intros t a w Hti Hai E. exact (keeps_nv n t a s w (argument_gfrag_no_vars t (Ht t Hti)) (argument_gfrag_no_vars a (Ha a Hai)) E).
Qed.

Lemma argument_gfrag_type_argument: forall a, argument_gfrag a = true -> is_type_argument a = true.
Proof. intros [| | | | | |] H; try discriminate H; reflexivity. Qed.

Lemma arguments_gfrag_no_vars: forall l, (forall a, In a l -> argument_gfrag a = true) -> forallb no_vars l = true.
Proof. intros l H. apply forallb_forall. intros a Ha. apply argument_gfrag_no_vars, H, Ha. Qed.

(* Where the type arguments xs of one reference to `sub` can stand in for those ys of another, the
   templates of `sub`, instantiated with xs, can stand in for those instantiated with ys; as targets
   too, where they aren't widened *)
Lemma glifting: forall s m sub xs ys,
    length xs = length (parameter_ids env sub) -> length ys = length (parameter_ids env sub) ->
    (forall x, In x xs -> argument_gfrag x = true) -> (forall y, In y ys -> argument_gfrag y = true) ->
    gleaves_lift m s xs ys ->
    (forall t, template_type env sub t = true ->
        glifts gfrag m s (instantiate env (bindings_of env sub xs) t) (instantiate env (bindings_of env sub ys) t)
        /\ (mentions_loosely_bound (bindings_of env sub ys) t = false ->
            glifts_back gfrag m s (instantiate env (bindings_of env sub xs) t) (instantiate env (bindings_of env sub ys) t)))
    /\ (forall a, template_argument env sub a = true ->
        glifts argument_gfrag m s (instantiate env (bindings_of env sub xs) a) (instantiate env (bindings_of env sub ys) a)
        /\ (mentions_loosely_bound (bindings_of env sub ys) a = false ->
            glifts_back argument_gfrag m s (instantiate env (bindings_of env sub xs) a) (instantiate env (bindings_of env sub ys) a))).
Proof.
    intros s m. induction m as [|m IH]; intros sub xs ys Hlx Hly Hxs Hys HL.
    { assert (H0: forall frag x y, glifts frag 0 s x y /\ glifts_back frag 0 s x y).
      { intros frag x y. split; intros z m' Hm' _ _ H; assert (m' = 0) by lia; subst m'; discriminate H. }
      split; intros t _; (split; [apply H0|intros _; apply H0]). }
    destruct (IH sub xs ys Hlx Hly Hxs Hys (gleaves_lift_weaken _ _ _ _ HL)) as [IHt IHa].
    assert (Hloose: Forall2 (fun x y => is_loose x = true -> is_loose y = true) xs ys).
    { eapply Forall2_impl; [|exact HL]. intros x y [_ Hb] Hx. destruct (is_loose y) eqn:E; [reflexivity|].
      destruct (Hb eq_refl) as [Hx' _]. congruence. }
    pose proof (mentions_monotone_with_arguments env wf sub xs ys Hlx Hly Hloose) as Hmono.
    assert (Hxs': forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; pose proof (Hxs x Hx) as E; destruct x; try discriminate E; reflexivity).
    assert (Hys': forall y, In y ys -> is_type_argument y = true)
        by (intros y Hy; pose proof (Hys y Hy) as E; destruct y; try discriminate E; reflexivity).
    set (bX := bindings_of env sub xs). set (bY := bindings_of env sub ys).
    assert (Hinst: forall a, template_argument env sub a = true ->
        argument_gfrag (instantiate env bX a) = true /\ argument_gfrag (instantiate env bY a) = true).
    { intros a Ha. split; [exact (proj2 (template_instances_gfrag sub xs Hlx Hxs _) a (le_n _) Ha)
                          |exact (proj2 (template_instances_gfrag sub ys Hly Hys _) a (le_n _) Ha)]. }
    assert (Hclass: forall m0 c targs, template_type env sub (RootResolved m0 c targs) = true ->
        glifts gfrag (S m) s (RootResolved m0 c (map (instantiate env bX) targs)) (RootResolved m0 c (map (instantiate env bY) targs))
        /\ (mentions_loosely_bound bY (RootResolved m0 c targs) = false ->
            glifts_back gfrag (S m) s (RootResolved m0 c (map (instantiate env bX) targs)) (RootResolved m0 c (map (instantiate env bY) targs)))).
    { intros m0 c targs Ht. destruct (root_template env sub m0 c targs Ht) as [Hlt Htargs].
      assert (HfX: forall a, In a (map (instantiate env bX) targs) -> argument_gfrag a = true)
          by (intros a Ha; apply in_map_iff in Ha; destruct Ha as [u [<- Hu]]; exact (proj1 (Hinst u (Htargs u Hu)))).
      assert (HfY: forall a, In a (map (instantiate env bY) targs) -> argument_gfrag a = true)
          by (intros a Ha; apply in_map_iff in Ha; destruct Ha as [u [<- Hu]]; exact (proj2 (Hinst u (Htargs u Hu)))).
      assert (HlX: length (map (instantiate env bX) targs) = length (parameter_ids env c)) by (rewrite length_map; exact Hlt).
      assert (HlY: length (map (instantiate env bY) targs) = length (parameter_ids env c)) by (rewrite length_map; exact Hlt).
      pose proof (IHt _ Ht) as [IHself IHself_back]. rewrite !instantiate_class in IHself, IHself_back.
      assert (HgX: gfrag (RootResolved m0 c (map (instantiate env bX) targs)) = true) by (apply make_root_gfrag; assumption).
      assert (HgY: gfrag (RootResolved m0 c (map (instantiate env bY) targs)) = true) by (apply make_root_gfrag; assumption).
      split.
      - intros z m' Hm' Hz Hrz H. destruct m' as [|m'']; [discriminate H|].
        apply never_fails_step. intros f s' E.
        destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> [_ Hzn]]]|[[gz [ngz [pz [bz [-> _]]]]]|[zcs ->]]]].
        + destruct (root_gfrag mz cz zargs Hz) as [Hlz Hzargs].
          rewrite unify_classes in H, E.
          rewrite (assignment_mutability_of_class env m0 c (map (instantiate env bX) targs) (map (instantiate env bY) targs)) in E.
          destruct (base_type_is_subtype_of env c cz) eqn:Hb; [|discriminate H].
          destruct (is_subtype_of _ _); [|discriminate H].
          destruct (class_eqb c nothing) eqn:Hcn; [discriminate E|].
          destruct (Class_eq_dec c cz) as [<-|Hne].
          * rewrite class_eqb_refl in H, E.
            pose proof (gpairs m'' zargs (map (instantiate env bY) targs) s ltac:(congruence) Hzargs HfY H) as Hp.
            apply (arguments_never_fail f zargs (map (instantiate env bX) targs) s' ltac:(congruence)
                (arguments_gfrag_no_vars _ Hzargs) (arguments_gfrag_no_vars _ HfX)); [|exact E].
            apply (forall2_chain (fun a t => unify env m'' t a (Ongoing s) = Some (Ongoing s))
                (fun x y => forall z, argument_gfrag z = true -> refs_wf z -> unify env m'' z y (Ongoing s) = Some (Ongoing s) -> never_fails z x)
                _ _ (map (instantiate env bY) targs) zargs Hp).
            -- apply Forall2_map_same. intros u Hu z' Hz' Hrz' E'. apply (proj1 (IHa u (Htargs u Hu)) z' m''); [lia|exact Hz'|exact Hrz'|exact E'].
            -- intros x y z' _ _ Hz' Hxy Hyz. exact (Hxy z' (Hzargs z' Hz') (refs_wf_root _ _ _ Hrz z' Hz') Hyz).
          * rewrite (class_eqb_false _ _ Hne) in H, E. rewrite !parameterized_supertype_arguments_eq in H, E.
            assert (Hcn': c <> nothing) by (apply class_eqb_false_neq; exact Hcn).
            destruct (wf_supertypes_are_templates env wf c cz Hne Hcn' Hb) as [Hlst Hst].
            assert (Hleaves: gleaves_lift m s (map (instantiate env bX) targs) (map (instantiate env bY) targs)).
            { apply Forall2_map_same. intros u Hu. split; [exact (proj1 (IHa u (Htargs u Hu)))|].
              intros Hly'. unfold bX, bY in *. rewrite (loose_instance env wf sub ys u Hly Hys' (Htargs u Hu)) in Hly'.
              apply orb_false_iff in Hly'. destruct Hly' as [Hlu Hmu]. split.
              - rewrite (loose_instance env wf sub xs u Hlx Hxs' (Htargs u Hu)), Hlu.
                destruct (mentions_loosely_bound (bindings_of env sub xs) u) eqn:Ex; [|reflexivity].
                pose proof (argument_depth_below m0 c targs u Hu).
                rewrite (proj2 (Hmono _) u (le_n _) (Htargs u Hu) Ex) in Hmu. discriminate Hmu.
              - exact (proj2 (IHa u (Htargs u Hu)) Hmu). }
            destruct (IH c _ _ HlX HlY HfX HfY Hleaves) as [_ IHc].
            assert (HnX: forall a, In a (map (instantiate env (bindings_of env c (map (instantiate env bX) targs))) (supertype_arguments env c cz)) -> argument_gfrag a = true).
            { intros a Ha. rewrite <- parameterized_supertype_arguments_eq in Ha.
              exact (proj2 (supertype_arguments_gfrag c cz _ Hne Hcn' Hb HlX HfX) a Ha). }
            assert (HnY: forall a, In a (map (instantiate env (bindings_of env c (map (instantiate env bY) targs))) (supertype_arguments env c cz)) -> argument_gfrag a = true).
            { intros a Ha. rewrite <- parameterized_supertype_arguments_eq in Ha.
              exact (proj2 (supertype_arguments_gfrag c cz _ Hne Hcn' Hb HlY HfY) a Ha). }
            pose proof (gpairs m'' zargs (map (instantiate env (bindings_of env c (map (instantiate env bY) targs))) (supertype_arguments env c cz)) s ltac:(rewrite length_map; congruence) Hzargs HnY H) as Hp.
            apply (arguments_never_fail f zargs (map (instantiate env (bindings_of env c (map (instantiate env bX) targs))) (supertype_arguments env c cz)) s' ltac:(rewrite length_map; congruence)
                (arguments_gfrag_no_vars _ Hzargs) (arguments_gfrag_no_vars _ HnX)); [|exact E].
            apply (forall2_chain (fun a t => unify env m'' t a (Ongoing s) = Some (Ongoing s))
                (fun x y => forall z, argument_gfrag z = true -> refs_wf z -> unify env m'' z y (Ongoing s) = Some (Ongoing s) -> never_fails z x)
                _ _ _ zargs Hp).
            -- apply Forall2_map_same. intros r Hr z' Hz' Hrz' E'. apply (proj1 (IHc r (Hst r Hr)) z' m''); [lia|exact Hz'|exact Hrz'|exact E'].
            -- intros x y z' _ _ Hz' Hxy Hyz. exact (Hxy z' (Hzargs z' Hz') (refs_wf_root _ _ _ Hrz z' Hz') Hyz).
        + rewrite unify_nullable_class in H, E. exact (IHself zn m'' ltac:(lia) Hzn Hrz H f s' E).
        + rewrite step_generic_root in H, E.
          change (is_non_nullable_nothing env (RootResolved m0 c (map (instantiate env bX) targs))) with (class_eqb c nothing) in E.
          change (is_non_nullable_nothing env (RootResolved m0 c (map (instantiate env bY) targs))) with (class_eqb c nothing) in H.
          rewrite (assignment_mutability_of_class env m0 c (map (instantiate env bX) targs) (map (instantiate env bY) targs)) in E.
          destruct (class_eqb c nothing && _) eqn:Eb in H; [|discriminate H]. rewrite Eb in E. discriminate E.
        + apply (inter_target_never_fails zcs _ (gfrag_components_no_vars zcs Hz) (gfrag_no_vars _ HgX) I) with (f := S f) (s := s');
              [|exact E].
          intros c' Hc'. apply (IHself c' m'' ltac:(lia) (gfrag_component zcs c' Hz Hc') (refs_wf_components zcs Hrz c' Hc')).
          exact (inter_target_all m'' zcs _ s s (gfrag_components_no_vars zcs Hz) (gfrag_no_vars _ HgY) I H c' Hc').
      - intros Hm z m' Hm' Hz Hrz H. destruct m' as [|m'']; [discriminate H|].
        rewrite mentions_class in Hm. pose proof (mentions_arguments_false _ targs Hm) as Hmu.
        apply never_fails_step. intros f s' E.
        destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> _]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]].
        + destruct (root_gfrag mz cz zargs Hz) as [Hlz Hzargs].
          rewrite unify_classes in H, E.
          rewrite (assignment_mutability_of_class env m0 c (map (instantiate env bX) targs) (map (instantiate env bY) targs)) in E.
          destruct (base_type_is_subtype_of env cz c) eqn:Hb; [|discriminate H].
          destruct (is_subtype_of _ _); [|discriminate H].
          destruct (class_eqb cz nothing) eqn:Hcn; [discriminate E|].
          destruct (Class_eq_dec cz c) as [->|Hne].
          * rewrite class_eqb_refl in H, E.
            pose proof (gpairs m'' (map (instantiate env bY) targs) zargs s ltac:(congruence) HfY Hzargs H) as Hp.
            apply (arguments_never_fail f (map (instantiate env bX) targs) zargs s' ltac:(congruence)
                (arguments_gfrag_no_vars _ HfX) (arguments_gfrag_no_vars _ Hzargs)); [|exact E].
            apply forall2_flip.
            apply (forall2_chain (fun y z => unify env m'' y z (Ongoing s) = Some (Ongoing s))
                (fun x y => forall z, argument_gfrag z = true -> refs_wf z -> unify env m'' y z (Ongoing s) = Some (Ongoing s) -> never_fails x z)
                (fun z x => never_fails x z) _ (map (instantiate env bY) targs) zargs (forall2_flip _ _ _ Hp)).
            -- apply Forall2_map_same. intros u Hu z' Hz' Hrz' E'.
               apply (proj2 (IHa u (Htargs u Hu)) (Hmu u Hu) z' m''); [lia|exact Hz'|exact Hrz'|exact E'].
            -- intros x y z' _ _ Hz' Hxy Hyz. exact (Hxy z' (Hzargs z' Hz') (refs_wf_root _ _ _ Hrz z' Hz') Hyz).
          * rewrite (class_eqb_false _ _ Hne) in H, E.
            destruct (supertype_arguments_gfrag cz c zargs Hne (class_eqb_false_neq _ _ Hcn) Hb Hlz Hzargs) as [Hln Hnorm].
            pose proof (supertype_arguments_refs_wf cz c zargs Hne (class_eqb_false_neq _ _ Hcn) Hb Hlz
                (fun z0 Hz0 => argument_gfrag_type_argument z0 (Hzargs z0 Hz0)) (refs_wf_root _ _ _ Hrz)) as Hrnorm.
            pose proof (gpairs m'' (map (instantiate env bY) targs) (parameterized_supertype_arguments env cz zargs c) s ltac:(congruence) HfY Hnorm H) as Hp.
            apply (arguments_never_fail f (map (instantiate env bX) targs) (parameterized_supertype_arguments env cz zargs c) s' ltac:(congruence)
                (arguments_gfrag_no_vars _ HfX) (arguments_gfrag_no_vars _ Hnorm)); [|exact E].
            apply forall2_flip.
            apply (forall2_chain (fun y z => unify env m'' y z (Ongoing s) = Some (Ongoing s))
                (fun x y => forall z, argument_gfrag z = true -> refs_wf z -> unify env m'' y z (Ongoing s) = Some (Ongoing s) -> never_fails x z)
                (fun z x => never_fails x z) _ (map (instantiate env bY) targs) _ (forall2_flip _ _ _ Hp)).
            -- apply Forall2_map_same. intros u Hu z' Hz' Hrz' E'.
               apply (proj2 (IHa u (Htargs u Hu)) (Hmu u Hu) z' m''); [lia|exact Hz'|exact Hrz'|exact E'].
            -- intros x y z' _ _ Hz' Hxy Hyz. exact (Hxy z' (Hnorm z' Hz') (Hrnorm z' Hz') Hyz).
        + rewrite unify_class_nullable in H. discriminate H.
        + rewrite step_root_generic in H, E. exact (IHself_back Hm bz m'' ltac:(lia) Hbz (proj1 Hrz) H f s' E).
        + rewrite step_root_inter in H, E. destruct (flipped_some m'' _ zcs s s H) as [c' [Hc' Hu]].
          eapply (flipped_never_fails f _ zcs s' c' Hc'); [|exact E].
          exact (IHself_back Hm c' m'' ltac:(lia) (gfrag_component zcs c' Hz Hc') (refs_wf_components zcs Hrz c' Hc') Hu f s'). }
    split.
    - intros t Ht. destruct (template_type_cases env sub t Ht) as [[m0 [c [targs ->]]]|[m0 [c [targs [-> Ht']]]]].
      + rewrite !instantiate_class. exact (Hclass m0 c targs Ht).
      + rewrite !instantiate_nullable_class, mentions_nullable.
        destruct (Hclass m0 c targs Ht') as [Hf Hb].
        split.
        * intros z m' Hm' Hz Hrz H. destruct m' as [|m'']; [discriminate H|].
          apply never_fails_step. intros f s' E.
          destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> [_ Hzn]]]|[[gz [ngz [pz [bz [-> _]]]]]|[zcs ->]]]].
          -- rewrite unify_class_nullable in H. discriminate H.
          -- rewrite unify_nullable_nullable in H, E. exact (Hf zn m'' ltac:(lia) Hzn Hrz H f s' E).
          -- rewrite step_generic_nullable in H. discriminate H.
          -- rewrite step_inter_nullable in H. discriminate H.
        * intros Hm z m' Hm' Hz Hrz H. destruct m' as [|m'']; [discriminate H|].
          apply never_fails_step. intros f s' E.
          destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> [_ Hzn]]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]].
          -- rewrite unify_nullable_class in H, E. exact (Hb Hm _ m'' ltac:(lia) Hz Hrz H f s' E).
          -- rewrite unify_nullable_nullable in H, E. exact (Hb Hm zn m'' ltac:(lia) Hzn Hrz H f s' E).
          -- rewrite step_nullable_generic in H, E. exact (Hb Hm _ m'' ltac:(lia) (gfrag_without_null _ Hz) (refs_wf_without_null _ Hz Hrz) H f s' E).
          -- rewrite step_nullable_inter in H, E. exact (Hb Hm _ m'' ltac:(lia) Hz Hrz H f s' E).
    - intros a Ha. destruct (template_kind env sub a Ha) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + (* a type parameter of sub: its type arguments, as they are *)
        destruct (nth_error_same_length _ xs i p (eq_sym Hlx) Hi) as [x Hx].
        destruct (nth_error_same_length _ ys i p (eq_sym Hly) Hi) as [y Hy].
        unfold bX, bY.
        rewrite (selects env wf sub xs p bp i x Hi Hx (Hxs' x (nth_error_In _ _ Hx))).
        rewrite (selects env wf sub ys p bp i y Hi Hy (Hys' y (nth_error_In _ _ Hy))).
        rewrite (mentions_parameter_template _ p bp y (lookup_parameter env wf sub ys i p y Hi Hy)).
        destruct (Forall2_nth_error _ xs ys i x y HL Hx Hy) as [Hf Hb]. split; [exact Hf|].
        intros Hl. exact (proj2 (Hb Hl)).
      + (* a class type of an explicit ownership *)
        destruct (IHt n Hn) as [IHn_f IHn_b].
        pose proof (template_shape env sub n Hn) as Hshape.
        pose proof (proj1 (template_instances_gfrag sub xs Hlx Hxs _) n (le_n _) Hn) as HfXn.
        pose proof (proj1 (template_instances_gfrag sub ys Hly Hys _) n (le_n _) Hn) as HfYn.
        change (mentions_loosely_bound bY (TypeArgument v o n)) with (mentions_loosely_bound bY n).
        rewrite (instantiate_template_argument env bX v o n Ho Hshape), (instantiate_template_argument env bY v o n Ho Hshape).
        set (Xn := instantiate env bX n) in *. set (Yn := instantiate env bY n) in *.
        assert (HnX: no_vars Xn = true) by (apply gfrag_no_vars; exact HfXn).
        assert (HnY: no_vars Yn = true) by (apply gfrag_no_vars; exact HfYn).
        destruct (mentions_loosely_bound bY n) eqn:Ey.
        * (* widened through ys *)
          split; [|intros Hm; discriminate Hm].
          intros z m' Hm' Hz Hrz H. destruct m' as [|m'']; [discriminate H|].
          destruct z as [| | | |vz oz Z| |]; simpl in Hz; try discriminate Hz.
          assert (HbotZ: forall t, gfrag t = true -> unify env m'' bottom_type Z (Ongoing s) = Some (Ongoing s) -> never_fails t Z)
              by (intros t' Ht' E0; exact (below_bottom_never_fails m'' Z s Hz E0 t' Ht')).
          destruct (mentions_loosely_bound bX n); destruct v; cbn iota in H |- *;
              eapply (ta_lift m'' vz oz Z _ _ o _ _ s Hz _ _ H); try first [exact HfYn|exact HfXn|exact bottom_gfrag].
          all: intros Hcmp; apply compare_variances_facts in Hcmp;
              try (apply gfrag_no_vars; first [exact Hz|exact HfYn|exact bottom_gfrag]);
              destruct vz; simpl in Hcmp |- *; try contradiction;
              first [ exact (gsuccess_never_fails _ _ _ _ Hz top_gfrag Hcmp)
                    | exact (gsuccess_never_fails _ _ _ _ bottom_gfrag Hz Hcmp)
                    | exact (HbotZ _ HfXn Hcmp)
                    | exact (IHn_f Z m'' ltac:(lia) Hz Hrz Hcmp) ].
        * (* not widened: neither through xs *)
          assert (Ex: mentions_loosely_bound bX n = false).
          { destruct (mentions_loosely_bound bX n) eqn:Ex; [|reflexivity].
            pose proof (proj1 (Hmono _) n (le_n _) Hn Ex) as Ey'. fold bY in Ey'. congruence. }
          rewrite Ex. split.
          -- intros z m' Hm' Hz Hrz H. destruct m' as [|m'']; [discriminate H|].
             destruct z as [| | | |vz oz Z| |]; simpl in Hz; try discriminate Hz.
             apply (ta_lift m'' vz oz Z v v o Yn Xn s Hz HfYn HfXn H). intros Hcmp.
             apply compare_variances_facts in Hcmp; [|apply gfrag_no_vars; exact Hz|exact HnY].
             destruct v, vz; simpl in Hcmp |- *; try contradiction;
                 first [ split; [exact (IHn_f Z m'' ltac:(lia) Hz Hrz (proj1 Hcmp))|exact (IHn_b Ey Z m'' ltac:(lia) Hz Hrz (proj2 Hcmp))]
                       | exact (gsuccess_never_fails _ _ _ _ Hz top_gfrag Hcmp)
                       | exact (gsuccess_never_fails _ _ _ _ bottom_gfrag Hz Hcmp)
                       | exact (IHn_f Z m'' ltac:(lia) Hz Hrz Hcmp)
                       | exact (IHn_b Ey Z m'' ltac:(lia) Hz Hrz Hcmp) ].
          -- intros _ z m' Hm' Hz Hrz H. destruct m' as [|m'']; [discriminate H|].
             destruct z as [| | | |vz oz Z| |]; simpl in Hz; try discriminate Hz.
             apply (ta_lift_back m'' v o Yn Xn vz oz Z s HfYn HfXn Hz H). intros Hcmp.
             apply compare_variances_facts in Hcmp; [|exact HnY|apply gfrag_no_vars; exact Hz].
             destruct v, vz; simpl in Hcmp |- *; try contradiction;
                 first [ split; [exact (IHn_b Ey Z m'' ltac:(lia) Hz Hrz (proj1 Hcmp))|exact (IHn_f Z m'' ltac:(lia) Hz Hrz (proj2 Hcmp))]
                       | exact (IHn_b Ey top_type m'' ltac:(lia) top_gfrag I Hcmp)
                       | exact (IHn_f bottom_type m'' ltac:(lia) bottom_gfrag I Hcmp)
                       | exact (IHn_f Z m'' ltac:(lia) Hz Hrz Hcmp)
                       | exact (IHn_b Ey Z m'' ltac:(lia) Hz Hrz Hcmp) ].
Unshelve. all: first [exact HfYn|exact HfXn|exact bottom_gfrag].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Transitivity                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma gtransitivity_with_arguments: forall N,
    (forall x y z n1 n2 s, n1 + n2 <= N ->
        gfrag x = true -> gfrag y = true -> gfrag z = true -> refs_wf x -> refs_wf y -> refs_wf z ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) -> unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        never_fails z x)
    /\ (forall x y z n1 n2 s, n1 + n2 <= N ->
        argument_gfrag x = true -> argument_gfrag y = true -> argument_gfrag z = true -> refs_wf x -> refs_wf y -> refs_wf z ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) -> unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        never_fails z x).
Proof.
    induction N as [|N [IHt IHa]].
    { split; intros x y z n1 n2 s HN _ _ _ _ _ _ H1 _; assert (n1 = 0) by lia; subst n1; discriminate H1. }
    split.
    - intros x y z n1 n2 s HN Hx Hy Hz Hrx Hry Hrz H1 H2.
      destruct n1 as [|n1']; [discriminate H1|]. destruct n2 as [|n2']; [discriminate H2|].
      pose proof H1 as H1o. pose proof H2 as H2o.
      destruct (gfrag_cases z Hz) as [[mz [cz [zargs ->]]]|[[zn [-> [Hzn Hz']]]|[[gz [ngz [pz [bz [-> Hbz]]]]]|[zcs ->]]]].
      + (* to a class type *)
        destruct (gfrag_cases y Hy) as [[my [cy [yargs ->]]]|[[yn [-> _]]|[[gy [ngy [py [by' [-> Hby]]]]]|[ycs ->]]]].
        * destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]].
          -- (* three class types *)
             destruct (root_gfrag mx cx xargs Hx) as [Hlx Hxargs].
             destruct (root_gfrag my cy yargs Hy) as [Hly Hyargs].
             destruct (root_gfrag mz cz zargs Hz) as [Hlz Hzargs].
             apply never_fails_step. intros f s' E.
             rewrite unify_classes in H1, H2, E.
             destruct (base_type_is_subtype_of env cx cy) eqn:Hb1; [|discriminate H1].
             destruct (base_type_is_subtype_of env cy cz) eqn:Hb2; [|discriminate H2].
             rewrite (base_type_is_subtype_of_trans env wf cx cy cz Hb1 Hb2) in E.
             destruct (is_subtype_of (assignment_mutability env (RootResolved mx cx xargs)) (assignment_mutability env (RootResolved my cy yargs))) eqn:Hm1;
                 [|discriminate H1].
             destruct (is_subtype_of (assignment_mutability env (RootResolved my cy yargs)) (assignment_mutability env (RootResolved mz cz zargs))) eqn:Hm2;
                 [|discriminate H2].
             rewrite (mutability_trans _ _ _ Hm1 Hm2) in E.
             destruct (class_eqb cx nothing) eqn:Hcx; [discriminate E|].
             destruct (class_eqb cy nothing) eqn:Hcy.
             { apply class_eqb_true in Hcy. subst cy. apply (only_nothing_is_below_nothing env) in Hb1. subst cx.
               rewrite class_eqb_refl in Hcx. discriminate Hcx. }
             apply class_eqb_false_neq in Hcx, Hcy.
             set (xs1 := if class_eqb cx cy then xargs else parameterized_supertype_arguments env cx xargs cy) in H1.
             assert (Hxs1: length xs1 = length (parameter_ids env cy) /\ (forall a, In a xs1 -> argument_gfrag a = true)
                 /\ (forall a, In a xs1 -> refs_wf a)).
             { unfold xs1. destruct (Class_eq_dec cx cy) as [<-|Hxy].
               - rewrite class_eqb_refl. split; [exact Hlx|]. split; [exact Hxargs|exact (refs_wf_root _ _ _ Hrx)].
               - rewrite (class_eqb_false _ _ Hxy). destruct (supertype_arguments_gfrag cx cy xargs Hxy Hcx Hb1 Hlx Hxargs) as [Hl1 Hf1].
                 split; [exact Hl1|]. split; [exact Hf1|].
                 exact (supertype_arguments_refs_wf cx cy xargs Hxy Hcx Hb1 Hlx
                     (fun a Ha => argument_gfrag_type_argument a (Hxargs a Ha)) (refs_wf_root _ _ _ Hrx)). }
             destruct Hxs1 as [Hlxs1 [Hfxs1 Hrxs1]].
             pose proof (gpairs n1' yargs xs1 s ltac:(congruence) Hyargs Hfxs1 H1) as Hpairs.
             destruct (Class_eq_dec cy cz) as [<-|Hyz].
             ++ (* y and z of the same class: x as a reference to the class of y, as it is *)
                rewrite class_eqb_refl in H2. fold xs1 in E.
                pose proof (gpairs n2' zargs yargs s ltac:(congruence) Hzargs Hyargs H2) as Hp2.
                apply (arguments_never_fail f zargs xs1 s' ltac:(congruence)
                    (arguments_gfrag_no_vars _ Hzargs) (arguments_gfrag_no_vars _ Hfxs1)); [|exact E].
                apply (forall2_chain (fun y' z' => unify env n2' z' y' (Ongoing s) = Some (Ongoing s))
                    (fun x' y' => unify env n1' y' x' (Ongoing s) = Some (Ongoing s)) never_fails xs1 yargs zargs Hp2 Hpairs).
                intros x' y' z' Hx' Hy' Hz' E1 E2.
                exact (IHa x' y' z' n1' n2' s ltac:(lia) (Hfxs1 x' Hx') (Hyargs y' Hy') (Hzargs z' Hz') (Hrxs1 x' Hx')
                    (refs_wf_root _ _ _ Hry y' Hy') (refs_wf_root _ _ _ Hrz z' Hz') E1 E2).
             ++ (* y of a subclass of z: lift what x as a reference to the class of y does into the supertype *)
                rewrite (class_eqb_false _ _ Hyz) in H2.
                destruct (Class_eq_dec cx cz) as [<-|Hxz].
                { exfalso. apply Hyz. symmetry. apply (wf_acyclic env wf); assumption. }
                rewrite (class_eqb_false _ _ Hxz) in E.
                replace (parameterized_supertype_arguments env cx xargs cz) with (parameterized_supertype_arguments env cy xs1 cz) in E.
                2: { unfold xs1. destruct (Class_eq_dec cx cy) as [<-|Hxy]; [rewrite class_eqb_refl; reflexivity|].
                     rewrite (class_eqb_false _ _ Hxy). symmetry. apply (parameterized_supertype_arguments_compose env wf); try assumption.
                     intros a Ha. apply argument_gfrag_type_argument, Hxargs, Ha. }
                destruct (wf_supertypes_are_templates env wf cy cz Hyz Hcy Hb2) as [Hlst Hst].
                assert (Hleaves: gleaves_lift n2' s xs1 yargs).
                { apply (Forall2_impl_in _ _ _ _ Hpairs). intros x' y' Hx' Hy' E1. split.
                  - intros z' m' Hm' Hz' Hrz' E2.
                    exact (IHa x' y' z' n1' m' s ltac:(lia) (Hfxs1 x' Hx') (Hyargs y' Hy') Hz' (Hrxs1 x' Hx')
                        (refs_wf_root _ _ _ Hry y' Hy') Hrz' E1 E2).
                  - intros Hl. split.
                    + destruct (is_loose x') eqn:Ex; [|reflexivity].
                      rewrite (gloose_monotone n1' x' y' s (Hfxs1 x' Hx') (Hyargs y' Hy') E1 Ex) in Hl. discriminate Hl.
                    + intros z' m' Hm' Hz' Hrz' E2.
                      exact (IHa z' y' x' m' n1' s ltac:(lia) Hz' (Hyargs y' Hy') (Hfxs1 x' Hx') Hrz'
                          (refs_wf_root _ _ _ Hry y' Hy') (Hrxs1 x' Hx') E2
                          (gexact_symmetric n1' x' y' s (Hfxs1 x' Hx') (Hyargs y' Hy') E1 Hl)). }
                destruct (glifting s n2' cy xs1 yargs Hlxs1 Hly Hfxs1 Hyargs Hleaves) as [_ Hlift].
                rewrite !parameterized_supertype_arguments_eq in H2, E.
                assert (HfX: forall a, In a (map (instantiate env (bindings_of env cy xs1)) (supertype_arguments env cy cz)) -> argument_gfrag a = true).
                { intros a Ha. rewrite <- parameterized_supertype_arguments_eq in Ha.
                  exact (proj2 (supertype_arguments_gfrag cy cz xs1 Hyz Hcy Hb2 Hlxs1 Hfxs1) a Ha). }
                assert (HfY: forall a, In a (map (instantiate env (bindings_of env cy yargs)) (supertype_arguments env cy cz)) -> argument_gfrag a = true).
                { intros a Ha. rewrite <- parameterized_supertype_arguments_eq in Ha.
                  exact (proj2 (supertype_arguments_gfrag cy cz yargs Hyz Hcy Hb2 Hly Hyargs) a Ha). }
                pose proof (gpairs n2' zargs (map (instantiate env (bindings_of env cy yargs)) (supertype_arguments env cy cz)) s
                    ltac:(rewrite length_map; congruence) Hzargs HfY H2) as Hp2.
                apply (arguments_never_fail f zargs (map (instantiate env (bindings_of env cy xs1)) (supertype_arguments env cy cz)) s'
                    ltac:(rewrite length_map; congruence) (arguments_gfrag_no_vars _ Hzargs) (arguments_gfrag_no_vars _ HfX)); [|exact E].
                apply (forall2_chain (fun y' z' => unify env n2' z' y' (Ongoing s) = Some (Ongoing s))
                    (fun x' y' => forall z', argument_gfrag z' = true -> refs_wf z' ->
                        unify env n2' z' y' (Ongoing s) = Some (Ongoing s) -> never_fails z' x')
                    never_fails _ _ zargs Hp2).
                ** apply Forall2_map_same. intros r Hr z' Hz' Hrz' E2. exact (proj1 (Hlift r (Hst r Hr)) z' n2' (le_n _) Hz' Hrz' E2).
                ** intros x' y' z' _ _ Hz' Hxy Hyz'. exact (Hxy z' (Hzargs z' Hz') (refs_wf_root _ _ _ Hrz z' Hz') Hyz').
          -- rewrite unify_class_nullable in H1. discriminate H1.
          -- rewrite step_root_generic in H1. apply never_fails_step. intros f s' E. rewrite step_root_generic in E.
             exact (IHt bx _ _ n1' (S n2') s ltac:(lia) Hbx Hy Hz (proj1 Hrx) Hry Hrz H1 H2o f s' E).
          -- rewrite step_root_inter in H1. destruct (flipped_some n1' _ xcs s s H1) as [c [Hc Hu]].
             apply never_fails_step. intros f s' E. rewrite step_root_inter in E.
             eapply (flipped_never_fails f _ xcs s' c Hc); [|exact E].
             exact (IHt c _ _ n1' (S n2') s ltac:(lia) (gfrag_component xcs c Hx Hc) Hy Hz (refs_wf_components xcs Hrx c Hc) Hry Hrz
                 Hu H2o f s').
        * rewrite unify_class_nullable in H2. discriminate H2.
        * (* through a type parameter *)
          rewrite step_root_generic in H2.
          destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]].
          -- rewrite step_generic_root in H1. destruct (_ && _) eqn:E1 in H1; [|discriminate H1].
             apply andb_true_iff in E1. destruct E1 as [Hn Hm]. simpl in Hn. apply class_eqb_true in Hn. subst cx.
             pose proof (accepted_mutability n2' _ _ s Hz Hby H2) as Hm2.
             apply never_fails_step. intros f s' E. rewrite unify_classes, (nothing_is_below_all env wf) in E.
             rewrite (mutability_trans _ _ _ Hm Hm2), class_eqb_refl in E. discriminate E.
          -- rewrite step_generic_nullable in H1. discriminate H1.
          -- rewrite step_generic_generic in H1. destruct (param_eqb px py) eqn:Ep.
             ++ apply param_eqb_eq in Ep. subst px. destruct (_ && _) eqn:E1 in H1; [|discriminate H1].
                apply andb_true_iff in E1. destruct E1 as [Hm Hn].
                assert (Hv: vle bx by').
                { apply (same_parameter_bounds gx ngx py bx gy ngy by' Hrx Hry Hm). intros E0. rewrite E0 in Hn. exact Hn. }
                pose proof (bounds_ordered n2' _ by' bx s Hz Hby Hbx Hv H2) as Hnf.
                apply never_fails_step. intros f s' E. rewrite step_root_generic in E. exact (Hnf f s' E).
             ++ apply never_fails_step. intros f s' E. rewrite step_root_generic in E.
                exact (IHt bx _ _ n1' (S n2') s ltac:(lia) Hbx Hy Hz (proj1 Hrx) Hry Hrz H1 H2o f s' E).
          -- rewrite step_generic_inter in H1. destruct (flipped_some n1' _ xcs s s H1) as [c [Hc Hu]].
             apply never_fails_step. intros f s' E. rewrite step_root_inter in E.
             eapply (flipped_never_fails f _ xcs s' c Hc); [|exact E].
             exact (IHt c _ _ n1' (S n2') s ltac:(lia) (gfrag_component xcs c Hx Hc) Hy Hz (refs_wf_components xcs Hrx c Hc) Hry Hrz
                 Hu H2o f s').
        * (* through an intersection: one of its components is below z *)
          rewrite step_root_inter in H2. destruct (flipped_some n2' _ ycs s s H2) as [c [Hc Hu2]].
          destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]];
              [| rewrite step_inter_nullable in H1; discriminate H1 | |];
              (pose proof (inter_target_all n1' ycs _ s s (gfrag_components_no_vars ycs Hy) (gfrag_no_vars _ Hx) I H1 c Hc) as Hu1);
              exact (IHt _ c _ n1' n2' s ltac:(lia) Hx (gfrag_component ycs c Hy Hc) Hz Hrx (refs_wf_components ycs Hry c Hc) Hrz Hu1 Hu2).
      + (* to a nullable type *)
        destruct (gfrag_cases y Hy) as [[my [cy [yargs ->]]]|[[yn [-> [Hyn Hy']]]|[[gy [ngy [py [by' [-> Hby]]]]]|[ycs ->]]]].
        3: idtac.
        2: { rewrite unify_nullable_nullable in H2.
             destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> [_ Hxn]]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]].
             - rewrite unify_nullable_class in H1. apply never_fails_step. intros f s' E. rewrite unify_nullable_class in E.
               exact (IHt _ yn zn n1' n2' s ltac:(lia) Hx Hy' Hz' Hrx Hry Hrz H1 H2 f s' E).
             - rewrite unify_nullable_nullable in H1. apply never_fails_step. intros f s' E. rewrite unify_nullable_nullable in E.
               exact (IHt xn yn zn n1' n2' s ltac:(lia) Hxn Hy' Hz' Hrx Hry Hrz H1 H2 f s' E).
             - rewrite step_nullable_generic in H1. apply never_fails_step. intros f s' E. rewrite step_nullable_generic in E.
               exact (IHt _ yn zn n1' n2' s ltac:(lia) (gfrag_without_null _ Hx) Hy' Hz' (refs_wf_without_null _ Hx Hrx) Hry Hrz
                   H1 H2 f s' E).
             - rewrite step_nullable_inter in H1. apply never_fails_step. intros f s' E. rewrite step_nullable_inter in E.
               exact (IHt _ yn zn n1' n2' s ltac:(lia) Hx Hy' Hz' Hrx Hry Hrz H1 H2 f s' E). }
        all: match type of H2 with unify env _ (Nullable ?zz) ?yy _ = _ =>
                 assert (H2': unify env n2' zz (without_null yy) (Ongoing s) = Some (Ongoing s)) by
                     (first [rewrite unify_nullable_class in H2 | rewrite step_nullable_generic in H2 | rewrite step_nullable_inter in H2];
                      exact H2) end.
        all: pose proof (accepted_without_null (S n1') _ x s Hy Hx I H1o) as H1'.
        all: pose proof (IHt _ _ zn (S n1') n2' s ltac:(lia) (gfrag_without_null _ Hx) (gfrag_without_null _ Hy) Hz'
                 (refs_wf_without_null _ Hx Hrx) (refs_wf_without_null _ Hy Hry) Hrz H1' H2') as Hnf.
        all: apply never_fails_step; intros f s' E.
        all: destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]];
                 [rewrite unify_nullable_class in E
                 | first [rewrite unify_class_nullable in H1o | rewrite step_generic_nullable in H1o | rewrite step_inter_nullable in H1o];
                   discriminate H1o
                 | rewrite step_nullable_generic in E
                 | rewrite step_nullable_inter in E]; exact (Hnf f s' E).
      + (* to a type parameter *)
        destruct (gfrag_cases y Hy) as [[my [cy [yargs ->]]]|[[yn [-> _]]|[[gy [ngy [py [by' [-> Hby]]]]]|[ycs ->]]]].
        * (* Nothing in between *)
          rewrite step_generic_root in H2. destruct (_ && _) eqn:E2 in H2; [|discriminate H2].
          apply andb_true_iff in E2. destruct E2 as [Hn2 Hm2]. simpl in Hn2. apply class_eqb_true in Hn2. subst cy.
          destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]].
          -- rewrite unify_classes in H1. destruct (base_type_is_subtype_of env cx nothing) eqn:Hb; [|discriminate H1].
             apply (only_nothing_is_below_nothing env) in Hb. subst cx.
             destruct (is_subtype_of _ _) eqn:Hm1 in H1; [|discriminate H1].
             apply never_fails_step. intros f s' E. rewrite step_generic_root in E.
             change (is_non_nullable_nothing env (RootResolved mx nothing xargs)) with (class_eqb nothing nothing) in E.
             rewrite class_eqb_refl, (mutability_trans _ _ _ Hm1 Hm2) in E. discriminate E.
          -- rewrite unify_class_nullable in H1. discriminate H1.
          -- rewrite step_root_generic in H1. apply never_fails_step. intros f s' E. rewrite step_generic_generic in E.
             destruct (param_eqb px pz).
             ++ pose proof (accepted_mutability n1' _ _ s Hy Hbx H1) as Hm1.
                pose proof (mutability_trans _ _ _ Hm1 Hm2) as Hm12.
                change (assignment_mutability env (Generic (mkGenericRef gz _ pz bz))) with (assignment_mutability env bz) in Hm12.
                rewrite Hm12 in E.
                rewrite (accepted_not_nullable n1' _ _ s Hy Hbx eq_refl H1) in E. discriminate E.
             ++ exact (IHt bx _ _ n1' (S n2') s ltac:(lia) Hbx Hy Hz (proj1 Hrx) Hry Hrz H1 H2o f s' E).
          -- rewrite step_root_inter in H1. destruct (flipped_some n1' _ xcs s s H1) as [c [Hc Hu]].
             apply never_fails_step. intros f s' E. rewrite step_generic_inter in E.
             eapply (flipped_never_fails f _ xcs s' c Hc); [|exact E].
             exact (IHt c _ _ n1' (S n2') s ltac:(lia) (gfrag_component xcs c Hx Hc) Hy Hz (refs_wf_components xcs Hrx c Hc) Hry Hrz
                 Hu H2o f s').
        * rewrite step_generic_nullable in H2. discriminate H2.
        * (* two type parameters *)
          rewrite step_generic_generic in H2. destruct (param_eqb py pz) eqn:Epz.
          -- (* the same *)
             apply param_eqb_eq in Epz. subst py.
             destruct (_ && _) eqn:E2 in H2; [|discriminate H2]. apply andb_true_iff in E2. destruct E2 as [Hm2 Hn2].
             destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]].
             ++ rewrite step_generic_root in H1. destruct (_ && _) eqn:E1 in H1; [|discriminate H1].
                apply andb_true_iff in E1. destruct E1 as [Hn1 Hm1].
                apply never_fails_step. intros f s' E. rewrite step_generic_root in E.
                change (assignment_mutability env (Generic (mkGenericRef gz _ pz bz))) with (assignment_mutability env bz) in E.
                rewrite Hn1, (mutability_trans _ _ _ Hm1 Hm2) in E. discriminate E.
             ++ rewrite step_generic_nullable in H1. discriminate H1.
             ++ rewrite step_generic_generic in H1. destruct (param_eqb px pz) eqn:Epx.
                ** destruct (_ && _) eqn:E1 in H1; [|discriminate H1]. apply andb_true_iff in E1. destruct E1 as [Hm1 Hn1].
                   apply never_fails_step. intros f s' E. rewrite step_generic_generic, Epx in E.
                   rewrite (mutability_trans _ _ _ Hm1 Hm2) in E.
                   destruct (is_nullable bx) eqn:Ebx; [|discriminate E].
                   simpl in Hn1. rewrite Hn1 in Hn2. simpl in Hn2. rewrite Hn2, orb_true_r in E. discriminate E.
                ** apply never_fails_step. intros f s' E. rewrite step_generic_generic, Epx in E.
                   exact (IHt bx _ _ n1' (S n2') s ltac:(lia) Hbx Hy Hz (proj1 Hrx) Hry Hrz H1 H2o f s' E).
             ++ rewrite step_generic_inter in H1. destruct (flipped_some n1' _ xcs s s H1) as [c [Hc Hu]].
                apply never_fails_step. intros f s' E. rewrite step_generic_inter in E.
                eapply (flipped_never_fails f _ xcs s' c Hc); [|exact E].
                exact (IHt c _ _ n1' (S n2') s ltac:(lia) (gfrag_component xcs c Hx Hc) Hy Hz (refs_wf_components xcs Hrx c Hc) Hry Hrz
                    Hu H2o f s').
          -- (* another one: through the bound of y *)
             destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]].
             ++ rewrite step_generic_root in H1. destruct (_ && _) eqn:E1 in H1; [|discriminate H1].
                apply andb_true_iff in E1. destruct E1 as [Hn1 Hm1].
                pose proof (accepted_mutability n2' _ _ s Hz Hby H2) as Hm2.
                apply never_fails_step. intros f s' E. rewrite step_generic_root in E.
                rewrite Hn1, (mutability_trans _ _ _ Hm1 Hm2) in E. discriminate E.
             ++ rewrite step_generic_nullable in H1. discriminate H1.
             ++ rewrite step_generic_generic in H1. destruct (param_eqb px py) eqn:Epy.
                ** (* x and y refer to the same: their bounds are in order *)
                   apply param_eqb_eq in Epy. subst px.
                   destruct (_ && _) eqn:E1 in H1; [|discriminate H1]. apply andb_true_iff in E1. destruct E1 as [Hm1 Hn1].
                   assert (Hv: vle bx by').
                   { apply (same_parameter_bounds gx ngx py bx gy ngy by' Hrx Hry Hm1). intros E0. rewrite E0 in Hn1. exact Hn1. }
                   pose proof (bounds_ordered n2' _ by' bx s Hz Hby Hbx Hv H2) as Hnf.
                   apply never_fails_step. intros f s' E. rewrite step_generic_generic, Epz in E. exact (Hnf f s' E).
                ** apply never_fails_step. intros f s' E. rewrite step_generic_generic in E. destruct (param_eqb px pz) eqn:Epx.
                   --- (* x refers to the type parameter of z *)
                       pose proof (accepted_mutability n1' _ _ s Hy Hbx H1) as Hm1.
                       pose proof (accepted_mutability n2' _ _ s Hz Hby H2) as Hm2.
                       pose proof (mutability_trans _ _ _ Hm1 Hm2) as Hm12.
                       change (assignment_mutability env (Generic (mkGenericRef gz _ pz bz))) with (assignment_mutability env bz) in Hm12.
                       rewrite Hm12 in E.
                       destruct (is_nullable bz) eqn:Ebz; [rewrite orb_true_r in E; discriminate E|].
                       rewrite (accepted_not_nullable n1' _ _ s Hy Hbx (accepted_not_nullable n2' _ _ s Hz Hby Ebz H2) H1) in E.
                       discriminate E.
                   --- exact (IHt bx _ _ n1' (S n2') s ltac:(lia) Hbx Hy Hz (proj1 Hrx) Hry Hrz H1 H2o f s' E).
             ++ rewrite step_generic_inter in H1. destruct (flipped_some n1' _ xcs s s H1) as [c [Hc Hu]].
                apply never_fails_step. intros f s' E. rewrite step_generic_inter in E.
                eapply (flipped_never_fails f _ xcs s' c Hc); [|exact E].
                exact (IHt c _ _ n1' (S n2') s ltac:(lia) (gfrag_component xcs c Hx Hc) Hy Hz (refs_wf_components xcs Hrx c Hc) Hry Hrz
                    Hu H2o f s').
        * rewrite step_generic_inter in H2. destruct (flipped_some n2' _ ycs s s H2) as [c [Hc Hu2]].
          destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]];
              [| rewrite step_inter_nullable in H1; discriminate H1 | |];
              (pose proof (inter_target_all n1' ycs _ s s (gfrag_components_no_vars ycs Hy) (gfrag_no_vars _ Hx) I H1 c Hc) as Hu1);
              exact (IHt _ c _ n1' n2' s ltac:(lia) Hx (gfrag_component ycs c Hy Hc) Hz Hrx (refs_wf_components ycs Hry c Hc) Hrz Hu1 Hu2).
      + (* to an intersection: each of its components *)
        destruct (gfrag_cases y Hy) as [[my [cy [yargs ->]]]|[[yn [-> _]]|[[gy [ngy [py [by' [-> Hby]]]]]|[ycs ->]]]];
            [| rewrite step_inter_nullable in H2; discriminate H2 | |];
            (destruct (gfrag_cases x Hx) as [[mx [cx [xargs ->]]]|[[xn [-> _]]|[[gx [ngx [px [bx [-> Hbx]]]]]|[xcs ->]]]];
                [| first [rewrite unify_class_nullable in H1 | rewrite step_generic_nullable in H1 | rewrite step_inter_nullable in H1];
                   discriminate H1 | |]);
            (apply inter_target_never_fails; [exact (gfrag_components_no_vars zcs Hz)|exact (gfrag_no_vars _ Hx)|exact I|]);
            intros c Hc;
            exact (IHt _ _ c (S n1') n2' s ltac:(lia) Hx Hy (gfrag_component zcs c Hz Hc) Hrx Hry (refs_wf_components zcs Hrz c Hc) H1o
                (inter_target_all n2' zcs _ s s (gfrag_components_no_vars zcs Hz) (gfrag_no_vars _ Hy) I H2o c Hc)).
    - intros [| | | |v1 o1 x| |] [| | | |v2 o2 y| |] [| | | |v3 o3 z| |] n1 n2 s HN Hx Hy Hz Hrx Hry Hrz H1 H2;
          simpl in Hx, Hy, Hz, Hrx, Hry, Hrz; try discriminate Hx; try discriminate Hy; try discriminate Hz.
      destruct n1 as [|n1']; [discriminate H1|]. destruct n2 as [|n2']; [discriminate H2|].
      rewrite gunify_type_arguments in H1, H2 by assumption.
      destruct (ownership_is_assignable_to o1 o2) eqn:Ho12; [|discriminate H1].
      destruct (ownership_is_assignable_to o2 o3) eqn:Ho23; [|discriminate H2].
      apply never_fails_step. intros f s' E. rewrite gunify_type_arguments in E by assumption.
      rewrite (ownership_trans o1 o2 o3 Ho12 Ho23) in E.
      apply compare_variances_facts in H1; [|apply gfrag_no_vars; assumption|apply gfrag_no_vars; assumption].
      apply compare_variances_facts in H2; [|apply gfrag_no_vars; assumption|apply gfrag_no_vars; assumption].
      apply (compare_variances_never_fails f v3 v1 z x s' (gfrag_no_vars z Hz) (gfrag_no_vars x Hx)); [|exact E].
      destruct v1, v2, v3; simpl in H1, H2 |- *; try contradiction;
          repeat match goal with H: _ /\ _ |- _ => destruct H end;
          first
            [ split;
                [ exact (IHt x y z n1' n2' s ltac:(lia) Hx Hy Hz Hrx Hry Hrz ltac:(assumption) ltac:(assumption))
                | exact (IHt z y x n2' n1' s ltac:(lia) Hz Hy Hx Hrz Hry Hrx ltac:(assumption) ltac:(assumption)) ]
            | exact (IHt x y z n1' n2' s ltac:(lia) Hx Hy Hz Hrx Hry Hrz ltac:(assumption) ltac:(assumption))
            | exact (IHt z y x n2' n1' s ltac:(lia) Hz Hy Hx Hrz Hry Hrx ltac:(assumption) ltac:(assumption))
            | exact (IHt top_type y z n1' n2' s ltac:(lia) top_gfrag Hy Hz I Hry Hrz ltac:(assumption) ltac:(assumption))
            | exact (IHt z y bottom_type n2' n1' s ltac:(lia) Hz Hy bottom_gfrag Hrz Hry I ltac:(assumption) ltac:(assumption))
            | exact (gsuccess_never_fails n2' z top_type s Hz top_gfrag ltac:(assumption))
            | exact (gsuccess_never_fails n2' bottom_type z s bottom_gfrag Hz ltac:(assumption))
            | exact (above_top_never_fails n2' z s Hz ltac:(assumption) x Hx)
            | exact (below_bottom_never_fails n2' z s Hz ltac:(assumption) x Hx) ].
Qed.

(*
 * Transitivity, with type parameters and intersections: where a type is assignable to another, and
 * that one to a third, unify never rejects assigning the first to the third. (Transitivity.v has the
 * same for class types, as the plain `is_assignable_to ... = Some true`.)
 *
 * Why "never rejects", rather than "accepts": where a value of an intersection type is assigned,
 * unify tries the components of the intersection in turn, and takes the first one that is assignable
 * (BoundIntersectionTypeReference.flippedUnify). To show that the value is assignable, every component
 * tried before that one has to come to an answer, too: unify has to terminate on those, on types that
 * may have nothing to do with the ones at hand. Whether unify always terminates is open. With
 * in-variant type arguments in the supertypes of classes, where the supertypes nest the type
 * parameters of the class ever deeper (`class N<Z> : C<in N<N<Z>>>`), nominal subtyping is known to be
 * undecidable in general (Kennedy and Pierce, On Decidability of Nominal Subtyping with Variance), and
 * an algorithm like unify may loop. The model counts the steps unify takes (its fuel), and running out
 * of them is no answer. So what this shows is: whenever unify comes to an answer, that answer is yes.
 * The frontend has no fuel; it terminates, with the answer, or it doesn't. Wherever it terminates on
 * the types at hand, this is transitivity as usual.
 *)
Theorem transitivity_never_fails: forall n1 n2 x y z,
    gfrag x = true -> gfrag y = true -> gfrag z = true -> refs_wf x -> refs_wf y -> refs_wf z ->
    is_assignable_to env n1 x y = Some true -> is_assignable_to env n2 y z = Some true ->
    forall f, is_assignable_to env f x z <> Some false.
Proof.
    intros n1 n2 x y z Hx Hy Hz Hrx Hry Hrz H1 H2 f E. unfold is_assignable_to, empty_unification in *.
    destruct (unify env n1 y x (Ongoing [])) as [[u1|]|] eqn:E1; try discriminate H1.
    destruct (unify env n2 z y (Ongoing [])) as [[u2|]|] eqn:E2; try discriminate H2.
    pose proof (gkeeps n1 y x [] u1 Hy Hx E1). subst u1.
    pose proof (gkeeps n2 z y [] u2 Hz Hy E2). subst u2.
    pose proof (proj1 (gtransitivity_with_arguments (n1 + n2)) x y z n1 n2 [] (le_n _) Hx Hy Hz Hrx Hry Hrz E1 E2 f []) as Hnf.
    destruct (unify env f z x (Ongoing [])) as [[u|]|]; simpl in E; try discriminate E. exact (Hnf eq_refl).
Qed.

End Generics.
