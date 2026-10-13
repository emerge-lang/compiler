From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Inference, with type variables bound by constraints                                              *)
(*                                                                                                *)
(* The type parameters of a function are inferred from the arguments of an invocation: unify       *)
(* records the constraints the arguments put on them, as a lower and an upper bound per type        *)
(* variable (plus_supertype_constraint, plus_subtype_constraint). Whatever unify accepts, it        *)
(* accepts with the type variables replaced by any types within their bounds (invocation_sound);   *)
(* and the types TypeUnification.getFinalValueFor picks are within them (final_values_satisfy).    *)
(* Together with capturing the type arguments of a receiver (Inference.v), that makes calling a    *)
(* member function with type parameters of its own sound (MemberCalls.v).                          *)
(*                                                                                                *)
(* Which types the variables are replaced with (xfrag), and which the bounds are (bfrag), is left   *)
(* open (inference_types): the class types of Transitivity.v (class_types_for_inference), or the  *)
(* type parameters and intersections of Fragment.v, as FinalValues.v has them.                     *)
(*                                                                                                *)
(* The bounds are combined with closestCommonSupertypeWith and intersect, which the model takes as  *)
(* given (Environment). They are assumed to be the bounds they are meant to be: what the closest   *)
(* common supertype of a bound and a type is assignable to, each of them is assignable to; and what *)
(* is assignable to the intersection of a bound and a type is assignable to each of them. Neither  *)
(* makes up type variables.                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)
(* Constraints                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

(*
 * What inference takes of the types the type variables are replaced with (xfrag), and of their
 * bounds (bfrag), which closestCommonSupertypeWith and intersect make
 *)
Record inference_types (env: Environment) (xfrag bfrag: EType -> Prop): Prop := {
    (* the types variables are replaced with: of the fragment of Fragment.v, those of the fragment of
       Transitivity.v among them, and each assignable to itself *)
    it_xfrag_gfrag: forall x, xfrag x -> gfrag env x = true;
    it_in_fragment_xfrag: forall x, in_fragment env x = true -> xfrag x;
    it_xfrag_reflexive: forall x, xfrag x -> exists n, unify env n x x (Ongoing []) = Some (Ongoing []);
    (* the bounds: the types of the fragment of Transitivity.v among them, and their intersections and
       closest common supertypes with those *)
    it_in_fragment_bfrag: forall x, in_fragment env x = true -> bfrag x;
    it_intersect_bfrag: forall a b, bfrag a -> in_fragment env b = true -> bfrag (intersect env a b);
    it_supertype_bfrag: forall a b, bfrag a -> in_fragment env b = true -> bfrag (closest_common_supertype_with env a b);
    (* what is assignable to the intersection of a bound and a type is assignable to each of them *)
    it_intersect_is_below: forall a b x n, bfrag a -> in_fragment env b = true -> xfrag x ->
        unify env n (intersect env a b) x (Ongoing []) = Some (Ongoing []) ->
        (exists n', unify env n' a x (Ongoing []) = Some (Ongoing [])) /\ (exists n', unify env n' b x (Ongoing []) = Some (Ongoing []));
    (* what the closest common supertype of a bound and a type is assignable to, each of them is assignable to *)
    it_supertype_is_above: forall a b x n, bfrag a -> in_fragment env b = true -> xfrag x ->
        unify env n x (closest_common_supertype_with env a b) (Ongoing []) = Some (Ongoing []) ->
        (exists n', unify env n' x a (Ongoing []) = Some (Ongoing [])) /\ (exists n', unify env n' x b (Ongoing []) = Some (Ongoing []));
    (* neither makes up type variables *)
    it_intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true;
    it_supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
        no_vars (closest_common_supertype_with env a b) = true;
}.

Section Constraints.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let supertypes_mention_nothing_as_bottom := wf_supertypes_mention_nothing_as_bottom env wf.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

Variables xfrag bfrag: EType -> Prop.
Hypothesis types: inference_types env xfrag bfrag.
Let xfrag_gfrag := it_xfrag_gfrag env xfrag bfrag types.
Let in_fragment_xfrag := it_in_fragment_xfrag env xfrag bfrag types.
Let xfrag_reflexive := it_xfrag_reflexive env xfrag bfrag types.
Let in_fragment_bfrag := it_in_fragment_bfrag env xfrag bfrag types.
Let intersect_bfrag := it_intersect_bfrag env xfrag bfrag types.
Let supertype_bfrag := it_supertype_bfrag env xfrag bfrag types.
Let intersect_is_below := it_intersect_is_below env xfrag bfrag types.
Let supertype_is_above := it_supertype_is_above env xfrag bfrag types.
Let intersect_no_vars := it_intersect_no_vars env xfrag bfrag types.
Let supertype_no_vars := it_supertype_no_vars env xfrag bfrag types.

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

(* unify on types without type variables, at other variable states *)
Lemma at_states: forall n t a s s', no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s').
Proof. intros n t a s s' Ht Ha H. exact (unify_free env wf n t a s s' _ Ht Ha H). Qed.

Lemma keeps_free: forall n t a s u, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s /\ unify env n t a (Ongoing []) = Some (Ongoing []).
Proof.
    intros n t a s u Ht Ha H. split.
    - pose proof (unify_free env wf n t a s s _ Ht Ha H) as E. rewrite H in E.
      injection E as ->. reflexivity.
    - exact (unify_free env wf n t a s [] _ Ht Ha H).
Qed.

(* A type the variable is replaced with, within what the state of the variable allows: the types the
   type argument it is bound to exactly stands for, or the types between its bounds *)
Definition fits (st: VariableState) (o: Ownership) (x: EType): Prop :=
    if is_exact st then
        exists vb ob X K, upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
            /\ in_fragment env X = true /\ in_fragment env x = true
            /\ unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing []) = Some (Ongoing [])
    else (exists K, unify env K x (lower_bound st) (Ongoing []) = Some (Ongoing []))
        /\ (exists K, unify env K (upper_bound st) x (Ongoing []) = Some (Ongoing [])).

Definition satisfies (b: Bindings) (s: VariableStates): Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        xfrag x /\ exists st, lookup_state s p = Some st /\ fits st o x.

(* The variable states unify works with: the bounds without type variables, the upper bound above the
   lower one where the variable isn't bound exactly, and no variable to capture *)
(* What is below the upper bound of a variable is below its declared one *)
Definition below_static (st: VariableState): Prop :=
    forall x f, xfrag x -> unify env f (upper_bound st) x (Ongoing []) = Some (Ongoing []) ->
        exists f', unify env f' (static_upper_bound st) x (Ongoing []) = Some (Ongoing []).

Definition wf_states (s: VariableStates): Prop :=
    forall p st, lookup_state s p = Some st ->
        no_vars (upper_bound st) = true /\ no_vars (lower_bound st) = true
        /\ (is_exact st = false -> is_capturable st = false
            /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
            /\ below_static st /\ bfrag (upper_bound st) /\ bfrag (lower_bound st)).

Lemma wf_set_state: forall s p st, wf_states s ->
    no_vars (upper_bound st) = true -> no_vars (lower_bound st) = true ->
    (is_exact st = false -> is_capturable st = false
        /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
        /\ below_static st /\ bfrag (upper_bound st) /\ bfrag (lower_bound st)) ->
    wf_states (set_state s p st).
Proof.
    intros s p st Hs Hu Hl He q st' Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq. injection Hq as <-. auto.
    - rewrite lookup_set_other in Hq by exact Hne. exact (Hs q st' Hq).
Qed.

Lemma satisfies_set_state: forall s p st st', lookup_state s p = Some st ->
    (forall o x, xfrag x -> fits st' o x -> fits st o x) ->
    forall b, satisfies b (set_state s p st') -> satisfies b s.
Proof.
    intros s p st st' Hl Hf b Hb q o x Hq. destruct (Hb q o x Hq) as [Hx [st'' [Hq' Hfit]]]. split; [exact Hx|].
    destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq'. injection Hq' as <-. exists st. split; [exact Hl|exact (Hf o x Hx Hfit)].
    - rewrite lookup_set_other in Hq' by exact Hne. exists st''. auto.
Qed.

Lemma not_capturable: forall s t, wf_states s -> capturable t s = None.
Proof.
    intros s [| | | | |[gm nn p bnd]|] Hs; try reflexivity. simpl.
    destruct (lookup_state s p) as [st|] eqn:E; [|reflexivity].
    destruct (is_exact st) eqn:Ee; [rewrite andb_false_r; reflexivity|].
    destruct (Hs p st E) as [_ [_ He]]. rewrite (proj1 (He Ee)). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A type variable, assigned to and assigned                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* What the variable takes: above the lower bound, which is above it *)
Lemma target_leaf: forall n p bnd st A s s', wf_states s -> lookup_state s p = Some st -> afrag env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f x A (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n p bnd st A s s' Hs Hl HAf H. destruct (Hs p st Hl) as [Hnu [Hnl He]].
    destruct (afrag_parts env A HAf) as [HA HAn].
    pose proof (in_fragment_no_vars A HA) as HnA.
    assert (H': plus_supertype_constraint env (unify env n) s p A = Some (Ongoing s')).
    { rewrite unify_step_once in H. destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
          unfold unify_step, unify_type_variable in H; [exact H|]. destruct (is_nullable _); [exact H|discriminate H]. }
    unfold plus_supertype_constraint in H'. rewrite Hl in H'. destruct (is_exact st) eqn:Ee.
    - (* bound exactly: its binding takes A *)
      destruct (keeps_free n _ A s s' Hnl HnA H') as [-> H0]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold fits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [HxF Hc]]]]]]]]. rewrite Hlo in H0.
      destruct (write_leaf env wf K [] n vb ob X o x A [] HX HxF HAf Hc H0) as [_ Hw]. exists (n + K + 1). exact Hw.
    - (* between bounds: the lower bound becomes the closest common supertype with A *)
      cbn zeta in H'.
      pose proof (supertype_no_vars _ _ Hnl HnA) as Hnn.
      destruct (unify env n (upper_bound st) (closest_common_supertype_with env (lower_bound st) A) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
      destruct (keeps_free n _ _ s ns Hnu Hnn E) as [-> H0].
      destruct (He eq_refl) as [Hcap [_ [Hbs [Hbu Hbl]]]].
      split; [|split].
      + apply wf_set_state; [exact Hs|exact Hnu|exact Hnn|]. intros _. split; [exact Hcap|]. split; [exists n; exact H0|].
        split; [exact Hbs|]. split; [exact Hbu|exact (supertype_bfrag _ _ Hbl HA)].
      + apply (satisfies_set_state s p st _ Hl). intros o x Hx Hfit. unfold fits in Hfit |- *. rewrite Ee.
        cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [[K1 E1] [K2 E2]]. split; [|exists K2; exact E2].
        exact (proj1 (supertype_is_above _ _ x K1 Hbl HA Hx E1)).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold fits in Hfit. cbn [is_exact lower_bound] in Hfit.
        destruct Hfit as [[K1 E1] _]. exact (proj2 (supertype_is_above _ _ x K1 Hbl HA Hx E1)).
Qed.

(* What the variable is assigned to: below the upper bound, which is below it *)
Lemma assignee_leaf: forall n p bnd st A s s', wf_states s -> lookup_state s p = Some st -> in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f A x (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n p bnd st A s s' Hs Hl HA H. destruct (Hs p st Hl) as [Hnu [Hnl He]].
    pose proof (in_fragment_no_vars A HA) as HnA.
    assert (H': plus_subtype_constraint env (unify env n) s p A = Some (Ongoing s')).
    { rewrite unify_step_once in H. destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
          exact H. }
    unfold plus_subtype_constraint in H'. rewrite Hl in H'. destruct (is_exact st) eqn:Ee.
    - (* bound exactly: A takes what its binding gives *)
      destruct (keeps_free n A _ s s' HnA Hnu H') as [-> H0]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold fits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [HxF Hc]]]]]]]]. rewrite Hu in H0.
      destruct (read_leaf env wf K [] n vb ob X o x A [] HX HxF HA Hc H0) as [_ Hr]. exists (n + K + 1). exact Hr.
    - (* between bounds: the upper bound becomes the intersection with A *)
      cbn zeta in H'.
      pose proof (intersect_no_vars _ _ Hnu HnA) as Hnn.
      destruct (is_non_nullable_nothing env (intersect env (upper_bound st) A)); [discriminate H'|].
      destruct (unify env n (intersect env (upper_bound st) A) (lower_bound st) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
      destruct (keeps_free n _ _ s ns Hnn Hnl E) as [-> H0].
      destruct (He eq_refl) as [Hcap [_ [Hbs [Hbu Hbl]]]].
      split; [|split].
      + apply wf_set_state; [exact Hs|exact Hnn|exact Hnl|]. intros _. split; [exact Hcap|]. split; [exists n; exact H0|].
        split; [|split; [exact (intersect_bfrag _ _ Hbu HA)|exact Hbl]].
        intros x f Hx Ex. destruct (intersect_is_below _ _ x f Hbu HA Hx Ex) as [[f1 E1] _]. exact (Hbs x f1 Hx E1).
      + apply (satisfies_set_state s p st _ Hl). intros o x Hx Hfit. unfold fits in Hfit |- *. rewrite Ee.
        cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [[K1 E1] [K2 E2]]. split; [exists K1; exact E1|].
        exact (proj1 (intersect_is_below _ _ x K2 Hbu HA Hx E2)).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold fits in Hfit. cbn [is_exact upper_bound] in Hfit.
        destruct Hfit as [_ [K2 E2]]. exact (proj2 (intersect_is_below _ _ x K2 Hbu HA Hx E2)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Pairs of type arguments                                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma combine_map_in: forall (f g: EType -> EType) (l1 l2: list EType) x y,
    In (x, y) (combine (map f l1) (map g l2)) -> exists t a, In (t, a) (combine l1 l2) /\ x = f t /\ y = g a.
Proof.
    intros f g l1. induction l1 as [|t l1 IH]; intros [|a l2] x y H; simpl in H; try destruct H.
    - injection H as <- <-. exists t, a. split; [left; reflexivity|split; reflexivity].
    - destruct (IH l2 x y H) as [t' [a' [Hin [-> ->]]]]. exists t', a'. split; [right; exact Hin|split; reflexivity].
Qed.

Lemma uniform_fuel: forall (l: list (EType * EType)) (Q: nat -> EType * EType -> Prop),
    (forall f f' x, f <= f' -> Q f x -> Q f' x) -> (forall x, In x l -> exists f, Q f x) ->
    exists f, forall x, In x l -> Q f x.
Proof.
    intros l Q Hm. induction l as [|x l IH]; intros H; [exists 0; intros _ []|].
    destruct (H x (or_introl eq_refl)) as [f1 H1]. destruct (IH (fun y Hy => H y (or_intror Hy))) as [f2 H2].
    exists (max f1 f2). intros y [<-|Hy]; [apply (Hm f1); [lia|exact H1]|apply (Hm f2); [lia|exact (H2 y Hy)]].
Qed.

Lemma fold_from_pairs: forall f (l: list (EType * EType)),
    (forall t a, In (t, a) l -> unify env f t a (Ongoing []) = Some (Ongoing [])) ->
    fold_unify (fun inner '(t, a) => unify env f t a inner) l (Ongoing []) = Some (Ongoing []).
Proof.
    intros f l H. induction l as [|[t a] l IH]; [reflexivity|]. simpl. rewrite (H t a (or_introl eq_refl)).
    apply IH. intros t' a' Hin. apply H. right. exact Hin.
Qed.

Lemma fold_chain: forall n (l: list (EType * EType)) s s',
    (forall t a, In (t, a) l -> forall s0 s0', wf_states s0 -> unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0)) ->
    wf_states s -> fold_unify (fun inner '(t, a) => unify env n t a inner) l (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall t a, In (t, a) l -> exists s0 s0', wf_states s0 /\ unify env n t a (Ongoing s0) = Some (Ongoing s0')
        /\ (forall b, satisfies b s' -> satisfies b s0')).
Proof.
    intros n l. induction l as [|[t a] l IH]; intros s s' Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros t a [].
    - destruct (unify env n t a (Ongoing s)) as [[s1|]|] eqn:E; [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      destruct (Hstep t a (or_introl eq_refl) s s1 Hs E) as [Hs1 Hext1].
      destruct (IH s1 s' (fun t' a' Hin => Hstep t' a' (or_intror Hin)) Hs1 H) as [Hs' [Hext Hpairs]].
      split; [exact Hs'|]. split; [intros b Hb; apply Hext1, Hext, Hb|].
      intros t' a' [E'|Hin].
      + injection E' as <- <-. exists s, s1. split; [exact Hs|]. split; [exact E|exact Hext].
      + exact (Hpairs t' a' Hin).
Qed.

Lemma state_of_target: forall n p bnd A s r, in_fragment env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing r) -> exists st, lookup_state s p = Some st.
Proof.
    intros n p bnd A s r HA H. destruct (lookup_state s p) as [st|] eqn:E; [eauto|exfalso].
    rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_type_variable, plus_supertype_constraint in H; [rewrite E in H; discriminate H|].
    destruct (is_nullable _); [rewrite E in H|]; discriminate H.
Qed.

Lemma state_of_assignee: forall n p bnd A s r, in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing r) -> exists st, lookup_state s p = Some st.
Proof.
    intros n p bnd A s r HA H. destruct (lookup_state s p) as [st|] eqn:E; [eauto|exfalso].
    rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_root_resolved, unify_nullable, type_variable_flipped_unify, plus_subtype_constraint in H;
        rewrite E in H; discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Soundness                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Section Main.

(* The types the type variables are replaced with, and the fuel with which they are within the
   bounds of the type parameters *)
Variable b: Bindings.
Variable K: nat.

Lemma constraints_with_arguments: forall n,
    (forall P A s s', ifrag env P = true -> afrag env A = true -> closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', ifrag env P = true -> afrag env A = true -> closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f A (inst env b P) (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f (instantiate env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f A (instantiate env b P) (Ongoing []) = Some (Ongoing []))).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    (* the parts of the types of the arguments *)
    assert (Hargs: forall ma ca aargs, in_fragment env (RootResolved ma ca aargs) = true ->
        nothing_is_bottom (RootResolved ma ca aargs) = true -> closed (RootResolved ma ca aargs) = true ->
        length aargs = length (parameter_ids env ca) /\ forall a, In a aargs ->
            argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
    { intros ma ca aargs Hf Hn Hc. destruct (root_in_fragment env ma ca aargs Hf) as [Hl Ha]. split; [exact Hl|].
      intros a Hin. split; [exact (Ha a Hin)|]. split; [exact (proj2 (nothing_is_bottom_root ma ca aargs Hn) a Hin)|].
      exact (closed_parts ma ca aargs Hc a Hin). }
    assert (Hnorm: forall ca ct aargs, ca <> ct -> ca <> nothing -> base_type_is_subtype_of env ca ct = true ->
        length aargs = length (parameter_ids env ca) ->
        (forall a, In a aargs -> argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true) ->
        forall a, In a (parameterized_supertype_arguments env ca aargs ct) ->
            argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
    { intros ca ct aargs Hne Hcn Hbase Hl Ha a Hin.
      assert (Hta: forall y, In y aargs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Ha, Hy).
      destruct (supertype_arguments_to_generic env wf ca ct aargs Hne Hcn Hbase Hl Hta)
          as [_ [_ [Hnb Hcl]]].
      destruct (supertype_arguments_in_fragment env wf ca ct aargs Hne Hcn Hbase Hl (fun y Hy => proj1 (Ha y Hy))) as [_ Hf].
      split; [exact (Hf a Hin)|]. split; [apply Hnb; [intros y Hy; apply Ha, Hy|exact Hin]|apply Hcl; [intros y Hy; apply Ha, Hy|exact Hin]]. }
    (* the pairs of type arguments of two class types *)
    assert (Hpairs: forall targs aargs s s' (inst_t inst_a: EType -> EType),
        (forall t a, In (t, a) (combine targs aargs) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (satisfies b s0' -> exists f, unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing []))) ->
        wf_states s -> fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, fold_unify (fun inner '(t, a) => unify env f t a inner)
            (combine (map inst_t targs) (map inst_a aargs)) (Ongoing []) = Some (Ongoing []))).
    { intros targs aargs s s' inst_t inst_a Hp Hs H.
      destruct (fold_chain n _ s s' (fun t a Hin s0 s0' Hs0 E => let H' := Hp t a Hin s0 s0' Hs0 E in conj (proj1 H') (proj1 (proj2 H')))
          Hs H) as [Hs' [Hext Hall]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hb.
      destruct (uniform_fuel (combine targs aargs) (fun f '(t, a) => unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing [])))
          as [f Hf].
      - intros f f' [t a] Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E).
      - intros [t a] Hin. destruct (Hall t a Hin) as [s0 [s0' [Hs0 [E Hx]]]].
        exact (proj2 (proj2 (Hp t a Hin s0 s0' Hs0 E)) (Hx b Hb)).
      - exists f. apply fold_from_pairs. intros x y Hin. destruct (combine_map_in inst_t inst_a _ _ x y Hin) as [t [a [Hin' [-> ->]]]].
        exact (Hf (t, a) Hin'). }
    split; [|split; [|split]].
    - (* a type with type variables as the target *)
      intros P A s s' HP HA HcA Hb Hs H. destruct (afrag_parts env A HA) as [HA' HAn].
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (satisfies b s' -> exists f, unify env f (inst env b (RootResolved mt ct targs)) (RootResolved ma ca aargs) (Ongoing [])
              = Some (Ongoing []))).
      { intros mt ct targs ma ca aargs Hft Hfa Hna Hca Hbt Hu.
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft)).
        pose proof (root_parts env b K [] mt ct targs Hft Hbt) as Htargs.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite unify_classes, Hbase, (mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) in Hu.
        assert (Hnorm': forall a, In a norm -> argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
        { unfold norm. destruct (Class_eq_dec ca ct) as [<-|Hne]; [rewrite class_eqb_refl; exact Haargs|].
          rewrite (class_eqb_false _ _ Hne). exact (Hnorm ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs). }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (satisfies b s0' -> exists f, unify env f (instantiate env b t) ((fun a => a) a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Htargs t Ht) as [Hft' Hbt']. destruct (Hnorm' a Ha) as [Hfa' [Hna' Hca']].
          exact (IHat t a s0 s0' Hft' Hfa' Hna' Hca' Hbt' Hs0 E). }
        destruct (Hpairs targs norm s s' (instantiate env b) (fun a => a) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn.
        exact Hf. }
      destruct (ifrag_cases env P HP) as [[mt [ct [targs [-> _]]]]|[->|[[mt [ct [targs [-> HP']]]]|[p [bnd [-> [Hfb Hcb]]]]]]];
          [| unfold bottom_type in * | |].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
        rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP')).
        destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]].
        * rewrite unify_nullable_class in H. destruct (IHt _ _ s s' HP' HA HcA Hb' Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP')) in Hf.
          exists (S f). rewrite unify_nullable_class. exact Hf.
        * rewrite unify_nullable_nullable in H.
          assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
          destruct (IHt _ _ s s' HP' HA2 HcA Hb' Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP')) in Hf.
          exists (S f). rewrite unify_nullable_nullable. exact Hf.
      + (* a type variable *)
        destruct (state_of_target n p bnd A s s' HA' H) as [st Hl].
        destruct (target_leaf n p bnd st A s s' Hs Hl HA H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        simpl in Hb. destruct (binds_exactly_some env b K [] p bnd Hb) as [o [x [Ex _]]].
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p bnd _ _ _ Ex). exists f. exact Hf.
    - (* a type with type variables as the assignee *)
      intros P A s s' HP HA HcA Hb Hs H. destruct (afrag_parts env A HA) as [HA' HAn].
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (satisfies b s' -> exists f, unify env f (RootResolved ma ca aargs) (inst env b (RootResolved mp cp pargs)) (Ongoing [])
              = Some (Ongoing []))).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hna Hca Hbp Hu.
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp)).
        pose proof (root_parts env b K [] mp cp pargs Hfp Hbp) as Hpargs.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite unify_classes, Hbase, (mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        assert (Hnorm': (forall a, In a norm -> argument_ifrag env a = true /\ bound_in env b K [] (to_generic a) = true)
            /\ (if class_eqb cp ca then map (instantiate env b) pargs
                else parameterized_supertype_arguments env cp (map (instantiate env b) pargs) ca) = map (instantiate env b) norm).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne]; [rewrite class_eqb_refl; split; [exact Hpargs|reflexivity]|].
          rewrite (class_eqb_false _ _ Hne).
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases env _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          destruct (supertype_commute_variables env wf b K [] cp ca pargs Hne
              (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          split; [exact Hnormp|exact Hcomm]. }
        destruct Hnorm' as [Hnormp Hcomm].
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (satisfies b s0' -> exists f, unify env f ((fun a => a) t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnormp a Ha) as [Hfa' Hba']. destruct (Haargs t Ht) as [Hft' [Hnt' Hct']].
          exact (IHaa a t s0 s0' Hfa' Hft' Hnt' Hct' Hba' Hs0 E). }
        destruct (Hpairs aargs norm s s' (fun a => a) (instantiate env b) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]];
      destruct (ifrag_cases env P HP) as [[mp [cp [pargs [-> _]]]]|[->|[[mp [cp [pargs [-> HP']]]]|[p [bnd [-> [Hfb Hcb]]]]]]];
          try (unfold bottom_type in *).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H).
      + rewrite unify_class_nullable in H. discriminate H.
      + destruct (state_of_assignee n p bnd _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n p bnd st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        simpl in Hb. destruct (binds_exactly_some env b K [] p bnd Hb) as [o [x [Ex _]]].
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p bnd _ _ _ Ex). exists f. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hb Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hb Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
        rewrite unify_nullable_nullable in H. destruct (IHa _ _ s s' HP' HA2 HcA Hb' Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP')) in Hf.
        rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP')).
        exists (S f). rewrite unify_nullable_nullable. exact Hf.
      + destruct (state_of_assignee n p bnd _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n p bnd st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        simpl in Hb. destruct (binds_exactly_some env b K [] p bnd Hb) as [o [x [Ex _]]].
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p bnd _ _ _ Ex). exists f. exact Hf.
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HA HAn HcA Hb Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn. destruct (bound_in_argument env b K [] vt ot (to_generic nt) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na (not_capturable s nt Hs)) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      assert (Hown: ownership_is_assignable_to oa (instantiate_ownership b ot) = true).
      { pose proof (instantiation_preserves_ownership_assignability b oa ot Ho) as Ho'.
        rewrite (ownership_not_instantiated b oa Hoa) in Ho'. exact Ho'. }
      assert (Hfi: is_type_variable (inst env b nt) = false)
          by exact (instance_not_variable env wf b K [] (to_generic nt) (ifrag_sfrag env nt HP) Hbn).
      assert (Hgoal: forall f, compare_variances (unify env f) vt va (inst env b nt) na [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env b (TypeArgument vt ot nt)) (TypeArgument va oa na) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env b K [] vt ot nt HP Hbn).
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va oa na [] Hfi), Hown. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHt nt na s s1 HP HAf Hcn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHa nt na s1 s' HP HAf Hcn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHt nt na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHt nt top_type s s' HP (top_in_afrag env wf) eq_refl Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt bottom_type s s' HP (bottom_in_afrag env wf) eq_refl Hbn Hs H) as [Hs' [Hext Hsnd]] ];
          split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
          exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HA HAn HcA Hb Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn. destruct (bound_in_argument env b K [] vp op (to_generic np) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (unify_type_arguments env n va oa na vp op np s (fragment_not_variable env _ HA)) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      assert (Hown: ownership_is_assignable_to (instantiate_ownership b op) oa = true).
      { pose proof (instantiation_preserves_ownership_assignability b op oa Ho) as Ho'.
        rewrite (ownership_not_instantiated b oa Hoa) in Ho'. exact Ho'. }
      assert (Hgoal: forall f, compare_variances (unify env f) va vp na (inst env b np) [] = Some (Ongoing []) ->
          unify env (S f) (TypeArgument va oa na) (instantiate env b (TypeArgument vp op np)) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env b K [] vp op np HP Hbn).
        rewrite (unify_type_arguments env f va oa na vp _ (inst env b np) [] (fragment_not_variable env _ HA)), Hown. exact E. }
      pose proof (in_fragment_no_vars na HA) as Hnna.
      destruct va, vp; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHa np na s s1 HP HAf Hcn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHt np na s1 s' HP HAf Hcn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHa np na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHt np na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | (* no type variables involved *)
            match type of H with unify env ?k ?x ?y _ = _ =>
              destruct (keeps_free k x y s s' ltac:(first [exact Hnna|reflexivity]) ltac:(first [exact Hnna|reflexivity]) H)
                  as [-> H0];
              split; [exact Hs|]; split; [auto|]; intros _; exists (S k); apply Hgoal; unfold compare_variances; exact H0
            end ].
Qed.

End Main.

(* ---------------------------------------------------------------------------------------------- *)
(* Invocations                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

(*
 * Inference is sound: where unify accepts each argument of an invocation for its parameter, in turn,
 * each argument fits its parameter with the type variables replaced by any types that satisfy the
 * variable states it ends with.
 *)
Theorem invocation_sound: forall n Ps As s0 u b K,
    wf_states s0 ->
    (forall P, In P Ps -> ifrag env P = true /\ bound_in env b K [] (to_generic P) = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (Ongoing s0) = Some (Ongoing u) ->
    wf_states u /\ (satisfies b u ->
        forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true).
Proof.
    intros n Ps As s0 u b K Hs0 HPs HAs H.
    assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', wf_states s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing []))).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP HbP]. destruct (HAs A HA) as [HfA HcA].
      exact (proj1 (constraints_with_arguments b K n) P A s s' HfP HfA HcA HbP Hs E). }
    destruct (fold_chain n _ s0 u (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
        Hs0 H) as [Hu [_ Hall]].
    split; [exact Hu|]. intros Hb P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
    destruct (proj2 (proj2 (Hstep P A Hin s s' Hs E)) (Hx b Hb)) as [f Hf].
    exists f. unfold is_assignable_to, empty_unification. rewrite Hf. reflexivity.
Qed.

(* TypeUnification.getFinalValueFor: the lower bound, unless it is still Nothing, then the upper one *)
Definition final_value (st: VariableState): EType :=
    if is_non_nullable_nothing env (lower_bound st) then upper_bound st else lower_bound st.

(* The final value of a variable that isn't bound exactly is within its bounds, if it is one of the
   types variables are replaced with *)
Lemma final_value_fits: forall s p st o, wf_states s -> lookup_state s p = Some st -> is_exact st = false ->
    xfrag (final_value st) -> fits st o (final_value st).
Proof.
    intros s p st o Hs Hl He Hf. destruct (Hs p st Hl) as [_ [_ Hb]]. destruct (Hb He) as [_ [[K HK] _]].
    unfold fits. rewrite He. destruct (xfrag_reflexive _ Hf) as [k Hr].
    unfold final_value in Hf, Hr |- *. destruct (is_non_nullable_nothing env (lower_bound st)).
    - split; [exists K; exact HK|exists k; exact Hr].
    - split; [exists k; exact Hr|exists K; exact HK].
Qed.

(*
 * The types the type variables are replaced with, in the end: the final value of each variable that
 * isn't bound exactly, and any type the type argument of one that is stands for. They satisfy the
 * variable states, so each argument fits its parameter with them (invocation_sound).
 *)
Theorem final_values_satisfy: forall u b, wf_states u ->
    (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        xfrag x /\ exists st, lookup_state u p = Some st /\
            (is_exact st = false -> x = final_value st)
            /\ (is_exact st = true -> fits st o x)) ->
    satisfies b u.
Proof.
    intros u b Hu Hb p o x E. destruct (Hb p o x E) as [Hx [st [Hl [Hfin Hex]]]]. split; [exact Hx|].
    exists st. split; [exact Hl|]. destruct (is_exact st) eqn:Ee; [exact (Hex eq_refl)|].
    rewrite (Hfin eq_refl) in Hx |- *. exact (final_value_fits u p st o Hu Hl Ee Hx).
Qed.

End Constraints.

(* The class types of Transitivity.v, with the types without type variables as bounds, are types for
   inference, given that intersect and closestCommonSupertypeWith are the bounds they are meant to be
   for them: the instance of Constraints that needs no conjecture *)
Lemma class_types_for_inference: forall env,
    (forall a b x n, no_vars a = true -> no_vars b = true -> in_fragment env x = true ->
        unify env n (intersect env a b) x (Ongoing []) = Some (Ongoing []) ->
        (exists n', unify env n' a x (Ongoing []) = Some (Ongoing [])) /\ (exists n', unify env n' b x (Ongoing []) = Some (Ongoing []))) ->
    (forall a b x n, no_vars a = true -> no_vars b = true -> in_fragment env x = true ->
        unify env n x (closest_common_supertype_with env a b) (Ongoing []) = Some (Ongoing []) ->
        (exists n', unify env n' x a (Ongoing []) = Some (Ongoing [])) /\ (exists n', unify env n' x b (Ongoing []) = Some (Ongoing []))) ->
    (forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true) ->
    (forall a b, no_vars a = true -> no_vars b = true -> no_vars (closest_common_supertype_with env a b) = true) ->
    inference_types env (fun x => in_fragment env x = true) (fun a => no_vars a = true).
Proof.
    intros env Hbelow Habove Hi Hs. constructor.
    - exact (in_fragment_is_gfrag env).
    - intros x Hx. exact Hx.
    - intros x Hx. exists (depth x). exact (proj1 (reflexivity_with_arguments env (depth x)) x [] Hx (le_n _)).
    - exact (in_fragment_no_vars env).
    - intros a b Ha Hb. exact (Hi a b Ha (in_fragment_no_vars env b Hb)).
    - intros a b Ha Hb. exact (Hs a b Ha (in_fragment_no_vars env b Hb)).
    - intros a b x n Ha Hb. exact (Hbelow a b x n Ha (in_fragment_no_vars env b Hb)).
    - intros a b x n Ha Hb. exact (Habove a b x n Ha (in_fragment_no_vars env b Hb)).
    - exact Hi.
    - exact Hs.
Qed.
