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

(* The closest common supertype of two class types is one, too: the lower bounds of the variables stay
   of the types of the arguments, the candidates checked against static upper bounds with type
   variables (plus_static_check) *)
Definition closest_common_supertype_of_classes (env: Environment): Prop :=
    forall a b, afrag env a = true -> closed a = true -> afrag env b = true -> closed b = true ->
        afrag env (closest_common_supertype_with env a b) = true /\ closed (closest_common_supertype_with env a b) = true.

Section Constraints.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
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

Hypothesis supertype_of_classes: closest_common_supertype_of_classes env.

Let in_fragment_no_vars := Inference.in_fragment_no_vars env.
Let argument_in_fragment_no_vars := Inference.argument_in_fragment_no_vars env.

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

(* What is below the upper bound of a variable is below its declared one, where that has no type
   variables (initial_upper_bound) *)
Definition below_static (st: VariableState): Prop :=
    forall x f, xfrag x -> unify env f (upper_bound st) x (Ongoing []) = Some (Ongoing []) ->
        exists f', unify env f' (static_upper_bound st) x (Ongoing []) = Some (Ongoing []).

(* No ownerships of type parameters *)
Fixpoint plain_owners (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb plain_owners arguments
    | Nullable n => plain_owners n
    | TypeArgument _ o n => negb (is_parameter_ownership o) && plain_owners n
    | _ => true
    end.

(* The lower bound of the variable p, checked against (each component of) its static upper bound, the
   variable itself replaced by it (plus_static_check): whatever bindings satisfy the states, it is
   below the bound instantiated with them. Until a lower bound is checked, it is Nothing. *)
Definition static_checked (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    is_non_nullable_nothing env (lower_bound st) = false ->
    forall C, In C (intersected_components (static_upper_bound st)) ->
    forall b K, bound_in env b K [] (to_generic (with_candidate env p (lower_bound st) C)) = true ->
        satisfies b s ->
        exists f, unify env f (inst env b (with_candidate env p (lower_bound st) C)) (lower_bound st) (Ongoing [])
            = Some (Ongoing []).

(* The static upper bound of a variable: without type variables, above the upper bound; with them,
   of the types of the parameters, checked against the lower bound, of the types of the arguments *)
Definition static_ok (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    if no_vars (static_upper_bound st) then below_static st
    else afrag env (lower_bound st) = true /\ closed (lower_bound st) = true
        /\ (forall C, In C (intersected_components (static_upper_bound st)) -> ifrag env C = true)
        /\ plain_owners (static_upper_bound st) = true /\ static_checked s p st.

(* The variable states unify works with: the bounds without type variables, the upper bound above the
   lower one where the variable isn't bound exactly, and no variable to capture; the static upper
   bounds of type variables of a lower rank, and the variable itself (States.ranked_states) *)
Definition wf_states (s: VariableStates): Prop :=
    forall p st, lookup_state s p = Some st ->
        no_vars (upper_bound st) = true /\ no_vars (lower_bound st) = true
        /\ (is_exact st = false -> is_capturable st = false
            /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
            /\ bfrag (upper_bound st) /\ bfrag (lower_bound st) /\ static_ok s p st)
        /\ vars_in (static_vars env p) (static_upper_bound st) = true.

Lemma wf_ranked: forall s, wf_states s -> ranked_states env s.
Proof. intros s Hs q st Hq. destruct (Hs q st Hq) as [Hu [Hl [_ Hv]]]. auto. Qed.

Lemma static_ok_mono: forall s s' p st, (forall b, satisfies b s' -> satisfies b s) -> static_ok s p st -> static_ok s' p st.
Proof.
    intros s s' p st Hn H. unfold static_ok in *. destruct (no_vars (static_upper_bound st)); [exact H|].
    destruct H as [H1 [H2 [H3 [H4 H5]]]]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    intros Hnn C HC b K Hb Hs. exact (H5 Hnn C HC b K Hb (Hn b Hs)).
Qed.

Lemma wf_set_state: forall s p st, wf_states s ->
    (forall b, satisfies b (set_state s p st) -> satisfies b s) ->
    no_vars (upper_bound st) = true -> no_vars (lower_bound st) = true ->
    (is_exact st = false -> is_capturable st = false
        /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
        /\ bfrag (upper_bound st) /\ bfrag (lower_bound st) /\ static_ok (set_state s p st) p st) ->
    vars_in (static_vars env p) (static_upper_bound st) = true ->
    wf_states (set_state s p st).
Proof.
    intros s p st Hs Hn Hu Hl He Hv q st' Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq. injection Hq as <-. auto.
    - rewrite lookup_set_other in Hq by exact Hne. destruct (Hs q st' Hq) as [H1 [H2 [H3 H4]]].
      split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
      intros E. destruct (H3 E) as [H5 [H6 [H7 [H8 H9]]]]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
      exact (static_ok_mono s _ q st' Hn H9).
Qed.

(* Where the static upper bounds have no type variables, the states of the other variables don't matter *)
Lemma static_ok_closed: forall s s' p st, no_vars (static_upper_bound st) = true -> static_ok s p st -> static_ok s' p st.
Proof. intros s s' p st Hc H. unfold static_ok in *. rewrite Hc in *. exact H. Qed.

Lemma wf_set_state_closed: forall s p st, wf_states s ->
    (forall q st', lookup_state s q = Some st' -> is_exact st' = false -> no_vars (static_upper_bound st') = true) ->
    no_vars (upper_bound st) = true -> no_vars (lower_bound st) = true ->
    (is_exact st = false -> is_capturable st = false
        /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
        /\ bfrag (upper_bound st) /\ bfrag (lower_bound st) /\ static_ok (set_state s p st) p st) ->
    vars_in (static_vars env p) (static_upper_bound st) = true ->
    wf_states (set_state s p st).
Proof.
    intros s p st Hs Hc Hu Hl He Hv q st' Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq. injection Hq as <-. auto.
    - rewrite lookup_set_other in Hq by exact Hne. destruct (Hs q st' Hq) as [H1 [H2 [H3 H4]]].
      split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
      intros E. destruct (H3 E) as [H5 [H6 [H7 [H8 H9]]]]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
      exact (static_ok_closed s _ q st' (Hc q st' Hq E) H9).
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
    destruct (Hs p st E) as [_ [_ [He _]]]. rewrite (proj1 (He Ee)). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A static upper bound with a candidate for its variable                                          *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma class_sfrag: forall t, in_fragment env t = true -> nothing_is_bottom t = true -> sfrag env t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hf Hn; try discriminate Hf.
    - change (Nat.eqb (length args) (length (parameter_ids env c))
          && forallb (fun a => match a with TypeArgument _ _ n => in_fragment env n | _ => false end) args = true) in Hf.
      change ((if class_eqb c nothing then is_bottom m args else true) && forallb nothing_is_bottom args = true) in Hn.
      apply andb_true_iff in Hf. destruct Hf as [Hl Ha]. apply andb_true_iff in Hn. destruct Hn as [Hb Hna].
      change ((if class_eqb c nothing then is_bottom m args else
          Nat.eqb (length args) (length (parameter_ids env c))
          && forallb (fun a => match a with TypeArgument _ _ n => sfrag env n | _ => false end) args) = true).
      destruct (class_eqb c nothing); [exact Hb|]. rewrite Hl. cbn [andb]. clear Hb Hl.
      induction args as [|a args IHa]; [reflexivity|]. simpl in Ha, Hna |- *.
      apply andb_true_iff in Ha. destruct Ha as [Ha1 Ha2]. apply andb_true_iff in Hna. destruct Hna as [Hn1 Hn2].
      destruct a as [| | | |v o x| |]; try discriminate Ha1. rewrite (IH x Ha1 Hn1). exact (IHa Ha2 Hn2).
    - change (is_class n && in_fragment env n = true) in Hf. apply andb_true_iff in Hf. destruct Hf as [Hc Hf].
      change ((is_class n || is_generic n) && sfrag env n = true). rewrite Hc. exact (IH n Hf Hn).
Qed.

Lemma to_generic_closed: forall t, closed t = true -> to_generic t = t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try discriminate H.
    - f_equal. induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - rewrite (IH n H). reflexivity.
    - apply andb_true_iff in H. rewrite (IH n (proj2 H)). reflexivity.
Qed.

Lemma class_no_generics: forall t, in_fragment env t = true -> closed t = true -> no_generics t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hf H; try discriminate Hf.
    - change (forallb closed args = true) in H. change (forallb no_generics args = true).
      change (Nat.eqb (length args) (length (parameter_ids env c))
          && forallb (fun a => match a with TypeArgument _ _ n => in_fragment env n | _ => false end) args = true) in Hf.
      apply andb_true_iff in Hf. destruct Hf as [_ Ha]. clear c m.
      induction args as [|a args IHa]; [reflexivity|]. simpl in Ha, H |- *.
      apply andb_true_iff in Ha. destruct Ha as [Ha1 Ha2]. apply andb_true_iff in H. destruct H as [H1 H2].
      destruct a as [| | | |v o x| |]; try discriminate Ha1. simpl in H1 |- *. apply andb_true_iff in H1.
      rewrite (IH x Ha1 (proj2 H1)). exact (IHa Ha2 H2).
    - change (is_class n && in_fragment env n = true) in Hf. apply andb_true_iff in Hf. destruct Hf as [Hc Hf].
      change (is_class n && no_generics n = true). rewrite Hc. exact (IH n Hf H).
Qed.

(* A closed type of the arguments is one of the parameters *)
Lemma closed_ifrag: forall t, afrag env t = true -> closed t = true -> ifrag env t = true.
Proof.
    intros t Ha Hc. destruct (afrag_parts env t Ha) as [Hf Hn]. unfold ifrag.
    rewrite (to_generic_closed t Hc), (class_sfrag t Hf Hn), (class_no_generics t Hf Hc). reflexivity.
Qed.

Lemma ifrag_root_intro: forall m c args, class_eqb c nothing = false -> length args = length (parameter_ids env c) ->
    (forall a, In a args -> argument_ifrag env a = true) -> ifrag env (RootResolved m c args) = true.
Proof.
    intros m c args Hc Hl Ha. unfold ifrag. apply andb_true_iff. split.
    - change ((if class_eqb c nothing then is_bottom m (map to_generic args) else
          Nat.eqb (length (map to_generic args)) (length (parameter_ids env c))
          && forallb (fun a => match a with TypeArgument _ _ n => sfrag env n | _ => false end) (map to_generic args)) = true).
      rewrite Hc, length_map, Hl, Nat.eqb_refl. cbn [andb]. apply forallb_forall. intros a' Ha'.
      apply in_map_iff in Ha'. destruct Ha' as [a [<- Hin]]. pose proof (Ha a Hin) as E.
      destruct a as [| | | |v o n| |]; try discriminate E. exact (ifrag_sfrag env n E).
    - change (forallb no_generics args = true). apply forallb_forall. intros a Hin. pose proof (Ha a Hin) as E.
      destruct a as [| | | |v o n| |]; try discriminate E. exact (ifrag_no_generics env n E).
Qed.

Lemma ifrag_nullable_intro: forall m c args, ifrag env (RootResolved m c args) = true -> ifrag env (Nullable (RootResolved m c args)) = true.
Proof.
    intros m c args H. unfold ifrag in *. apply andb_true_iff in H. destruct H as [Hs Hn].
    change (((is_class (to_generic (RootResolved m c args)) || is_generic (to_generic (RootResolved m c args)))
        && sfrag env (to_generic (RootResolved m c args))) && (is_class (RootResolved m c args) && no_generics (RootResolved m c args)) = true).
    rewrite Hs, Hn. reflexivity.
Qed.

Lemma none_loose: forall b, (forall p a, lookup_binding b p = Some a -> is_loose a = false) ->
    forall t, mentions_loosely_bound b t = false /\ mentions_loosely_bound_in_arguments b t = false.
Proof.
    intros b Hb. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; simpl; try (split; reflexivity).
    - assert (E: existsb (mentions_loosely_bound b) args = false).
      { induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite (proj1 (IH a)). exact IHa. }
      split; exact E.
    - exact (IH n).
    - destruct (lookup_binding b p) eqn:E; [|split; reflexivity]. rewrite (Hb p e E). split; reflexivity.
    - split; [exact (proj1 (IH n))|reflexivity].
    - destruct (lookup_binding b p) eqn:E; [|split; reflexivity]. rewrite (Hb p e E). split; reflexivity.
    - assert (E1: existsb (mentions_loosely_bound b) cs = false).
      { induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (proj1 (IH c)). exact IHc. }
      assert (E2: existsb (mentions_loosely_bound_in_arguments b) cs = false).
      { clear E1. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (proj2 (IH c)). exact IHc. }
      split; [exact E1|exact E2].
Qed.

Lemma candidate_final: forall c, afrag env c = true -> final_argument (TypeArgument invariant ref c) = c.
Proof.
    intros c H. destruct (afrag_parts env c H) as [Hf _]. unfold final_argument. simpl.
    destruct (fragment_cases env c Hf) as [[m [c' [args ->]]]|[m [c' [args [-> _]]]]]; reflexivity.
Qed.

(* A type argument instantiated with bindings that aren't loose, where the type does not become a
   type argument *)
Lemma instantiate_unloose_argument: forall b v o n, (forall p a, lookup_binding b p = Some a -> is_loose a = false) ->
    is_type_argument (instantiate env b n) = false -> (forall x, instantiate env b n = Nullable x -> is_type_argument x = false) ->
    instantiate env b (TypeArgument v o n) = TypeArgument v (instantiate_ownership b o) (instantiate env b n).
Proof.
    intros b v o n Hb Hn Hx. cbn [instantiate]. rewrite (proj2 (none_loose b Hb n)). revert Hn Hx.
    destruct (instantiate env b n) as [m c args|x|g|me msg|v' o' x|g|cs]; intros Hn Hx; try reflexivity.
    - destruct x as [| | | |v' o' y| |]; try reflexivity. specialize (Hx _ eq_refl). discriminate Hx.
    - discriminate Hn.
Qed.

(* The static upper bound of a variable, of the types of the parameters, with a candidate of the types
   of the arguments for the variable, is of the types of the parameters, too *)
Lemma with_candidate_ifrag: forall p c, afrag env c = true -> closed c = true ->
    forall S, ifrag env S = true -> ifrag env (with_candidate env p c S) = true.
Proof.
    intros p c Hc Hcc.
    assert (Hb: forall q a, lookup_binding [(p, TypeArgument invariant ref c)] q = Some a -> is_loose a = false).
    { intros q a E. simpl in E. destruct (param_eqb q p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Hshape: forall t, ifrag env t = true -> is_type_argument t = false /\ forall x, t = Nullable x -> is_type_argument x = false).
    { intros t Ht. destruct (ifrag_cases env wf t Ht) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          split; try reflexivity; intros x E; try discriminate E; injection E as <-; reflexivity. }
    intros S. unfold with_candidate. remember (vsize S) as k eqn:Hk. revert S Hk.
    induction k as [k IH] using lt_wf_ind. intros S -> HS.
    destruct (ifrag_cases env wf S HS) as [[m [c' [args [-> [Hn [Hl Hargs]]]]]]|[->|[[m [c' [args [-> Hr]]]]|[q [-> _]]]]].
    - cbn [instantiate]. apply ifrag_root_intro; [exact Hn|rewrite length_map; exact Hl|].
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (Hargs a Ha) as Ea.
      destruct a as [| | | |v o n| |]; try discriminate Ea. simpl in Ea.
      assert (HIn: ifrag env (instantiate env [(p, TypeArgument invariant ref c)] n) = true).
      { apply (IH (vsize n)); [|reflexivity|exact Ea]. pose proof (vsize_below m c' args _ Ha) as Hv. simpl in Hv |- *. lia. }
      destruct (Hshape _ HIn) as [Ht Hx]. rewrite (instantiate_unloose_argument _ v o n Hb Ht Hx). exact HIn.
    - exact HS.
    - assert (HIn: ifrag env (instantiate env [(p, TypeArgument invariant ref c)] (RootResolved m c' args)) = true).
      { apply (IH (vsize (RootResolved m c' args))); [simpl; lia|reflexivity|exact Hr]. }
      cbn [instantiate] in HIn |- *. cbn [rewrap_nullable]. exact (ifrag_nullable_intro _ _ _ HIn).
    - cbn [instantiate lookup_binding]. destruct (param_eqb q p).
      + rewrite (candidate_final c Hc). exact (closed_ifrag c Hc Hcc).
      + exact HS.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A type variable, assigned to and assigned                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* Unify with the components of an intersection, in turn *)
Lemma fold_components: forall n (cs: list EType) (tgt: EType -> EType) A s s',
    (forall C, In C cs -> forall s0 s0', wf_states s0 -> unify env n (tgt C) A (Ongoing s0) = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0)) ->
    wf_states s -> fold_unify (fun inner C => unify env n (tgt C) A inner) cs (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall C, In C cs -> exists s0 s0', wf_states s0 /\ unify env n (tgt C) A (Ongoing s0) = Some (Ongoing s0')
        /\ (forall b, satisfies b s' -> satisfies b s0')).
Proof.
    intros n cs tgt A. induction cs as [|C cs IH]; intros s s' Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros C [].
    - destruct (unify env n (tgt C) A (Ongoing s)) as [[s1|]|] eqn:E;
          [|rewrite (fold_failed _ cs (fun x _ => unify_keeps_failure env n _ _)) in H; discriminate H|discriminate H].
      destruct (Hstep C (or_introl eq_refl) s s1 Hs E) as [Hs1 Hext1].
      destruct (IH s1 s' (fun C' Hin => Hstep C' (or_intror Hin)) Hs1 H) as [Hs' [Hext Hall]].
      split; [exact Hs'|]. split; [intros b Hb; apply Hext1, Hext, Hb|].
      intros C' [<-|Hin].
      + exists s, s1. split; [exact Hs|]. split; [exact E|exact Hext].
      + exact (Hall C' Hin).
Qed.

(* What unify does with a type of the parameters and one of the arguments, at the fuel of a static
   check *)
Definition target_step (n: nat): Prop :=
    forall P A s s', ifrag env P = true -> afrag env A = true -> closed A = true ->
        wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing [])).

(* What the variable takes: above the lower bound, which is above it; the lower bound checked against
   the static upper bound, where that has type variables, constrains those of a lower rank only *)
Lemma target_leaf: forall n p bnd st A s s', target_step n ->
    wf_states s -> lookup_state s p = Some st -> afrag env A = true -> closed A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f x A (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n p bnd st A s s' IH Hs Hl HAf HcA H. destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
    destruct (afrag_parts env A HAf) as [HA HAn].
    pose proof (in_fragment_no_vars A HA) as HnA.
    assert (H': plus_supertype_constraint env (unify env n) s p A = Some (Ongoing s')).
    { rewrite unify_step_once in H. destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
          unfold unify_step, unify_type_variable in H; [exact H|]. destruct (is_nullable env _); [exact H|discriminate H]. }
    unfold plus_supertype_constraint in H'. rewrite Hl in H'. destruct (is_exact st) eqn:Ee.
    - (* bound exactly: its binding takes A *)
      destruct (keeps_free n _ A s s' Hnl HnA H') as [-> H0]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold fits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [HxF Hc]]]]]]]]. rewrite Hlo in H0.
      destruct (write_leaf env wf K [] n vb ob X o x A [] HX HxF HAf Hc H0) as [_ Hw]. exists (n + K + 1). exact Hw.
    - (* between bounds: the lower bound becomes the closest common supertype with A, checked *)
      cbn zeta in H'.
      pose proof (supertype_no_vars _ _ Hnl HnA) as Hnc.
      destruct (unify env n (upper_bound st) (closest_common_supertype_with env (lower_bound st) A) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'.
      destruct (keeps_free n _ _ s ns Hnu Hnc E) as [-> H0].
      destruct (He eq_refl) as [Hcap [_ [Hbu [Hbl Hok]]]].
      set (c := closest_common_supertype_with env (lower_bound st) A) in *.
      set (st' := mkVariableState (static_upper_bound st) (upper_bound st) c false (is_capturable st)).
      assert (Hfit': forall o x, xfrag x -> fits st' o x -> fits st o x).
      { intros o x Hx Hfit. unfold fits in Hfit |- *. rewrite Ee. unfold st' in Hfit. cbn [is_exact upper_bound lower_bound] in Hfit.
        destruct Hfit as [[K1 E1] [K2 E2]]. split; [|exists K2; exact E2].
        exact (proj1 (supertype_is_above _ _ x K1 Hbl HA Hx E1)). }
      destruct (plus_static_check env (unify env n) st p c (Ongoing s)) as [[s2|]|] eqn:E2; cbn beta iota in H'; try discriminate H'.
      injection H' as <-.
      assert (Hcheck: wf_states s2 /\ (forall b, satisfies b s2 -> satisfies b s) /\ lookup_state s2 p = Some st
          /\ (no_vars (static_upper_bound st) = false -> afrag env c = true /\ closed c = true
              /\ forall C, In C (intersected_components (static_upper_bound st)) ->
                  forall b K, bound_in env b K [] (to_generic (with_candidate env p c C)) = true -> satisfies b s2 ->
                  exists f, unify env f (inst env b (with_candidate env p c C)) c (Ongoing []) = Some (Ongoing []))).
      { unfold plus_static_check in E2. destruct (no_vars (static_upper_bound st)) eqn:Ens.
        - injection E2 as <-. split; [exact Hs|]. split; [auto|]. split; [exact Hl|]. intros E'; discriminate E'.
        - unfold static_ok in Hok. rewrite Ens in Hok. destruct Hok as [HlA [HlC [HSi _]]].
          destruct (supertype_of_classes _ _ HlA HlC HAf HcA) as [HcF HcC].
          destruct (fold_components n _ (fun C => with_candidate env p c C) c s s2
              (fun C HC s0 s0' Hs0 E0 => let H' := IH _ c s0 s0' (with_candidate_ifrag p c HcF HcC _ (HSi C HC)) HcF HcC Hs0 E0 in
                  conj (proj1 H') (proj1 (proj2 H')))
              Hs E2) as [Hs2 [Hn2 Hall]].
          destruct (fold_keeps_from env _ _ (parameter_rank env p) s s2
              (fun C s0 s0' HC Hs0 E0 => unify_keeps_from env wf intersect_no_vars supertype_no_vars n (parameter_rank env p) _ c s0 s0' Hs0
                  (or_intror (conj (candidate_below env wf p c C (vars_in_intersected _ _ Hsv C HC) Hnc) Hnc)) E0)
              (fun C _ => unify_keeps_failure env n _ _) (wf_ranked s Hs) E2) as [Kf _].
          split; [exact Hs2|]. split; [exact Hn2|]. split; [rewrite (Kf p (le_n _)); exact Hl|].
          intros _. split; [exact HcF|]. split; [exact HcC|].
          intros C HC b K Hb Hsat. destruct (Hall C HC) as [s0 [s0' [Hs0 [E0 Hx]]]].
          destruct (IH _ c s0 s0' (with_candidate_ifrag p c HcF HcC _ (HSi C HC)) HcF HcC Hs0 E0) as [_ [_ Hsnd]].
          exact (Hsnd b K Hb (Hx b Hsat)). }
      destruct Hcheck as [Hs2 [Hn2 [Hl2 Hchk]]].
      pose proof (satisfies_set_state s2 p st st' Hl2 Hfit') as Hn'.
      split; [|split; [intros b Hb; exact (Hn2 b (Hn' b Hb))|]].
      + apply (wf_set_state s2 p st' Hs2 Hn' Hnu Hnc); [|exact Hsv].
        intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact Hbu|]. split; [exact (supertype_bfrag _ _ Hbl HA)|].
        unfold static_ok. unfold st'. cbn [static_upper_bound lower_bound upper_bound].
        destruct (no_vars (static_upper_bound st)) eqn:Ens.
        * unfold static_ok in Hok. rewrite Ens in Hok. exact Hok.
        * destruct (Hchk eq_refl) as [HcF [HcC Hsnd]]. unfold static_ok in Hok. rewrite Ens in Hok. destruct Hok as [_ [_ [HSi [HSo _]]]].
          split; [exact HcF|]. split; [exact HcC|]. split; [exact HSi|]. split; [exact HSo|].
          intros _ C HC b K Hb Hsat. exact (Hsnd C HC b K Hb (Hn' b Hsat)).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s2 p _)). unfold fits in Hfit. unfold st' in Hfit.
        cbn [is_exact lower_bound] in Hfit.
        destruct Hfit as [[K1 E1] _]. exact (proj2 (supertype_is_above _ _ x K1 Hbl HA Hx E1)).
Qed.

(* What the variable is assigned to: below the upper bound, which is below it *)
Lemma assignee_leaf: forall n p bnd st A s s', wf_states s -> lookup_state s p = Some st -> in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f A x (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n p bnd st A s s' Hs Hl HA H. destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
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
      destruct (He eq_refl) as [Hcap [_ [Hbu [Hbl Hok]]]].
      set (st' := mkVariableState (static_upper_bound st) (intersect env (upper_bound st) A) (lower_bound st) false (is_capturable st)).
      assert (Hfit': forall o x, xfrag x -> fits st' o x -> fits st o x).
      { intros o x Hx Hfit. unfold fits in Hfit |- *. rewrite Ee. unfold st' in Hfit.
        cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [[K1 E1] [K2 E2]]. split; [exists K1; exact E1|].
        exact (proj1 (intersect_is_below _ _ x K2 Hbu HA Hx E2)). }
      pose proof (satisfies_set_state s p st st' Hl Hfit') as Hn'.
      split; [|split; [exact Hn'|]].
      + apply (wf_set_state s p st' Hs Hn' Hnn Hnl); [|exact Hsv].
        intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact (intersect_bfrag _ _ Hbu HA)|]. split; [exact Hbl|].
        unfold static_ok. unfold st'. cbn [static_upper_bound lower_bound upper_bound].
        unfold static_ok in Hok. destruct (no_vars (static_upper_bound st)).
        * intros x f Hx Ex. destruct (intersect_is_below _ _ x f Hbu HA Hx Ex) as [[f1 E1] _]. exact (Hok x f1 Hx E1).
        * destruct Hok as [H1 [H2 [H3 [H4 H5]]]]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
          intros Hnn' C HC b K Hb Hsat. exact (H5 Hnn' C HC b K Hb (Hn' b Hsat)).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold fits in Hfit. unfold st' in Hfit.
        cbn [is_exact upper_bound] in Hfit.
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
    destruct (is_nullable env _); [rewrite E in H|]; discriminate H.
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

Lemma root_args_ifrag: forall m c args, ifrag env (RootResolved m c args) = true -> forall a, In a args -> argument_ifrag env a = true.
Proof.
    intros m c args Hf a Ha.
    destruct (ifrag_cases env wf _ Hf) as [[m' [c' [args' [Heq [_ [_ Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
        try discriminate Heq.
    - injection Heq as <- <- <-. exact (Hargs a Ha).
    - unfold bottom_type in Heq. injection Heq as _ _ ->. destruct Ha.
Qed.

Lemma constraints_with_arguments: forall n,
    (forall P A s s', ifrag env P = true -> afrag env A = true -> closed A = true ->
        wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', ifrag env P = true -> afrag env A = true -> closed A = true ->
        wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f A (inst env b P) (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f (instantiate env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f A (instantiate env b P) (Ongoing []) = Some (Ongoing []))).
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
    assert (Hpairs: forall targs aargs s s' (inst_t inst_a: Bindings -> EType -> EType) (Bp: Bindings -> nat -> Prop),
        (forall t a, In (t, a) (combine targs aargs) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (forall b K, Bp b K -> satisfies b s0' -> exists f, unify env f (inst_t b t) (inst_a b a) (Ongoing []) = Some (Ongoing []))) ->
        wf_states s -> fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, Bp b K -> satisfies b s' -> exists f, fold_unify (fun inner '(t, a) => unify env f t a inner)
            (combine (map (inst_t b) targs) (map (inst_a b) aargs)) (Ongoing []) = Some (Ongoing []))).
    { intros targs aargs s s' inst_t inst_a Bp Hp Hs H.
      destruct (fold_chain n _ s s' (fun t a Hin s0 s0' Hs0 E => let H' := Hp t a Hin s0 s0' Hs0 E in conj (proj1 H') (proj1 (proj2 H')))
          Hs H) as [Hs' [Hext Hall]].
      split; [exact Hs'|]. split; [exact Hext|]. intros b K HB Hb.
      destruct (uniform_fuel (combine targs aargs) (fun f '(t, a) => unify env f (inst_t b t) (inst_a b a) (Ongoing []) = Some (Ongoing [])))
          as [f Hf].
      - intros f f' [t a] Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E).
      - intros [t a] Hin. destruct (Hall t a Hin) as [s0 [s0' [Hs0 [E Hx]]]].
        exact (proj2 (proj2 (Hp t a Hin s0 s0' Hs0 E)) b K HB (Hx b Hb)).
      - exists f. apply fold_from_pairs. intros x y Hin. destruct (combine_map_in (inst_t b) (inst_a b) _ _ x y Hin) as [t [a [Hin' [-> ->]]]].
        exact (Hf (t, a) Hin'). }
    split; [|split; [|split]].
    - (* a type with type variables as the target *)
      intros P A s s' HP HA HcA Hs H. destruct (afrag_parts env A HA) as [HA' HAn].
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (forall b K, bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true -> satisfies b s' ->
              exists f, unify env f (inst env b (RootResolved mt ct targs)) (RootResolved ma ca aargs) (Ongoing [])
              = Some (Ongoing []))).
      { intros mt ct targs ma ca aargs Hft Hfa Hna Hca Hu.
        pose proof (root_args_ifrag mt ct targs Hft) as Htargs.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros b K Hbt _. exists 1.
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft) ltac:(solve_bound_vars)).
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) in Hu.
        assert (Hnorm': forall a, In a norm -> argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
        { unfold norm. destruct (Class_eq_dec ca ct) as [<-|Hne]; [rewrite class_eqb_refl; exact Haargs|].
          rewrite (class_eqb_false _ _ Hne). exact (Hnorm ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs). }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (forall b K, bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true -> satisfies b s0' ->
                exists f, unify env f ((fun b => instantiate env b) b t) ((fun _ a => a) b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnorm' a Ha) as [Hfa' [Hna' Hca']].
          destruct (IHat t a s0 s0' (Htargs t Ht) Hfa' Hna' Hca' Hs0 E) as [Hs1 [Hn1 Hsnd]].
          split; [exact Hs1|]. split; [exact Hn1|]. intros b K Hbt Hsb.
          exact (Hsnd b K (bound_in_root env b K [] mt ct (map to_generic targs) Hbt _ (in_map _ _ _ Ht)) Hsb). }
        destruct (Hpairs targs norm s s' (fun b => instantiate env b) (fun _ a => a) _ Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hbt Hsb. destruct (Hsound b K Hbt Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft) ltac:(solve_bound_vars)).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn.
        exact Hf. }
      destruct (ifrag_cases env wf P HP) as [[mt [ct [targs [-> _]]]]|[->|[[mt [ct [targs [-> HP']]]]|[p [-> Hfb]]]]];
          [| unfold bottom_type in * | |].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]].
        * rewrite unify_nullable_class in H. destruct (IHt _ _ s s' HP' HA HcA Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
          assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
          destruct (Hsound b K Hb' Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hf.
          rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
          exists (S f). rewrite unify_nullable_class. exact Hf.
        * rewrite unify_nullable_nullable in H.
          assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
          destruct (IHt _ _ s s' HP' HA2 HcA Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
          assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
          destruct (Hsound b K Hb' Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hf.
          rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
          exists (S f). rewrite unify_nullable_nullable. exact Hf.
      + (* a type variable *)
        destruct (state_of_target n p [] A s s' HA' H) as [st Hl].
        destruct (target_leaf n p [] st A s s' IHt Hs Hl HA HcA H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p [] _ _ _ Ex). exists f. exact Hf.
    - (* a type with type variables as the assignee *)
      intros P A s s' HP HA HcA Hs H. destruct (afrag_parts env A HA) as [HA' HAn].
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (forall b K, bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true -> satisfies b s' ->
              exists f, unify env f (RootResolved ma ca aargs) (inst env b (RootResolved mp cp pargs)) (Ongoing [])
              = Some (Ongoing []))).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hna Hca Hu.
        pose proof (root_args_ifrag mp cp pargs Hfp) as Hpargs0.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros b K Hbp _. exists 1.
          rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp) ltac:(solve_bound_vars)).
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        assert (Hlp: length pargs = length (parameter_ids env cp)).
        { destruct (ifrag_cases env wf _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
              try discriminate Heq.
          - injection Heq as <- <- <-. exact Hl.
          - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
        (* the parts of the normalized type arguments, and how they instantiate, from the bindings *)
        assert (Hnorm': forall b K, bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true ->
            (forall a, In a norm -> argument_ifrag env a = true /\ bound_in env b K [] (to_generic a) = true)
            /\ (if class_eqb cp ca then map (instantiate env b) pargs
                else parameterized_supertype_arguments env cp (map (instantiate env b) pargs) ca) = map (instantiate env b) norm).
        { intros b K Hbp. pose proof (root_parts env wf b K [] mp cp pargs Hfp Hbp) as Hpargs.
          unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne]; [rewrite class_eqb_refl; split; [exact Hpargs|reflexivity]|].
          rewrite (class_eqb_false _ _ Hne).
          destruct (supertype_commute_variables env wf b K [] cp ca pargs Hne
              (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          split; [exact Hnormp|exact Hcomm]. }
        (* the normalized type arguments are of the parameters, whatever the bindings *)
        assert (Hnormi: forall a, In a norm -> argument_ifrag env a = true).
        { intros a Ha. unfold norm in Ha. destruct (Class_eq_dec cp ca) as [<-|Hne].
          - rewrite class_eqb_refl in Ha. exact (Hpargs0 a Ha).
          - rewrite (class_eqb_false _ _ Hne) in Ha.
            exact (supertype_arguments_ifrag env wf cp ca pargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs0 a Ha). }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (forall b K, bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true -> satisfies b s0' ->
                exists f, unify env f ((fun _ a => a) b t) ((fun b => instantiate env b) b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Haargs t Ht) as [Hft' [Hnt' Hct']].
          destruct (IHaa a t s0 s0' (Hnormi a Ha) Hft' Hnt' Hct' Hs0 E) as [Hs1 [Hn1 Hsnd]].
          split; [exact Hs1|]. split; [exact Hn1|]. intros b K Hbp Hsb.
          exact (Hsnd b K (proj2 (proj1 (Hnorm' b K Hbp) a Ha)) Hsb). }
        destruct (Hpairs aargs norm s s' (fun _ a => a) (fun b => instantiate env b) _ Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hbp Hsb. destruct (Hsound b K Hbp Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp) ltac:(solve_bound_vars)).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn.
        unfold unify_arguments. rewrite (proj2 (Hnorm' b K Hbp)). exact Hf. }
      destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]];
      destruct (ifrag_cases env wf P HP) as [[mp [cp [pargs [-> _]]]]|[->|[[mp [cp [pargs [-> HP']]]]|[p [-> Hfb]]]]];
          try (unfold bottom_type in *).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA H).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA H).
      + rewrite unify_class_nullable in H. discriminate H.
      + destruct (state_of_assignee n p [] _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n p [] st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p [] _ _ _ Ex). exists f. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb. destruct (Hsound b K Hb Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb. destruct (Hsound b K Hb Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_nullable in H. destruct (IHa _ _ s s' HP' HA2 HcA Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
        destruct (Hsound b K Hb' Hsb) as [f Hf].
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hf.
        rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
        exists (S f). rewrite unify_nullable_nullable. exact Hf.
      + destruct (state_of_assignee n p [] _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n p [] st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p [] _ _ _ Ex). exists f. exact Hf.
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HA HAn HcA Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn.
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na (not_capturable s nt Hs)) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      assert (Hgoal: forall b K, bound_in env b K [] (to_generic (TypeArgument vt ot nt)) = true ->
          forall f, compare_variances (unify env f) vt va (inst env b nt) na [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env b (TypeArgument vt ot nt)) (TypeArgument va oa na) (Ongoing []) = Some (Ongoing [])).
      { intros b K Hb f E. destruct (bound_in_argument env b K [] vt ot (to_generic nt) Hb) as [_ Hbn].
        assert (Hown: ownership_is_assignable_to oa (instantiate_ownership b ot) = true).
        { pose proof (instantiation_preserves_ownership_assignability b oa ot Ho) as Ho'.
          rewrite (ownership_not_instantiated b oa Hoa) in Ho'. exact Ho'. }
        assert (Hfi: is_type_variable (inst env b nt) = false)
            by exact (instance_not_variable env wf b K [] (to_generic nt) (ifrag_sfrag env nt HP) Hbn).
        rewrite (instantiate_argument env wf b K [] vt ot nt HP Hbn).
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va oa na [] Hfi), Hown. exact E. }
      assert (Hpart: forall b K, bound_in env b K [] (to_generic (TypeArgument vt ot nt)) = true -> bound_in env b K [] (to_generic nt) = true)
          by (intros b K Hb; exact (proj2 (bound_in_argument env b K [] vt ot (to_generic nt) Hb))).
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHt nt na s s1 HP HAf Hcn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHa nt na s1 s' HP HAf Hcn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros b K Hb Hsb.
           destruct (Hsnd2 b K (Hpart b K Hb) Hsb) as [f2 Hf2]. destruct (Hsnd1 b K (Hpart b K Hb) (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply (Hgoal b K Hb). unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHt nt na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHt nt top_type s s' HP (top_in_afrag env wf) eq_refl Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt bottom_type s s' HP (bottom_in_afrag env wf) eq_refl Hs H) as [Hs' [Hext Hsnd]] ];
          split; [exact Hs'|]; split; [exact Hext|]; intros b K Hb Hsb; destruct (Hsnd b K (Hpart b K Hb) Hsb) as [f Hf];
          exists (S f); apply (Hgoal b K Hb); unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HA HAn HcA Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn.
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (unify_type_arguments env n va oa na vp op np s (fragment_not_variable env _ HA)) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      assert (Hgoal: forall b K, bound_in env b K [] (to_generic (TypeArgument vp op np)) = true ->
          forall f, compare_variances (unify env f) va vp na (inst env b np) [] = Some (Ongoing []) ->
          unify env (S f) (TypeArgument va oa na) (instantiate env b (TypeArgument vp op np)) (Ongoing []) = Some (Ongoing [])).
      { intros b K Hb f E. destruct (bound_in_argument env b K [] vp op (to_generic np) Hb) as [_ Hbn].
        assert (Hown: ownership_is_assignable_to (instantiate_ownership b op) oa = true).
        { pose proof (instantiation_preserves_ownership_assignability b op oa Ho) as Ho'.
          rewrite (ownership_not_instantiated b oa Hoa) in Ho'. exact Ho'. }
        rewrite (instantiate_argument env wf b K [] vp op np HP Hbn).
        rewrite (unify_type_arguments env f va oa na vp _ (inst env b np) [] (fragment_not_variable env _ HA)), Hown. exact E. }
      assert (Hpart: forall b K, bound_in env b K [] (to_generic (TypeArgument vp op np)) = true -> bound_in env b K [] (to_generic np) = true)
          by (intros b K Hb; exact (proj2 (bound_in_argument env b K [] vp op (to_generic np) Hb))).
      pose proof (in_fragment_no_vars na HA) as Hnna.
      destruct va, vp; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHa np na s s1 HP HAf Hcn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHt np na s1 s' HP HAf Hcn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros b K Hb Hsb.
           destruct (Hsnd2 b K (Hpart b K Hb) Hsb) as [f2 Hf2]. destruct (Hsnd1 b K (Hpart b K Hb) (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply (Hgoal b K Hb). unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHa np na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros b K Hb Hsb; destruct (Hsnd b K (Hpart b K Hb) Hsb) as [f Hf];
            exists (S f); apply (Hgoal b K Hb); unfold compare_variances; exact Hf
          | destruct (IHt np na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros b K Hb Hsb; destruct (Hsnd b K (Hpart b K Hb) Hsb) as [f Hf];
            exists (S f); apply (Hgoal b K Hb); unfold compare_variances; exact Hf
          | (* no type variables involved *)
            match type of H with unify env ?k ?x ?y _ = _ =>
              destruct (keeps_free k x y s s' ltac:(first [exact Hnna|reflexivity]) ltac:(first [exact Hnna|reflexivity]) H)
                  as [-> H0];
              split; [exact Hs|]; split; [auto|]; intros b K Hb _; exists (S k); apply (Hgoal b K Hb); unfold compare_variances; exact H0
            end ].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Invocations                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

(*
 * Inference is sound: where unify accepts each argument of an invocation for its parameter, in turn,
 * each argument fits its parameter with the type variables replaced by any types that satisfy the
 * variable states it ends with.
 *)
Theorem invocation_sound: forall n Ps As s0 u,
    wf_states s0 ->
    (forall P, In P Ps -> ifrag env P = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (Ongoing s0) = Some (Ongoing u) ->
    wf_states u /\ (forall b K, (forall P, In P Ps -> bound_in env b K [] (to_generic P) = true) -> satisfies b u ->
        forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true).
Proof.
    intros n Ps As s0 u Hs0 HPs HAs H.
    assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', wf_states s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing []))).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HAs A HA) as [HfA HcA].
      exact (proj1 (constraints_with_arguments n) P A s s' (HPs P HP) HfA HcA Hs E). }
    destruct (fold_chain n _ s0 u (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
        Hs0 H) as [Hu [_ Hall]].
    split; [exact Hu|]. intros b K HbP Hb P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
    apply in_combine_l in Hin as HP.
    destruct (proj2 (proj2 (Hstep P A Hin s s' Hs E)) b K (HbP P HP) (Hx b Hb)) as [f Hf].
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
    intros s p st o Hs Hl He Hf. destruct (Hs p st Hl) as [_ [_ [Hb _]]]. destruct (Hb He) as [_ [[K HK] _]].
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
