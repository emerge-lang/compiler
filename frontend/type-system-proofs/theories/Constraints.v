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
    (* what takes a class type takes it with a mutability given to it, and without null, where that fits *)
    it_reference_takes: forall gm (nn: bool) x a n, xfrag x -> in_fragment env a = true ->
        (forall m, gm = Some m -> Model.is_subtype_of (assignment_mutability env a) m = true) -> (nn = true -> is_nullable env a = false) ->
        unify env n x a (Ongoing []) = Some (Ongoing []) -> exists n', unify env n' (ref_apply env gm nn x) a (Ongoing []) = Some (Ongoing []);
    (* what is assigned a type takes it with a mutability given to it, and without null *)
    it_reference_assigns: forall gm (nn: bool) x a n, xfrag x -> in_fragment env a = true ->
        unify env n a x (Ongoing []) = Some (Ongoing []) -> exists n', unify env n' a (ref_apply env gm nn x) (Ongoing []) = Some (Ongoing []);
    (* what is within a class type is, of a mutability given to both and without null, within it *)
    it_reference_within: forall gm (nn: bool) x B n, xfrag x -> in_fragment env B = true ->
        unify env n B x (Ongoing []) = Some (Ongoing []) ->
        exists n', unify env n' (bound_apply env gm nn B) (ref_apply env gm nn x) (Ongoing []) = Some (Ongoing []);
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
Let reference_takes := it_reference_takes env xfrag bfrag types.
Let reference_assigns := it_reference_assigns env xfrag bfrag types.
Let reference_within := it_reference_within env xfrag bfrag types.

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

(* The components of an intersection, nullable or not *)
Definition inter_of (t: EType): option (list EType) :=
    match t with Intersection cs | Nullable (Intersection cs) => Some cs | _ => None end.

Lemma intersected_none: forall t, inter_of t = None -> intersected_components t = [t].
Proof. intros [| [| | | | | |cs] | | | | |cs] E; try discriminate E; reflexivity. Qed.

(* No type of pfrag is an intersection *)
Lemma pfrag_not_inter: forall P, pfrag env P = true -> inter_of P = None.
Proof.
    intros [| [| | | | | |cs] | | | | |cs] H; try reflexivity; unfold pfrag, ifrag, reference_variable in H; cbn in H; discriminate H.
Qed.

Lemma no_inter: forall Ps, (forall P, In P Ps -> pfrag env P = true) -> ~ exists P cs, In P Ps /\ inter_of P = Some cs.
Proof. intros Ps H [P [cs [HP Ei]]]. rewrite (pfrag_not_inter P (H P HP)) in Ei. discriminate Ei. Qed.

(* The lower bound of the variable p, checked against its static upper bound, the variable itself
   replaced by it (plus_static_check): whatever bindings satisfy the states, it is below each component
   of the bound instantiated with them; of an intersection, where they are class types. Until a lower
   bound is checked, it is Nothing. *)
Definition static_checked (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    is_non_nullable_nothing env (lower_bound st) = false ->
    forall C, In C (intersected_components (static_upper_bound st)) ->
    forall b K, bound_in env b K [] (to_generic (with_candidate env p (lower_bound st) C)) = true ->
        satisfies b s ->
        ((exists cs, inter_of (static_upper_bound st) = Some cs) -> bindings_in_fragment env b) ->
        exists f, unify env f (inst env b (with_candidate env p (lower_bound st) C)) (lower_bound st) (Ongoing [])
            = Some (Ongoing []).

(* A static upper bound with type variables: an intersection as ofComponents makes it, nullable or not,
   of components of the types of the parameters or type variables (compfrag), assigned as one
   mutability, none of them the variable
   p itself; or a type variable other than p, of any mutability, narrowed or made nullable *)
Definition static_form (p: TypeParameterId) (S: EType): Prop :=
    (forall cs, inter_of S = Some cs -> (forall C, In C cs -> compfrag env C = true)
        /\ components_sfrag env (map to_generic cs) = true
        /\ (forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs))
        /\ forall g, In (TypeVariable g) cs -> param_of g <> p)
    /\ forall gm nn q, S = TypeVariable (mkGenericRef gm nn q []) \/ S = Nullable (TypeVariable (mkGenericRef gm nn q [])) -> q <> p.

(* The static upper bound of a variable: without type variables, above the upper bound; with them,
   of the types of the parameters, checked against the lower bound, of the types of the arguments *)
Definition static_ok (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    if no_vars (static_upper_bound st) then below_static st
    else afrag env (lower_bound st) = true /\ closed (lower_bound st) = true
        /\ (forall C, In C (intersected_components (static_upper_bound st)) -> pfrag env C = true)
        /\ plain_owners (static_upper_bound st) = true /\ static_form p (static_upper_bound st)
        /\ static_checked s p st.

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
    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    split; [exact H5|]. intros Hnn C HC b K Hb Hs. exact (H6 Hnn C HC b K Hb (Hn b Hs)).
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

Lemma class_sfrag: forall t, in_fragment env t = true -> sfrag env t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hf; try discriminate Hf.
    - change (Nat.eqb (length args) (length (parameter_ids env c))
          && forallb (fun a => match a with TypeArgument _ _ n => in_fragment env n | _ => false end) args = true) in Hf.
      apply andb_true_iff in Hf. destruct Hf as [Hl Ha].
      change (Nat.eqb (length args) (length (parameter_ids env c))
          && forallb (fun a => match a with TypeArgument _ _ n => sfrag env n | _ => false end) args = true).
      rewrite Hl. cbn [andb]. clear Hl.
      induction args as [|a args IHa]; [reflexivity|]. simpl in Ha |- *.
      apply andb_true_iff in Ha. destruct Ha as [Ha1 Ha2].
      destruct a as [| | | |v o x| |]; try discriminate Ha1. rewrite (IH x Ha1). exact (IHa Ha2).
    - change (is_class n && in_fragment env n = true) in Hf. apply andb_true_iff in Hf. destruct Hf as [Hc Hf].
      change ((is_class n || is_generic n) && sfrag env n = true). rewrite Hc. exact (IH n Hf).
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
    intros t Ha Hc. pose proof (afrag_in_fragment env t Ha) as Hf. unfold ifrag.
    rewrite (to_generic_closed t Hc), (class_sfrag t Hf), (class_no_generics t Hf Hc). reflexivity.
Qed.

Lemma ifrag_root_intro: forall m c args, length args = length (parameter_ids env c) ->
    (forall a, In a args -> argument_ifrag env a = true) -> ifrag env (RootResolved m c args) = true.
Proof.
    intros m c args Hl Ha. unfold ifrag. apply andb_true_iff. split.
    - change (Nat.eqb (length (map to_generic args)) (length (parameter_ids env c))
          && forallb (fun a => match a with TypeArgument _ _ n => sfrag env n | _ => false end) (map to_generic args) = true).
      rewrite length_map, Hl, Nat.eqb_refl. cbn [andb]. apply forallb_forall. intros a' Ha'.
      apply in_map_iff in Ha'. destruct Ha' as [a [<- Hin]]. pose proof (Ha a Hin) as E.
      destruct a as [| | | |v o n| |]; try discriminate E. exact (proj1 (proj2 (argument_ifrag_parts env _ E))).
    - change (forallb no_generics args = true). apply forallb_forall. intros a Hin. pose proof (Ha a Hin) as E.
      exact (proj2 (proj2 (argument_ifrag_parts env _ E))).
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
    intros c H. pose proof (afrag_in_fragment env c H) as Hf. unfold final_argument. simpl.
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
    { intros t Ht. destruct (ifrag_cases env wf t Ht) as [[m [c' [args [-> _]]]]|[[m_bot ->]|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          split; try reflexivity; intros x E; try discriminate E; injection E as <-; reflexivity. }
    intros S. unfold with_candidate. remember (vsize S) as k eqn:Hk. revert S Hk.
    induction k as [k IH] using lt_wf_ind. intros S -> HS.
    destruct (ifrag_cases env wf S HS) as [[m [c' [args [-> [Hn [Hl Hargs]]]]]]|[[m_bot ->]|[[m [c' [args [-> Hr]]]]|[q [-> _]]]]].
    - cbn [instantiate]. apply ifrag_root_intro; [rewrite length_map; exact Hl|].
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (Hargs a Ha) as Ea.
      destruct a as [| | | |v o n| |]; try discriminate Ea. change (nfrag env n = true) in Ea.
      destruct (nfrag_cases env n Ea) as [En|[gm [nn [q [Eq _]]]]].
      + assert (HIn: ifrag env (instantiate env [(p, TypeArgument invariant ref c)] n) = true).
        { apply (IH (vsize n)); [|reflexivity|exact En]. pose proof (vsize_below m c' args _ Ha) as Hv. simpl in Hv |- *. lia. }
        destruct (Hshape _ HIn) as [Ht Hx]. rewrite (instantiate_unloose_argument _ v o n Hb Ht Hx). exact (ifrag_nfrag env _ HIn).
      + (* a reference to the variable: of the candidate, of the mutability given to it, without null or
           made nullable; to another, it stays *)
        assert (Hi: instantiate env [(p, TypeArgument invariant ref c)] n = n
            \/ ifrag env (instantiate env [(p, TypeArgument invariant ref c)] n) = true).
        { destruct (ref_apply_afrag env gm nn c Hc) as [Hr Hrc]. rewrite <- Hrc in Hcc.
          destruct (param_eqb q p) eqn:Epq.
          - right. assert (El: lookup_binding [(p, TypeArgument invariant ref c)] q = Some (TypeArgument invariant ref c))
                by (simpl; rewrite Epq; reflexivity).
            destruct Eq as [-> | ->].
            { rewrite (instantiate_reference env _ gm nn q [] _ El), (candidate_final c Hc). exact (closed_ifrag _ Hr Hcc). }
            rewrite instantiate_nullable_any, (instantiate_reference env _ gm nn q [] _ El), (candidate_final c Hc).
            pose proof (afrag_in_fragment env _ Hr) as Hrf.
            destruct (fragment_cases env _ Hrf) as [[my [cy [yargs Ey]]]|[my [cy [yargs [Ey _]]]]]; rewrite Ey in *;
                cbn [rewrap_nullable]; [apply ifrag_nullable_intro|]; exact (closed_ifrag _ Hr Hcc).
          - left. assert (El: lookup_binding [(p, TypeArgument invariant ref c)] q = None) by (simpl; rewrite Epq; reflexivity).
            destruct Eq as [-> | ->]; [|rewrite instantiate_nullable_any]; rewrite (instantiate_unbound_variable env _ (mkGenericRef gm nn q []) El); reflexivity. }
        destruct Hi as [Hi|Hi].
        * assert (Ht: is_type_argument (instantiate env [(p, TypeArgument invariant ref c)] n) = false
              /\ forall x, instantiate env [(p, TypeArgument invariant ref c)] n = Nullable x -> is_type_argument x = false)
              by (rewrite Hi; destruct Eq as [-> | ->]; split; try reflexivity; intros x E; try discriminate E; injection E as <-; reflexivity).
          destruct Ht as [Ht Hx]. rewrite (instantiate_unloose_argument _ v o n Hb Ht Hx), Hi. exact Ea.
        * destruct (Hshape _ Hi) as [Ht Hx]. rewrite (instantiate_unloose_argument _ v o n Hb Ht Hx). exact (ifrag_nfrag env _ Hi).
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
Lemma state_of_target: forall n p bnd A s r, in_fragment env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing r) -> exists st, lookup_state s p = Some st.
Proof.
    intros n p bnd A s r HA H. destruct (lookup_state s p) as [st|] eqn:E; [eauto|exfalso].
    rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_type_variable, plus_supertype_constraint in H; [rewrite E in H; discriminate H|].
    destruct (is_nullable env _); [rewrite E in H|]; discriminate H.
Qed.

Lemma target_step_down: forall k n, k <= n -> target_step n -> target_step k.
Proof.
    intros k n Hk IH P A s s' HP HA HcA Hs H.
    exact (IH P A s s' HP HA HcA Hs (unify_fuel_monotone env k n _ _ _ _ Hk H)).
Qed.

(* What target_leaf shows, with the fuel k *)
Definition leaf_step (k: nat): Prop :=
    forall p bnd st A s s', wf_states s -> lookup_state s p = Some st -> afrag env A = true -> closed A = true ->
    unify env (S k) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f x A (Ongoing []) = Some (Ongoing [])).

(* Unify through a fold, step by step *)
Lemma fold_steps: forall (g: Unification -> EType -> option Unification) (Q: EType -> VariableStates -> Prop) cs s s',
    (forall x, g Failed x = Some Failed) ->
    (forall C, In C cs -> forall s0 s0', wf_states s0 -> g (Ongoing s0) C = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0) /\ Q C s0') ->
    wf_states s -> fold_unify g cs (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall C, In C cs -> exists s0', Q C s0' /\ (forall b, satisfies b s' -> satisfies b s0')).
Proof.
    intros g Q cs. induction cs as [|C cs IH]; intros s s' Hf Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros C [].
    - destruct (g (Ongoing s) C) as [[s1|]|] eqn:E;
          [|rewrite (fold_failed g cs (fun x _ => Hf x)) in H; discriminate H|discriminate H].
      destruct (Hstep C (or_introl eq_refl) s s1 Hs E) as [Hs1 [Hext1 HQ1]].
      destruct (IH s1 s' Hf (fun C' Hin => Hstep C' (or_intror Hin)) Hs1 H) as [Hs' [Hext Hall]].
      split; [exact Hs'|]. split; [intros b Hb; apply Hext1, Hext, Hb|].
      intros C' [<-|Hin].
      + exists s1. split; [exact HQ1|exact Hext].
      + exact (Hall C' Hin).
Qed.

Lemma find_first_found: forall (attempt: EType -> option Unification) l x u,
    find_first attempt l = Some (Some (x, u)) -> In x l /\ attempt x = Some (Ongoing u).
Proof.
    intros attempt l. induction l as [|y l IH]; intros x u H; simpl in H; [discriminate H|].
    destruct (attempt y) as [[w|]|] eqn:E; simpl in H; try discriminate H.
    - injection H as <- <-. split; [left; reflexivity|exact E].
    - destruct (IH x u H) as [Hin Ex]. split; [right; exact Hin|exact Ex].
Qed.

(* Of a class type as the target, unify reads the mutability it is assigned as only *)
Lemma unify_root_mutability: forall k m1 m2 cl args A carry, is_class A = true ->
    assignment_mutability env (RootResolved m1 cl args) = assignment_mutability env (RootResolved m2 cl args) ->
    unify env k (RootResolved m1 cl args) A carry = unify env k (RootResolved m2 cl args) A carry.
Proof.
    intros [|k] m1 m2 cl args A [s|] HA Hm; try reflexivity.
    destruct A as [ma ca aargs| | | | | |]; try discriminate HA.
    rewrite !unify_classes, Hm. reflexivity.
Qed.

(* Of a type variable as the target, the mutability given to it only rejects class types beyond it *)
Lemma unify_variable_mutability: forall k m nn q bnd A s s', is_class A = true ->
    unify env (S k) (TypeVariable (mkGenericRef (Some m) nn q bnd)) A (Ongoing s) = Some (Ongoing s') ->
    unify env (S k) (TypeVariable (mkGenericRef None false q bnd)) A (Ongoing s) = Some (Ongoing s').
Proof.
    intros k m nn q bnd A s s' HA H. destruct A as [ma ca aargs| | | | | |]; try discriminate HA.
    rewrite unify_step_once in H |- *. unfold unify_step, unify_type_variable in H |- *.
    match type of H with context [given_mutability_fits ?e ?x ?y] => destruct (given_mutability_fits e x y) end;
        [exact H|discriminate H].
Qed.

Let any_afrag := Inference.any_afrag env wf.
Let below_any := Inference.below_any env wf.
Let through_class := Inference.through_class env wf.
Let assigned_below_own := Inference.assigned_below_own env.

Lemma candidate_other: forall p c q, q <> p ->
    with_candidate env p c (TypeVariable (mkGenericRef None false q [])) = TypeVariable (mkGenericRef None false q []).
Proof.
    intros p c q Hq. unfold with_candidate. cbn [instantiate lookup_binding]. unfold param_eqb.
    rewrite (proj2 (Nat.eqb_neq q p) Hq). reflexivity.
Qed.

Lemma candidate_reference: forall p c gm nn q, q <> p ->
    with_candidate env p c (TypeVariable (mkGenericRef gm nn q [])) = TypeVariable (mkGenericRef gm nn q [])
    /\ with_candidate env p c (Nullable (TypeVariable (mkGenericRef gm nn q []))) = Nullable (TypeVariable (mkGenericRef gm nn q [])).
Proof.
    intros p c gm nn q Hq. unfold with_candidate. cbn [instantiate lookup_binding param_of]. unfold param_eqb.
    rewrite (proj2 (Nat.eqb_neq q p) Hq). split; reflexivity.
Qed.

(* The components of an intersection that is a static upper bound: class types, and type variables
   other than p *)
Lemma static_component_cases: forall p cs C, (forall C, In C cs -> compfrag env C = true) ->
    components_sfrag env (map to_generic cs) = true -> (forall g, In (TypeVariable g) cs -> param_of g <> p) -> In C cs ->
    (exists m cl args, C = RootResolved m cl args)
    \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p).
Proof.
    intros p cs C HSi Hcs Hnp Hin. destruct (components_sfrag_facts env _ Hcs) as [_ Hc].
    destruct (Hc (to_generic C) (in_map _ _ _ Hin)) as [Hsh _].
    destruct (compfrag_cases env C (HSi C Hin)) as [Hif|[gm [nn [q [-> _]]]]];
        [|right; exists gm, nn, q; split; [reflexivity|exact (Hnp _ Hin)]].
    destruct (ifrag_cases env wf C Hif) as [[m [cl [args [-> _]]]]|[[m_bot ->]|[[m [cl [args [-> _]]]]|[q [-> _]]]]].
    - left. eauto.
    - left. unfold bottom_type. eauto.
    - simpl in Hsh. discriminate Hsh.
    - right. exists None, false, q. split; [reflexivity|]. exact (Hnp _ Hin).
Qed.

(* An intersection that is a static upper bound, with the candidate for p: of the components with it,
   each of their common mutability *)
Lemma with_candidate_intersection: forall p c cs, 2 <= length cs ->
    (forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p)) ->
    (forall C, In C cs -> is_nullable env C = false) ->
    with_candidate env p c (Intersection cs)
    = Intersection (map (fun C => with_mutability env (assignment_mutability env (Intersection cs)) (with_candidate env p c C)) cs).
Proof.
    intros p c cs Hl Hcases Hn.
    assert (Hinst: forall C, In C cs -> intersected_components (with_candidate env p c C) = [with_candidate env p c C]
        /\ is_nullable env (with_candidate env p c C) = false /\ without_null env (with_candidate env p c C) = with_candidate env p c C
        /\ assignment_mutability env (with_candidate env p c C) = assignment_mutability env C).
    { intros C HC. destruct (Hcases C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> Hq]]]]].
      - unfold with_candidate. cbn [instantiate]. repeat split; reflexivity.
      - rewrite (proj1 (candidate_reference p c gm nn q Hq)). pose proof (Hn _ HC) as Hn'.
        repeat split; first [exact Hn'|reflexivity]. }
    assert (Hflat: forall l, (forall C, In C l -> In C cs) ->
        flat_map intersected_components (map (with_candidate env p c) l) = map (with_candidate env p c) l).
    { induction l as [|C l IH]; intros Hsub; [reflexivity|]. cbn [map flat_map].
      rewrite (proj1 (Hinst C (Hsub C (or_introl eq_refl)))), IH by (intros C' H'; apply Hsub; right; exact H'). reflexivity. }
    change (with_candidate env p c (Intersection cs)) with (intersect_instances env (map (with_candidate env p c) cs)).
    rewrite intersect_instances_plain.
    2:{ intros t Ht. apply in_map_iff in Ht. destruct Ht as [C [<- HC]].
        destruct (Hcases C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> Hq]]]]];
            [reflexivity|rewrite (proj1 (candidate_reference p c gm nn q Hq)); reflexivity]. }
    rewrite (Hflat cs (fun C H => H)).
    rewrite (of_components_many env (map (with_candidate env p c) cs)).
    - f_equal. rewrite map_map. apply map_ext_in. intros C HC.
      destruct (Hinst C HC) as [_ [_ [Hw _]]]. rewrite Hw. f_equal.
      unfold common_mutability. rewrite map_map. cbn [assignment_mutability]. f_equal.
      apply map_ext_in. intros C' HC'. exact (proj2 (proj2 (proj2 (Hinst C' HC')))).
    - rewrite length_map. exact Hl.
    - destruct cs as [|C1 cs']; [simpl in Hl; lia|]. cbn [map forallb].
      rewrite (proj1 (proj2 (Hinst C1 (or_introl eq_refl)))). reflexivity.
Qed.

(* The static check of a candidate c against an intersection that is its static upper bound, the
   assignee a (c, or c without null where the intersection is nullable): whatever class types satisfy
   the states it ends with, a is below the instance of each component with the candidate in it. Unify
   gives the components that aren't type variables a, and those that are what the others don't cover
   of it (Any of the mutability of a), or a itself. *)
Lemma static_components: forall n p cs c a s s', target_step n -> (forall k, k < n -> leaf_step k) ->
    (forall C, In C cs -> compfrag env C = true) -> components_sfrag env (map to_generic cs) = true ->
    (forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)) ->
    (forall g, In (TypeVariable g) cs -> param_of g <> p) ->
    afrag env c = true -> closed c = true -> afrag env a = true -> closed a = true -> wf_states s ->
    unify env n (with_candidate env p c (Intersection cs)) a (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ forall C, In C cs -> forall b K,
        bound_in env b K [] (to_generic (with_candidate env p c C)) = true -> satisfies b s' -> bindings_in_fragment env b ->
        exists f, unify env f (inst env b (with_candidate env p c C)) a (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p cs c a s s' IH IHleaf HSi Hcs Hunif Hnp Hc HcC Ha HaC Hs H.
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcomp]. rewrite length_map in Hlen.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p))
        by (intros C HC; exact (static_component_cases p cs C HSi Hcs Hnp HC)).
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hcomp _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> _]]]]]; [reflexivity|exact Hsh]. }
    rewrite (with_candidate_intersection p c cs Hlen Hcase Hnull) in H.
    set (m0 := assignment_mutability env (Intersection cs)) in *.
    set (w := fun C => with_mutability env m0 (with_candidate env p c C)) in H.
    destruct n as [|n1]; [discriminate H|].
    assert (IH1: target_step n1) by (apply (target_step_down n1 (S n1)); [lia|exact IH]).
    pose proof (afrag_in_fragment env a Ha) as Hcf.
    destruct (fragment_cases env a Hcf) as [[ma [ca [aargs Ea]]]|[ma [ca [aargs [Ea _]]]]]; subst a.
    2:{ (* a nullable assignee, for a non-null intersection *)
        assert (Hwn: is_nullable env (Intersection (map w cs)) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|]. apply (intersection_not_nullable env (map w (C0 :: cs0)) (w C0) (or_introl eq_refl)).
          unfold w. rewrite (proj1 (proj2 (with_mutability_keeps env ranked _ _))).
          destruct (Hcase C0 (or_introl eq_refl)) as [[m [cl [args ->]]]|[gm [nn [q [-> Hq]]]]].
          - unfold with_candidate. cbn [instantiate]. reflexivity.
          - rewrite (proj1 (candidate_reference p c gm nn q Hq)). exact (Hnull _ (or_introl eq_refl)). }
        rewrite unify_step_once in H. unfold unify_step, unify_intersection in H. rewrite Hwn in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step, unify_intersection, intersection_body in H. cbv zeta in H.
    (* what the components take *)
    set (Sound := fun C u => forall b K, bound_in env b K [] (to_generic (with_candidate env p c C)) = true ->
        satisfies b u -> exists f, unify env f (inst env b (with_candidate env p c C))
            (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing [])).
    assert (Hroot: forall C, In C cs -> is_type_variable (w C) = false -> forall s0 s0', wf_states s0 ->
        unify env n1 (w C) (RootResolved ma ca aargs) (Ongoing s0) = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0) /\ Sound C s0').
    { intros C HC Hv s0 s0' Hs0 E0. destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
      2:{ unfold w in Hv. rewrite EC, (proj1 (candidate_reference p c gm nn q Hq)) in Hv. discriminate Hv. }
      assert (Ew: unify env n1 (w C) (RootResolved ma ca aargs) (Ongoing s0)
          = unify env n1 (with_candidate env p c C) (RootResolved ma ca aargs) (Ongoing s0)).
      { pose proof (Hunif C HC) as Hu. fold m0 in Hu. unfold w. rewrite EC in Hu |- *. unfold with_candidate.
        cbn [instantiate with_mutability]. apply unify_root_mutability; [reflexivity|].
        cbn [assignment_mutability] in Hu |- *. destruct (is_const (declaration_of env cl)); [reflexivity|exact (eq_sym Hu)]. }
      rewrite Ew in E0.
      exact (IH1 _ _ s0 s0' (with_candidate_ifrag p _ Hc HcC C (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)))
          Ha HaC Hs0 E0). }
    set (ns := filter (fun x => negb (is_type_variable x)) (map w cs)) in H.
    set (vs := filter is_type_variable (map w cs)) in H.
    assert (Hns: forall x, In x ns -> forall s0 s0', wf_states s0 ->
        unify env n1 x (RootResolved ma ca aargs) (Ongoing s0) = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0) /\ (forall C, In C cs -> w C = x -> Sound C s0')).
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      apply in_map_iff in Hx. destruct Hx as [C0 [EC0 HC0]]. subst x.
      destruct (Hroot C0 HC0 Hv s0 s0' Hs0 E0) as [Hs0' [Hn0 _]].
      split; [exact Hs0'|]. split; [exact Hn0|]. intros C HC Ew. rewrite <- Ew in Hv, E0.
      exact (proj2 (proj2 (Hroot C HC Hv s0 s0' Hs0 E0))). }
    destruct (fold_unify (fun inner component => unify env n1 component (RootResolved ma ca aargs) inner) ns (Ongoing s))
        as [[s2|]|] eqn:E2; cbn beta iota in H; try discriminate H.
    destruct (fold_steps (fun inner x => unify env n1 x (RootResolved ma ca aargs) inner)
        (fun x u => forall C, In C cs -> w C = x -> Sound C u) ns s s2
        (fun x => unify_keeps_failure env n1 _ _) Hns Hs E2) as [Hs2 [Hn2 Hall2]].
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, wf_states s3 /\ (forall b, satisfies b s3 -> satisfies b s2)
        /\ afrag env na = true /\ closed na = true /\ is_class na = true
        /\ Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) (assignment_mutability env na) = true
        /\ (forall y f, in_fragment env y = true -> unify env f y na (Ongoing []) = Some (Ongoing []) ->
            exists f', unify env f' y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing []))
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component (RootResolved ma ca aargs) inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component (RootResolved ma ca aargs) (Ongoing s2)) ns)
          as [[[cov s3]|]|] eqn:E3; cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of c, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        destruct (Hns cov Hcov s2 s3 Hs2 Ecov) as [Hs3 [Hn3 _]].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        apply in_map_iff in Hcov. destruct Hcov as [C1 [EC1 HC1]].
        destruct (Hcase C1 HC1) as [[m1 [cl1 [args1 EC]]]|[gm [nn [q [EC Hq]]]]].
        2:{ subst cov. unfold w in Hv. rewrite EC, (proj1 (candidate_reference p c gm nn q Hq)) in Hv. discriminate Hv. }
        assert (Ecov': exists mc argsc, cov = RootResolved mc cl1 argsc).
        { subst cov. unfold w. rewrite EC. unfold with_candidate. cbn [instantiate with_mutability]. eauto. }
        destruct Ecov' as [mc [argsc ->]].
        cbn [is_nullable] in H.
        set (m' := intersect_mutability (mutability_of env (RootResolved ma ca aargs)) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) m' = true).
        { unfold m'. apply Ops.intersect_mutability_greatest; [exact (assigned_below_own (RootResolved ma ca aargs) eq_refl)|].
          destruct n1 as [|n2]; [discriminate Ecov|]. rewrite unify_classes in Ecov.
          destruct (base_type_is_subtype_of env ca cl1); [|discriminate Ecov].
          destruct (Model.is_subtype_of _ _) eqn:Em; [|discriminate Ecov].
          exact (mutability_trans _ _ _ Em (assigned_below_own (RootResolved mc cl1 argsc) eq_refl)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hn3|].
        destruct (any_afrag m') as [Haf Hac]. split; [exact Haf|]. split; [exact Hac|]. split; [reflexivity|].
        split; [cbn [assignment_mutability]; rewrite (wf_any_is_not_const env wf); exact Hm'|].
        split; [|exact H].
        intros y f Hy Ey. apply (through_class _ (RootResolved (Some m') any []) y 1 f Hcf (afrag_in_fragment env _ Haf) Hy); [|exact Ey].
        apply below_any. exact Hm'.
      - (* nothing covers: the variables take c *)
        exists (RootResolved ma ca aargs), s2. split; [exact Hs2|]. split; [auto|].
        split; [exact Ha|]. split; [exact HaC|]. split; [reflexivity|]. split; [apply mutability_is_subtype_of_refl|].
        split; [intros y f _ Ey; exists f; exact Ey|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hn3 [Hnaf [Hnac [Hnacl [Hnam [Hthrough Hfold]]]]]]]]].
    assert (Hvs: forall x, In x vs -> forall s0 s0', wf_states s0 ->
        match unify env n1 x na (Ongoing s0) with
        | Some Failed => unify env n1 x (RootResolved ma ca aargs) (Ongoing s0)
        | r => r
        end = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0)
        /\ (forall nn q, x = TypeVariable (mkGenericRef (Some m0) nn q []) ->
            Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) m0 = true
            /\ forall o y, xfrag y -> in_fragment env y = true -> (forall st', lookup_state s0' q = Some st' -> fits st' o y) ->
            exists f, unify env f y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing []))).
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      apply in_map_iff in Hx. destruct Hx as [C0 [EC0 HC0]].
      destruct (Hcase C0 HC0) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
      { subst x. unfold w in Hv. rewrite EC in Hv. unfold with_candidate in Hv. cbn in Hv. discriminate Hv. }
      assert (Ex: x = TypeVariable (mkGenericRef (Some m0) nn q [])).
      { subst x. unfold w. rewrite EC, (proj1 (candidate_reference p c gm nn q Hq)). reflexivity. }
      rewrite Ex in E0 |- *. destruct n1 as [|n2]; [discriminate E0|].
      assert (Hleaf: leaf_step n2) by (apply IHleaf; lia).
      (* the variable takes A, of the types of the arguments, through which it takes c *)
      assert (Hone: forall A, afrag env A = true -> closed A = true -> is_class A = true ->
          (forall y f, in_fragment env y = true -> unify env f y A (Ongoing []) = Some (Ongoing []) ->
              exists f', unify env f' y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing [])) ->
          Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) (assignment_mutability env A) = true ->
          unify env (S n2) (TypeVariable (mkGenericRef (Some m0) nn q [])) A (Ongoing s0) = Some (Ongoing s0') ->
          wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0)
          /\ (forall nn' q', TypeVariable (mkGenericRef (Some m0) nn q []) = TypeVariable (mkGenericRef (Some m0) nn' q' []) ->
              Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) m0 = true
              /\ forall o y, xfrag y -> in_fragment env y = true -> (forall st', lookup_state s0' q' = Some st' -> fits st' o y) ->
              exists f, unify env f y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing []))).
      { intros A HAf HAc HAk Hthr HAm EA.
        (* the mutability given to the variable admits A only *)
        assert (Hfit0: Model.is_subtype_of (assignment_mutability env A) m0 = true).
        { destruct A as [ma' ca' aargs'| | | | | |]; try discriminate HAk. pose proof EA as EA0.
          rewrite unify_step_once in EA0. unfold unify_step, unify_type_variable in EA0.
          match type of EA0 with context [given_mutability_fits ?e ?x ?y] => destruct (given_mutability_fits e x y) eqn:Eg end;
              [exact Eg|discriminate EA0]. }
        apply (unify_variable_mutability n2 m0 nn q [] A s0 s0' HAk) in EA.
        destruct (state_of_target n2 q [] A s0 s0' (afrag_in_fragment env A HAf) EA) as [st0 Hl0].
        destruct (Hleaf q [] st0 A s0 s0' Hs0 Hl0 HAf HAc EA) as [Hs0' [Hn0 Hsnd]].
        split; [exact Hs0'|]. split; [exact Hn0|].
        intros nn' q' Eq. injection Eq as <- <-. split; [exact (mutability_trans _ _ _ HAm Hfit0)|].
        intros o y Hy Hyf Hfit. destruct (Hsnd o y Hy Hfit) as [f Ef]. exact (Hthr y f Hyf Ef). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef (Some m0) nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena;
          try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->. exact (Hone na Hnaf Hnac Hnacl Hthrough Hnam Ena).
      - exact (Hone (RootResolved ma ca aargs) Ha HaC eq_refl (fun y f _ Ey => ex_intro _ f Ey) (mutability_is_subtype_of_refl _) E0). }
    set (gv := fun inner x => match unify env n1 x na inner with
        | Some Failed => unify env n1 x (RootResolved ma ca aargs) inner
        | r => r
        end) in Hfold.
    assert (Hgf: forall x, gv Failed x = Some Failed).
    { intros x. unfold gv. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    destruct (fold_steps gv (fun x u => forall nn q, x = TypeVariable (mkGenericRef (Some m0) nn q []) ->
            Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) m0 = true /\ forall o y, xfrag y ->
            in_fragment env y = true -> (forall st', lookup_state u q = Some st' -> fits st' o y) ->
            exists f, unify env f y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing [])) vs s3 s'
        Hgf Hvs Hs3 Hfold)
        as [Hs' [Hn' Hallv]].
    split; [exact Hs'|]. split; [intros b Hb; apply Hn2, Hn3, Hn', Hb|].
    intros C HC b K Hb Hsat Hbf.
    destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
    - (* a class type *)
      assert (Hin: In (w C) ns).
      { apply filter_In. split; [exact (in_map w cs C HC)|]. unfold w. rewrite EC. unfold with_candidate. reflexivity. }
      destruct (Hall2 _ Hin) as [u [HQ Hnu]].
      exact (HQ C HC eq_refl b K Hb (Hnu b (Hn3 b (Hn' b Hsat)))).
    - (* a type variable, narrowed or not *)
      assert (Hin: In (w C) vs).
      { apply filter_In. split; [exact (in_map w cs C HC)|]. unfold w. rewrite EC, (proj1 (candidate_reference p c gm nn q Hq)). reflexivity. }
      destruct (Hallv _ Hin) as [u [HQ Hnu]].
      rewrite EC, (proj1 (candidate_reference p c gm nn q Hq)) in Hb |- *.
      destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) Hb) as [o [y [Ey _]]]. cbn [param_of] in Ey.
      destruct (Hnu b Hsat q o y Ey) as [Hy [st' [Hl' Hfit]]].
      assert (Hfits: forall st'', lookup_state u q = Some st'' -> fits st'' o y)
          by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
      assert (Ew: w C = TypeVariable (mkGenericRef (Some m0) nn q [])).
      { unfold w. rewrite EC, (proj1 (candidate_reference p c gm nn q Hq)). reflexivity. }
      destruct (HQ nn q Ew) as [Ham HQy]. destruct (HQy o y Hy (Hbf q o y Ey) Hfits) as [f Ef].
      (* the type it stands for, of the mutability given to it and without null where it is narrowed *)
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ey)). exists f.
      apply (class_reference_takes env f gm nn y _ [] (Hbf q o y Ey) Hcf); [|intros _; reflexivity|exact Ef].
      (* the common mutability is no more than that given to it *)
      intros m' Em. apply (mutability_trans _ _ _ Ham). pose proof (Hunif C HC) as Hu. fold m0 in Hu. rewrite <- Hu, EC.
      exact (compfrag_given env wf gm nn q m' ltac:(rewrite <- EC; exact (HSi C HC)) Em).
Qed.


(* A type variable of a mutability given to it, narrowed or not: the plain variable takes A, and the
   type it stands for, of that mutability and without null where it is narrowed, takes A *)
Lemma reference_step: forall k gm nn q A s s', leaf_step k -> sfrag env (Generic (mkGenericRef gm nn q [])) = true ->
    afrag env A = true -> closed A = true -> wf_states s ->
    unify env (S k) (TypeVariable (mkGenericRef gm nn q [])) A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
    /\ (forall b o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> satisfies b s' ->
        exists f, unify env f (ref_apply env gm nn x) A (Ongoing []) = Some (Ongoing [])).
Proof.
    intros k gm nn q A s s' Hleaf Hsf HA HcA Hs H0. pose proof (afrag_in_fragment env A HA) as HA'.
    destruct (fragment_cases env A HA') as [[ma [ca [aa E0]]]|[ma [ca [aa [E0 _]]]]]; subst A;
    (destruct ((fun HS => unify_variable_given env wf k gm nn q _ s s' HS H0) I) as [H1 [Hgm Hnul]];
     destruct (state_of_target k q [] _ s s' HA' H1) as [st Hl];
     destruct (Hleaf q [] st _ s s' Hs Hl HA HcA H1) as [Hs' [Hext Hsound]];
     split; [exact Hs'|]; split; [exact Hext|]; intros b o x Ex Hsb;
     destruct (Hsb q o x Ex) as [Hx [st' [Hl' Hfit]]];
     assert (Hfits: forall st'', lookup_state s' q = Some st'' -> fits st'' o x)
         by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit);
     destruct (Hsound o x Hx Hfits) as [f Hf];
     apply (reference_takes gm nn x _ f Hx HA' Hgm); [|exact Hf];
     intros En; subst nn; destruct (is_nullable env _) eqn:EA; [|reflexivity];
     rewrite (narrowed_not_nullable env wf gm q Hsf) in Hnul; discriminate (Hnul eq_refl)).
Qed.

(* The static check of a candidate c against the static upper bound S as a whole: whatever bindings
   satisfy the states it ends with, c is below the instance of each component of S; of an
   intersection, nullable or not, where the bindings are class types (static_components). *)
Lemma static_whole: forall n p S c s s', target_step n -> (forall k, k < n -> leaf_step k) ->
    (forall C, In C (intersected_components S) -> pfrag env C = true) -> static_form p S ->
    afrag env c = true -> closed c = true -> wf_states s ->
    unify env n (with_candidate env p c S) c (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ forall C, In C (intersected_components S) -> forall b K,
        bound_in env b K [] (to_generic (with_candidate env p c C)) = true -> satisfies b s' ->
        ((exists cs, inter_of S = Some cs) -> bindings_in_fragment env b) ->
        exists f, unify env f (inst env b (with_candidate env p c C)) c (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p S c s s' IH IHleaf HSi Hform Hc HcC Hs H.
    assert (Hcases: intersected_components S = [S] \/ (exists cs, S = Intersection cs) \/ (exists cs, S = Nullable (Intersection cs))).
    { destruct S as [m c' args|[| | | | | |cs]|g|me msg|v o x|g|cs]; try (left; reflexivity); right; [right|left]; exists cs; reflexivity. }
    destruct Hcases as [E|[[cs ->]|[cs ->]]].
    - rewrite E in HSi |- *.
      destruct (pfrag_cases env S (HSi S (or_introl eq_refl))) as [HS|[[gm [nn [q [ES [Hsf _]]]]]|[gm [nn [q [ES [Hsf _]]]]]]].
      + (* no intersection: as any other type of the parameters *)
        pose proof (with_candidate_ifrag p c Hc HcC S HS) as Hw.
        destruct (IH _ c s s' Hw Hc HcC Hs H) as [Hs' [Hn' Hsnd]].
        split; [exact Hs'|]. split; [exact Hn'|].
        intros C [<-|[]] b K Hb Hsat _. exact (Hsnd b K Hb Hsat).
      + (* a type variable of a mutability given to it, narrowed or not: the type it stands for so *)
        subst S. pose proof (proj2 Hform gm nn q (or_introl eq_refl)) as Hq.
        rewrite (proj1 (candidate_reference p c gm nn q Hq)) in H.
        destruct n as [|n]; [discriminate H|].
        destruct (reference_step n gm nn q c s s' (IHleaf n (Nat.lt_succ_diag_r n)) Hsf Hc HcC Hs H) as [Hs' [Hn' Hsnd]].
        split; [exact Hs'|]. split; [exact Hn'|].
        intros C [<-|[]] b K Hb Hsat _. rewrite (proj1 (candidate_reference p c gm nn q Hq)) in Hb |- *.
        destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)). exact (Hsnd b o x Ex Hsat).
      + (* made nullable: the variable takes the candidate without null *)
        subst S. pose proof (proj2 Hform gm nn q (or_intror eq_refl)) as Hq.
        rewrite (proj2 (candidate_reference p c gm nn q Hq)) in H.
        pose proof (afrag_in_fragment env c Hc) as Hcf.
        destruct n as [|n]; [discriminate H|].
        assert (H0: unify env n (TypeVariable (mkGenericRef gm nn q [])) (without_null env c) (Ongoing s) = Some (Ongoing s')).
        { destruct (fragment_cases env c Hcf) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
              [rewrite unify_nullable_class in H|rewrite unify_nullable_nullable in H]; exact H. }
        destruct (without_null_afrag env c Hc) as [HA0 HcA0]. rewrite <- HcA0 in HcC.
        destruct n as [|n]; [discriminate H0|].
        destruct (reference_step n gm nn q _ s s' (IHleaf n ltac:(lia)) Hsf HA0 HcC Hs H0) as [Hs' [Hn' Hsnd]].
        split; [exact Hs'|]. split; [exact Hn'|].
        intros C [<-|[]] b K Hb Hsat _. rewrite (proj2 (candidate_reference p c gm nn q Hq)) in Hb |- *.
        destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsnd b o x Ex Hsat) as [f Hf].
        rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ex)). exists (S f). exact (unify_rewrap_target env _ _ c [] _ Hcf Hf).
    - destruct (proj1 Hform cs eq_refl) as [HSi0 [Hcs [Hunif Hnp]]]. clear HSi. rename HSi0 into HSi.
      cbn [intersected_components] in HSi |- *.
      destruct (static_components n p cs c c s s' IH IHleaf HSi Hcs Hunif Hnp Hc HcC Hc HcC Hs H) as [Hs' [Hn' Hall]].
      split; [exact Hs'|]. split; [exact Hn'|].
      intros C HC b K Hb Hsat Hbf. exact (Hall C HC b K Hb Hsat (Hbf (ex_intro _ cs eq_refl))).
    - (* a nullable intersection: of the candidate without null, the components made nullable *)
      destruct (proj1 Hform cs eq_refl) as [HSi0 [Hcs [Hunif Hnp]]]. clear HSi. rename HSi0 into HSi.
      cbn [intersected_components].
      destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcomp]. rewrite length_map in Hlen.
      assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
          \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p))
          by (intros C HC; exact (static_component_cases p cs C HSi Hcs Hnp HC)).
      assert (Hnull: forall C, In C cs -> is_nullable env C = false).
      { intros C HC. destruct (Hcomp _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
        apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
        destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> _]]]]]; [reflexivity|exact Hsh]. }
      pose proof (afrag_in_fragment env c Hc) as Hcf.
      assert (HA0: afrag env (without_null env c) = true /\ closed (without_null env c) = true).
      { destruct (fragment_cases env c Hcf) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HR]]]]];
            [exact (conj Hc HcC)|split; [exact HR|exact HcC]]. }
      change (with_candidate env p c (Nullable (Intersection cs))) with (rewrap_nullable (with_candidate env p c (Intersection cs))) in H.
      rewrite (with_candidate_intersection p c cs Hlen Hcase Hnull) in H. cbn [rewrap_nullable] in H.
      destruct n as [|n]; [discriminate H|].
      rewrite (unify_nullable_target env n _ c s Hcf) in H. rewrite <- (with_candidate_intersection p c cs Hlen Hcase Hnull) in H.
      destruct (static_components n p cs c _ s s' (target_step_down n (S n) (le_S _ _ (le_n _)) IH)
          (fun k Hk => IHleaf k ltac:(lia)) HSi Hcs Hunif Hnp Hc HcC (proj1 HA0) (proj2 HA0) Hs H)
          as [Hs' [Hn' Hall]].
      split; [exact Hs'|]. split; [exact Hn'|].
      intros C' HC' b K Hb Hsat Hbf. apply in_map_iff in HC'. destruct HC' as [C [<- HC]].
      destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]]; subst C.
      + destruct (Hall _ HC b K Hb Hsat (Hbf (ex_intro _ cs eq_refl))) as [f Hf].
        exists (S f). exact (unify_rewrap_target env _ _ c [] _ Hcf Hf).
      + (* a type variable, made nullable: the type it stands for takes the candidate without null *)
        rewrite (proj2 (candidate_reference p c gm nn q Hq)) in Hb |- *.
        destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        pose proof (Hall _ HC b K) as Hq'. rewrite (proj1 (candidate_reference p c gm nn q Hq)) in Hq'.
        destruct (Hq' Hb Hsat (Hbf (ex_intro _ cs eq_refl))) as [f Hf].
        rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)) in Hf.
        rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ex)). exists (S f). exact (unify_rewrap_target env _ _ c [] _ Hcf Hf).
Qed.

Let param_component_cases := Inference.param_component_cases env wf.

(* An intersection as the type of a parameter, of the argument a (a without null, where the intersection
   is nullable): whatever class types satisfy the states unify ends with, a is below the instance of each
   component, as of a static upper bound (static_components), the components as they are *)
Lemma param_components: forall n cs a s s', target_step n -> (forall k, k < n -> leaf_step k) ->
    (forall C, In C cs -> compfrag env C = true) -> components_sfrag env (map to_generic cs) = true ->
    afrag env a = true -> closed a = true -> wf_states s ->
    unify env n (Intersection cs) a (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ forall C, In C cs -> forall b K, bound_in env b K [] (to_generic C) = true -> satisfies b s' -> bindings_in_fragment env b ->
        exists f, unify env f (inst env b C) a (Ongoing []) = Some (Ongoing []).
Proof.
    intros n cs a s s' IH IHleaf HSi Hcs Ha HaC Hs H.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q [])))
        by (intros C HC; exact (param_component_cases cs C HSi Hcs HC)).
    destruct n as [|n1]; [discriminate H|].
    assert (IH1: target_step n1) by (apply (target_step_down n1 (S n1)); [lia|exact IH]).
    pose proof (afrag_in_fragment env a Ha) as Hcf.
    destruct (fragment_cases env a Hcf) as [[ma [ca [aargs Ea]]]|[ma [ca [aargs [Ea _]]]]]; subst a.
    2:{ (* a nullable argument, for a non-null intersection *)
        destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcomp]. rewrite length_map in Hlen.
        assert (Hin: is_nullable env (Intersection cs) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|]. apply (intersection_not_nullable env (C0 :: cs0) C0 (or_introl eq_refl)).
          destruct (Hcomp _ (in_map to_generic (C0 :: cs0) C0 (or_introl eq_refl))) as [Hsh _]. unfold is_component_shape in Hsh.
          apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
          destruct (Hcase C0 (or_introl eq_refl)) as [[m [cl [args ->]]]|[gm [nn [q ->]]]]; [reflexivity|exact Hsh]. }
        rewrite unify_step_once in H. unfold unify_step, unify_intersection in H. rewrite Hin in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step, unify_intersection, intersection_body in H. cbv zeta in H.
    (* what the components take *)
    set (Sound := fun C u => forall b K, bound_in env b K [] (to_generic C) = true ->
        satisfies b u -> exists f, unify env f (inst env b C) (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing [])).
    set (ns := filter (fun x => negb (is_type_variable x)) cs) in H.
    set (vs := filter is_type_variable cs) in H.
    assert (Hns: forall x, In x ns -> forall s0 s0', wf_states s0 ->
        unify env n1 x (RootResolved ma ca aargs) (Ongoing s0) = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0) /\ Sound x s0').
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      exact (IH1 _ _ s0 s0' (compfrag_ifrag env x (HSi x Hx) Hv) Ha HaC Hs0 E0). }
    destruct (fold_unify (fun inner component => unify env n1 component (RootResolved ma ca aargs) inner) ns (Ongoing s))
        as [[s2|]|] eqn:E2; cbn beta iota in H; try discriminate H.
    destruct (fold_steps (fun inner x => unify env n1 x (RootResolved ma ca aargs) inner) Sound ns s s2
        (fun x => unify_keeps_failure env n1 _ _) Hns Hs E2) as [Hs2 [Hn2 Hall2]].
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, wf_states s3 /\ (forall b, satisfies b s3 -> satisfies b s2)
        /\ afrag env na = true /\ closed na = true /\ is_class na = true
        /\ Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) (assignment_mutability env na) = true
        /\ (forall y f, in_fragment env y = true -> unify env f y na (Ongoing []) = Some (Ongoing []) ->
            exists f', unify env f' y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing []))
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component (RootResolved ma ca aargs) inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component (RootResolved ma ca aargs) (Ongoing s2)) ns)
          as [[[cov s3]|]|] eqn:E3; cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of a, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        destruct (Hns cov Hcov s2 s3 Hs2 Ecov) as [Hs3 [Hn3 _]].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        destruct (Hcase cov Hcov) as [[mc [cl1 [argsc ->]]]|[gm [nn [q ->]]]]; [|discriminate Hv].
        cbn [is_nullable] in H.
        set (m' := intersect_mutability (mutability_of env (RootResolved ma ca aargs)) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) m' = true).
        { unfold m'. apply Ops.intersect_mutability_greatest; [exact (assigned_below_own (RootResolved ma ca aargs) eq_refl)|].
          destruct n1 as [|n2]; [discriminate Ecov|]. rewrite unify_classes in Ecov.
          destruct (base_type_is_subtype_of env ca cl1); [|discriminate Ecov].
          destruct (Model.is_subtype_of _ _) eqn:Em; [|discriminate Ecov].
          exact (mutability_trans _ _ _ Em (assigned_below_own (RootResolved mc cl1 argsc) eq_refl)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hn3|].
        destruct (any_afrag m') as [Haf Hac]. split; [exact Haf|]. split; [exact Hac|]. split; [reflexivity|].
        split; [cbn [assignment_mutability]; rewrite (wf_any_is_not_const env wf); exact Hm'|].
        split; [|exact H].
        intros y f Hy Ey. apply (through_class _ (RootResolved (Some m') any []) y 1 f Hcf (afrag_in_fragment env _ Haf) Hy); [|exact Ey].
        apply below_any. exact Hm'.
      - (* nothing covers: the variables take a *)
        exists (RootResolved ma ca aargs), s2. split; [exact Hs2|]. split; [auto|].
        split; [exact Ha|]. split; [exact HaC|]. split; [reflexivity|]. split; [apply mutability_is_subtype_of_refl|].
        split; [intros y f _ Ey; exists f; exact Ey|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hn3 [Hnaf [Hnac [Hnacl [Hnam [Hthrough Hfold]]]]]]]]].
    set (VSound := fun x u => forall gm nn q, x = TypeVariable (mkGenericRef gm nn q []) ->
        (forall m, gm = Some m -> Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) m = true)
        /\ forall o y, xfrag y -> in_fragment env y = true -> (forall st', lookup_state u q = Some st' -> fits st' o y) ->
            exists f, unify env f y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing [])).
    assert (Hvs: forall x, In x vs -> forall s0 s0', wf_states s0 ->
        match unify env n1 x na (Ongoing s0) with
        | Some Failed => unify env n1 x (RootResolved ma ca aargs) (Ongoing s0)
        | r => r
        end = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0) /\ VSound x s0').
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      destruct (Hcase x Hx) as [[m [cl [args ->]]]|[gm [nn [q ->]]]]; [discriminate Hv|].
      destruct n1 as [|n2]; [discriminate E0|].
      assert (Hleaf: leaf_step n2) by (apply IHleaf; lia).
      (* the variable takes A, of the types of the arguments, through which it takes a *)
      assert (Hone: forall A, afrag env A = true -> closed A = true -> is_class A = true ->
          (forall y f, in_fragment env y = true -> unify env f y A (Ongoing []) = Some (Ongoing []) ->
              exists f', unify env f' y (RootResolved ma ca aargs) (Ongoing []) = Some (Ongoing [])) ->
          Model.is_subtype_of (assignment_mutability env (RootResolved ma ca aargs)) (assignment_mutability env A) = true ->
          unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) A (Ongoing s0) = Some (Ongoing s0') ->
          wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0) /\ VSound (TypeVariable (mkGenericRef gm nn q [])) s0').
      { intros A HAf HAc HAk Hthr HAm EA.
        assert (Hsh: match A with Error _ _ | TypeVariable _ => False | _ => True end)
            by (destruct A; try discriminate HAk; exact I).
        assert (HAa: assignee_mutability env A = assignment_mutability env A) by (destruct A; try discriminate HAk; reflexivity).
        destruct (unify_variable_given env wf n2 gm nn q A s0 s0' Hsh EA) as [EA' [Hgm _]].
        destruct (state_of_target n2 q [] A s0 s0' (afrag_in_fragment env A HAf) EA') as [st0 Hl0].
        destruct (Hleaf q [] st0 A s0 s0' Hs0 Hl0 HAf HAc EA') as [Hs0' [Hn0 Hsnd]].
        split; [exact Hs0'|]. split; [exact Hn0|].
        intros gm' nn' q' Eq. injection Eq as <- <- <-. split.
        - intros m Em. pose proof (Hgm m Em) as Hm. rewrite HAa in Hm. exact (mutability_trans _ _ _ HAm Hm).
        - intros o y Hy Hyf Hfit. destruct (Hsnd o y Hy Hfit) as [f Ef]. exact (Hthr y f Hyf Ef). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena;
          try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->. exact (Hone na Hnaf Hnac Hnacl Hthrough Hnam Ena).
      - exact (Hone (RootResolved ma ca aargs) Ha HaC eq_refl (fun y f _ Ey => ex_intro _ f Ey) (mutability_is_subtype_of_refl _) E0). }
    set (gv := fun inner x => match unify env n1 x na inner with
        | Some Failed => unify env n1 x (RootResolved ma ca aargs) inner
        | r => r
        end) in Hfold.
    assert (Hgf: forall x, gv Failed x = Some Failed).
    { intros x. unfold gv. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    destruct (fold_steps gv VSound vs s3 s' Hgf Hvs Hs3 Hfold) as [Hs' [Hn' Hallv]].
    split; [exact Hs'|]. split; [intros b Hb; apply Hn2, Hn3, Hn', Hb|].
    intros C HC b K Hb Hsat Hbf.
    destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
    - (* a class type *)
      assert (Hin: In C ns) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]).
      destruct (Hall2 _ Hin) as [u [HQ Hnu]].
      exact (HQ b K Hb (Hnu b (Hn3 b (Hn' b Hsat)))).
    - (* a type variable: the type it stands for, of the mutability given to it and without null where it is narrowed *)
      assert (Hin: In C vs) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]).
      destruct (Hallv _ Hin) as [u [HQ Hnu]].
      rewrite EC in Hb |- *.
      destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) Hb) as [o [y [Ey _]]]. cbn [param_of] in Ey.
      destruct (Hnu b Hsat q o y Ey) as [Hy [st' [Hl' Hfit]]].
      assert (Hfits: forall st'', lookup_state u q = Some st'' -> fits st'' o y)
          by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
      destruct (HQ gm nn q EC) as [Ham HQy]. destruct (HQy o y Hy (Hbf q o y Ey) Hfits) as [f Ef].
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ey)). exists f.
      apply (class_reference_takes env f gm nn y _ [] (Hbf q o y Ey) Hcf Ham); [intros _; reflexivity|exact Ef].
Qed.

Let below_intersection_instance := Inference.below_intersection_instance env wf.

Lemma leaf_all: forall n, target_step n -> leaf_step n.
Proof.
    induction n as [n IHn] using lt_wf_ind. intros IH.
    assert (IHleaf: forall k, k < n -> leaf_step k)
        by (intros k Hk; exact (IHn k Hk (target_step_down k n (Nat.lt_le_incl _ _ Hk) IH))).
    intros p bnd st A s s' Hs Hl HAf HcA H. destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
    pose proof (afrag_in_fragment env A HAf) as HA.
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
                  ((exists cs, inter_of (static_upper_bound st) = Some cs) -> bindings_in_fragment env b) ->
                  exists f, unify env f (inst env b (with_candidate env p c C)) c (Ongoing []) = Some (Ongoing []))).
      { unfold plus_static_check in E2. destruct (no_vars (static_upper_bound st)) eqn:Ens.
        - injection E2 as <-. split; [exact Hs|]. split; [auto|]. split; [exact Hl|]. intros E'; discriminate E'.
        - unfold static_ok in Hok. rewrite Ens in Hok. destruct Hok as [HlA [HlC [HSi [_ [Hform _]]]]].
          destruct (supertype_of_classes _ _ HlA HlC HAf HcA) as [HcF HcC].
          destruct (static_whole n p (static_upper_bound st) c s s2 IH IHleaf HSi Hform HcF HcC Hs E2) as [Hs2 [Hn2 Hall]].
          destruct (unify_keeps_from env wf intersect_no_vars supertype_no_vars n (parameter_rank env p) _ c s s2 (wf_ranked s Hs)
              (or_intror (conj (candidate_below env wf p c _ Hsv Hnc) Hnc)) E2) as [Kf _].
          split; [exact Hs2|]. split; [exact Hn2|]. split; [rewrite (Kf p (le_n _)); exact Hl|].
          intros _. split; [exact HcF|]. split; [exact HcC|]. exact Hall. }
      destruct Hcheck as [Hs2 [Hn2 [Hl2 Hchk]]].
      pose proof (satisfies_set_state s2 p st st' Hl2 Hfit') as Hn'.
      split; [|split; [intros b Hb; exact (Hn2 b (Hn' b Hb))|]].
      + apply (wf_set_state s2 p st' Hs2 Hn' Hnu Hnc); [|exact Hsv].
        intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact Hbu|]. split; [exact (supertype_bfrag _ _ Hbl HA)|].
        unfold static_ok. unfold st'. cbn [static_upper_bound lower_bound upper_bound].
        destruct (no_vars (static_upper_bound st)) eqn:Ens.
        * unfold static_ok in Hok. rewrite Ens in Hok. exact Hok.
        * destruct (Hchk eq_refl) as [HcF [HcC Hsnd]]. unfold static_ok in Hok. rewrite Ens in Hok.
          destruct Hok as [_ [_ [HSi [HSo [Hform _]]]]].
          split; [exact HcF|]. split; [exact HcC|]. split; [exact HSi|]. split; [exact HSo|]. split; [exact Hform|].
          intros _ C HC b K Hb Hsat Hbf. exact (Hsnd C HC b K Hb (Hn' b Hsat) Hbf).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s2 p _)). unfold fits in Hfit. unfold st' in Hfit.
        cbn [is_exact lower_bound] in Hfit.
        destruct Hfit as [[K1 E1] _]. exact (proj2 (supertype_is_above _ _ x K1 Hbl HA Hx E1)).
Qed.

Lemma target_leaf: forall n p bnd st A s s', target_step n ->
    wf_states s -> lookup_state s p = Some st -> afrag env A = true -> closed A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f x A (Ongoing []) = Some (Ongoing [])).
Proof. intros n p bnd st A s s' IH. exact (leaf_all n IH p bnd st A s s'). Qed.

(* What the variable is assigned to: below the upper bound, which is below it *)
Lemma assignee_leaf: forall n gm nn p bnd st A s s', wf_states s -> lookup_state s p = Some st -> in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef gm nn p bnd)) (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f A x (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n gm nn p bnd st A s s' Hs Hl HA H. destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
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
        * destruct Hok as [H1 [H2 [H3 [H4 [H5 H6]]]]]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
          split; [exact H5|]. intros Hnn' C HC b K Hb Hsat. exact (H6 Hnn' C HC b K Hb (Hn' b Hsat)).
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

Lemma state_of_assignee: forall n gm nn p bnd A s r, in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef gm nn p bnd)) (Ongoing s) = Some (Ongoing r) -> exists st, lookup_state s p = Some st.
Proof.
    intros n gm nn p bnd A s r HA H. destruct (lookup_state s p) as [st|] eqn:E; [eauto|exfalso].
    rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_root_resolved, unify_nullable, type_variable_flipped_unify, plus_subtype_constraint in H;
        rewrite E in H; discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Soundness                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* A type variable of a mutability given to it, narrowed or made nullable, in a type argument: as the
   target, as for the type of a parameter (parameter_step), *)
Lemma nested_target_step: forall n, target_step n -> forall gm nn q P A s s', sfrag env (Generic (mkGenericRef gm nn q [])) = true ->
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    afrag env A = true -> closed A = true -> wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
    /\ (forall b o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> satisfies b s' ->
        exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n IH gm nn q P A s s' Hsf EP HA HcA Hs H. pose proof (afrag_in_fragment env A HA) as HA'.
    assert (Hstep: forall k A0, k <= n -> afrag env A0 = true -> closed A0 = true ->
        unify env (S k) (TypeVariable (mkGenericRef gm nn q [])) A0 (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> satisfies b s' ->
            exists f, unify env f (ref_apply env gm nn x) A0 (Ongoing []) = Some (Ongoing []))).
    { intros k A0 Hk HA0 HcA0 H0.
      exact (reference_step k gm nn q A0 s s' (leaf_all k (target_step_down k n Hk IH)) Hsf HA0 HcA0 Hs H0). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A ltac:(lia) HA HcA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros b o x Ex Hsb.
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)). exact (Hsnd b o x Ex Hsb).
    - destruct n as [|n]; [discriminate H|].
      assert (H0: unify env n (TypeVariable (mkGenericRef gm nn q [])) (without_null env A) (Ongoing s) = Some (Ongoing s')).
      { destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [rewrite unify_nullable_class in H|rewrite unify_nullable_nullable in H]; exact H. }
      destruct (without_null_afrag env A HA) as [HA0 HcA0]. rewrite <- HcA0 in HcA.
      destruct n as [|n]; [discriminate H0|].
      destruct (Hstep n _ ltac:(lia) HA0 HcA H0) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros b o x Ex Hsb.
      destruct (Hsnd b o x Ex Hsb) as [f Hf].
      rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ex)). exists (S f). exact (unify_rewrap_target env _ _ A [] _ HA' Hf).
Qed.

(* A nullable class type takes the nullable form of what the class type takes *)
Lemma unify_rewrap_assignee: forall f m c args y, unify env f (RootResolved m c args) y (Ongoing []) = Some (Ongoing []) ->
    unify env (S f) (Nullable (RootResolved m c args)) (rewrap_nullable y) (Ongoing []) = Some (Ongoing []).
Proof.
    intros f m c args [| y | | | | |] H; cbn [rewrap_nullable]; rewrite unify_nullable_nullable; try exact H.
    destruct f as [|f]; [discriminate H|]. rewrite unify_class_nullable in H. discriminate H.
Qed.

(* ... and as the assignee: what takes the type it stands for takes it of that mutability, without
   null, or made nullable where it takes null *)
Lemma nested_assignee_step: forall n gm nn q P A s s',
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    in_fragment env A = true -> wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
    /\ (forall b o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> satisfies b s' ->
        exists f, unify env f A (inst env b P) (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n gm nn q P A s s' EP HA Hs H.
    assert (Hstep: forall k A0, in_fragment env A0 = true ->
        unify env (S k) A0 (TypeVariable (mkGenericRef gm nn q [])) (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> satisfies b s' ->
            exists f, unify env f A0 (ref_apply env gm nn x) (Ongoing []) = Some (Ongoing []))).
    { intros k A0 HA0 H0. destruct (state_of_assignee k gm nn q [] A0 s s' HA0 H0) as [st Hl].
      destruct (assignee_leaf k gm nn q [] st A0 s s' Hs Hl HA0 H0) as [Hs' [Hext Hsound]].
      split; [exact Hs'|]. split; [exact Hext|]. intros b o x Ex Hsb.
      destruct (Hsb q o x Ex) as [Hx [st' [Hl' Hfit]]].
      assert (Hfits: forall st'', lookup_state s' q = Some st'' -> fits st'' o x)
          by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
      destruct (Hsound o x Hx Hfits) as [f Hf]. exact (reference_assigns gm nn x A0 f Hx HA0 Hf). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros b o x Ex Hsb.
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)). exact (Hsnd b o x Ex Hsb).
    - destruct n as [|n]; [discriminate H|].
      destruct (fragment_cases env A HA) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HR]]]]].
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_nullable in H. destruct n as [|n]; [discriminate H|].
        destruct (Hstep n _ HR H) as [Hs' [Hext Hsnd]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b o x Ex Hsb.
        destruct (Hsnd b o x Ex Hsb) as [f Hf].
        rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ex)). exists (S f). exact (unify_rewrap_assignee _ _ _ _ _ Hf).
Qed.

Lemma root_args_ifrag: forall m c args, ifrag env (RootResolved m c args) = true -> forall a, In a args -> argument_ifrag env a = true.
Proof.
    intros m c args Hf a Ha.
    destruct (ifrag_cases env wf _ Hf) as [[m' [c' [args' [Heq [_ [_ Hargs]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
        try discriminate Heq.
    - injection Heq as <- <- <-. exact (Hargs a Ha).
    - unfold bottom_type in Heq. injection Heq as _ _ ->. destruct Ha.
Qed.

(* A type of the parameters without type variables, nor ownerships of type parameters, is a class type *)
Lemma closed_of_ifrag: forall t, ifrag env t = true -> no_vars t = true -> plain_owners t = true -> closed t = true.
Proof.
    intros t. remember (vsize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Ht Hn Ho.
    destruct (ifrag_cases env wf t Ht) as [[m [c [args [-> [_ [_ Hargs]]]]]]|[[m_bot ->]|[[m [c [args [-> Hr]]]]|[q [-> _]]]]].
    - change (forallb closed args = true). apply forallb_forall. intros a Ha. pose proof (Hargs a Ha) as Ea.
      change (forallb no_vars args = true) in Hn. rewrite forallb_forall in Hn.
      change (forallb plain_owners args = true) in Ho. rewrite forallb_forall in Ho.
      destruct a as [| | | |v o n| |]; try discriminate Ea. change (nfrag env n = true) in Ea. pose proof (Hn _ Ha) as Hna. pose proof (Ho _ Ha) as Hoa.
      simpl in Hna, Hoa |- *. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon]. rewrite Hop. cbn [andb].
      destruct (nfrag_cases env n Ea) as [Ea'|[gm [nn [q [[-> | ->] _]]]]]; [|discriminate Hna|discriminate Hna].
      apply (IH (vsize n)); [|reflexivity|exact Ea'|exact Hna|exact Hon]. pose proof (vsize_below m c args _ Ha) as Hv. simpl in Hv |- *. lia.
    - reflexivity.
    - change (closed (RootResolved m c args) = true). apply (IH (vsize (RootResolved m c args))); [simpl; lia|reflexivity|exact Hr|exact Hn|exact Ho].
    - discriminate Hn.
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
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true ->
        closed A = true -> wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f (instantiate env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true ->
        closed A = true -> wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f A (instantiate env b P) (Ongoing []) = Some (Ongoing []))).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    (* the type of a type argument, also a type variable of a mutability given to it, narrowed or made nullable *)
    assert (IHnt: forall P A s s', nfrag env P = true -> afrag env A = true -> closed A = true ->
        wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing []))).
    { intros P A s s' HP HA HcA Hs H. destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP Hsf]]]]]; [exact (IHt P A s s' HP' HA HcA Hs H)|].
      destruct (nested_target_step n IHt gm nn q P A s s' Hsf EP HA HcA Hs H) as [H1 [H2 H3]].
      split; [exact H1|]. split; [exact H2|]. intros b K Hb Hsb.
      assert (Hb': bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct EP as [-> | ->]; exact Hb).
      destruct (binds_ref_some env wf b K [] _ Hb') as [o [x [Ex _]]]. cbn [param_of] in Ex. exact (H3 b o x Ex Hsb). }
    assert (IHna: forall P A s s', nfrag env P = true -> afrag env A = true -> closed A = true ->
        wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (to_generic P) = true -> satisfies b s' ->
            exists f, unify env f A (inst env b P) (Ongoing []) = Some (Ongoing []))).
    { intros P A s s' HP HA HcA Hs H. destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP _]]]]]; [exact (IHa P A s s' HP' HA HcA Hs H)|].
      destruct (nested_assignee_step n gm nn q P A s s' EP (afrag_in_fragment env A HA) Hs H) as [H1 [H2 H3]].
      split; [exact H1|]. split; [exact H2|]. intros b K Hb Hsb.
      assert (Hb': bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct EP as [-> | ->]; exact Hb).
      destruct (binds_ref_some env wf b K [] _ Hb') as [o [x [Ex _]]]. cbn [param_of] in Ex. exact (H3 b o x Ex Hsb). }
    (* the parts of the types of the arguments *)
    assert (Hargs: forall ma ca aargs, in_fragment env (RootResolved ma ca aargs) = true ->
        closed (RootResolved ma ca aargs) = true ->
        length aargs = length (parameter_ids env ca) /\ forall a, In a aargs ->
            argument_in_fragment env a = true /\ closed a = true).
    { intros ma ca aargs Hf Hc. destruct (root_in_fragment env ma ca aargs Hf) as [Hl Ha]. split; [exact Hl|].
      intros a Hin. split; [exact (Ha a Hin)|]. exact (closed_parts ma ca aargs Hc a Hin). }
    assert (Hnorm: forall ca ct aargs, ca <> ct -> ca <> nothing -> base_type_is_subtype_of env ca ct = true ->
        length aargs = length (parameter_ids env ca) ->
        (forall a, In a aargs -> argument_in_fragment env a = true /\ closed a = true) ->
        forall a, In a (parameterized_supertype_arguments env ca aargs ct) ->
            argument_in_fragment env a = true /\ closed a = true).
    { intros ca ct aargs Hne Hcn Hbase Hl Ha a Hin.
      assert (Hta: forall y, In y aargs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Ha, Hy).
      destruct (supertype_arguments_to_generic env wf ca ct aargs Hne Hcn Hbase Hl Hta)
          as [_ [_ Hcl]].
      destruct (supertype_arguments_in_fragment env wf ca ct aargs Hne Hcn Hbase Hl (fun y Hy => proj1 (Ha y Hy))) as [_ Hf].
      split; [exact (Hf a Hin)|]. apply Hcl; [intros y Hy; apply Ha, Hy|exact Hin]. }
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
      intros P A s s' HP HA HcA Hs H. pose proof (afrag_in_fragment env A HA) as HA'.
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (forall b K, bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true -> satisfies b s' ->
              exists f, unify env f (inst env b (RootResolved mt ct targs)) (RootResolved ma ca aargs) (Ongoing [])
              = Some (Ongoing []))).
      { intros mt ct targs ma ca aargs Hft Hfa Hca Hu.
        pose proof (root_args_ifrag mt ct targs Hft) as Htargs.
        destruct (Hargs ma ca aargs Hfa Hca) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros b K Hbt _. exists 1.
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft) ltac:(solve_bound_vars)).
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) in Hu.
        assert (Hnorm': forall a, In a norm -> argument_in_fragment env a = true /\ closed a = true).
        { unfold norm. destruct (Class_eq_dec ca ct) as [<-|Hne]; [rewrite class_eqb_refl; exact Haargs|].
          rewrite (class_eqb_false _ _ Hne). exact (Hnorm ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs). }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (forall b K, bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true -> satisfies b s0' ->
                exists f, unify env f ((fun b => instantiate env b) b t) ((fun _ a => a) b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnorm' a Ha) as [Hfa' Hca'].
          destruct (IHat t a s0 s0' (Htargs t Ht) Hfa' Hca' Hs0 E) as [Hs1 [Hn1 Hsnd]].
          split; [exact Hs1|]. split; [exact Hn1|]. intros b K Hbt Hsb.
          exact (Hsnd b K (bound_in_root env b K [] mt ct (map to_generic targs) Hbt _ (in_map _ _ _ Ht)) Hsb). }
        destruct (Hpairs targs norm s s' (fun b => instantiate env b) (fun _ a => a) _ Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hbt Hsb. destruct (Hsound b K Hbt Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft) ltac:(solve_bound_vars)).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn.
        exact Hf. }
      destruct (ifrag_cases env wf P HP) as [[mt [ct [targs [-> _]]]]|[[m_bot ->]|[[mt [ct [targs [-> HP']]]]|[p [-> Hfb]]]]];
          [| unfold bottom_type in * | |].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HcA H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HcA H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]].
        * rewrite unify_nullable_class in H. destruct (IHt _ _ s s' HP' HA HcA Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
          assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
          destruct (Hsound b K Hb' Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hf.
          rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
          exists (S f). rewrite unify_nullable_class. exact Hf.
        * rewrite unify_nullable_nullable in H.
          assert (HA2: afrag env (RootResolved ma ca aargs) = true) by exact HA''.
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
      intros P A s s' HP HA HcA Hs H. pose proof (afrag_in_fragment env A HA) as HA'.
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (forall b K, bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true -> satisfies b s' ->
              exists f, unify env f (RootResolved ma ca aargs) (inst env b (RootResolved mp cp pargs)) (Ongoing [])
              = Some (Ongoing []))).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hca Hu.
        pose proof (root_args_ifrag mp cp pargs Hfp) as Hpargs0.
        destruct (Hargs ma ca aargs Hfa Hca) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros b K Hbp _. exists 1.
          rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp) ltac:(solve_bound_vars)).
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        assert (Hlp: length pargs = length (parameter_ids env cp)).
        { destruct (ifrag_cases env wf _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
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
          destruct (Haargs t Ht) as [Hft' Hct'].
          destruct (IHaa a t s0 s0' (Hnormi a Ha) Hft' Hct' Hs0 E) as [Hs1 [Hn1 Hsnd]].
          split; [exact Hs1|]. split; [exact Hn1|]. intros b K Hbp Hsb.
          exact (Hsnd b K (proj2 (proj1 (Hnorm' b K Hbp) a Ha)) Hsb). }
        destruct (Hpairs aargs norm s s' (fun _ a => a) (fun b => instantiate env b) _ Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hbp Hsb. destruct (Hsound b K Hbp Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp) ltac:(solve_bound_vars)).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn.
        unfold unify_arguments. rewrite (proj2 (Hnorm' b K Hbp)). exact Hf. }
      destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]];
      destruct (ifrag_cases env wf P HP) as [[mp [cp [pargs [-> _]]]]|[[m_bot ->]|[[mp [cp [pargs [-> HP']]]]|[p [-> Hfb]]]]];
          try (unfold bottom_type in *).
      + exact (Hroot _ _ _ _ _ _ HP HA' HcA H).
      + exact (Hroot _ _ _ _ _ _ HP HA' HcA H).
      + rewrite unify_class_nullable in H. discriminate H.
      + destruct (state_of_assignee n None false p [] _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n None false p [] st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p [] _ _ _ Ex). exists f. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by exact HA''.
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb. destruct (Hsound b K Hb Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by exact HA''.
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb. destruct (Hsound b K Hb Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by exact HA''.
        rewrite unify_nullable_nullable in H. destruct (IHa _ _ s s' HP' HA2 HcA Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
        destruct (Hsound b K Hb' Hsb) as [f Hf].
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hf.
        rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
        exists (S f). rewrite unify_nullable_nullable. exact Hf.
      + destruct (state_of_assignee n None false p [] _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n None false p [] st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p [] _ _ _ Ex). exists f. exact Hf.
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HA HcA Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA.
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by exact HA.
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
            by exact (instance_not_variable env wf b K [] (to_generic nt) (nfrag_sfrag env nt HP) Hbn).
        rewrite (instantiate_argument env wf b K [] vt ot nt HP Hbn).
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va oa na [] Hfi), Hown. exact E. }
      assert (Hpart: forall b K, bound_in env b K [] (to_generic (TypeArgument vt ot nt)) = true -> bound_in env b K [] (to_generic nt) = true)
          by (intros b K Hb; exact (proj2 (bound_in_argument env b K [] vt ot (to_generic nt) Hb))).
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHnt nt na s s1 HP HAf Hcn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHna nt na s1 s' HP HAf Hcn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros b K Hb Hsb.
           destruct (Hsnd2 b K (Hpart b K Hb) Hsb) as [f2 Hf2]. destruct (Hsnd1 b K (Hpart b K Hb) (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply (Hgoal b K Hb). unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHnt nt na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHna nt na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHnt nt top_type s s' HP (top_in_afrag env wf) eq_refl Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHna nt bottom_type s s' HP (bottom_in_afrag env wf) eq_refl Hs H) as [Hs' [Hext Hsnd]] ];
          split; [exact Hs'|]; split; [exact Hext|]; intros b K Hb Hsb; destruct (Hsnd b K (Hpart b K Hb) Hsb) as [f Hf];
          exists (S f); apply (Hgoal b K Hb); unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HA HcA Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA.
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by exact HA.
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
           destruct (IHna np na s s1 HP HAf Hcn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHnt np na s1 s' HP HAf Hcn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros b K Hb Hsb.
           destruct (Hsnd2 b K (Hpart b K Hb) Hsb) as [f2 Hf2]. destruct (Hsnd1 b K (Hpart b K Hb) (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply (Hgoal b K Hb). unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHna np na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros b K Hb Hsb; destruct (Hsnd b K (Hpart b K Hb) Hsb) as [f Hf];
            exists (S f); apply (Hgoal b K Hb); unfold compare_variances; exact Hf
          | destruct (IHnt np na s s' HP HAf Hcn Hs H) as [Hs' [Hext Hsnd]];
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

(* A parameter whose type is a type variable of a mutability given to it, narrowed or made nullable:
   the plain variable takes the argument, without null where the variable is made nullable, and the type
   it stands for, of that mutability and nullability, takes the argument. Of an intersection, nullable or
   not, the argument (without null) is below the instance of each component, and so below that of the
   intersection, where the type variables are bound to class types *)
Lemma parameter_step: forall n P A s s', qfrag env P = true -> afrag env A = true -> closed A = true ->
    wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
    /\ (forall b K, bound_in env b K [] (pgeneric P) = true -> satisfies b s' ->
        ((exists cs, inter_of P = Some cs) -> bindings_in_fragment env b) ->
        exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n P A s s' HQ HA HcA Hs H. destruct (qfrag_cases env P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]].
    2:{ pose proof (afrag_in_fragment env A HA) as HA'.
        assert (Hinter: forall k a s0, k <= n -> afrag env a = true -> closed a = true ->
            unify env k (Intersection cs) a (Ongoing s) = Some (Ongoing s0) ->
            wf_states s0 /\ (forall b', satisfies b' s0 -> satisfies b' s)
            /\ forall b K, bound_in env b K [] (Intersection (map to_generic cs)) = true -> satisfies b s0 -> bindings_in_fragment env b ->
                exists f, unify env f (inst_nested env b (Intersection (map to_generic cs))) a (Ongoing []) = Some (Ongoing [])).
        { intros k a s0 Hk Ha Hca E.
          destruct (param_components k cs a s s0 (proj1 (constraints_with_arguments k))
              (fun j _ => leaf_all j (proj1 (constraints_with_arguments j))) HSi Hcs Ha Hca Hs E) as [Hs0 [Hn0 Hall]].
          split; [exact Hs0|]. split; [exact Hn0|]. intros b K Hb Hsb Hbf.
          destruct (bound_in_weak env wf b K [] _ Hb) as [Hbx Htop].
          apply (below_intersection_instance b K (map to_generic cs) a Hbf Hcs Hbx); [|exact (afrag_in_fragment env a Ha)|].
          - intros c Hc. cbn [bound_in_top_h] in Htop. rewrite forallb_forall in Htop. exact (Htop c Hc).
          - intros c Hc. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
            exact (Hall C HC b K (bound_in_component env b K [] _ _ Hb (in_map _ _ _ HC)) Hsb Hbf). }
        destruct EP as [->| ->].
        - destruct (Hinter n A s' (le_n n) HA HcA H) as [Hs' [Hn' Hsnd]].
          split; [exact Hs'|]. split; [exact Hn'|]. intros b K Hb Hsb Hbf. exact (Hsnd b K Hb Hsb (Hbf (ex_intro _ cs eq_refl))).
        - (* nullable: the intersection takes the argument without null *)
          destruct n as [|n]; [discriminate H|]. rewrite (unify_nullable_target env n _ A s HA') in H.
          destruct (without_null_afrag env A HA) as [HA0 HcA0]. rewrite <- HcA0 in HcA.
          destruct (Hinter n _ s' (Nat.le_succ_diag_r n) HA0 HcA H) as [Hs' [Hn' Hsnd]].
          split; [exact Hs'|]. split; [exact Hn'|]. intros b K Hb Hsb Hbf.
          destruct (Hsnd b K Hb Hsb (Hbf (ex_intro _ cs eq_refl))) as [f Hf].
          change (inst env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection (map to_generic cs)))).
          exists (S f). exact (unify_rewrap_target env _ _ A [] _ HA' Hf). }
    destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> [Hsf _]]]]]|[gm [nn [p [-> [Hsf _]]]]]]].
    { destruct (proj1 (constraints_with_arguments n) P A s s' HP' HA HcA Hs H) as [H1 [H2 H3]].
      split; [exact H1|]. split; [exact H2|]. intros b K Hb Hsb _. rewrite (pgeneric_ifrag env wf P HP') in Hb. exact (H3 b K Hb Hsb). }
    all: pose proof (afrag_in_fragment env A HA) as HA'.
    all: assert (Hstep: forall k A0, afrag env A0 = true -> closed A0 = true ->
        unify env (S k) (TypeVariable (mkGenericRef gm nn p [])) A0 (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> satisfies b s' ->
            exists f, unify env f (ref_apply env gm nn x) A0 (Ongoing []) = Some (Ongoing []))).
    all: try (intros k A0 HA0 HcA0 H0;
        exact (reference_step k gm nn p A0 s s' (leaf_all k (proj1 (constraints_with_arguments k))) Hsf HA0 HcA0 Hs H0)).
    - (* the variable itself *)
      destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA HcA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb _.
      destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj1 (inst_reference env b gm nn p [] _ _ _ Ex)). exact (Hsnd b o x Ex Hsb).
    - (* made nullable: the variable takes the argument without null *)
      destruct n as [|n]; [discriminate H|].
      assert (H0: unify env n (TypeVariable (mkGenericRef gm nn p [])) (without_null env A) (Ongoing s) = Some (Ongoing s')).
      { destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [rewrite unify_nullable_class in H|rewrite unify_nullable_nullable in H]; exact H. }
      assert (HA0: afrag env (without_null env A) = true).
      { destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HR]]]]]; [exact HA|].
        exact HR. }
      assert (HcA0: closed (without_null env A) = true).
      { destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]]; exact HcA. }
      destruct n as [|n]; [discriminate H0|].
      destruct (Hstep n _ HA0 HcA0 H0) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros b K Hb Hsb _.
      destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      destruct (Hsnd b o x Ex Hsb) as [f Hf].
      rewrite (proj2 (inst_reference env b gm nn p [] _ _ _ Ex)). exists (S f). exact (unify_rewrap_target env _ _ A [] _ HA' Hf).
Qed.

(*
 * Inference is sound: where unify accepts each argument of an invocation for its parameter, in turn,
 * each argument fits its parameter with the type variables replaced by any types that satisfy the
 * variable states it ends with.
 *)
Theorem invocation_sound: forall n Ps As s0 u,
    wf_states s0 ->
    (forall P, In P Ps -> qfrag env P = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (Ongoing s0) = Some (Ongoing u) ->
    wf_states u /\ (forall b K, (forall P, In P Ps -> bound_in env b K [] (pgeneric P) = true) -> satisfies b u ->
        ((exists P cs, In P Ps /\ inter_of P = Some cs) -> bindings_in_fragment env b) ->
        forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true).
Proof.
    intros n Ps As s0 u Hs0 HPs HAs H.
    assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', wf_states s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (forall b K, bound_in env b K [] (pgeneric P) = true -> satisfies b s' ->
            ((exists cs, inter_of P = Some cs) -> bindings_in_fragment env b) ->
            exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing []))).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HAs A HA) as [HfA HcA].
      exact (parameter_step n P A s s' (HPs P HP) HfA HcA Hs E). }
    destruct (fold_chain n _ s0 u (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
        Hs0 H) as [Hu [_ Hall]].
    split; [exact Hu|]. intros b K HbP Hb Hbf P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
    apply in_combine_l in Hin as HP.
    destruct (proj2 (proj2 (Hstep P A Hin s s' Hs E)) b K (HbP P HP) (Hx b Hb)
        (fun '(ex_intro _ cs Ecs) => Hbf (ex_intro _ P (ex_intro _ cs (conj HP Ecs))))) as [f Hf].
    exists f. unfold is_assignable_to, empty_unification. rewrite Hf. reflexivity.
Qed.

(* TypeUnification.getFinalValueFor: the lower bound, unless it is still Nothing, then the upper one *)
Definition final_value (st: VariableState): EType :=
    if is_non_nullable_nothing env (lower_bound st) then upper_bound st else lower_bound st.

(* The type a value of t reads as, where it is a type argument, made nullable or not
   (BoundTypeReference.asReadType) *)
Definition read_value (t: EType): EType :=
    match t with
    | TypeArgument v _ x => read_type v x
    | Nullable (TypeArgument v _ x) => rewrap_nullable (read_type v x)
    | _ => t
    end.

(* TypeUnification.getFinalValueFor in full: of the variable p without a lower bound whose static upper
   bound mentions other type variables, but not p itself, the upper bound intersected with the static
   upper bound, its type variables replaced by their final values b, as a value of it reads: that is a
   type argument where the bound is a type parameter of a class captured from a variant receiver. Otherwise
   final_value; the theorems take the variables whose bounds mention type variables to get a lower
   bound, where the two agree (final_value_with_lower) *)
Definition final_value_with (b: Bindings) (p: TypeParameterId) (st: VariableState): EType :=
    if is_non_nullable_nothing env (lower_bound st) && negb (no_vars (static_upper_bound st))
        && vars_in (fun q => negb (param_eqb q p)) (static_upper_bound st)
    then intersect env (upper_bound st) (read_value (instantiate_free env b (static_upper_bound st)))
    else final_value st.

Lemma final_value_with_lower: forall b p st,
    (no_vars (static_upper_bound st) = false -> is_non_nullable_nothing env (lower_bound st) = false) ->
    final_value_with b p st = final_value st.
Proof.
    intros b p st H. unfold final_value_with. destruct (no_vars (static_upper_bound st)) eqn:E.
    - rewrite andb_false_r. reflexivity.
    - rewrite (H eq_refl). reflexivity.
Qed.

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
    - intros gm nn x a n Hx Ha Hgm Hnn H. exists n. exact (class_reference_takes env n gm nn x a [] Hx Ha Hgm Hnn H).
    - intros gm nn x a n Hx Ha H. exists n. exact (reference_takes_assignee env n gm nn x a [] Hx Ha H).
    - intros gm nn x B n Hx HB H. exists n. exact (class_reference_within env n gm nn x B [] Hx HB H).
Qed.
