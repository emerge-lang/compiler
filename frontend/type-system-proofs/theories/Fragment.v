From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Transitivity.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The fragment of type parameters and intersections                                                *)
(*                                                                                                *)
(* The types as the frontend builds them, beyond the class types of Transitivity.v: references to  *)
(* type parameters, and intersections (see Generics.v). Here, ahead of the substitution, so that   *)
(* type parameters can be replaced with types of it.                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Section Fragment.

Variable env: Environment.

(* A component of an intersection: a class type, or a non-null reference to a type parameter *)
Definition is_component (t: EType): bool :=
    match t with
    | RootResolved _ _ _ => true
    | Generic _ => negb (is_nullable t)
    | _ => false
    end.

(* What a nullable type wraps *)
Definition non_null (t: EType): bool :=
    match t with
    | Intersection _ => true
    | _ => is_component t
    end.

Fixpoint gfrag (t: EType): bool :=
    match t with
    | RootResolved _ c arguments =>
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with TypeArgument _ _ n => gfrag n | _ => false end) arguments
    | Nullable n => non_null n && gfrag n
    | Generic (mkGenericRef _ _ bound) => gfrag bound
    | Intersection components =>
        negb (Nat.eqb (length components) 0) && forallb (fun c => is_component c && gfrag c) components
    | _ => false
    end.

Definition argument_gfrag (a: EType): bool :=
    match a with TypeArgument _ _ n => gfrag n | _ => false end.

Lemma root_gfrag: forall m c arguments, gfrag (RootResolved m c arguments) = true ->
    length arguments = length (parameter_ids env c) /\ forall a, In a arguments -> argument_gfrag a = true.
Proof.
    intros m c arguments H.
    change (Nat.eqb (length arguments) (length (parameter_ids env c)) && forallb argument_gfrag arguments = true) in H.
    apply andb_true_iff in H. destruct H as [Hl Ha]. split; [apply Nat.eqb_eq, Hl|apply forallb_forall, Ha].
Qed.

Lemma make_root_gfrag: forall m c arguments,
    length arguments = length (parameter_ids env c) -> (forall a, In a arguments -> argument_gfrag a = true) ->
    gfrag (RootResolved m c arguments) = true.
Proof.
    intros m c arguments Hl Ha.
    change (Nat.eqb (length arguments) (length (parameter_ids env c)) && forallb argument_gfrag arguments = true).
    rewrite Hl, Nat.eqb_refl. apply forallb_forall, Ha.
Qed.

Lemma intersection_gfrag: forall cs, gfrag (Intersection cs) = true ->
    cs <> [] /\ forall c, In c cs -> is_component c = true /\ gfrag c = true.
Proof.
    intros cs H. simpl in H. apply andb_true_iff in H. destruct H as [Hl H]. split.
    - intros ->. discriminate Hl.
    - intros c Hc. rewrite forallb_forall in H. apply andb_true_iff, H, Hc.
Qed.

Lemma gfrag_cases: forall t, gfrag t = true ->
    (exists m c arguments, t = RootResolved m c arguments)
    \/ (exists n, t = Nullable n /\ non_null n = true /\ gfrag n = true)
    \/ (exists gm p bound, t = Generic (mkGenericRef gm p bound) /\ gfrag bound = true)
    \/ (exists cs, t = Intersection cs).
Proof.
    intros [m c args|n|[gm p bound]|me msg|v o n|g|cs] H; simpl in H; try discriminate H.
    - left. eauto.
    - right. left. apply andb_true_iff in H. exists n. split; [reflexivity|exact H].
    - right. right. left. eauto.
    - right. right. right. eauto.
Qed.

Lemma component_cases: forall c, is_component c = true -> gfrag c = true ->
    (exists m d arguments, c = RootResolved m d arguments)
    \/ (exists gm p bound, c = Generic (mkGenericRef gm p bound) /\ is_nullable bound = false /\ gfrag bound = true).
Proof.
    intros [m d args|n|[gm p bound]|me msg|v o n|g|cs] Hc H; simpl in Hc, H; try discriminate Hc.
    - left. eauto.
    - right. exists gm, p, bound. split; [reflexivity|]. split; [apply negb_true_iff; exact Hc|exact H].
Qed.

Lemma non_null_not_nullable: forall t, non_null t = true -> is_nullable t = false.
Proof. intros [| |[gm p b]| | | |] H; simpl in H |- *; try discriminate H; try reflexivity. apply negb_true_iff, H. Qed.

Lemma in_fragment_gfrag: forall k,
    (forall t, depth t <= k -> in_fragment env t = true -> gfrag t = true)
    /\ (forall a, argument_depth a <= k -> argument_in_fragment env a = true -> argument_gfrag a = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split; [intros [m c args|[m c args| | | | | |]| | | | |] Hd H|intros [| | | |v o n| |] Hd H]; simpl in Hd, H;
          try discriminate H; lia. }
    assert (Hroot: forall m c args, depth (RootResolved m c args) <= S k -> in_fragment env (RootResolved m c args) = true ->
        gfrag (RootResolved m c args) = true).
    { intros m c args Hd H. destruct (root_in_fragment env m c args H) as [Hl Ha]. apply make_root_gfrag; [exact Hl|].
      intros a Hin. pose proof (argument_depth_below m c args a Hin). apply IHa; [lia|apply Ha, Hin]. }
    split.
    - intros t Hd H. destruct (fragment_cases env t H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]].
      + exact (Hroot m c args Hd H).
      + rewrite depth_nullable in Hd. change (true && gfrag (RootResolved m c args) = true). apply Hroot; [lia|exact H'].
    - intros [| | | |v o n| |] Hd H; simpl in H; try discriminate H. simpl in Hd. apply IHt; [lia|exact H].
Qed.

Lemma in_fragment_is_gfrag: forall t, in_fragment env t = true -> gfrag t = true.
Proof. intros t. apply (proj1 (in_fragment_gfrag (depth t))). lia. Qed.

Lemma gfrag_not_variable: forall t, gfrag t = true -> is_type_variable t = false.
Proof. intros [| | | | |g|] H; simpl in H; try discriminate H; reflexivity. Qed.

End Fragment.
