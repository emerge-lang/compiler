From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating the free variables                                                               *)
(*                                                                                                *)
(* In generic code, the types inference works with mention the type parameters of the caller, which *)
(* aren't under inference. Subtyping.instantiate_free (BoundTypeReference.instantiateFreeVariables)  *)
(* replaces only the type variables, and leaves everything else as it is: a type that mentions no  *)
(* variable bound stays the same (free_unmentioned). Checking a candidate for a variable against    *)
(* its static upper bound puts the candidate in place of the variable (with_candidate); with the    *)
(* other variables bound in turn, that is the bound with all of them bound (free_candidate).        *)
(* ---------------------------------------------------------------------------------------------- *)

Section FreeInstances.

Variable env: Environment.

(* Bindings to type arguments that aren't loose, whose types aren't type arguments *)
Definition plain_values (b: Bindings): Prop :=
    forall p a, lookup_binding b p = Some a -> is_loose a = false
        /\ exists o y, a = TypeArgument invariant o y /\ nests_argument y = false.

Lemma plain_not_loose: forall b, plain_values b -> forall p a, lookup_binding b p = Some a -> is_loose a = false.
Proof. intros b H p a E. exact (proj1 (H p a E)). Qed.

(* A type of the fragment of Fragment.v is no type argument, nor a nullable one *)
Lemma gfrag_not_nested: forall t, gfrag env t = true -> nests_argument t = false.
Proof.
    intros [m c args|n|g|me msg|v o n|g|cs] H; try reflexivity; try discriminate H.
    cbn [gfrag] in H. apply andb_true_iff in H. destruct H as [Hn _].
    destruct n; try reflexivity; discriminate Hn.
Qed.

(* A type that mentions nothing bound stays as it is *)
Lemma free_unmentioned: forall b, plain_values b ->
    forall t, gfrag env t = true -> mentions_bound b t = false -> instantiate_free env b t = t.
Proof.
    intros b Hb.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H Hm; cbn [gfrag mentions_bound] in H, Hm; try discriminate H.
    - cbn [instantiate_free]. f_equal. apply andb_true_iff in H. destruct H as [_ H].
      induction args as [|a args IHa]; [reflexivity|]. cbn [forallb existsb] in H, Hm.
      apply andb_true_iff in H. destruct H as [Ha Has]. apply orb_false_iff in Hm. destruct Hm as [Hma Hmas].
      cbn [map]. f_equal; [|exact (IHa Has Hmas)].
      destruct a as [| | | |v o n| |]; try discriminate Ha. cbn [mentions_bound] in Hma. apply orb_false_iff in Hma.
      destruct Hma as [Ho Hn]. cbn [instantiate_free]. rewrite (IH n Ha Hn).
      rewrite (proj2 (none_loose b (plain_not_loose b Hb) n)).
      assert (Eo: instantiate_free_ownership b o = o).
      { destruct o as [| | |q]; try reflexivity. cbn [instantiate_free_ownership].
        destruct (lookup_binding b q); [discriminate Ho|reflexivity]. }
      rewrite Eo. pose proof (gfrag_not_nested n Ha) as Hnn.
      destruct n as [| [| | | | | |] | | | | |]; try reflexivity; discriminate Hnn.
    - apply andb_true_iff in H. destruct H as [Hs Hn]. cbn [instantiate_free]. rewrite (IH n Hn Hm).
      destruct n; try reflexivity; discriminate Hs.
    - reflexivity.
    - cbn [instantiate_free]. rewrite Hm. reflexivity.
Qed.

(* The bindings of the variable p to the candidate c, then those of b *)
Definition with_value (p: TypeParameterId) (c: EType) (b: Bindings): Bindings := (p, TypeArgument invariant ref c) :: b.

(* The static upper bounds: type variables only, no ownerships of type parameters *)
Fixpoint plain_variables (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc =>
        match a with TypeArgument _ o n => is_parameter_ownership o = false /\ plain_variables n | _ => False end /\ acc) True arguments
    | Nullable n => plain_variables n /\ match n with RootResolved _ _ _ => True | _ => False end
    | TypeVariable (mkGenericRef None false _ _) => True
    | Error _ _ => True
    | _ => False
    end.

Lemma free_argument: forall b v o n, plain_values b -> nests_argument (instantiate_free env b n) = false ->
    instantiate_free env b (TypeArgument v o n) = TypeArgument v (instantiate_free_ownership b o) (instantiate_free env b n).
Proof.
    intros b v o n Hb Hn. cbn [instantiate_free].
    rewrite (proj2 (none_loose b (plain_not_loose b Hb) n)).
    destruct (instantiate_free env b n) as [| [| | | | | |] | | | | |]; try reflexivity; discriminate Hn.
Qed.

Lemma plain_variables_free: forall b t, plain_values b -> plain_variables t -> nests_argument (instantiate_free env b t) = false.
Proof.
    intros b [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] Hb H; cbn [plain_variables] in H; try contradiction; try reflexivity.
    - destruct H as [_ Hs]. destruct n as [m c args| | | | | |]; try contradiction. reflexivity.
    - destruct gm, nn; try contradiction. cbn [instantiate_free]. destruct (lookup_binding b p) as [a|] eqn:Ea; [|reflexivity].
      destruct (Hb p a Ea) as [Hl [o [y [-> Hy]]]]. unfold final_argument. rewrite Hl, Hy. exact Hy.
Qed.

Lemma free_rewrap: forall b t, instantiate_free env b (rewrap_nullable t) = rewrap_nullable (instantiate_free env b t).
Proof.
    intros b [m c args|n|g|me msg|v o n|g|cs]; try reflexivity.
    cbn [rewrap_nullable instantiate_free]. destruct (instantiate_free env b n); reflexivity.
Qed.

Lemma free_plain_ownership: forall b o, is_parameter_ownership o = false -> instantiate_free_ownership b o = o.
Proof. intros b [| | |q] H; try reflexivity; discriminate H. Qed.

Lemma plain_variables_only: forall b t, plain_variables t -> variables_only b t.
Proof.
    intros b. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; cbn [plain_variables] in H; cbn [variables_only];
        try contradiction; try exact I.
    - induction args as [|a args IHa]; [exact I|]. cbn [fold_right] in H |- *. destruct H as [Ha Has].
      split; [|exact (IHa Has)]. destruct a as [| | | |v o n| |]; try contradiction. destruct Ha as [Ho Hn].
      cbn [variables_only]. split; [intros q Eq; subst o; discriminate Ho|exact (IH n Hn)].
    - exact (IH n (proj1 H)).
Qed.

(* Binding the free variables twice, the candidate first and then the others, is binding them at once *)
Lemma free_compose: forall b p c, plain_values b -> gfrag env c = true -> mentions_bound b c = false ->
    forall S, plain_variables S ->
    instantiate_free env b (instantiate_free env [(p, TypeArgument invariant ref c)] S) = instantiate_free env (with_value p c b) S.
Proof.
    intros b p c Hb Hc Hm.
    assert (Hbp: plain_values (with_value p c b)).
    { intros q a Ea. cbn [with_value lookup_binding] in Ea. destruct (param_eqb q p).
      - injection Ea as <-. split; [reflexivity|]. exists ref, c. split; [reflexivity|exact (gfrag_not_nested c Hc)].
      - exact (Hb q a Ea). }
    assert (Hpp: plain_values [(p, TypeArgument invariant ref c)]).
    { intros q a Ea. cbn [lookup_binding] in Ea. destruct (param_eqb q p); [|discriminate Ea].
      injection Ea as <-. split; [reflexivity|]. exists ref, c. split; [reflexivity|exact (gfrag_not_nested c Hc)]. }
    fix IH 1. intros [m c' args|n|g|me msg|v o n|[gm nn q vs]|cs] H; cbn [plain_variables] in H; try contradiction.
    - cbn [instantiate_free]. f_equal. rewrite map_map.
      induction args as [|a args IHa]; [reflexivity|]. cbn [fold_right] in H. destruct H as [Ha Has].
      cbn [map]. f_equal; [|exact (IHa Has)].
      destruct a as [| | | |v o n| |]; try contradiction. destruct Ha as [Ho Hn].
      rewrite (free_argument _ v o n Hpp (plain_variables_free _ n Hpp Hn)), (free_plain_ownership _ o Ho).
      pose proof (IH n Hn) as En.
      rewrite (free_argument b v o _ Hb); [|rewrite En; exact (plain_variables_free _ n Hbp Hn)].
      rewrite (free_argument _ v o n Hbp (plain_variables_free _ n Hbp Hn)), !(free_plain_ownership _ o Ho), En. reflexivity.
    - destruct H as [Hn _].
      change (instantiate_free env b (rewrap_nullable (instantiate_free env [(p, TypeArgument invariant ref c)] n))
          = rewrap_nullable (instantiate_free env (with_value p c b) n)).
      rewrite free_rewrap, (IH n Hn). reflexivity.
    - reflexivity.
    - destruct gm, nn; try contradiction. cbn [instantiate_free with_value lookup_binding].
      destruct (param_eqb q p) eqn:Eq.
      + unfold final_argument. cbn [is_loose Variance_beq negb orb]. rewrite (gfrag_not_nested c Hc). cbn [orb].
        exact (free_unmentioned b Hb c Hc Hm).
      + reflexivity.
Qed.

(*
 * The static upper bound S with the candidate c in place of the variable p (with_candidate), the
 * other variables bound in b, is S with p bound to c, too, as c mentions none of the variables
 *)
Lemma free_candidate: forall b p c S, plain_values b -> gfrag env c = true -> mentions_bound b c = false ->
    plain_variables S ->
    instantiate_free env b (with_candidate env p c S) = instantiate_free env (with_value p c b) S.
Proof.
    intros b p c S Hb Hc Hm HS. unfold with_candidate.
    rewrite <- (instantiate_free_variables_only env _ S (plain_variables_only _ S HS)).
    exact (free_compose b p c Hb Hc Hm S HS).
Qed.

End FreeInstances.
