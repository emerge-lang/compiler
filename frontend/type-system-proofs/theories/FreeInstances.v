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

(* A type variable other than p, of a mutability given to it, narrowed, or made nullable *)
Definition other_ref (p: TypeParameterId) (n: EType): Prop :=
    match n with
    | TypeVariable (mkGenericRef _ _ q []) | Nullable (TypeVariable (mkGenericRef _ _ q [])) => q <> p
    | _ => False
    end.

(* p itself, of a mutability given to it, narrowed, or made nullable *)
Definition self_ref (p: TypeParameterId) (n: EType): Prop :=
    match n with
    | TypeVariable (mkGenericRef _ _ q []) | Nullable (TypeVariable (mkGenericRef _ _ q [])) => q = p
    | _ => False
    end.

(* The static upper bounds of p: type variables only, no ownerships of type parameters; in type
   arguments, type variables also of a mutability given to them, narrowed, or made nullable *)
Fixpoint plain_variables (p: TypeParameterId) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc =>
        match a with TypeArgument _ o n => is_parameter_ownership o = false /\ (plain_variables p n \/ other_ref p n \/ self_ref p n) | _ => False end
        /\ acc) True arguments
    | Nullable n => plain_variables p n /\ match n with RootResolved _ _ _ => True | _ => False end
    | TypeVariable (mkGenericRef None false _ _) => True
    | Error _ _ => True
    | _ => False
    end.

Lemma free_argument: forall b v o x, plain_values b -> nests_argument (instantiate_free env b x) = false ->
    instantiate_free env b (TypeArgument v o x) = TypeArgument v (instantiate_free_ownership b o) (instantiate_free env b x).
Proof.
    intros b v o x Hb Hn. cbn [instantiate_free].
    rewrite (proj2 (none_loose b (plain_not_loose b Hb) x)).
    destruct (instantiate_free env b x) as [| [| | | | | |] | | | | |]; try reflexivity; discriminate Hn.
Qed.

Lemma plain_variables_free: forall q b t, plain_values b -> plain_variables q t -> nests_argument (instantiate_free env b t) = false.
Proof.
    intros q b [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] Hb H; cbn [plain_variables] in H; try contradiction; try reflexivity.
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

Lemma plain_variables_only: forall q b t, plain_variables q t -> variables_only b t.
Proof.
    intros q b. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; cbn [plain_variables] in H; cbn [variables_only];
        try contradiction; try exact I.
    - induction args as [|a args IHa]; [exact I|]. cbn [fold_right] in H |- *. destruct H as [Ha Has].
      split; [|exact (IHa Has)]. destruct a as [| | | |v o n| |]; try contradiction. destruct Ha as [Ho Hn].
      cbn [variables_only]. split; [intros q' Eq; subst o; discriminate Ho|].
      destruct Hn as [Hn|[Hn|Hn]]; [exact (IH n Hn)| |];
          destruct n as [| [| | | | |[? ? ? []]|] | | | |[? ? ? []]|]; cbn [other_ref self_ref] in Hn; try contradiction; exact I.
    - exact (IH n (proj1 H)).
Qed.

(* A type variable other than p, in a type argument: binding p first leaves it as it is, and binding
   it then is binding it with p bound, too *)
Lemma other_ref_unbound: forall p a v o x, is_parameter_ownership o = false -> other_ref p x ->
    instantiate_free env [(p, a)] (TypeArgument v o x) = TypeArgument v o x.
Proof.
    intros p a v o x Ho Hn.
    destruct x as [| [| | | | |[gm nn q []]|] | | | |[gm nn q []]|]; cbn [other_ref] in Hn; try contradiction;
        cbn [instantiate_free lookup_binding mentions_loosely_bound_in_arguments]; unfold param_eqb;
        rewrite (proj2 (Nat.eqb_neq q p) Hn), (free_plain_ownership _ o Ho); reflexivity.
Qed.

Lemma other_ref_bound: forall p x b v o y, is_parameter_ownership o = false -> other_ref p y ->
    instantiate_free env (with_value p x b) (TypeArgument v o y) = instantiate_free env b (TypeArgument v o y).
Proof.
    intros p x b v o y Ho Hn. unfold with_value.
    destruct y as [| [| | | | |[gm nn q []]|] | | | |[gm nn q []]|]; cbn [other_ref] in Hn; try contradiction;
        cbn [instantiate_free lookup_binding mentions_loosely_bound_in_arguments]; unfold param_eqb;
        rewrite (proj2 (Nat.eqb_neq q p) Hn), !(free_plain_ownership _ o Ho); reflexivity.
Qed.

Lemma nests_rewrap: forall y, nests_argument y = false -> nests_argument (rewrap_nullable y) = false.
Proof. intros [| [] | | | | |] H; first [reflexivity|discriminate H]. Qed.

(* p itself in a type argument, bound to c: c of the mutability given to it, narrowed, or made nullable *)
Lemma self_ref_value: forall p x b y, self_ref p y -> nests_argument x = false ->
    exists gm nn, instantiate_free env (with_value p x b) y = instantiate_free env [(p, TypeArgument invariant ref x)] y
        /\ (instantiate_free env [(p, TypeArgument invariant ref x)] y = ref_apply env gm nn x
            \/ instantiate_free env [(p, TypeArgument invariant ref x)] y = rewrap_nullable (ref_apply env gm nn x)).
Proof.
    intros p x b y Hn Hc.
    destruct y as [| [| | | | |[gm nn q []]|] | | | |[gm nn q []]|]; cbn [self_ref] in Hn; try contradiction; subst q; exists gm, nn;
        cbn [instantiate_free with_value lookup_binding]; rewrite param_eqb_refl; unfold final_argument;
        cbn [is_loose Variance_beq negb orb]; rewrite Hc; (split; [reflexivity|]); [right|left]; reflexivity.
Qed.

(* Binding the free variables twice, the candidate first and then the others, is binding them at once.
   Where p itself is in a type argument, c is there, of the mutability given to it or narrowed: as c,
   that mentions none of the variables *)
Lemma free_compose: forall b p x, plain_values b -> gfrag env x = true -> mentions_bound b x = false ->
    (forall gm nn, nests_argument (ref_apply env gm nn x) = false /\ instantiate_free env b (ref_apply env gm nn x) = ref_apply env gm nn x) ->
    forall B, plain_variables p B ->
    instantiate_free env b (instantiate_free env [(p, TypeArgument invariant ref x)] B) = instantiate_free env (with_value p x b) B.
Proof.
    intros b p x Hb Hc Hm Href.
    assert (Hbp: plain_values (with_value p x b)).
    { intros q a Ea. cbn [with_value lookup_binding] in Ea. destruct (param_eqb q p).
      - injection Ea as <-. split; [reflexivity|]. exists ref, x. split; [reflexivity|exact (gfrag_not_nested x Hc)].
      - exact (Hb q a Ea). }
    assert (Hpp: plain_values [(p, TypeArgument invariant ref x)]).
    { intros q a Ea. cbn [lookup_binding] in Ea. destruct (param_eqb q p); [|discriminate Ea].
      injection Ea as <-. split; [reflexivity|]. exists ref, x. split; [reflexivity|exact (gfrag_not_nested x Hc)]. }
    fix IH 1. intros [m c' args|n|g|me msg|v o n|[gm nn q vs]|cs] H; cbn [plain_variables] in H; try contradiction.
    - cbn [instantiate_free]. f_equal. rewrite map_map.
      induction args as [|a args IHa]; [reflexivity|]. cbn [fold_right] in H. destruct H as [Ha Has].
      cbn [map]. f_equal; [|exact (IHa Has)].
      destruct a as [| | | |v o n| |]; try contradiction. destruct Ha as [Ho [Hn|[Hn|Hn]]].
      2:{ rewrite (other_ref_unbound p _ v o n Ho Hn). exact (eq_sym (other_ref_bound p x b v o n Ho Hn)). }
      2:{ destruct (self_ref_value p x b n Hn (gfrag_not_nested x Hc)) as [gm [nn [Eb Ey]]].
          set (y := instantiate_free env [(p, TypeArgument invariant ref x)] n) in *.
          assert (Hy: nests_argument y = false /\ instantiate_free env b y = y).
          { destruct (Href gm nn) as [Hn1 Hn2]. destruct Ey as [-> | ->]; [split; assumption|].
            split; [exact (nests_rewrap _ Hn1)|rewrite free_rewrap, Hn2; reflexivity]. }
          destruct Hy as [Hy1 Hy2].
          rewrite (free_argument _ v o n Hpp Hy1), (free_plain_ownership _ o Ho). fold y.
          rewrite (free_argument b v o _ Hb); [|rewrite Hy2; exact Hy1].
          rewrite (free_argument _ v o n Hbp); [|rewrite Eb; exact Hy1].
          rewrite !(free_plain_ownership _ o Ho), Eb, Hy2. reflexivity. }
      rewrite (free_argument _ v o n Hpp (plain_variables_free p _ n Hpp Hn)), (free_plain_ownership _ o Ho).
      pose proof (IH n Hn) as En.
      rewrite (free_argument b v o _ Hb); [|rewrite En; exact (plain_variables_free p _ n Hbp Hn)].
      rewrite (free_argument _ v o n Hbp (plain_variables_free p _ n Hbp Hn)), !(free_plain_ownership _ o Ho), En. reflexivity.
    - destruct H as [Hn _].
      change (instantiate_free env b (rewrap_nullable (instantiate_free env [(p, TypeArgument invariant ref x)] n))
          = rewrap_nullable (instantiate_free env (with_value p x b) n)).
      rewrite free_rewrap, (IH n Hn). reflexivity.
    - reflexivity.
    - destruct gm, nn; try contradiction. cbn [instantiate_free with_value lookup_binding].
      destruct (param_eqb q p) eqn:Eq.
      + unfold final_argument. cbn [is_loose Variance_beq negb orb]. rewrite (gfrag_not_nested x Hc). cbn [orb].
        exact (free_unmentioned b Hb x Hc Hm).
      + reflexivity.
Qed.

(*
 * The static upper bound S with the candidate c in place of the variable p (with_candidate), the
 * other variables bound in b, is S with p bound to c, too, as c mentions none of the variables
 *)
Lemma free_candidate: forall b p a B, plain_values b -> gfrag env a = true -> mentions_bound b a = false ->
    (forall gm nn, nests_argument (ref_apply env gm nn a) = false /\ instantiate_free env b (ref_apply env gm nn a) = ref_apply env gm nn a) ->
    plain_variables p B ->
    instantiate_free env b (with_candidate env p a B) = instantiate_free env (with_value p a b) B.
Proof.
    intros b p a S Hb Hc Hm Href HS. unfold with_candidate.
    rewrite <- (instantiate_free_variables_only env _ S (plain_variables_only p _ S HS)).
    exact (free_compose b p a Hb Hc Hm Href S HS).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Bindings that look up the same                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Definition same_lookups (b1 b2: Bindings): Prop := forall q, lookup_binding b1 q = lookup_binding b2 q.

Lemma loosely_ext: forall b1 b2, same_lookups b1 b2 ->
    forall t, mentions_loosely_bound b1 t = mentions_loosely_bound b2 t.
Proof.
    intros b1 b2 E. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; cbn [mentions_loosely_bound];
        try reflexivity; try (rewrite E; reflexivity); try exact (IH n).
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb]. rewrite (IH a), IHa. reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb]. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma loosely_arguments_ext: forall b1 b2, same_lookups b1 b2 ->
    forall t, mentions_loosely_bound_in_arguments b1 t = mentions_loosely_bound_in_arguments b2 t.
Proof.
    intros b1 b2 E. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; cbn [mentions_loosely_bound_in_arguments];
        try reflexivity; try exact (IH n).
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb]. rewrite (loosely_ext b1 b2 E a), IHa. reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb]. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma mentions_bound_ext: forall b1 b2, same_lookups b1 b2 -> forall t, mentions_bound b1 t = mentions_bound b2 t.
Proof.
    intros b1 b2 E. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs]; cbn [mentions_bound];
        try reflexivity; try exact (IH n).
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb]. rewrite (IH a), IHa. reflexivity.
    - rewrite (IH n). destruct o as [| | |q]; try reflexivity. rewrite E. reflexivity.
    - rewrite E. reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb]. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma free_ext: forall b1 b2, same_lookups b1 b2 -> forall t, instantiate_free env b1 t = instantiate_free env b2 t.
Proof.
    intros b1 b2 E. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs]; cbn [instantiate_free]; try reflexivity.
    - f_equal. induction args as [|a args IHa]; [reflexivity|]. cbn [map]. rewrite (IH a), IHa. reflexivity.
    - rewrite (IH n). reflexivity.
    - rewrite (IH n), (loosely_arguments_ext b1 b2 E n).
      assert (Eo: instantiate_free_ownership b1 o = instantiate_free_ownership b2 o)
          by (destruct o as [| | |q]; try reflexivity; cbn [instantiate_free_ownership]; rewrite E; reflexivity).
      rewrite Eo. reflexivity.
    - rewrite E. reflexivity.
    - assert (Em: existsb (mentions_bound b1) cs = existsb (mentions_bound b2) cs).
      { induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb]. rewrite (mentions_bound_ext b1 b2 E c), IHc. reflexivity. }
      rewrite Em. destruct (existsb (mentions_bound b2) cs); [|reflexivity]. clear Em.
      f_equal. induction cs as [|c cs IHc]; [reflexivity|]. cbn [map]. rewrite (IH c), IHc. reflexivity.
Qed.

(* The type parameters a type refers to, as a type variable, a reference or an ownership, all of P *)
Fixpoint refs_among (P: TypeParameterId -> bool) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb (refs_among P) arguments
    | Nullable n => refs_among P n
    | Generic (mkGenericRef _ _ p _) | TypeVariable (mkGenericRef _ _ p _) => P p
    | Error _ _ => true
    | TypeArgument _ o n => match o with parameter_ownership q => P q | _ => true end && refs_among P n
    | Intersection components => forallb (refs_among P) components
    end.

(* Bindings that look up the same, for the type parameters of P *)
Definition same_lookups_on (P: TypeParameterId -> bool) (b1 b2: Bindings): Prop :=
    forall q, P q = true -> lookup_binding b1 q = lookup_binding b2 q.

Lemma loosely_ext_on: forall Q b1 b2, same_lookups_on Q b1 b2 ->
    forall t, refs_among Q t = true -> mentions_loosely_bound b1 t = mentions_loosely_bound b2 t.
Proof.
    intros Q b1 b2 E. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] H; cbn [mentions_loosely_bound refs_among] in H |- *;
        try reflexivity; try (rewrite (E p H); reflexivity).
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - apply andb_true_iff in H. exact (IH n (proj2 H)).
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

Lemma loosely_arguments_ext_on: forall Q b1 b2, same_lookups_on Q b1 b2 ->
    forall t, refs_among Q t = true -> mentions_loosely_bound_in_arguments b1 t = mentions_loosely_bound_in_arguments b2 t.
Proof.
    intros Q b1 b2 E. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; cbn [mentions_loosely_bound_in_arguments refs_among] in H |- *;
        try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb forallb] in H |- *. apply andb_true_iff in H.
      rewrite (loosely_ext_on Q b1 b2 E a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

Lemma mentions_bound_ext_on: forall Q b1 b2, same_lookups_on Q b1 b2 ->
    forall t, refs_among Q t = true -> mentions_bound b1 t = mentions_bound b2 t.
Proof.
    intros Q b1 b2 E. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] H; cbn [mentions_bound refs_among] in H |- *;
        try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - apply andb_true_iff in H. destruct H as [Ho Hn]. rewrite (IH n Hn).
      destruct o as [| | |q]; try reflexivity. rewrite (E q Ho). reflexivity.
    - rewrite (E p H). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

(* Instantiating the free variables of a type looks up only the type parameters it refers to *)
Lemma free_ext_on: forall Q b1 b2, same_lookups_on Q b1 b2 ->
    forall t, refs_among Q t = true -> instantiate_free env b1 t = instantiate_free env b2 t.
Proof.
    intros Q b1 b2 E. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] H; cbn [instantiate_free refs_among] in H |- *;
        try reflexivity.
    - f_equal. induction args as [|a args IHa]; [reflexivity|]. cbn [map forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - rewrite (IH n H). reflexivity.
    - apply andb_true_iff in H. destruct H as [Ho Hn].
      rewrite (IH n Hn), (loosely_arguments_ext_on Q b1 b2 E n Hn).
      assert (Eo: instantiate_free_ownership b1 o = instantiate_free_ownership b2 o)
          by (destruct o as [| | |q]; try reflexivity; cbn [instantiate_free_ownership]; rewrite (E q Ho); reflexivity).
      rewrite Eo. reflexivity.
    - rewrite (E p H). reflexivity.
    - assert (Em: existsb (mentions_bound b1) cs = existsb (mentions_bound b2) cs).
      { induction cs as [|c cs IHc]; [reflexivity|]. cbn [existsb forallb] in H |- *. apply andb_true_iff in H.
        rewrite (mentions_bound_ext_on Q b1 b2 E c (proj1 H)), (IHc (proj2 H)). reflexivity. }
      rewrite Em. destruct (existsb (mentions_bound b2) cs); [|reflexivity]. clear Em.
      f_equal. induction cs as [|c cs IHc]; [reflexivity|]. cbn [map forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

(* Binding p again to what b binds it to changes nothing *)
Lemma with_value_same: forall b p x, lookup_binding b p = Some (TypeArgument invariant ref x) ->
    same_lookups (with_value p x b) b.
Proof.
    intros b p x Hp q. cbn [with_value lookup_binding]. destruct (param_eqb q p) eqn:Eq; [|reflexivity].
    apply param_eqb_eq in Eq. subst q. rewrite Hp. reflexivity.
Qed.

End FreeInstances.
