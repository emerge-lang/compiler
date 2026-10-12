From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The substitution lemma                                                                           *)
(*                                                                                                *)
(* Instantiating the type parameters keeps assignability: if a type is assignable to another, it  *)
(* still is with the type parameters in both replaced by type arguments. This is what makes        *)
(* checking generic code once enough: at run time, every type parameter stands for one exact type. *)
(* So the type parameters are instantiated with exact type arguments here: invariant, owned or ref,*)
(* of types of the fragment of Transitivity.v, and within the bound of the type parameter.          *)
(* The types instantiated are                                                                      *)
(* - class types, whose type arguments are of any variance and ownership, and contain types of     *)
(*   the fragment; Nothing only as `exclusive Nothing`;                                            *)
(* - nullable class types;                                                                         *)
(* - type parameters, without a mutability of their own, whose bound is such a type, without      *)
(*   type parameters;                                                                              *)
(* - without type inference (no type variables), intersections or erroneous types.               *)
(* A type parameter accepts any non-nullable Nothing, also one whose mutability an instantiation   *)
(* of it doesn't accept (`mut Nothing` isn't a `const C`). Nothing is never instantiated, though,   *)
(* so that doesn't matter for the soundness; hence `exclusive Nothing` only, also in the type       *)
(* arguments of supertypes (supertypes_mention_nothing_as_bottom).                                  *)
(*                                                                                                *)
(* A type parameter assigned to a class type needs the transitivity of unify: the type argument is *)
(* assignable to the bound, which is assignable to the class type. A subclass assigned to its       *)
(* superclass needs instantiating the supertype to commute with instantiating the type parameters  *)
(* (supertype_arguments_commute).                                                                  *)
(* A type parameter on its own becomes the type in its type argument (inst_nested), as it does in   *)
(* a type argument.                                                                                *)
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

(* Nothing is `exclusive Nothing`, nowhere else *)
Definition is_bottom (m: option Mutability) (arguments: list EType): bool :=
    match m, arguments with Some exclusive, [] => true | _, _ => false end.

Fixpoint nothing_is_bottom (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        (if class_eqb c nothing then is_bottom m arguments else true) && forallb nothing_is_bottom arguments
    | Nullable n => nothing_is_bottom n
    | TypeArgument _ _ n => nothing_is_bottom n
    | _ => true
    end.

Hypothesis supertypes_mention_nothing_as_bottom: forall sub super t,
    In t (supertype_arguments env sub super) -> nothing_is_bottom t = true.

(* Without type parameters *)
Fixpoint closed (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb closed arguments
    | Nullable n => closed n
    | TypeArgument _ o n => negb (is_parameter_ownership o) && closed n
    | _ => false
    end.

(* The types instantiated *)
Fixpoint sfrag (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        if class_eqb c nothing then is_bottom m arguments else
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with TypeArgument _ _ n => sfrag n | _ => false end) arguments
    | Nullable n => is_class n && sfrag n
    | Generic (mkGenericRef None _ bound) => sfrag bound && closed bound
    | _ => false
    end.

Definition argument_sfrag (a: EType): bool :=
    match a with TypeArgument _ _ n => sfrag n | _ => false end.

Fixpoint sdepth (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments =>
        S (list_max (map (fun a => match a with TypeArgument _ _ n => S (sdepth n) | _ => 0 end) arguments))
    | Nullable n => S (sdepth n)
    | Generic (mkGenericRef _ _ bound) => S (sdepth bound)
    | _ => 0
    end.

Definition argument_sdepth (a: EType): nat :=
    match a with TypeArgument _ _ n => S (sdepth n) | _ => 0 end.

(* What a type in a type argument becomes, when instantiated: a type parameter, the type of its
   type argument *)
Definition inst_nested (b: Bindings) (n: EType): EType :=
    match n with
    | Generic (mkGenericRef _ p _) =>
        match lookup_binding b p with
        | Some (TypeArgument _ _ x) => x
        | _ => n
        end
    | _ => instantiate env b n
    end.

Section Bindings.

(* The bindings, and the fuel and states with which their type arguments are assignable to the
   bounds of the type parameters *)
Variable b: Bindings.
Variable K: nat.
Variable s: VariableStates.

Definition respects (x bound: EType): bool :=
    match unify env K bound x (Ongoing s) with Some (Ongoing _) => true | _ => false end.

(* The type parameter p is bound exactly, to a type of the fragment of Transitivity.v that is
   assignable to `bound` *)
Definition binds_exactly (p: TypeParameterId) (bound: EType): bool :=
    match lookup_binding b p with
    | Some (TypeArgument Model.invariant o x) => is_exact_ownership o && in_fragment env x && respects x bound
    | _ => false
    end.

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
    | Generic (mkGenericRef _ p bound) => binds_exactly p bound
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
    \/ (exists p bound, t = Generic (mkGenericRef None p bound) /\ sfrag bound = true /\ closed bound = true).
Proof.
    intros [m c args|[m c args| | | | | |]| [[gm|] p bound] | | | |] H; simpl in H; try discriminate H.
    - destruct (class_eqb c nothing) eqn:Hc.
      + right. left. apply class_eqb_true in Hc. subst c.
        destruct m as [[]|], args; simpl in H; try discriminate H. reflexivity.
      + left. apply andb_true_iff in H. destruct H as [Hl Ha]. exists m, c, args.
        split; [reflexivity|]. split; [exact Hc|]. split; [apply Nat.eqb_eq, Hl|]. apply forallb_forall, Ha.
    - right. right. left. exists m, c, args. split; [reflexivity|exact H].
    - right. right. right. exists p, bound. apply andb_true_iff in H. split; [reflexivity|exact H].
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

Lemma top_in_sfrag: sfrag top_type = true.
Proof.
    change (is_class (RootResolved (Some readonly) any []) && sfrag (RootResolved (Some readonly) any []) = true).
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
      - intros t Hd Ht _. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [bound [-> _]]]]]];
            simpl in Hd; lia.
      - intros [| | | |v o n| |] Hd Ha _; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    assert (Hroot: forall m c args, sdepth (RootResolved m c args) <= S k -> sfrag (RootResolved m c args) = true ->
        closed (RootResolved m c args) = true ->
        in_fragment env (RootResolved m c args) = true /\ instantiate env b (RootResolved m c args) = RootResolved m c args
        /\ bound_in (RootResolved m c args) = true /\ mentions_loosely_bound b (RootResolved m c args) = false).
    { intros m c args Hd Ht Hc. change (forallb closed args = true) in Hc. rewrite forallb_forall in Hc.
      destruct (sfrag_cases _ Ht) as [[m' [c' [args' [Heq [Hcn [Hl Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
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
    - intros t Hd Ht Hc. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[p [bound [-> _]]]]]].
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
    - intros [| | | |v o n| |] Hd Ha Hc; simpl in Ha; try discriminate Ha. simpl in Hd.
      change (negb (is_parameter_ownership o) && closed n = true) in Hc. apply andb_true_iff in Hc. destruct Hc as [Ho Hc].
      destruct (IHt n ltac:(lia) Ha Hc) as [Hf [Hi [Hb Hm]]].
      assert (Ho': instantiate_ownership b o = o /\ ownership_bound o = true) by (destruct o; split; first [reflexivity|discriminate Ho]).
      destruct Ho' as [Hio Hob]. repeat split.
      + exact Hf.
      + destruct (sfrag_cases n Ha) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [bound [-> _]]]]]].
        * simpl in Hi, Hm |- *. injection Hi as Hi. rewrite Hm, Hio, Hi. reflexivity.
        * simpl. rewrite Hio. reflexivity.
        * simpl in Hi, Hm |- *. injection Hi as Hi. rewrite Hm, Hio, Hi. reflexivity.
        * discriminate Hc.
      + simpl. rewrite Hob. exact Hb.
      + exact Hm.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating with exact type arguments                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma binds_exactly_some: forall p bound, binds_exactly p bound = true ->
    exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ in_fragment env x = true /\ respects x bound = true.
Proof.
    intros p bound H. unfold binds_exactly in H. destruct (lookup_binding b p) as [a|]; [|discriminate H].
    destruct a as [| | | |v o x| |]; try discriminate H. destruct v; try discriminate H.
    apply andb_true_iff in H. destruct H as [H Hr]. apply andb_true_iff in H. destruct H as [Ho Hx].
    exists o, x. auto.
Qed.

(* Nothing is bound loosely, so instantiating widens no type argument *)
Lemma no_loose: forall k,
    (forall t, sdepth t <= k -> sfrag t = true -> bound_in t = true -> mentions_loosely_bound b t = false)
    /\ (forall a, argument_sdepth a <= k -> argument_sfrag a = true -> bound_in a = true -> mentions_loosely_bound b a = false).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht _. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [bound [-> _]]]]]];
            simpl in Hd; lia.
      - intros [| | | |v o n| |] Hd Ha _; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    assert (Hroot: forall m c args, sdepth (RootResolved m c args) <= S k -> sfrag (RootResolved m c args) = true ->
        bound_in (RootResolved m c args) = true -> mentions_loosely_bound b (RootResolved m c args) = false).
    { intros m c args Hd Ht Hb.
      destruct (sfrag_cases _ Ht) as [[m' [c' [args' [Heq [_ [_ Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
          try discriminate Heq.
      - injection Heq as <- <- <-. apply not_true_iff_false. intros H.
        change (existsb (mentions_loosely_bound b) args = true) in H.
        apply existsb_exists in H. destruct H as [a [Ha H]]. pose proof (sdepth_below m c args a Ha).
        rewrite (IHa a ltac:(lia) (Hargs a Ha) (bound_in_root m c args Hb a Ha)) in H. discriminate H.
      - unfold bottom_type in Heq. injection Heq as -> -> ->. reflexivity. }
    split.
    - intros t Hd Ht Hb. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[p [bound [-> _]]]]]].
      + exact (Hroot _ _ _ Hd Ht Hb).
      + exact (Hroot _ _ _ Hd Ht Hb).
      + assert (Hd': sdepth (RootResolved m c args) <= S k) by (simpl in Hd |- *; lia). exact (Hroot _ _ _ Hd' Ht' Hb).
      + simpl in Hb. destruct (binds_exactly_some p bound Hb) as [o [x [E [Ho _]]]].
        simpl. rewrite E. destruct o; try discriminate Ho; reflexivity.
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
    destruct (sfrag_cases n Hn) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [bound [-> _]]]]]].
    - simpl in Hm |- *. rewrite Hm. reflexivity.
    - reflexivity.
    - simpl in Hm |- *. rewrite Hm. reflexivity.
    - simpl in Hb. destruct (binds_exactly_some p bound Hb) as [o' [x [E _]]].
      simpl. rewrite E. destruct v; reflexivity.
Qed.

Lemma bound_in_argument: forall v o n, bound_in (TypeArgument v o n) = true -> ownership_bound o = true /\ bound_in n = true.
Proof. intros v o n H. simpl in H. apply andb_true_iff in H. exact H. Qed.

(* Instantiated, a type is of the fragment of Transitivity.v *)
Lemma instances_in_fragment: forall k,
    (forall t, sdepth t <= k -> sfrag t = true -> bound_in t = true -> in_fragment env (inst_nested b t) = true)
    /\ (forall a, argument_sdepth a <= k -> argument_sfrag a = true -> bound_in a = true ->
        argument_in_fragment env (instantiate env b a) = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht _. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [bound [-> _]]]]]];
            simpl in Hd; lia.
      - intros [| | | |v o n| |] Hd Ha _; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    assert (Hroot: forall m c args, sdepth (RootResolved m c args) <= S k -> sfrag (RootResolved m c args) = true ->
        bound_in (RootResolved m c args) = true -> in_fragment env (RootResolved m c (map (instantiate env b) args)) = true).
    { intros m c args Hd Ht Hb.
      destruct (sfrag_cases _ Ht) as [[m' [c' [args' [Heq [_ [Hl Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
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
    - intros t Hd Ht Hb. destruct (sfrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[p [bound [-> _]]]]]].
      + exact (Hroot _ _ _ Hd Ht Hb).
      + exact (Hroot _ _ _ Hd Ht Hb).
      + assert (Hd': sdepth (RootResolved m c args) <= S k) by (simpl in Hd |- *; lia).
        change (is_class (RootResolved m c (map (instantiate env b) args))
            && in_fragment env (RootResolved m c (map (instantiate env b) args)) = true).
        rewrite (Hroot _ _ _ Hd' Ht' Hb). reflexivity.
      + simpl in Hb. destruct (binds_exactly_some p bound Hb) as [o [x [E [_ [Hx _]]]]].
        simpl. rewrite E. exact Hx.
    - intros [| | | |v o n| |] Hd Ha Hb; simpl in Ha; try discriminate Ha. simpl in Hd.
      destruct (bound_in_argument v o n Hb) as [_ Hb'].
      rewrite (instantiate_bound_argument v o n Ha Hb'). apply IHt; [lia|exact Ha|exact Hb'].
Qed.

Lemma instance_in_fragment: forall t, sfrag t = true -> bound_in t = true -> in_fragment env (inst_nested b t) = true.
Proof. intros t. apply (proj1 (instances_in_fragment (sdepth t))). lia. Qed.

Lemma argument_instance_in_fragment: forall a, argument_sfrag a = true -> bound_in a = true ->
    argument_in_fragment env (instantiate env b a) = true.
Proof. intros a. apply (proj2 (instances_in_fragment (argument_sdepth a))). lia. Qed.

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
        change (is_class (RootResolved m c (map (instantiate env bS) targs))
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

Lemma unify_root_generic: forall n m c args gm q bound,
    unify env (S n) (RootResolved m c args) (Generic (mkGenericRef gm q bound)) (Ongoing s)
    = unify env n (RootResolved m c args) bound (Ongoing s).
Proof. reflexivity. Qed.

Lemma unify_nullable_generic: forall n m c args gm q bound,
    unify env (S n) (Nullable (RootResolved m c args)) (Generic (mkGenericRef gm q bound)) (Ongoing s)
    = unify env n (Nullable (RootResolved m c args)) bound (Ongoing s).
Proof. reflexivity. Qed.

Lemma unify_generic_root: forall n p bound m c args,
    unify env (S n) (Generic (mkGenericRef None p bound)) (RootResolved m c args) (Ongoing s)
    = if class_eqb c nothing && Model.is_subtype_of (mutability_of env (RootResolved m c args))
        (mutability_of env (Generic (mkGenericRef None p bound)))
      then Some (Ongoing s) else Some Failed.
Proof. reflexivity. Qed.

Lemma unify_generic_nullable: forall n p bound na,
    unify env (S n) (Generic (mkGenericRef None p bound)) (Nullable na) (Ongoing s) = Some Failed.
Proof. reflexivity. Qed.

(* A type parameter, whose bound is no type parameter, is assignable to nothing but itself *)
Lemma unify_generic_generic: forall n p bp q bq u,
    sfrag bq = true -> closed bq = true ->
    unify env (S n) (Generic (mkGenericRef None p bp)) (Generic (mkGenericRef None q bq)) (Ongoing s) = Some (Ongoing u) ->
    q = p /\ u = s.
Proof.
    intros n p bp q bq u Hf Hc H. rewrite unify_step_once in H. unfold unify_step, unify_generic in H.
    cbn [generic_is_subtype_of] in H. destruct (param_eqb q p) eqn:E.
    - apply param_eqb_eq in E. split; [exact E|]. destruct (Model.is_subtype_of _ _); injection H; auto. discriminate.
    - destruct (sfrag_cases bq Hf) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[? [? [-> _]]]]]];
          [discriminate H|discriminate H|discriminate H|discriminate Hc].
Qed.

Lemma inst_nested_generic: forall gm p bound v o x,
    lookup_binding b p = Some (TypeArgument v o x) -> inst_nested b (Generic (mkGenericRef gm p bound)) = x.
Proof. intros gm p bound v o x H. simpl. rewrite H. reflexivity. Qed.

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

(* ---------------------------------------------------------------------------------------------- *)
(* The substitution lemma                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

Section Main.

(* The fuel it takes to unify a type argument of the bindings with itself, and one to spare *)
Variable E: nat.
Hypothesis HE2: 2 <= E.
Hypothesis HE: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> depth x <= E.

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
      (* a type parameter assigned to a class type: its type argument is assignable to the bound *)
      assert (Hvia: forall q bnd, sfrag bnd = true -> closed bnd = true -> bound_in (Generic (mkGenericRef None q bnd)) = true ->
          unify env n t bnd (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (P + E + S K)) (inst_nested b t) (inst_nested b (Generic (mkGenericRef None q bnd))) (Ongoing s)
              = Some (Ongoing s)).
      { intros q bnd Hfb Hcb Hbq Hu.
        destruct (proj1 (closed_facts (sdepth bnd)) bnd (le_n _) Hfb Hcb) as [HTb [Hib [Hbb _]]].
        destruct (IHt t bnd u Ht Hfb Hbt Hbb Hu) as [-> Hi].
        assert (Hnb: inst_nested b bnd = bnd).
        { destruct (sfrag_cases bnd Hfb) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[? [? [-> _]]]]]];
              [exact Hib|exact Hib|exact Hib|discriminate Hcb]. }
        rewrite Hnb in Hi. simpl in Hbq. destruct (binds_exactly_some q bnd Hbq) as [o [x [Ex [_ [Hx Hr]]]]].
        rewrite (inst_nested_generic None q bnd _ o x Ex). split; [reflexivity|].
        apply (unify_fuel_monotone env (K + (P + E))); [lia|].
        apply (proj1 (transitivity_with_arguments env wf (K + (P + E))) x bnd (inst_nested b t) K (P + E) s (le_n _));
            [exact Hx|exact HTb|apply instance_in_fragment; assumption|apply respects_unify; assumption|exact Hi]. }
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
        destruct (sfrag_cases _ Hfa) as [[ma' [ca' [aargs' [Heq [_ [Hla Haargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
            try discriminate Heq;
            [injection Heq as <- <- <-|unfold bottom_type in Heq; injection Heq as _ -> _; rewrite class_eqb_refl in Hcn; discriminate Hcn].
        assert (Htargs: forall a, In a targs -> argument_sfrag a = true).
        { destruct (sfrag_cases _ Hft) as [[mt' [ct' [targs' [Heq [_ [_ Htargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
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
      destruct (sfrag_cases t Ht) as [[mt [ct [targs [-> _]]]]|[->|[[mt [ct [targs [-> Ht']]]]|[p [bt [-> [Hfbt Hcbt]]]]]]];
      destruct (sfrag_cases a Ha) as [[ma [ca [aargs [-> [Hca _]]]]]|[->|[[ma [ca [aargs [-> Ha']]]]|[q [ba [-> [Hfba Hcba]]]]]]];
          unfold bottom_type in *.
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_root_generic in H. exact (Hvia q ba Hfba Hcba Hba H).
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + exact (Hroot _ _ _ _ _ _ Ht Ha Hbt Hba H).
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_root_generic in H. exact (Hvia q ba Hfba Hcba Hba H).
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
      + rewrite unify_nullable_generic in H. exact (Hvia q ba Hfba Hcba Hba H).
      + rewrite unify_generic_root, Hca in H. cbn [andb] in H. discriminate H.
      + rewrite unify_generic_root, class_eqb_refl in H. cbn [andb] in H.
        destruct (Model.is_subtype_of _ _); [|discriminate H]. injection H as <-. split; [reflexivity|].
        simpl in Hbt. destruct (binds_exactly_some p bt Hbt) as [o [x [Ex [_ [Hx _]]]]].
        rewrite (inst_nested_generic None p bt _ o x Ex). apply below_all; [exact Hx|lia].
      + rewrite unify_generic_nullable in H. discriminate H.
      + destruct (unify_generic_generic n p bt q ba u Hfba Hcba H) as [-> ->]. split; [reflexivity|].
        simpl in Hbt. destruct (binds_exactly_some p bt Hbt) as [o [x [Ex [_ [Hx _]]]]].
        rewrite (inst_nested_generic None p bt _ o x Ex), (inst_nested_generic None p ba _ o x Ex).
        apply (proj1 (reflexivity_with_arguments env _)); [exact Hx|]. pose proof (HE p o x Ex). lia.
    - intros [| | | |vt ot nt| |] [| | | |va oa na| |] u Ht Ha Hbt Hba H; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha.
      destruct (bound_in_argument vt ot nt Hbt) as [_ Hbnt]. destruct (bound_in_argument va oa na Hba) as [_ Hbna].
      rewrite (instantiate_bound_argument vt ot nt Ht Hbnt), (instantiate_bound_argument va oa na Ha Hbna).
      rewrite unify_type_arguments in H |- * by first
          [ apply (fragment_not_variable env); apply instance_in_fragment; assumption
          | destruct (sfrag_cases nt Ht) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[? [? [-> _]]]]]]; reflexivity ].
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
 * the type parameters in both instantiated exactly, within their bounds (with fuel K). The fuel it
 * takes grows by the fuel the bounds take, and by the depth of the type arguments (E).
 *)
Theorem substitution_lemma: forall b K E fuel t a,
    2 <= E -> (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> depth x <= E) ->
    sfrag t = true -> sfrag a = true -> bound_in b K [] t = true -> bound_in b K [] a = true ->
    is_assignable_to env fuel a t = Some true ->
    is_assignable_to env (fuel * S (S K) + E) (inst_nested b a) (inst_nested b t) = Some true.
Proof.
    intros b K E fuel t a HE2 HE Ht Ha Hbt Hba H. unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel t a (Ongoing [])) as [[u|]|] eqn:Eu; try discriminate H.
    destruct (proj1 (substitution_with_arguments b K [] E HE2 HE fuel) t a u Ht Ha Hbt Hba Eu) as [_ Hi].
    rewrite Hi. reflexivity.
Qed.

End Substitution.
