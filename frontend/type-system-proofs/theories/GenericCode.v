From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import MemberCalls.
From EmergeTypeSystem Require Import FinalValues.
From EmergeTypeSystem Require Import SubstitutionWide.
From EmergeTypeSystem Require Import WithinBounds.
From EmergeTypeSystem Require Import FreeInstances.
From EmergeTypeSystem Require Import GenericArguments.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Calls in generic code, instantiated                                                            *)
(*                                                                                                *)
(* Generic code is checked once, with its type parameters as they are. A call in it, of a member  *)
(* function with type parameters of its own, is sound for those types (GenericArguments.v). At    *)
(* run time, the type parameters of the caller are bound to type arguments (sigma), and those of  *)
(* the callee to the final values of inference, instantiated by sigma in turn: the type of a      *)
(* parameter becomes `instantiate sigma (inst b P)`. Each argument, instantiated, fits it         *)
(* (member_call_in_generic_code_instantiated): what inference accepted in the generic code stays  *)
(* accepted, by the substitution lemma of SubstitutionWide.v, with the references within their    *)
(* bounds by WithinBounds.v.                                                                      *)
(*                                                                                                *)
(* That takes the types of generic code (caller_type): of the wide fragment of                    *)
(* SubstitutionWide.v, the references in them as GenericTypeReference makes them, to the type     *)
(* parameters of the caller. For the final values of inference to be of them, intersect and       *)
(* closestCommonSupertypeWith are taken to build them (intersect_stays_in_generic_code,           *)
(* closest_common_supertype_stays_in_generic_code), which the theorem takes as premises, like     *)
(* those of Conjectures.v.                                                                        *)
(*                                                                                                *)
(* The object called on is of a type without type parameters, as objects at run time are.         *)
(* ---------------------------------------------------------------------------------------------- *)

Section CallerTypes.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
(* The type parameters of the caller *)
Variable ps: list TypeParameterId.

(* The types of generic code: of the wide fragment, the references in them as GenericTypeReference
   makes them, to the type parameters of the caller *)
Definition caller_type (t: EType): Prop := wtfrag env t = true /\ built env declared t /\ mentions_only env ps t.

Lemma wtfrag_root_arguments: forall m c args a, wtfrag env (RootResolved m c args) = true -> In a args ->
    argument_wfrag env a = true.
Proof.
    intros m c args a H Ha. change (wfrag env (RootResolved m c args) = true) in H. cbn [wfrag] in H.
    destruct (class_eqb c nothing).
    - destruct m as [[]|], args; simpl in H; try discriminate H. destruct Ha.
    - apply andb_true_iff in H. destruct H as [_ H]. rewrite forallb_forall in H. specialize (H a Ha).
      destruct a as [| | | |v o n| |]; try discriminate H. exact H.
Qed.

Lemma caller_top: caller_type top_type.
Proof.
    split; [|split; exact I]. change (wfrag env (RootResolved (Some readonly) any []) = true). cbn [wfrag].
    simpl. rewrite (wf_any_has_no_type_parameters env wf). reflexivity.
Qed.

Lemma caller_any: forall m, caller_type (RootResolved (Some m) any []).
Proof.
    intros m. split; [|split; exact I]. change (wfrag env (RootResolved (Some m) any []) = true). cbn [wfrag].
    simpl. rewrite (wf_any_has_no_type_parameters env wf). reflexivity.
Qed.

Lemma caller_bottom: caller_type bottom_type.
Proof.
    split; [|split; exact I]. change (wfrag env (RootResolved (Some exclusive) nothing []) = true). cbn [wfrag].
    simpl. reflexivity.
Qed.

(* A type argument of generic code: of a type of it, of an ownership of the caller *)
Definition caller_argument (a: EType): Prop :=
    match a with TypeArgument _ _ n => caller_type n | _ => False end /\ mentions_only env ps a.

Lemma caller_argument_nested: forall v o n, caller_argument (TypeArgument v o n) -> caller_type n.
Proof. intros v o n [H _]. exact H. Qed.

Lemma caller_root: forall m c args a, caller_type (RootResolved m c args) -> In a args -> caller_argument a.
Proof.
    intros m c args a [Hw [Hb Hm]] Ha. pose proof (wtfrag_root_arguments m c args a Hw Ha) as Hwa.
    split; [|exact (fold_and_in _ args Hm _ Ha)].
    destruct a as [| | | |v o n| |]; try discriminate Hwa.
    split; [exact Hwa|]. split; [exact I|exact (proj2 (fold_and_in _ args Hm _ Ha))].
Qed.

Lemma caller_nullable: forall n, caller_type (Nullable n) -> caller_type n.
Proof. intros n [Hw [Hb Hm]]. split; [exact (wtfrag_nullable_inner env n Hw)|split; assumption]. Qed.

Lemma caller_bound: forall g, caller_type (Generic g) -> caller_type (effective_bound env g).
Proof.
    intros g [Hw [Hb Hm]]. destruct (generic_of_wtfrag env wf _ Hw) as [Ht _].
    split; [exact (tfrag_wtfrag env wf _ Ht)|]. split; [exact I|exact (mentions_only_generic env wf ps g Hm)].
Qed.

Lemma caller_component: forall cs c, caller_type (Intersection cs) -> In c cs -> caller_type c.
Proof.
    intros cs c [Hw [Hb Hm]] Hc. destruct (wcomponents_facts env cs Hw) as [_ Hcs].
    split; [exact (wfrag_wtfrag env c (proj2 (Hcs c Hc)))|]. split; [exact I|exact (fold_and_in _ cs Hm c Hc)].
Qed.

Lemma caller_nullable_component: forall cs c, caller_type (Nullable (Intersection cs)) -> In c cs -> caller_type (Nullable c).
Proof.
    intros cs c [Hw [Hb Hm]] Hc. destruct (wcomponents_facts env cs Hw) as [_ Hcs]. destruct (Hcs c Hc) as [Hsh Hwc].
    split; [|split; [exact I|exact (fold_and_in _ cs Hm c Hc)]].
    assert (Hcl: is_class c || is_generic c = true) by (unfold is_component_shape in Hsh; apply andb_true_iff in Hsh; exact (proj1 Hsh)).
    destruct c as [m cl args|n|g|me msg|v o n|g|cs']; try discriminate Hcl; cbn [wtfrag].
    - change ((is_class (RootResolved m cl args) || is_generic (RootResolved m cl args)) && wfrag env (RootResolved m cl args) = true).
      rewrite Hwc. reflexivity.
    - change ((is_class (Generic g) || is_generic (Generic g)) && wfrag env (Generic g) = true). rewrite Hwc. reflexivity.
Qed.

Lemma built_without_null: forall t, built env declared t -> built env declared (without_null env t).
Proof. intros. exact I. Qed.

Lemma mentions_without_null: forall t, mentions_only env ps t -> mentions_only env ps (without_null env t).
Proof. exact (mentions_only_without_null env ps). Qed.

Lemma caller_narrowed: forall g, caller_type (Generic g) -> caller_type (without_null env (Generic g)).
Proof.
    intros g [Hw [Hb Hm]]. split; [|split; [exact (built_without_null _ Hb)|exact (mentions_without_null _ Hm)]].
    pose proof (generic_of_wtfrag env wf g Hw) as Hg. pose proof (generic_sfrag_sfrag env wf g Hg) as Hs.
    destruct (tfrag_without_null env wf _ (Generic g) (le_n _) (sfrag_tfrag env _ Hs)) as [Ht' _].
    exact (tfrag_wtfrag env wf _ Ht').
Qed.

(* Made nullable, or without null, a type of generic code is one *)
Lemma caller_rewrap: forall t, caller_type t -> caller_type (rewrap_nullable t).
Proof.
    intros t [Hw [Hb Hm]]. split; [|split; [exact I|]];
        destruct t as [m c args|n|g|me msg|v o n|g|cs]; cbn [rewrap_nullable]; first [exact Hw|exact Hm].
Qed.

Lemma caller_without_null: forall t, caller_type t -> caller_type (without_null env t).
Proof.
    assert (Hshape: forall n, caller_type n -> match n with Nullable _ => False | _ => True end -> caller_type (without_null env n)).
    { intros [m c args|n|g|me msg|v o n|g|cs] Hc Hs; try contradiction; try exact Hc;
          try (rewrite (without_null_not_nullable_intersection env cs (wcomponents_not_nullable env cs (proj1 Hc))); exact Hc);
          try exact (caller_narrowed g Hc); destruct Hc as [Hw _]; discriminate Hw. }
    intros [m c args|n|g|me msg|v o n|g|cs] Hc; try (apply Hshape; [exact Hc|exact I]).
    change (caller_type (without_null env n)). apply Hshape; [exact (caller_nullable n Hc)|].
    destruct Hc as [Hw _]. destruct n; try exact I. discriminate Hw.
Qed.

Lemma caller_without_null_not_nullable: forall t, caller_type t -> is_nullable env (without_null env t) = false.
Proof.
    assert (Hg: forall gm nn p vs, wtfrag env (Generic (mkGenericRef gm nn p vs)) = true ->
        is_nullable env (without_null env (Generic (mkGenericRef gm nn p vs))) = false).
    { intros gm nn p vs Hw. destruct (generic_of_wtfrag env wf _ Hw) as [_ [_ [Hv _]]].
      cbn [no_type_variables variables_of] in Hv. destruct vs; [|discriminate Hv].
      exact (proj2 (proj2 (narrowed_ref env wf declared declared_wf gm nn p))). }
    intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] [Hw _]; try discriminate Hw; try reflexivity.
    - cbn [without_null]. destruct n as [m c args|n'|[gm nn p vs]|me msg|v o n'|g|cs]; try discriminate Hw; try reflexivity.
      + exact (Hg gm nn p vs Hw).
      + rewrite (without_null_not_nullable_intersection env cs (wcomponents_not_nullable env cs Hw)).
        exact (wcomponents_not_nullable env cs Hw).
    - exact (Hg gm nn p vs Hw).
    - rewrite (without_null_not_nullable_intersection env cs (wcomponents_not_nullable env cs Hw)).
      exact (wcomponents_not_nullable env cs Hw).
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* A mutability given to a type of generic code                                                    *)
(*                                                                                                *)
(* Instantiating `m T` with T bound to x gives x the meet of its own mutability and m (ref_apply).  *)
(* A mutability no more than its own keeps a type of the fragment one: for `exclusive Nothing`, as  *)
(* that leaves it exclusive; for a reference to a type parameter, as its effective bound takes the  *)
(* mutability given (effective_bound_given); for an intersection, as its components take the one   *)
(* they are assigned as in common, exclusive where one of them is const.                           *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma with_mutability_rewrap: forall k y, with_mutability env k (rewrap_nullable y) = rewrap_nullable (with_mutability env k y).
Proof. intros k [m c args|n|g|me msg|v o n|g|cs]; try reflexivity. cbn [rewrap_nullable with_mutability]. destruct (with_mutability env k n); reflexivity. Qed.

(* Applying a mutability replaces the one before *)
Lemma with_mutability_twice: forall k m t, with_mutability env k (with_mutability env m t) = with_mutability env k t.
Proof.
    fix IH 3. intros k m [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; try reflexivity.
    - cbn [with_mutability]. rewrite with_mutability_rewrap, IH. reflexivity.
    - cbn [with_mutability]. rewrite IH. reflexivity.
    - cbn [with_mutability].
      generalize (fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly) as c1.
      intros c1. rewrite !map_map.
      assert (E: forall j, map (fun c => with_mutability env j (with_mutability env c1 c)) cs = map (with_mutability env j) cs).
      { intros j. clear m. induction cs as [|c cs IHc]; [reflexivity|]. cbn [map]. rewrite (IH j c1 c), IHc. reflexivity. }
      assert (E2: map (fun c => assignment_mutability env (with_mutability env k (with_mutability env c1 c))) cs
          = map (fun c => assignment_mutability env (with_mutability env k c)) cs).
      { clear m E. induction cs as [|c cs IHc]; [reflexivity|]. cbn [map]. rewrite (IH k c1 c), IHc. reflexivity. }
      rewrite E2, E. reflexivity.
Qed.

Lemma with_mutability_without_null: forall k t, with_mutability env k (without_null env t) = without_null env (with_mutability env k t).
Proof.
    fix IH 2. intros k [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; try reflexivity.
    - cbn [without_null with_mutability]. rewrite IH, (without_null_rewrap env). reflexivity.
    - pose proof (proj1 (proj2 (with_mutability_keeps env ranked k (Generic (mkGenericRef gm nn p vs))))) as E.
      cbn [with_mutability is_nullable] in E. cbn [without_null with_mutability]. rewrite E. reflexivity.
    - cbn [without_null with_mutability]. rewrite IH. reflexivity.
    - cbn [without_null with_mutability].
      assert (Hn: forall m', forallb (is_nullable env) (map (with_mutability env m') cs) = forallb (is_nullable env) cs).
      { intros m'. clear IH. induction cs as [|c cs IHc]; [reflexivity|]. cbn [map forallb].
        rewrite (proj1 (proj2 (with_mutability_keeps env ranked m' c))), IHc. reflexivity. }
      rewrite Hn. destruct (forallb (is_nullable env) cs); [|reflexivity]. cbn [with_mutability].
      assert (Ec: map (fun c => assignment_mutability env (with_mutability env k c)) (map (without_null env) cs)
          = map (fun c => assignment_mutability env (with_mutability env k c)) cs).
      { clear Hn. induction cs as [|c cs IHc]; [reflexivity|]. cbn [map].
        rewrite IH, (without_null_keeps_assignment_mutability env ranked), IHc. reflexivity. }
      rewrite Ec. f_equal. generalize (fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env k c)) cs) readonly).
      intros m'. clear Hn Ec. induction cs as [|c cs IHc]; [reflexivity|]. cbn [map]. rewrite IH, IHc. reflexivity.
Qed.

(* The effective bound of a reference given a mutability is that of the reference, of the mutability *)
Lemma effective_bound_given: forall k gm nn p,
    effective_bound env (mkGenericRef (Some k) nn p []) = with_mutability env k (effective_bound env (mkGenericRef gm nn p [])).
Proof.
    intros k gm nn p. rewrite !(effective_bound_eq env ranked). cbn [with_type_variables variables_of given_mutability is_narrowed param_of].
    destruct nn, gm; try rewrite with_mutability_without_null; try rewrite with_mutability_twice; reflexivity.
Qed.

(* The mutability the components of an intersection take *)
Lemma common_given: forall k cs, cs <> [] ->
    (forall c, In c cs -> assignment_mutability env (with_mutability env k c) = if top_const env c then exclusive else k) ->
    fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env k c)) cs) readonly
    = if existsb (top_const env) cs then exclusive else k.
Proof.
    intros k cs Hne H. rewrite (fold_intersect_const env _ k cs readonly H).
    destruct (existsb (top_const env) cs), cs; try contradiction; destruct k; reflexivity.
Qed.

Lemma common_below: forall k cs, Model.is_subtype_of k (mutability_of env (Intersection cs)) = true ->
    forall c, In c cs -> Model.is_subtype_of (if existsb (top_const env) cs then exclusive else k) (mutability_of env c) = true.
Proof.
    intros k cs Hk c Hc. cbn [mutability_of] in Hk. destruct (existsb (top_const env) cs); [destruct (mutability_of env c); reflexivity|].
    apply (mutability_subtype_trans _ _ _ Hk). apply fold_intersect_below_element. apply in_map, Hc.
Qed.

(* A type of the fragment, of a mutability applied to it, is assigned as that mutability, or as
   exclusive where its values are objects of a const class *)
Lemma assignment_given: forall n t k, tdepth env t < n -> tfrag env t = true ->
    assignment_mutability env (with_mutability env k t) = if top_const env t then exclusive else k.
Proof.
    induction n as [|n IH]; [intros; lia|].
    assert (Hgen: forall gm nn p vs k, tdepth env (Generic (mkGenericRef gm nn p vs)) < S n -> generic_sfrag env (mkGenericRef gm nn p vs) ->
        assignment_mutability env (with_mutability env k (Generic (mkGenericRef gm nn p vs)))
        = if top_const env (Generic (mkGenericRef gm nn p vs)) then exclusive else k).
    { intros gm nn p vs k Hd [Hf [_ [Hv _]]]. destruct vs; [|discriminate Hv]. rewrite (tdepth_bound env wf) in Hd.
      cbn [with_mutability]. rewrite !(assignment_mutability_generic env ranked), (top_const_generic env ranked), (effective_bound_given k gm nn p).
      exact (IH (effective_bound env (mkGenericRef gm nn p [])) k ltac:(lia) Hf). }
    assert (Hs: forall t k, tdepth env t < S n -> sfrag env t = true ->
        assignment_mutability env (with_mutability env k t) = if top_const env t then exclusive else k).
    { intros t k Hd Ht.
      destruct (sfrag_cases env wf t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[[gm nn p vs] [-> Hg]]|[[gm nn p vs] [-> Hg]]]]]].
      - cbn [with_mutability assignment_mutability top_const]. destruct (is_const _); reflexivity.
      - unfold bottom_type. cbn [with_mutability assignment_mutability top_const]. destruct (is_const _); reflexivity.
      - cbn [with_mutability rewrap_nullable assignment_mutability top_const]. destruct (is_const _); reflexivity.
      - exact (Hgen gm nn p vs k Hd Hg).
      - change (S (tdepth env (Generic (mkGenericRef gm nn p vs))) < S n) in Hd. exact (Hgen gm nn p vs k ltac:(lia) Hg). }
    intros t k Hd Ht. destruct (tfrag_cases env t Ht) as [Hs'|[[cs [-> Hcs]]|[cs [-> Hcs]]]]; [exact (Hs t k Hd Hs')| |].
    all: destruct (components_sfrag_facts env cs Hcs) as [Hlen Hc].
    all: assert (Hne: cs <> []) by (intros ->; simpl in Hlen; lia).
    all: assert (Hall: forall j c, In c cs -> assignment_mutability env (with_mutability env j c) = if top_const env c then exclusive else j)
        by (intros j c Hin; pose proof (tdepth_component env cs c Hin); cbn [tdepth] in *;
            exact (Hs c j ltac:(lia) (proj2 (Hc c Hin)))).
    all: cbn [with_mutability rewrap_nullable assignment_mutability top_const].
    all: rewrite (common_given k cs Hne (Hall k)), map_map.
    all: rewrite (common_given _ cs Hne (Hall _)).
    all: destruct (existsb (top_const env) cs); reflexivity.
Qed.

(* ... a type of the fragment, where the mutability is no more than its own *)
Lemma tfrag_given: forall n t k, tdepth env t < n -> tfrag env t = true -> Model.is_subtype_of k (mutability_of env t) = true ->
    tfrag env (with_mutability env k t) = true.
Proof.
    induction n as [|n IH]; [intros; lia|].
    assert (Hroot: forall m c args k, sfrag env (RootResolved m c args) = true ->
        Model.is_subtype_of k (mutability_of env (RootResolved m c args)) = true -> sfrag env (with_mutability env k (RootResolved m c args)) = true).
    { intros m c args k H Hk. cbn [with_mutability sfrag] in H |- *. destruct (class_eqb c nothing) eqn:Ec; [|exact H].
      apply class_eqb_true in Ec. subst c. cbn [mutability_of] in Hk. rewrite (wf_nothing_is_not_const env wf) in Hk |- *.
      destruct m as [[]|], args; simpl in H; try discriminate H. cbn [or_readonly] in Hk.
      rewrite (mutability_subtype_of_exclusive k Hk). reflexivity. }
    assert (Hgen: forall gm nn p k, tdepth env (Generic (mkGenericRef gm nn p [])) < S n -> generic_sfrag env (mkGenericRef gm nn p []) ->
        Model.is_subtype_of k (mutability_of env (Generic (mkGenericRef gm nn p []))) = true ->
        sfrag env (Generic (mkGenericRef (Some k) nn p [])) = true).
    { intros gm nn p k Hd [Hf [Hw [Hv Hp]]] Hk. rewrite (tdepth_bound env wf) in Hd. rewrite (mutability_of_generic env ranked) in Hk.
      apply (generic_sfrag_sfrag env wf). pose proof (effective_bound_given k gm nn p) as Ee.
      split; [rewrite Ee; exact (IH (effective_bound env (mkGenericRef gm nn p [])) k ltac:(lia) Hf Hk)|]. split; [|split; [reflexivity|exact Hp]].
      unfold as_written in Hw |- *. cbn [given_mutability is_narrowed] in Hw |- *.
      rewrite Ee, (assignment_given (S n) (effective_bound env (mkGenericRef gm nn p [])) k ltac:(lia) Hf), (proj1 (proj2 (with_mutability_keeps env ranked k _))).
      apply andb_true_iff in Hw. destruct Hw as [_ Hwn]. rewrite Hwn, andb_true_r. destruct (top_const env _), k; reflexivity. }
    assert (Hint: forall cs k, tdepth env (Intersection cs) < S n -> components_sfrag env cs = true ->
        Model.is_subtype_of k (mutability_of env (Intersection cs)) = true ->
        exists cs', with_mutability env k (Intersection cs) = Intersection cs' /\ components_sfrag env cs' = true).
    { intros cs k Hd Hcs Hk. destruct (components_sfrag_facts env cs Hcs) as [Hlen Hc].
      assert (Hne: cs <> []) by (intros ->; simpl in Hlen; lia).
      assert (Hdc: forall c, In c cs -> tdepth env c < n)
          by (intros c Hin; pose proof (tdepth_component env cs c Hin); lia).
      set (C := if existsb (top_const env) cs then exclusive else k).
      exists (map (with_mutability env C) cs). split.
      - cbn [with_mutability]. unfold C. rewrite (common_given k cs Hne).
        + reflexivity.
        + intros c Hin. exact (assignment_given (S n) c k ltac:(pose proof (Hdc c Hin); lia) (sfrag_tfrag env c (proj2 (Hc c Hin)))).
      - unfold components_sfrag. rewrite length_map. apply andb_true_iff. split; [apply Nat.leb_le; lia|].
        apply forallb_forall. intros c' Hc'. apply in_map_iff in Hc'. destruct Hc' as [c [<- Hin]].
        pose proof (common_below k cs Hk c Hin) as HC. fold C in HC. pose proof (Hdc c Hin) as Hdc'. destruct (Hc c Hin) as [Hsh Hsc].
        destruct (sfrag_cases env wf c Hsc) as [[m [cl [args [Ec _]]]]|[Ec|[[m [cl [args [Ec _]]]]|[[[gm nn p vs] [Ec Hg]]|[[gm nn p vs] [Ec Hg]]]]]];
            subst c; try discriminate Hsh.
        + apply andb_true_iff. split; [reflexivity|exact (Hroot m cl args C Hsc HC)].
        + apply andb_true_iff. split; [reflexivity|exact (Hroot _ _ _ C Hsc HC)].
        + destruct vs; [|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv]. apply andb_true_iff. split.
          * unfold is_component_shape in Hsh |- *. rewrite (proj1 (proj2 (with_mutability_keeps env ranked C _))). exact Hsh.
          * exact (Hgen gm nn p C ltac:(lia) Hg HC). }
    intros t k Hd Ht Hk. destruct (tfrag_cases env t Ht) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (sfrag_cases env wf t Hs) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[[[gm nn p vs] [-> Hg]]|[[gm nn p vs] [-> Hg]]]]]].
      + exact (Hroot m c args k Hs Hk).
      + exact (Hroot _ _ _ k Hs Hk).
      + change ((is_class (with_mutability env k (RootResolved m c args)) || is_generic (with_mutability env k (RootResolved m c args)))
            && sfrag env (with_mutability env k (RootResolved m c args)) = true).
        rewrite (Hroot m c args k Ht' Hk). reflexivity.
      + destruct vs; [|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv]. exact (Hgen gm nn p k Hd Hg Hk).
      + destruct vs; [|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv].
        change (S (tdepth env (Generic (mkGenericRef gm nn p []))) < S n) in Hd.
        change ((is_class (Generic (mkGenericRef (Some k) nn p [])) || is_generic (Generic (mkGenericRef (Some k) nn p [])))
            && sfrag env (Generic (mkGenericRef (Some k) nn p [])) = true).
        rewrite (Hgen gm nn p k ltac:(lia) Hg Hk). reflexivity.
    - destruct (Hint cs k Hd Hcs Hk) as [cs' [E H]]. rewrite E. exact H.
    - change (S (tdepth env (Intersection cs)) < S n) in Hd. destruct (Hint cs k ltac:(lia) Hcs Hk) as [cs' [E H]].
      change (tfrag env (rewrap_nullable (with_mutability env k (Intersection cs))) = true). rewrite E. exact H.
Qed.


(* ... a type of generic code, of the wide fragment *)
Lemma wtfrag_given: forall t k, wtfrag env t = true -> Model.is_subtype_of k (mutability_of env t) = true ->
    wtfrag env (with_mutability env k t) = true.
Proof.
    assert (Hroot: forall m c args k, wfrag env (RootResolved m c args) = true ->
        Model.is_subtype_of k (mutability_of env (RootResolved m c args)) = true -> wfrag env (with_mutability env k (RootResolved m c args)) = true).
    { intros m c args k H Hk. cbn [with_mutability wfrag] in H |- *. destruct (class_eqb c nothing) eqn:Ec; [|exact H].
      apply class_eqb_true in Ec. subst c. cbn [mutability_of] in Hk. rewrite (wf_nothing_is_not_const env wf) in Hk |- *.
      destruct m as [[]|], args; simpl in H; try discriminate H. cbn [or_readonly] in Hk.
      rewrite (mutability_subtype_of_exclusive k Hk). reflexivity. }
    assert (Hgen: forall g k, wfrag env (Generic g) = true -> Model.is_subtype_of k (mutability_of env (Generic g)) = true ->
        wfrag env (with_mutability env k (Generic g)) = true).
    { intros [gm nn p vs] k H Hk. change (sfrag env (Generic (mkGenericRef gm nn p vs)) = true) in H.
      exact (tfrag_given (S (tdepth env (Generic (mkGenericRef gm nn p vs)))) _ k (le_n _) (sfrag_tfrag env _ H) Hk). }
    assert (Hassign: forall c j, wfrag env c = true -> is_component_shape env c = true ->
        assignment_mutability env (with_mutability env j c) = if top_const env c then exclusive else j).
    { intros c j Hw Hsh.
      destruct (wfrag_cases env wf c Hw) as [[m [cl [args [-> _]]]]|[->|[[m [cl [args [-> _]]]]|[[g [-> Hg]]|[g [-> Hg]]]]]];
          try discriminate Hsh.
      - cbn [with_mutability assignment_mutability top_const]. destruct (is_const _); reflexivity.
      - unfold bottom_type. cbn [with_mutability assignment_mutability top_const]. destruct (is_const _); reflexivity.
      - exact (assignment_given (S (tdepth env (Generic g))) (Generic g) j (le_n _) (sfrag_tfrag env _ (generic_sfrag_sfrag env wf g Hg))). }
    assert (Hint: forall cs k, wcomponents env cs = true -> Model.is_subtype_of k (mutability_of env (Intersection cs)) = true ->
        exists cs', with_mutability env k (Intersection cs) = Intersection cs' /\ wcomponents env cs' = true).
    { intros cs k Hcs Hk. destruct (wcomponents_facts env cs Hcs) as [Hlen Hc].
      assert (Hne: cs <> []) by (intros ->; simpl in Hlen; lia).
      set (C := if existsb (top_const env) cs then exclusive else k).
      exists (map (with_mutability env C) cs). split.
      - cbn [with_mutability]. unfold C. rewrite (common_given k cs Hne); [reflexivity|].
        intros c Hin. exact (Hassign c k (proj2 (Hc c Hin)) (proj1 (Hc c Hin))).
      - unfold wcomponents. rewrite length_map. apply andb_true_iff. split; [apply Nat.leb_le; lia|].
        apply forallb_forall. intros c' Hc'. apply in_map_iff in Hc'. destruct Hc' as [c [<- Hin]].
        pose proof (common_below k cs Hk c Hin) as HC. fold C in HC. destruct (Hc c Hin) as [Hsh Hwc].
        destruct (wfrag_cases env wf c Hwc) as [[m [cl [args [Ec _]]]]|[Ec|[[m [cl [args [Ec _]]]]|[[[gm nn p vs] [Ec Hg]]|[[gm nn p vs] [Ec Hg]]]]]];
            subst c; try discriminate Hsh.
        + apply andb_true_iff. split; [reflexivity|exact (Hroot m cl args C Hwc HC)].
        + apply andb_true_iff. split; [reflexivity|exact (Hroot _ _ _ C Hwc HC)].
        + apply andb_true_iff. split.
          * unfold is_component_shape in Hsh |- *. rewrite (proj1 (proj2 (with_mutability_keeps env ranked C _))). exact Hsh.
          * exact (Hgen _ C Hwc HC). }
    assert (Hw: forall t k, wfrag env t = true -> Model.is_subtype_of k (mutability_of env t) = true -> wfrag env (with_mutability env k t) = true).
    { intros t k H Hk. destruct (wfrag_cases env wf t H) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> H']]]]|[[g [-> Hg]]|[[gm nn p vs] [-> Hg]]]]]].
      - exact (Hroot _ _ _ k H Hk).
      - exact (Hroot _ _ _ k H Hk).
      - change ((is_class (with_mutability env k (RootResolved m c args)) || is_generic (with_mutability env k (RootResolved m c args)))
            && wfrag env (with_mutability env k (RootResolved m c args)) = true).
        rewrite (Hroot m c args k H' Hk). reflexivity.
      - exact (Hgen g k H Hk).
      - pose proof (Hgen (mkGenericRef gm nn p vs) k (generic_sfrag_sfrag env wf _ Hg) Hk) as E. cbn [with_mutability] in E.
        change ((is_class (Generic (mkGenericRef (Some k) nn p vs)) || is_generic (Generic (mkGenericRef (Some k) nn p vs)))
            && wfrag env (Generic (mkGenericRef (Some k) nn p vs)) = true).
        rewrite E. reflexivity. }
    intros t k Ht Hk.
    destruct t as [m c args|[m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs];
        try (exfalso; cbn in Ht; discriminate Ht); try exact (Hw _ k Ht Hk).
    - change (wtfrag env (rewrap_nullable (with_mutability env k (Intersection cs))) = true).
      destruct (Hint cs k Ht Hk) as [cs' [E H]]. rewrite E. exact H.
    - destruct (Hint cs k Ht Hk) as [cs' [E H]]. rewrite E. exact H.
Qed.

(* A type of generic code given a mutability, as instantiating `m T` gives it, or narrowed *)
Lemma caller_given: forall m x, caller_type x -> caller_type (with_mutability env (intersect_mutability (mutability_of env x) m) x).
Proof.
    intros m x [Hw [Hb Hm]]. split; [|split; [exact I|exact (mentions_only_with_mutability env ps _ x Hm)]].
    apply wtfrag_given; [exact Hw|apply intersect_mutability_left].
Qed.

Lemma caller_ref_apply: forall gm nn x, caller_type x -> caller_type (ref_apply env gm nn x).
Proof.
    intros gm nn x Hx. unfold ref_apply. cbn zeta.
    destruct gm as [m|]; [pose proof (caller_given m x Hx) as Hy|pose proof Hx as Hy]; destruct nn; first [exact (caller_without_null _ Hy)|exact Hy].
Qed.

(* A type of generic code without null, as a component of an intersection: a class type or a
   reference, non-null *)
Lemma caller_component_without_null: forall c, caller_type c -> wfrag env c = true ->
    caller_type (without_null env c) /\ is_component_shape env (without_null env c) = true /\ wfrag env (without_null env c) = true.
Proof.
    intros c Hc Hw. pose proof (caller_without_null c Hc) as Hc'. split; [exact Hc'|].
    destruct (wfrag_cases env wf c Hw) as [[m [d [args [-> _]]]]|[->|[[m [d [args [-> Hd]]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
    - split; [reflexivity|exact Hw].
    - split; [reflexivity|exact Hw].
    - split; [reflexivity|exact Hd].
    - destruct g as [gm nn p vs]. destruct Hg as [_ [_ [Hv _]]]. unfold no_type_variables in Hv. cbn [variables_of] in Hv.
      destruct vs; [|discriminate Hv]. destruct (narrowed_ref env wf declared declared_wf gm nn p) as [E1 [_ E3]].
      split; [unfold is_component_shape; rewrite E3, E1; reflexivity|exact (proj1 Hc')].
    - destruct g as [gm nn p vs]. destruct Hg as [_ [_ [Hv _]]]. unfold no_type_variables in Hv. cbn [variables_of] in Hv.
      destruct vs; [|discriminate Hv]. destruct (narrowed_ref env wf declared declared_wf gm nn p) as [E1 [_ E3]].
      change (without_null env (Nullable (Generic (mkGenericRef gm nn p [])))) with (without_null env (Generic (mkGenericRef gm nn p [])))
          in Hc' |- *.
      split; [unfold is_component_shape; rewrite E3, E1; reflexivity|exact (proj1 Hc')].
Qed.

(* An intersection of types of generic code, as ofComponents makes it (the components flattened,
   without null, of the mutability they are assigned as in common), is one *)
(* A value that may be null, other than a nullable type `X?`, is the value of a type parameter whose
   bound is nullable, as the values are within their bounds (values_respected). Otherwise, the
   instance of an intersection with a type parameter of a non-null bound among its components,
   `T & A?` with T bound to a P that may be null, keeps the nullability of its components, and is no
   type of generic code. *)
Definition nullability_respected (p: TypeParameterId) (x: EType): Prop :=
    is_nullable env x = true -> is_nullable_type x = true \/ is_nullable env (Generic (mkGenericRef None false p [])) = true.

(* A reference to a type parameter of a non-null bound, given a value that respects it: nullable only
   as a nullable type *)
Lemma ref_apply_nullable: forall gm nn q x, caller_type x -> nullability_respected q x ->
    is_nullable env (Generic (mkGenericRef gm nn q [])) = false ->
    is_nullable env (ref_apply env gm nn x) = true -> match ref_apply env gm nn x with Nullable _ => True | _ => False end.
Proof.
    intros gm nn q x Hx Hr Hg Hn. destruct nn.
    - exfalso. change (ref_apply env gm true x) with (without_null env (ref_apply env gm false x)) in Hn.
      rewrite (caller_without_null_not_nullable _ (caller_ref_apply gm false x Hx)) in Hn. discriminate Hn.
    - assert (Hnx: is_nullable env x = true)
          by (destruct gm as [m|]; [cbn [ref_apply] in Hn; rewrite (is_nullable_with_mutability env wf) in Hn|]; exact Hn).
      destruct (Hr Hnx) as [Ht|Hb].
      + destruct x as [| n | | | | |]; try discriminate Ht.
        destruct gm as [m|]; [cbn [ref_apply with_mutability]; match goal with |- context [rewrap_nullable ?w] => destruct w end|];
            exact I.
      + exfalso. destruct gm as [m|]; [|rewrite Hb in Hg; discriminate Hg].
        change (Generic (mkGenericRef (Some m) false q [])) with (with_mutability env m (Generic (mkGenericRef None false q []))) in Hg.
        rewrite (is_nullable_with_mutability env wf), Hb in Hg. discriminate Hg.
Qed.

Lemma caller_of_components: forall ys, 2 <= length ys -> (forall y, In y ys -> caller_type y) ->
    (* nullable only as nullable types: no type parameter that may be null among them *)
    (forall y, In y ys -> is_nullable env y = true -> match y with Nullable _ => True | _ => False end) ->
    caller_type (of_components env (flat_map intersected_components ys)).
Proof.
    intros ys Hl Hys Hno.
    (* the nullable components are nullable types *)
    assert (Hwr: forall z, In z (flat_map intersected_components ys) -> is_nullable env z = true -> is_nullable_type z = true).
    { intros z Hz Hnz. apply in_flat_map in Hz. destruct Hz as [y [Hy Hzy]].
      destruct y as [m c args|[m c args|n|g|me msg|v o n|g|cs]|g|me msg|v o n|g|cs];
          cbn [intersected_components] in Hzy;
          try (destruct Hzy as [<-|[]]; pose proof (Hno _ Hy Hnz) as F; first [reflexivity|contradiction F]).
      - apply in_map_iff in Hzy. destruct Hzy as [d [<- _]]. reflexivity.
      - destruct (wcomponents_facts env cs (proj1 (Hys _ Hy))) as [_ Hcs]. destruct (Hcs z Hzy) as [Hsh _].
        unfold is_component_shape in Hsh. apply andb_true_iff in Hsh. rewrite Hnz in Hsh. destruct Hsh as [_ F]. discriminate F. }
    assert (Hz: forall z, In z (flat_map intersected_components ys) ->
        caller_type (without_null env z) /\ is_component_shape env (without_null env z) = true /\ wfrag env (without_null env z) = true).
    { intros z Hz. apply in_flat_map in Hz. destruct Hz as [y [Hy Hzy]]. pose proof (Hys y Hy) as Hcy.
      destruct (wtfrag_cases env y (proj1 Hcy)) as [Hw|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
      - assert (Ey: intersected_components y = [y])
            by (destruct y as [| [| | | | | |cs] | | | | |cs]; try reflexivity; cbn in Hw; discriminate Hw).
        rewrite Ey in Hzy. destruct Hzy as [<-|[]]. exact (caller_component_without_null y Hcy Hw).
      - cbn [intersected_components] in Hzy. destruct (wcomponents_facts env cs Hcs) as [_ Hc].
        exact (caller_component_without_null z (caller_component cs z Hcy Hzy) (proj2 (Hc z Hzy))).
      - cbn [intersected_components] in Hzy. apply in_map_iff in Hzy. destruct Hzy as [d [<- Hd]].
        destruct (wcomponents_facts env cs Hcs) as [_ Hc].
        pose proof (caller_nullable_component cs d Hcy Hd) as Hcd.
        change (without_null env (Nullable d)) with (without_null env d).
        exact (caller_component_without_null d (caller_nullable d Hcd) (proj2 (Hc d Hd))). }
    assert (Hlen: 2 <= length (flat_map intersected_components ys)).
    { enough (Hge: length ys <= length (flat_map intersected_components ys)) by lia.
      assert (Hne: forall y, In y ys -> intersected_components y <> []).
      { intros y Hy. destruct (wtfrag_cases env y (proj1 (Hys y Hy))) as [Hw|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
        - destruct y as [| [| | | | | |cs] | | | | |cs]; try discriminate; cbn in Hw; discriminate Hw.
        - destruct (wcomponents_facts env cs Hcs) as [Hl' _]. destruct cs; [simpl in Hl'; lia|discriminate].
        - destruct (wcomponents_facts env cs Hcs) as [Hl' _]. destruct cs; [simpl in Hl'; lia|discriminate]. }
      clear -Hne. induction ys as [|y ys IH]; [simpl; lia|]. cbn [flat_map]. rewrite length_app. cbn [length].
      pose proof (Hne y (or_introl eq_refl)) as Hy. destruct (intersected_components y); [contradiction|].
      cbn [length]. pose proof (IH (fun y' Hy' => Hne y' (or_intror Hy'))). lia. }
    remember (flat_map intersected_components ys) as zs eqn:Ezs. clear Ezs Hys Hl.
    set (m := fold_left intersect_mutability (map (assignment_mutability env) zs) readonly).
    assert (Emeet: forall k k', Model.is_subtype_of k k' = true -> intersect_mutability k' k = k)
        by (intros [] [] H; first [reflexivity|discriminate H]).
    (* each component of the common mutability: of generic code *)
    assert (Hw: forall z, In z zs -> caller_type (with_mutability env m (without_null env z))
        /\ is_component_shape env (with_mutability env m (without_null env z)) = true
        /\ wfrag env (with_mutability env m (without_null env z)) = true).
    { intros z Hz'. destruct (Hz z Hz') as [Hcz [Hsz Hfz]].
      assert (Hmz: Model.is_subtype_of m (mutability_of env (without_null env z)) = true).
      { apply (mutability_subtype_trans _ (assignment_mutability env (without_null env z))); [|exact (assignment_mutability_below env (wf_bounds_ranked env wf) _)].
        rewrite (assignment_mutability_without_null env wf z). apply fold_intersect_below_element, in_map, Hz'. }
      pose proof (caller_given m _ Hcz) as Hc. rewrite (Emeet _ _ Hmz) in Hc.
      assert (Hshape: forall w, is_component_shape env w = true ->
          is_component_shape env (with_mutability env m w) = true
          /\ (wtfrag env (with_mutability env m w) = true -> wfrag env (with_mutability env m w) = true)).
      { intros w Hsw. unfold is_component_shape in Hsw |- *. rewrite (is_nullable_with_mutability env wf).
        destruct w as [m0 d args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; try discriminate Hsw;
            (split; [exact Hsw|intros Ht; exact Ht]). }
      destruct (Hshape _ Hsz) as [Hs Hf]. split; [exact Hc|]. split; [exact Hs|exact (Hf (proj1 Hc))]. }
    set (ws := map (fun c => with_mutability env m (without_null env c)) zs).
    assert (Hcws: wcomponents env ws = true).
    { unfold wcomponents. apply andb_true_iff. split; [unfold ws; rewrite length_map; apply Nat.leb_le; exact Hlen|].
      apply forallb_forall. intros w Hw'. unfold ws in Hw'. apply in_map_iff in Hw'. destruct Hw' as [z [<- Hz']].
      destruct (Hw z Hz') as [_ [Hs Hf]]. rewrite Hs, Hf. reflexivity. }
    assert (Hmo: mentions_only env ps (Intersection ws)).
    { change (fold_right (fun c acc => mentions_only env ps c /\ acc) True ws). unfold ws.
      apply (fold_and_map (mentions_only env ps) (fun c => with_mutability env m (without_null env c)) zs).
      intros z Hz'. exact (proj2 (proj2 (proj1 (Hw z Hz')))). }
    unfold of_components. destruct zs as [|z1 [|z2 zs']]; [simpl in Hlen; lia|simpl in Hlen; lia|]. fold m. fold ws.
    destruct (negb (forallb (is_nullable env) (z1 :: z2 :: zs'))) eqn:Enn; [split; [exact Hcws|split; [exact I|exact Hmo]]|].
    destruct (forallb is_nullable_type (z1 :: z2 :: zs')) eqn:Ewr; [split; [exact Hcws|split; [exact I|exact Hmo]]|].
    exfalso. apply negb_false_iff in Enn. rewrite forallb_forall in Enn.
    assert (Ewr': forallb is_nullable_type (z1 :: z2 :: zs') = true)
        by (apply forallb_forall; intros z Hz'; exact (Hwr z Hz' (Enn z Hz'))).
    rewrite Ewr' in Ewr. discriminate Ewr.
Qed.

(* The type arguments of supertypes, made of those of a subclass *)
Section Templates.

Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> is_type_argument y = true /\ caller_argument y.

Lemma template_instances_caller: forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> nothing_is_bottom t = true ->
        caller_type (instantiate env (bindings_of env sub ys) t))
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> nothing_is_bottom r = true ->
        caller_argument (instantiate env (bindings_of env sub ys) r)).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    set (bS := bindings_of env sub ys).
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true -> nothing_is_bottom (RootResolved m c targs) = true ->
        caller_type (instantiate env bS (RootResolved m c targs))).
    { intros m c targs Hd Ht Hn. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      destruct (nothing_is_bottom_root m c targs Hn) as [Hc Hnargs].
      assert (Hall: forall a, In a targs -> caller_argument (instantiate env bS a))
          by (intros a Ha; pose proof (argument_depth_below m c targs a Ha); exact (IHa a ltac:(lia) (Htargs a Ha) (Hnargs a Ha))).
      rewrite instantiate_class. split; [|split].
      - change (wfrag env (RootResolved m c (map (instantiate env bS) targs)) = true). cbn [wfrag].
        destruct (class_eqb c nothing) eqn:Ec.
        + specialize (Hc eq_refl). destruct m as [[]|], targs; simpl in Hc; try discriminate Hc. reflexivity.
        + apply andb_true_iff. split; [rewrite length_map, Hl; apply Nat.eqb_refl|].
          apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
          destruct (Hall a Ha) as [Hq _]. destruct (instantiate env bS a) as [| | | |v o n| |]; try contradiction Hq.
          exact (proj1 Hq).
      - exact I.
      - apply fold_and_map. intros a Ha. exact (proj2 (Hall a Ha)). }
    split.
    - intros t Hd Ht Hn. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + exact (Hroot m c targs Hd Ht Hn).
      + rewrite depth_nullable in Hd. unfold bS. rewrite instantiate_nullable_class, <- instantiate_class.
        destruct (Hroot m c targs ltac:(lia) Ht' Hn) as [Hw Hbm]. split; [|exact Hbm].
        rewrite instantiate_class in Hw |- *.
        change (true && wfrag env (RootResolved m c (map (instantiate env bS) targs)) = true). exact Hw.
    - intros r Hd Hr Hn. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        destruct (Hys y (nth_error_In _ _ Hy)) as [Hty Hqy].
        unfold bS. rewrite (selects env wf sub ys p bp i y Hi Hy Hty). exact Hqy.
      + simpl in Hd, Hn. pose proof (IHt n ltac:(lia) Hn' Hn) as Hq.
        assert (Ho': forall q, o = parameter_ownership q -> In q ps) by (intros q Eo; subst o; discriminate Ho).
        unfold bS. rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn')).
        destruct (mentions_loosely_bound _ n); [destruct v|];
            first [split; [exact Hq|split; [exact Ho'|exact (proj2 (proj2 Hq))]]
                  |split; [exact caller_bottom|split; [exact Ho'|exact I]]].
Qed.

End Templates.

Lemma caller_supertype_arguments: forall sub super xs,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids env sub) -> (forall x, In x xs -> caller_argument x) ->
    forall a, In a (parameterized_supertype_arguments env sub xs super) -> caller_argument a.
Proof.
    intros sub super xs Hne Hn Hbase Hl Hxs a Ha.
    assert (Hta: forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; destruct (Hxs x Hx) as [Hq _]; destruct x; try contradiction Hq; reflexivity).
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
    exact (proj2 (template_instances_caller sub xs Hl (fun x Hx => conj (Hta x Hx) (Hxs x Hx)) (argument_depth r)) r (le_n _)
        (Ht r Hr) (wf_supertypes_mention_nothing_as_bottom env wf sub super r Hr)).
Qed.

Section Instances.

(* Class types, without type parameters: of generic code, of no references or intersections *)
Lemma classes_caller: forall k t, depth t <= k -> in_fragment env t = true -> nothing_is_bottom t = true -> closed t = true ->
    caller_type t.
Proof.
    induction k as [|k IH].
    { intros t Hd Ht. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; simpl in Hd; lia. }
    assert (Hroot: forall m c args, depth (RootResolved m c args) <= S k -> in_fragment env (RootResolved m c args) = true ->
        nothing_is_bottom (RootResolved m c args) = true -> closed (RootResolved m c args) = true ->
        caller_type (RootResolved m c args)).
    { intros m c args Hd Ht Hn Hc. destruct (root_in_fragment env m c args Ht) as [Hl Hargs].
      destruct (nothing_is_bottom_root m c args Hn) as [Hnc Hnargs].
      assert (Hall: forall a, In a args -> exists v o n, a = TypeArgument v o n /\ is_parameter_ownership o = false
          /\ caller_type n).
      { intros a Ha. pose proof (Hargs a Ha) as Hfa. destruct a as [| | | |v o n| |]; try discriminate Hfa.
        destruct (closed_argument v o n (closed_parts m c args Hc _ Ha)) as [Ho Hcn].
        pose proof (argument_depth_below m c args _ Ha). simpl in Hnargs.
        exists v, o, n. split; [reflexivity|]. split; [exact Ho|].
        exact (IH n ltac:(simpl in *; lia) Hfa (Hnargs _ Ha) Hcn). }
      split; [|split].
      - change (wfrag env (RootResolved m c args) = true). cbn [wfrag]. destruct (class_eqb c nothing) eqn:Ec.
        + exact (Hnc eq_refl).
        + apply andb_true_iff. split; [rewrite Hl; apply Nat.eqb_refl|]. apply forallb_forall. intros a Ha.
          destruct (Hall a Ha) as [v [o [n [-> [_ [Hw _]]]]]]. exact Hw.
      - exact I.
      - apply fold_and_intro. intros a Ha. destruct (Hall a Ha) as [v [o [n [-> [Ho [_ [_ Hm]]]]]]].
        split; [intros q Eq; subst o; discriminate Ho|exact Hm]. }
    intros t Hd Ht Hn Hc. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> Ht']]]]].
    - exact (Hroot m c args Hd Ht Hn Hc).
    - rewrite depth_nullable in Hd. destruct (Hroot m c args ltac:(lia) Ht' Hn Hc) as [Hw Hbm]. split; [|exact Hbm].
      change (true && wfrag env (RootResolved m c args) = true). exact Hw.
Qed.

(* The bindings of the callee: the type arguments of the object, and the final values of inference *)
Variable b: Bindings.
Variable K: nat.
Hypothesis Hvals: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    is_exact_ownership o = true /\ caller_type x.
Hypothesis Hnulls: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> nullability_respected p x.

(* The types of the parameters, instantiated, are types of generic code *)
Lemma instances_caller: forall k,
    (forall P, vsize P <= k -> ifrag env P = true -> bound_in env b K [] (to_generic P) = true ->
        caller_type (inst env b P))
    /\ (forall a, vsize a <= k -> argument_ifrag env a = true -> bound_in env b K [] (to_generic a) = true ->
        caller_argument (instantiate env b a)).
Proof.
    induction k as [|k [IHt IHa]].
    - split.
      + intros P Hd HP HbP. destruct (ifrag_cases env wf P HP) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [-> _]]]]];
            try (simpl in Hd; lia).
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        rewrite (inst_variable env b p [] _ _ _ Ex). exact (proj2 (Hvals p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia.
    - assert (Hroot: forall m c args, ifrag env (RootResolved m c args) = true ->
          bound_in env b K [] (to_generic (RootResolved m c args)) = true -> vsize (RootResolved m c args) <= S k ->
          caller_type (inst env b (RootResolved m c args))).
      { intros m c args HP HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)).
        assert (Hargs: forall a, In a args -> caller_argument (instantiate env b a)).
        { intros a Ha. destruct (root_parts env wf b K [] m c args HP HbP a Ha) as [Hfa Hba].
          pose proof (vsize_below m c args a Ha). apply IHa; [lia|exact Hfa|exact Hba]. }
        split; [|split].
        - change (wfrag env (RootResolved m c (map (instantiate env b) args)) = true). cbn [wfrag].
          destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [Hcn [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
              try discriminate Heq.
          + injection Heq as <- <- <-. rewrite Hcn. apply andb_true_iff. split; [rewrite length_map, Hl; apply Nat.eqb_refl|].
            apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
            destruct (Hargs a Ha) as [Hq _]. destruct (instantiate env b a) as [| | | |v o n| |]; try contradiction Hq.
            exact (proj1 Hq).
          + unfold bottom_type in Heq. injection Heq as -> -> ->. reflexivity.
        - exact I.
        - apply fold_and_map. intros a Ha. exact (proj2 (Hargs a Ha)). }
      split.
      + intros P Hd HP HbP. destruct (ifrag_shapes env wf P HP) as [[m [c [args ->]]]|[[m [c [args [-> HP']]]]|[p [bnd ->]]]].
        * exact (Hroot m c args HP HbP Hd).
        * assert (Hb': bound_in env b K [] (to_generic (RootResolved m c args)) = true) by exact HbP.
          simpl in Hd. destruct (Hroot m c args HP' Hb' ltac:(simpl; lia)) as [Hw Hbm].
          rewrite (inst_root env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hw, Hbm.
          rewrite (inst_nullable env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
          split; [|exact Hbm].
          change (true && wfrag env (RootResolved m c (map (instantiate env b) args)) = true). exact Hw.
        * destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
          rewrite (inst_variable env b p bnd _ _ _ Ex). exact (proj2 (Hvals p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha HbA; simpl in Ha; try discriminate Ha. simpl in Hd. change (nfrag env n = true) in Ha.
        destruct (bound_in_argument env b K [] v o (to_generic n) HbA) as [Hob Hbn].
        rewrite (instantiate_argument env wf b K [] v o n Ha Hbn).
        assert (Hq: caller_type (inst env b n)).
        { destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [Eq _]]]]]; [exact (IHt n ltac:(lia) Ha' Hbn)|].
          (* a type variable narrowed, or made nullable: the type it is bound to, without null, or made nullable *)
          assert (Hbq: bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct Eq as [-> | ->]; exact Hbn).
          destruct (binds_ref_some env wf b K [] _ Hbq) as [o' [x [Ex _]]]. cbn [param_of] in Ex.
          destruct (inst_reference env b gm nn q [] _ _ _ Ex) as [Ei Ein]. pose proof (proj2 (Hvals q o' x Ex)) as Hx.
          destruct Eq as [-> | ->]; [rewrite Ei|rewrite Ein; apply caller_rewrap]; exact (caller_ref_apply gm nn x Hx). }
        split; [exact Hq|split; [|exact (proj2 (proj2 Hq))]].
        (* the ownership is that of the type argument bound, which is exact *)
        intros q Eq. destruct o as [| | |p']; cbn [instantiate_ownership] in Eq; try discriminate Eq.
        cbn [ownership_bound] in Hob. destruct (lookup_binding b p') as [[| | | |[] o'' x| |]|]; try discriminate Hob; try discriminate Eq.
        subst o''. discriminate Hob.
Qed.

(* The same for the type of a parameter, a type variable narrowed or made nullable among them *)
Lemma pinst_caller: forall P, pfrag env P = true -> bound_in env b K [] (pgeneric P) = true ->
    caller_type (inst env b P).
Proof.
    intros P HP Hb. destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> _]]]]|[gm [nn [p [-> _]]]]]].
    - rewrite (pgeneric_ifrag env wf P HP') in Hb. exact (proj1 (instances_caller (vsize P)) P (le_n _) HP' Hb).
    - destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj1 (inst_reference env b gm nn p [] _ _ _ Ex)). exact (caller_ref_apply gm nn x (proj2 (Hvals p o x Ex))).
    - destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj2 (inst_reference env b gm nn p [] _ _ _ Ex)). apply caller_rewrap.
      exact (caller_ref_apply gm nn x (proj2 (Hvals p o x Ex))).
Qed.

(* The same for the types of qfrag: an intersection, nullable or not, as ofComponents makes its instance *)
Lemma qinst_caller: forall P, qfrag env P = true -> bound_in env b K [] (pgeneric P) = true -> caller_type (inst env b P).
Proof.
    intros P HQ Hb. destruct (qfrag_cases env P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]]; [exact (pinst_caller P HP Hb)|].
    assert (HbI: bound_in env b K [] (Intersection (map to_generic cs)) = true) by (destruct EP as [-> | ->]; exact Hb).
    destruct (components_sfrag_facts env _ Hcs) as [Hl Hcsf].
    assert (HI: caller_type (inst_nested env b (Intersection (map to_generic cs)))).
    { change (inst_nested env b (Intersection (map to_generic cs)))
          with (of_components env (flat_map intersected_components (map (inst_component env b) (map to_generic cs)))).
      rewrite (map_ext_in (inst_component env b) (inst_nested env b) (map to_generic cs))
          by (intros c Hc; exact (inst_component_nested env b c (proj1 (Hcsf c Hc)))).
      apply caller_of_components; [rewrite length_map; exact Hl| |].
      2:{ intros y Hy Hn. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]]. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
          pose proof (bound_in_component env b K [] _ _ HbI (in_map _ _ _ HC)) as HbC.
          destruct (Hcsf _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
          apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
          destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args ->]]]|[gm [nn [q ->]]]];
              [simpl in Hn; discriminate Hn|].
          destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) HbC) as [o [x [Ex _]]]. cbn [param_of] in Ex.
          change (inst_nested env b (to_generic (TypeVariable (mkGenericRef gm nn q []))))
              with (inst env b (TypeVariable (mkGenericRef gm nn q []))) in Hn |- *.
          rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)) in Hn |- *.
          exact (ref_apply_nullable gm nn q x (proj2 (Hvals q o x Ex)) (Hnulls q o x Ex) Hsh Hn). }
      intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]]. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
      pose proof (bound_in_component env b K [] _ _ HbI (in_map _ _ _ HC)) as HbC.
      destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
      - pose proof (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)) as HCi.
        change (inst_nested env b (to_generic C)) with (inst env b C).
        apply (pinst_caller C (ifrag_pfrag env C HCi)). rewrite (pgeneric_ifrag env wf C HCi). exact HbC.
      - rewrite EC in HbC |- *. destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) HbC) as [o [x [Ex _]]].
        cbn [param_of] in Ex.
        change (inst_nested env b (to_generic (TypeVariable (mkGenericRef gm nn q []))))
            with (inst env b (TypeVariable (mkGenericRef gm nn q []))).
        rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)). exact (caller_ref_apply gm nn x (proj2 (Hvals q o x Ex))). }
    destruct EP as [-> | ->]; [exact HI|].
    change (inst env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection (map to_generic cs)))).
    exact (caller_rewrap _ HI).
Qed.

End Instances.

(* The type parameters of the caller: none of those bound in b, so neither are their ownerships *)
Lemma mentions_only_free: forall b, (forall q, In q ps -> lookup_binding b q = None) ->
    forall t, mentions_only env ps t -> owners_free env b t.
Proof.
    intros b Hb.
    (* the declared bounds of the type parameters, by their ranks *)
    assert (Hparam: forall p, param_mentions_only env ps p -> param_owners_free env b p).
    { intros p. remember (parameter_rank env p) as r eqn:Er. revert p Er. induction r as [r IH] using lt_wf_ind. intros p -> H.
      unfold param_owners_free.
      rewrite (through_param_eq env (owners_free_h b) True (wf_bounds_deep_ranked env wf) (owners_free_h_agree env b) p).
      apply (param_mentions_only_iff env wf ps) in H. pose proof (wf_bounds_deep_ranked env wf p) as Hd. revert H Hd.
      generalize (parameter_bound env p) as t.
      fix IHt 1. intros [m c args|n|g|me msg|v o n|g|cs] H Hd; simpl in H, Hd |- *; try exact I.
      - induction args as [|a args IHa]; [exact I|]. simpl in Hd. apply andb_true_iff in Hd. destruct H as [Ha Has].
        exact (conj (IHt a Ha (proj1 Hd)) (IHa Has (proj2 Hd))).
      - exact (IHt n H Hd).
      - destruct (deep_ranked_param env p _ g Hd) as [Hp|Hr]; [rewrite Hp; unfold param_eqb; rewrite Nat.eqb_refl; exact I|].
        destruct (param_eqb (param_of g) p); [exact I|]. exact (IH _ Hr _ eq_refl (proj2 (proj2 H))).
      - destruct H as [Ho Hn]. split; [destruct o as [| | |q]; try exact I; exact (Hb q (Ho q eq_refl))|exact (IHt n Hn Hd)].
      - induction cs as [|c cs IHc]; [exact I|]. simpl in Hd. apply andb_true_iff in Hd. destruct H as [Hc Hcs].
        exact (conj (IHt c Hc (proj1 Hd)) (IHc Hcs (proj2 Hd))). }
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try exact I.
    - induction args as [|a args IHa]; [exact I|]. destruct H as [Ha Has]. exact (conj (IH a Ha) (IHa Has)).
    - exact (IH n H).
    - exact (Hparam _ (proj2 (proj2 H))).
    - destruct H as [Ho Hn]. split; [destruct o as [| | |q]; try exact I; exact (Hb q (Ho q eq_refl))|exact (IH n Hn)].
    - induction cs as [|c cs IHc]; [exact I|]. destruct H as [Hc Hcs]. exact (conj (IH c Hc) (IHc Hcs)).
Qed.

(* A type of the parameters without ownerships of type parameters, its type variables bound to types of
   generic code: a type of generic code *)
(* A type of generic code is no type argument *)
Lemma caller_not_nested: forall t, caller_type t -> nests_argument t = false.
Proof. intros [| [| | | | | |] | | | | |] [Hw _]; try reflexivity; simpl in Hw; discriminate Hw. Qed.

Lemma free_caller: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> caller_type x) ->
    forall P, ifrag env P = true -> plain_owners P = true -> vars_in (bound_b b) P = true ->
        caller_type (instantiate_free env b P).
Proof.
    intros b Hpb Hvals.
    (* a reference to a class: its type arguments, of generic code *)
    assert (Hroot: forall m c args, ifrag env (RootResolved m c args) = true ->
        (forall a, In a args -> caller_argument (instantiate_free env b a)) ->
        caller_type (instantiate_free env b (RootResolved m c args))).
    { intros m c args HP Hargs. cbn [instantiate_free]. split; [|split].
      - change (wfrag env (RootResolved m c (map (instantiate_free env b) args)) = true). cbn [wfrag].
        destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [Hcn [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
            try discriminate Heq.
        + injection Heq as <- <- <-. rewrite Hcn. apply andb_true_iff. split; [rewrite length_map, Hl; apply Nat.eqb_refl|].
          apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
          destruct (Hargs a Ha) as [Hq _]. destruct (instantiate_free env b a) as [| | | |v o n| |]; try contradiction Hq.
          exact (proj1 Hq).
        + unfold bottom_type in Heq. injection Heq as -> -> ->. reflexivity.
      - exact I.
      - apply fold_and_map. intros a Ha. exact (proj2 (Hargs a Ha)). }
    fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn q vs]|cs] HP Ho Hv; try discriminate HP.
    - apply (Hroot m c args HP). pose proof (root_args_ifrag env wf m c args HP) as Hargs. cbn [plain_owners] in Ho.
      cbn [vars_in] in Hv. clear HP.
      induction args as [|a args IHa]; [intros a Ha; destruct Ha|].
      cbn [forallb] in Ho, Hv. apply andb_true_iff in Ho. destruct Ho as [Hoa Hoas]. apply andb_true_iff in Hv. destruct Hv as [Hva Hvas].
      intros a' [<-|Ha'].
      + pose proof (Hargs a (or_introl eq_refl)) as Ha. destruct a as [| | | |v o n| |]; try discriminate Ha.
        cbn [argument_ifrag] in Ha. cbn [plain_owners] in Hoa. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon].
        apply negb_true_iff in Hop. cbn [vars_in] in Hva.
        assert (Hc: caller_type (instantiate_free env b n)).
        { destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [Eq _]]]]]; [exact (IH n Ha' Hon Hva)|].
          (* a type variable narrowed, or made nullable: the type it is bound to, without null, or made nullable *)
          assert (Hq: bound_b b q = true) by (destruct Eq as [-> | ->]; cbn [vars_in] in Hva; rewrite andb_true_r in Hva; exact Hva).
          unfold bound_b in Hq. destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate Hq].
          destruct (Hpb q a Ea) as [Hl [o' [x [-> Hy]]]]. pose proof (Hvals q o' x Ea) as Hx.
          destruct Eq as [-> | ->]; cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; cbn [orb];
              [|apply caller_rewrap]; exact (caller_ref_apply gm nn x Hx). }
        rewrite (free_argument env b v o n Hpb (caller_not_nested _ Hc)), (free_plain_ownership b o Hop).
        split; [exact Hc|].
        split; [intros q Eq; subst o; discriminate Hop|exact (proj2 (proj2 Hc))].
      + exact (IHa Hoas Hvas (fun a'' Ha'' => Hargs a'' (or_intror Ha'')) a' Ha').
    - (* nullable: of a class type *)
      assert (Hn: ifrag env n = true /\ exists m c args, n = RootResolved m c args).
      { destruct (ifrag_cases env wf _ HP) as [[? [? [? [Heq _]]]]|[Heq|[[m [c [args [Heq H']]]]|[? [Heq _]]]]];
            try discriminate Heq.
        injection Heq as ->. split; [exact H'|eauto]. }
      destruct Hn as [Hn Hroot']. cbn [plain_owners] in Ho. cbn [vars_in] in Hv. pose proof (IH n Hn Ho Hv) as Hc.
      destruct Hroot' as [m [c [args ->]]]. destruct Hc as [Hw [_ Hm]].
      cbn [instantiate_free] in Hw, Hm |- *. cbn [rewrap_nullable]. split; [|split; [exact I|exact Hm]].
      change (true && wfrag env (RootResolved m c (map (instantiate_free env b) args)) = true). exact Hw.
    - unfold ifrag in HP. cbn [no_generics] in HP. rewrite andb_false_r in HP. discriminate HP.
    - destruct gm, nn; try (unfold ifrag in HP; apply andb_true_iff in HP; destruct HP as [_ HP]; discriminate HP).
      cbn [vars_in] in Hv. apply andb_true_iff in Hv. destruct Hv as [Hq _]. unfold bound_b in Hq.
      cbn [instantiate_free]. destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate Hq].
      destruct (Hpb q a Ea) as [Hl [o [y [-> Hy]]]]. unfold final_argument. rewrite Hl, Hy. exact (Hvals q o y Ea).
Qed.

(* The same for the type of a parameter, a type variable narrowed or made nullable among them *)
Lemma pfree_caller: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> caller_type x) ->
    forall P, pfrag env P = true -> plain_owners P = true -> vars_in (bound_b b) P = true ->
        caller_type (instantiate_free env b P).
Proof.
    intros b Hpb Hvals P HP Ho Hv. destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> _]]]]|[gm [nn [p [-> _]]]]]].
    { exact (free_caller b Hpb Hvals P HP' Ho Hv). }
    all: cbn [vars_in] in Hv; rewrite andb_true_r in Hv; unfold bound_b in Hv.
    all: destruct (lookup_binding b p) as [a|] eqn:Ea; [|discriminate Hv].
    all: destruct (Hpb p a Ea) as [Hl [o [x [-> Hy]]]].
    all: assert (Ei: forall nn', instantiate_free env b (TypeVariable (mkGenericRef gm nn' p [])) = ref_apply env gm nn' x)
        by (intros nn'; cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
    all: assert (Ein: forall nn', instantiate_free env b (Nullable (TypeVariable (mkGenericRef gm nn' p [])))
        = rewrap_nullable (ref_apply env gm nn' x))
        by (intros nn'; cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
    all: pose proof (Hvals p o x Ea) as Hx.
    all: first [rewrite Ein|rewrite Ei].
    2: apply caller_rewrap.
    all: exact (caller_ref_apply gm nn x Hx).
Qed.

(* The same for the types of qfrag: an intersection, nullable or not, as ofComponents makes its instance,
   or as it is where it mentions nothing bound *)
Lemma qfree_caller: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> caller_type x) ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> nullability_respected q x) ->
    forall P, qfrag env P = true -> (forall C, In C (intersected_components P) -> plain_owners C = true) ->
        vars_in (bound_b b) P = true -> caller_type (instantiate_free env b P).
Proof.
    intros b Hpb Hvals Hnulls P HQ Ho Hv. destruct (qfrag_cases env P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]].
    { apply (pfree_caller b Hpb Hvals P HP); [|exact Hv].
      apply Ho. rewrite (intersected_none P (pfrag_not_inter env P HP)). left. reflexivity. }
    assert (Ho': forall C, In C cs -> plain_owners C = true)
        by (intros C HC; destruct EP as [-> | ->]; [exact (Ho C HC)|exact (Ho (Nullable C) (in_map Nullable _ _ HC))]).
    assert (Hv': forall C, In C cs -> vars_in (bound_b b) C = true)
        by (intros C HC; destruct EP as [-> | ->]; cbn [vars_in] in Hv; rewrite forallb_forall in Hv; exact (Hv C HC)).
    destruct (components_sfrag_facts env _ Hcs) as [Hl Hcsf]. rewrite length_map in Hl.
    assert (HI: caller_type (instantiate_free env b (Intersection cs))).
    { cbn [instantiate_free]. destruct (existsb (mentions_bound b) cs) eqn:Em.
      - apply caller_of_components; [rewrite length_map; exact Hl| |].
        2:{ intros y Hy Hn. apply in_map_iff in Hy. destruct Hy as [C [<- HC]].
            destruct (Hcsf _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
            apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
            destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args ->]]]|[gm [nn [q ->]]]];
                [simpl in Hn; discriminate Hn|].
            pose proof (Hv' _ HC) as HvT. cbn [vars_in] in HvT. rewrite andb_true_r in HvT.
            unfold bound_b in HvT. destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate HvT].
            destruct (Hpb q a Ea) as [Hla [o [x [-> Hy]]]].
            assert (Ei: instantiate_free env b (TypeVariable (mkGenericRef gm nn q [])) = ref_apply env gm nn x)
                by (cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hla, Hy; reflexivity).
            rewrite Ei in Hn |- *. exact (ref_apply_nullable gm nn q x (Hvals q o x Ea) (Hnulls q o x Ea) Hsh Hn). }
        intros y Hy. apply in_map_iff in Hy. destruct Hy as [C [<- HC]].
        destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
        + exact (free_caller b Hpb Hvals C (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)) (Ho' C HC) (Hv' C HC)).
        + pose proof (Hv' C HC) as HvT. rewrite EC in HvT |- *. cbn [vars_in] in HvT. rewrite andb_true_r in HvT.
          unfold bound_b in HvT. destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate HvT].
          destruct (Hpb q a Ea) as [Hla [o [x [-> Hy]]]].
          cbn [instantiate_free]. rewrite Ea. unfold final_argument. rewrite Hla, Hy. exact (caller_ref_apply gm nn x (Hvals q o x Ea)).
      - (* it mentions nothing bound: of closed class types *)
        assert (HC: forall C, In C cs -> caller_type C /\ is_component_shape env C = true /\ wfrag env C = true).
        { intros C HC. destruct (Hcsf (to_generic C) (in_map _ _ _ HC)) as [Hsh Hsf].
          assert (Hnv: no_vars C = true).
          { apply (bound_unmentioned_closed b C (Hv' C HC)).
            destruct (mentions_bound b C) eqn:EmC; [|reflexivity].
            rewrite (proj2 (existsb_exists _ _) (ex_intro _ C (conj HC EmC))) in Em. discriminate Em. }
          destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]];
              [|rewrite EC in Hnv; discriminate Hnv].
          pose proof (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)) as HCi.
          pose proof (closed_of_ifrag env wf C HCi Hnv (Ho' C HC)) as Hcl.
          rewrite (to_generic_closed C Hcl) in Hsh, Hsf.
          destruct (proj1 (closed_facts env wf [] 0 [] _) C (le_n _) Hsf Hcl) as [Hfr _].
          pose proof (classes_caller (depth C) C (le_n _) Hfr (ifrag_nib env wf C HCi) Hcl) as Hcc.
          split; [exact Hcc|]. split; [exact Hsh|]. rewrite EC in Hcc |- *. exact (proj1 Hcc). }
        split; [|split; [exact I|]].
        + change (wcomponents env cs = true). unfold wcomponents. apply andb_true_iff. split; [apply Nat.leb_le; exact Hl|].
          apply forallb_forall. intros C HC'. destruct (HC C HC') as [_ [Hs Hf]]. rewrite Hs, Hf. reflexivity.
        + change (fold_right (fun c acc => mentions_only env ps c /\ acc) True cs).
          clear -HC. induction cs as [|C cs IH]; [exact I|].
          split; [exact (proj2 (proj2 (proj1 (HC C (or_introl eq_refl)))))|exact (IH (fun C' HC' => HC C' (or_intror HC')))]. }
    destruct EP as [-> | ->]; [exact HI|].
    change (instantiate_free env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate_free env b (Intersection cs))).
    exact (caller_rewrap _ HI).
Qed.

Lemma values_respected: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x) ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> exists S, to_generic S = parameter_bound env q
        /\ ((gfrag env S = true /\ below env x S)
            \/ (forall C, In C (bound_components S) -> gfrag env C = true /\ below env x C)
            \/ (forall C, In C (bound_components S) -> pfrag env C = true /\ vars_in (bound_b b) C = true
                /\ below env x (instantiate_free env b C)))) ->
    forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> nullability_respected q x.
Proof.
    intros b Hpb Hbf Hform q o x Eq Hn. destruct (is_nullable env (Generic (mkGenericRef None false q []))) eqn:E; [right; reflexivity|].
    rewrite (values_not_nullable env wf declared declared_wf b Hpb Hbf Hform q o x Eq E) in Hn. discriminate Hn.
Qed.

End CallerTypes.

(* ---------------------------------------------------------------------------------------------- *)
(* Conjectures                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

(* intersect builds types of generic code from types of it: of the wide fragment, the references as
   GenericTypeReference makes them, to the type parameters of its operands *)
Definition intersect_stays_in_generic_code (env: Environment) (declared: TypeParameterId -> EType): Prop :=
    forall ps a c, of_fragment env declared a -> of_fragment env declared c ->
        caller_type env declared ps a -> caller_type env declared ps c -> caller_type env declared ps (intersect env a c).

(* closestCommonSupertypeWith, likewise *)
Definition closest_common_supertype_stays_in_generic_code (env: Environment) (declared: TypeParameterId -> EType): Prop :=
    forall ps a c, of_fragment env declared a -> of_fragment env declared c ->
        caller_type env declared ps a -> caller_type env declared ps c ->
        caller_type env declared ps (closest_common_supertype_with env a c).

(* ---------------------------------------------------------------------------------------------- *)
(* Calls in generic code, instantiated                                                             *)
(* ---------------------------------------------------------------------------------------------- *)

Section Instantiated.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Hypothesis intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true.
Hypothesis supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
    no_vars (closest_common_supertype_with env a b) = true.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.

(* The conjectures of Conjectures.v, and those above *)
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis tame: tame_inheritance env.
Hypothesis intersect_in_fragment: intersect_always_stays_in_fragment env declared.
Hypothesis supertype_in_fragment: closest_common_supertype_stays_in_fragment env declared.
Hypothesis intersect_below: intersect_is_below_both env declared.
Hypothesis supertype_above: closest_common_supertype_is_above_both env declared.
Hypothesis intersect_generic: intersect_stays_in_generic_code env declared.
Hypothesis supertype_generic: closest_common_supertype_stays_in_generic_code env declared.

Theorem member_call_in_generic_code_instantiated: forall ps sigma n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    (* the type parameters of the caller, bound to types within their declared bounds, instantiated *)
    bindings_in_fragment env sigma ->
    (forall p, In p ps -> exists o x, lookup_binding sigma p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true
        /\ exists f, unify env f (inst_nested env sigma (declared p)) x (Ongoing []) = Some (Ongoing [])) ->
    (forall p, In p ps -> tfrag env (declared p) = true /\ built env declared (declared p)
        /\ mentions_only env ps (declared p)) ->
    (* the call, as in member_call_in_generic_code_sound; the object of a type without type parameters *)
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    in_fragment env (RootResolved mo e xs) = true -> nothing_is_bottom (RootResolved mo e xs) = true ->
    closed (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (forall P, In P Ps -> qfrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    (* the arguments: types of generic code *)
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ owners_outside env (map fst (cvars ++ ovars)) A
        /\ caller_type env declared ps A) ->
    (forall p bound, In (p, bound) ovars -> caller_type env declared ps bound) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of env U (fst v)))) ovars ->
    (* the bounds: the declared ones *)
    (forall p bound, In (p, bound) (cvars ++ ovars) -> to_generic bound = parameter_bound env p) ->
    forall P A, In (P, A) (combine Ps As) ->
        exists f, is_assignable_to env f (instantiate env sigma A) (instantiate env sigma (inst env b P)) = Some true.
Proof.
    intros ps sigma n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hsf Hwithin Hdeclared Hc Hca He Hids Hnd Hbounds Hfy Hrec
        Hfo Hno Hcl Hobj Hzs Hxx Hzb HPs HPn HAs HQbounds Hfold b Hbdef Hdb P A HPA.
    destruct (member_call_in_generic_code_sound env wf intersect_no_vars supertype_no_vars declared declared_wf terminates finite
        tame intersect_in_fragment supertype_in_fragment intersect_below supertype_above
        (caller_type env declared ps) (caller_argument env declared ps) (caller_argument_nested env declared ps)
        (intersect_generic ps) (supertype_generic ps) (caller_top env wf declared ps) (caller_bottom env declared ps)
        (caller_any env wf declared ps) (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
        (caller_narrowed env wf declared ps) (caller_component env declared ps)
        (caller_supertype_arguments env wf declared ps)
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hdb Hfy Hrec Hfo Hobj Hzs Hxx Hzb HPs
        HPn HAs
        HQbounds Hfold) as [HQfin Hmain].
    destruct (Hmain b Hbdef) as [[K0 HK0] [Hlook [Hpbv [Hwb Hsound]]]].
    (* the values, within their bounds, respect their nullability *)
    assert (Hnr: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> nullability_respected env p x).
    { apply (values_respected env wf declared declared_wf b Hpbv).
      - intros q o x Eq. destruct (Hwb q o x Eq) as [_ [_ [Hfx _]]]. exact Hfx.
      - intros q o x Eq. destruct (Hwb q o x Eq) as [bound [Hin [_ Hbx]]]. exists bound. split; [exact (Hdb q bound Hin)|].
        left. split; [exact (in_fragment_is_gfrag env _ (Hbounds q bound Hin))|exact Hbx]. }
    destruct (Hsound P A HPA) as [f0 Hf0].
    apply in_combine_l in HPA as HP. apply in_combine_r in HPA as HA.
    (* the type arguments of the object, as those of c *)
    assert (Hzs': forall z, In z zs -> argument_in_fragment env z = true /\ nothing_is_bottom z = true /\ closed z = true).
    { pose proof (object_below env wf n mr c _ ma ca ys _ u mo e xs n0 Hrec Hobj) as Hbe.
      destruct (root_in_fragment env mo e xs Hfo) as [Hlx Hxs].
      assert (Hxs': forall x, In x xs -> argument_in_fragment env x = true /\ nothing_is_bottom x = true /\ closed x = true).
      { intros x Hx. split; [exact (Hxs x Hx)|].
        split; [exact (proj2 (nothing_is_bottom_root mo e xs Hno) x Hx)|exact (closed_parts mo e xs Hcl x Hx)]. }
      subst zs. destruct (Class_eq_dec e c) as [<-|Hne]; [rewrite class_eqb_refl; exact Hxs'|]. rewrite (class_eqb_false _ _ Hne).
      assert (Hta: forall y, In y xs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Hxs, Hy).
      destruct (supertype_arguments_to_generic env wf e c xs Hne He Hbe Hlx Hta) as [_ [_ [Hnb Hcb]]].
      destruct (supertype_arguments_in_fragment env wf e c xs Hne He Hbe Hlx Hxs) as [_ Hf].
      intros z Hz. split; [exact (Hf z Hz)|].
      split; [exact (Hnb (fun y Hy => proj1 (proj2 (Hxs' y Hy))) z Hz)|exact (Hcb (fun y Hy => proj2 (proj2 (Hxs' y Hy))) z Hz)]. }
    (* what b binds to: types of generic code *)
    assert (Hvals: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        is_exact_ownership o = true /\ caller_type env declared ps x).
    { intros p o x Hpb. destruct (Hlook p o x Hpb) as [Ho [Hz|[bound [Hin ->]]]]; split; try exact Ho.
      - destruct (Hzs' _ Hz) as [Hfz [Hnz Hcz]]. cbn [argument_in_fragment] in Hfz. cbn [nothing_is_bottom] in Hnz.
        destruct (closed_argument _ _ _ Hcz) as [_ Hcx].
        exact (classes_caller env declared ps (depth x) x (le_n _) Hfz Hnz Hcx).
      - exact (HQfin p bound Hin). }
    destruct (qinst_caller env wf declared declared_wf ps b K0 Hvals Hnr P (proj1 (HPs P HP)) (HK0 P HP)) as [HwP [HbP HmP]].
    destruct (HAs A HA) as [_ [_ [_ [HwA [HbA HmA]]]]].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ HbP HmP) as [K1 HK1].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ HbA HmA) as [K2 HK2].
    exact (substitution_wide env declared sigma (max K1 K2) f0 (inst env b P) A wf declared_wf terminates finite tame Hsf
        HwP HwA (bound_in_mono env wf sigma K1 (max K1 K2) _ (Nat.le_max_l K1 K2) HK1) (bound_in_mono env wf sigma K2 (max K1 K2) _ (Nat.le_max_r K1 K2) HK2) Hf0).
Qed.

(* closestCommonSupertypeWith keeps Nothing only as `exclusive Nothing` (GenericArguments.v) *)
Hypothesis supertype_bottom_only: closest_common_supertype_keeps_bottom_only env declared.

(*
 * A call in generic code of a member function whose type parameters are bounded by types mentioning
 * them, instantiated: as member_call_in_generic_code_instantiated, from
 * generic_member_call_with_bounded_variables_sound. The final values of the type parameters of the
 * function, instantiated, are within their static upper bounds with the type variables replaced and
 * instantiated, and each argument, instantiated, fits its parameter so replaced and instantiated. The
 * type parameters of the caller are none of those of the callee.
 *)
Theorem generic_member_call_with_bounded_variables_instantiated: forall ps sigma n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    (* the type parameters of the caller, bound to types within their declared bounds, instantiated *)
    bindings_in_fragment env sigma ->
    (forall p, In p ps -> exists o x, lookup_binding sigma p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true
        /\ exists f, unify env f (inst_nested env sigma (declared p)) x (Ongoing []) = Some (Ongoing [])) ->
    (forall p, In p ps -> tfrag env (declared p) = true /\ built env declared (declared p)
        /\ mentions_only env ps (declared p)) ->
    (forall q, In q ps -> ~ In q (map fst (cvars ++ ovars))) ->
    (* the call, as in generic_member_call_with_bounded_variables_sound; the object of a type without type parameters *)
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p S, In (p, S) cvars -> in_fragment env S = true) ->
    (forall p S, In (p, S) ovars -> gstatic_bound env declared (caller_type env declared ps) (cvars ++ ovars) p S) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    in_fragment env (RootResolved mo e xs) = true -> nothing_is_bottom (RootResolved mo e xs) = true ->
    closed (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (forall P, In P Ps -> qfrag env P = true /\ (forall C, In C (intersected_components P) -> plain_owners C = true)
        /\ vars_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) P = true) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    (* the arguments: types of generic code *)
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ caller_type env declared ps A) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (forall p S st, In (p, S) ovars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (gfinal_of env U (fst v)))) ovars ->
    (* the bounds of the type parameters of c: the declared ones, and the type arguments of the object within them *)
    (forall p S, In (p, S) cvars -> to_generic S = parameter_bound env p) ->
    (forall i p S z, nth_error cvars i = Some (p, S) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f S x (Ongoing []) = Some (Ongoing [])) ->
    (forall p S, In (p, S) ovars -> forall C, In C (bound_components S) ->
        exists f, is_assignable_to env f (instantiate env sigma (gfinal_of env U p))
            (instantiate env sigma (instantiate_free env b C)) = Some true)
    /\ forall P A, In (P, A) (combine Ps As) ->
        exists f, is_assignable_to env f (instantiate env sigma A) (instantiate env sigma (instantiate_free env b P)) = Some true.
Proof.
    intros ps sigma n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hsf Hwithin Hdeclared Hdis Hc Hca He Hids Hnd Hcb Hst
        Hfy Hrec Hfo Hno Hcl Hobj Hzs Hxx HPs HPn HAs Hfold Hlow b Hbdef Hcdecl Hzb.
    (* none of the type parameters of the caller is bound in b, nor so their ownerships *)
    assert (Hnone: forall q, In q ps -> lookup_binding b q = None).
    { intros q Hq. pose proof (Hdis q Hq) as Hn. rewrite map_app in Hn. rewrite Hbdef, lookup_app.
      assert (Hnc: ~ In q (parameter_ids env c)) by (rewrite <- Hids; intros H; apply Hn; apply in_or_app; left; exact H).
      rewrite (lookup_combine_none _ zs q Hnc: lookup_binding (bindings_of env c zs) q = None).
      apply lookup_map_none. intros H. apply Hn. apply in_or_app. right. exact H. }
    assert (Hown: forall t, caller_type env declared ps t -> owners_free env b t)
        by (intros t Ht; exact (mentions_only_free env wf ps b Hnone t (proj2 (proj2 Ht)))).
    assert (HAs': forall A, In A As -> yfrag env declared (caller_type env declared ps) b A).
    { intros A HA. destruct (HAs A HA) as [Hf [Hbo Hq]]. split; [exact Hf|]. split; [exact Hbo|]. split; [exact (Hown A Hq)|exact Hq]. }
    destruct (generic_member_call_with_bounded_variables_sound env wf intersect_no_vars supertype_no_vars declared declared_wf terminates
        finite tame intersect_in_fragment supertype_in_fragment intersect_below supertype_above
        (caller_type env declared ps) (caller_argument env declared ps) (caller_argument_nested env declared ps)
        (intersect_generic ps) (supertype_generic ps) (caller_top env wf declared ps) (caller_bottom env declared ps)
        (caller_any env wf declared ps) (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
        (caller_narrowed env wf declared ps) (caller_component env declared ps) (caller_nullable_component env declared ps)
        (caller_supertype_arguments env wf declared ps) supertype_bottom_only
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hcb Hcdecl Hst Hfy Hrec Hfo Hobj Hzs Hxx Hzb HPs HPn Hfold Hlow
        b Hbdef HAs' Hown) as [Hpb [Hdomb [Hvals0 [Hvx [Hfinal Hargs]]]]].
    (* the type arguments of the object, as those of c *)
    assert (Hzs': forall z, In z zs -> argument_in_fragment env z = true /\ nothing_is_bottom z = true /\ closed z = true).
    { pose proof (object_below env wf n mr c _ ma ca ys _ u mo e xs n0 Hrec Hobj) as Hbe.
      destruct (root_in_fragment env mo e xs Hfo) as [Hlx Hxs].
      assert (Hxs': forall x, In x xs -> argument_in_fragment env x = true /\ nothing_is_bottom x = true /\ closed x = true).
      { intros x Hx. split; [exact (Hxs x Hx)|].
        split; [exact (proj2 (nothing_is_bottom_root mo e xs Hno) x Hx)|exact (closed_parts mo e xs Hcl x Hx)]. }
      subst zs. destruct (Class_eq_dec e c) as [<-|Hne]; [rewrite class_eqb_refl; exact Hxs'|]. rewrite (class_eqb_false _ _ Hne).
      assert (Hta: forall y, In y xs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Hxs, Hy).
      destruct (supertype_arguments_to_generic env wf e c xs Hne He Hbe Hlx Hta) as [_ [_ [Hnb Hcb']]].
      destruct (supertype_arguments_in_fragment env wf e c xs Hne He Hbe Hlx Hxs) as [_ Hf].
      intros z Hz. split; [exact (Hf z Hz)|].
      split; [exact (Hnb (fun y Hy => proj1 (proj2 (Hxs' y Hy))) z Hz)|exact (Hcb' (fun y Hy => proj2 (proj2 (Hxs' y Hy))) z Hz)]. }
    (* what b binds to: types of generic code *)
    assert (Hvals: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> caller_type env declared ps x).
    { intros q o x Eq. destruct (Hvals0 q o x Eq) as [Hz|Hq]; [|exact Hq].
      destruct (Hzs' _ Hz) as [Hfz [Hnz Hcz]]. cbn [argument_in_fragment] in Hfz. cbn [nothing_is_bottom] in Hnz.
      destruct (closed_argument _ _ _ Hcz) as [_ Hcx].
      exact (classes_caller env declared ps (depth x) x (le_n _) Hfz Hnz Hcx). }
    assert (Hdomb': forall q, existsb (param_eqb q) (map fst (cvars ++ ovars)) = true -> bound_b b q = true).
    { intros q E. apply existsb_exists in E. destruct E as [q' [Hq' Eq]]. apply param_eqb_eq in Eq. subst q'. exact (Hdomb q Hq'). }
    (* the values, within their bounds, respect their nullability *)
    assert (Hnr: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> nullability_respected env p x).
    { apply (values_respected env wf declared declared_wf b Hpb).
      - intros q o x Eq. exact (proj1 (Hvx q o x Eq)).
      - intros q o x Eq. destruct (Hvx q o x Eq) as [_ [[i [S [Hi Hz]]]|[S [Hin ->]]]].
        + exists S. split; [exact (Hcdecl q S (nth_error_In _ _ Hi))|]. left.
          destruct (Hzb i q S _ Hi Hz) as [o' [x' [f [Ez Ef]]]]. injection Ez as <- <-.
          split; [exact (in_fragment_is_gfrag env _ (Hcb q S (nth_error_In _ _ Hi)))|exists f; exact Ef].
        + destruct (Hst q S Hin) as [ES [Hsv [Hcl' Hvar]]]. exists S. split; [exact ES|]. right.
          destruct (Hfinal q S Hin) as [_ HbF]. destruct (no_vars S) eqn:Ens.
          * left. intros C HC. destruct (Hcl' eq_refl) as [HfS HqS].
            destruct (bound_component_of env wf declared declared_wf terminates finite tame (caller_type env declared ps)
                (caller_component env declared ps) (caller_nullable_component env declared ps) S C HfS HqS HC) as [HfC [HqC _]].
            split; [exact (proj1 HfC)|]. pose proof (HbF C HC) as HbC.
            rewrite (free_unmentioned env b Hpb C (proj1 HfC) (unmentioned env b C (proj1 HfC) (Hown C HqC))) in HbC. exact HbC.
          * right. intros C HC. destruct (Hvar eq_refl) as [Hcomp _]. destruct (Hcomp C HC) as [HCp _].
            split; [exact HCp|]. split; [|exact (HbF C HC)].
            apply (vars_in_mono _ _ Hdomb').
            apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ (vars_in_bound_component _ S C Hsv HC)). }
    (* what unify accepts in generic code, instantiated *)
    assert (Hinst: forall x y, caller_type env declared ps x -> caller_type env declared ps y -> below env x y ->
        exists f, is_assignable_to env f (instantiate env sigma x) (instantiate env sigma y) = Some true).
    { intros x y [Hwx [Hbx Hmx]] [Hwy [Hby Hmy]] [f0 Ef0].
      destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ Hbx Hmx) as [K1 HK1].
      destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ Hby Hmy) as [K2 HK2].
      apply (substitution_wide env declared sigma (max K1 K2) f0 y x wf declared_wf terminates finite tame Hsf Hwy Hwx
          (bound_in_mono env wf sigma K2 (max K1 K2) _ (Nat.le_max_r K1 K2) HK2)
          (bound_in_mono env wf sigma K1 (max K1 K2) _ (Nat.le_max_l K1 K2) HK1)).
      unfold is_assignable_to, empty_unification. rewrite Ef0. reflexivity. }
    split.
    - (* the final values *)
      intros p S Hin C HC. destruct (Hfinal p S Hin) as [Hq Hbelow]. apply (Hinst _ _ Hq); [|exact (Hbelow C HC)].
      destruct (Hst p S Hin) as [_ [Hsv [Hcl' Hvar]]]. destruct (no_vars S) eqn:Ens.
      + destruct (Hcl' eq_refl) as [HfS HqS].
        assert (HC': caller_type env declared ps C /\ gfrag env C = true).
        { destruct S as [m c' args|[m'' c'' a''|n''|g''|me' msg'|v' o' x'|g''|cs']|g|me msg|v o x|g|cs]; cbn [bound_components] in HC;
              try (destruct HC as [<-|[]]; exact (conj HqS (proj1 HfS))).
          - apply in_map_iff in HC. destruct HC as [c0 [<- Hc0]].
            pose proof (proj1 HfS) as HgS. cbn [gfrag] in HgS. apply andb_true_iff in HgS. destruct HgS as [_ HgI].
            destruct (proj2 (intersection_gfrag env cs' HgI) c0 Hc0) as [Hcc Hgc].
            split; [exact (caller_nullable_component env declared ps cs' c0 HqS Hc0)|].
            cbn [gfrag]. rewrite Hgc, andb_true_r. destruct c0; first [exact Hcc|discriminate Hcc].
          - split; [exact (caller_component env declared ps cs C HqS HC)|exact (proj2 (proj2 (intersection_gfrag env cs (proj1 HfS)) C HC))]. }
        rewrite (free_unmentioned env b Hpb C (proj2 HC') (unmentioned env b C (proj2 HC') (Hown C (proj1 HC')))). exact (proj1 HC').
      + destruct (Hvar eq_refl) as [Hcomp _]. destruct (Hcomp C HC) as [HCi HCo].
        apply (pfree_caller env wf declared ps b Hpb Hvals C HCi (proj1 (bplain_parts env p C HCo))).
        apply (vars_in_mono _ _ Hdomb').
        apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ (vars_in_bound_component _ S C Hsv HC)).
    - (* the arguments *)
      intros P A HPA. apply in_combine_l in HPA as HP. apply in_combine_r in HPA as HA.
      destruct (HPs P HP) as [HfP [HoP HvP]]. destruct (HAs A HA) as [_ [_ HqA]].
      apply (Hinst _ _ HqA); [|exact (Hargs P A HPA)].
      exact (qfree_caller env wf declared declared_wf ps b Hpb Hvals Hnr P HfP HoP (vars_in_mono _ _ Hdomb' P HvP)).
Qed.

End Instantiated.
