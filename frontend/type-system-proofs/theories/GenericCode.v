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
          try exact (caller_narrowed g Hc); destruct Hc as [Hw _]; discriminate Hw. }
    intros [m c args|n|g|me msg|v o n|g|cs] Hc; try (apply Hshape; [exact Hc|exact I]).
    change (caller_type (without_null env n)). apply Hshape; [exact (caller_nullable n Hc)|].
    destruct Hc as [Hw _]. destruct n; try exact I. discriminate Hw.
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

(* The types of the parameters, instantiated, are types of generic code *)
Lemma instances_caller: forall k,
    (forall P, vsize P <= k -> ifrag env P = true -> no_given P = true -> bound_in env b K [] (to_generic P) = true ->
        caller_type (inst env b P))
    /\ (forall a, vsize a <= k -> argument_ifrag env a = true -> no_given a = true -> bound_in env b K [] (to_generic a) = true ->
        caller_argument (instantiate env b a)).
Proof.
    induction k as [|k [IHt IHa]].
    - split.
      + intros P Hd HP _ HbP. destruct (ifrag_cases env wf P HP) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [-> _]]]]];
            try (simpl in Hd; lia).
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        rewrite (inst_variable env b p [] _ _ _ Ex). exact (proj2 (Hvals p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia.
    - assert (Hroot: forall m c args, ifrag env (RootResolved m c args) = true -> no_given (RootResolved m c args) = true ->
          bound_in env b K [] (to_generic (RootResolved m c args)) = true -> vsize (RootResolved m c args) <= S k ->
          caller_type (inst env b (RootResolved m c args))).
      { intros m c args HP Hg HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)).
        assert (Hargs: forall a, In a args -> caller_argument (instantiate env b a)).
        { intros a Ha. destruct (root_parts env wf b K [] m c args HP HbP a Ha) as [Hfa Hba].
          pose proof (vsize_below m c args a Ha). apply IHa; [lia|exact Hfa|exact (no_given_root m c args Hg a Ha)|exact Hba]. }
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
      + intros P Hd HP Hg HbP. destruct (ifrag_shapes env wf P HP) as [[m [c [args ->]]]|[[m [c [args [-> HP']]]]|[p [bnd ->]]]].
        * exact (Hroot m c args HP Hg HbP Hd).
        * assert (Hb': bound_in env b K [] (to_generic (RootResolved m c args)) = true) by exact HbP.
          simpl in Hd. destruct (Hroot m c args HP' Hg Hb' ltac:(simpl; lia)) as [Hw Hbm].
          rewrite (inst_root env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hw, Hbm.
          rewrite (inst_nullable env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
          split; [|exact Hbm].
          change (true && wfrag env (RootResolved m c (map (instantiate env b) args)) = true). exact Hw.
        * destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
          rewrite (inst_variable env b p bnd _ _ _ Ex). exact (proj2 (Hvals p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha Hg HbA; simpl in Ha; try discriminate Ha. simpl in Hd. change (nfrag env n = true) in Ha.
        destruct (bound_in_argument env b K [] v o (to_generic n) HbA) as [Hob Hbn].
        rewrite (instantiate_argument env wf b K [] v o n Ha Hbn).
        assert (Hq: caller_type (inst env b n)).
        { destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [Eq _]]]]]; [exact (IHt n ltac:(lia) Ha' Hg Hbn)|].
          (* a type variable narrowed, or made nullable: the type it is bound to, without null, or made nullable *)
          assert (Hbq: bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct Eq as [-> | ->]; exact Hbn).
          destruct (binds_ref_some env wf b K [] _ Hbq) as [o' [x [Ex _]]]. cbn [param_of] in Ex.
          destruct (inst_reference env b gm nn q [] _ _ _ Ex) as [Ei Ein]. pose proof (proj2 (Hvals q o' x Ex)) as Hx.
          destruct Eq as [-> | ->]; cbn [no_given] in Hg; destruct gm; try discriminate Hg; [rewrite Ei|rewrite Ein; apply caller_rewrap];
              unfold ref_apply; cbn zeta; destruct nn; first [exact (caller_without_null x Hx)|exact Hx]. }
        split; [exact Hq|split; [|exact (proj2 (proj2 Hq))]].
        (* the ownership is that of the type argument bound, which is exact *)
        intros q Eq. destruct o as [| | |p']; cbn [instantiate_ownership] in Eq; try discriminate Eq.
        cbn [ownership_bound] in Hob. destruct (lookup_binding b p') as [[| | | |[] o'' x| |]|]; try discriminate Hob; try discriminate Eq.
        subst o''. discriminate Hob.
Qed.

(* The same for the type of a parameter, a type variable narrowed or made nullable among them *)
Lemma pinst_caller: forall P, pfrag env P = true -> no_given P = true -> bound_in env b K [] (pgeneric P) = true ->
    caller_type (inst env b P).
Proof.
    intros P HP Hg Hb. destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> _]]]]|[gm [nn [p [-> _]]]]]].
    - rewrite (pgeneric_ifrag env wf P HP') in Hb. exact (proj1 (instances_caller (vsize P)) P (le_n _) HP' Hg Hb).
    - destruct gm; [discriminate Hg|].
      destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj1 (inst_reference env b None nn p [] _ _ _ Ex)). unfold ref_apply. cbn zeta.
      pose proof (proj2 (Hvals p o x Ex)) as Hx. destruct nn; [exact (caller_without_null x Hx)|exact Hx].
    - destruct gm; [discriminate Hg|].
      destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
      rewrite (proj2 (inst_reference env b None nn p [] _ _ _ Ex)). apply caller_rewrap. unfold ref_apply. cbn zeta.
      pose proof (proj2 (Hvals p o x Ex)) as Hx. destruct nn; [exact (caller_without_null x Hx)|exact Hx].
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
    forall P, ifrag env P = true -> plain_owners P = true -> vars_in (bound_b b) P = true -> no_given P = true ->
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
    fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn q vs]|cs] HP Ho Hv Hg; try discriminate HP.
    - apply (Hroot m c args HP). pose proof (root_args_ifrag env wf m c args HP) as Hargs. cbn [plain_owners] in Ho.
      cbn [vars_in] in Hv. cbn [no_given] in Hg. clear HP.
      induction args as [|a args IHa]; [intros a Ha; destruct Ha|].
      cbn [forallb] in Ho, Hv, Hg. apply andb_true_iff in Ho. destruct Ho as [Hoa Hoas]. apply andb_true_iff in Hv. destruct Hv as [Hva Hvas].
      apply andb_true_iff in Hg. destruct Hg as [Hga Hgas].
      intros a' [<-|Ha'].
      + pose proof (Hargs a (or_introl eq_refl)) as Ha. destruct a as [| | | |v o n| |]; try discriminate Ha.
        cbn [argument_ifrag] in Ha. cbn [plain_owners] in Hoa. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon].
        apply negb_true_iff in Hop. cbn [vars_in] in Hva. cbn [no_given] in Hga.
        assert (Hc: caller_type (instantiate_free env b n)).
        { destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [Eq _]]]]]; [exact (IH n Ha' Hon Hva Hga)|].
          (* a type variable narrowed, or made nullable: the type it is bound to, without null, or made nullable *)
          assert (Hq: bound_b b q = true) by (destruct Eq as [-> | ->]; cbn [vars_in] in Hva; rewrite andb_true_r in Hva; exact Hva).
          unfold bound_b in Hq. destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate Hq].
          destruct (Hpb q a Ea) as [Hl [o' [x [-> Hy]]]]. pose proof (Hvals q o' x Ea) as Hx.
          destruct Eq as [-> | ->]; cbn [no_given] in Hga; destruct gm; try discriminate Hga;
              cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; cbn [orb];
              [|apply caller_rewrap]; destruct nn; first [exact (caller_without_null x Hx)|exact Hx]. }
        rewrite (free_argument env b v o n Hpb (caller_not_nested _ Hc)), (free_plain_ownership b o Hop).
        split; [exact Hc|].
        split; [intros q Eq; subst o; discriminate Hop|exact (proj2 (proj2 Hc))].
      + exact (IHa Hoas Hvas Hgas (fun a'' Ha'' => Hargs a'' (or_intror Ha'')) a' Ha').
    - (* nullable: of a class type *)
      assert (Hn: ifrag env n = true /\ exists m c args, n = RootResolved m c args).
      { destruct (ifrag_cases env wf _ HP) as [[? [? [? [Heq _]]]]|[Heq|[[m [c [args [Heq H']]]]|[? [Heq _]]]]];
            try discriminate Heq.
        injection Heq as ->. split; [exact H'|eauto]. }
      destruct Hn as [Hn Hroot']. cbn [plain_owners] in Ho. cbn [vars_in] in Hv. pose proof (IH n Hn Ho Hv Hg) as Hc.
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
    forall P, pfrag env P = true -> no_given P = true -> plain_owners P = true -> vars_in (bound_b b) P = true ->
        caller_type (instantiate_free env b P).
Proof.
    intros b Hpb Hvals P HP Hg Ho Hv. destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> _]]]]|[gm [nn [p [-> _]]]]]].
    { exact (free_caller b Hpb Hvals P HP' Ho Hv Hg). }
    all: destruct gm; [discriminate Hg|].
    all: cbn [vars_in] in Hv; rewrite andb_true_r in Hv; unfold bound_b in Hv.
    all: destruct (lookup_binding b p) as [a|] eqn:Ea; [|discriminate Hv].
    all: destruct (Hpb p a Ea) as [Hl [o [x [-> Hy]]]].
    all: assert (Ei: forall nn', instantiate_free env b (TypeVariable (mkGenericRef None nn' p [])) = ref_apply env None nn' x)
        by (intros nn'; cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
    all: assert (Ein: forall nn', instantiate_free env b (Nullable (TypeVariable (mkGenericRef None nn' p [])))
        = rewrap_nullable (ref_apply env None nn' x))
        by (intros nn'; cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
    all: pose proof (Hvals p o x Ea) as Hx.
    all: first [rewrite Ein|rewrite Ei].
    2: apply caller_rewrap.
    all: unfold ref_apply; cbn zeta; destruct nn; [exact (caller_without_null x Hx)|exact Hx].
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
Hypothesis not_expansive: non_expansive env.
Hypothesis intersect_in_fragment: intersect_stays_in_fragment env declared.
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
    (forall P, In P Ps -> pfrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (forall P, In P Ps -> no_given P = true) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed *)
    (forall P, In P Ps -> args_narrowed P = true) ->
    (* the arguments: types of generic code *)
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ owners_outside env (map fst (cvars ++ ovars)) A
        /\ caller_type env declared ps A) ->
    (forall p bound, In (p, bound) ovars -> caller_type env declared ps bound) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of env U (fst v)))) ovars ->
    forall P A, In (P, A) (combine Ps As) ->
        exists f, is_assignable_to env f (instantiate env sigma A) (instantiate env sigma (inst env b P)) = Some true.
Proof.
    intros ps sigma n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hsf Hwithin Hdeclared Hc Hca He Hids Hnd Hbounds Hfy Hrec
        Hfo Hno Hcl Hobj Hzs Hxx Hzb HPs HPg HPn HAs HQbounds Hfold b Hbdef P A HPA.
    destruct (member_call_in_generic_code_sound env wf intersect_no_vars supertype_no_vars declared declared_wf terminates finite
        not_expansive intersect_in_fragment supertype_in_fragment intersect_below supertype_above
        (caller_type env declared ps) (caller_argument env declared ps) (caller_argument_nested env declared ps)
        (intersect_generic ps) (supertype_generic ps) (caller_top env wf declared ps) (caller_bottom env declared ps)
        (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
        (caller_narrowed env wf declared ps) (caller_component env declared ps)
        (caller_supertype_arguments env wf declared ps)
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hxx Hzb HPs
        HPn HAs
        HQbounds Hfold) as [HQfin Hmain].
    destruct (Hmain b Hbdef) as [[K0 HK0] [Hlook Hsound]].
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
    destruct (pinst_caller env wf declared ps b K0 Hvals P (proj1 (HPs P HP)) (HPg P HP) (HK0 P HP)) as [HwP [HbP HmP]].
    destruct (HAs A HA) as [_ [_ [_ [HwA [HbA HmA]]]]].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ HbP HmP) as [K1 HK1].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ HbA HmA) as [K2 HK2].
    exact (substitution_wide env declared sigma (max K1 K2) f0 (inst env b P) A wf declared_wf terminates finite not_expansive Hsf
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
 * type parameters of the caller are none of those of the callee. No type of a parameter, nor bound, is
 * a type variable of a mutability given to it (no_given).
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
    (forall P, In P Ps -> pfrag env P = true /\ plain_owners P = true
        /\ vars_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) P = true) ->
    (forall P, In P Ps -> no_given P = true) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed *)
    (forall P, In P Ps -> args_narrowed P = true) ->
    (forall p S, In (p, S) ovars -> forall C, In C (bound_components S) -> no_given C = true) ->
    (* the arguments: types of generic code *)
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ caller_type env declared ps A) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (forall p S st, In (p, S) ovars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (gfinal_of env U (fst v)))) ovars ->
    (forall p S, In (p, S) ovars -> forall C, In C (bound_components S) ->
        exists f, is_assignable_to env f (instantiate env sigma (gfinal_of env U p))
            (instantiate env sigma (instantiate_free env b C)) = Some true)
    /\ forall P A, In (P, A) (combine Ps As) ->
        exists f, is_assignable_to env f (instantiate env sigma A) (instantiate env sigma (instantiate_free env b P)) = Some true.
Proof.
    intros ps sigma n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hsf Hwithin Hdeclared Hdis Hc Hca He Hids Hnd Hcb Hst
        Hfy Hrec Hfo Hno Hcl Hobj Hzs Hxx HPs HPg HPn HSg HAs Hfold Hlow b Hbdef.
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
        finite not_expansive intersect_in_fragment supertype_in_fragment intersect_below supertype_above
        (caller_type env declared ps) (caller_argument env declared ps) (caller_argument_nested env declared ps)
        (intersect_generic ps) (supertype_generic ps) (caller_top env wf declared ps) (caller_bottom env declared ps)
        (caller_any env wf declared ps) (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
        (caller_narrowed env wf declared ps) (caller_component env declared ps) (caller_nullable_component env declared ps)
        (caller_supertype_arguments env wf declared ps) supertype_bottom_only
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hcb Hst Hfy Hrec Hfo Hobj Hzs Hxx HPs HPn Hfold Hlow
        b Hbdef HAs' Hown) as [Hpb [Hdomb [Hvals0 [Hfinal Hargs]]]].
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
    (* what unify accepts in generic code, instantiated *)
    assert (Hinst: forall x y, caller_type env declared ps x -> caller_type env declared ps y -> below env x y ->
        exists f, is_assignable_to env f (instantiate env sigma x) (instantiate env sigma y) = Some true).
    { intros x y [Hwx [Hbx Hmx]] [Hwy [Hby Hmy]] [f0 Ef0].
      destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ Hbx Hmx) as [K1 HK1].
      destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ Hby Hmy) as [K2 HK2].
      apply (substitution_wide env declared sigma (max K1 K2) f0 y x wf declared_wf terminates finite not_expansive Hsf Hwy Hwx
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
        apply (pfree_caller env wf declared ps b Hpb Hvals C HCi (HSg p S Hin C HC) (proj1 (andb_prop _ _ HCo))).
        apply (vars_in_mono _ _ Hdomb').
        apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ (vars_in_bound_component _ S C Hsv HC)).
    - (* the arguments *)
      intros P A HPA. apply in_combine_l in HPA as HP. apply in_combine_r in HPA as HA.
      destruct (HPs P HP) as [HfP [HoP HvP]]. destruct (HAs A HA) as [_ [_ HqA]].
      apply (Hinst _ _ HqA); [|exact (Hargs P A HPA)].
      exact (pfree_caller env wf declared ps b Hpb Hvals P HfP (HPg P HP) HoP (vars_in_mono _ _ Hdomb' P HvP)).
Qed.

End Instantiated.
