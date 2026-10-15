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
    rewrite (mentions_only_generic env wf) in Hm.
    split; [exact (tfrag_wtfrag env wf _ Ht)|]. split; [exact I|exact (proj2 (proj2 Hm))].
Qed.

Lemma caller_component: forall cs c, caller_type (Intersection cs) -> In c cs -> caller_type c.
Proof.
    intros cs c [Hw [Hb Hm]] Hc. destruct (wcomponents_facts env cs Hw) as [_ Hcs].
    split; [exact (wfrag_wtfrag env c (proj2 (Hcs c Hc)))|]. split; [exact I|exact (fold_and_in _ cs Hm c Hc)].
Qed.

Lemma built_without_null: forall t, built env declared t -> built env declared (without_null env t).
Proof. intros. exact I. Qed.

Lemma mentions_without_null: forall t, mentions_only env ps t -> mentions_only env ps (without_null env t).
Proof. exact (mentions_only_without_null env wf ps). Qed.

Lemma caller_narrowed: forall g, caller_type (Generic g) -> caller_type (without_null env (Generic g)).
Proof.
    intros g [Hw [Hb Hm]]. split; [|split; [exact (built_without_null _ Hb)|exact (mentions_without_null _ Hm)]].
    pose proof (generic_of_wtfrag env wf g Hw) as Hg. pose proof (generic_sfrag_sfrag env wf g Hg) as Hs.
    destruct (tfrag_without_null env wf (sdepth env (Generic g)) (Generic g) (le_n _) (sfrag_tfrag env _ Hs)) as [Ht' _].
    exact (tfrag_wtfrag env wf _ Ht').
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
      { intros m c args HP HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP)).
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
          rewrite (inst_root env b m c args (ifrag_no_generics env _ HP')) in Hw, Hbm.
          rewrite (inst_nullable env b m c args (ifrag_no_generics env _ HP')).
          split; [|exact Hbm].
          change (true && wfrag env (RootResolved m c (map (instantiate env b) args)) = true). exact Hw.
        * destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
          rewrite (inst_variable env b p bnd _ _ _ Ex). exact (proj2 (Hvals p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha HbA; simpl in Ha; try discriminate Ha. simpl in Hd.
        destruct (bound_in_argument env b K [] v o (to_generic n) HbA) as [Hob Hbn].
        rewrite (instantiate_argument env wf b K [] v o n Ha Hbn).
        pose proof (IHt n ltac:(lia) Ha Hbn) as Hq.
        split; [exact Hq|split; [|exact (proj2 (proj2 Hq))]].
        (* the ownership is that of the type argument bound, which is exact *)
        intros q Eq. destruct o as [| | |p']; cbn [instantiate_ownership] in Eq; try discriminate Eq.
        cbn [ownership_bound] in Hob. destruct (lookup_binding b p') as [[| | | |[] o'' x| |]|]; try discriminate Hob; try discriminate Eq.
        subst o''. discriminate Hob.
Qed.

End Instances.

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
    (forall P, In P Ps -> ifrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
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
        Hfo Hno Hcl Hobj Hzs Hxx Hzb HPs HAs HQbounds Hfold b Hbdef P A HPA.
    destruct (member_call_in_generic_code_sound env wf intersect_no_vars supertype_no_vars declared declared_wf terminates finite
        not_expansive intersect_in_fragment supertype_in_fragment intersect_below supertype_above
        (caller_type env declared ps) (caller_argument env declared ps) (caller_argument_nested env declared ps)
        (intersect_generic ps) (supertype_generic ps) (caller_top env wf declared ps) (caller_bottom env declared ps)
        (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
        (caller_narrowed env wf declared ps) (caller_component env declared ps)
        (caller_supertype_arguments env wf declared ps)
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hxx Hzb HPs
        HAs
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
    destruct (proj1 (instances_caller env wf declared ps b K0 Hvals (vsize P)) P (le_n _) (proj1 (HPs P HP)) (HK0 P HP))
        as [HwP [HbP HmP]].
    destruct (HAs A HA) as [_ [_ [_ [HwA [HbA HmA]]]]].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ HbP HmP) as [K1 HK1].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) _ HbA HmA) as [K2 HK2].
    exact (substitution_wide env declared sigma (max K1 K2) f0 (inst env b P) A wf declared_wf terminates finite not_expansive Hsf
        HwP HwA (bound_in_mono env wf sigma K1 (max K1 K2) _ (Nat.le_max_l K1 K2) HK1) (bound_in_mono env wf sigma K2 (max K1 K2) _ (Nat.le_max_r K1 K2) HK2) Hf0).
Qed.

End Instantiated.
