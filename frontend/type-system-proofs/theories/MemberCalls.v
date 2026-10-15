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
(* Member calls, with type parameters of the function                                              *)
(*                                                                                                *)
(* Calling a member function is sound: the receiver captures the type arguments of the class       *)
(* (Inference.v), the arguments put constraints on the type parameters of the function             *)
(* (Constraints.v), and every argument accepted fits its parameter with the type parameters        *)
(* replaced by the type arguments of the object called on and by the final values of inference.   *)
(* ---------------------------------------------------------------------------------------------- *)

Section MemberCalls.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Let supertypes_mention_nothing_as_bottom := wf_supertypes_mention_nothing_as_bottom env wf.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

Variables xfrag bfrag: EType -> Prop.
Hypothesis types: inference_types env xfrag bfrag.
Let xfrag_gfrag := it_xfrag_gfrag env xfrag bfrag types.
Let in_fragment_xfrag := it_in_fragment_xfrag env xfrag bfrag types.
Let in_fragment_bfrag := it_in_fragment_bfrag env xfrag bfrag types.

Let in_fragment_no_vars := Constraints.in_fragment_no_vars env.
Let argument_in_fragment_no_vars := Constraints.argument_in_fragment_no_vars env.
Let fits := Constraints.fits env.
Let final_value := Constraints.final_value env.
Let wf_states := Constraints.wf_states env xfrag bfrag.
Let invocation_sound := Constraints.invocation_sound env wf xfrag bfrag types.
Let final_value_fits := Constraints.final_value_fits env xfrag bfrag types.

Definition final_value_of (u: VariableStates) (p: TypeParameterId): EType :=
    match lookup_state u p with Some st => final_value st | None => bottom_type end.

Lemma lookup_for_inference: forall (vars: list (TypeParameterId * EType)) caps p bound, NoDup (map fst vars) -> In (p, bound) vars ->
    lookup_state (map (fun '(q, bnd) => (q, mkVariableState bnd bnd bottom_type false (existsb (param_eqb q) caps))) vars) p
    = Some (mkVariableState bound bound bottom_type false (existsb (param_eqb p) caps)).
Proof.
    intros vars caps. induction vars as [|[q bq] rest IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_for_inference_in: forall (vars: list (TypeParameterId * EType)) caps p st,
    lookup_state (map (fun '(q, bnd) => (q, mkVariableState bnd bnd bottom_type false (existsb (param_eqb q) caps))) vars) p = Some st ->
    exists bound, In (p, bound) vars.
Proof.
    intros vars caps. induction vars as [|[q bq] rest IH]; intros p st H; simpl in H; [discriminate H|].
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. exists bq. left. reflexivity.
    - destruct (IH p st H) as [bound Hin]. exists bound. right. exact Hin.
Qed.

Lemma nodup_app_l: forall (l1 l2: list TypeParameterId), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
    intros l1 l2. induction l1 as [|x l1 IH]; intros H; [constructor|]. inversion H as [|? ? Hnotin H2]. subst.
    constructor; [intros Hx; apply Hnotin, in_or_app; left; exact Hx|exact (IH H2)].
Qed.

Lemma nodup_app_disjoint: forall (l1 l2: list TypeParameterId) a, NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
    intros l1 l2 a. induction l1 as [|x l1 IH]; intros Hnd H1 H2; [destruct H1|]. inversion Hnd as [|? ? Hnotin Hnd2]. subst.
    destruct H1 as [->|H1]; [apply Hnotin, in_or_app; right; exact H2|exact (IH Hnd2 H1 H2)].
Qed.

Lemma lookup_app: forall (l1 l2: Bindings) p,
    lookup_binding (l1 ++ l2) p = match lookup_binding l1 p with Some a => Some a | None => lookup_binding l2 p end.
Proof.
    intros l1 l2 p. induction l1 as [|[q a] l1 IH]; [reflexivity|]. simpl. destruct (param_eqb p q); [reflexivity|exact IH].
Qed.

Lemma lookup_own: forall (l: list (TypeParameterId * EType)) (g: TypeParameterId -> EType) p a,
    lookup_binding (map (fun v => (fst v, g (fst v))) l) p = Some a -> a = g p /\ In p (map fst l).
Proof.
    intros l g p a. induction l as [|[q bq] l IH]; intros H; simpl in H; [discriminate H|].
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. injection H as <-. split; [reflexivity|left; reflexivity].
    - destruct (IH H) as [-> Hin]. split; [reflexivity|right; exact Hin].
Qed.

Lemma fold_keeps_exact_unify: forall nf (l: list (EType * EType)) s s',
    fold_unify (fun inner '(P, A) => unify env nf P A inner) l (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros nf l s s' H. apply (fold_keeps_exact (fun inner '(P, A) => unify env nf P A inner) l s s'); [| |exact H].
    - intros [P A] s0 s0' _ E. exact (unify_keeps_exact env nf P A s0 s0' E).
    - intros [P A] _. apply unify_keeps_failure.
Qed.

Lemma template_not_loose: forall sub ys, length ys = length (parameter_ids env sub) ->
    (forall y, In y ys -> is_loose y = false) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> mentions_loosely_bound (bindings_of env sub ys) t = false)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> mentions_loosely_bound (bindings_of env sub ys) r = false).
Proof.
    intros sub ys Hl Hys k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k -> template_type env sub (RootResolved m c targs) = true ->
        existsb (mentions_loosely_bound (bindings_of env sub ys)) targs = false).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs].
      apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [a [Ha E]].
      pose proof (argument_depth_below m c targs a Ha). rewrite (IHa a ltac:(lia) (Htargs a Ha)) in E. discriminate E. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite mentions_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite mentions_nullable, mentions_class. exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hl) Hi) as [y Hy].
        rewrite (mentions_parameter_template _ p bp y (lookup_parameter env wf sub ys i p y Hi Hy)).
        apply Hys. eapply nth_error_In. exact Hy.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn].
Qed.

(* The type arguments of a supertype, for exact type arguments of the subclass, are exact where the
   supertype is declared with exact ones *)
Lemma supertype_arguments_exact: forall e c xs, e <> c -> e <> nothing -> base_type_is_subtype_of env e c = true ->
    length xs = length (parameter_ids env e) -> (forall x, In x xs -> exact_argument env x = true) ->
    (forall r, In r (supertype_arguments env e c) -> exact_template_argument r = true) ->
    forall z, In z (parameterized_supertype_arguments env e xs c) -> exact_argument env z = true.
Proof.
    intros e c xs Hne Hn Hb Hl Hxs Hex z Hz.
    destruct (wf_supertypes_are_templates env wf e c Hne Hn Hb) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Hz. apply in_map_iff in Hz. destruct Hz as [r [<- Hr]].
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true).
    { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o nx| |]; try discriminate E.
      simpl in E |- *. apply andb_true_iff in E. apply E. }
    assert (Hta: forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; apply (argument_in_fragment_is_type_argument env), Hfxs, Hx).
    destruct (template_kind env e r (Ht r Hr)) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
    - destruct (nth_error_same_length _ xs i p (eq_sym Hl) Hi) as [x Hx].
      rewrite (selects env wf e xs p bp i x Hi Hx (Hta x (nth_error_In _ _ Hx))). apply Hxs. eapply nth_error_In. exact Hx.
    - pose proof (Hex _ Hr) as Hexr. simpl in Hexr. destruct v; try discriminate Hexr.
      rewrite (instantiate_template_argument env _ Model.invariant o n Ho (template_shape env e n Hn')).
      assert (Hnl: forall x, In x xs -> is_loose x = false).
      { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o' nx| |]; try discriminate E.
        destruct o'; try discriminate E; reflexivity. }
      rewrite (proj1 (template_not_loose e xs Hl Hnl (depth n)) n (le_n _) Hn').
      simpl. destruct o; try discriminate Ho; try discriminate Hexr;
          rewrite (template_type_instance_in_fragment env wf e xs n Hl Hfxs Hn'); reflexivity.
Qed.

(* The object is of a class below the one the function is declared in *)
Lemma object_below: forall n mr c targs ma ca ys st u mo e xs n0,
    unify env n (RootResolved mr c targs) (RootResolved ma ca ys) (Ongoing st) = Some (Ongoing u) ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    base_type_is_subtype_of env e c = true.
Proof.
    intros n mr c targs ma ca ys st u mo e xs n0 Hrec Hobj.
    destruct n as [|n]; [discriminate Hrec|]. rewrite unify_classes in Hrec.
    destruct (base_type_is_subtype_of env ca c) eqn:Hbca; [|discriminate Hrec].
    unfold is_assignable_to, empty_unification in Hobj.
    destruct n0 as [|n0]; [discriminate Hobj|]. rewrite unify_classes in Hobj.
    destruct (base_type_is_subtype_of env e ca) eqn:Hbe; [|discriminate Hobj].
    exact (base_type_is_subtype_of_trans env wf e ca c Hbe Hbca).
Qed.

(* The type arguments of the object, as those of a class it is below, are exact *)
Lemma object_arguments_exact: forall c mo e xs zs, e <> nothing -> base_type_is_subtype_of env e c = true ->
    in_fragment env (RootResolved mo e xs) = true -> (forall x, In x xs -> exact_argument env x = true) ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    forall z, In z zs -> exact_argument env z = true.
Proof.
    intros c mo e xs zs He Hbe Hfo Hxs ->. destruct (Class_eq_dec e c) as [<-|Hne]; [rewrite class_eqb_refl; exact Hxs|].
    rewrite (class_eqb_false _ _ Hne).
    apply (supertype_arguments_exact e c xs Hne He Hbe (proj1 (root_in_fragment env mo e xs Hfo)) Hxs).
    intros r Hr. exact (wf_supertypes_are_exact env wf e c r Hr).
Qed.

Lemma forall2_diag: forall {A: Type} (R: A -> A -> Prop) (l: list A), (forall x, In x l -> R x x) -> Forall2 R l l.
Proof.
    intros A R l H. induction l as [|x l IH]; constructor; [apply H; left; reflexivity|].
    apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma uniform_fuel_list: forall {A: Type} (l: list A) (Q: nat -> A -> Prop),
    (forall f f' x, f <= f' -> Q f x -> Q f' x) -> (forall x, In x l -> exists f, Q f x) ->
    exists f, forall x, In x l -> Q f x.
Proof.
    intros A l Q Hm. induction l as [|x l IH]; intros H; [exists 0; intros _ []|].
    destruct (H x (or_introl eq_refl)) as [f1 H1]. destruct (IH (fun y Hy => H y (or_intror Hy))) as [f2 H2].
    exists (max f1 f2). intros y [<-|Hy]; [apply (Hm f1); [lia|exact H1]|apply (Hm f2); [lia|exact (H2 y Hy)]].
Qed.

(* The type parameters a type mentions, in references to them and as ownership, are among vars, with
   the bounds vars have for them *)
Fixpoint refs_within (vars: list (TypeParameterId * EType)) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => refs_within vars a /\ acc) True arguments
    | Nullable n => refs_within vars n
    | Generic (mkGenericRef None false p []) | TypeVariable (mkGenericRef None false p []) => In (p, parameter_bound env p) vars
    | Generic _ | TypeVariable _ => False
    | TypeArgument _ o n => (forall q, o = parameter_ownership q -> In q (map fst vars)) /\ refs_within vars n
    | _ => True
    end.

Lemma bound_in_from_refs: forall vars b K t, (ifrag env t = true \/ argument_ifrag env t = true) -> refs_within vars t ->
    (forall p bound, In (p, bound) vars -> binds_exactly env b K [] p bound = true) ->
    (forall q, In q (map fst vars) -> ownership_bound b (parameter_ownership q) = true) ->
    bound_in env b K [] (to_generic t) = true.
Proof.
    intros vars b K t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Hf H Hp Ho.
    destruct Hf as [Hf|Hf].
    - destruct (ifrag_cases env wf t Hf) as [[m [c [args [-> [_ [_ Hargs]]]]]]|[->|[[m [c [args [-> Ht']]]]|[p [-> [Hfb Hcb]]]]]].
      + change (forallb (bound_in env b K []) (map to_generic args) = true). apply forallb_forall. intros a' Ha'.
        apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        apply (IH (esize a)); [pose proof (esize_in args a Ha); simpl; lia|reflexivity|right; exact (Hargs a Ha)| |exact Hp|exact Ho].
        exact (fold_and_in _ args H a Ha).
      + reflexivity.
      + change (bound_in env b K [] (to_generic (RootResolved m c args)) = true).
        apply (IH (esize (RootResolved m c args))); [simpl; lia|reflexivity|left; exact Ht'|exact H|exact Hp|exact Ho].
      + simpl in H. change (bound_in env b K [] (Generic (mkGenericRef None false p [])) = true).
        rewrite (binds_ref_closed env wf b K [] p Hfb Hcb). exact (Hp p _ H).
    - destruct t as [| | | |v o n| |]; try discriminate Hf. simpl in Hf, H |- *. destruct H as [Hq Hn]. apply andb_true_iff. split.
      + destruct o as [| | |q]; try reflexivity. exact (Ho q (Hq q eq_refl)).
      + apply (IH (esize n)); [simpl; lia|reflexivity|left; exact Hf|exact Hn|exact Hp|exact Ho].
Qed.

Lemma lookup_map_vars: forall (l: list (TypeParameterId * EType)) (g: TypeParameterId * EType -> EType) p bound,
    NoDup (map fst l) -> In (p, bound) l -> lookup_binding (map (fun v => (fst v, g v)) l) p = Some (g (p, bound)).
Proof.
    intros l g. induction l as [|[q bq] l IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_combine_none: forall (ids: list TypeParameterId) (xs: list EType) p, ~ In p ids -> lookup_binding (combine ids xs) p = None.
Proof.
    intros ids. induction ids as [|q ids IH]; intros [|x xs] p H; try reflexivity. simpl.
    destruct (param_eqb p q) eqn:E; [apply param_eqb_eq in E; subst q; exfalso; apply H; left; reflexivity|].
    apply IH. intros Hin. apply H. right. exact Hin.
Qed.

(* What unifying the receiver leaves, and how the object relates to the receiver, as references to
   the class the function is declared in *)
Lemma receiver_and_object: forall n mr c cvars ovars ma ca ys u mo e xs zs n0,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    in_fragment env (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    exists ys' n1,
        length ys' = length cvars /\ length zs = length cvars
        /\ (forall y, In y ys' -> argument_in_fragment env y = true)
        /\ (forall i p bound y, nth_error cvars i = Some (p, bound) -> nth_error ys' i = Some y ->
            lookup_state u p = Some (mkVariableState bound y y true true))
        /\ (forall p bound, In (p, bound) ovars -> lookup_state u p = Some (mkVariableState bound bound bottom_type false false))
        /\ wf_states u
        /\ Forall2 (fun z y => unify env n1 y z (Ongoing []) = Some (Ongoing [])) zs ys'
        /\ (forall p st, lookup_state u p = Some st -> is_exact st = false ->
            exists bound, In (p, bound) ovars /\ st = mkVariableState bound bound bottom_type false false).
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd bnd bottom_type false (existsb (param_eqb q) (map fst cvars))))
        (cvars ++ ovars)).
    assert (Hs0: for_inference_of (cvars ++ ovars) (map fst cvars) = Ongoing s0) by reflexivity.
    rewrite Hs0 in Hrec.
    rewrite map_app in Hnd.
    assert (Hndc: NoDup (map fst cvars)) by exact (nodup_app_l _ _ Hnd).
    assert (Hcls: forall p bound, In (p, bound) cvars -> existsb (param_eqb p) (map fst cvars) = true).
    { intros p bound Hin. apply existsb_exists. exists p. split; [exact (in_map fst _ _ Hin)|apply param_eqb_refl]. }
    assert (Hown: forall p bound, In (p, bound) ovars -> existsb (param_eqb p) (map fst cvars) = false).
    { intros p bound Hin. apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [q [Hq Hpq]].
      apply param_eqb_eq in Hpq. subst q. exact (nodup_app_disjoint _ _ p Hnd Hq (in_map fst _ _ Hin)). }
    assert (Hnd': NoDup (map fst (cvars ++ ovars))) by (rewrite map_app; exact Hnd).
    (* the receiver, as a reference to c, binds the type parameters of c exactly *)
    destruct n as [|n]; [discriminate Hrec|].
    rewrite unify_classes in Hrec.
    destruct (base_type_is_subtype_of env ca c) eqn:Hbca; [|discriminate Hrec].
    destruct (Model.is_subtype_of _ _) eqn:Hmr; [|discriminate Hrec].
    rewrite (class_eqb_false ca nothing Hca) in Hrec. unfold unify_arguments in Hrec.
    set (ys' := if class_eqb ca c then ys else parameterized_supertype_arguments env ca ys c) in Hrec.
    assert (Hys': length ys' = length (parameter_ids env c) /\ forall y, In y ys' -> argument_in_fragment env y = true).
    { unfold ys'. destruct (Class_eq_dec ca c) as [<-|Hne]; [rewrite class_eqb_refl; exact (root_in_fragment env ma ca ys Hfy)|].
      rewrite (class_eqb_false _ _ Hne). destruct (root_in_fragment env ma ca ys Hfy) as [Hly0 Hys0].
      exact (supertype_arguments_in_fragment env wf ca c ys Hne Hca Hbca Hly0 Hys0). }
    destruct Hys' as [Hly Hys].
    assert (Hl: length ys' = length cvars) by (rewrite Hly, <- Hids, length_map; reflexivity).
    assert (Hfresh: forall p bound, In (p, bound) cvars ->
        lookup_state s0 p = Some (mkVariableState bound bound bottom_type false true) /\ in_fragment env bound = true).
    { intros p bound Hin. split; [|exact (Hbounds p bound (in_or_app _ _ _ (or_introl Hin)))].
      unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_introl Hin))), (Hcls p bound Hin). reflexivity. }
    destruct (capture_arguments env wf n cvars ys' s0 u Hndc Hl Hys Hfresh Hrec) as [Hcap Hoth].
    assert (Hownu: forall p bound, In (p, bound) ovars -> lookup_state u p = Some (mkVariableState bound bound bottom_type false false)).
    { intros p bound Hin.
      assert (Hnin: ~ In p (map fst cvars)) by (intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite (Hoth p Hnin). unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_intror Hin))).
      rewrite (Hown p bound Hin). reflexivity. }
    (* the variable states are those unify works with *)
    assert (Hwfu: wf_states u).
    { intros p st Hp. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin].
      - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        rewrite (Hcap i p bound y Hi Hy) in Hp. injection Hp as <-. cbn [upper_bound lower_bound is_exact].
        pose proof (argument_in_fragment_no_vars y (Hys y (nth_error_In _ _ Hy))) as Hny.
        split; [exact Hny|]. split; [exact Hny|]. intros E; discriminate E.
      - rewrite (Hoth p Hnin) in Hp. unfold s0 in Hp. destruct (lookup_for_inference_in _ _ p st Hp) as [bound Hin].
        rewrite (lookup_for_inference _ _ p bound Hnd' Hin) in Hp. injection Hp as <-.
        apply in_app_or in Hin as Hin2. destruct Hin2 as [Hin2|Hin2]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin2)|].
        rewrite (Hown p bound Hin2). cbn [upper_bound lower_bound is_exact is_capturable].
        pose proof (Hbounds p bound Hin) as Hfb.
        split; [exact (in_fragment_no_vars bound Hfb)|]. split; [reflexivity|]. intros _. split; [reflexivity|].
        split; [exists 2; apply (below_all env wf [] bound 2 Hfb); lia|]. split; [intros x f _ Ex; exists f; exact Ex|].
        split; [exact (in_fragment_bfrag _ Hfb)|exact (in_fragment_bfrag _ (bottom_in_fragment env wf))]. }
    (* the type arguments of the object as c, assignable to those of the receiver as c *)
    assert (Hfzs: forall z, In z zs -> argument_in_fragment env z = true).
    { intros z Hz. pose proof (Hzx z Hz) as E. destruct z as [| | | |[] o nz| |]; try discriminate E.
      simpl in E |- *. apply andb_true_iff in E. apply E. }
    assert (HfD: in_fragment env (RootResolved mr c ys') = true).
    { change (Nat.eqb (length ys') (length (parameter_ids env c)) && forallb (argument_in_fragment env) ys' = true).
      rewrite Hly, Nat.eqb_refl. apply forallb_forall, Hys. }
    set (k := depth (RootResolved mr c ys')).
    assert (HD: unify env (S k) (RootResolved mr c ys') (RootResolved ma ca ys) (Ongoing []) = Some (Ongoing [])).
    { rewrite unify_classes, Hbca, (assignment_mutability_of_class env mr c ys' (map receiver_leaf cvars)), Hmr, (class_eqb_false ca nothing Hca).
      fold ys'. unfold unify_arguments. apply (fold_of_pairs env). apply forall2_diag. intros y Hy.
      apply (proj2 (reflexivity_with_arguments env k)); [exact (Hys y Hy)|].
      pose proof (argument_depth_below mr c ys' y Hy). unfold k. lia. }
    unfold is_assignable_to, empty_unification in Hobj.
    destruct (unify env n0 (RootResolved ma ca ys) (RootResolved mo e xs) (Ongoing [])) as [[w|]|] eqn:Eo; try discriminate Hobj.
    pose proof (proj1 (keeps_states_with_arguments env wf n0) _ _ [] w Hfy Hfo Eo) as ->.
    pose proof (proj1 (transitivity_with_arguments env wf (n0 + S k)) _ _ _ n0 (S k) [] (le_n _) Hfo Hfy HfD Eo HD) as ED.
    replace (n0 + S k) with (S (n0 + k)) in ED by lia.
    rewrite unify_classes in ED.
    destruct (base_type_is_subtype_of env e c) eqn:Hbe; [|discriminate ED].
    match type of ED with context [if Model.is_subtype_of ?x ?y then _ else _] =>
        destruct (Model.is_subtype_of x y); [|discriminate ED] end.
    rewrite (class_eqb_false e nothing He), <- Hzs in ED.
    assert (Hlz: length zs = length ys').
    { rewrite Hly. subst zs. destruct (Class_eq_dec e c) as [<-|Hne].
      - rewrite class_eqb_refl. exact (proj1 (root_in_fragment env mo e xs Hfo)).
      - rewrite (class_eqb_false _ _ Hne). destruct (root_in_fragment env mo e xs Hfo) as [Hlx Hxs].
        exact (proj1 (supertype_arguments_in_fragment env wf e c xs Hne He Hbe Hlx Hxs)). }
    pose proof (pairwise_of_arguments env (n0 + k) ys' zs [] ltac:(lia)
        (fun t a w0 Ht Ha E => proj2 (keeps_states_with_arguments env wf (n0 + k)) t a [] w0 (Hys t Ht) (Hfzs a Ha) E) ED) as Hp.
    exists ys', (n0 + k). split; [exact Hl|]. split; [lia|]. split; [exact Hys|]. split; [exact Hcap|]. split; [exact Hownu|].
    split; [exact Hwfu|]. split; [exact Hp|].
    (* the variables not bound exactly: those of the function, as they were *)
    intros p st Hp' Hex. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin].
    - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
      destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
      rewrite (Hcap i p bound y Hi Hy) in Hp'. injection Hp' as <-. discriminate Hex.
    - pose proof Hp' as Hp2. rewrite (Hoth p Hnin) in Hp2. unfold s0 in Hp2. destruct (lookup_for_inference_in _ _ p st Hp2) as [bound Hin].
      apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin)|].
      exists bound. split; [exact Hin|]. rewrite (Hownu p bound Hin) in Hp'. injection Hp' as <-. reflexivity.
Qed.

(*
 * Calling a member function is sound: the function is declared in class c; the receiver is a reference
 * to a class ca below c, whose type arguments, as those of c, are captured by the type parameters of
 * c; the object called on is of a class e below ca, its type arguments exact, and so as those of c
 * (object_arguments_exact: the type arguments of supertypes are exact), within the bounds of the
 * type parameters of c. Inferring the type parameters of the function from
 * the arguments gives them lower and upper bounds, and their final values. Whatever argument is
 * accepted for a parameter fits the parameter with the type parameters of c replaced by the type
 * arguments of the object as c, and those of the function by their final values.
 *)
Theorem member_call_through_subtypes_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is; its type arguments are exact, and as those of c within the bounds *)
    in_fragment env (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> ifrag env P = true /\ refs_within (cvars ++ ovars) P) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (* the final values of the type parameters of the function, which are bounds, are among the types
       variables are replaced with *)
    (forall p bound, In (p, bound) ovars -> bfrag (final_value_of U p) -> xfrag (final_value_of U p)) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of U (fst v)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hxx Hzb
        HPs HAs Hfold Hfinal b Hbdef.
    pose proof (object_arguments_exact c mo e xs zs He (object_below n mr c _ ma ca ys _ u mo e xs n0 Hrec Hobj) Hfo Hxx Hzs) as Hzx.
    destruct (receiver_and_object n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n1 [Hl [Hlz [Hys [Hcap [Hownu [Hwfu [Hp _]]]]]]]]].
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    (* the variable states unify ends with, with the bounds themselves for the type parameters *)
    set (b0 := map (fun v => (fst v, TypeArgument Model.invariant ref (snd v))) vars).
    destruct (uniform_fuel_list vars (fun f v => unify env f (snd v) (snd v) (Ongoing []) = Some (Ongoing [])))
        as [K0 HK0].
    { intros f f' v Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { intros [p bound] Hin. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (to_generic P) = true).
    { intros P HP. apply (bound_in_from_refs vars _ _ P (or_introl (proj1 (HPs P HP))) (proj2 (HPs P HP))).
      - intros p bound Hin. unfold binds_exactly, b0. rewrite (lookup_map_vars vars _ p bound Hnd' Hin). cbn [snd].
        rewrite (in_fragment_is_gfrag env _ (Hbounds p bound Hin)). unfold respects. pose proof (HK0 (p, bound) Hin) as E0. cbn [snd] in E0. rewrite E0. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    destruct (invocation_sound nf Ps As u U b0 K0 Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb0 P HP)) HAs Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify nf _ u U Hfold) as [Hkeep Hkeep2].
    assert (Hfinal': forall p bound, In (p, bound) ovars -> xfrag (final_value_of U p)).
    { intros p bound Hin. apply (Hfinal p bound Hin).
      destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 _]]].
      destruct (HwfU p st2 HlU) as [_ [_ Hw]]. destruct (Hw He2) as [_ [_ [_ [Hbu Hbl]]]].
      unfold final_value_of, final_value, Constraints.final_value. rewrite HlU. destruct (is_non_nullable_nothing env (lower_bound st2)); assumption. }
    (* the type parameters of the function: their final values, below their bounds *)
    assert (Hfin: forall p bound, In (p, bound) ovars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ final_value_of U p = final_value st /\ fits st ref (final_value st)
        /\ exists f, unify env f bound (final_value st) (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 [_ Hst2]]]].
      pose proof (Hfinal' p bound Hin) as Hff. unfold final_value_of in Hff. rewrite HlU in Hff.
      pose proof (final_value_fits U p st2 ref HwfU HlU He2 Hff) as Hfit.
      exists st2. split; [exact HlU|]. split; [exact He2|]. split; [unfold final_value_of; rewrite HlU; reflexivity|].
      split; [exact Hfit|].
      destruct (HwfU p st2 HlU) as [_ [_ Hw]]. destruct (Hw He2) as [_ [_ [Hbs _]]].
      unfold fits, Constraints.fits in Hfit. rewrite He2 in Hfit. destruct Hfit as [_ [K2 E2]].
      destruct (Hbs _ K2 Hff E2) as [f Ef]. cbn [static_upper_bound] in Hst2. rewrite Hst2 in Ef. exists f. exact Ef. }
    (* the type arguments of b, within the bounds *)
    assert (Hlookup: forall p bound, In (p, bound) vars -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ gfrag env x = true
        /\ exists f, unify env f bound x (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. rewrite Hbdef, lookup_app. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct (In_nth_error _ _ Hin) as [i Hi].
        assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
        destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
        rewrite (lookup_parameter env wf c zs i p z Hpi Hz).
        destruct (Hzb i p bound z Hi Hz) as [o [x [f [-> Ef]]]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [Ho Hx].
        exists o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact (in_fragment_is_gfrag env _ Hx)|]. exists f. exact Ef.
      - assert (Hnin: ~ In p (parameter_ids env c))
            by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
        rewrite (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
        assert (Hndo: NoDup (map fst ovars)).
        { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
          inversion H. apply IH. assumption. }
        rewrite (lookup_map_vars ovars (fun v => TypeArgument Model.invariant ref (final_value_of U (fst v))) p bound Hndo Hin).
        cbn [fst]. exists ref, (final_value_of U p). split; [reflexivity|]. split; [reflexivity|].
        split; [exact (xfrag_gfrag _ (Hfinal' p bound Hin))|].
        destruct (Hfin p bound Hin) as [st [_ [_ [-> [_ Ef]]]]]. exact Ef. }
    destruct (uniform_fuel_list vars (fun f v => forall o x, lookup_binding b (fst v) = Some (TypeArgument Model.invariant o x) ->
        unify env f (snd v) x (Ongoing []) = Some (Ongoing []))) as [K HK].
    { intros f f' v Hle E o x Hx. exact (unify_fuel_monotone env f f' _ _ _ _ Hle (E o x Hx)). }
    { intros [p bound] Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [_ [_ [f Ef]]]]]].
      exists f. intros o' x' Hx'. cbn [fst snd] in Hx' |- *. rewrite Hl' in Hx'. injection Hx' as <- <-. exact Ef. }
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (to_generic P) = true).
    { intros P HP. apply (bound_in_from_refs vars _ _ P (or_introl (proj1 (HPs P HP))) (proj2 (HPs P HP))).
      - intros p bound Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [Ho [Hx _]]]]].
        unfold binds_exactly. rewrite Hl', Ho, Hx. unfold respects. pose proof (HK (p, bound) Hin o x Hl') as E1. cbn [snd] in E1. rewrite E1. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        destruct (Hlookup q bound Hin) as [o [x [Hl' [Ho _]]]]. simpl. rewrite Hl'. exact Ho. }
    destruct (invocation_sound nf Ps As u U b K Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb P HP)) HAs Hfold) as [_ Hsound].
    (* the type arguments satisfy the variable states unify ends with *)
    apply Hsound. intros p o x Hpb.
    assert (Hin: exists bound, In (p, bound) vars).
    { rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
      - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
      - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of U q)) p _ Hpb) as [_ Hin].
        apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        exists bound. apply in_or_app. right. exact Hin. }
    destruct Hin as [bound Hin]. unfold vars in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - (* a type parameter of c: the type argument of the object, captured by that of the receiver *)
      destruct (In_nth_error _ _ Hin) as [i Hi].
      assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
      destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
      destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
      rewrite Hbdef, lookup_app, (lookup_parameter env wf c zs i p z Hpi Hz) in Hpb. injection Hpb as ->.
      pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [_ Hfx].
      split; [exact (in_fragment_xfrag _ Hfx)|]. exists (mkVariableState bound y y true true).
      split; [exact (Hkeep p _ (Hcap i p bound y Hi Hy) eq_refl)|].
      pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy2.
      destruct y as [| | | |vb ob X| |]; try discriminate Hfy2.
      unfold fits, Constraints.fits. cbn [is_exact upper_bound lower_bound]. exists vb, ob, X, n1. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hfy2|]. split; [exact Hfx|]. apply (unify_fuel_monotone env n1); [lia|].
      exact (Forall2_nth_error _ zs ys' i _ _ Hp Hz Hy).
    - (* a type parameter of the function: its final value *)
      assert (Hnin: ~ In p (parameter_ids env c))
          by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None) in Hpb.
      destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of U q)) p _ Hpb) as [Ea _].
      injection Ea as Eo2 Ex2. subst o x.
      destruct (Hfin p bound Hin) as [st [HlU [_ [Hfv [Hfit _]]]]].
      split; [exact (Hfinal' p bound Hin)|]. exists st. split; [exact HlU|]. rewrite Hfv. exact Hfit.
Qed.

(* The same, where the receiver and the object are of the class the function is declared in *)
Theorem member_call_with_type_parameters_sound: forall n mr c cvars ovars ma ys u mo xs n0 Ps As nf U,
    c <> nothing -> map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma c ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma c ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is, of exact type arguments within the bounds *)
    length xs = length (parameter_ids env c) -> (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error xs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    is_assignable_to env n0 (RootResolved mo c xs) (RootResolved ma c ys) = Some true ->
    (* the parameters and the arguments, accepted in turn *)
    (forall P, In P Ps -> ifrag env P = true /\ refs_within (cvars ++ ovars) P) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (* the final values of the type parameters of the function, which are bounds, are among the types
       variables are replaced with *)
    (forall p bound, In (p, bound) ovars -> bfrag (final_value_of U p) -> xfrag (final_value_of U p)) ->
    forall b, b = bindings_of env c xs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of U (fst v)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ys u mo xs n0 Ps As nf U Hc Hids Hnd Hbounds Hfy Hrec Hlx Hxs Hxb Hobj HPs HAs Hfold Hfinal
        b Hbdef.
    assert (Hfo: in_fragment env (RootResolved mo c xs) = true).
    { change (Nat.eqb (length xs) (length (parameter_ids env c)) && forallb (argument_in_fragment env) xs = true).
      rewrite Hlx, Nat.eqb_refl. apply forallb_forall. intros x Hx. pose proof (Hxs x Hx) as E.
      destruct x as [| | | |[] o nx| |]; try discriminate E. simpl in E |- *. apply andb_true_iff in E. apply E. }
    exact (member_call_through_subtypes_sound n mr c cvars ovars ma c ys u mo c xs xs n0 Ps As nf U Hc Hc Hc Hids Hnd Hbounds
        Hfy Hrec Hfo Hobj ltac:(rewrite class_eqb_refl; reflexivity) Hxs Hxb HPs HAs Hfold Hfinal b Hbdef).
Qed.

End MemberCalls.
