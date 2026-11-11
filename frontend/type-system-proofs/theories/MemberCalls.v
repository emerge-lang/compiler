From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From Stdlib Require Import Bool List Arith Lia Sorting.
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
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

Variables xfrag bfrag: EType -> Prop.
Hypothesis types: inference_types env xfrag bfrag.
Let xfrag_gfrag := it_xfrag_gfrag env xfrag bfrag types.
Let in_fragment_xfrag := it_in_fragment_xfrag env xfrag bfrag types.
Let in_fragment_bfrag := it_in_fragment_bfrag env xfrag bfrag types.

Let in_fragment_no_vars := Inference.in_fragment_no_vars env.
Let argument_in_fragment_no_vars := Inference.argument_in_fragment_no_vars env.
Let fits := Constraints.fits env.
Let final_value := Constraints.final_value env.
Let wf_states := Constraints.wf_states env xfrag bfrag.
Hypothesis supertype_of_classes: closest_common_supertype_of_classes env.
(* The type parameters of the functions here are bounded by class types, so the arguments needn't be
   without contravariance (Constraints.strict) *)
Let invocation_sound := Constraints.invocation_sound env wf xfrag bfrag types supertype_of_classes false
    (fun E => False_ind _ (diff_false_true E)).
Let final_value_fits := Constraints.final_value_fits env xfrag bfrag types false.

Definition final_value_of (u: VariableStates) (p: TypeParameterId): EType :=
    match lookup_state u p with Some st => final_value st | None => bottom_type end.

Lemma lookup_for_inference: forall (vars: list (TypeParameterId * EType)) caps p bound, NoDup (map fst vars) -> In (p, bound) vars ->
    lookup_state (map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) caps))) vars) p
    = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false (existsb (param_eqb p) caps)).
Proof.
    intros vars caps. induction vars as [|[q bq] rest IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_for_inference_in: forall (vars: list (TypeParameterId * EType)) caps p st,
    lookup_state (map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) caps))) vars) p = Some st ->
    exists bound, In (p, bound) vars.
Proof.
    intros vars caps. induction vars as [|[q bq] rest IH]; intros p st H; simpl in H; [discriminate H|].
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. exists bq. left. reflexivity.
    - destruct (IH p st H) as [bound Hin]. exists bound. right. exact Hin.
Qed.

Lemma nodup_app_l: forall (ps1 ps2: list TypeParameterId), NoDup (ps1 ++ ps2) -> NoDup ps1.
Proof.
    intros ps1 ps2. induction ps1 as [|x ps1 IH]; intros H; [constructor|]. inversion H as [|? ? Hnotin H2]. subst.
    constructor; [intros Hx; apply Hnotin, in_or_app; left; exact Hx|exact (IH H2)].
Qed.

Lemma nodup_app_disjoint: forall (ps1 ps2: list TypeParameterId) p, NoDup (ps1 ++ ps2) -> In p ps1 -> In p ps2 -> False.
Proof.
    intros ps1 ps2 p. induction ps1 as [|x ps1 IH]; intros Hnd H1 H2; [destruct H1|]. inversion Hnd as [|? ? Hnotin Hnd2]. subst.
    destruct H1 as [->|H1]; [apply Hnotin, in_or_app; right; exact H2|exact (IH Hnd2 H1 H2)].
Qed.

Lemma lookup_app: forall (b1 b2: Bindings) p,
    lookup_binding (b1 ++ b2) p = match lookup_binding b1 p with Some a => Some a | None => lookup_binding b2 p end.
Proof.
    intros b1 b2 p. induction b1 as [|[q a] b1 IH]; [reflexivity|]. simpl. destruct (param_eqb p q); [reflexivity|exact IH].
Qed.

Lemma lookup_own: forall (l: list (TypeParameterId * EType)) (f: TypeParameterId -> EType) p a,
    lookup_binding (map (fun entry => (fst entry, f (fst entry))) l) p = Some a -> a = f p /\ In p (map fst l).
Proof.
    intros l f p a. induction l as [|[q bq] l IH]; intros H; simpl in H; [discriminate H|].
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. injection H as <-. split; [reflexivity|left; reflexivity].
    - destruct (IH H) as [-> Hin]. split; [reflexivity|right; exact Hin].
Qed.

Lemma fold_keeps_exact_unify: forall n (l: list (EType * EType)) s s',
    fold_unify (fun inner '(P, A) => unify env n P A inner) l (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros n l s s' H. apply (fold_keeps_exact (fun inner '(P, A) => unify env n P A inner) l s s'); [| |exact H].
    - intros [P A] s0 s0' _ E. exact (unify_keeps_exact env n P A s0 s0' E).
    - intros [P A] _. apply unify_keeps_failure.
Qed.

Lemma template_not_loose: forall sub ys, length ys = length (parameter_ids env sub) ->
    (forall y, In y ys -> is_loose y = false) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> mentions_loosely_bound (bindings_of env sub ys) t = false)
    /\ (forall x, argument_depth x <= k -> template_argument env sub x = true -> mentions_loosely_bound (bindings_of env sub ys) x = false).
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
    - intros x Hd Hr. destruct (template_kind env sub x Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hl) Hi) as [y Hy].
        rewrite (mentions_parameter_template _ p bp y (lookup_parameter env wf sub ys i p y Hi Hy)).
        apply Hys. eapply nth_error_In. exact Hy.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn].
Qed.

(* The type arguments of a supertype, for exact type arguments of the subclass, are exact where the
   supertype is declared with exact ones *)
Lemma supertype_arguments_exact: forall sub c xs, sub <> c -> sub <> nothing -> base_type_is_subtype_of env sub c = true ->
    length xs = length (parameter_ids env sub) -> (forall x, In x xs -> exact_argument env x = true) ->
    (forall y, In y (supertype_arguments env sub c) -> exact_template_argument y = true) ->
    forall z, In z (parameterized_supertype_arguments env sub xs c) -> exact_argument env z = true.
Proof.
    intros sub c xs Hne Hn Hb Hl Hxs Hex z Hz.
    destruct (wf_supertypes_are_templates env wf sub c Hne Hn Hb) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Hz. apply in_map_iff in Hz. destruct Hz as [y [<- Hr]].
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true).
    { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o nx| |]; try discriminate E.
      simpl in E |- *. apply andb_true_iff in E. apply E. }
    assert (Hta: forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; apply (argument_in_fragment_is_type_argument env), Hfxs, Hx).
    destruct (template_kind env sub y (Ht y Hr)) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
    - destruct (nth_error_same_length _ xs i p (eq_sym Hl) Hi) as [x Hx].
      rewrite (selects env wf sub xs p bp i x Hi Hx (Hta x (nth_error_In _ _ Hx))). apply Hxs. eapply nth_error_In. exact Hx.
    - pose proof (Hex _ Hr) as Hexr. simpl in Hexr. destruct v; try discriminate Hexr.
      rewrite (instantiate_template_argument env _ Model.invariant o n Ho (template_shape env sub n Hn')).
      assert (Hnl: forall x, In x xs -> is_loose x = false).
      { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o' nx| |]; try discriminate E.
        destruct o'; try discriminate E; reflexivity. }
      rewrite (proj1 (template_not_loose sub xs Hl Hnl (depth n)) n (le_n _) Hn').
      simpl. destruct o; try discriminate Ho; try discriminate Hexr;
          rewrite (template_type_instance_in_fragment env wf sub xs n Hl Hfxs Hn'); reflexivity.
Qed.

(* The object is of a class below the one the function is declared in *)
Lemma object_below: forall n0 mr c targs ma ca ys s' s mo sub xs n1,
    unify env n0 (RootResolved mr c targs) (RootResolved ma ca ys) (Ongoing s') = Some (Ongoing s) ->
    is_assignable_to env n1 (RootResolved mo sub xs) (RootResolved ma ca ys) = Some true ->
    base_type_is_subtype_of env sub c = true.
Proof.
    intros n0 mr c targs ma ca ys s' s mo sub xs n1 Hrec Hobj.
    destruct n0 as [|n0]; [discriminate Hrec|]. rewrite unify_classes in Hrec.
    destruct (base_type_is_subtype_of env ca c) eqn:Hbca; [|discriminate Hrec].
    unfold is_assignable_to, empty_unification in Hobj.
    destruct n1 as [|n1]; [discriminate Hobj|]. rewrite unify_classes in Hobj.
    destruct (base_type_is_subtype_of env sub ca) eqn:Hbe; [|discriminate Hobj].
    exact (base_type_is_subtype_of_trans env wf sub ca c Hbe Hbca).
Qed.

(* The type arguments of the object, as those of a class it is below, are exact *)
Lemma object_arguments_exact: forall c mo sub xs zs, sub <> nothing -> base_type_is_subtype_of env sub c = true ->
    in_fragment env (RootResolved mo sub xs) = true -> (forall x, In x xs -> exact_argument env x = true) ->
    zs = (if class_eqb sub c then xs else parameterized_supertype_arguments env sub xs c) ->
    forall z, In z zs -> exact_argument env z = true.
Proof.
    intros c mo sub xs zs He Hbe Hfo Hxs ->. destruct (Class_eq_dec sub c) as [<-|Hne]; [rewrite class_eqb_refl; exact Hxs|].
    rewrite (class_eqb_false _ _ Hne).
    apply (supertype_arguments_exact sub c xs Hne He Hbe (proj1 (root_in_fragment env mo sub xs Hfo)) Hxs).
    intros r Hr. exact (wf_supertypes_are_exact env wf sub c r Hr).
Qed.

Lemma forall2_diag: forall {T: Type} (R: T -> T -> Prop) (l: list T), (forall x, In x l -> R x x) -> Forall2 R l l.
Proof.
    intros T R l H. induction l as [|x l IH]; constructor; [apply H; left; reflexivity|].
    apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* The type parameters a type mentions, in references to them and as ownership, are among vars, with
   the bounds vars have for them, class types without type parameters *)
Fixpoint refs_within (vars: list (TypeParameterId * EType)) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => refs_within vars a /\ acc) True arguments
    | Nullable n => refs_within vars n
    (* a type variable also of a mutability given to it, or narrowed, as at the top of the type of a parameter *)
    | Generic (mkGenericRef None false p []) | TypeVariable (mkGenericRef _ _ p []) =>
        In (p, parameter_bound env p) vars /\ sfrag env (parameter_bound env p) = true /\ closed (parameter_bound env p) = true
    | Generic _ | TypeVariable _ => False
    | TypeArgument _ o n => (forall q, o = parameter_ownership q -> In q (map fst vars)) /\ refs_within vars n
    | Intersection components => fold_right (fun a acc => refs_within vars a /\ acc) True components
    | _ => True
    end.

(* A reference to a type parameter whose bound is a class type without type parameters is bound in
   where the parameter is bound within the bound, of the mutability given to the reference and without
   null where it is narrowed *)
Lemma closed_ref_bound_in: forall b d g, sfrag env (Generic g) = true -> variables_of g = [] ->
    sfrag env (parameter_bound env (param_of g)) = true -> closed (parameter_bound env (param_of g)) = true ->
    bound_in env b d [] (Generic g) = binds_ref env b d [] g.
Proof.
    intros b d [gm nn p vs] Hs Hv Hf Hc. cbn [variables_of param_of] in Hv, Hf, Hc. subst vs.
    destruct (proj1 (closed_facts env wf b d [] (sdepth _)) _ (le_n _) Hf Hc) as [HB [_ [Hb _]]].
    assert (Heff: effective_bound env (mkGenericRef gm nn p []) = bound_apply env gm nn (parameter_bound env p))
        by (rewrite (effective_bound_eq env ranked); destruct gm, nn; reflexivity).
    assert (Hca: closed (bound_apply env gm nn (parameter_bound env p)) = true).
    { destruct (fragment_cases env _ HB) as [[m [c [args E]]]|[m [c [args [E _]]]]]; rewrite E in Hc |- *;
          destruct gm, nn; exact Hc. }
    assert (Ht: top_bound_in env b d [] (mkGenericRef gm nn p []) = true).
    { rewrite (top_bound_in_eq env wf b d []), Heff. clear -Hca. revert Hca. generalize (bound_apply env gm nn (parameter_bound env p)) as t.
      fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try discriminate H;
          [exact (IH n H)|apply andb_true_iff in H; exact (IH n (proj2 H))]. }
    change (bound_in env b d [] (Generic (mkGenericRef gm nn p [])))
        with (binds_ref env b d [] (mkGenericRef gm nn p []) && no_type_variables (mkGenericRef gm nn p [])
            && top_bound_in env b d [] (mkGenericRef gm nn p []) && param_bound_in env b d [] p).
    rewrite Ht, (param_bound_in_eq env wf b d [] p), Hb, !andb_true_r. reflexivity.
Qed.

Lemma bound_in_from_refs: forall vars b d t, (ifrag env t = true \/ argument_ifrag env t = true) -> refs_within vars t ->
    (forall p bound, In (p, bound) vars -> binds_exactly env b d [] p bound = true) ->
    (forall gm nn p, In (p, parameter_bound env p) vars -> sfrag env (Generic (mkGenericRef gm nn p [])) = true ->
        sfrag env (parameter_bound env p) = true -> closed (parameter_bound env p) = true ->
        binds_ref env b d [] (mkGenericRef gm nn p []) = true) ->
    (forall q, In q (map fst vars) -> ownership_bound b (parameter_ownership q) = true) ->
    bound_in env b d [] (to_generic t) = true.
Proof.
    intros vars b d t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Hf H Hp Hr Ho.
    destruct Hf as [Hf|Hf].
    - destruct (ifrag_cases env wf t Hf) as [[m [c [args [-> [_ [_ Hargs]]]]]]|[[m_bot ->]|[[m [c [args [-> Ht']]]]|[p [-> Hfb]]]]].
      + change (forallb (bound_in env b d []) (map to_generic args) = true). apply forallb_forall. intros a' Ha'.
        apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        apply (IH (esize a)); [pose proof (esize_in args a Ha); simpl; lia|reflexivity|right; exact (Hargs a Ha)| |exact Hp|exact Hr|exact Ho].
        exact (fold_and_in _ args H a Ha).
      + reflexivity.
      + change (bound_in env b d [] (to_generic (RootResolved m c args)) = true).
        apply (IH (esize (RootResolved m c args))); [simpl; lia|reflexivity|left; exact Ht'|exact H|exact Hp|exact Hr|exact Ho].
      + simpl in H. destruct H as [H [Hfb' Hcb]]. change (bound_in env b d [] (Generic (mkGenericRef None false p [])) = true).
        rewrite (binds_ref_closed env wf b d [] p Hfb' Hcb). exact (Hp p _ H).
    - destruct t as [| | | |v o n| |]; try discriminate Hf. simpl in Hf, H |- *. destruct H as [Hq Hn]. apply andb_true_iff. split.
      + destruct o as [| | |q]; try reflexivity. exact (Ho q (Hq q eq_refl)).
      + change (nfrag env n = true) in Hf. destruct (nfrag_cases env n Hf) as [Hf'|[gm [nn [q [Eq Hsq]]]]].
        * apply (IH (esize n)); [simpl; lia|reflexivity|left; exact Hf'|exact Hn|exact Hp|exact Hr|exact Ho].
        * (* a reference of a mutability given to it, narrowed or made nullable *)
          assert (Hn': In (q, parameter_bound env q) vars /\ sfrag env (parameter_bound env q) = true
              /\ closed (parameter_bound env q) = true) by (destruct Eq as [-> | ->]; exact Hn).
          destruct Hn' as [Hin [Hfb Hcb]].
          assert (Hg: bound_in env b d [] (Generic (mkGenericRef gm nn q [])) = true)
              by (rewrite (closed_ref_bound_in b d _ Hsq eq_refl Hfb Hcb); exact (Hr gm nn q Hin Hsq Hfb Hcb)).
          destruct Eq as [-> | ->]; exact Hg.
Qed.

(* The same for the type of a parameter, a type variable made nullable as the plain reference; of an
   intersection, each component *)
Lemma pbound_in_from_refs: forall vars b d t, kqfrag env t = true -> refs_within vars t ->
    (forall p bound, In (p, bound) vars -> binds_exactly env b d [] p bound = true) ->
    (forall gm nn p, In (p, parameter_bound env p) vars -> sfrag env (Generic (mkGenericRef gm nn p [])) = true ->
        sfrag env (parameter_bound env p) = true -> closed (parameter_bound env p) = true ->
        binds_ref env b d [] (mkGenericRef gm nn p []) = true) ->
    (forall q, In q (map fst vars) -> ownership_bound b (parameter_ownership q) = true) ->
    bound_in env b d [] (pgeneric t) = true.
Proof.
    intros vars b d t Hq H Hp Hr Ho. destruct (kqfrag_components env t Hq) as [Ht|[cs [Et HSi]]].
    2:{ assert (Hcs: refs_within vars (Intersection cs)) by (destruct Et as [-> | ->]; exact H).
        assert (Hall: bound_in env b d [] (Intersection (map to_generic cs)) = true).
        { change (forallb (bound_in env b d []) (map to_generic cs) = true). apply forallb_forall. intros c' Hc'.
          apply in_map_iff in Hc'. destruct Hc' as [C [<- HC]]. pose proof (fold_and_in _ cs Hcs C HC) as HrC.
          destruct (compfrag_cases env C (HSi C HC)) as [Hif|[gm [nn [q [-> [Hsq _]]]]]].
          - exact (bound_in_from_refs vars b d C (or_introl Hif) HrC Hp Hr Ho).
          - destruct HrC as [Hin [Hfb Hcb]]. cbn [to_generic].
            rewrite (closed_ref_bound_in b d _ Hsq eq_refl Hfb Hcb). exact (Hr gm nn q Hin Hsq Hfb Hcb). }
        destruct Et as [-> | ->]; exact Hall. }
    destruct (pfrag_cases env t Ht) as [Hf|[[gm [nn [p [-> _]]]]|[gm [nn [p [-> _]]]]]].
    - rewrite (pgeneric_ifrag env wf t Hf). exact (bound_in_from_refs vars b d t (or_introl Hf) H Hp Hr Ho).
    - change (bound_in env b d [] (Generic (mkGenericRef None false p [])) = true).
      destruct H as [Hin [Hfb' Hcb]]. rewrite (binds_ref_closed env wf b d [] p Hfb' Hcb). exact (Hp p _ Hin).
    - change (bound_in env b d [] (Generic (mkGenericRef None false p [])) = true).
      destruct H as [Hin [Hfb' Hcb]]. rewrite (binds_ref_closed env wf b d [] p Hfb' Hcb). exact (Hp p _ Hin).
Qed.

Lemma binds_ref_fuel: forall b d d' g, d <= d' -> binds_ref env b d [] g = true -> binds_ref env b d' [] g = true.
Proof.
    intros b d d' g Hle Hb. unfold binds_ref, respects in Hb |- *.
    destruct (lookup_binding b (param_of g)) as [[| | | |[] o x| |]|]; try discriminate Hb.
    apply andb_true_iff in Hb. destruct Hb as [Hox Hb]. rewrite Hox.
    destruct (unify env d _ _ (Ongoing [])) as [[w|]|] eqn:E; try discriminate Hb.
    rewrite (unify_fuel_monotone env d d' _ _ _ _ Hle E). reflexivity.
Qed.

(* The mutabilities and `!` a reference may be given *)
Definition ref_shapes: list (option Mutability * bool) :=
    [(None, false); (None, true)] ++ flat_map (fun m => [(Some m, false); (Some m, true)]) [own; immutable; readonly; mutable].

Lemma ref_shapes_complete: forall gm nn, In (gm, nn) ref_shapes.
Proof. intros [[]|] []; simpl; tauto. Qed.

(* Where the type parameters are bound within their bounds, class types, so is every reference to
   them, of any mutability and `!` *)
Lemma refs_fuel: forall (vars: list (TypeParameterId * EType)) b,
    (forall p bound, In (p, bound) vars -> in_fragment env bound = true) ->
    (forall p bound, In (p, bound) vars -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ xfrag x /\ exists n, unify env n bound x (Ongoing []) = Some (Ongoing [])) ->
    exists d, (forall p bound, In (p, bound) vars -> binds_exactly env b d [] p bound = true)
        /\ (forall gm nn p, In (p, parameter_bound env p) vars -> sfrag env (Generic (mkGenericRef gm nn p [])) = true ->
            sfrag env (parameter_bound env p) = true -> closed (parameter_bound env p) = true ->
            binds_ref env b d [] (mkGenericRef gm nn p []) = true).
Proof.
    intros vars b Hbounds Hlookup.
    (* each shape of reference: the instance of the binding, within the bound of that shape *)
    assert (Hshape: forall p bound gm nn, In (p, bound) vars -> exists d, parameter_bound env p = bound ->
        sfrag env (Generic (mkGenericRef gm nn p [])) = true -> sfrag env bound = true -> closed bound = true ->
        binds_ref env b d [] (mkGenericRef gm nn p []) = true).
    { intros p bound gm nn Hin. destruct (Hlookup p bound Hin) as [o [x [Ex [Ho [Hx [n Ef]]]]]].
      destruct (it_reference_within env xfrag bfrag types gm nn x bound n Hx (Hbounds p bound Hin) Ef) as [d HK].
      exists d. intros Ep Hs Hfb Hcb. subst bound.
      assert (Heff: effective_bound env (mkGenericRef gm nn p []) = bound_apply env gm nn (parameter_bound env p))
          by (rewrite (effective_bound_eq env ranked); destruct gm, nn; reflexivity).
      assert (Hsa: sfrag env (bound_apply env gm nn (parameter_bound env p)) = true /\ closed (bound_apply env gm nn (parameter_bound env p)) = true).
      { destruct (sfrag_cases env wf _ Hs) as [[? [? [? [E _]]]]|[[m_bot E]|[[? [? [? [E _]]]]|[[g [E Hg]]|[? [E _]]]]]]; try discriminate E.
        injection E as <-. destruct Hg as [Htf _]. rewrite Heff in Htf.
        destruct (proj1 (closed_facts env wf b d [] (sdepth _)) _ (le_n _) Hfb Hcb) as [HB _].
        destruct (fragment_cases env _ HB) as [[m [c [args E]]]|[m [c [args [E _]]]]]; rewrite E in Hcb, Htf |- *;
            destruct gm, nn; (split; [exact Htf|exact Hcb]). }
      unfold binds_ref. cbn [param_of]. rewrite Ex, Ho, (xfrag_gfrag x Hx). cbn [andb].
      rewrite (inst_ref_apply env), Heff, (inst_nested_closed env wf b d [] _ (proj1 Hsa) (proj2 Hsa)).
      unfold respects. rewrite HK. reflexivity. }
    destruct (uniform_fuel_list vars (fun d v => (forall o x, lookup_binding b (fst v) = Some (TypeArgument Model.invariant o x) ->
        unify env d (snd v) x (Ongoing []) = Some (Ongoing []))
        /\ forall gm nn, parameter_bound env (fst v) = snd v -> sfrag env (Generic (mkGenericRef gm nn (fst v) [])) = true ->
            sfrag env (snd v) = true -> closed (snd v) = true -> binds_ref env b d [] (mkGenericRef gm nn (fst v) []) = true))
        as [d HK].
    { intros n f' v Hle [E1 E2]. split.
      - intros o x Hx. exact (unify_fuel_monotone env n f' _ _ _ _ Hle (E1 o x Hx)).
      - intros gm nn Ep Hs Hfb Hcb. exact (binds_ref_fuel b n f' _ Hle (E2 gm nn Ep Hs Hfb Hcb)). }
    { intros [p bound] Hin. destruct (Hlookup p bound Hin) as [o [x [Ex [_ [_ [n Ef]]]]]].
      destruct (uniform_fuel_list ref_shapes (fun d s => parameter_bound env p = bound ->
          sfrag env (Generic (mkGenericRef (fst s) (snd s) p [])) = true -> sfrag env bound = true -> closed bound = true ->
          binds_ref env b d [] (mkGenericRef (fst s) (snd s) p []) = true)) as [Ks HKs].
      { intros f1 f1' s Hle E Ep Hs Hfb Hcb. exact (binds_ref_fuel b f1 f1' _ Hle (E Ep Hs Hfb Hcb)). }
      { intros [gm nn] _. exact (Hshape p bound gm nn Hin). }
      exists (max n Ks). cbn [fst snd]. split.
      - intros o' x' Ex'. rewrite Ex in Ex'. injection Ex' as <- <-. exact (unify_fuel_monotone env n (max n Ks) _ _ _ _ ltac:(lia) Ef).
      - intros gm nn Ep Hs Hfb Hcb. apply (binds_ref_fuel b Ks); [lia|].
        exact (HKs (gm, nn) (ref_shapes_complete gm nn) Ep Hs Hfb Hcb). }
    exists d. split.
    - intros p bound Hin. destruct (Hlookup p bound Hin) as [o [x [Ex [Ho [Hx _]]]]].
      unfold binds_exactly. rewrite Ex, Ho, (xfrag_gfrag x Hx). unfold respects. pose proof (proj1 (HK (p, bound) Hin) o x Ex) as E1. cbn [snd] in E1. rewrite E1. reflexivity.
    - intros gm nn p Hin Hs Hfb Hcb. exact (proj2 (HK (p, parameter_bound env p) Hin) gm nn eq_refl Hs Hfb Hcb).
Qed.

Lemma lookup_map_vars: forall (l: list (TypeParameterId * EType)) (f: TypeParameterId * EType -> EType) p bound,
    NoDup (map fst l) -> In (p, bound) l -> lookup_binding (map (fun entry => (fst entry, f entry)) l) p = Some (f (p, bound)).
Proof.
    intros l f. induction l as [|[q bq] l IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_combine_none: forall (ps: list TypeParameterId) (xs: list EType) p, ~ In p ps -> lookup_binding (combine ps xs) p = None.
Proof.
    intros ps. induction ps as [|q ps IH]; intros [|x xs] p H; try reflexivity. simpl.
    destruct (param_eqb p q) eqn:E; [apply param_eqb_eq in E; subst q; exfalso; apply H; left; reflexivity|].
    apply IH. intros Hin. apply H. right. exact Hin.
Qed.

(* The state a type parameter of the function starts inference with is one unify works with, whatever
   the states of the other variables *)
Definition initial_ok (strict: bool) (p: TypeParameterId) (bound: EType): Prop :=
    forall s, let st := mkVariableState bound (initial_upper_bound bound) bottom_type false false in
        no_vars (upper_bound st) = true /\ no_vars (lower_bound st) = true
        /\ (is_exact st = false -> is_capturable st = false
            /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
            /\ bfrag (upper_bound st) /\ bfrag (lower_bound st) /\ Constraints.static_ok env xfrag strict s p st)
        /\ vars_in (static_vars env p) (static_upper_bound st) = true.

(* So does one bounded by a class type *)
Lemma initial_ok_closed: forall strict p bound, in_fragment env bound = true -> initial_ok strict p bound.
Proof.
    intros strict p bound Hfb s. cbn zeta. cbn [upper_bound lower_bound is_exact is_capturable static_upper_bound].
    rewrite (initial_in_fragment env bound Hfb).
    split; [exact (in_fragment_no_vars bound Hfb)|]. split; [reflexivity|]. split.
    - intros _. split; [reflexivity|]. split; [exists 2; apply (below_all env wf [] bound 2 Hfb); lia|].
      split; [exact (in_fragment_bfrag _ Hfb)|]. split; [exact (in_fragment_bfrag _ (bottom_in_fragment env wf))|].
      unfold static_ok. cbn [static_upper_bound]. rewrite (in_fragment_no_vars bound Hfb). intros x f _ Ex; exists f; exact Ex.
    - exact (no_vars_in _ _ (in_fragment_no_vars bound Hfb)).
Qed.

(* What unifying the receiver leaves, and how the object relates to the receiver, as references to
   the class the function is declared in; the type parameters of the class bounded by class types *)
Lemma receiver_captures: forall n0 mr c cvars ovars ma ca ys s mo sub xs zs n1,
    c <> nothing -> ca <> nothing -> sub <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) cvars -> in_fragment env bound = true) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n0 (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing s) ->
    in_fragment env (RootResolved mo sub xs) = true ->
    is_assignable_to env n1 (RootResolved mo sub xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb sub c then xs else parameterized_supertype_arguments env sub xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    exists ys' n2,
        length ys' = length cvars /\ length zs = length cvars
        /\ (forall y, In y ys' -> argument_in_fragment env y = true)
        /\ (forall i p bound y, nth_error cvars i = Some (p, bound) -> nth_error ys' i = Some y ->
            lookup_state s p = Some (mkVariableState bound y y true true))
        /\ (forall p bound, In (p, bound) ovars -> lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false))
        /\ (forall p st, lookup_state s p = Some st -> In p (map fst cvars) \/ exists bound, In (p, bound) ovars)
        /\ Forall2 (fun z y => unify env n2 y z (Ongoing []) = Some (Ongoing [])) zs ys'
        /\ (forall p st, lookup_state s p = Some st -> is_exact st = false ->
            exists bound, In (p, bound) ovars /\ st = mkVariableState bound (initial_upper_bound bound) bottom_type false false).
Proof.
    intros n0 mr c cvars ovars ma ca ys s mo sub xs zs n1 Hc Hca He Hids Hnd Hcb Hfy Hrec Hfo Hobj Hzs Hzx.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) (map fst cvars))))
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
    destruct n0 as [|n0]; [discriminate Hrec|].
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
        lookup_state s0 p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true) /\ in_fragment env bound = true).
    { intros p bound Hin. split; [|exact (Hcb p bound Hin)].
      unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_introl Hin))), (Hcls p bound Hin). reflexivity. }
    destruct (capture_arguments env wf n0 cvars ys' s0 s Hndc Hl Hys Hfresh Hrec) as [Hcap Hoth].
    assert (Hownu: forall p bound, In (p, bound) ovars -> lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false)).
    { intros p bound Hin.
      assert (Hnin: ~ In p (map fst cvars)) by (intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite (Hoth p Hnin). unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_intror Hin))).
      rewrite (Hown p bound Hin). reflexivity. }
    (* the variables: those of c and of the function *)
    assert (Hdomu: forall p st, lookup_state s p = Some st -> In p (map fst cvars) \/ exists bound, In (p, bound) ovars).
    { intros p st Hp. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin]; [left; exact Hin|right].
      rewrite (Hoth p Hnin) in Hp. unfold s0 in Hp. destruct (lookup_for_inference_in _ _ p st Hp) as [bound Hin].
      apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin)|].
      exists bound. exact Hin. }
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
    destruct (unify env n1 (RootResolved ma ca ys) (RootResolved mo sub xs) (Ongoing [])) as [[w|]|] eqn:Eo; try discriminate Hobj.
    pose proof (proj1 (keeps_states_with_arguments env wf n1) _ _ [] w Hfy Hfo Eo) as ->.
    pose proof (proj1 (transitivity_with_arguments env wf (n1 + S k)) _ _ _ n1 (S k) [] (le_n _) Hfo Hfy HfD Eo HD) as ED.
    replace (n1 + S k) with (S (n1 + k)) in ED by lia.
    rewrite unify_classes in ED.
    destruct (base_type_is_subtype_of env sub c) eqn:Hbe; [|discriminate ED].
    match type of ED with context [if Model.is_subtype_of ?x ?y then _ else _] =>
        destruct (Model.is_subtype_of x y); [|discriminate ED] end.
    rewrite (class_eqb_false sub nothing He), <- Hzs in ED.
    assert (Hlz: length zs = length ys').
    { rewrite Hly. subst zs. destruct (Class_eq_dec sub c) as [<-|Hne].
      - rewrite class_eqb_refl. exact (proj1 (root_in_fragment env mo sub xs Hfo)).
      - rewrite (class_eqb_false _ _ Hne). destruct (root_in_fragment env mo sub xs Hfo) as [Hlx Hxs].
        exact (proj1 (supertype_arguments_in_fragment env wf sub c xs Hne He Hbe Hlx Hxs)). }
    pose proof (pairwise_of_arguments env (n1 + k) ys' zs [] ltac:(lia)
        (fun t a w0 Ht Ha E => proj2 (keeps_states_with_arguments env wf (n1 + k)) t a [] w0 (Hys t Ht) (Hfzs a Ha) E) ED) as Hp.
    exists ys', (n1 + k). split; [exact Hl|]. split; [lia|]. split; [exact Hys|]. split; [exact Hcap|]. split; [exact Hownu|].
    split; [exact Hdomu|]. split; [exact Hp|].
    (* the variables not bound exactly: those of the function, as they were *)
    intros p st Hp' Hex. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin].
    - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
      destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
      rewrite (Hcap i p bound y Hi Hy) in Hp'. injection Hp' as <-. discriminate Hex.
    - pose proof Hp' as Hp2. rewrite (Hoth p Hnin) in Hp2. unfold s0 in Hp2. destruct (lookup_for_inference_in _ _ p st Hp2) as [bound Hin].
      apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin)|].
      exists bound. split; [exact Hin|]. rewrite (Hownu p bound Hin) in Hp'. injection Hp' as <-. reflexivity.
Qed.

(* So, with the type parameters of the function starting as unify works with them *)
Lemma receiver_and_object_with: forall strict n0 mr c cvars ovars ma ca ys s mo sub xs zs n1,
    c <> nothing -> ca <> nothing -> sub <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) cvars -> in_fragment env bound = true) ->
    (forall p bound, In (p, bound) ovars -> initial_ok strict p bound) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n0 (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing s) ->
    in_fragment env (RootResolved mo sub xs) = true ->
    is_assignable_to env n1 (RootResolved mo sub xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb sub c then xs else parameterized_supertype_arguments env sub xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    exists ys' n2,
        length ys' = length cvars /\ length zs = length cvars
        /\ (forall y, In y ys' -> argument_in_fragment env y = true)
        /\ (forall i p bound y, nth_error cvars i = Some (p, bound) -> nth_error ys' i = Some y ->
            lookup_state s p = Some (mkVariableState bound y y true true))
        /\ (forall p bound, In (p, bound) ovars -> lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false))
        /\ wf_states strict s
        /\ Forall2 (fun z y => unify env n2 y z (Ongoing []) = Some (Ongoing [])) zs ys'
        /\ (forall p st, lookup_state s p = Some st -> is_exact st = false ->
            exists bound, In (p, bound) ovars /\ st = mkVariableState bound (initial_upper_bound bound) bottom_type false false).
Proof.
    intros strict n0 mr c cvars ovars ma ca ys s mo sub xs zs n1 Hc Hca He Hids Hnd Hcb Hinit Hfy Hrec Hfo Hobj Hzs Hzx.
    destruct (receiver_captures n0 mr c cvars ovars ma ca ys s mo sub xs zs n1 Hc Hca He Hids Hnd Hcb Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n2 [Hl [Hlz [Hys [Hcap [Hownu [Hdomu [Hp Hrest]]]]]]]]].
    exists ys', n2. split; [exact Hl|]. split; [exact Hlz|]. split; [exact Hys|]. split; [exact Hcap|]. split; [exact Hownu|].
    split; [|split; [exact Hp|exact Hrest]].
    (* the variable states are those unify works with *)
    intros p st Hp'. destruct (Hdomu p st Hp') as [Hin|[bound Hin]].
    - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
      destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
      rewrite (Hcap i p bound y Hi Hy) in Hp'. injection Hp' as <-. cbn [upper_bound lower_bound is_exact static_upper_bound].
      pose proof (argument_in_fragment_no_vars y (Hys y (nth_error_In _ _ Hy))) as Hny.
      split; [exact Hny|]. split; [exact Hny|]. split; [intros E; discriminate E|].
      exact (no_vars_in _ _ (in_fragment_no_vars bound (Hcb p bound Hin))).
    - rewrite (Hownu p bound Hin) in Hp'. injection Hp' as <-. exact (Hinit p bound Hin s).
Qed.

(* What unifying the receiver leaves, and how the object relates to the receiver, as references to
   the class the function is declared in *)
Lemma receiver_and_object: forall n0 mr c cvars ovars ma ca ys s mo sub xs zs n1,
    c <> nothing -> ca <> nothing -> sub <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n0 (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing s) ->
    in_fragment env (RootResolved mo sub xs) = true ->
    is_assignable_to env n1 (RootResolved mo sub xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb sub c then xs else parameterized_supertype_arguments env sub xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    exists ys' n2,
        length ys' = length cvars /\ length zs = length cvars
        /\ (forall y, In y ys' -> argument_in_fragment env y = true)
        /\ (forall i p bound y, nth_error cvars i = Some (p, bound) -> nth_error ys' i = Some y ->
            lookup_state s p = Some (mkVariableState bound y y true true))
        /\ (forall p bound, In (p, bound) ovars -> lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false))
        /\ (forall strict, wf_states strict s)
        /\ Forall2 (fun z y => unify env n2 y z (Ongoing []) = Some (Ongoing [])) zs ys'
        /\ (forall p st, lookup_state s p = Some st -> is_exact st = false ->
            exists bound, In (p, bound) ovars /\ st = mkVariableState bound (initial_upper_bound bound) bottom_type false false).
Proof.
    intros n0 mr c cvars ovars ma ca ys s mo sub xs zs n1 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx.
    (* the states are those unify works with whatever strict is: the bounds have no type variables *)
    pose proof (fun strict => receiver_and_object_with strict n0 mr c cvars ovars ma ca ys s mo sub xs zs n1 Hc Hca He Hids Hnd
        (fun p bound Hin => Hbounds p bound (in_or_app _ _ _ (or_introl Hin)))
        (fun p bound Hin => initial_ok_closed strict p bound (Hbounds p bound (in_or_app _ _ _ (or_intror Hin))))
        Hfy Hrec Hfo Hobj Hzs Hzx) as H.
    destruct (H false) as [ys' [n2 [Hl [Hlz [Hys [Hcap [Hownu [_ [Hp Hrest]]]]]]]]].
    exists ys', n2. split; [exact Hl|]. split; [exact Hlz|]. split; [exact Hys|]. split; [exact Hcap|]. split; [exact Hownu|].
    split; [|split; [exact Hp|exact Hrest]].
    intros strict. destruct (H strict) as [? [? [_ [_ [_ [_ [_ [Hw _]]]]]]]]. exact Hw.
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
Theorem member_call_through_subtypes_sound: forall n0 mr c cvars ovars ma ca ys s' mo sub xs zs n1 Ps As n2 s,
    c <> nothing -> ca <> nothing -> sub <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n0 (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing s') ->
    (* the object it is; its type arguments are exact, and as those of c within the bounds *)
    in_fragment env (RootResolved mo sub xs) = true ->
    is_assignable_to env n1 (RootResolved mo sub xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb sub c then xs else parameterized_supertype_arguments env sub xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error zs i = Some z ->
        exists o x n', z = TypeArgument Model.invariant o x /\ unify env n' bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> kqfrag env P = true /\ refs_within (cvars ++ ovars) P) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env n2 P A inner) (combine Ps As) (Ongoing s') = Some (Ongoing s) ->
    (* the final values of the type parameters of the function, which are bounds, are among the types
       variables are replaced with *)
    (forall p bound, In (p, bound) ovars -> bfrag (final_value_of s p) -> xfrag (final_value_of s p)) ->
    (* where a parameter type is an intersection, they are class types *)
    ((exists P cs, In P Ps /\ inter_of P = Some cs) -> forall p bound, In (p, bound) ovars -> in_fragment env (final_value_of s p) = true) ->
    forall b, b = bindings_of env c zs ++ map (fun entry => (fst entry, TypeArgument Model.invariant ref (final_value_of s (fst entry)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists n', is_assignable_to env n' A (inst env b P) = Some true.
Proof.
    intros n0 mr c cvars ovars ma ca ys s' mo sub xs zs n1 Ps As n2 s Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hxx Hzb
        HPs HAs Hfold Hfinal Hclass b Hbdef.
    pose proof (object_arguments_exact c mo sub xs zs He (object_below n0 mr c _ ma ca ys _ s' mo sub xs n1 Hrec Hobj) Hfo Hxx Hzs) as Hzx.
    destruct (receiver_and_object n0 mr c cvars ovars ma ca ys s' mo sub xs zs n1 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n3 [Hl [Hlz [Hys [Hcap [Hownu [Hwfu [Hp _]]]]]]]]].
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    (* the variable states unify ends with, with the bounds themselves for the type parameters *)
    set (b0 := map (fun entry => (fst entry, TypeArgument Model.invariant ref (snd entry))) vars).
    destruct (refs_fuel vars b0 Hbounds) as [K0 [HK0 HK0r]].
    { intros p bound Hin. exists ref, bound. split; [unfold b0; exact (lookup_map_vars vars _ p bound Hnd' Hin)|].
      split; [reflexivity|]. split; [exact (in_fragment_xfrag _ (Hbounds p bound Hin))|]. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (pgeneric P) = true).
    { intros P HP. apply (pbound_in_from_refs vars _ _ P (proj1 (HPs P HP)) (proj2 (HPs P HP)) HK0 HK0r).
      intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    destruct (invocation_sound n2 Ps As s' s (Hwfu false) (fun P HP => proj1 (HPs P HP)) HAs (fun E => False_ind _ (diff_false_true E)) Hfold)
        as [HwfU _].
    destruct (fold_keeps_exact_unify n2 _ s' s Hfold) as [Hkeep [Hkeep2 _]].
    assert (Hfinal': forall p bound, In (p, bound) ovars -> xfrag (final_value_of s p)).
    { intros p bound Hin. apply (Hfinal p bound Hin).
      destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 _]]].
      destruct (HwfU p st2 HlU) as [_ [_ [Hw _]]]. destruct (Hw He2) as [_ [_ [Hbu [Hbl _]]]].
      unfold final_value_of, final_value, Constraints.final_value. rewrite HlU. destruct (is_non_nullable_nothing env (lower_bound st2)); assumption. }
    (* the type parameters of the function: their final values, below their bounds *)
    assert (Hfin: forall p bound, In (p, bound) ovars -> exists st, lookup_state s p = Some st /\ is_exact st = false
        /\ final_value_of s p = final_value st /\ fits st ref (final_value st)
        /\ exists n', unify env n' bound (final_value st) (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 [_ Hst2]]]].
      pose proof (Hfinal' p bound Hin) as Hff. unfold final_value_of in Hff. rewrite HlU in Hff.
      pose proof (final_value_fits s p st2 ref HwfU HlU He2 Hff) as Hfit.
      exists st2. split; [exact HlU|]. split; [exact He2|]. split; [unfold final_value_of; rewrite HlU; reflexivity|].
      split; [exact Hfit|].
      destruct (HwfU p st2 HlU) as [_ [_ [Hw Hsv]]]. destruct (Hw He2) as [_ [_ [_ [_ Hok]]]].
      unfold fits, Constraints.fits in Hfit. rewrite He2 in Hfit. destruct Hfit as [_ [K2 E2]].
      cbn [static_upper_bound] in Hst2. unfold static_ok, Constraints.static_ok in Hok.
      rewrite Hst2, (in_fragment_no_vars bound (Hbounds p bound (in_or_app _ _ _ (or_intror Hin)))) in Hok.
      destruct (Hok _ K2 Hff E2) as [n' Ef]. rewrite Hst2 in Ef. exists n'. exact Ef. }
    (* the type arguments of b, within the bounds *)
    assert (Hlookup: forall p bound, In (p, bound) vars -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ xfrag x
        /\ exists n', unify env n' bound x (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. rewrite Hbdef, lookup_app. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct (In_nth_error _ _ Hin) as [i Hi].
        assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
        destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
        rewrite (lookup_parameter env wf c zs i p z Hpi Hz).
        destruct (Hzb i p bound z Hi Hz) as [o [x [n' [-> Ef]]]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [Ho Hx].
        exists o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact (in_fragment_xfrag _ Hx)|]. exists n'. exact Ef.
      - assert (Hnin: ~ In p (parameter_ids env c))
            by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
        rewrite (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
        assert (Hndo: NoDup (map fst ovars)).
        { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
          inversion H. apply IH. assumption. }
        rewrite (lookup_map_vars ovars (fun entry => TypeArgument Model.invariant ref (final_value_of s (fst entry))) p bound Hndo Hin).
        cbn [fst]. exists ref, (final_value_of s p). split; [reflexivity|]. split; [reflexivity|].
        split; [exact (Hfinal' p bound Hin)|].
        destruct (Hfin p bound Hin) as [st [_ [_ [-> [_ Ef]]]]]. exact Ef. }
    destruct (refs_fuel vars b Hbounds Hlookup) as [K [HK HKr]].
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (pgeneric P) = true).
    { intros P HP. apply (pbound_in_from_refs vars _ _ P (proj1 (HPs P HP)) (proj2 (HPs P HP)) HK HKr).
      intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        destruct (Hlookup q bound Hin) as [o [x [Hl' [Ho _]]]]. simpl. rewrite Hl'. exact Ho. }
    destruct (invocation_sound n2 Ps As s' s (Hwfu false) (fun P HP => proj1 (HPs P HP)) HAs (fun E => False_ind _ (diff_false_true E)) Hfold)
        as [_ Hsound].
    (* the type parameters bound in b *)
    assert (Hvars: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> exists bound, In (p, bound) vars).
    { intros p o x Hpb. rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
      - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
      - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of s q)) p _ Hpb) as [_ Hin].
        apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        exists bound. apply in_or_app. right. exact Hin. }
    (* where a parameter type is an intersection, class types *)
    assert (Hbf: (exists P cs, In P Ps /\ inter_of P = Some cs) -> bindings_in_fragment env b).
    { intros Hi p o x Hpb. destruct (Hvars p o x Hpb) as [bound Hin]. unfold vars in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct (In_nth_error _ _ Hin) as [i Hi'].
        assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi'; reflexivity).
        destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi') as [z Hz].
        rewrite Hbdef, lookup_app, (lookup_parameter env wf c zs i p z Hpi Hz) in Hpb. injection Hpb as ->.
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. exact (proj2 Hex).
      - assert (Hnin: ~ In p (parameter_ids env c))
            by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
        rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None) in Hpb.
        destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of s q)) p _ Hpb) as [Ea _].
        injection Ea as _ Ex2. subst x. exact (Hclass Hi p bound Hin). }
    (* the type arguments satisfy the variable states unify ends with *)
    apply (Hsound b K Hb); [|exact Hbf]. intros p o x Hpb.
    destruct (Hvars p o x Hpb) as [bound Hin]. unfold vars in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
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
      unfold fits, Constraints.fits. cbn [is_exact upper_bound lower_bound]. exists vb, ob, X, n3. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hfy2|]. split; [exact Hfx|]. apply (unify_fuel_monotone env n3); [lia|].
      exact (Forall2_nth_error _ zs ys' i _ _ Hp Hz Hy).
    - (* a type parameter of the function: its final value *)
      assert (Hnin: ~ In p (parameter_ids env c))
          by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None) in Hpb.
      destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of s q)) p _ Hpb) as [Ea _].
      injection Ea as Eo2 Ex2. subst o x.
      destruct (Hfin p bound Hin) as [st [HlU [_ [Hfv [Hfit _]]]]].
      split; [exact (Hfinal' p bound Hin)|]. exists st. split; [exact HlU|]. rewrite Hfv. exact Hfit.
Qed.

(* The same, where the receiver and the object are of the class the function is declared in *)
Theorem member_call_with_type_parameters_sound: forall n0 mr c cvars ovars ma ys s' mo xs n1 Ps As n2 s,
    c <> nothing -> map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma c ys) = true ->
    unify env n0 (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma c ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing s') ->
    (* the object it is, of exact type arguments within the bounds *)
    length xs = length (parameter_ids env c) -> (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error xs i = Some z ->
        exists o x n', z = TypeArgument Model.invariant o x /\ unify env n' bound x (Ongoing []) = Some (Ongoing [])) ->
    is_assignable_to env n1 (RootResolved mo c xs) (RootResolved ma c ys) = Some true ->
    (* the parameters and the arguments, accepted in turn *)
    (forall P, In P Ps -> kqfrag env P = true /\ refs_within (cvars ++ ovars) P) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env n2 P A inner) (combine Ps As) (Ongoing s') = Some (Ongoing s) ->
    (* the final values of the type parameters of the function, which are bounds, are among the types
       variables are replaced with *)
    (forall p bound, In (p, bound) ovars -> bfrag (final_value_of s p) -> xfrag (final_value_of s p)) ->
    (* where a parameter type is an intersection, they are class types *)
    ((exists P cs, In P Ps /\ inter_of P = Some cs) -> forall p bound, In (p, bound) ovars -> in_fragment env (final_value_of s p) = true) ->
    forall b, b = bindings_of env c xs ++ map (fun entry => (fst entry, TypeArgument Model.invariant ref (final_value_of s (fst entry)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists n', is_assignable_to env n' A (inst env b P) = Some true.
Proof.
    intros n0 mr c cvars ovars ma ys s' mo xs n1 Ps As n2 s Hc Hids Hnd Hbounds Hfy Hrec Hlx Hxs Hxb Hobj HPs HAs Hfold Hfinal
        Hclass b Hbdef.
    assert (Hfo: in_fragment env (RootResolved mo c xs) = true).
    { change (Nat.eqb (length xs) (length (parameter_ids env c)) && forallb (argument_in_fragment env) xs = true).
      rewrite Hlx, Nat.eqb_refl. apply forallb_forall. intros x Hx. pose proof (Hxs x Hx) as E.
      destruct x as [| | | |[] o nx| |]; try discriminate E. simpl in E |- *. apply andb_true_iff in E. apply E. }
    exact (member_call_through_subtypes_sound n0 mr c cvars ovars ma c ys s' mo c xs xs n1 Ps As n2 s Hc Hc Hc Hids Hnd Hbounds
        Hfy Hrec Hfo Hobj ltac:(rewrite class_eqb_refl; reflexivity) Hxs Hxb HPs HAs Hfold Hfinal Hclass b Hbdef).
Qed.

End MemberCalls.

(* ---------------------------------------------------------------------------------------------- *)
(* The type parameters of the class bounded by types mentioning them                              *)
(* ---------------------------------------------------------------------------------------------- *)

Section ClassBounds.

Variable env: Environment.
Hypothesis wf: wellformed env.
Hypothesis intersect_no_vars: forall x y, no_vars x = true -> no_vars y = true -> no_vars (intersect env x y) = true.
Hypothesis supertype_no_vars: forall x y, no_vars x = true -> no_vars y = true ->
    no_vars (closest_common_supertype_with env x y) = true.

(* The same variable states, as far as looking them up goes *)
Definition same_states (s s': VariableStates): Prop := forall q, lookup_state s q = lookup_state s' q.

(* Checking a candidate against a static upper bound whose type variables of a lower rank than its
   own are bound exactly leaves the variable states as they are *)
Lemma check_same: forall k p y B s s',
    ranked_states env s -> vars_in (static_vars env p) B = true -> no_vars y = true ->
    (forall q st, lookup_state s q = Some st -> parameter_rank env q < parameter_rank env p -> is_exact st = true) ->
    unify env k (with_candidate env p y B) y (Ongoing s) = Some (Ongoing s') -> same_states s' s.
Proof.
    intros k p y S s s' Hs HS HY Hex H.
    destruct (unify_keeps_from env wf intersect_no_vars supertype_no_vars k (parameter_rank env p) _ _ s s' Hs
        (or_intror (conj (candidate_below env wf p y S HS HY) HY)) H) as [Kf _].
    destruct (unify_keeps_exact env k _ _ s s' H) as [Ke1 [_ Ke3]].
    intros q. destruct (le_lt_dec (parameter_rank env p) (parameter_rank env q)) as [Hle|Hlt].
    - exact (Kf q Hle).
    - destruct (lookup_state s q) as [st|] eqn:Eq.
      + exact (Ke1 q st Eq (Hex q st Eq Hlt)).
      + exact (Ke3 q Eq).
Qed.

(* The type arguments captured: of the types A admits, without type variables, and that unify with
   Nothing as unify does with a class type, leaving the variable states as they are *)
Variable Q: EType -> bool.
Hypothesis A_shape: forall y, Q y = true -> is_type_argument y = true /\ no_vars y = true
    /\ forall vy oy x k s s', y = TypeArgument vy oy x -> unify env k x bottom_type (Ongoing s) = Some (Ongoing s') -> s' = s.

(* Capturing the type argument of a receiver, checked against the bound, where the check leaves the
   variable states as they are *)
Lemma capture_step_checked: forall n p bound s y s',
    lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true) ->
    Q y = true ->
    (forall vy oy x k s'', y = TypeArgument vy oy x ->
        unify env k (with_candidate env p x bound) x (Ongoing s) = Some (Ongoing s'') -> same_states s'' s) ->
    unify env n (receiver_leaf (p, bound)) y (Ongoing s) = Some (Ongoing s') ->
    same_states s' (set_state s p (mkVariableState bound y y true true)).
Proof.
    intros n p bound s y s' Hl Hy Hchk H. destruct (A_shape y Hy) as [Hta [_ Hk]].
    destruct y as [| | | |vy oy x| |]; try discriminate Hta.
    destruct n as [|n]; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_type_argument, receiver_leaf in H. cbn beta iota zeta in H.
    replace (ownership_is_assignable_to oy any_ownership) with true in H by (destruct oy; reflexivity).
    cbn [negb fst snd] in H. unfold capturable in H. cbn beta iota in H. rewrite Hl in H. cbn [is_capturable is_exact negb andb] in H.
    unfold plus_exact_binding in H. rewrite Hl in H. cbn [upper_bound lower_bound static_upper_bound is_capturable] in H.
    unfold plus_binding_check, plus_static_check in H. cbn [static_upper_bound] in H.
    destruct (unify env n (initial_upper_bound bound) x (Ongoing s)) as [[s''|]|] eqn:E1; try discriminate H.
    destruct (unify env n (TypeArgument vy oy x) bottom_type (Ongoing s)) as [[w'|]|] eqn:E2; try discriminate H.
    assert (Ew: w' = s).
    { destruct n as [|n]; [discriminate E2|].
      destruct vy; rewrite unify_step_once in E2; unfold unify_step, unify_type_argument in E2; cbn beta iota zeta in E2;
          try (injection E2 as <-; reflexivity).
      - exact (Hk _ _ _ n s w' eq_refl E2).
      - exact (Hk _ _ _ n s w' eq_refl E2). }
    subst w'.
    remember (match vy with
        | invariant => if no_vars bound then Some (Ongoing s) else unify env n (with_candidate env p x bound) x (Ongoing s)
        | _ => Some (Ongoing s) end) as chk eqn:Echk.
    assert (Hc: forall r, chk = Some (Ongoing r) -> same_states r s).
    { intros r Er. rewrite Echk in Er. destruct vy; try (injection Er as <-; intros q; reflexivity).
      destruct (no_vars bound); [injection Er as <-; intros q; reflexivity|]. exact (Hchk invariant oy x n r eq_refl Er). }
    destruct chk as [[r|]|]; try discriminate H. injection H as <-. pose proof (Hc r eq_refl) as Hr.
    intros q. destruct (Nat.eq_dec p q) as [<-|Hne]; [rewrite !lookup_set_same; reflexivity|].
    rewrite !lookup_set_other by exact Hne. exact (Hr q).
Qed.

(* All of them, in the order of their ranks, as the type parameters of a class are declared: the
   variables a bound mentions are bound exactly when it is checked *)
Lemma capture_arguments_checked: forall n vars ys s s',
    NoDup (map fst vars) -> length ys = length vars ->
    StronglySorted (fun p q => parameter_rank env p < parameter_rank env q) (map fst vars) ->
    (forall y, In y ys -> Q y = true) ->
    (forall p bound, In (p, bound) vars ->
        lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true)
        /\ vars_in (static_vars env p) bound = true) ->
    ranked_states env s ->
    (forall q st, lookup_state s q = Some st -> is_exact st = false -> forall p bound, In (p, bound) vars ->
        parameter_rank env q < parameter_rank env p -> In q (map fst vars)) ->
    fold_unify (fun inner '(t, z) => unify env n t z inner) (combine (map receiver_leaf vars) ys) (Ongoing s) = Some (Ongoing s') ->
    (forall i p bound y, nth_error vars i = Some (p, bound) -> nth_error ys i = Some y ->
        lookup_state s' p = Some (mkVariableState bound y y true true))
    /\ (forall q, ~ In q (map fst vars) -> lookup_state s' q = lookup_state s q).
Proof.
    intros n vars. induction vars as [|[p bound] rest IH]; intros [|y ys] s s' Hnd Hl Hsort Hys Hvars Hrk Hlow H;
        simpl in Hl; try discriminate Hl.
    - simpl in H. injection H as <-. split; [intros [|i]; discriminate|reflexivity].
    - inversion Hnd as [|? ? Hnotin Hnd']. subst. inversion Hsort as [|? ? Hsort' Hhead]. subst.
      rewrite Forall_forall in Hhead.
      simpl in H. destruct (unify env n (receiver_leaf (p, bound)) y (Ongoing s)) as [[s1|]|] eqn:E;
          [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      destruct (Hvars p bound (or_introl eq_refl)) as [Hlp Hbp].
      pose proof (Hys y (or_introl eq_refl)) as Hy. destruct (A_shape y Hy) as [_ [Hny _]].
      (* the bound of p, checked: the variables of a lower rank are bound exactly *)
      assert (Hchk: forall vy oy x k s'', y = TypeArgument vy oy x ->
          unify env k (with_candidate env p x bound) x (Ongoing s) = Some (Ongoing s'') -> same_states s'' s).
      { intros vy oy x k s'' -> Ek. apply (check_same k p x bound s s'' Hrk Hbp); [|clear Ek|exact Ek].
        - exact Hny.
        - intros q st Hq Hr. destruct (is_exact st) eqn:Ex; [reflexivity|].
          pose proof (Hlow q st Hq Ex p bound (or_introl eq_refl) Hr) as Hin. cbn [map fst In] in Hin.
          destruct Hin as [<-|Hin]; [lia|]. pose proof (Hhead q Hin). lia. }
      pose proof (capture_step_checked n p bound s y s1 Hlp Hy Hchk E) as Hs1.
      set (st1 := mkVariableState bound y y true true) in *.
      destruct (IH ys s1 s' Hnd' ltac:(lia) Hsort' (fun y' Hy' => Hys y' (or_intror Hy'))) as [IH1 IH2].
      + intros q bq Hin. destruct (Hvars q bq (or_intror Hin)) as [Hlq Hbq]. split; [|exact Hbq].
        rewrite Hs1, lookup_set_other; [exact Hlq|]. intros ->. apply Hnotin. exact (in_map fst _ _ Hin).
      + intros q st Hq. rewrite Hs1 in Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
        * rewrite lookup_set_same in Hq. injection Hq as <-.
          split; [exact Hny|]. split; [exact Hny|exact Hbp].
        * rewrite lookup_set_other in Hq by exact Hne. exact (Hrk q st Hq).
      + intros q st Hq Ex p' bound' Hin' Hr. rewrite Hs1 in Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
        * rewrite lookup_set_same in Hq. injection Hq as <-. discriminate Ex.
        * rewrite lookup_set_other in Hq by exact Hne.
          destruct (Hlow q st Hq Ex p' bound' (or_intror Hin') Hr) as [<-|Hin]; [contradiction|exact Hin].
      + exact H.
      + split.
        * intros [|i] q bq y' Hq Hy'.
          -- simpl in Hq, Hy'. injection Hq as <- <-. injection Hy' as <-. rewrite (IH2 p Hnotin), Hs1. apply lookup_set_same.
          -- exact (IH1 i q bq y' Hq Hy').
        * intros q Hq. simpl in Hq. rewrite (IH2 q (fun H' => Hq (or_intror H'))), Hs1. apply lookup_set_other.
          intros ->. apply Hq. left. reflexivity.
Qed.

End ClassBounds.

Section ClassReceivers.

Variable env: Environment.
Hypothesis wf: wellformed env.
Hypothesis intersect_no_vars: forall x y, no_vars x = true -> no_vars y = true -> no_vars (intersect env x y) = true.
Hypothesis supertype_no_vars: forall x y, no_vars x = true -> no_vars y = true ->
    no_vars (closest_common_supertype_with env x y) = true.

(* The type arguments of class types are captured so *)
Lemma argument_in_fragment_shape: forall y, argument_in_fragment env y = true -> is_type_argument y = true /\ no_vars y = true
    /\ forall vy oy x k s s', y = TypeArgument vy oy x -> unify env k x bottom_type (Ongoing s) = Some (Ongoing s') -> s' = s.
Proof.
    intros y Hy. split; [exact (argument_in_fragment_is_type_argument env y Hy)|].
    split; [exact (Inference.argument_in_fragment_no_vars env y Hy)|]. intros vy oy x k s s' -> E.
    exact (proj1 (keeps_states_with_arguments env wf k) x bottom_type s s' Hy (bottom_in_fragment env wf) E).
Qed.

(* As receiver_captures, with the bounds of the type parameters of the class mentioning type
   variables: those of the class declared before, as the type parameters of the function are declared
   after them *)
Lemma receiver_captures_ranked:forall n0 mr c cvars ovars ma ca ys s mo sub xs zs n1,
    c <> nothing -> ca <> nothing -> sub <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    StronglySorted (fun p q => parameter_rank env p < parameter_rank env q) (map fst cvars) ->
    (forall p bound q B, In (p, bound) cvars -> In (q, B) ovars -> parameter_rank env p < parameter_rank env q) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> vars_in (static_vars env p) bound = true) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n0 (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing s) ->
    in_fragment env (RootResolved mo sub xs) = true ->
    is_assignable_to env n1 (RootResolved mo sub xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb sub c then xs else parameterized_supertype_arguments env sub xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    exists ys' n2,
        length ys' = length cvars /\ length zs = length cvars
        /\ (forall y, In y ys' -> argument_in_fragment env y = true)
        /\ (forall i p bound y, nth_error cvars i = Some (p, bound) -> nth_error ys' i = Some y ->
            lookup_state s p = Some (mkVariableState bound y y true true))
        /\ (forall p bound, In (p, bound) ovars -> lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false))
        /\ (forall p st, lookup_state s p = Some st -> In p (map fst cvars) \/ exists bound, In (p, bound) ovars)
        /\ Forall2 (fun z y => unify env n2 y z (Ongoing []) = Some (Ongoing [])) zs ys'
        /\ (forall p st, lookup_state s p = Some st -> is_exact st = false ->
            exists bound, In (p, bound) ovars /\ st = mkVariableState bound (initial_upper_bound bound) bottom_type false false).
Proof.
    intros n0 mr c cvars ovars ma ca ys s mo sub xs zs n1 Hc Hca He Hids Hnd Hsort Hfn Hvb Hfy Hrec Hfo Hobj Hzs Hzx.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) (map fst cvars))))
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
    destruct n0 as [|n0]; [discriminate Hrec|].
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
        lookup_state s0 p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true)
        /\ vars_in (static_vars env p) bound = true).
    { intros p bound Hin. split; [|exact (Hvb p bound (in_or_app _ _ _ (or_introl Hin)))].
      unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_introl Hin))), (Hcls p bound Hin). reflexivity. }
    assert (Hrk0: ranked_states env s0).
    { intros q st Hq. unfold s0 in Hq. destruct (lookup_for_inference_in _ _ q st Hq) as [bound Hin].
      rewrite (lookup_for_inference _ _ q bound Hnd' Hin) in Hq. injection Hq as <-.
      cbn [upper_bound lower_bound static_upper_bound]. unfold initial_upper_bound.
      split; [destruct (no_vars bound) eqn:E; [exact E|reflexivity]|]. split; [reflexivity|exact (Hvb q bound Hin)]. }
    assert (Hlow0: forall q st, lookup_state s0 q = Some st -> is_exact st = false -> forall p bound, In (p, bound) cvars ->
        parameter_rank env q < parameter_rank env p -> In q (map fst cvars)).
    { intros q st Hq _ p bound Hin Hr. unfold s0 in Hq. destruct (lookup_for_inference_in _ _ q st Hq) as [B Hinq].
      apply in_app_or in Hinq. destruct Hinq as [Hinq|Hinq]; [exact (in_map fst _ _ Hinq)|].
      pose proof (Hfn p bound q B Hin Hinq). lia. }
    destruct (capture_arguments_checked env wf intersect_no_vars supertype_no_vars (argument_in_fragment env) argument_in_fragment_shape
        n0 cvars ys' s0 s Hndc Hl Hsort Hys Hfresh Hrk0 Hlow0 Hrec) as [Hcap Hoth].
    assert (Hownu: forall p bound, In (p, bound) ovars -> lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false)).
    { intros p bound Hin.
      assert (Hnin: ~ In p (map fst cvars)) by (intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite (Hoth p Hnin). unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_intror Hin))).
      rewrite (Hown p bound Hin). reflexivity. }
    (* the variables: those of c and of the function *)
    assert (Hdomu: forall p st, lookup_state s p = Some st -> In p (map fst cvars) \/ exists bound, In (p, bound) ovars).
    { intros p st Hp. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin]; [left; exact Hin|right].
      rewrite (Hoth p Hnin) in Hp. unfold s0 in Hp. destruct (lookup_for_inference_in _ _ p st Hp) as [bound Hin].
      apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin)|].
      exists bound. exact Hin. }
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
    destruct (unify env n1 (RootResolved ma ca ys) (RootResolved mo sub xs) (Ongoing [])) as [[w|]|] eqn:Eo; try discriminate Hobj.
    pose proof (proj1 (keeps_states_with_arguments env wf n1) _ _ [] w Hfy Hfo Eo) as ->.
    pose proof (proj1 (transitivity_with_arguments env wf (n1 + S k)) _ _ _ n1 (S k) [] (le_n _) Hfo Hfy HfD Eo HD) as ED.
    replace (n1 + S k) with (S (n1 + k)) in ED by lia.
    rewrite unify_classes in ED.
    destruct (base_type_is_subtype_of env sub c) eqn:Hbe; [|discriminate ED].
    match type of ED with context [if Model.is_subtype_of ?x ?y then _ else _] =>
        destruct (Model.is_subtype_of x y); [|discriminate ED] end.
    rewrite (class_eqb_false sub nothing He), <- Hzs in ED.
    assert (Hlz: length zs = length ys').
    { rewrite Hly. subst zs. destruct (Class_eq_dec sub c) as [<-|Hne].
      - rewrite class_eqb_refl. exact (proj1 (root_in_fragment env mo sub xs Hfo)).
      - rewrite (class_eqb_false _ _ Hne). destruct (root_in_fragment env mo sub xs Hfo) as [Hlx Hxs].
        exact (proj1 (supertype_arguments_in_fragment env wf sub c xs Hne He Hbe Hlx Hxs)). }
    pose proof (pairwise_of_arguments env (n1 + k) ys' zs [] ltac:(lia)
        (fun t x0 w0 Ht Ha E => proj2 (keeps_states_with_arguments env wf (n1 + k)) t x0 [] w0 (Hys t Ht) (Hfzs x0 Ha) E) ED) as Hp.
    exists ys', (n1 + k). split; [exact Hl|]. split; [lia|]. split; [exact Hys|]. split; [exact Hcap|]. split; [exact Hownu|].
    split; [exact Hdomu|]. split; [exact Hp|].
    (* the variables not bound exactly: those of the function, as they were *)
    intros p st Hp' Hex. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin].
    - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
      destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
      rewrite (Hcap i p bound y Hi Hy) in Hp'. injection Hp' as <-. discriminate Hex.
    - pose proof Hp' as Hp2. rewrite (Hoth p Hnin) in Hp2. unfold s0 in Hp2. destruct (lookup_for_inference_in _ _ p st Hp2) as [bound Hin].
      apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin)|].
      exists bound. split; [exact Hin|]. rewrite (Hownu p bound Hin) in Hp'. injection Hp' as <-. reflexivity.
Qed.

End ClassReceivers.
