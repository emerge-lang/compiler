From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import MemberAccess.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import FinalValues.
From EmergeTypeSystem Require Import SubstitutionTerminating.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Substitution with intersections in type arguments                                              *)
(*                                                                                                *)
(* The substitution lemma of Substitution.v, for types whose type arguments may be intersections, *)
(* too (`Box<A & T>`, the wide fragment wtfrag). Instantiated, those are types of the fragment of *)
(* Fragment.v without type parameters (ground), but no longer of the fragment of Transitivity.v,  *)
(* whose transitivity Substitution.v relies on. So this takes transitivity from Generics.v and    *)
(* Conjectures.v: where unify terminates (unify_terminates, which rests on inheritance not being  *)
(* expansive, as findExpansiveSupertypes in compiler/binding/basetype/ExpansiveInheritance.kt     *)
(* makes sure), unify is transitive on them (transitivity_terminating), and what it never         *)
(* rejects, it accepts (accepts). The proof is the induction of Substitution.v once more, in the  *)
(* form of some fuel being enough (wide_main), with intersections as targets and as assignees in  *)
(* every position: an intersection takes what each of its components takes, of the mutability     *)
(* common to them; one is taken where one of its components is.                                   *)
(* ---------------------------------------------------------------------------------------------- *)

Section Ground.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.

(* No references to type parameters, type variables or erroneous types in it *)
Fixpoint no_refs (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb no_refs arguments
    | Nullable n | TypeArgument _ _ n => no_refs n
    | Intersection components => forallb no_refs components
    | _ => false
    end.

(* What instantiating types gives: the types of Fragment.v without type parameters *)
Definition ground (t: EType): bool := gfrag env t && no_refs t.

Lemma ground_gfrag: forall t, ground t = true -> gfrag env t = true.
Proof. intros t H. apply andb_true_iff in H. apply H. Qed.

Lemma ground_no_vars: forall t, ground t = true -> no_vars t = true.
Proof. intros t H. exact (gfrag_no_vars env t (ground_gfrag t H)). Qed.

Lemma no_refs_refs_wf: forall t, no_refs t = true -> refs_wf env declared t.
Proof. intros. exact I. Qed.

Lemma ground_of_fragment: forall t, ground t = true -> gfrag env t = true /\ refs_wf env declared t.
Proof. intros t H. apply andb_true_iff in H. destruct H as [Hg Hn]. exact (conj Hg (no_refs_refs_wf t Hn)). Qed.

Lemma in_fragment_no_refs: forall k,
    (forall t, depth t <= k -> in_fragment env t = true -> no_refs t = true)
    /\ (forall a, argument_depth a <= k -> argument_in_fragment env a = true -> no_refs a = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split; [intros [m c args|[m c args| | | | | |]| | | | |] Hd H|intros [| | | |v o n| |] Hd H]; simpl in Hd, H;
          try discriminate H; lia. }
    assert (Hroot: forall m c args, depth (RootResolved m c args) <= S k -> in_fragment env (RootResolved m c args) = true ->
        no_refs (RootResolved m c args) = true).
    { intros m c args Hd H. destruct (root_in_fragment env m c args H) as [_ Ha].
      change (forallb no_refs args = true). apply forallb_forall.
      intros a Hin. pose proof (argument_depth_below m c args a Hin). apply IHa; [lia|apply Ha, Hin]. }
    split.
    - intros t Hd H. destruct (fragment_cases env t H) as [[m [c [args ->]]]|[m [c [args [-> H1]]]]].
      + exact (Hroot m c args Hd H).
      + rewrite depth_nullable in Hd. exact (Hroot m c args ltac:(lia) H1).
    - intros [| | | |v o n| |] Hd H; simpl in H; try discriminate H. simpl in Hd |- *. apply IHt; [lia|exact H].
Qed.

Lemma in_fragment_ground: forall t, in_fragment env t = true -> ground t = true.
Proof.
    intros t H. unfold ground. rewrite (in_fragment_is_gfrag env t H).
    rewrite (proj1 (in_fragment_no_refs (depth t)) t (le_n _) H). reflexivity.
Qed.

(* A class type, nullable or not, an intersection of class types, nullable or not *)
Lemma ground_cases: forall t, ground t = true ->
    (exists m c args, t = RootResolved m c args)
    \/ (exists m c args, t = Nullable (RootResolved m c args))
    \/ (exists ys, t = Intersection ys /\ ys <> [] /\ forall y, In y ys -> is_class y = true /\ ground y = true)
    \/ (exists ys, t = Nullable (Intersection ys) /\ ys <> [] /\ forall y, In y ys -> is_class y = true /\ ground y = true).
Proof.
    assert (Hinter: forall ys, ground (Intersection ys) = true ->
        ys <> [] /\ forall y, In y ys -> is_class y = true /\ ground y = true).
    { intros ys H. unfold ground in H. apply andb_true_iff in H. destruct H as [Hg Hn].
      destruct (intersection_gfrag env ys Hg) as [Hne Hc]. split; [exact Hne|].
      intros y Hy. destruct (Hc y Hy) as [Hcomp Hgy]. simpl in Hn. rewrite forallb_forall in Hn. pose proof (Hn y Hy) as Hny.
      destruct y as [| |g| | | |]; simpl in Hcomp; try discriminate Hcomp; try discriminate Hny.
      split; [reflexivity|unfold ground; apply andb_true_iff; split; [exact Hgy|exact Hny]]. }
    intros t H. pose proof H as H'. unfold ground in H'. apply andb_true_iff in H'. destruct H' as [Hg Hn].
    destruct t as [m c args|[m c args|n|g|me msg|v o n|g|ys]|g|me msg|v o n|g|ys]; simpl in Hg, Hn; try discriminate Hg;
        try discriminate Hn.
    - left. eauto.
    - right. left. eauto.
    - right. right. right. exists ys. split; [reflexivity|]. apply Hinter.
      unfold ground in H |- *. apply andb_true_iff in H. destruct H as [H1 H2].
      change (non_null env (Intersection ys) && gfrag env (Intersection ys) = true) in H1.
      apply andb_true_iff in H1. apply andb_true_iff. split; [exact (proj2 H1)|exact H2].
    - right. right. left. exists ys. split; [reflexivity|]. exact (Hinter ys H).
Qed.

Lemma ground_nullable_inner: forall n, ground (Nullable n) = true -> ground n = true.
Proof.
    intros n H. unfold ground in *. apply andb_true_iff in H. destruct H as [Hg Hn]. simpl in Hg, Hn.
    apply andb_true_iff in Hg. rewrite (proj2 Hg), Hn. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify on ground types                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* A nullable target takes what the type in it takes without null *)
Lemma ground_nullable_target: forall f T y s, ground y = true ->
    unify env (S f) (Nullable T) y (Ongoing s) = unify env f T (without_null env y) (Ongoing s).
Proof.
    intros f T y s Hy.
    destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; reflexivity.
Qed.

Lemma ground_rewrap: forall X, ground X = true -> rewrap_nullable X = Nullable (without_null env X).
Proof.
    intros X HX. destruct (ground_cases X HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; reflexivity.
Qed.

Lemma ground_without_null_idempotent: forall X, ground X = true -> without_null env (without_null env X) = without_null env X.
Proof.
    intros X HX. destruct (ground_cases X HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; reflexivity.
Qed.

Lemma ground_without_null: forall X, ground X = true -> ground (without_null env X) = true.
Proof.
    intros X HX. destruct (ground_cases X HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
        first [exact HX|exact (ground_nullable_inner _ HX)].
Qed.

Lemma ground_non_null_without_null: forall X, ground X = true -> is_nullable env X = false -> without_null env X = X.
Proof.
    intros X HX Hn. destruct (ground_cases X HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
        first [reflexivity|discriminate Hn].
Qed.

Lemma ground_keeps: forall f D y s r, ground D = true -> ground y = true ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> r = s.
Proof.
    intros f D y s r HD Hy H. pose proof (unify_free env wf f D y s s _ (ground_no_vars D HD) (ground_no_vars y Hy) H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

(* A non-null target takes no nullable value *)
Lemma ground_non_null: forall f D y s r, ground D = true -> ground y = true -> is_nullable env D = false ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> is_nullable env y = false.
Proof.
    intros [|f] D y s r HD Hy Hn H; [discriminate H|].
    destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try reflexivity;
    destruct (ground_cases D HD) as [[md [cd [dargs ->]]]|[[md [cd [dargs ->]]]|[[ds [-> _]]|[ds [-> _]]]]];
        try discriminate Hn; simpl in H; discriminate H.
Qed.

(* Without null on both sides, what is taken stays taken *)
Lemma ground_unify_without_null: forall f D y s r, ground D = true -> ground y = true ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> unify env f (without_null env D) (without_null env y) (Ongoing s) = Some (Ongoing r).
Proof.
    intros f D y s r HD Hy H.
    destruct (is_nullable env D) eqn:En.
    - destruct f as [|f]; [discriminate H|].
      destruct (ground_cases D HD) as [[md [cd [dargs ->]]]|[[md [cd [dargs ->]]]|[[ds [-> _]]|[ds [-> _]]]]].
      + discriminate En.
      + rewrite ground_nullable_target in H by exact Hy. apply (unify_fuel_monotone env f); [lia|exact H].
      + discriminate En.
      + rewrite ground_nullable_target in H by exact Hy. apply (unify_fuel_monotone env f); [lia|exact H].
    - rewrite (ground_non_null_without_null D HD En), (ground_non_null_without_null y Hy (ground_non_null f D y s r HD Hy En H)).
      exact H.
Qed.

(* What a target takes is of no more mutability than it *)
Lemma ground_mutability: forall f D y s r, ground D = true -> ground y = true ->
    unify env f D y (Ongoing s) = Some (Ongoing r) -> Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env D) = true.
Proof.
    induction f as [|f IH]; intros D y s r HD Hy H; [discriminate H|].
    destruct (ground_cases D HD) as [[md [cd [dargs ->]]]|[[md [cd [dargs ->]]]|[[ds [-> [Hne Hds]]]|[ds [-> [Hne Hds]]]]]].
    - destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> [_ Hys]]]|[ys [-> _]]]]].
      + rewrite unify_classes in H. destruct (base_type_is_subtype_of env c cd); [|discriminate H].
        destruct (Model.is_subtype_of _ _) eqn:Em; [reflexivity|discriminate H].
      + discriminate H.
      + destruct (intersection_flipped_unify_found env f _ ys s r H) as [c [Hc Hu]].
        eapply mutability_subtype_trans; [apply intersection_assignment_mutability_below_component, Hc|].
        exact (IH _ c s r HD (proj2 (Hys c Hc)) Hu).
      + discriminate H.
    - rewrite ground_nullable_target in H by exact Hy. change (assignment_mutability env (Nullable (RootResolved md cd dargs)))
          with (assignment_mutability env (RootResolved md cd dargs)).
      rewrite <- (without_null_keeps_assignment_mutability env ranked y).
      exact (IH _ _ s r (ground_nullable_inner _ HD) (ground_without_null y Hy) H).
    - destruct (is_nullable env y) eqn:Eny.
      { destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
            try discriminate Eny; simpl in H; discriminate H. }
      assert (Hshape: match y with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end)
          by (destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
              first [exact I|discriminate Eny]).
      assert (Hnv: forall c, In c ds -> is_type_variable c = false)
          by (intros c Hc; pose proof (proj1 (Hds c Hc)) as Hcl; destruct c; first [reflexivity|discriminate Hcl]).
      destruct (intersection_target env f ds y s r Hnv Hne Hshape (fun c u Hc E => ground_keeps f c y s u (proj2 (Hds c Hc)) Hy E) H) as [_ Hall].
      rewrite (intersection_assignment_mutability env). apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
      intros mc Hmc. apply in_map_iff in Hmc. destruct Hmc as [c [<- Hc]].
      exact (IH c y s s (proj2 (Hds c Hc)) Hy (Hall c Hc)).
    - rewrite ground_nullable_target in H by exact Hy. change (assignment_mutability env (Nullable (Intersection ds)))
          with (assignment_mutability env (Intersection ds)).
      rewrite <- (without_null_keeps_assignment_mutability env ranked y).
      exact (IH _ _ s r (ground_nullable_inner _ HD) (ground_without_null y Hy) H).
Qed.

End Ground.

Section Wide.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable b: Bindings.
Variable K: nat.
Hypothesis Hbf: bindings_in_fragment env b.

(* The types instantiated: those of sfrag, the type arguments of which may be intersections, too *)
Fixpoint wfrag (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        if class_eqb c nothing then is_bottom m arguments else
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with
            | TypeArgument _ _ n =>
                match n with
                | Intersection cs | Nullable (Intersection cs) =>
                    Nat.leb 2 (length cs) && forallb (fun c => is_component_shape env c && wfrag c) cs
                | _ => wfrag n
                end
            | _ => false
            end) arguments
    | Nullable n => (is_class n || is_generic n) && wfrag n
    | Generic _ => sfrag env t
    | _ => false
    end.

Definition wcomponents (cs: list EType): bool := Nat.leb 2 (length cs) && forallb (fun c => is_component_shape env c && wfrag c) cs.

Definition wtfrag (t: EType): bool :=
    match t with
    | Intersection cs | Nullable (Intersection cs) => wcomponents cs
    | _ => wfrag t
    end.

Definition argument_wfrag (a: EType): bool := match a with TypeArgument _ _ n => wtfrag n | _ => false end.

Lemma wfrag_cases: forall t, wfrag t = true ->
    (exists m c args, t = RootResolved m c args /\ class_eqb c nothing = false
        /\ length args = length (parameter_ids env c) /\ forall a, In a args -> argument_wfrag a = true)
    \/ t = bottom_type
    \/ (exists m c args, t = Nullable (RootResolved m c args) /\ wfrag (RootResolved m c args) = true)
    \/ (exists g, t = Generic g /\ generic_sfrag env g)
    \/ (exists g, t = Nullable (Generic g) /\ generic_sfrag env g).
Proof.
    assert (Hg: forall g, wfrag (Generic g) = true -> generic_sfrag env g).
    { intros g H. change (sfrag env (Generic g) = true) in H. apply (sfrag_generic_iff env wf) in H. exact H. }
    intros [m c args|[m c args| |g| | | |]| g | | | |] H; try discriminate H.
    - cbn [wfrag] in H. destruct (class_eqb c nothing) eqn:Hc.
      + right. left. apply class_eqb_true in Hc. subst c.
        destruct m as [[]|], args; simpl in H; try discriminate H. reflexivity.
      + left. apply andb_true_iff in H. destruct H as [Hl Ha]. exists m, c, args.
        split; [reflexivity|]. split; [exact Hc|]. split; [apply Nat.eqb_eq, Hl|].
        intros a Hin. rewrite forallb_forall in Ha. pose proof (Ha a Hin) as Ha'.
        destruct a as [| | | |v o n| |]; try discriminate Ha'. exact Ha'.
    - right. right. left. exists m, c, args. split; [reflexivity|]. simpl in H. exact H.
    - right. right. right. right. exists g. split; [reflexivity|]. apply Hg. simpl in H. exact H.
    - right. right. right. left. exists g. split; [reflexivity|]. exact (Hg g H).
Qed.

Lemma wtfrag_cases: forall t, wtfrag t = true ->
    wfrag t = true
    \/ (exists cs, t = Intersection cs /\ wcomponents cs = true)
    \/ (exists cs, t = Nullable (Intersection cs) /\ wcomponents cs = true).
Proof.
    intros t H. destruct t as [m c args|[m c args|n|g|me msg|v o n|g|cs]|g|me msg|v o n|g|cs];
        try (left; exact H).
    - right. right. exists cs. split; [reflexivity|exact H].
    - right. left. exists cs. split; [reflexivity|exact H].
Qed.

Lemma wcomponents_facts: forall cs, wcomponents cs = true ->
    2 <= length cs /\ forall c, In c cs -> is_component_shape env c = true /\ wfrag c = true.
Proof.
    intros cs H. unfold wcomponents in H. apply andb_true_iff in H. destruct H as [Hl H].
    split; [apply Nat.leb_le, Hl|]. intros c Hc. rewrite forallb_forall in H. apply andb_true_iff, H, Hc.
Qed.

Lemma wfrag_wtfrag: forall t, wfrag t = true -> wtfrag t = true.
Proof. intros [| [] | | | | |] H; try exact H; discriminate H. Qed.

Lemma sfrag_wfrag: forall t, sfrag env t = true -> wfrag t = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct (sfrag_cases env wf t H) as [[m [c [args [-> [Hc [Hl Hargs]]]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> _]]|[g [-> _]]]]]].
    - simpl. rewrite Hc, Hl, Nat.eqb_refl. apply forallb_forall. intros a Hin. pose proof (Hargs a Hin) as Ha.
      destruct a as [| | | |v o n| |]; try discriminate Ha. simpl in Ha.
      pose proof (esize_in args _ Hin) as Hs. simpl in Hs.
      assert (Hn: wfrag n = true) by (apply (IH (esize n)); [simpl; lia|reflexivity|exact Ha]).
      destruct (sfrag_cases env wf n Ha) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[[? [-> _]]|[? [-> _]]]]]]; exact Hn.
    - reflexivity.
    - change ((is_class (RootResolved m c args) || is_generic (RootResolved m c args)) && wfrag (RootResolved m c args) = true).
      simpl (is_class _ || is_generic _). apply (IH (esize (RootResolved m c args))); [simpl; lia|reflexivity|exact Ht'].
    - exact H.
    - exact H.
Qed.

Lemma tfrag_wtfrag: forall t, tfrag env t = true -> wtfrag t = true.
Proof.
    intros t H. destruct (tfrag_cases env t H) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - exact (wfrag_wtfrag t (sfrag_wfrag t Hs)).
    - destruct (components_sfrag_facts env cs Hcs) as [Hl Hc]. unfold wtfrag, wcomponents.
      rewrite (proj2 (Nat.leb_le _ _) Hl). apply forallb_forall. intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      rewrite Hsh, (sfrag_wfrag c Hs). reflexivity.
    - destruct (components_sfrag_facts env cs Hcs) as [Hl Hc]. unfold wtfrag, wcomponents.
      rewrite (proj2 (Nat.leb_le _ _) Hl). apply forallb_forall. intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      rewrite Hsh, (sfrag_wfrag c Hs). reflexivity.
Qed.

End Wide.

Section WideInstances.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable b: Bindings.
Variable K: nat.
Hypothesis Hbf: bindings_in_fragment env b.

Lemma of_class_types: forall ys, 2 <= length ys -> (forall y, In y ys -> is_class y = true) ->
    of_components env (flat_map intersected_components ys) = Intersection (map (with_mutability env (common_mutability env ys)) ys).
Proof.
    intros ys Hl H. rewrite (flat_map_classes ys H). rewrite (of_components_many env ys Hl).
    - f_equal. apply map_ext_in. intros y Hy. pose proof (H y Hy) as Hc. destruct y; try discriminate Hc. reflexivity.
    - destruct ys as [|y1 ys']; [simpl in Hl; lia|]. pose proof (H y1 (or_introl eq_refl)) as Hc.
      destruct y1; try discriminate Hc. reflexivity.
Qed.

Lemma ground_with_mutability: forall k y, is_class y = true -> ground env y = true ->
    ground env (with_mutability env k y) = true /\ is_class (with_mutability env k y) = true.
Proof. intros k [m c args| | | | | |] Hc Hy; try discriminate Hc. split; [exact Hy|reflexivity]. Qed.

(* Instantiated, a type of the wide fragment is ground, and mentions no type parameter bound loosely *)
Lemma wide_instance: forall t, wtfrag env t = true -> bound_in env b K [] t = true ->
    ground env (instantiate env b t) = true
    /\ mentions_loosely_bound b t = false /\ mentions_loosely_bound_in_arguments b t = false
    /\ nests_argument (instantiate env b t) = false
    /\ (is_nullable env t = false -> is_nullable env (instantiate env b t) = false)
    /\ (is_component_shape env t = true -> is_class (instantiate env b t) = true).
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Ht Hb.
    (* a class type *)
    assert (Hroot: forall m c args, esize (RootResolved m c args) <= esize t -> wfrag env (RootResolved m c args) = true ->
        bound_in env b K [] (RootResolved m c args) = true ->
        ground env (RootResolved m c (map (instantiate env b) args)) = true /\ existsb (mentions_loosely_bound b) args = false).
    { intros m c args Hd Hf Hb'.
      destruct (wfrag_cases env wf (RootResolved m c args) Hf)
          as [[m' [c' [args' [Heq [_ [Hl Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
          try discriminate Heq.
      - injection Heq as <- <- <-.
        assert (Hall: forall a, In a args -> argument_gfrag env (instantiate env b a) = true
            /\ no_refs (instantiate env b a) = true /\ mentions_loosely_bound b a = false).
        { intros a Hin. pose proof (Hargs a Hin) as Ha. pose proof (bound_in_root env b K [] m c args Hb' a Hin) as Hba.
          pose proof (esize_in args a Hin) as Hs.
          destruct a as [| | | |v o n| |]; try discriminate Ha. simpl in Ha, Hs.
          destruct (bound_in_argument env b K [] v o n Hba) as [_ Hbn].
          destruct (IH (esize n) ltac:(simpl in Hd; lia) n eq_refl Ha Hbn) as [Hg [Hm [Hmi [Hnest _]]]].
          rewrite (instantiate_argument_plain env b v o n _ eq_refl Hmi Hnest).
          unfold ground in Hg. apply andb_true_iff in Hg. destruct Hg as [Hg Hn].
          split; [exact Hg|split; [exact Hn|exact Hm]]. }
        split.
        + unfold ground. apply andb_true_iff. split.
          * change (Nat.eqb (length (map (instantiate env b) args)) (length (parameter_ids env c))
                && forallb (argument_gfrag env) (map (instantiate env b) args) = true).
            rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
            destruct Ha' as [a [<- Hin]]. apply (Hall a Hin).
          * change (forallb no_refs (map (instantiate env b) args) = true). apply forallb_forall. intros a' Ha'.
            apply in_map_iff in Ha'. destruct Ha' as [a [<- Hin]]. apply (Hall a Hin).
        + apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [a [Hin E]].
          rewrite (proj2 (proj2 (Hall a Hin))) in E. discriminate E.
      - unfold bottom_type in Heq. injection Heq as -> -> ->. split; [|reflexivity].
        unfold ground. simpl. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
    (* a reference to a type parameter *)
    assert (Hgen: forall g, generic_sfrag env g -> bound_in env b K [] (Generic g) = true ->
        in_fragment env (instantiate env b (Generic g)) = true /\ mentions_loosely_bound b (Generic g) = false
        /\ (is_nullable env (Generic g) = false -> is_nullable env (instantiate env b (Generic g)) = false)
        /\ nests_argument (instantiate env b (Generic g)) = false).
    { intros g Hg Hb'. destruct (binds_ref_some env wf b K [] g Hb') as [o [x [E [Ho [Hx _]]]]].
      destruct (instantiate_exact_generic env b g o x E Ho Hx) as [Hi Hm].
      pose proof (sfrag_tfrag env _ (generic_sfrag_sfrag env wf g Hg)) as Htf.
      pose proof (proj2 (proj2 (instance_facts env wf b K [] Hbf _ (Generic g) (le_n _) Htf Hb'))) as Hn.
      rewrite (inst_nested_instantiate env wf b K [] (Generic g) Htf Hb') in Hn.
      rewrite Hi in Hn |- *. split; [exact (inst_ref_in_fragment env g x (Hbf _ o x E))|].
      split; [exact Hm|split; [exact Hn|exact (gfrag_inst_ref_flat env g x Hx)]]. }
    destruct (wtfrag_cases env t Ht) as [Hw|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (wfrag_cases env wf t Hw) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + rewrite instantiate_class. destruct (Hroot m c args (le_n _) Hw Hb) as [Hg Hm].
        split; [exact Hg|]. change (mentions_loosely_bound b (RootResolved m c args)) with (existsb (mentions_loosely_bound b) args).
        change (mentions_loosely_bound_in_arguments b (RootResolved m c args)) with (existsb (mentions_loosely_bound b) args).
        rewrite Hm. repeat split; reflexivity.
      + unfold bottom_type in *. rewrite instantiate_class. destruct (Hroot _ _ _ (le_n _) Hw Hb) as [Hg Hm].
        split; [exact Hg|]. repeat split; reflexivity.
      + rewrite instantiate_nullable_class. destruct (Hroot m c args ltac:(simpl; lia) Ht' Hb) as [Hg Hm].
        split; [exact Hg|]. change (mentions_loosely_bound b (Nullable (RootResolved m c args))) with (existsb (mentions_loosely_bound b) args).
        change (mentions_loosely_bound_in_arguments b (Nullable (RootResolved m c args))) with (existsb (mentions_loosely_bound b) args).
        rewrite Hm. repeat split; try reflexivity; intros H0; discriminate H0.
      + destruct (Hgen g Hg Hb) as [Hf [Hm [Hn Hnest]]]. split; [exact (in_fragment_ground env _ Hf)|].
        split; [exact Hm|]. split; [reflexivity|]. split; [exact Hnest|]. split; [exact Hn|].
        intros Hsh. pose proof (Hn (component_non_null env _ Hsh)) as Hn'.
        destruct (fragment_cases env _ Hf) as [[m [c [args E]]]|[m [c [args [E _]]]]]; rewrite E in Hn' |- *;
            [reflexivity|discriminate Hn'].
      + destruct (Hgen g Hg Hb) as [Hf [Hm _]].
        change (instantiate env b (Nullable (Generic g))) with (rewrap_nullable (instantiate env b (Generic g))).
        pose proof (in_fragment_rewrap env _ Hf) as Hf'.
        split; [exact (in_fragment_ground env _ Hf')|]. split; [exact Hm|]. split; [reflexivity|].
        split; [exact (fragment_not_nesting env _ Hf')|]. split; intros H0; discriminate H0.
    - (* an intersection *)
      destruct (wcomponents_facts env cs Hcs) as [Hl Hc].
      assert (Hall: forall c, In c cs -> ground env (instantiate env b c) = true /\ is_class (instantiate env b c) = true
          /\ mentions_loosely_bound b c = false /\ mentions_loosely_bound_in_arguments b c = false).
      { intros c Hin. destruct (Hc c Hin) as [Hsh Hwc]. pose proof (esize_in cs c Hin) as Hs.
        destruct (IH (esize c) ltac:(simpl; lia) c eq_refl (wfrag_wtfrag env c Hwc) (bound_in_component env b K [] cs c Hb Hin))
            as [Hg [Hm [Hmi [_ [_ Hcl]]]]].
        exact (conj Hg (conj (Hcl Hsh) (conj Hm Hmi))). }
      assert (Hys: forall y, In y (map (instantiate env b) cs) -> is_class y = true).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]]. apply (Hall c Hin). }
      change (instantiate env b (Intersection cs)) with (of_components env (flat_map intersected_components (map (instantiate env b) cs))).
      rewrite (of_class_types _ ltac:(rewrite length_map; exact Hl) Hys).
      split; [|split; [|split; [|split; [reflexivity|split; [reflexivity|intros H0; discriminate H0]]]]].
      + unfold ground. apply andb_true_iff. split.
        * simpl. apply andb_true_iff. split; [destruct cs as [|c1 cs']; simpl in Hl |- *; [lia|reflexivity]|].
          apply forallb_forall. intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']].
          apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]]. destruct (Hall c Hin) as [Hg [Hcl _]].
          destruct (ground_with_mutability (common_mutability env (map (instantiate env b) cs)) _ Hcl Hg) as [Hg' Hcl'].
          destruct (instantiate env b c) as [| | | | | |]; try discriminate Hcl. apply andb_true_iff. split; [reflexivity|].
          apply (ground_gfrag env), Hg'.
        * change (forallb no_refs (map (with_mutability env (common_mutability env (map (instantiate env b) cs)))
              (map (instantiate env b) cs)) = true).
          apply forallb_forall. intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']].
          apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]]. destruct (Hall c Hin) as [Hg [Hcl _]].
          destruct (ground_with_mutability (common_mutability env (map (instantiate env b) cs)) _ Hcl Hg) as [Hg' _].
          unfold ground in Hg'. apply andb_true_iff in Hg'. apply Hg'.
      + change (existsb (mentions_loosely_bound b) cs = false). apply not_true_iff_false. intros E.
        apply existsb_exists in E. destruct E as [c [Hin E]]. rewrite (proj1 (proj2 (proj2 (Hall c Hin)))) in E. discriminate E.
      + change (existsb (mentions_loosely_bound_in_arguments b) cs = false). apply not_true_iff_false. intros E.
        apply existsb_exists in E. destruct E as [c [Hin E]]. rewrite (proj2 (proj2 (proj2 (Hall c Hin)))) in E. discriminate E.
    - (* a nullable intersection *)
      destruct (IH (esize (Intersection cs)) ltac:(simpl; lia) (Intersection cs) eq_refl Hcs Hb)
          as [Hg [Hm [Hmi [_ [Hn _]]]]].
      change (instantiate env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate env b (Intersection cs))).
      pose proof (Hn eq_refl) as Hn'.
      destruct (ground_cases env _ Hg) as [[m [c [args E]]]|[[m [c [args E]]]|[[ys [E _]]|[ys [E _]]]]];
          rewrite E in Hg, Hn' |- *; try discriminate Hn'; cbn [rewrap_nullable].
      + split; [exact Hg|]. split; [exact Hm|]. split; [exact Hmi|]. split; [reflexivity|]. split; intros H0; discriminate H0.
      + split; [exact Hg|]. split; [exact Hm|]. split; [exact Hmi|]. split; [reflexivity|]. split; intros H0; discriminate H0.
Qed.

(* A type argument of the wide fragment, instantiated *)
Lemma wide_argument: forall a, argument_wfrag env a = true -> bound_in env b K [] a = true ->
    exists v o n, a = TypeArgument v o n /\ instantiate env b a = TypeArgument v (instantiate_ownership b o) (instantiate env b n)
        /\ wtfrag env n = true /\ bound_in env b K [] n = true /\ ownership_bound b o = true
        /\ argument_gfrag env (instantiate env b a) = true /\ no_refs (instantiate env b a) = true
        /\ is_loose (instantiate env b a) = is_loose a /\ mentions_loosely_bound b a = false.
Proof.
    intros [| | | |v o n| |] Ha Hb; try discriminate Ha. exists v, o, n. simpl in Ha.
    destruct (bound_in_argument env b K [] v o n Hb) as [Ho Hbn].
    destruct (wide_instance n Ha Hbn) as [Hg [Hm [Hmi [Hnest _]]]].
    pose proof (instantiate_argument_plain env b v o n _ eq_refl Hmi Hnest) as Hi.
    rewrite Hi. unfold ground in Hg. apply andb_true_iff in Hg. destruct Hg as [Hg Hn].
    repeat split; try assumption.
    simpl. destruct o as [| | |q]; try reflexivity. simpl in Ho |- *.
    destruct (lookup_binding b q) as [[| | | |v' o' x| |]|]; try discriminate Ho. destruct v'; try discriminate Ho.
    destruct o'; try discriminate Ho; reflexivity.
Qed.

End WideInstances.

Section WideTemplates.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Let supertypes_mention_nothing_as_bottom := wf_supertypes_mention_nothing_as_bottom env wf.
Variable b: Bindings.
Variable K: nat.
Hypothesis Hbf: bindings_in_fragment env b.

Section Templates.

Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> argument_wfrag env y = true /\ bound_in env b K [] y = true.

Let bS := bindings_of env sub ys.
Let bL := bindings_of env sub (map (instantiate env b) ys).

Lemma wide_ys_type_argument: forall y, In y ys -> is_type_argument y = true.
Proof.
    intros y Hy. destruct (Hys y Hy) as [Ha _]. destruct y as [| | | |v o n| |]; try discriminate Ha. reflexivity.
Qed.

Lemma wide_template_instances: forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> nothing_is_bottom t = true ->
        wfrag env (instantiate env bS t) = true /\ bound_in env b K [] (instantiate env bS t) = true)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> nothing_is_bottom r = true ->
        argument_wfrag env (instantiate env bS r) = true /\ bound_in env b K [] (instantiate env bS r) = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht _; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true -> nothing_is_bottom (RootResolved m c targs) = true ->
        wfrag env (RootResolved m c (map (instantiate env bS) targs)) = true
        /\ bound_in env b K [] (RootResolved m c (map (instantiate env bS) targs)) = true).
    { intros m c targs Hd Ht Hn. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      destruct (nothing_is_bottom_root m c targs Hn) as [Hc Hnargs].
      assert (Hall: forall a, In a targs -> argument_wfrag env (instantiate env bS a) = true
          /\ bound_in env b K [] (instantiate env bS a) = true).
      { intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha|apply Hnargs, Ha]. }
      split.
      - cbn [wfrag]. destruct (class_eqb c nothing) eqn:Ec.
        + specialize (Hc eq_refl). destruct m as [[]|], targs; simpl in Hc; try discriminate Hc. reflexivity.
        + rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
          destruct Ha' as [a [<- Ha]]. pose proof (proj1 (Hall a Ha)) as Hw.
          destruct (instantiate env bS a) as [| | | |v o n| |]; try discriminate Hw. exact Hw.
      - change (forallb (bound_in env b K []) (map (instantiate env bS) targs) = true). apply forallb_forall.
        intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. apply Hall, Ha. }
    split.
    - intros t Hd Ht Hn. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite instantiate_class. exact (Hroot m c targs Hd Ht Hn).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class.
        destruct (Hroot m c targs ltac:(lia) Ht' Hn) as [Hf Hb]. split; [|exact Hb].
        change ((is_class (RootResolved m c (map (instantiate env bS) targs)) || is_generic (RootResolved m c (map (instantiate env bS) targs)))
            && wfrag env (RootResolved m c (map (instantiate env bS) targs)) = true). rewrite Hf. reflexivity.
    - intros r Hd Hr Hn. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        unfold bS. rewrite (selects env wf sub ys p bp i y Hi Hy (wide_ys_type_argument y (nth_error_In _ _ Hy))).
        apply Hys. eapply nth_error_In. exact Hy.
      + simpl in Hd, Hn. destruct (IHt n ltac:(lia) Hn' Hn) as [Hf Hb].
        pose proof (wfrag_wtfrag env _ Hf) as Hf'.
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        assert (Hob: ownership_bound b o = true) by (destruct o; first [reflexivity|discriminate Ho]).
        destruct (mentions_loosely_bound bS n); [destruct v|]; cbn [argument_wfrag bound_in];
            rewrite ?Hob, ?Hf', ?Hb; split; reflexivity.
Qed.

Lemma wide_template_looseness: forall k,
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
        destruct (Hys y (nth_error_In _ _ Hy)) as [Ha Hb].
        destruct (wide_argument env wf b K Hbf y Ha Hb) as [v [o [n [_ [_ [_ [_ [_ [_ [_ [Hl _]]]]]]]]]]]. exact Hl.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn'].
Qed.

Lemma wide_template_commutes: forall k,
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
        destruct (wide_argument env wf b K Hbf y Ha Hb) as [vy [oy [ny [_ [Ei _]]]]].
        unfold bS, bL. rewrite (selects env wf sub ys p bp i y Hi Hy (wide_ys_type_argument y (nth_error_In _ _ Hy))).
        rewrite (selects env wf sub _ p bp i _ Hi Hy'); [reflexivity|]. rewrite Ei. reflexivity.
      + simpl in Hd, Hn.
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        rewrite (instantiate_template_argument env bL v o n Ho (template_shape env sub n Hn')).
        rewrite (proj1 (wide_template_looseness (depth n)) n (le_n _) Hn').
        destruct (proj1 (wide_template_instances (depth n)) n (le_n _) Hn' Hn) as [Hf Hb].
        assert (Hio: instantiate_ownership b o = o) by (destruct o; first [reflexivity|discriminate Ho]).
        assert (Hob: ownership_bound b o = true) by (destruct o; first [reflexivity|discriminate Ho]).
        assert (Hinst: forall w, instantiate env b (TypeArgument w o (instantiate env bS n))
            = TypeArgument w o (instantiate env b (instantiate env bS n))).
        { intros w. assert (Ha: argument_wfrag env (TypeArgument w o (instantiate env bS n)) = true) by exact (wfrag_wtfrag env _ Hf).
          assert (Hba: bound_in env b K [] (TypeArgument w o (instantiate env bS n)) = true)
              by (cbn [bound_in]; rewrite Hob, Hb; reflexivity).
          destruct (wide_argument env wf b K Hbf _ Ha Hba) as [w' [o' [n' [E [Ei _]]]]].
          injection E as <- <- <-. rewrite Ei, Hio. reflexivity. }
        destruct (mentions_loosely_bound bS n); [destruct v; cbn beta iota|];
            first [ rewrite Hinst, (IHt n ltac:(lia) Hn' Hn); reflexivity
                  | cbn [instantiate]; rewrite Hio; reflexivity ].
Qed.

End Templates.

Lemma wide_supertype_arguments_commute: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) ->
    (forall y, In y ys -> argument_wfrag env y = true /\ bound_in env b K [] y = true) ->
    parameterized_supertype_arguments env sub (map (instantiate env b) ys) super
        = map (instantiate env b) (parameterized_supertype_arguments env sub ys super)
    /\ forall a, In a (parameterized_supertype_arguments env sub ys super) ->
        argument_wfrag env a = true /\ bound_in env b K [] a = true.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite !parameterized_supertype_arguments_eq. split.
    - rewrite map_map. apply map_ext_in. intros r Hr. symmetry.
      apply (proj2 (wide_template_commutes sub ys Hl Hys (argument_depth r))); [lia|apply Ht, Hr|].
      exact (supertypes_mention_nothing_as_bottom sub super r Hr).
    - intros a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      apply (proj2 (wide_template_instances sub ys Hl Hys (argument_depth r))); [lia|apply Ht, Hr|].
      exact (supertypes_mention_nothing_as_bottom sub super r Hr).
Qed.

End WideTemplates.

Section WideHelpers.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis not_expansive: non_expansive env.
Variable b: Bindings.

(* What unify never rejects of ground types, it accepts *)
Lemma ground_accepts: forall D y, ground env D = true -> ground env y = true -> never_fails env D y ->
    exists f, unify env f D y (Ongoing []) = Some (Ongoing []).
Proof.
    intros D y HD Hy H. exact (accepts env wf declared declared_wf terminates finite not_expansive y D
        (ground_of_fragment env declared y Hy) (ground_of_fragment env declared D HD) H).
Qed.

Lemma ground_trans: forall f1 f2 X Y Z, ground env X = true -> ground env Y = true -> ground env Z = true ->
    unify env f1 Y X (Ongoing []) = Some (Ongoing []) -> unify env f2 Z Y (Ongoing []) = Some (Ongoing []) ->
    exists f, unify env f Z X (Ongoing []) = Some (Ongoing []).
Proof.
    intros f1 f2 X Y Z HX HY HZ H1 H2.
    destruct (ground_of_fragment env declared X HX) as [gX rX]. destruct (ground_of_fragment env declared Y HY) as [gY rY].
    destruct (ground_of_fragment env declared Z HZ) as [gZ rZ].
    assert (A1: is_assignable_to env f1 X Y = Some true) by (unfold is_assignable_to, empty_unification; rewrite H1; reflexivity).
    assert (A2: is_assignable_to env f2 Y Z = Some true) by (unfold is_assignable_to, empty_unification; rewrite H2; reflexivity).
    destruct (transitivity_terminating env wf declared declared_wf terminates finite not_expansive f1 f2 X Y Z
        gX gY gZ rX rY rZ A1 A2) as [f Hf].
    exists f. unfold is_assignable_to, empty_unification in Hf.
    destruct (unify env f Z X (Ongoing [])) as [[u|]|] eqn:E; try discriminate Hf.
    pose proof (ground_keeps env wf f Z X [] u HZ HX E) as ->. reflexivity.
Qed.

Definition class_shaped_target (D: EType): Prop :=
    match D with RootResolved _ _ _ | Nullable (RootResolved _ _ _) => True | _ => False end.

Lemma remut_class_target: forall D, class_shaped_target D -> remut D D.
Proof.
    intros [md cd ad|[md cd ad| | | | | |]| | | | |] H; try contradiction; [left|right]; exists md, md, cd, ad; split; reflexivity.
Qed.

Lemma remut_with_mutability_class: forall k m c args, remut (RootResolved m c args) (with_mutability env k (RootResolved m c args)).
Proof. intros k m c args. left. do 2 eexists. exists c, args. split; reflexivity. Qed.

(* Of the same class, of a mutability below its own, a class type is taken where it is *)
Lemma ground_accepts_lower: forall f D x k s r, ground env D = true -> ground env x = true -> is_class x = true ->
    class_shaped_target D -> Model.is_subtype_of k (assignment_mutability env x) = true ->
    unify env f D x (Ongoing s) = Some (Ongoing r) -> unify env f D (with_mutability env k x) (Ongoing s) = Some (Ongoing r).
Proof.
    intros f D x k s r HD Hx Hc Hshape Hk H.
    pose proof (ground_mutability env wf f D x s r HD Hx H) as Hm.
    destruct x as [mx cx ax| | | | | |]; try discriminate Hc.
    apply (unify_remut env f D D (RootResolved mx cx ax) _ s r (remut_class_target D Hshape) (remut_with_mutability_class k mx cx ax));
        [|exact H].
    simpl in Hm, Hk |- *. destruct (is_const (declaration_of env cx)); [exact Hm|exact (mutability_subtype_trans _ _ _ Hk Hm)].
Qed.

(* A type that never rejects a component of an intersection of class types, never rejects the
   intersection *)
Lemma ground_never_fails_into_intersection: forall D ys y, class_shaped_target D -> In y ys -> is_class y = true ->
    never_fails env D y -> never_fails env D (Intersection ys).
Proof.
    intros D ys y HD Hin Hy H. apply never_fails_step. intros f s.
    destruct D as [m c args|[m c args| | | | | |]| | | | |]; try contradiction.
    - exact (flipped_never_fails env f _ ys s y Hin (H f s)).
    - change (unify env (S f) (Nullable (RootResolved m c args)) (Intersection ys) (Ongoing s))
          with (unify env f (RootResolved m c args) (Intersection ys) (Ongoing s)).
      destruct f as [|f]; [discriminate|].
      apply (flipped_never_fails env f _ ys s y Hin).
      destruct y as [my cy argsy| | | | | |]; try discriminate Hy.
      pose proof (H (S f) s) as H'. rewrite unify_nullable_class in H'. exact H'.
Qed.

(* A class type, of another mutability, that each component of the assignee fits, never rejects
   what it takes *)
Lemma with_mutability_target_never_fails: forall f D y k, ground env D = true -> is_class D = true -> ground env y = true ->
    unify env f D y (Ongoing []) = Some (Ongoing []) ->
    (forall c, In c (intersected_components y) -> Model.is_subtype_of (assignment_mutability env c) k = true) ->
    never_fails env (with_mutability env k D) y.
Proof.
    intros f D y k HD Hc Hy H Hk. destruct D as [md cd ad| | | | | |]; try discriminate Hc.
    assert (Hnv: no_vars (with_mutability env k (RootResolved md cd ad)) = true) by exact (ground_no_vars env _ HD).
    (* the class type of the other mutability takes a class type it takes, which fits *)
    assert (Hcls: forall g x, ground env x = true -> is_class x = true ->
        unify env g (RootResolved md cd ad) x (Ongoing []) = Some (Ongoing []) ->
        Model.is_subtype_of (assignment_mutability env x) k = true ->
        unify env g (with_mutability env k (RootResolved md cd ad)) x (Ongoing []) = Some (Ongoing [])).
    { intros g x Hx Hcx E Hxk. destruct x as [mx cx ax| | | | | |]; try discriminate Hcx.
      apply (unify_remut env g _ _ _ _ [] [] (remut_with_mutability_class k md cd ad) (remut_class_target (RootResolved mx cx ax) I)); [|exact E].
      pose proof (ground_mutability env wf g _ _ [] [] HD Hx E) as Hm.
      simpl in Hm |- *. destruct (is_const (declaration_of env cd)); [exact Hm|exact Hxk]. }
    destruct f as [|f]; [discriminate H|].
    destruct (ground_cases env y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> [_ Hys]]]|[ys [-> _]]]]].
    - exact (success_never_fails env wf _ _ _ [] Hnv (ground_no_vars env _ Hy)
          (Hcls (S f) _ Hy eq_refl H (Hk _ (or_introl eq_refl)))).
    - rewrite unify_class_nullable in H. discriminate H.
    - destruct (intersection_flipped_unify_found env f _ ys [] [] H) as [c [Hin Hu]].
      destruct (Hys c Hin) as [Hcc Hgc].
      pose proof (Hcls f c Hgc Hcc Hu (Hk c Hin)) as Hc'.
      pose proof (success_never_fails env wf _ _ _ [] Hnv (ground_no_vars env _ Hgc) Hc') as Hnf.
      apply never_fails_step. intros f' s.
      exact (flipped_never_fails env f' _ ys s c Hin (Hnf f' s)).
    - rewrite unify_class_nullable in H. discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The types instantiated                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

(* No type variables in the types of the wide fragment *)
Lemma wide_no_vars: forall t, wtfrag env t = true -> no_vars t = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct (wtfrag_cases env t H) as [Hw|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (wfrag_cases env wf t Hw) as [[m [c [args [-> [_ [_ Hargs]]]]]]|[->|[[m [c [args [-> Ht']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + simpl. apply forallb_forall. intros a Hin. pose proof (Hargs a Hin) as Ha. pose proof (esize_in args a Hin) as Hs.
        destruct a as [| | | |v o n| |]; try discriminate Ha. simpl in Ha, Hs |- *.
        apply (IH (esize n)); [simpl; lia|reflexivity|exact Ha].
      + reflexivity.
      + exact (IH (esize (RootResolved m c args)) ltac:(simpl; lia) (RootResolved m c args) eq_refl (wfrag_wtfrag env _ Ht')).
      + destruct g as [gm nn p [|v vs]]; [reflexivity|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv].
      + destruct g as [gm nn p [|v vs]]; [reflexivity|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv].
    - destruct (wcomponents_facts env cs Hcs) as [_ Hc]. simpl. apply forallb_forall. intros c Hin.
      pose proof (esize_in cs c Hin) as Hs.
      apply (IH (esize c)); [simpl; lia|reflexivity|exact (wfrag_wtfrag env c (proj2 (Hc c Hin)))].
    - destruct (wcomponents_facts env cs Hcs) as [_ Hc]. simpl. apply forallb_forall. intros c Hin.
      pose proof (esize_in cs c Hin) as Hs.
      apply (IH (esize c)); [simpl; lia|reflexivity|exact (wfrag_wtfrag env c (proj2 (Hc c Hin)))].
Qed.

Lemma no_vars_keeps: forall n t a s u, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s.
Proof.
    intros n t a s u Ht Ha H. pose proof (unify_free env wf n t a s s _ Ht Ha H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

(* What a nullable target unifies the type in it with *)
Definition nullable_assignee (a: EType): EType :=
    match a with
    | Nullable n => n
    | Generic g => Generic (narrow_ref env g)
    | _ => a
    end.

Lemma unify_nullable_step: forall n t0 a s, (match a with TypeArgument _ _ _ | TypeVariable _ => False | _ => True end) ->
    unify env (S n) (Nullable t0) a (Ongoing s) = unify env n t0 (nullable_assignee a) (Ongoing s).
Proof. intros n t0 [| |[]| | | |] s H; try contradiction; reflexivity. Qed.

End WideHelpers.

Section WideMain.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis not_expansive: non_expansive env.
Variable b: Bindings.
Variable K: nat.
Hypothesis Hbf: bindings_in_fragment env b.


(* A type, instantiated, takes the instance of a type that it takes *)
Definition wide_claim (n: nat) (t a: EType): Prop :=
    forall u, unify env n t a (Ongoing []) = Some (Ongoing u) ->
    exists f, unify env f (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing []).

Definition types_claim (n: nat): Prop :=
    forall t a, wtfrag env t = true -> wtfrag env a = true -> bound_in env b K [] t = true -> bound_in env b K [] a = true -> wide_claim n t a.

Definition arguments_claim (n: nat): Prop :=
    forall t a, argument_wfrag env t = true -> argument_wfrag env a = true -> bound_in env b K [] t = true -> bound_in env b K [] a = true -> wide_claim n t a.

Lemma inst_facts: forall t, wtfrag env t = true -> bound_in env b K [] t = true ->
    ground env (instantiate env b t) = true /\ (is_nullable env t = false -> is_nullable env (instantiate env b t) = false)
    /\ (is_component_shape env t = true -> is_class (instantiate env b t) = true).
Proof.
    intros t Ht Hb. destruct (wide_instance env wf b K Hbf t Ht Hb) as [Hg [_ [_ [_ [Hn Hc]]]]]. exact (conj Hg (conj Hn Hc)).
Qed.

Lemma wtfrag_nullable_inner: forall t0, wtfrag env (Nullable t0) = true -> wtfrag env t0 = true.
Proof.
    intros [m c args|n|g|me msg|v o n|g|cs] H; try discriminate H; exact H.
Qed.

Lemma generic_of_wtfrag: forall g, wtfrag env (Generic g) = true -> generic_sfrag env g.
Proof.
    intros g H. change (sfrag env (Generic g) = true) in H. apply (sfrag_generic_iff env wf) in H. exact H.
Qed.

(* An intersection, instantiated *)
Lemma inst_intersection: forall cs, wcomponents env cs = true -> bound_in env b K [] (Intersection cs) = true ->
    instantiate env b (Intersection cs) = Intersection (map (with_mutability env (common_mutability env (map (instantiate env b) cs))) (map (instantiate env b) cs))
    /\ forall c, In c cs -> ground env (instantiate env b c) = true /\ is_class (instantiate env b c) = true.
Proof.
    intros cs Hcs Hb. destruct (wcomponents_facts env cs Hcs) as [Hl Hc].
    assert (Hall: forall c, In c cs -> ground env (instantiate env b c) = true /\ is_class (instantiate env b c) = true).
    { intros c Hin. destruct (Hc c Hin) as [Hsh Hwc].
      destruct (inst_facts c (wfrag_wtfrag env c Hwc) (bound_in_component env b K [] cs c Hb Hin)) as [Hg [_ Hcl]].
      exact (conj Hg (Hcl Hsh)). }
    split; [|exact Hall].
    change (instantiate env b (Intersection cs)) with (of_components env (flat_map intersected_components (map (instantiate env b) cs))).
    apply of_class_types; [rewrite length_map; exact Hl|].
    intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]]. apply (Hall c Hin).
Qed.

Lemma intersection_ground: forall cs, wcomponents env cs = true -> bound_in env b K [] (Intersection cs) = true -> forall y,
    In y (map (with_mutability env (common_mutability env (map (instantiate env b) cs))) (map (instantiate env b) cs)) ->
    ground env y = true /\ is_class y = true.
Proof.
    intros cs Hcs Hb y Hy. destruct (inst_intersection cs Hcs Hb) as [_ Hall].
    apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]].
    destruct (Hall c Hin) as [Hg Hcl]. exact (ground_with_mutability env _ _ Hcl Hg).
Qed.

Lemma class_non_null: forall x, is_class x = true -> is_nullable env x = false.
Proof. intros x H. destruct x; first [reflexivity|discriminate H]. Qed.

(* The instance of a type that is no intersection is a class type, nullable or not *)
Lemma inst_class_shaped: forall t, wfrag env t = true -> bound_in env b K [] t = true -> class_shaped_target (instantiate env b t).
Proof.
    intros t Ht Hb.
    destruct (wfrag_cases env wf t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> Hg]]|[g [-> Hg]]]]]];
        try exact I.
    - destruct (binds_ref_some env wf b K [] g Hb) as [o [x [Ex [Ho [Hx _]]]]].
      rewrite (proj1 (instantiate_exact_generic env b g o x Ex Ho Hx)).
      destruct (fragment_cases env _ (inst_ref_in_fragment env g x (Hbf _ o x Ex))) as [[m [c [args E]]]|[m [c [args [E _]]]]];
          rewrite E; exact I.
    - destruct (binds_ref_some env wf b K [] g Hb) as [o [x [Ex [Ho [Hx _]]]]].
      change (instantiate env b (Nullable (Generic g))) with (rewrap_nullable (instantiate env b (Generic g))).
      rewrite (proj1 (instantiate_exact_generic env b g o x Ex Ho Hx)).
      destruct (fragment_cases env _ (in_fragment_rewrap env _ (inst_ref_in_fragment env g x (Hbf _ o x Ex))))
          as [[m [c [args E]]]|[m [c [args [E _]]]]]; rewrite E; exact I.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases, by the target                                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

(* A nullable target: the type in it takes the assignee without null *)
Lemma wide_nullable_target: forall n t0 a, types_claim n ->
    wtfrag env (Nullable t0) = true -> wtfrag env a = true -> bound_in env b K [] t0 = true -> bound_in env b K [] a = true -> wide_claim (S n) (Nullable t0) a.
Proof.
    intros n t0 a IH Ht Ha Hbt Hba u H. pose proof (wtfrag_nullable_inner t0 Ht) as Ht0.
    (* what the type in the target unifies with *)
    assert (Ha': wtfrag env (nullable_assignee env a) = true /\ bound_in env b K [] (nullable_assignee env a) = true
        /\ without_null env (instantiate env b (nullable_assignee env a)) = without_null env (instantiate env b a)).
    { destruct a as [m c args|an|ga|me msg|v o n'|g|cs]; try discriminate Ha; cbn [nullable_assignee].
      - split; [exact Ha|split; [exact Hba|reflexivity]].
      - split; [exact (wtfrag_nullable_inner an Ha)|]. split; [exact Hba|].
        change (instantiate env b (Nullable an)) with (rewrap_nullable (instantiate env b an)). rewrite without_null_rewrap. reflexivity.
      - pose proof (generic_of_wtfrag ga Ha) as Hga.
        destruct (narrow_generic env wf b K [] Hbf ga Hga Hba) as [Hfn [Hbn Hin]].
        split; [exact (wfrag_wtfrag env _ (sfrag_wfrag env wf _ Hfn))|]. split; [exact Hbn|].
        rewrite <- (inst_nested_instantiate env wf b K [] _ (sfrag_tfrag env _ Hfn) Hbn), Hin.
        rewrite (inst_nested_instantiate env wf b K [] _ (sfrag_tfrag env _ (generic_sfrag_sfrag env wf ga Hga)) Hba).
        apply (ground_without_null_idempotent env). exact (proj1 (inst_facts _ Ha Hba)).
      - split; [exact Ha|split; [exact Hba|reflexivity]]. }
    destruct Ha' as [Hwa [Hba' Hwn]].
    rewrite (unify_nullable_step env n t0 a [] ltac:(destruct a; try discriminate Ha; exact I)) in H.
    destruct (IH t0 _ Ht0 Hwa Hbt Hba' u H) as [f Hf].
    pose proof (proj1 (inst_facts t0 Ht0 Hbt)) as HT0. pose proof (proj1 (inst_facts _ Hwa Hba')) as HA'.
    pose proof (proj1 (inst_facts a Ha Hba)) as HA.
    pose proof (ground_unify_without_null env f _ _ [] [] HT0 HA' Hf) as Hw.
    exists (S f). change (instantiate env b (Nullable t0)) with (rewrap_nullable (instantiate env b t0)).
    rewrite (ground_rewrap env _ HT0), (ground_nullable_target env f _ _ [] HA), <- Hwn. exact Hw.
Qed.

(* An intersection as the target: each of its components takes the assignee *)
Lemma wide_intersection_target: forall n ts a, types_claim n ->
    wcomponents env ts = true -> wtfrag env a = true -> bound_in env b K [] (Intersection ts) = true -> bound_in env b K [] a = true ->
    wide_claim (S n) (Intersection ts) a.
Proof.
    intros n ts a IH Hts Ha Hbt Hba u H. destruct (wcomponents_facts env ts Hts) as [Hl Hc].
    assert (Hshape: match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end).
    { destruct a; try exact I; try discriminate Ha. simpl in H. discriminate H. }
    assert (Hnv: forall c, In c ts -> is_type_variable c = false)
        by (intros c Hin; pose proof (proj1 (Hc c Hin)) as Hsh; destruct c; first [reflexivity|discriminate Hsh]).
    assert (Hne: ts <> []) by (intros ->; simpl in Hl; lia).
    pose proof (wide_no_vars env wf a Ha) as Hnva.
    destruct (intersection_target env n ts a [] u Hnv Hne Hshape
        (fun c u' Hin E => no_vars_keeps env wf n c a [] u' (wide_no_vars env wf c (wfrag_wtfrag env c (proj2 (Hc c Hin)))) Hnva E) H)
        as [_ Hall].
    (* each component, instantiated, takes the instance of the assignee *)
    assert (Hcomp: forall c, In c ts -> exists f, unify env f (instantiate env b c) (instantiate env b a) (Ongoing []) = Some (Ongoing [])).
    { intros c Hin. destruct (Hc c Hin) as [_ Hwc].
      exact (IH c a (wfrag_wtfrag env c Hwc) Ha (bound_in_component env b K [] ts c Hbt Hin) Hba [] (Hall c Hin)). }
    destruct (inst_intersection ts Hts Hbt) as [Heq Hcs].
    pose proof (proj1 (inst_facts a Ha Hba)) as HA.
    (* the instance of the assignee is non-null *)
    assert (HnA: is_nullable env (instantiate env b a) = false).
    { destruct ts as [|c1 ts']; [exfalso; exact (Hne eq_refl)|].
      destruct (Hcomp c1 (or_introl eq_refl)) as [f1 H1]. destruct (Hcs c1 (or_introl eq_refl)) as [Hg1 Hcl1].
      exact (ground_non_null env f1 _ _ [] [] Hg1 HA (class_non_null _ Hcl1) H1). }
    (* the components of the instance of the assignee are of one mutability, which each component of
       the target takes *)
    assert (Hfit: forall c, In c ts -> forall y, In y (intersected_components (instantiate env b a)) ->
        Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env (instantiate env b c)) = true).
    { intros c Hin y Hy. destruct (Hcomp c Hin) as [f Hf]. destruct (Hcs c Hin) as [Hgc Hclc].
      destruct (wtfrag_cases env a Ha) as [Hw|[[cs [Ea Hcs']]|[cs [Ea _]]]].
      - assert (Hy': y = instantiate env b a).
        { pose proof (inst_class_shaped a Hw Hba) as Hsh.
          destruct (instantiate env b a) as [m d args|[m d args| | | | | |]| | | | |]; try contradiction; try discriminate HnA.
          destruct Hy as [<-|[]]. reflexivity. }
        subst y. exact (ground_mutability env wf f _ _ [] [] Hgc HA Hf).
      - subst a. destruct (inst_intersection cs Hcs' Hba) as [Heqa Hca].
        rewrite Heqa in Hy, Hf. cbn [intersected_components] in Hy.
        destruct f as [|f]; [discriminate Hf|].
        destruct (instantiate env b c) as [mc dc ac| | | | | |] eqn:Ec; try discriminate Hclc.
        destruct (intersection_flipped_unify_found env f _ _ [] [] Hf) as [y' [Hy'in Hu]].
        pose proof (ground_mutability env wf f _ _ [] [] Hgc (proj1 (intersection_ground cs Hcs' Hba y' Hy'in)) Hu) as Hm.
        apply in_map_iff in Hy, Hy'in. destruct Hy as [y0 [<- Hy0]]. destruct Hy'in as [y1 [<- Hy1]].
        apply in_map_iff in Hy0, Hy1. destruct Hy0 as [c0 [<- Hc0]]. destruct Hy1 as [c1 [<- Hc1]].
        rewrite (common_class_mutability env _ _ (in_map _ _ _ Hc0) (proj2 (Hca c0 Hc0))).
        rewrite (common_class_mutability env _ _ (in_map _ _ _ Hc1) (proj2 (Hca c1 Hc1))) in Hm. exact Hm.
      - subst a. destruct Hshape. }
    rewrite Heq. apply (ground_accepts env wf declared declared_wf terminates finite not_expansive).
    - unfold ground. apply andb_true_iff. split.
      + simpl. apply andb_true_iff. split; [destruct ts as [|c1 ts']; simpl in Hl |- *; [lia|reflexivity]|].
        apply forallb_forall. intros y Hy. destruct (intersection_ground ts Hts Hbt y Hy) as [Hg Hcl].
        destruct y as [| | | | | |]; try discriminate Hcl. apply andb_true_iff. split; [reflexivity|exact (ground_gfrag env _ Hg)].
      + change (forallb no_refs (map (with_mutability env (common_mutability env (map (instantiate env b) ts))) (map (instantiate env b) ts)) = true).
        apply forallb_forall. intros y Hy. destruct (intersection_ground ts Hts Hbt y Hy) as [Hg _].
        unfold ground in Hg. apply andb_true_iff in Hg. apply Hg.
    - exact HA.
    - apply (inter_target_never_fails env wf).
      + apply forallb_forall. intros y Hy. exact (ground_no_vars env _ (proj1 (intersection_ground ts Hts Hbt y Hy))).
      + exact (ground_no_vars env _ HA).
      + destruct (ground_cases env _ HA) as [[m [d [args E]]]|[[m [d [args E]]]|[[ys [E _]]|[ys [E _]]]]];
            rewrite E in HnA |- *; first [exact I|discriminate HnA].
      + intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'.
        destruct Hy' as [c [<- Hin]]. destruct (Hcomp c Hin) as [f Hf]. destruct (Hcs c Hin) as [Hgc Hclc].
        apply (with_mutability_target_never_fails env wf f); [exact Hgc|exact Hclc|exact HA|exact Hf|].
        intros y Hy. apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
        intros m Hm. apply in_map_iff in Hm. destruct Hm as [z [<- Hz]]. apply in_map_iff in Hz. destruct Hz as [c' [<- Hin']].
        exact (Hfit c' Hin' y Hy).
Qed.

(* A class type or a reference as the target, an intersection as the assignee: one component of it is
   taken, and so is its instance, of the common mutability *)
Lemma wide_into_intersection: forall n t cs, types_claim n ->
    wtfrag env t = true -> (is_class t || is_generic t) = true -> wcomponents env cs = true ->
    bound_in env b K [] t = true -> bound_in env b K [] (Intersection cs) = true -> wide_claim (S n) t (Intersection cs).
Proof.
    intros n t cs IH Ht Hshape Hcs Hbt Hba u H.
    destruct (unify_into_components env n t cs [] u H Hshape) as [c [Hin Hc]].
    destruct (wcomponents_facts env cs Hcs) as [_ Hcomps]. destruct (Hcomps c Hin) as [_ Hwc].
    destruct (IH t c Ht (wfrag_wtfrag env c Hwc) Hbt (bound_in_component env b K [] cs c Hba Hin) u Hc) as [f Hf].
    destruct (inst_intersection cs Hcs Hba) as [Heq Hall]. destruct (Hall c Hin) as [Hgc Hclc].
    pose proof (proj1 (inst_facts t Ht Hbt)) as HT.
    assert (Hst: class_shaped_target (instantiate env b t)).
    { apply inst_class_shaped; [|exact Hbt].
      destruct (wtfrag_cases env t Ht) as [Hw|[[cs' [-> _]]|[cs' [-> _]]]]; [exact Hw|discriminate Hshape|discriminate Hshape]. }
    assert (Hlow: unify env f (instantiate env b t)
        (with_mutability env (common_mutability env (map (instantiate env b) cs)) (instantiate env b c)) (Ongoing []) = Some (Ongoing [])).
    { apply (ground_accepts_lower env wf f); [exact HT|exact Hgc|exact Hclc|exact Hst| |exact Hf].
      apply fold_intersect_below_element. apply in_map, in_map, Hin. }
    rewrite Heq. apply (ground_accepts env wf declared declared_wf terminates finite not_expansive).
    - exact HT.
    - rewrite <- Heq. exact (proj1 (inst_facts (Intersection cs) Hcs Hba)).
    - set (k := common_mutability env (map (instantiate env b) cs)) in *.
      destruct (ground_with_mutability env k _ Hclc Hgc) as [Hgk Hck].
      apply (ground_never_fails_into_intersection env _ _ (with_mutability env k (instantiate env b c)) Hst);
          [apply in_map, in_map, Hin|exact Hck|].
      exact (success_never_fails env wf f _ _ [] (ground_no_vars env _ HT) (ground_no_vars env _ Hgk) Hlow).
Qed.

(* A reference as the assignee, to a type parameter that another one or a class type takes: its
   instance is within its bound, instantiated, which the instance of the target takes *)
Lemma wide_via_bound: forall n t ga, types_claim n ->
    wtfrag env t = true -> (is_class t || is_generic t) = true -> generic_sfrag env ga ->
    bound_in env b K [] t = true -> bound_in env b K [] (Generic ga) = true ->
    forall u, unify env n t (effective_bound env ga) (Ongoing []) = Some (Ongoing u) ->
    exists f, unify env f (instantiate env b t) (instantiate env b (Generic ga)) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n t ga IH Ht Hshape [Hfb _] Hbt Hba u Hu.
    destruct (binds_ref_some env wf b K [] ga Hba) as [o [x [E [Ho [Hx [Hr Hbe]]]]]].
    pose proof (Hbf _ o x E) as HFx. pose proof (inst_ref_in_fragment env ga x HFx) as HI.
    rewrite (proj1 (instantiate_exact_generic env b ga o x E Ho Hx)).
    destruct (instance_facts env wf b K [] Hbf _ _ (le_n _) Hfb Hbe) as [HB _].
    pose proof (respects_unify env wf K [] _ _ HI HB Hr) as Hra.
    pose proof (proj1 (inst_facts t Ht Hbt)) as HT.
    pose proof (in_fragment_ground env _ HI) as HgI.
    destruct (tfrag_cases env _ Hfb) as [Hsb|[[cs [Eb Hcs]]|[cs [Eb Hcs]]]].
    - rewrite (inst_nested_instantiate env wf b K [] _ Hfb Hbe) in Hra.
      pose proof (wfrag_wtfrag env _ (sfrag_wfrag env wf _ Hsb)) as Hwb.
      destruct (IH t _ Ht Hwb Hbt Hbe u Hu) as [f Hf].
      exact (ground_trans env wf declared declared_wf terminates finite not_expansive K f _ _ _ HgI
          (proj1 (inst_facts _ Hwb Hbe)) HT Hra Hf).
    - (* the bound is an intersection: through the component of it that the target takes *)
      rewrite Eb in Hu, Hra, Hbe, HB. destruct n as [|n]; [discriminate Hu|].
      destruct (unify_into_components env n t cs [] u Hu Hshape) as [c [Hin Hc]].
      destruct (components_sfrag_facts env cs Hcs) as [_ Hcomps]. destruct (Hcomps c Hin) as [Hshc Hsc].
      pose proof (wfrag_wtfrag env c (sfrag_wfrag env wf c Hsc)) as Hwc. pose proof (bound_in_component env b K [] cs c Hbe Hin) as Hbc.
      destruct (IH t c Ht Hwc Hbt Hbc u (unify_fuel_monotone env n (S n) _ _ _ _ ltac:(lia) Hc))
          as [f Hf].
      assert (Hn: forall c', In c' cs -> is_nullable env (inst_nested env b c') = false).
      { intros c' Hin'. destruct (Hcomps c' Hin') as [Hsh' Hs'].
        apply (proj2 (proj2 (instance_facts env wf b K [] Hbf _ c' (le_n _) (sfrag_tfrag env c' Hs')
            (bound_in_component env b K [] cs c' Hbe Hin')))).
        apply (component_non_null env), Hsh'. }
      destruct (intersection_instance env wf b K [] Hbf cs Hcs Hbe Hn) as [Heq [Hcc Hcomp]].
      rewrite Heq in Hra. assert (HK: exists K', K = S K') by (destruct K; [discriminate Hra|eauto]).
      destruct HK as [K' HK']. rewrite HK' in Hra.
      destruct (inter_accepts env wf K' _ _ [] [] Hcc HI Hra) as [_ [_ Hall]].
      destruct (Hcomp c Hin) as [Hfc Hm].
      pose proof (with_mutability_accepts env K' _ _ _ [] [] Hfc HI Hm (Hall _ (in_map _ _ _ (in_map _ _ _ Hin)))) as Hcx.
      rewrite (inst_nested_instantiate env wf b K [] c (sfrag_tfrag env c Hsc) Hbc) in Hcx.
      exact (ground_trans env wf declared declared_wf terminates finite not_expansive K' f _ _ _ HgI
          (proj1 (inst_facts c Hwc Hbc)) HT Hcx Hf).
    - (* a nullable bound, which a class type or a reference takes nothing of *)
      rewrite Eb in Hu. destruct n as [|n]; [discriminate Hu|].
      destruct (wtfrag_cases env t Ht) as [Hw|[[cs' [-> _]]|[cs' [-> _]]]]; [|discriminate Hshape|discriminate Hshape].
      destruct (wfrag_cases env wf t Hw) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
          unfold bottom_type in *; try discriminate Hshape.
      + rewrite unify_class_nullable in Hu. discriminate Hu.
      + rewrite unify_class_nullable in Hu. discriminate Hu.
      + rewrite (unify_generic_nullable env) in Hu. discriminate Hu.
Qed.

(* Two references to the same type parameter: the instances are ordered as the bounds are *)
Lemma wide_same_parameter: forall gt ga, generic_sfrag env gt -> generic_sfrag env ga ->
    bound_in env b K [] (Generic gt) = true -> bound_in env b K [] (Generic ga) = true -> param_of ga = param_of gt ->
    Model.is_subtype_of (assignment_mutability env (effective_bound env ga)) (assignment_mutability env (effective_bound env gt)) = true ->
    (negb (is_nullable env (effective_bound env ga)) || is_nullable env (effective_bound env gt)) = true ->
    exists f, unify env f (instantiate env b (Generic gt)) (instantiate env b (Generic ga)) (Ongoing []) = Some (Ongoing []).
Proof.
    intros gt ga Hgt Hga Hbt Hba Ep Hm Hn.
    destruct (binds_ref_some env wf b K [] gt Hbt) as [o [x [Ex [Hot [Hxt _]]]]].
    destruct (binds_ref_some env wf b K [] ga Hba) as [o' [x' [Ea [Hoa [Hxa [Hra Hbe]]]]]].
    rewrite Ep, Ex in Ea. injection Ea as <- <-.
    pose proof (Hbf _ o x Ex) as HFx. destruct Hga as [Hfa [Hwa _]].
    destruct (instance_facts env wf b K [] Hbf _ _ (le_n _) Hfa Hbe) as [HB [HmB HnB]].
    rewrite (proj1 (instantiate_exact_generic env b gt o x Ex Hot Hxt)).
    rewrite (proj1 (instantiate_exact_generic env b ga o x (eq_trans (f_equal (lookup_binding b) Ep) Ex) Hot Hxt)).
    exists (depth x).
    apply (same_parameter env wf K [] (depth x) gt ga x _ HFx HB); [|exact Hgt| |exact HmB|exact HnB|exact Hm|exact Hn].
    - exact (proj1 (reflexivity_with_arguments env (depth x)) x [] HFx (le_n _)).
    - apply (respects_unify env wf K []); [apply inst_ref_in_fragment, HFx|exact HB|exact Hra].
Qed.

Lemma forall2_uniform: forall (P: nat -> EType -> EType -> Prop), (forall f f' x y, f <= f' -> P f x y -> P f' x y) ->
    forall xs ys, Forall2 (fun x y => exists f, P f x y) xs ys -> exists F, Forall2 (P F) xs ys.
Proof.
    intros P Hm xs ys H. induction H as [|x y xs ys [f1 H1] _ [F HF]]; [exists 0; constructor|].
    exists (max f1 F). constructor; [apply (Hm f1); [lia|exact H1]|].
    apply (Forall2_impl_in _ _ xs ys HF). intros a c _ _ Ha. apply (Hm F); [lia|exact Ha].
Qed.

Lemma forall2_map_instances: forall F xs ys,
    Forall2 (fun a t => unify env F (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing [])) xs ys ->
    Forall2 (fun a t => unify env F t a (Ongoing []) = Some (Ongoing [])) (map (instantiate env b) xs) (map (instantiate env b) ys).
Proof. intros F xs ys H. induction H; constructor; assumption. Qed.


(* Two class types: their type arguments pairwise, those of a subclass normalized *)
Lemma wide_classes: forall n mt ct targs ma ca aargs, arguments_claim n ->
    wfrag env (RootResolved mt ct targs) = true -> wfrag env (RootResolved ma ca aargs) = true ->
    bound_in env b K [] (RootResolved mt ct targs) = true -> bound_in env b K [] (RootResolved ma ca aargs) = true ->
    wide_claim (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs).
Proof.
    intros n mt ct targs ma ca aargs IH Ht Ha Hbt Hba u H.
    pose proof (no_vars_keeps env wf _ _ _ _ _ (wide_no_vars env wf _ (wfrag_wtfrag env _ Ht))
        (wide_no_vars env wf _ (wfrag_wtfrag env _ Ha)) H) as ->.
    change (instantiate env b (RootResolved mt ct targs)) with (RootResolved mt ct (map (instantiate env b) targs)).
    change (instantiate env b (RootResolved ma ca aargs)) with (RootResolved ma ca (map (instantiate env b) aargs)).
    rewrite unify_classes in H.
    destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate H].
    destruct (Model.is_subtype_of _ _) eqn:Em; [|discriminate H].
    destruct (class_eqb ca nothing) eqn:Hcn.
    { exists 1. rewrite unify_classes, Hbase.
      rewrite (assignment_mutability_of_class env ma ca (map (instantiate env b) aargs) aargs),
          (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Em, Hcn. reflexivity. }
    assert (Hct: class_eqb ct nothing = false).
    { destruct (class_eqb ct nothing) eqn:E; [|reflexivity]. apply class_eqb_true in E. subst ct.
      rewrite (only_nothing_is_below_nothing env ca Hbase), class_eqb_refl in Hcn. discriminate Hcn. }
    destruct (wfrag_cases env wf _ Ht) as [[mt' [ct' [targs' [Heq [_ [Hlt Htargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
        try discriminate Heq; [injection Heq as <- <- <-|unfold bottom_type in Heq; injection Heq as _ -> _; rewrite class_eqb_refl in Hct; discriminate Hct].
    destruct (wfrag_cases env wf _ Ha) as [[ma' [ca' [aargs' [Heq [_ [Hla Haargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
        try discriminate Heq; [injection Heq as <- <- <-|unfold bottom_type in Heq; injection Heq as _ -> _; rewrite class_eqb_refl in Hcn; discriminate Hcn].
    (* the type arguments of the assignee, normalized to the target's class, and instantiated *)
    assert (Hnorm: exists nargs,
        (if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) = nargs
        /\ (if class_eqb ca ct then map (instantiate env b) aargs
            else parameterized_supertype_arguments env ca (map (instantiate env b) aargs) ct) = map (instantiate env b) nargs
        /\ length targs = length nargs
        /\ forall a, In a nargs -> argument_wfrag env a = true /\ bound_in env b K [] a = true).
    { destruct (Class_eq_dec ca ct) as [<-|Hne].
      - rewrite class_eqb_refl. exists aargs. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
        intros a Hin. split; [exact (Haargs a Hin)|]. exact (bound_in_root env b K [] _ _ _ Hba a Hin).
      - rewrite (class_eqb_false _ _ Hne).
        assert (Hys: forall y, In y aargs -> argument_wfrag env y = true /\ bound_in env b K [] y = true)
            by (intros y Hy; split; [apply Haargs, Hy|apply (bound_in_root env b K [] _ _ _ Hba y Hy)]).
        destruct (wide_supertype_arguments_commute env wf b K Hbf ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Hys)
            as [Hcomm Hfacts].
        exists (parameterized_supertype_arguments env ca aargs ct). split; [reflexivity|]. split; [exact Hcomm|]. split.
        + destruct (wf_supertypes_are_templates env wf ca ct Hne (class_eqb_false_neq _ _ Hcn) Hbase) as [Hlt' _].
          rewrite parameterized_supertype_arguments_eq, length_map, Hlt'. lia.
        + intros a Hin. destruct (Hfacts a Hin) as [Hw Hb']. split; [exact Hw|exact Hb']. }
    destruct Hnorm as [nargs [E1 [E2 [Hlen Hnargs]]]].
    rewrite E1 in H. unfold unify_arguments in H.
    (* the type arguments pairwise, generically *)
    assert (Hargs_nv: forall a, argument_wfrag env a = true -> no_vars a = true).
    { intros [| | | |v o n'| |] Ha'; try discriminate Ha'. exact (wide_no_vars env wf n' Ha'). }
    pose proof (pairwise_of_arguments env n targs nargs [] Hlen
        (fun t a w Hti Hai E => no_vars_keeps env wf n t a [] w (Hargs_nv t (Htargs t Hti)) (Hargs_nv a (proj1 (Hnargs a Hai))) E) H)
        as Hpairs.
    (* and instantiated *)
    assert (Hinst: Forall2 (fun a t => exists f, unify env f (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))
        nargs targs).
    { apply (Forall2_impl_in _ _ _ _ Hpairs). intros a t Hai Hti E.
      destruct (Hnargs a Hai) as [Hwa Hba'].
      exact (IH t a (Htargs t Hti) Hwa (bound_in_root env b K [] _ _ _ Hbt t Hti) Hba' [] E). }
    destruct (forall2_uniform (fun F a t => unify env F (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))
        (fun f f' a t Hle E => unify_fuel_monotone env f f' _ _ _ _ Hle E) nargs targs Hinst) as [F HF].
    exists (S F). rewrite unify_classes, Hbase.
    rewrite (assignment_mutability_of_class env ma ca (map (instantiate env b) aargs) aargs),
        (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Em, Hcn, E2.
    unfold unify_arguments. apply (fold_of_pairs env). exact (forall2_map_instances F nargs targs HF).
Qed.

Lemma top_wide: wtfrag env top_type = true /\ bound_in env b K [] top_type = true
    /\ instantiate env b top_type = top_type.
Proof.
    split; [exact (wfrag_wtfrag env _ (sfrag_wfrag env wf _ (top_in_sfrag env wf)))|]. repeat split; exact I.
Qed.

Lemma bottom_wide: wtfrag env bottom_type = true /\ bound_in env b K [] bottom_type = true
    /\ instantiate env b bottom_type = bottom_type.
Proof. split; [exact (wfrag_wtfrag env _ (sfrag_wfrag env wf _ (bottom_in_sfrag env)))|]. repeat split; exact I. Qed.

(* Two type arguments *)
Lemma wide_arguments_case: forall n, types_claim n -> arguments_claim (S n).
Proof.
    intros n IH [| | | |vt ot nt| |] [| | | |va oa na| |] Ht Ha Hbt Hba u H; try discriminate Ht; try discriminate Ha.
    destruct (wide_argument env wf b K Hbf _ Ht Hbt) as [vt' [ot' [nt' [Et [Eit [Hwt [Hbnt [_ [_ [_ _]]]]]]]]]].
    injection Et as <- <- <-.
    destruct (wide_argument env wf b K Hbf _ Ha Hba) as [va' [oa' [na' [Ea [Eia [Hwa [Hbna [_ [_ [_ _]]]]]]]]]].
    injection Ea as <- <- <-.
    pose proof (wide_no_vars env wf nt Hwt) as Hnvt.
    assert (Htv: is_type_variable nt = false) by (destruct nt; first [reflexivity|discriminate Hnvt]).
    pose proof (proj1 (inst_facts nt Hwt Hbnt)) as HIt.
    assert (Htv': is_type_variable (instantiate env b nt) = false)
        by (pose proof (ground_no_vars env _ HIt) as Hv; destruct (instantiate env b nt); first [reflexivity|discriminate Hv]).
    rewrite unify_type_arguments in H by exact Htv.
    destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
    rewrite Eit, Eia.
    destruct top_wide as [Hwtop [Hbtop Hitop]]. destruct bottom_wide as [Hwbot [Hbbot Hibot]].
    assert (Hown: ownership_is_assignable_to (instantiate_ownership b oa) (instantiate_ownership b ot) = true)
        by exact (instantiation_preserves_ownership_assignability b oa ot Ho).
    destruct vt, va; unfold compare_variances in H; try discriminate H.
    1: { (* both ways *)
      destruct (unify env n nt na (Ongoing [])) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
      pose proof (no_vars_keeps env wf _ _ _ _ _ Hnvt (wide_no_vars env wf na Hwa) E1) as ->.
      destruct (IH nt na Hwt Hwa Hbnt Hbna [] E1) as [f1 H1].
      destruct (IH na nt Hwa Hwt Hbna Hbnt u H) as [f2 H2].
      exists (S (max f1 f2)). rewrite unify_type_arguments by exact Htv'. rewrite Hown. unfold compare_variances.
      rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) H1).
      exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) H2). }
    all: first
        [ destruct (IH nt na Hwt Hwa Hbnt Hbna u H) as [f Hf]
        | destruct (IH na nt Hwa Hwt Hbna Hbnt u H) as [f Hf]
        | destruct (IH nt top_type Hwt Hwtop Hbnt Hbtop u H) as [f Hf]; rewrite Hitop in Hf
        | destruct (IH bottom_type nt Hwbot Hwt Hbbot Hbnt u H) as [f Hf]; rewrite Hibot in Hf ];
        exists (S f); (rewrite unify_type_arguments by exact Htv'); rewrite Hown; exact Hf.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* All the cases                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma wide_main: forall n, types_claim n /\ arguments_claim n.
Proof.
    induction n as [|n [IHt IHa]].
    { split; intros t a _ _ _ _ u H; discriminate H. }
    split; [|exact (wide_arguments_case n IHt)].
    intros t a Ht Ha Hbt Hba u H.
    destruct (wtfrag_cases env t Ht) as [Hw|[[ts [-> Hts]]|[ts [-> Hts]]]].
    2: exact (wide_intersection_target n ts a IHt Hts Ha Hbt Hba u H).
    2: exact (wide_nullable_target n (Intersection ts) a IHt Ht Ha Hbt Hba u H).
    destruct (wfrag_cases env wf t Hw) as [[mt [ct [targs [-> _]]]]|[->|[[mt [ct [targs [-> _]]]]|[[gt [-> Hgt]]|[gt [-> Hgt]]]]]].
    4: (* a reference to a type parameter *)
      { destruct (wtfrag_cases env a Ha) as [Hwa|[[cs [-> Hcs]]|[cs [-> _]]]].
        - destruct (wfrag_cases env wf a Hwa) as [[ma [ca [aargs [-> [Hca _]]]]]|[->|[[ma [ca [aargs [-> _]]]]|[[ga [-> Hga]]|[ga [-> _]]]]]].
          + rewrite (unify_generic_root env wf), Hca in H. cbn [andb] in H. discriminate H.
          + unfold bottom_type in H. rewrite (unify_generic_root env wf) in H. rewrite class_eqb_refl in H. cbn [andb] in H.
            destruct (Model.is_subtype_of _ _); [|discriminate H].
            destruct (binds_ref_some env wf b K [] gt Hbt) as [o [x [Ex [Ho [Hx _]]]]].
            rewrite (proj1 (instantiate_exact_generic env b gt o x Ex Ho Hx)). exists 2.
            exact (below_all env wf [] _ 2 (inst_ref_in_fragment env gt x (Hbf _ o x Ex)) (le_n _)).
          + rewrite (unify_generic_nullable env) in H. discriminate H.
          + rewrite (unify_generic_generic_step env wf) in H. destruct (param_eqb (param_of ga) (param_of gt)) eqn:Ep.
            * apply param_eqb_eq in Ep. destruct (_ && _) eqn:Ec in H; [|discriminate H].
              apply andb_true_iff in Ec. destruct Ec as [Hm Hn].
              exact (wide_same_parameter gt ga Hgt Hga Hbt Hba Ep Hm Hn).
            * exact (wide_via_bound n (Generic gt) ga IHt Ht eq_refl Hga Hbt Hba u H).
          + rewrite (unify_generic_nullable env) in H. discriminate H.
        - exact (wide_into_intersection n (Generic gt) cs IHt Ht eq_refl Hcs Hbt Hba u H).
        - rewrite (unify_generic_nullable env) in H. discriminate H. }
    3,4: exact (wide_nullable_target n _ a IHt Ht Ha Hbt Hba u H).
    (* a class type *)
    all: unfold bottom_type in *.
    all: destruct (wtfrag_cases env a Ha) as [Hwa|[[cs [-> Hcs]]|[cs [-> _]]]];
        [|exact (wide_into_intersection n _ cs IHt Ht eq_refl Hcs Hbt Hba u H)
         |rewrite unify_class_nullable in H; discriminate H].
    all: destruct (wfrag_cases env wf a Hwa) as [[ma [ca [aargs [-> _]]]]|[->|[[ma [ca [aargs [-> _]]]]|[[ga [-> Hga]]|[ga [-> _]]]]]];
        unfold bottom_type in *;
        first [ rewrite unify_class_nullable in H; discriminate H
              | exact (wide_classes n _ _ _ _ _ _ IHa Hw Hwa Hbt Hba u H)
              | rewrite (unify_root_generic env) in H; exact (wide_via_bound n _ ga IHt Ht eq_refl Hga Hbt Hba u H) ].
Qed.

End WideMain.

(*
 * The substitution lemma, intersections in type arguments included: within the wide fragment, a
 * type that is assignable to another stays so, with the type parameters in both instantiated
 * exactly, where unify terminates (unify_terminates, on inheritance that isn't expansive:
 * ExpansiveInheritance.kt)
 *)
Theorem substitution_wide: forall env declared b K fuel t a,
    wellformed env -> bounds_wellformed env declared -> unify_terminates ->
    finitely_many_templates env -> non_expansive env -> bindings_in_fragment env b ->
    wtfrag env t = true -> wtfrag env a = true -> bound_in env b K [] t = true -> bound_in env b K [] a = true ->
    is_assignable_to env fuel a t = Some true ->
    exists f, is_assignable_to env f (instantiate env b a) (instantiate env b t) = Some true.
Proof.
    intros env declared b K fuel t a wf declared_wf terminates finite not_expansive Hbf Ht Ha Hbt Hba H.
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel t a (Ongoing [])) as [[u|]|] eqn:Eu; try discriminate H.
    destruct (proj1 (wide_main env wf declared declared_wf terminates finite not_expansive b K Hbf fuel)
        t a Ht Ha Hbt Hba u Eu) as [f Hf].
    exists f. rewrite Hf. reflexivity.
Qed.
