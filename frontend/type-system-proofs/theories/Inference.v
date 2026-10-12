From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Substitution.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Inference, with type variables bound exactly                                                     *)
(*                                                                                                *)
(* An invocation unifies the types of the parameters, in which the type parameters of the function *)
(* are type variables, with the types of the arguments. A type variable bound exactly, to a type    *)
(* argument, stands for each type the type argument does: `out B` for B and its subtypes; it is     *)
(* bound so by the explicit type arguments of an invocation, and by capturing the type arguments of *)
(* the receiver (Subtyping.capturable). Whatever unify accepts with the variables bound so, it      *)
(* accepts with the variables replaced by any of the types they stand for                          *)
(* (inference_with_arguments). Unifying the receiver parameter of a member function with the       *)
(* receiver binds the type parameters of the class so (receiver_captures), which makes calling a   *)
(* member function sound, where the function has no type parameters of its own (member_call_sound). *)
(* Type variables that aren't bound exactly, with lower and upper bounds, are left for later.       *)
(*                                                                                                *)
(* The types of the parameters are those of Substitution.v, with type variables in place of the    *)
(* type parameters (to_generic relates the two); the types of the arguments are those of            *)
(* Transitivity.v, Nothing only as `exclusive Nothing` (Substitution.nothing_is_bottom): Nothing    *)
(* is assignable to an out-variant type argument whatever its mutability, and there are no values  *)
(* of type Nothing.                                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma existsb_map_ext: forall {A B: Type} (f: B -> bool) (g: A -> bool) (h: A -> B) l,
    (forall a, In a l -> f (h a) = g a) -> existsb f (map h l) = existsb g l.
Proof.
    intros A B f g h l H. induction l as [|a l IH]; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Section Inference.

Variable env: Environment.
Hypothesis wf: wellformed env.
Hypothesis supertypes_mention_nothing_as_bottom: forall sub super t,
    In t (supertype_arguments env sub super) -> nothing_is_bottom t = true.

(* The type parameters of a type, as type variables *)
Fixpoint to_generic (t: EType): EType :=
    match t with
    | RootResolved m c arguments => RootResolved m c (map to_generic arguments)
    | Nullable n => Nullable (to_generic n)
    | TypeVariable g => Generic g
    | TypeArgument v o n => TypeArgument v o (to_generic n)
    | _ => t
    end.

(* No type parameters but as type variables, of no mutability of their own *)
Fixpoint no_generics (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb no_generics arguments
    | Nullable n => no_generics n
    | TypeVariable (mkGenericRef None _ _) => true
    | TypeArgument _ _ n => no_generics n
    | _ => false
    end.

(* The types of the parameters *)
Definition ifrag (t: EType): bool := sfrag env (to_generic t) && no_generics t.

(* The types of the arguments *)
Definition afrag (t: EType): bool := in_fragment env t && nothing_is_bottom t.

Fixpoint vsize (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments => S (list_max (map vsize arguments))
    | Nullable n => S (vsize n)
    | TypeArgument _ _ n => S (vsize n)
    | _ => 0
    end.

Lemma vsize_below: forall m c arguments a, In a arguments -> vsize a < vsize (RootResolved m c arguments).
Proof.
    intros m c arguments a Ha. change (vsize a < S (list_max (map vsize arguments))).
    assert (H: Forall (fun k => k <= list_max (map vsize arguments)) (map vsize arguments)) by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (vsize a) (in_map _ _ _ Ha)). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Type variables and type parameters instantiate alike                                            *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma to_generic_facts: forall k t, vsize t <= k -> no_generics t = true ->
    (forall b, mentions_loosely_bound b (to_generic t) = mentions_loosely_bound b t)
    /\ (forall b, mentions_loosely_bound_in_arguments b (to_generic t) = mentions_loosely_bound_in_arguments b t)
    /\ mutability_of env (to_generic t) = mutability_of env t
    /\ (forall b, instantiate env b (to_generic t) = instantiate env b t).
Proof.
    induction k as [|k IH]; intros t Hk Ht.
    - destruct t as [| |[]| | |[[|] p bnd]|]; simpl in Hk, Ht; try lia; try discriminate Ht.
      repeat split; reflexivity.
    - destruct t as [m c args|n|[]|m msg|v o n|[[|] p bnd]|cs]; simpl in Ht; try discriminate Ht.
      + assert (Hall: forall a, In a args -> (forall b, mentions_loosely_bound b (to_generic a) = mentions_loosely_bound b a)
            /\ (forall b, instantiate env b (to_generic a) = instantiate env b a)).
        { intros a Ha. pose proof (vsize_below m c args a Ha).
          rewrite forallb_forall in Ht. destruct (IH a ltac:(lia) (Ht a Ha)) as [H1 [_ [_ H4]]]. auto. }
        repeat split; intros; simpl.
        * apply existsb_map_ext. intros a Ha. apply Hall, Ha.
        * apply existsb_map_ext. intros a Ha. apply Hall, Ha.
        * rewrite map_map. f_equal. apply map_ext_in. intros a Ha. apply Hall, Ha.
      + simpl in Hk. destruct (IH n ltac:(lia) Ht) as [H1 [H2 [H3 H4]]]. repeat split; intros; simpl; rewrite ?H1, ?H2, ?H3, ?H4; reflexivity.
      + simpl in Hk. destruct (IH n ltac:(lia) Ht) as [H1 [H2 [H3 H4]]].
        repeat split; intros; simpl; rewrite ?H1, ?H2, ?H3, ?H4; reflexivity.
      + repeat split; reflexivity.
Qed.

Lemma instantiate_to_generic: forall b t, no_generics t = true -> instantiate env b (to_generic t) = instantiate env b t.
Proof. intros b t H. exact (proj2 (proj2 (proj2 (to_generic_facts (vsize t) t (le_n _) H))) b). Qed.

Lemma mentions_to_generic: forall b t, no_generics t = true -> mentions_loosely_bound b (to_generic t) = mentions_loosely_bound b t.
Proof. intros b t H. exact (proj1 (to_generic_facts (vsize t) t (le_n _) H) b). Qed.

Lemma loose_to_generic: forall a, is_loose (to_generic a) = is_loose a.
Proof. intros [| | | |v o n| |]; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Supertypes of types with type variables                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Section Templates.

Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> is_type_argument y = true.

(* Templates are loose where they are instantiated with ys exactly where with ys mapped by a function
   that keeps type arguments loose or not *)
Lemma template_looseness_map: forall (f: EType -> EType),
    (forall y, In y ys -> is_loose (f y) = is_loose y) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        mentions_loosely_bound (bindings_of env sub (map f ys)) t = mentions_loosely_bound (bindings_of env sub ys) t)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        mentions_loosely_bound (bindings_of env sub (map f ys)) r = mentions_loosely_bound (bindings_of env sub ys) r).
Proof.
    intros f Hf k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        existsb (mentions_loosely_bound (bindings_of env sub (map f ys))) targs
        = existsb (mentions_loosely_bound (bindings_of env sub ys)) targs).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs]. apply existsb_ext_in.
      intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite !mentions_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite !mentions_nullable, !mentions_class. exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map f ys) i = Some (f y)) by (rewrite nth_error_map, Hy; reflexivity).
        rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub _ i p _ Hi Hy')).
        rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub ys i p y Hi Hy)).
        apply Hf. eapply nth_error_In. exact Hy.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn'].
Qed.

(* A template, instantiated with ys: with type variables as type parameters, it is instantiated with
   ys as type parameters; it has no type parameters but those in ys, and Nothing as bottom type if
   ys do *)
Lemma template_bridge: forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        to_generic (instantiate env (bindings_of env sub ys) t) = instantiate env (bindings_of env sub (map to_generic ys)) t
        /\ ((forall y, In y ys -> no_generics y = true) -> no_generics (instantiate env (bindings_of env sub ys) t) = true)
        /\ (nothing_is_bottom t = true -> (forall y, In y ys -> nothing_is_bottom y = true) ->
            nothing_is_bottom (instantiate env (bindings_of env sub ys) t) = true))
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        to_generic (instantiate env (bindings_of env sub ys) r) = instantiate env (bindings_of env sub (map to_generic ys)) r
        /\ ((forall y, In y ys -> no_generics y = true) -> no_generics (instantiate env (bindings_of env sub ys) r) = true)
        /\ (nothing_is_bottom r = true -> (forall y, In y ys -> nothing_is_bottom y = true) ->
            nothing_is_bottom (instantiate env (bindings_of env sub ys) r) = true)).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    set (bS := bindings_of env sub ys). set (bG := bindings_of env sub (map to_generic ys)).
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        to_generic (instantiate env bS (RootResolved m c targs)) = instantiate env bG (RootResolved m c targs)
        /\ ((forall y, In y ys -> no_generics y = true) -> no_generics (instantiate env bS (RootResolved m c targs)) = true)
        /\ (nothing_is_bottom (RootResolved m c targs) = true -> (forall y, In y ys -> nothing_is_bottom y = true) ->
            nothing_is_bottom (instantiate env bS (RootResolved m c targs)) = true)).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      assert (Hall: forall a, In a targs -> _) by (intros a Ha; pose proof (argument_depth_below m c targs a Ha);
          exact (IHa a ltac:(lia) (Htargs a Ha))).
      rewrite !instantiate_class. repeat split.
      - simpl. rewrite map_map. f_equal. apply map_ext_in. intros a Ha. apply (Hall a Ha).
      - intros Hng. change (forallb no_generics (map (instantiate env bS) targs) = true).
        apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        apply (Hall a Ha), Hng.
      - intros Hn Hny. destruct (nothing_is_bottom_root m c targs Hn) as [Hc Hnargs].
        simpl. apply andb_true_iff. split.
        + destruct (class_eqb c nothing) eqn:Ec; [|reflexivity].
          specialize (Hc eq_refl). destruct m as [[]|], targs; simpl in Hc; try discriminate Hc. reflexivity.
        + apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
          apply (Hall a Ha); [apply Hnargs, Ha|exact Hny]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. destruct (Hroot m c targs ltac:(lia) Ht') as [H1 [H2 H3]].
        rewrite instantiate_nullable_class, <- instantiate_class in *. rewrite (instantiate_nullable_class env bG), <- instantiate_class.
        repeat split.
        * simpl. f_equal. exact H1.
        * exact H2.
        * exact H3.
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map to_generic ys) i = Some (to_generic y)) by (rewrite nth_error_map, Hy; reflexivity).
        pose proof (Hys y (nth_error_In _ _ Hy)) as Hty.
        unfold bS, bG. rewrite (selects env wf sub ys p bp i y Hi Hy Hty).
        rewrite (selects env wf sub _ p bp i _ Hi Hy'); [|destruct y; try discriminate Hty; reflexivity].
        split; [reflexivity|split]; [intros H|intros _ H]; apply H; eapply nth_error_In; exact Hy.
      + simpl in Hd. destruct (IHt n ltac:(lia) Hn') as [H1 [H2 H3]].
        unfold bS, bG in *.
        rewrite (instantiate_template_argument env (bindings_of env sub ys) v o n Ho (template_shape env sub n Hn')).
        rewrite (instantiate_template_argument env (bindings_of env sub (map to_generic ys)) v o n Ho (template_shape env sub n Hn')).
        rewrite (proj1 (template_looseness_map to_generic (fun y _ => loose_to_generic y) (depth n)) n (le_n _) Hn').
        destruct (mentions_loosely_bound (bindings_of env sub ys) n); [destruct v|]; cbn [to_generic no_generics nothing_is_bottom];
            rewrite ?H1; repeat split; try reflexivity; intros; first [apply H2; assumption|apply H3; assumption].
Qed.

(* A template, instantiated with types without type parameters, has none *)
Lemma template_closed: forall k, (forall y, In y ys -> closed y = true) ->
    (forall t, depth t <= k -> template_type env sub t = true -> closed (instantiate env (bindings_of env sub ys) t) = true)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> closed (instantiate env (bindings_of env sub ys) r) = true).
Proof.
    intros k Hc. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        closed (instantiate env (bindings_of env sub ys) (RootResolved m c targs)) = true).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs]. rewrite instantiate_class.
      change (forallb closed (map (instantiate env (bindings_of env sub ys)) targs) = true). apply forallb_forall.
      intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (argument_depth_below m c targs a Ha).
      apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class, <- instantiate_class.
        exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        rewrite (selects env wf sub ys p bp i y Hi Hy (Hys y (nth_error_In _ _ Hy))). apply Hc. eapply nth_error_In. exact Hy.
      + simpl in Hd. rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn')).
        destruct (mentions_loosely_bound _ n); [destruct v|]; cbn [closed]; rewrite Ho; cbn [negb andb];
            first [reflexivity | apply IHt; [lia|exact Hn']].
Qed.

End Templates.

(* The type arguments of a supertype, normalized from those of a subclass with type variables, with
   type variables as type parameters *)
Lemma supertype_arguments_to_generic: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> is_type_argument y = true) ->
    parameterized_supertype_arguments env sub (map to_generic ys) super = map to_generic (parameterized_supertype_arguments env sub ys super)
    /\ ((forall y, In y ys -> no_generics y = true) ->
        forall a, In a (parameterized_supertype_arguments env sub ys super) -> no_generics a = true)
    /\ ((forall y, In y ys -> nothing_is_bottom y = true) ->
        forall a, In a (parameterized_supertype_arguments env sub ys super) -> nothing_is_bottom a = true)
    /\ ((forall y, In y ys -> closed y = true) ->
        forall a, In a (parameterized_supertype_arguments env sub ys super) -> closed a = true).
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite !parameterized_supertype_arguments_eq. repeat split.
    - rewrite map_map. apply map_ext_in. intros r Hr. symmetry.
      exact (proj1 (proj2 (template_bridge sub ys Hl Hys (argument_depth r)) r (le_n _) (Ht r Hr))).
    - intros Hng a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      exact (proj1 (proj2 (proj2 (template_bridge sub ys Hl Hys (argument_depth r)) r (le_n _) (Ht r Hr))) Hng).
    - intros Hnb a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      exact (proj2 (proj2 (proj2 (template_bridge sub ys Hl Hys (argument_depth r)) r (le_n _) (Ht r Hr)))
          (supertypes_mention_nothing_as_bottom sub super r Hr) Hnb).
    - intros Hc a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      exact (proj2 (template_closed sub ys Hl Hys (argument_depth r) Hc) r (le_n _) (Ht r Hr)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The fragment                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Definition argument_ifrag (a: EType): bool := match a with TypeArgument _ _ n => ifrag n | _ => false end.

Lemma ifrag_cases: forall t, ifrag t = true ->
    (exists m c args, t = RootResolved m c args /\ class_eqb c nothing = false
        /\ length args = length (parameter_ids env c) /\ forall a, In a args -> argument_ifrag a = true)
    \/ t = bottom_type
    \/ (exists m c args, t = Nullable (RootResolved m c args) /\ ifrag (RootResolved m c args) = true)
    \/ (exists p bound, t = TypeVariable (mkGenericRef None p bound) /\ sfrag env bound = true /\ closed bound = true).
Proof.
    intros t H. unfold ifrag in H. apply andb_true_iff in H. destruct H as [Hs Hn].
    destruct t as [m c args|n|[gm0 p0 bnd0]|m msg|v o n|[[gm|] p bnd]|cs]; simpl in Hn; try discriminate Hn;
        try (simpl in Hs; discriminate Hs).
    - destruct (sfrag_cases env _ Hs) as [[m' [c' [args' [Heq [Hc [Hl Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
          try discriminate Heq.
      + injection Heq as <- <- Hargs'. left. exists m, c, args. split; [reflexivity|]. split; [exact Hc|].
        split; [rewrite <- Hargs', length_map in Hl; exact Hl|].
        intros a Ha. assert (Ha': argument_sfrag env (to_generic a) = true)
            by (apply Hargs; rewrite <- Hargs'; apply in_map, Ha).
        rewrite forallb_forall in Hn. pose proof (Hn a Ha) as Hna.
        destruct a as [| | | |v o n| |]; simpl in Ha', Hna |- *; try discriminate Ha'.
        unfold ifrag. rewrite Ha', Hna. reflexivity.
      + unfold bottom_type in Heq. injection Heq as -> -> Hargs'. destruct args; [|discriminate Hargs'].
        right. left. reflexivity.
    - change (is_class (to_generic n) && sfrag env (to_generic n) = true) in Hs. apply andb_true_iff in Hs. destruct Hs as [Hc Hs].
      destruct n as [m c args| | | | | |]; try discriminate Hc.
      right. right. left. exists m, c, args. split; [reflexivity|]. unfold ifrag. rewrite Hs, Hn. reflexivity.
    - right. right. right. exists p, bnd. change (sfrag env bnd && closed bnd = true) in Hs. apply andb_true_iff in Hs.
      split; [reflexivity|exact Hs].
Qed.

Lemma ifrag_root_args: forall m c args, ifrag (RootResolved m c args) = true ->
    no_generics (RootResolved m c args) = true /\ forall a, In a args -> no_generics a = true.
Proof.
    intros m c args H. unfold ifrag in H. apply andb_true_iff in H. destruct H as [_ H]. split; [exact H|].
    change (forallb no_generics args = true) in H. apply forallb_forall, H.
Qed.

Lemma ifrag_no_generics: forall t, ifrag t = true -> no_generics t = true.
Proof. intros t H. unfold ifrag in H. apply andb_true_iff in H. apply H. Qed.

Lemma ifrag_sfrag: forall t, ifrag t = true -> sfrag env (to_generic t) = true.
Proof. intros t H. unfold ifrag in H. apply andb_true_iff in H. apply H. Qed.

Lemma afrag_parts: forall t, afrag t = true -> in_fragment env t = true /\ nothing_is_bottom t = true.
Proof. intros t H. unfold afrag in H. apply andb_true_iff in H. exact H. Qed.

Lemma top_in_afrag: afrag top_type = true.
Proof. unfold afrag. rewrite (top_in_fragment env wf). reflexivity. Qed.

Lemma bottom_in_afrag: afrag bottom_type = true.
Proof. unfold afrag. rewrite (bottom_in_fragment env wf). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Without type variables, the variable states don't matter                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma fold_of_pairs: forall n (targs aargs: list EType) s',
    Forall2 (fun a t => unify env n t a (Ongoing s') = Some (Ongoing s')) aargs targs ->
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s') = Some (Ongoing s').
Proof.
    intros n targs aargs s' H. revert targs H. induction aargs as [|a aargs IH]; intros targs H; inversion H; subst; [reflexivity|].
    simpl. match goal with E: unify env n ?t a _ = _ |- _ => rewrite E end. apply IH. assumption.
Qed.

Lemma states_irrelevant: forall n,
    (forall t a s s', in_fragment env t = true -> in_fragment env a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s'))
    /\ (forall t a s s', argument_in_fragment env t = true -> argument_in_fragment env a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s')).
Proof.
    induction n as [|n [IHt IHa]]; [split; intros t a s s' _ _ H; discriminate H|].
    split.
    - intros t a s s' Ht Ha H.
      destruct (fragment_cases env t Ht) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> Ht']]]]];
      destruct (fragment_cases env a Ha) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> Ha']]]]];
          try (rewrite unify_class_nullable in H |- *; discriminate H).
      + destruct (root_in_fragment env _ _ _ Ht) as [Hlt Htargs]. destruct (root_in_fragment env _ _ _ Ha) as [Hla Haargs].
        rewrite unify_classes in H |- *.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hb; [|discriminate H].
        destruct (Model.is_subtype_of _ _); [|discriminate H].
        destruct (class_eqb ca nothing) eqn:Hcn; [reflexivity|].
        assert (Hfold: forall aargs', length aargs' = length targs -> (forall x, In x aargs' -> argument_in_fragment env x = true) ->
            unify_arguments (unify env n) targs aargs' s = Some (Ongoing s) ->
            unify_arguments (unify env n) targs aargs' s' = Some (Ongoing s')).
        { intros aargs' Hl' Hf' E. pose proof (pairwise_of_arguments env n targs aargs' s ltac:(lia)
              (fun t0 a0 w Ht0 Ha0 E0 => proj2 (keeps_states_with_arguments env wf n) t0 a0 s w (Htargs t0 Ht0) (Hf' a0 Ha0) E0) E) as Hp.
          unfold unify_arguments. apply fold_of_pairs.
          apply (Forall2_impl_in _ _ _ _ Hp). intros a0 t0 Ha0 Ht0 E0. exact (IHa t0 a0 s s' (Htargs t0 Ht0) (Hf' a0 Ha0) E0). }
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        * rewrite class_eqb_refl in H |- *. apply Hfold; [lia|exact Haargs|exact H].
        * rewrite (class_eqb_false _ _ Hne) in H |- *.
          destruct (supertype_arguments_in_fragment env wf ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hb Hla Haargs) as [Hln Hfn].
          apply Hfold; [lia|exact Hfn|exact H].
      + rewrite unify_nullable_class in H |- *. exact (IHt _ _ s s' Ht' Ha H).
      + rewrite unify_nullable_nullable in H |- *. exact (IHt _ _ s s' Ht' Ha' H).
    - intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' Ht Ha H; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha.
      rewrite (unify_type_arguments env n vt ot nt va oa na s (fragment_not_variable env nt Ht)) in H.
      rewrite (unify_type_arguments env n vt ot nt va oa na s' (fragment_not_variable env nt Ht)).
      destruct (ownership_is_assignable_to oa ot); [|discriminate H].
      destruct vt, va; unfold compare_variances in H |- *; try discriminate H.
      1: { apply (both_ways (unify env n) nt na s) in H;
               [|apply unify_keeps_failure|intros w; exact (proj1 (keeps_states_with_arguments env wf n) nt na s w Ht Ha)].
           destruct H as [H1 H2]. rewrite (IHt nt na s s' Ht Ha H1). exact (IHt na nt s s' Ha Ht H2). }
      all: first
          [ exact (IHt _ _ s s' Ht Ha H) | exact (IHt _ _ s s' Ha Ht H)
          | exact (IHt _ _ s s' Ht (top_in_fragment env wf) H) | exact (IHt _ _ s s' (bottom_in_fragment env wf) Ht H) ].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Type variables bound exactly                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Section Exact.

(* The types the type variables are replaced with (exact type arguments), the fuel with which they
   are within the bounds of the type parameters and the type arguments the variables are bound to,
   and the variable states of the unification *)
Variable b: Bindings.
Variable K: nat.
Variable s: VariableStates.

(* Each type variable replaced is bound exactly, to a type argument that stands for its replacement *)
Hypothesis Hcover: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    exists st vb ob X, lookup_state s p = Some st /\ is_exact st = true
        /\ upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
        /\ in_fragment env X = true
        /\ unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s).
Hypothesis Hbf: bindings_in_fragment env b.

Definition inst (t: EType): EType := inst_nested env b (to_generic t).

Lemma inst_root: forall m c args, no_generics (RootResolved m c args) = true ->
    inst (RootResolved m c args) = RootResolved m c (map (instantiate env b) args).
Proof.
    intros m c args H. unfold inst. change (instantiate env b (to_generic (RootResolved m c args)) = RootResolved m c (map (instantiate env b) args)).
    rewrite (instantiate_to_generic b _ H). apply instantiate_class.
Qed.

Lemma inst_nullable: forall m c args, no_generics (RootResolved m c args) = true ->
    inst (Nullable (RootResolved m c args)) = Nullable (RootResolved m c (map (instantiate env b) args)).
Proof.
    intros m c args H. unfold inst. change (instantiate env b (to_generic (Nullable (RootResolved m c args))) = Nullable (RootResolved m c (map (instantiate env b) args))).
    rewrite (instantiate_to_generic b (Nullable (RootResolved m c args)) H). apply instantiate_nullable_class.
Qed.

Lemma inst_variable: forall p bound v o x, lookup_binding b p = Some (TypeArgument v o x) ->
    inst (TypeVariable (mkGenericRef None p bound)) = x.
Proof. intros p bound v o x H. unfold inst. simpl. rewrite H. reflexivity. Qed.

Lemma instantiate_argument: forall v o n, ifrag n = true -> bound_in env b K s (to_generic n) = true ->
    instantiate env b (TypeArgument v o n) = TypeArgument v (instantiate_ownership b o) (inst n).
Proof.
    intros v o n Hn Hb. rewrite <- (instantiate_to_generic b (TypeArgument v o n)) by exact (ifrag_no_generics n Hn).
    exact (instantiate_bound_argument env b K s v o (to_generic n) (ifrag_sfrag n Hn) Hb).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify, one step                                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma unify_type_arguments_exact: forall n vt ot nt va oa na,
    capturable nt s = None ->
    unify env (S n) (TypeArgument vt ot nt) (TypeArgument va oa na) (Ongoing s) =
    if ownership_is_assignable_to oa ot then compare_variances (unify env n) vt va nt na s else Some Failed.
Proof.
    intros n vt ot nt va oa na Hc. rewrite unify_step_once. unfold unify_step, unify_type_argument. cbn beta iota zeta.
    destruct (ownership_is_assignable_to oa ot); [|reflexivity]. rewrite Hc. destruct vt, va; reflexivity.
Qed.

Lemma bound_variable: forall p bound, bound_in env b K s (Generic (mkGenericRef None p bound)) = true ->
    exists o x st vb ob X, lookup_binding b p = Some (TypeArgument Model.invariant o x) /\ in_fragment env x = true
        /\ lookup_state s p = Some st /\ is_exact st = true
        /\ upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X /\ in_fragment env X = true
        /\ unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s).
Proof.
    intros p bound H. simpl in H. destruct (binds_exactly_some env b K s p bound H) as [o [x [E _]]]. pose proof (Hbf p o x E) as Hx.
    destruct (Hcover p o x E) as [st [vb [ob [X [Hl [He [Hu [Hlo [HX Hc]]]]]]]]].
    exists o, x, st, vb, ob, X. repeat split; assumption.
Qed.

Lemma variable_not_capturable: forall p bound st, lookup_state s p = Some st -> is_exact st = true ->
    capturable (TypeVariable (mkGenericRef None p bound)) s = None.
Proof. intros p bound st Hl He. simpl. rewrite Hl, He, andb_false_r. reflexivity. Qed.

Lemma ifrag_not_capturable: forall t, ifrag t = true -> bound_in env b K s (to_generic t) = true -> capturable t s = None.
Proof.
    intros t Ht Hb. destruct (ifrag_cases t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [bound [-> _]]]]]];
        try reflexivity.
    destruct (bound_variable p bound Hb) as [o [x [st [vb [ob [X [_ [_ [Hl [He _]]]]]]]]]].
    exact (variable_not_capturable p bound st Hl He).
Qed.

(* A type variable bound exactly as the target: its binding *)
Lemma unify_variable_target: forall n p bound st A u, lookup_state s p = Some st -> is_exact st = true ->
    in_fragment env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None p bound)) A (Ongoing s) = Some (Ongoing u) ->
    unify env n (lower_bound st) A (Ongoing s) = Some (Ongoing u).
Proof.
    intros n p bound st A u Hl He HA H. rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_type_variable, plus_supertype_constraint in H.
    - rewrite Hl, He in H. exact H.
    - destruct (is_nullable _); [|discriminate H]. rewrite Hl, He in H. exact H.
Qed.

(* ... and as the assignee *)
Lemma unify_variable_assignee: forall n p bound st A u, lookup_state s p = Some st -> is_exact st = true ->
    in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef None p bound)) (Ongoing s) = Some (Ongoing u) ->
    unify env n A (upper_bound st) (Ongoing s) = Some (Ongoing u).
Proof.
    intros n p bound st A u Hl He HA H. rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_root_resolved, unify_nullable, type_variable_flipped_unify, plus_subtype_constraint in H;
        rewrite Hl, He in H; exact H.
Qed.

(* A value assigned to a type argument, and a type argument assigned to a reference *)
Lemma unify_value_argument: forall n A v o t, in_fragment env A = true ->
    unify env (S n) A (TypeArgument v o t) (Ongoing s) = unify env n A (read_type v t) (Ongoing s).
Proof. intros n A v o t HA. destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

Lemma unify_argument_with_value: forall n v o t V, in_fragment env V = true ->
    unify env (S n) (TypeArgument v o t) V (Ongoing s) =
    if Variance_beq v output then (if is_non_nullable_nothing env V then Some (Ongoing s) else Some Failed)
    else unify env n t V (Ongoing s).
Proof.
    intros n v o t V HV. destruct (fragment_cases env V HV) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; destruct v; reflexivity.
Qed.

Lemma keeps: forall n t a u, in_fragment env t = true -> in_fragment env a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s.
Proof. intros n t a u Ht Ha H. exact (proj1 (keeps_states_with_arguments env wf n) t a s u Ht Ha H). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The type a variable stands for, where the variable is assigned to or assigned                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* Whatever can be assigned to the type argument, a variable is bound to, can be assigned to each of
   the types it stands for *)
Lemma write_leaf: forall n vb ob X o x A u, in_fragment env X = true -> in_fragment env x = true -> afrag A = true ->
    unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s) ->
    unify env n (TypeArgument vb ob X) A (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (n + K + 1) x A (Ongoing s) = Some (Ongoing s).
Proof.
    intros n vb ob X o x A u HX Hx HA Hc H. destruct (afrag_parts A HA) as [HA' HAn].
    destruct n as [|n]; [discriminate H|].
    rewrite (unify_type_arguments env K vb ob X Model.invariant o x s (fragment_not_variable env X HX)) in Hc.
    destruct (ownership_is_assignable_to o ob); [|discriminate Hc].
    rewrite (unify_argument_with_value n vb ob X A HA') in H.
    destruct vb; cbn [Variance_beq] in H.
    - (* invariant: x is X *)
      unfold compare_variances in Hc. apply (both_ways (unify env K) X x s) in Hc;
          [|apply unify_keeps_failure|intros w; exact (keeps K X x w HX Hx)].
      destruct Hc as [_ Hc]. pose proof (keeps n X A u HX HA' H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (n + K)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (n + K)) A X x n K s (le_n _) HA' HX Hx H Hc).
    - (* in: x is above X *)
      unfold compare_variances in Hc. pose proof (keeps n X A u HX HA' H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (n + K)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (n + K)) A X x n K s (le_n _) HA' HX Hx H Hc).
    - (* out: nothing but Nothing, which is the bottom type *)
      destruct (is_non_nullable_nothing env A) eqn:En; [|discriminate H]. injection H as <-. split; [reflexivity|].
      destruct (fragment_cases env A HA') as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; [|discriminate En].
      simpl in En. apply class_eqb_true in En. subst c.
      destruct (nothing_is_bottom_root m nothing args HAn) as [Hb _]. specialize (Hb (class_eqb_refl nothing)).
      destruct m as [[]|], args; simpl in Hb; try discriminate Hb.
      apply (below_all env wf s x); [exact Hx|lia].
Qed.

(* Whatever the type argument a variable is bound to can be assigned to, each of the types it stands
   for can be assigned to *)
Lemma read_leaf: forall n vb ob X o x A u, in_fragment env X = true -> in_fragment env x = true -> in_fragment env A = true ->
    unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing s) = Some (Ongoing s) ->
    unify env n A (TypeArgument vb ob X) (Ongoing s) = Some (Ongoing u) ->
    u = s /\ unify env (n + K + 1) A x (Ongoing s) = Some (Ongoing s).
Proof.
    intros n vb ob X o x A u HX Hx HA Hc H.
    destruct n as [|n]; [discriminate H|].
    rewrite (unify_type_arguments env K vb ob X Model.invariant o x s (fragment_not_variable env X HX)) in Hc.
    destruct (ownership_is_assignable_to o ob); [|discriminate Hc].
    rewrite (unify_value_argument n A vb ob X HA) in H.
    destruct vb; cbn [read_type] in H; unfold compare_variances in Hc.
    - apply (both_ways (unify env K) X x s) in Hc; [|apply unify_keeps_failure|intros w; exact (keeps K X x w HX Hx)].
      destruct Hc as [Hc _]. pose proof (keeps n A X u HA HX H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (K + n)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (K + n)) x X A K n s (le_n _) Hx HX HA Hc H).
    - (* in: reads as read Any?, which is above everything *)
      pose proof (keeps n A top_type u HA (top_in_fragment env wf) H) as ->. split; [reflexivity|].
      apply (above_top env wf n A s HA H x); [exact Hx|lia].
    - pose proof (keeps n A X u HA HX H) as ->. split; [reflexivity|].
      apply (unify_fuel_monotone env (K + n)); [lia|].
      exact (proj1 (transitivity_with_arguments env wf (K + n)) x X A K n s (le_n _) Hx HX HA Hc H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Supertypes, and pairs of type arguments                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma supertype_commute_variables: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) ->
    (forall y, In y ys -> argument_ifrag y = true /\ bound_in env b K s (to_generic y) = true) ->
    parameterized_supertype_arguments env sub (map (instantiate env b) ys) super
        = map (instantiate env b) (parameterized_supertype_arguments env sub ys super)
    /\ forall a, In a (parameterized_supertype_arguments env sub ys super) ->
        argument_ifrag a = true /\ bound_in env b K s (to_generic a) = true.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    assert (Hta: forall y, In y ys -> is_type_argument y = true)
        by (intros y Hy; destruct (Hys y Hy) as [H _]; destruct y; try discriminate H; reflexivity).
    assert (Hng: forall y, In y ys -> no_generics y = true)
        by (intros y Hy; destruct (Hys y Hy) as [H _]; destruct y as [| | | |v o n| |]; try discriminate H;
            exact (ifrag_no_generics n H)).
    destruct (supertype_arguments_to_generic sub super ys Hne Hn Hbase Hl Hta) as [Htg [Hng' _]].
    assert (Hys': forall y, In y (map to_generic ys) -> argument_sfrag env y = true /\ bound_in env b K s y = true).
    { intros y' Hy'. apply in_map_iff in Hy'. destruct Hy' as [y [<- Hy]]. destruct (Hys y Hy) as [Hf Hb]. split; [|exact Hb].
      destruct y as [| | | |v o n| |]; try discriminate Hf. exact (ifrag_sfrag n Hf). }
    destruct (supertype_arguments_commute env wf supertypes_mention_nothing_as_bottom b K s sub super (map to_generic ys)
        Hne Hn Hbase ltac:(rewrite length_map; exact Hl) Hys') as [Hcomm Hnorm].
    split.
    - replace (map (instantiate env b) ys) with (map (instantiate env b) (map to_generic ys))
          by (rewrite map_map; apply map_ext_in; intros y Hy; apply instantiate_to_generic, Hng, Hy).
      rewrite Hcomm, Htg, map_map. apply map_ext_in. intros a Ha. apply instantiate_to_generic, (Hng' Hng a Ha).
    - intros a Ha. rewrite Htg in Hnorm. destruct (Hnorm (to_generic a) (in_map _ _ _ Ha)) as [Hf Hb]. split; [|exact Hb].
      pose proof (Hng' Hng a Ha) as Hna. destruct a as [| | | |v o n| |]; try discriminate Hf.
      simpl in Hf, Hna. unfold argument_ifrag, ifrag. rewrite Hf, Hna. reflexivity.
Qed.

Lemma fold_map: forall n n' (f g: EType -> EType) targs aargs u,
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing u) ->
    (forall t a u0, In t targs -> In a aargs -> unify env n t a (Ongoing s) = Some (Ongoing u0) ->
        u0 = s /\ unify env n' (f t) (g a) (Ongoing s) = Some (Ongoing s)) ->
    u = s /\ fold_unify (fun inner '(t, a) => unify env n' t a inner) (combine (map f targs) (map g aargs)) (Ongoing s)
        = Some (Ongoing s).
Proof.
    intros n n' f g targs. induction targs as [|t targs IH]; intros aargs u H Hpair;
        destruct aargs as [|a aargs]; simpl in *; try (injection H as <-; auto).
    destruct (unify env n t a (Ongoing s)) as [[s1|]|] eqn:E1; try discriminate H.
    - destruct (Hpair t a s1 (or_introl eq_refl) (or_introl eq_refl) E1) as [-> Hinst].
      rewrite Hinst. apply (IH aargs u H). intros t' a' u0 Ht Ha. apply Hpair; right; assumption.
    - rewrite fold_stays_failed in H. discriminate H.
Qed.

(* The parts of a class type of the fragment *)
Lemma root_parts: forall m c args, ifrag (RootResolved m c args) = true ->
    bound_in env b K s (to_generic (RootResolved m c args)) = true ->
    forall a, In a args -> argument_ifrag a = true /\ bound_in env b K s (to_generic a) = true.
Proof.
    intros m c args Hf Hb a Ha. split.
    - destruct (ifrag_cases _ Hf) as [[m' [c' [args' [Heq [_ [_ Hargs]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
          try discriminate Heq.
      + injection Heq as <- <- <-. exact (Hargs a Ha).
      + unfold bottom_type in Heq. injection Heq as _ _ ->. destruct Ha.
    - apply (bound_in_root env b K s m c (map to_generic args) Hb). apply in_map, Ha.
Qed.

Lemma closed_parts: forall m c args, closed (RootResolved m c args) = true -> forall a, In a args -> closed a = true.
Proof. intros m c args H. change (forallb closed args = true) in H. apply forallb_forall, H. Qed.

Lemma closed_argument: forall v o n, closed (TypeArgument v o n) = true -> is_parameter_ownership o = false /\ closed n = true.
Proof.
    intros v o n H. change (negb (is_parameter_ownership o) && closed n = true) in H. apply andb_true_iff in H.
    destruct H as [Ho Hn]. split; [destruct (is_parameter_ownership o); [discriminate Ho|reflexivity]|exact Hn].
Qed.

Lemma ownership_not_instantiated: forall o, is_parameter_ownership o = false -> instantiate_ownership b o = o.
Proof. intros [| | |p] H; [reflexivity..|discriminate H]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Soundness                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma inference_with_arguments: forall n,
    (forall P A u, ifrag P = true -> afrag A = true -> closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n P A (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) (inst P) A (Ongoing s) = Some (Ongoing s))
    /\ (forall P A u, ifrag P = true -> afrag A = true -> closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n A P (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) A (inst P) (Ongoing s) = Some (Ongoing s))
    /\ (forall P A u, argument_ifrag P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n P A (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) (instantiate env b P) A (Ongoing s) = Some (Ongoing s))
    /\ (forall P A u, argument_ifrag P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> bound_in env b K s (to_generic P) = true ->
        unify env n A P (Ongoing s) = Some (Ongoing u) ->
        u = s /\ unify env (n * S (S K) + 2) A (instantiate env b P) (Ongoing s) = Some (Ongoing s)).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A u; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    assert (HPn: n <= n * S (S K)) by (rewrite Nat.mul_succ_r; lia).
    rewrite Nat.mul_succ_l. remember (n * S (S K)) as F eqn:HF. clear HF.
    replace (F + S (S K) + 2) with (S (F + 2 + S K)) by lia.
    assert (Hmono: forall t a, unify env (F + 2) t a (Ongoing s) = Some (Ongoing s) ->
        unify env (F + 2 + S K) t a (Ongoing s) = Some (Ongoing s))
        by (intros t a E; apply (unify_fuel_monotone env (F + 2)); [lia|exact E]).
    (* the parts of the types of the arguments *)
    assert (Hargs: forall ma ca aargs, in_fragment env (RootResolved ma ca aargs) = true ->
        nothing_is_bottom (RootResolved ma ca aargs) = true -> closed (RootResolved ma ca aargs) = true ->
        length aargs = length (parameter_ids env ca) /\ forall a, In a aargs ->
            argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
    { intros ma ca aargs Hf Hn Hc. destruct (root_in_fragment env ma ca aargs Hf) as [Hl Ha]. split; [exact Hl|].
      intros a Hin. split; [exact (Ha a Hin)|]. split; [exact (proj2 (nothing_is_bottom_root ma ca aargs Hn) a Hin)|].
      exact (closed_parts ma ca aargs Hc a Hin). }
    (* the same, as normalized to a supertype *)
    assert (Hnorm: forall ca ct aargs, ca <> ct -> ca <> nothing -> base_type_is_subtype_of env ca ct = true ->
        length aargs = length (parameter_ids env ca) ->
        (forall a, In a aargs -> argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true) ->
        forall a, In a (parameterized_supertype_arguments env ca aargs ct) ->
            argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
    { intros ca ct aargs Hne Hcn Hbase Hl Ha a Hin.
      assert (Hta: forall y, In y aargs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Ha, Hy).
      destruct (supertype_arguments_to_generic ca ct aargs Hne Hcn Hbase Hl Hta) as [_ [_ [Hnb Hcl]]].
      destruct (supertype_arguments_in_fragment env wf ca ct aargs Hne Hcn Hbase Hl (fun y Hy => proj1 (Ha y Hy))) as [_ Hf].
      split; [exact (Hf a Hin)|]. split; [apply Hnb; [intros y Hy; apply Ha, Hy|exact Hin]|apply Hcl; [intros y Hy; apply Ha, Hy|exact Hin]]. }
    split; [|split; [|split]].
    - (* a type with type variables as the target *)
      intros P A u HP HA HcA Hb H. destruct (afrag_parts A HA) as [HA' HAn].
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag (RootResolved mt ct targs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K s (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (F + 2 + S K)) (inst (RootResolved mt ct targs)) (RootResolved ma ca aargs) (Ongoing s)
              = Some (Ongoing s)).
      { intros mt ct targs ma ca aargs Hft Hfa Hna Hca Hbt Hu.
        rewrite (inst_root mt ct targs (ifrag_no_generics _ Hft)).
        pose proof (root_parts mt ct targs Hft Hbt) as Htargs.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [Hla Haargs].
        rewrite unify_classes in Hu |- *.
        rewrite (mutability_of_class env mt ct (map (instantiate env b) targs) targs).
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _); [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn; [injection Hu as <-; auto|].
        unfold unify_arguments in Hu |- *.
        assert (Hpair: forall aargs', (forall a, In a aargs' -> argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true) ->
            fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs') (Ongoing s) = Some (Ongoing u) ->
            u = s /\ fold_unify (fun inner '(t, a) => unify env (F + 2 + S K) t a inner)
                (combine (map (instantiate env b) targs) aargs') (Ongoing s) = Some (Ongoing s)).
        { intros aargs' Ha' Hf. rewrite <- (map_id aargs').
          apply (fold_map n (F + 2 + S K) (instantiate env b) (fun a => a) targs aargs' u Hf).
          intros t a u0 Ht Ha E. destruct (Htargs t Ht) as [Hft' Hbt']. destruct (Ha' a Ha) as [Hfa' [Hna' Hca']].
          destruct (IHat t a u0 Hft' Hfa' Hna' Hca' Hbt' E) as [-> Hi]. split; [reflexivity|exact (Hmono _ _ Hi)]. }
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        - rewrite class_eqb_refl in Hu |- *. exact (Hpair aargs Haargs Hu).
        - rewrite (class_eqb_false _ _ Hne) in Hu |- *.
          exact (Hpair _ (Hnorm ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs) Hu). }
      destruct (ifrag_cases P HP) as [[mt [ct [targs [-> _]]]]|[->|[[mt [ct [targs [-> HP']]]]|[p [bnd [-> [Hfb Hcb]]]]]]];
          [| unfold bottom_type in * | |].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + rewrite (inst_nullable mt ct targs (ifrag_no_generics _ HP')).
        assert (Hb': bound_in env b K s (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
        destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]].
        * rewrite unify_nullable_class in H |- *.
          destruct (IHt _ _ u HP' HA HcA Hb' H) as [-> Hi]. split; [reflexivity|].
          rewrite (inst_root mt ct targs (ifrag_no_generics _ HP')) in Hi. exact (Hmono _ _ Hi).
        * rewrite unify_nullable_nullable in H |- *.
          assert (HA2: afrag (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
          destruct (IHt _ _ u HP' HA2 HcA Hb' H) as [-> Hi]. split; [reflexivity|].
          rewrite (inst_root mt ct targs (ifrag_no_generics _ HP')) in Hi. exact (Hmono _ _ Hi).
      + (* a type variable: the type it stands for takes what its binding takes *)
        destruct (bound_variable p bnd Hb) as [o [x [st [vb [ob [X [Ex [Hx [Hl [He [Hup [Hlo [HX Hc]]]]]]]]]]]]].
        apply (unify_variable_target n p bnd st A u Hl He HA') in H. rewrite Hlo in H.
        destruct (write_leaf n vb ob X o x A u HX Hx HA Hc H) as [-> Hw]. split; [reflexivity|].
        rewrite (inst_variable p bnd _ _ _ Ex). apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hw].
    - (* a type with type variables as the assignee *)
      intros P A u HP HA HcA Hb H. destruct (afrag_parts A HA) as [HA' HAn].
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag (RootResolved mp cp pargs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K s (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing u) ->
          u = s /\ unify env (S (F + 2 + S K)) (RootResolved ma ca aargs) (inst (RootResolved mp cp pargs)) (Ongoing s)
              = Some (Ongoing s)).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hna Hca Hbp Hu.
        rewrite (inst_root mp cp pargs (ifrag_no_generics _ Hfp)).
        pose proof (root_parts mp cp pargs Hfp Hbp) as Hpargs.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [_ Haargs].
        rewrite unify_classes in Hu |- *.
        rewrite (mutability_of_class env mp cp (map (instantiate env b) pargs) pargs).
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _); [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn; [injection Hu as <-; auto|].
        unfold unify_arguments in Hu |- *.
        assert (Hpair: forall pargs', (forall a, In a pargs' -> argument_ifrag a = true /\ bound_in env b K s (to_generic a) = true) ->
            fold_unify (fun inner '(t, a) => unify env n t a inner) (combine aargs pargs') (Ongoing s) = Some (Ongoing u) ->
            u = s /\ fold_unify (fun inner '(t, a) => unify env (F + 2 + S K) t a inner)
                (combine aargs (map (instantiate env b) pargs')) (Ongoing s) = Some (Ongoing s)).
        { intros pargs' Hp' Hf. rewrite <- (map_id aargs).
          apply (fold_map n (F + 2 + S K) (fun a => a) (instantiate env b) aargs pargs' u Hf).
          intros t a u0 Ht Ha E. destruct (Hp' a Ha) as [Hfa' Hba']. destruct (Haargs t Ht) as [Hft' [Hnt' Hct']].
          destruct (IHaa a t u0 Hfa' Hft' Hnt' Hct' Hba' E) as [-> Hi]. split; [reflexivity|exact (Hmono _ _ Hi)]. }
        destruct (Class_eq_dec cp ca) as [<-|Hne].
        - rewrite class_eqb_refl in Hu |- *. exact (Hpair pargs Hpargs Hu).
        - rewrite (class_eqb_false _ _ Hne) in Hu |- *.
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          destruct (supertype_commute_variables cp ca pargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          rewrite Hcomm. exact (Hpair _ Hnormp Hu). }
      destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]];
      destruct (ifrag_cases P HP) as [[mp [cp [pargs [-> _]]]]|[->|[[mp [cp [pargs [-> HP']]]]|[p [bnd [-> [Hfb Hcb]]]]]]];
          try (unfold bottom_type in *).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H).
      + rewrite unify_class_nullable in H. discriminate H.
      + destruct (bound_variable p bnd Hb) as [o [x [st [vb [ob [X [Ex [Hx [Hl [He [Hup [Hlo [HX Hc]]]]]]]]]]]]].
        apply (unify_variable_assignee n p bnd st _ u Hl He HA') in H. rewrite Hup in H.
        destruct (read_leaf n vb ob X o x _ u HX Hx HA' Hc H) as [-> Hr]. split; [reflexivity|].
        rewrite (inst_variable p bnd _ _ _ Ex). apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hr].
      + assert (HA2: afrag (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ u HP HA2 HcA Hb H) as [-> Hi]. split; [reflexivity|].
        rewrite (inst_root mp cp pargs (ifrag_no_generics _ HP)) in Hi |- *. rewrite unify_nullable_class. exact (Hmono _ _ Hi).
      + assert (HA2: afrag (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ u HP HA2 HcA Hb H) as [-> Hi]. split; [reflexivity|].
        rewrite (inst_root _ _ _ (ifrag_no_generics _ HP)) in Hi |- *. rewrite unify_nullable_class. exact (Hmono _ _ Hi).
      + assert (HA2: afrag (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        assert (Hb': bound_in env b K s (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
        rewrite unify_nullable_nullable in H. destruct (IHa _ _ u HP' HA2 HcA Hb' H) as [-> Hi]. split; [reflexivity|].
        rewrite (inst_root mp cp pargs (ifrag_no_generics _ HP')) in Hi. rewrite (inst_nullable mp cp pargs (ifrag_no_generics _ HP')).
        rewrite unify_nullable_nullable. exact (Hmono _ _ Hi).
      + destruct (bound_variable p bnd Hb) as [o [x [st [vb [ob [X [Ex [Hx [Hl [He [Hup [Hlo [HX Hc]]]]]]]]]]]]].
        apply (unify_variable_assignee n p bnd st _ u Hl He HA') in H. rewrite Hup in H.
        destruct (read_leaf n vb ob X o x _ u HX Hx HA' Hc H) as [-> Hr]. split; [reflexivity|].
        rewrite (inst_variable p bnd _ _ _ Ex). apply (unify_fuel_monotone env (n + K + 1)); [lia|exact Hr].
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] u HP HA HAn HcA Hb H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn. destruct (bound_in_argument env b K s vt ot (to_generic nt) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (instantiate_argument vt ot nt HP Hbn).
      rewrite (unify_type_arguments_exact n vt ot nt va oa na (ifrag_not_capturable nt HP Hbn)) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      assert (Hfi: in_fragment env (inst nt) = true) by exact (instance_in_fragment env wf b K s Hbf (to_generic nt) (ifrag_sfrag nt HP) Hbn).
      rewrite (unify_type_arguments env (F + 2 + S K) vt _ (inst nt) va oa na s (fragment_not_variable env _ Hfi)).
      pose proof (instantiation_preserves_ownership_assignability b oa ot Ho) as Ho'.
      rewrite (ownership_not_instantiated oa Hoa) in Ho'. rewrite Ho'.
      destruct vt, va; unfold compare_variances in H |- *; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHt nt na w HP HAf Hcn Hbn E1) as [-> Hi1].
           destruct (IHa nt na u HP HAf Hcn Hbn H) as [-> Hi2]. split; [reflexivity|].
           rewrite (Hmono _ _ Hi1). exact (Hmono _ _ Hi2). }
      all: first
          [ destruct (IHt nt na u HP HAf Hcn Hbn H) as [-> Hi]
          | destruct (IHa nt na u HP HAf Hcn Hbn H) as [-> Hi]
          | destruct (IHt nt top_type u HP top_in_afrag eq_refl Hbn H) as [-> Hi]
          | destruct (IHa nt bottom_type u HP bottom_in_afrag eq_refl Hbn H) as [-> Hi] ];
          split; [reflexivity|exact (Hmono _ _ Hi)].
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] u HP HA HAn HcA Hb H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn. destruct (bound_in_argument env b K s vp op (to_generic np) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (instantiate_argument vp op np HP Hbn).
      rewrite (unify_type_arguments env n va oa na vp op np s (fragment_not_variable env _ HA)) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      rewrite (unify_type_arguments env (F + 2 + S K) va oa na vp _ (inst np) s (fragment_not_variable env _ HA)).
      pose proof (instantiation_preserves_ownership_assignability b op oa Ho) as Ho'.
      rewrite (ownership_not_instantiated oa Hoa) in Ho'. rewrite Ho'.
      destruct va, vp; unfold compare_variances in H |- *; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHa np na w HP HAf Hcn Hbn E1) as [-> Hi1].
           destruct (IHt np na u HP HAf Hcn Hbn H) as [-> Hi2]. split; [reflexivity|].
           rewrite (Hmono _ _ Hi1). exact (Hmono _ _ Hi2). }
      all: first
          [ destruct (IHa np na u HP HAf Hcn Hbn H) as [-> Hi]; split; [reflexivity|exact (Hmono _ _ Hi)]
          | destruct (IHt np na u HP HAf Hcn Hbn H) as [-> Hi]; split; [reflexivity|exact (Hmono _ _ Hi)]
          | match type of H with unify env ?k ?x ?y _ = _ =>
              let Hx := fresh "Hx" in let Hy := fresh "Hy" in
              assert (Hx: in_fragment env x = true) by first [exact HA|exact (top_in_fragment env wf)|exact (bottom_in_fragment env wf)];
              assert (Hy: in_fragment env y = true) by first [exact HA|exact (top_in_fragment env wf)|exact (bottom_in_fragment env wf)];
              pose proof (keeps k x y u Hx Hy H) as ->;
              split; [reflexivity|apply (unify_fuel_monotone env k); [lia|exact H]]
            end ].
Qed.

End Exact.

(* ---------------------------------------------------------------------------------------------- *)
(* Capturing the type arguments of a receiver                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* The type of the receiver parameter of a member function: its class, with the type parameters of
   the class as type variables. Kotlin has no ownership yet; any ownership takes them all. *)
Definition receiver_leaf (v: TypeParameterId * EType): EType :=
    TypeArgument Model.invariant any_ownership (TypeVariable (mkGenericRef None (fst v) (snd v))).

(* The variable states for inferring the type parameters of the class of a receiver: none bound yet,
   all may be captured *)
Definition receiver_states (vars: list (TypeParameterId * EType)): VariableStates :=
    map (fun '(p, bound) => (p, mkVariableState bound bound bottom_type false true)) vars.

Lemma receiver_states_for_inference: forall vars,
    for_inference_of vars (map fst vars) = Ongoing (receiver_states vars).
Proof.
    intros vars. unfold for_inference_of, receiver_states. f_equal. apply map_ext_in. intros [p bound] Hin.
    replace (existsb (param_eqb p) (map fst vars)) with true; [reflexivity|].
    symmetry. apply existsb_exists. exists p. split; [apply (in_map fst _ _ Hin)|apply param_eqb_refl].
Qed.

Lemma lookup_receiver_states: forall vars p bound, NoDup (map fst vars) -> In (p, bound) vars ->
    lookup_state (receiver_states vars) p = Some (mkVariableState bound bound bottom_type false true).
Proof.
    intros vars. induction vars as [|[q bq] rest IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_filter_other: forall (st: VariableStates) p q, p <> q ->
    lookup_state (filter (fun '(p', _) => negb (param_eqb p p')) st) q = lookup_state st q.
Proof.
    intros st p q Hne. induction st as [|[p' v'] rest IH]; [reflexivity|]. simpl.
    destruct (param_eqb p p') eqn:E1; simpl.
    - apply param_eqb_eq in E1. subst p'. destruct (param_eqb q p) eqn:E2; [apply param_eqb_eq in E2; congruence|exact IH].
    - destruct (param_eqb q p'); [reflexivity|exact IH].
Qed.

Lemma lookup_set_same: forall st p v, lookup_state (set_state st p v) p = Some v.
Proof. intros. unfold set_state. simpl. rewrite param_eqb_refl. reflexivity. Qed.

Lemma lookup_set_other: forall st p q v, p <> q -> lookup_state (set_state st p v) q = lookup_state st q.
Proof.
    intros st p q v Hne. unfold set_state. simpl. destruct (param_eqb q p) eqn:E; [apply param_eqb_eq in E; congruence|].
    exact (lookup_filter_other st p q Hne).
Qed.

(* One type argument of the receiver, captured *)
Lemma capture_step: forall n p bound s y u,
    lookup_state s p = Some (mkVariableState bound bound bottom_type false true) ->
    in_fragment env bound = true -> argument_in_fragment env y = true ->
    unify env n (receiver_leaf (p, bound)) y (Ongoing s) = Some (Ongoing u) ->
    u = set_state s p (mkVariableState bound y y true true).
Proof.
    intros n p bound s [| | | |vy oy Y| |] u Hl Hb Hy H; simpl in Hy; try discriminate Hy.
    destruct n as [|n]; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_type_argument, receiver_leaf in H. cbn beta iota zeta in H.
    replace (ownership_is_assignable_to oy any_ownership) with true in H by (destruct oy; reflexivity).
    cbn [negb fst snd] in H. unfold capturable in H. cbn beta iota in H. rewrite Hl in H. cbn [is_capturable is_exact negb andb] in H.
    unfold plus_exact_binding in H. rewrite Hl in H. cbn [upper_bound lower_bound static_upper_bound is_capturable] in H.
    destruct (unify env n bound Y (Ongoing s)) as [[w|]|] eqn:E1; try discriminate H.
    destruct (unify env n (TypeArgument vy oy Y) bottom_type (Ongoing s)) as [[w'|]|] eqn:E2; try discriminate H.
    injection H as <-. f_equal.
    destruct n as [|n]; [discriminate E2|].
    destruct vy; rewrite unify_step_once in E2; unfold unify_step, unify_type_argument in E2; cbn beta iota zeta in E2;
        try (injection E2 as <-; reflexivity).
    - exact (proj1 (keeps_states_with_arguments env wf n) Y bottom_type s w' Hy (bottom_in_fragment env wf) E2).
    - exact (proj1 (keeps_states_with_arguments env wf n) Y bottom_type s w' Hy (bottom_in_fragment env wf) E2).
Qed.

(* All of them *)
Lemma capture_arguments: forall n vars ys s u,
    NoDup (map fst vars) -> length ys = length vars ->
    (forall y, In y ys -> argument_in_fragment env y = true) ->
    (forall p bound, In (p, bound) vars ->
        lookup_state s p = Some (mkVariableState bound bound bottom_type false true) /\ in_fragment env bound = true) ->
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine (map receiver_leaf vars) ys) (Ongoing s) = Some (Ongoing u) ->
    (forall i p bound y, nth_error vars i = Some (p, bound) -> nth_error ys i = Some y ->
        lookup_state u p = Some (mkVariableState bound y y true true))
    /\ (forall q, ~ In q (map fst vars) -> lookup_state u q = lookup_state s q).
Proof.
    intros n vars. induction vars as [|[p bound] rest IH]; intros [|y ys] s u Hnd Hl Hys Hvars H; simpl in Hl; try discriminate Hl.
    - simpl in H. injection H as <-. split; [intros [|i]; discriminate|reflexivity].
    - inversion Hnd as [|? ? Hnotin Hnd']. subst.
      simpl in H. destruct (unify env n (receiver_leaf (p, bound)) y (Ongoing s)) as [[s1|]|] eqn:E; [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      destruct (Hvars p bound (or_introl eq_refl)) as [Hlp Hbp].
      pose proof (capture_step n p bound s y s1 Hlp Hbp (Hys y (or_introl eq_refl)) E) as ->.
      destruct (IH ys (set_state s p (mkVariableState bound y y true true)) u Hnd' ltac:(lia) (fun y' Hy' => Hys y' (or_intror Hy'))) as [IH1 IH2]; [|exact H|].
      + intros q bq Hin. destruct (Hvars q bq (or_intror Hin)) as [Hlq Hbq]. split; [|exact Hbq].
        rewrite lookup_set_other; [exact Hlq|]. intros ->. apply Hnotin. exact (in_map fst _ _ Hin).
      + split.
        * intros [|i] q bq y' Hq Hy'.
          -- simpl in Hq, Hy'. injection Hq as <- <-. injection Hy' as <-. rewrite (IH2 p Hnotin). apply lookup_set_same.
          -- exact (IH1 i q bq y' Hq Hy').
        * intros q Hq. simpl in Hq. rewrite (IH2 q (fun H' => Hq (or_intror H'))). apply lookup_set_other.
          intros ->. apply Hq. left. reflexivity.
Qed.

(* Unifying the receiver parameter with the receiver binds each type parameter of the class exactly
   to the type argument of the receiver in its place *)
Lemma receiver_captures: forall n mr c vars ma ys u,
    c <> nothing -> map fst vars = parameter_ids env c ->
    (forall p bound, In (p, bound) vars -> in_fragment env bound = true) ->
    in_fragment env (RootResolved ma c ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf vars)) (RootResolved ma c ys) (Ongoing (receiver_states vars))
        = Some (Ongoing u) ->
    forall i p bound y, nth_error vars i = Some (p, bound) -> nth_error ys i = Some y ->
        lookup_state u p = Some (mkVariableState bound y y true true).
Proof.
    intros n mr c vars ma ys u Hc Hids Hbounds Hf H. destruct n as [|n]; [discriminate H|].
    destruct (root_in_fragment env ma c ys Hf) as [Hl Hys].
    assert (Hnd: NoDup (map fst vars)) by (rewrite Hids; apply (wf_parameter_ids_are_distinct env wf)).
    rewrite unify_classes in H.
    replace (base_type_is_subtype_of env c c) with true in H by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
    destruct (Model.is_subtype_of _ _); [|discriminate H].
    rewrite (class_eqb_false c nothing Hc), class_eqb_refl in H. unfold unify_arguments in H.
    refine (proj1 (capture_arguments n vars ys (receiver_states vars) u Hnd _ Hys _ H)).
    - rewrite Hl, <- Hids, length_map. reflexivity.
    - intros p bound Hin. split; [exact (lookup_receiver_states vars p bound Hnd Hin)|exact (Hbounds p bound Hin)].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Member calls                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma bound_in_transfer: forall b K s K' s', bindings_in_fragment env b -> K <= K' -> forall k t, sdepth t <= k -> sfrag env t = true ->
    bound_in env b K s t = true -> bound_in env b K' s' t = true.
Proof.
    intros b K s K' s' Hbf HK k. induction k as [|k IH]; intros t Hd Ht Hb.
    { destruct (sfrag_cases env t Ht) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[? [? [-> _]]]]]]; simpl in Hd; lia. }
    destruct (sfrag_cases env t Ht) as [[m [c [args [-> [_ [_ Hargs]]]]]]|[->|[[m [c [args [-> Ht']]]]|[p [bound [-> [Hfb Hcb]]]]]]].
    - change (forallb (bound_in env b K' s') args = true). apply forallb_forall. intros a Ha.
      pose proof (bound_in_root env b K s m c args Hb a Ha) as Hba. pose proof (Hargs a Ha) as Hfa.
      pose proof (sdepth_below m c args a Ha) as Hda.
      destruct a as [| | | |v o n| |]; try discriminate Hfa. simpl in Hfa, Hba |- *.
      change (argument_sdepth (TypeArgument v o n)) with (S (sdepth n)) in Hda.
      apply andb_true_iff in Hba. destruct Hba as [Ho Hn]. rewrite Ho. apply IH; [lia|exact Hfa|exact Hn].
    - reflexivity.
    - assert (Hd': sdepth (RootResolved m c args) <= k) by (simpl in Hd |- *; lia). exact (IH _ Hd' Ht' Hb).
    - simpl in Hb |- *. unfold binds_exactly, respects in Hb |- *.
      destruct (lookup_binding b p) as [[| | | |[] o x| |]|] eqn:Ex; try discriminate Hb.
      apply andb_true_iff in Hb. destruct Hb as [Hb Hr]. rewrite Hb. pose proof (Hbf p o x Ex) as Hx.
      destruct (unify env K bound x (Ongoing s)) as [[w|]|] eqn:E; try discriminate Hr.
      destruct (proj1 (closed_facts env wf b K s (sdepth bound)) bound (le_n _) Hfb Hcb) as [HFb _].
      pose proof (proj1 (keeps_states_with_arguments env wf K) bound x s w HFb Hx E) as ->.
      rewrite (unify_fuel_monotone env K K' bound x (Ongoing s') (Ongoing s') HK
          (proj1 (states_irrelevant K) bound x s s' HFb Hx E)).
      reflexivity.
Qed.

Lemma lookup_combine_nth: forall (ids: list TypeParameterId) (xs: list EType) p a,
    lookup_binding (combine ids xs) p = Some a -> exists i, nth_error ids i = Some p /\ nth_error xs i = Some a.
Proof.
    intros ids. induction ids as [|q ids IH]; intros [|x xs] p a H; simpl in H; try discriminate H.
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. injection H as <-. exists 0. split; reflexivity.
    - destruct (IH xs p a H) as [i [Hi Hx]]. exists (S i). split; assumption.
Qed.

(* The type arguments of a class type of the fragment, as bindings, are of the fragment *)
Lemma bindings_of_in_fragment: forall c xs, (forall x, In x xs -> argument_in_fragment env x = true) ->
    bindings_in_fragment env (bindings_of env c xs).
Proof.
    intros c xs Hxs p o x E. destruct (lookup_combine_nth _ _ p _ E) as [i [_ Hx]].
    exact (Hxs _ (nth_error_In _ _ Hx)).
Qed.


Definition exact_argument (x: EType): bool :=
    match x with
    | TypeArgument Model.invariant o n => is_exact_ownership o && in_fragment env n
    | _ => false
    end.

(*
 * Calling a member function is sound, where the class of the receiver is the class the function is
 * declared in, and the function has no type parameters of its own: unifying the receiver parameter
 * with the receiver binds the type parameters of the class exactly to the type arguments of the
 * receiver, capturing those of a variance. Whatever argument is then accepted for a parameter fits
 * the parameter with the type parameters of the class replaced by the type arguments of the object
 * actually called on: those of any object the receiver may be. (The return value is read, as a
 * member is: see MemberAccess.member_read_sound.)
 *)
Theorem member_call_sound: forall n mr c vars ma ys u mo xs n0 K P A fuel u',
    c <> nothing -> map fst vars = parameter_ids env c ->
    (forall p bound, In (p, bound) vars -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma c ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf vars)) (RootResolved ma c ys) (Ongoing (receiver_states vars))
        = Some (Ongoing u) ->
    (* the object it is, of exact type arguments within the bounds of the type parameters *)
    length xs = length (parameter_ids env c) -> (forall x, In x xs -> exact_argument x = true) ->
    is_assignable_to env n0 (RootResolved mo c xs) (RootResolved ma c ys) = Some true ->
    (* a parameter and an argument for it, accepted *)
    ifrag P = true -> afrag A = true -> closed A = true -> bound_in env (bindings_of env c xs) K [] (to_generic P) = true ->
    unify env fuel P A (Ongoing u) = Some (Ongoing u') ->
    exists fuel', is_assignable_to env fuel' A (inst (bindings_of env c xs) P) = Some true.
Proof.
    intros n mr c vars ma ys u mo xs n0 K P A fuel u' Hc Hids Hbounds Hfy Hrec Hlx Hxs Hobj HP HA HcA Hb H.
    destruct (root_in_fragment env ma c ys Hfy) as [Hly Hys].
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true).
    { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o nx| |]; try discriminate E.
      simpl in E |- *. apply andb_true_iff in E. apply E. }
    assert (Hfo: in_fragment env (RootResolved mo c xs) = true).
    { change (Nat.eqb (length xs) (length (parameter_ids env c)) && forallb (argument_in_fragment env) xs = true).
      rewrite Hlx, Nat.eqb_refl. apply forallb_forall, Hfxs. }
    (* the type arguments of the object, assignable to those of the receiver *)
    unfold is_assignable_to, empty_unification in Hobj.
    destruct (unify env n0 (RootResolved ma c ys) (RootResolved mo c xs) (Ongoing [])) as [[w|]|] eqn:Eo; try discriminate Hobj.
    pose proof (proj1 (keeps_states_with_arguments env wf n0) _ _ [] w Hfy Hfo Eo) as ->.
    destruct n0 as [|n0]; [discriminate Eo|].
    rewrite unify_classes in Eo.
    replace (base_type_is_subtype_of env c c) with true in Eo by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
    destruct (Model.is_subtype_of _ _); [|discriminate Eo].
    rewrite (class_eqb_false c nothing Hc), class_eqb_refl in Eo.
    pose proof (pairwise_of_arguments env n0 ys xs [] ltac:(lia)
        (fun t a w0 Ht Ha E => proj2 (keeps_states_with_arguments env wf n0) t a [] w0 (Hys t Ht) (Hfxs a Ha) E) Eo) as Hp.
    (* each type variable is bound exactly, to the type argument of the receiver *)
    set (K' := K + n0).
    assert (Hcover: forall p o x, lookup_binding (bindings_of env c xs) p = Some (TypeArgument Model.invariant o x) ->
        exists st vb ob X, lookup_state u p = Some st /\ is_exact st = true
            /\ upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
            /\ in_fragment env X = true
            /\ unify env (S K') (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing u) = Some (Ongoing u)).
    { intros p o x E. destruct (lookup_combine_nth _ _ p _ E) as [i [Hi Hx]].
      change (nth_error (parameter_ids env c) i = Some p) in Hi. rewrite <- Hids, nth_error_map in Hi.
      destruct (nth_error vars i) as [[p' bound]|] eqn:Ev; [|discriminate Hi]. simpl in Hi. injection Hi as ->.
      destruct (nth_error_same_length xs ys i _ ltac:(lia) Hx) as [y Hy].
      pose proof (receiver_captures n mr c vars ma ys u Hc Hids Hbounds Hfy Hrec i p bound y Ev Hy) as Hst.
      pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy'.
      destruct y as [| | | |vb ob X| |]; try discriminate Hfy'.
      exists (mkVariableState bound (TypeArgument vb ob X) (TypeArgument vb ob X) true true), vb, ob, X.
      repeat split; try reflexivity; [exact Hst|exact Hfy'|].
      pose proof (Forall2_nth_error _ xs ys i _ _ Hp Hx Hy) as Ex.
      apply (unify_fuel_monotone env n0); [unfold K'; lia|].
      exact (proj2 (states_irrelevant n0) _ _ [] u Hfy' (Hfxs _ (nth_error_In _ _ Hx)) Ex). }
    pose proof (bindings_of_in_fragment c xs Hfxs) as Hbf.
    assert (Hb': bound_in env (bindings_of env c xs) K' u (to_generic P) = true)
        by exact (bound_in_transfer _ K [] K' u Hbf ltac:(unfold K'; lia) _ _ (le_n _) (ifrag_sfrag P HP) Hb).
    destruct (proj1 (inference_with_arguments (bindings_of env c xs) K' u Hcover Hbf fuel) P A u' HP HA HcA Hb' H) as [-> Hi].
    exists (fuel * S (S K') + 2). unfold is_assignable_to, empty_unification.
    assert (HfI: in_fragment env (inst (bindings_of env c xs) P) = true)
        by exact (instance_in_fragment env wf (bindings_of env c xs) K' u Hbf (to_generic P) (ifrag_sfrag P HP) Hb').
    rewrite (proj1 (states_irrelevant _) _ _ u [] HfI (proj1 (afrag_parts A HA)) Hi). reflexivity.
Qed.

End Inference.
