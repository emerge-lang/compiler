From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Transitivity.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The fragment of type parameters and intersections, and with unions                               *)
(*                                                                                                *)
(* The types as the frontend builds them, beyond the class types of Transitivity.v: references to  *)
(* type parameters, and intersections (see Generics.v). Here, ahead of the substitution, so that   *)
(* type parameters can be replaced with types of it. After it, the fragment with unions at the top:    *)
(* ugfrag, with non-null components, where transitivity is proven (Unions.v), and kugfrag, with    *)
(* the components the frontend also builds, which intersect and closestCommonSupertypeWith are    *)
(* conjectured to stay in (Conjectures.v).                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma fold_and_in: forall (Q: EType -> Prop) (xs: list EType), fold_right (fun a acc => Q a /\ acc) True xs -> forall a, In a xs -> Q a.
Proof. intros Q xs H. induction xs as [|x xs IH]; intros a Ha; [destruct Ha|]. destruct H as [Hx H]. destruct Ha as [<-|Ha]; auto. Qed.

Lemma fold_and_map: forall (Q: EType -> Prop) (f: EType -> EType) (xs: list EType),
    (forall a, In a xs -> Q (f a)) -> fold_right (fun a acc => Q a /\ acc) True (map f xs).
Proof. intros Q f xs H. induction xs as [|x xs IH]; [exact I|]. split; [apply H; left; reflexivity|]. apply IH. intros a Ha. apply H. right. exact Ha. Qed.

(* A type of values of the fragment that is no union, and not made nullable: a class type, a reference to a type
   parameter, an intersection *)
Definition flat (t: EType): Prop := match t with RootResolved _ _ _ | Generic _ | Intersection _ => True | _ => False end.

Section Fragment.

Variable env: Environment.

(* A component of an intersection: a class type, or a non-null reference to a type parameter *)
Definition is_component (t: EType): bool :=
    match t with
    | RootResolved _ _ _ => true
    | Generic _ => negb (is_nullable env t)
    | _ => false
    end.

(* What a nullable type wraps *)
Definition non_null (t: EType): bool :=
    match t with
    | Intersection _ => negb (is_nullable env t)
    | _ => is_component t
    end.

(* A component of an intersection that keeps its nullability (coverage #15): a component made
   nullable, `A?`, or a reference to a type parameter of a nullable bound, as it is, `P` *)
Definition is_kept_component (t: EType): bool :=
    match t with
    | Nullable n => is_component n
    | Generic _ => is_nullable env t
    | _ => false
    end.

Fixpoint gfrag (t: EType): bool :=
    match t with
    | RootResolved _ c arguments =>
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with TypeArgument _ _ n => gfrag n | _ => false end) arguments
    | Nullable n => non_null n && gfrag n
    (* the bound is the parameter's, of the fragment where the bounds are (Generics.bounds_wellformed);
       a reference whose bound has type variables in it is not *)
    | Generic (mkGenericRef _ _ _ vs) => match vs with [] => true | _ => false end
    (* as ofComponents makes them: the components assigned as the intersection, as one mutability;
       non-null, or keeping their nullability where not all of them are `X?` *)
    | Intersection components =>
        negb (Nat.eqb (length components) 0)
        && (forallb (fun c => is_component c && gfrag c) components
            || forallb (fun c => is_kept_component c && gfrag c) components && negb (forallb is_nullable_type components))
        && forallb (fun c => Mutability_beq (assignment_mutability env c) (assignment_mutability env t)) components
    | _ => false
    end.

Definition argument_gfrag (a: EType): bool :=
    match a with TypeArgument _ _ n => gfrag n | _ => false end.

Lemma root_gfrag: forall m c arguments, gfrag (RootResolved m c arguments) = true ->
    length arguments = length (parameter_ids env c) /\ forall a, In a arguments -> argument_gfrag a = true.
Proof.
    intros m c arguments H.
    change (Nat.eqb (length arguments) (length (parameter_ids env c)) && forallb argument_gfrag arguments = true) in H.
    apply andb_true_iff in H. destruct H as [Hl Ha]. split; [apply Nat.eqb_eq, Hl|apply forallb_forall, Ha].
Qed.

Lemma make_root_gfrag: forall m c arguments,
    length arguments = length (parameter_ids env c) -> (forall a, In a arguments -> argument_gfrag a = true) ->
    gfrag (RootResolved m c arguments) = true.
Proof.
    intros m c arguments Hl Ha.
    change (Nat.eqb (length arguments) (length (parameter_ids env c)) && forallb argument_gfrag arguments = true).
    rewrite Hl, Nat.eqb_refl. apply forallb_forall, Ha.
Qed.

Lemma is_component_not_nullable: forall x, is_component x = true -> is_nullable env x = false.
Proof. intros [| |[gm nn p b]| | | | |] H; cbn [is_component] in H; try discriminate H; try reflexivity; apply negb_true_iff, H. Qed.

Lemma kept_component_nullable: forall x, is_kept_component x = true -> is_nullable env x = true.
Proof. intros [|n|[gm nn p b]| | | | |] H; cbn [is_kept_component] in H; try discriminate H; [reflexivity|exact H]. Qed.

(* The components of an intersection of the fragment: non-null, or all keeping their nullability *)
Lemma intersection_gfrag_cases: forall cs, gfrag (Intersection cs) = true ->
    cs <> [] /\ (forall C, In C cs -> gfrag C = true)
    /\ ((forall C, In C cs -> is_component C = true)
        \/ ((forall C, In C cs -> is_kept_component C = true) /\ forallb is_nullable_type cs = false)).
Proof.
    intros cs H. simpl in H. apply andb_true_iff in H. destruct H as [H _]. apply andb_true_iff in H. destruct H as [Hl H].
    split; [intros ->; discriminate Hl|].
    apply orb_true_iff in H. destruct H as [H|H].
    - rewrite forallb_forall in H. split.
      + intros C Hc. exact (proj2 (proj1 (andb_true_iff _ _) (H C Hc))).
      + left. intros C Hc. exact (proj1 (proj1 (andb_true_iff _ _) (H C Hc))).
    - apply andb_true_iff in H. destruct H as [H Hn]. rewrite forallb_forall in H. split.
      + intros C Hc. exact (proj2 (proj1 (andb_true_iff _ _) (H C Hc))).
      + right. split; [intros C Hc; exact (proj1 (proj1 (andb_true_iff _ _) (H C Hc)))|apply negb_true_iff, Hn].
Qed.

Lemma intersection_gfrag: forall cs, gfrag (Intersection cs) = true -> is_nullable env (Intersection cs) = false ->
    cs <> [] /\ forall C, In C cs -> is_component C = true /\ gfrag C = true.
Proof.
    intros cs H Hn. destruct (intersection_gfrag_cases cs H) as [Hne [Hf [Hc|[Hk _]]]].
    - split; [exact Hne|]. intros C Hin. exact (conj (Hc C Hin) (Hf C Hin)).
    - exfalso. cbn [is_nullable] in Hn. assert (E: forallb (is_nullable env) cs = true).
      { apply forallb_forall. intros C Hin. exact (kept_component_nullable C (Hk C Hin)). }
      rewrite E in Hn. discriminate Hn.
Qed.

Lemma kept_intersection_gfrag: forall cs, gfrag (Intersection cs) = true -> is_nullable env (Intersection cs) = true ->
    cs <> [] /\ (forall C, In C cs -> is_kept_component C = true /\ gfrag C = true) /\ forallb is_nullable_type cs = false.
Proof.
    intros cs H Hn. destruct (intersection_gfrag_cases cs H) as [Hne [Hf [Hc|[Hk Ht]]]].
    - exfalso. destruct cs as [|C cs']; [contradiction (Hne eq_refl)|]. cbn [is_nullable] in Hn.
      change (is_nullable env C && forallb (is_nullable env) cs' = true) in Hn.
      rewrite (is_component_not_nullable C (Hc C (or_introl eq_refl))) in Hn. discriminate Hn.
    - split; [exact Hne|]. split; [intros C Hin; exact (conj (Hk C Hin) (Hf C Hin))|exact Ht].
Qed.

Lemma make_intersection_gfrag: forall cs, cs <> [] -> (forall C, In C cs -> is_component C = true /\ gfrag C = true) ->
    (forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)) ->
    gfrag (Intersection cs) = true.
Proof.
    intros cs Hne Hc Hm. simpl. apply andb_true_iff. split; [apply andb_true_iff; split|].
    - destruct cs; [contradiction (Hne eq_refl)|reflexivity].
    - apply orb_true_iff. left. apply forallb_forall. intros C Hin. apply andb_true_iff, Hc, Hin.
    - apply forallb_forall. intros C Hin. rewrite (Hm C Hin). apply internal_Mutability_dec_lb. reflexivity.
Qed.

Lemma make_kept_intersection_gfrag: forall cs, cs <> [] -> (forall C, In C cs -> is_kept_component C = true /\ gfrag C = true) ->
    forallb is_nullable_type cs = false ->
    (forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)) ->
    gfrag (Intersection cs) = true.
Proof.
    intros cs Hne Hc Ht Hm. simpl. apply andb_true_iff. split; [apply andb_true_iff; split|].
    - destruct cs; [contradiction (Hne eq_refl)|reflexivity].
    - apply orb_true_iff. right. apply andb_true_iff. split; [|rewrite Ht; reflexivity].
      apply forallb_forall. intros C Hin. apply andb_true_iff, Hc, Hin.
    - apply forallb_forall. intros C Hin. rewrite (Hm C Hin). apply internal_Mutability_dec_lb. reflexivity.
Qed.

(* The components of an intersection are assigned as the intersection *)
Lemma intersection_uniform: forall cs, gfrag (Intersection cs) = true ->
    forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs).
Proof.
    intros cs H C Hc. cbn [gfrag] in H. apply andb_true_iff in H. destruct H as [_ H]. rewrite forallb_forall in H.
    apply internal_Mutability_dec_bl, H, Hc.
Qed.

Lemma gfrag_cases: forall t, gfrag t = true ->
    (exists m c arguments, t = RootResolved m c arguments)
    \/ (exists x, t = Nullable x /\ non_null x = true /\ gfrag x = true)
    \/ (exists gm nn p vs, t = Generic (mkGenericRef gm nn p vs) /\ vs = [])
    \/ (exists cs, t = Intersection cs).
Proof.
    intros [m c args|x|[gm nn p [|v vs]]|me msg|v o x|g|cs|uns] H; simpl in H; try discriminate H.
    - left. eauto.
    - right. left. apply andb_true_iff in H. exists x. split; [reflexivity|exact H].
    - right. right. left. exists gm, nn, p, []. split; reflexivity.
    - right. right. right. eauto.
Qed.

Lemma component_cases: forall x, is_component x = true -> gfrag x = true ->
    (exists m c' arguments, x = RootResolved m c' arguments)
    \/ (exists gm nn p vs, x = Generic (mkGenericRef gm nn p vs) /\ is_nullable env x = false /\ vs = []).
Proof.
    intros [m c' args|n|[gm nn p [|v vs]]|me msg|v o n|g|cs|uns] Hc H; simpl in H; try discriminate H; try discriminate Hc.
    - left. eauto.
    - right. exists gm, nn, p, []. split; [reflexivity|]. split; [apply negb_true_iff; exact Hc|reflexivity].
Qed.

Lemma non_null_not_nullable: forall t, non_null t = true -> is_nullable env t = false.
Proof. intros [| |[gm nn p b]| | | | |] H; cbn [non_null is_component] in H; try discriminate H; try reflexivity; apply negb_true_iff, H. Qed.

Lemma in_fragment_gfrag: forall k,
    (forall t, depth t <= k -> in_fragment env t = true -> gfrag t = true)
    /\ (forall a, argument_depth a <= k -> argument_in_fragment env a = true -> argument_gfrag a = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split; [intros [m c args|[m c args| | | | | | |]| | | | | |] Hd H|intros [| | | |v o n| | |] Hd H]; simpl in Hd, H;
          try discriminate H; lia. }
    assert (Hroot: forall m c args, depth (RootResolved m c args) <= S k -> in_fragment env (RootResolved m c args) = true ->
        gfrag (RootResolved m c args) = true).
    { intros m c args Hd H. destruct (root_in_fragment env m c args H) as [Hl Ha]. apply make_root_gfrag; [exact Hl|].
      intros a Hin. pose proof (argument_depth_below m c args a Hin). apply IHa; [lia|apply Ha, Hin]. }
    split.
    - intros t Hd H. destruct (fragment_cases env t H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]].
      + exact (Hroot m c args Hd H).
      + rewrite depth_nullable in Hd. change (true && gfrag (RootResolved m c args) = true). apply Hroot; [lia|exact H'].
    - intros [| | | |v o n| | |] Hd H; simpl in H; try discriminate H. simpl in Hd. apply IHt; [lia|exact H].
Qed.

Lemma in_fragment_is_gfrag: forall t, in_fragment env t = true -> gfrag t = true.
Proof. intros t. apply (proj1 (in_fragment_gfrag (depth t))). lia. Qed.

Lemma gfrag_not_variable: forall t, gfrag t = true -> is_type_variable t = false.
Proof. intros [| | | | |g| |] H; simpl in H; try discriminate H; reflexivity. Qed.


(* A component of a union: a non-null type of values of gfrag, no union and not made nullable, as of_union pulls the
   nullability of the components written `X?` out. A component that may be null as it is, a reference to a type
   parameter of a nullable bound (`A | P` with `P : Any?`) or an intersection that keeps the nullability of its
   components, is left out (coverage: union types) *)
Definition is_union_component (t: EType): bool :=
    match t with
    | RootResolved _ _ _ | Generic _ | Intersection _ => gfrag t && negb (is_nullable env t)
    | _ => false
    end.

(* The fragment with unions at the top: gfrag, and non-empty unions of its components, nullable or not: `A | B`,
   `(A | B)?` (what of_union makes of `A? | B`), `A | P!`, `(A & B) | C`. Not nested, nor in type arguments *)
Definition ugfrag (t: EType): bool :=
    match t with
    | Union us | Nullable (Union us) => negb (Nat.eqb (length us) 0) && forallb is_union_component us
    | _ => gfrag t
    end.

Lemma union_component_gfrag: forall C, is_union_component C = true -> gfrag C = true.
Proof. intros [| | | | | | |] H; cbn [is_union_component] in H; try discriminate H; exact (proj1 (proj1 (andb_true_iff _ _) H)). Qed.

Lemma union_component_not_nullable: forall C, is_union_component C = true -> is_nullable env C = false.
Proof.
    intros [| | | | | | |] H; cbn [is_union_component] in H; try discriminate H;
        exact (proj1 (negb_true_iff _) (proj2 (proj1 (andb_true_iff _ _) H))).
Qed.

Lemma union_component_flat: forall C, is_union_component C = true -> flat C.
Proof. intros [| | | | | | |] H; cbn [is_union_component] in H; first [exact I|discriminate H]. Qed.

(* A component of a union, made nullable, is of gfrag: it is non-null *)
Lemma union_component_nullable_gfrag: forall C, is_union_component C = true -> gfrag (Nullable C) = true.
Proof.
    intros C H. pose proof (union_component_gfrag C H) as Hg. pose proof (union_component_not_nullable C H) as Hn.
    change (non_null C && gfrag C = true). rewrite Hg, andb_true_r.
    destruct C as [| | | | | | |]; cbn [is_union_component] in H; try discriminate H; cbn [non_null is_component]; [reflexivity| |];
        rewrite Hn; reflexivity.
Qed.

Lemma gfrag_ugfrag: forall t, gfrag t = true -> ugfrag t = true.
Proof. intros [|[| | | | | | |us]| | | | | |us] H; try exact H; simpl in H; discriminate H. Qed.

Lemma ugfrag_cases: forall t, ugfrag t = true ->
    gfrag t = true
    \/ (exists us, t = Union us /\ us <> [] /\ forall C, In C us -> is_union_component C = true)
    \/ (exists us, t = Nullable (Union us) /\ us <> [] /\ forall C, In C us -> is_union_component C = true).
Proof.
    intros [m c args|[m c args|n|g|me msg|v o n|g|cs|us]|g|me msg|v o n|g|cs|us] H; try (left; exact H).
    - right. right. cbn [ugfrag] in H. apply andb_true_iff in H. destruct H as [Hl H]. exists us.
      split; [reflexivity|]. split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
    - right. left. cbn [ugfrag] in H. apply andb_true_iff in H. destruct H as [Hl H]. exists us.
      split; [reflexivity|]. split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
Qed.

Lemma ugfrag_union: forall us, ugfrag (Union us) = true -> us <> [] /\ forall C, In C us -> is_union_component C = true.
Proof.
    intros us H. cbn [ugfrag] in H. apply andb_true_iff in H. destruct H as [Hl H].
    split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
Qed.

Lemma ugfrag_nullable_union: forall us, ugfrag (Nullable (Union us)) = ugfrag (Union us).
Proof. reflexivity. Qed.

Lemma gfrag_nullable_inner: forall y, gfrag (Nullable y) = true -> gfrag y = true.
Proof. intros y H. change (non_null y && gfrag y = true) in H. apply andb_true_iff in H. exact (proj2 H). Qed.

Lemma ugfrag_nullable: forall y, ugfrag (Nullable y) = true -> ugfrag y = true.
Proof.
    intros y H. destruct (ugfrag_cases (Nullable y) H) as [Hg|[[us [E _]]|[us [E _]]]]; [|discriminate E|injection E as ->; exact H].
    exact (gfrag_ugfrag y (gfrag_nullable_inner y Hg)).
Qed.

(* The types of the fragment unify sees: none a type variable, erroneous or a type argument *)
Lemma ugfrag_shape: forall t, ugfrag t = true ->
    match t with RootResolved _ _ _ | Nullable _ | Generic _ | Intersection _ | Union _ => True | _ => False end.
Proof.
    intros t H. destruct (ugfrag_cases t H) as [Hg|[[us [-> _]]|[us [-> _]]]]; try exact I.
    destruct (gfrag_cases t Hg) as [[m [c [args ->]]]|[[x [-> _]]|[[gm [nn [p [vs [-> _]]]]]|[cs ->]]]]; exact I.
Qed.

(* A component of a union as the frontend builds them: also one that may be null as it is, a reference to a type
   parameter of a nullable bound (`A | P` with `P : Any?`) or an intersection that keeps the nullability of its
   components (`A | (B? & P)`) *)
Definition is_kept_union_component (t: EType): bool :=
    match t with RootResolved _ _ _ | Generic _ | Intersection _ => gfrag t | _ => false end.

(* The fragment with unions at the top as the frontend builds them: ugfrag, and unions with components that keep
   their nullability. What intersect and closestCommonSupertypeWith are conjectured to stay in (Conjectures.v) *)
Definition kugfrag (t: EType): bool :=
    match t with
    | Union us | Nullable (Union us) => negb (Nat.eqb (length us) 0) && forallb is_kept_union_component us
    | _ => gfrag t
    end.

Lemma kept_union_component_gfrag: forall C, is_kept_union_component C = true -> gfrag C = true.
Proof. intros [| | | | | | |] H; cbn [is_kept_union_component] in H; first [exact H|discriminate H]. Qed.

Lemma kept_union_component_flat: forall C, is_kept_union_component C = true -> flat C.
Proof. intros [| | | | | | |] H; cbn [is_kept_union_component] in H; first [exact I|discriminate H]. Qed.

Lemma union_component_kept: forall C, is_union_component C = true -> is_kept_union_component C = true.
Proof.
    intros [| | | | | | |] H; cbn [is_union_component is_kept_union_component] in H |- *; try discriminate H;
        exact (proj1 (proj1 (andb_true_iff _ _) H)).
Qed.

Lemma gfrag_kugfrag: forall t, gfrag t = true -> kugfrag t = true.
Proof. intros [|[| | | | | | |us]| | | | | |us] H; try exact H; simpl in H; discriminate H. Qed.

Lemma ugfrag_kugfrag: forall t, ugfrag t = true -> kugfrag t = true.
Proof.
    intros t H. destruct (ugfrag_cases t H) as [Hg|[[us [-> [Hne Hus]]]|[us [-> [Hne Hus]]]]]; [exact (gfrag_kugfrag t Hg)| |];
        cbn [kugfrag]; apply andb_true_iff; split; try (destruct us; [contradiction (Hne eq_refl)|reflexivity]);
        apply forallb_forall; intros C Hc; exact (union_component_kept C (Hus C Hc)).
Qed.

Lemma kugfrag_cases: forall t, kugfrag t = true ->
    gfrag t = true
    \/ (exists us, t = Union us /\ us <> [] /\ forall C, In C us -> is_kept_union_component C = true)
    \/ (exists us, t = Nullable (Union us) /\ us <> [] /\ forall C, In C us -> is_kept_union_component C = true).
Proof.
    intros [m c args|[m c args|n|g|me msg|v o n|g|cs|us]|g|me msg|v o n|g|cs|us] H; try (left; exact H).
    - right. right. cbn [kugfrag] in H. apply andb_true_iff in H. destruct H as [Hl H]. exists us.
      split; [reflexivity|]. split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
    - right. left. cbn [kugfrag] in H. apply andb_true_iff in H. destruct H as [Hl H]. exists us.
      split; [reflexivity|]. split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
Qed.

Lemma kugfrag_union: forall us, kugfrag (Union us) = true -> us <> [] /\ forall C, In C us -> is_kept_union_component C = true.
Proof.
    intros us H. cbn [kugfrag] in H. apply andb_true_iff in H. destruct H as [Hl H].
    split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
Qed.

Lemma kugfrag_nullable: forall y, kugfrag (Nullable y) = true -> kugfrag y = true.
Proof.
    intros y H. destruct (kugfrag_cases (Nullable y) H) as [Hg|[[us [E _]]|[us [E _]]]]; [|discriminate E|injection E as ->; exact H].
    exact (gfrag_kugfrag y (gfrag_nullable_inner y Hg)).
Qed.

Lemma kugfrag_shape: forall t, kugfrag t = true ->
    match t with RootResolved _ _ _ | Nullable _ | Generic _ | Intersection _ | Union _ => True | _ => False end.
Proof.
    intros t H. destruct (kugfrag_cases t H) as [Hg|[[us [-> _]]|[us [-> _]]]]; try exact I.
    destruct (gfrag_cases t Hg) as [[m [c [args ->]]]|[[x [-> _]]|[[gm [nn [p [vs [-> _]]]]]|[cs ->]]]]; exact I.
Qed.

End Fragment.
