From EmergeTypeSystem Require Import Model Subtyping Ownership Transitivity Fragment Substitution MemberAccess Inference States
    Constraints Generics Conjectures MemberCalls FinalValues FreeInstances GenericArguments SubstitutionWide WithinBounds
    GenericCode Overrides.
From Stdlib Require Import Bool List Arith Lia Sorting.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The headline theorems, applied to a program                                                    *)
(*                                                                                                *)
(* A theorem whose premises no program satisfies compiles all the same, and proves nothing. Here  *)
(* each theorem is applied to one small program, every premise shown to hold of it, and the       *)
(* conclusion stated as an Example: the premises are jointly satisfiable, and not only by the     *)
(* degenerate case of empty lists. The program, in Emerge:                                         *)
(*                                                                                                *)
(*   interface Number                                                                             *)
(*   class Int : const Number                                                                     *)
(*   interface List<E>                                                                            *)
(*   class ArrayList<E> : List<E>                                                                 *)
(*   class Box<E> { var value: E = init; var maybe: E? = init }                                   *)
(*                                                                                                *)
(* and functions of their own, each Example says which. The type arguments written are `ref`, as  *)
(* those of objects are (exact, for MemberAccess.v and Overrides.v); a parameter that takes any   *)
(* ownership is `any`, as Kotlin, which has no ownership, has every type argument.                 *)
(*                                                                                                *)
(* The Environment takes intersect and closestCommonSupertypeWith as given (Model.v). Here they   *)
(* are meet and join, below: precise where one operand is the top or the bottom type, or both are *)
(* the same, and otherwise Nothing and `read Any?`. That is coarser than the Kotlin functions, but *)
(* it is what each conjecture about them asks of them, which is proven for this program (types,  *)
(* intersect_below, supertype_above and the like), not assumed.                                   *)
(*                                                                                                *)
(* What this finds: every premise of the theorems taken holds of this program, but one, that      *)
(* unify terminates on it (unify_terminates_on, Conjectures.v), which is open: the Examples of    *)
(* member_call_in_generic_code_sound and generic_member_call_with_bounded_variables_instantiated  *)
(* take it as a premise of their own, and show the other premises jointly satisfiable. The claim   *)
(* it replaced, that unify terminates on every environment whose inheritance is tame             *)
(* (unify_always_terminates), is false: unify loops on `T` against `Cn<in T>` where                *)
(* `T : Cn<Cn<in T>>`, an F-bound with contravariance; that is no supertype, so tame_inheritance   *)
(* doesn't rule it out (unify_always_terminates_is_false, at the end).                            *)
(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)
(* The classes and type parameters                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Definition CNumber := some_class 1.
Definition CInt := some_class 2.
Definition CList := some_class 3.
Definition CArrayList := some_class 4.
Definition CBox := some_class 5.

(* The E of List, of ArrayList, of Box *)
Definition pL: TypeParameterId := 1.
Definition pA: TypeParameterId := 2.
Definition pB: TypeParameterId := 3.
(* `<U : Number, T : List<out U>>` of a function (1, 2), the type parameter of a function without a bound
   (4), and `<W : Number>` of generic code calling functions (5, 6) *)
Definition pU: TypeParameterId := 10.
Definition pT: TypeParameterId := 11.
Definition pV: TypeParameterId := 12.
Definition pW: TypeParameterId := 14.

Definition gref (p: TypeParameterId): EType := Generic (mkGenericRef None false p []).
Definition tvar (p: TypeParameterId): EType := TypeVariable (mkGenericRef None false p []).
Definition arg (v: Variance) (o: Ownership) (t: EType): EType := TypeArgument v o t.
Definition tInt: EType := RootResolved None CInt [].
Definition tNumber: EType := RootResolved None CNumber [].

Definition param (p: TypeParameterId): TypeParameterDecl := {| param_id := p; prescribed_ownership := None |}.

Definition plain_decl (k: ClassKind) (c: bool) (ps: list TypeParameterDecl) (sts: list EType): ClassDecl :=
    {| kind := k; is_const := c; is_non_token := true; type_parameters := ps; supertypes := sts; fields := [] |}.

Definition decl (c: Class): ClassDecl :=
    match c with
    | any => plain_decl interface_kind false [] []
    | nothing => plain_decl class_kind true [] [RootResolved (Some immutable) any []]
    | some_class 1 => plain_decl interface_kind false [] []
    | some_class 2 => plain_decl class_kind true [] [RootResolved (Some immutable) CNumber []]
    | some_class 3 => plain_decl interface_kind false [param pL] []
    | some_class 4 => plain_decl class_kind false [param pA]
        [RootResolved None CList [TypeArgument invariant (parameter_ownership pA) (gref pA)]]
    | some_class 5 => {| kind := class_kind; is_const := false; is_non_token := true; type_parameters := [param pB]; supertypes := [];
                         fields := [{| Model.is_ref := false |}; {| Model.is_ref := false |}] |}
    | some_class _ => plain_decl class_kind false [] []
    end.

(* The transitive supertypes, but Any *)
Definition sups (c: Class): list Class :=
    match c with
    | some_class 2 => [CNumber]
    | some_class 4 => [CList]
    | _ => []
    end.

Definition psup (sub super: Class): EType :=
    match sub, super with
    | some_class 4, some_class 3 => RootResolved None CList [TypeArgument invariant (parameter_ownership pA) (gref pA)]
    | _, _ => RootResolved None super []
    end.

Definition bound (p: TypeParameterId): EType :=
    match p with
    | 10 => tNumber
    | 11 => RootResolved None CList [TypeArgument output ref (gref pU)]
    | 14 => tNumber
    | _ => top_type
    end.

Definition rank (p: TypeParameterId): nat :=
    match p with
    | 10 => 1
    | 11 => 2
    | 14 => 1
    | _ => 0
    end.

(* ---------------------------------------------------------------------------------------------- *)
(* intersect and closestCommonSupertypeWith                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Definition is_top (t: EType): bool :=
    match t with Nullable (RootResolved (Some readonly) any []) => true | _ => false end.
Definition is_bottom (t: EType): bool :=
    match t with RootResolved (Some own) nothing [] => true | _ => false end.

(* Equality of types, as far as it is told; erroneous types are never equal *)
Definition opt_mut_eqb (a b: option Mutability): bool :=
    match a, b with Some x, Some y => Mutability_beq x y | None, None => true | _, _ => false end.
Definition own_eqb (a b: Ownership): bool :=
    match a, b with
    | owned, owned | ref, ref | any_ownership, any_ownership => true
    | parameter_ownership p, parameter_ownership q => Nat.eqb p q
    | _, _ => false
    end.
Fixpoint nats_eqb (a b: list nat): bool :=
    match a, b with [], [] => true | x :: r, y :: r' => Nat.eqb x y && nats_eqb r r' | _, _ => false end.
Definition gref_eqb (g h: GenericRef): bool :=
    match g, h with mkGenericRef m n p vs, mkGenericRef m' n' p' vs' =>
        opt_mut_eqb m m' && Bool.eqb n n' && Nat.eqb p p' && nats_eqb vs vs' end.
Fixpoint list_eqb_with (f: EType -> EType -> bool) (l l': list EType): bool :=
    match l, l' with [], [] => true | x :: r, y :: r' => f x y && list_eqb_with f r r' | _, _ => false end.
Fixpoint ety_eqb (a b: EType): bool :=
    match a, b with
    | RootResolved m c args, RootResolved m' c' args' => opt_mut_eqb m m' && class_eqb c c' && list_eqb_with ety_eqb args args'
    | Nullable n, Nullable n' => ety_eqb n n'
    | Generic g, Generic g' => gref_eqb g g'
    | TypeArgument v o n, TypeArgument v' o' n' => Variance_beq v v' && own_eqb o o' && ety_eqb n n'
    | TypeVariable g, TypeVariable g' => gref_eqb g g'
    | Intersection cs, Intersection cs' => list_eqb_with ety_eqb cs cs'
    | _, _ => false
    end.

(* The intersection of two types: the other where one is `read Any?`, the type where both are the
   same; `own Nothing` otherwise, which is below both. The closest common supertype: the other
   where one is `own Nothing`, the type where both are the same; `read Any?` otherwise *)
Definition meet (a b: EType): EType :=
    if is_top a then b else if is_top b then a else if ety_eqb a b then a else bottom_type.
Definition join (a b: EType): EType :=
    if is_bottom a then b else if is_bottom b then a else if ety_eqb a b then a else top_type.

Definition penv: Environment := {|
    declaration_of := decl;
    supertypes_of := sups;
    closest_common_super_class := fun _ => any;
    parameterized_supertype := psup;
    closest_common_supertype_with := join;
    intersect := meet;
    parameter_bound := bound;
    parameter_rank := rank;
|}.

Lemma opt_mut_eqb_eq: forall m0 m1, opt_mut_eqb m0 m1 = true -> m0 = m1.
Proof. intros [m0|] [m1|] H; try discriminate H; [f_equal; exact (internal_Mutability_dec_bl m0 m1 H)|reflexivity]. Qed.

Lemma own_eqb_eq: forall o0 o1, own_eqb o0 o1 = true -> o0 = o1.
Proof. intros [| | |p] [| | |q] H; try discriminate H; try reflexivity. f_equal. apply Nat.eqb_eq, H. Qed.

Lemma nats_eqb_eq: forall l0 l1, nats_eqb l0 l1 = true -> l0 = l1.
Proof.
    induction l0 as [|x l0 IH]; intros [|y l1] H; try discriminate H; [reflexivity|].
    cbn in H. apply andb_true_iff in H. destruct H as [Hx H]. apply Nat.eqb_eq in Hx. subst y. f_equal. exact (IH l1 H).
Qed.

Lemma gref_eqb_eq: forall g0 g1, gref_eqb g0 g1 = true -> g0 = g1.
Proof.
    intros [m n p vs] [m' n' p' vs'] H. cbn in H. apply andb_true_iff in H. destruct H as [H Hvs].
    apply andb_true_iff in H. destruct H as [H Hp]. apply andb_true_iff in H. destruct H as [Hm Hn].
    rewrite (opt_mut_eqb_eq m m' Hm), (eqb_prop n n' Hn), (proj1 (Nat.eqb_eq p p') Hp), (nats_eqb_eq vs vs' Hvs).
    reflexivity.
Qed.

Lemma ety_eqb_eq: forall z y0, ety_eqb z y0 = true -> z = y0.
Proof.
    fix IH 1. intros [m c args|n|g|m msg|v o n|g|cs] [m' c' args'|n'|g'|mm msg'|v' o' n'|g'|cs'] H;
        cbn [ety_eqb] in H; try discriminate H.
    - apply andb_true_iff in H. destruct H as [H Ha]. apply andb_true_iff in H. destruct H as [Hm Hc].
      rewrite (opt_mut_eqb_eq m m' Hm). unfold class_eqb in Hc. destruct (Class_eq_dec c c') as [<-|]; [|discriminate Hc].
      f_equal. revert args' Ha. induction args as [|x args IHa]; intros [|y args'] Ha; try discriminate Ha; [reflexivity|].
      cbn [list_eqb_with] in Ha. apply andb_true_iff in Ha. destruct Ha as [Hx Ha]. f_equal; [exact (IH x y Hx)|exact (IHa args' Ha)].
    - f_equal. exact (IH n n' H).
    - f_equal. exact (gref_eqb_eq g g' H).
    - apply andb_true_iff in H. destruct H as [H Hn]. apply andb_true_iff in H. destruct H as [Hv Ho].
      rewrite (internal_Variance_dec_bl v v' Hv), (own_eqb_eq o o' Ho), (IH n n' Hn). reflexivity.
    - f_equal. exact (gref_eqb_eq g g' H).
    - f_equal. revert cs' H. induction cs as [|x cs IHa]; intros [|y cs'] Ha; try discriminate Ha; [reflexivity|].
      cbn [list_eqb_with] in Ha. apply andb_true_iff in Ha. destruct Ha as [Hx Ha]. f_equal; [exact (IH x y Hx)|exact (IHa cs' Ha)].
Qed.

Lemma is_top_eq: forall t, is_top t = true -> t = top_type.
Proof.
    intros [|[m c args| | | | | |]| | | | |] H; try discriminate H.
    destruct m as [[]|], c, args; try discriminate H; reflexivity.
Qed.

Lemma is_bottom_eq: forall t, is_bottom t = true -> t = bottom_type.
Proof.
    intros [m c args| | | | | |] H; try discriminate H.
    destruct m as [[]|], c, args; try discriminate H; reflexivity.
Qed.

Lemma meet_cases: forall x y, (meet x y = y /\ x = top_type) \/ (meet x y = x /\ y = top_type)
    \/ (meet x y = x /\ x = y) \/ meet x y = bottom_type.
Proof.
    intros x y. unfold meet. destruct (is_top x) eqn:Ea; [left; split; [reflexivity|exact (is_top_eq x Ea)]|].
    destruct (is_top y) eqn:Eb; [right; left; split; [reflexivity|exact (is_top_eq y Eb)]|].
    destruct (ety_eqb x y) eqn:Eab; [right; right; left; split; [reflexivity|exact (ety_eqb_eq x y Eab)]|right; right; right; reflexivity].
Qed.

Lemma join_cases: forall x y, (join x y = y /\ x = bottom_type) \/ (join x y = x /\ y = bottom_type)
    \/ (join x y = x /\ x = y) \/ join x y = top_type.
Proof.
    intros x y. unfold join. destruct (is_bottom x) eqn:Ea; [left; split; [reflexivity|exact (is_bottom_eq x Ea)]|].
    destruct (is_bottom y) eqn:Eb; [right; left; split; [reflexivity|exact (is_bottom_eq y Eb)]|].
    destruct (ety_eqb x y) eqn:Eab; [right; right; left; split; [reflexivity|exact (ety_eqb_eq x y Eab)]|right; right; right; reflexivity].
Qed.

(* What either function makes of two types: one of them, or the bottom or the top type *)
Lemma meet_is: forall x y, meet x y = x \/ meet x y = y \/ meet x y = bottom_type.
Proof. intros x y. destruct (meet_cases x y) as [[E _]|[[E _]|[[E _]|E]]]; auto. Qed.

Lemma join_is: forall x y, join x y = x \/ join x y = y \/ join x y = top_type.
Proof. intros x y. destruct (join_cases x y) as [[E _]|[[E _]|[[E _]|E]]]; auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The program is well-formed                                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* The classes declared, and one for all others: some_class of 6 or more *)
Ltac classes c := destruct c as [|[|[|[|[|[|[|?]]]]]]|].

Lemma sub_cases: forall c0 c1, base_type_is_subtype_of penv c0 c1 = true ->
    c0 = c1 \/ c1 = any \/ c0 = nothing \/ (c0 = CInt /\ c1 = CNumber) \/ (c0 = CArrayList /\ c1 = CList).
Proof.
    intros c0 c1 H. unfold base_type_is_subtype_of in H. unfold class_eqb at 1 in H.
    destruct (Class_eq_dec c1 c0) as [<-|Hne]; [left; reflexivity|].
    classes c0; classes c1; cbn in H; try discriminate H;
        solve [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
              | right; right; right; left; split; reflexivity | right; right; right; right; split; reflexivity].
Qed.

Lemma wf: wellformed penv.
Proof.
    constructor.
    - intros a b c Hb Hc. classes a; cbn in Hb; try contradiction; destruct Hb as [<-|[]]; cbn in Hc; contradiction.
    - reflexivity.
    - intros c c' H1 H2. destruct (sub_cases _ _ H1) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst; try reflexivity.
      + destruct (sub_cases _ _ H2) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst; try reflexivity; discriminate.
      + destruct (sub_cases _ _ H2) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst; try reflexivity; discriminate.
      + vm_compute in H2. discriminate H2.
      + vm_compute in H2. discriminate H2.
    - intros c. classes c; cbn; repeat constructor; cbn; tauto.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros sub super Hne Hn H. destruct (sub_cases _ _ H) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst;
        try contradiction.
      + classes sub; try contradiction; cbn; split; try reflexivity; intros t [].
      + cbn. split; [reflexivity|intros t []].
      + cbn. split; [reflexivity|]. intros t [<-|[]]. reflexivity.
    - intros a b c Hab Hbc Hac Ha Hb H1 H2.
      destruct (sub_cases _ _ H2) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst; try contradiction.
      + classes a; classes b; try contradiction; reflexivity.
      + destruct (sub_cases _ _ H1) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst; try contradiction; discriminate.
      + destruct (sub_cases _ _ H1) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst; try contradiction; discriminate.
    - intros sub super t H. classes sub; classes super; cbn in H; try contradiction; destruct H as [<-|[]]; reflexivity.
    - intros sub super t H. classes sub; classes super; cbn in H; try contradiction; destruct H as [<-|[]]; reflexivity.
    - intros p. do 15 (destruct p as [|p]; [reflexivity|]). reflexivity.
    - intros p. do 15 (destruct p as [|p]; [reflexivity|]). reflexivity.
    - intros p. do 15 (destruct p as [|p]; [reflexivity|]). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 1. Transitivity.transitivity                                                                   *)
(*                                                                                                *)
(*   val x: mut ArrayList<Int> = ...                                                              *)
(*   val y: List<out Number> = x                                                                  *)
(*   val z: List<out any Any?> = y                                                                *)
(*                                                                                                *)
(* A subclass, a const class below an interface, and variance and ownership on the type arguments. *)
(* ---------------------------------------------------------------------------------------------- *)

Definition x1: EType := RootResolved (Some mutable) CArrayList [arg invariant ref tInt].
Definition y1: EType := RootResolved (Some readonly) CList [arg output ref tNumber].
Definition z1: EType := RootResolved (Some readonly) CList [arg output any_ownership top_type].

Example transitivity_instance: is_assignable_to penv 12 x1 z1 = Some true.
Proof.
    exact (transitivity penv wf 6 6 x1 y1 z1 eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 2. Substitution.substitution_lemma                                                             *)
(*                                                                                                *)
(*   fn f<U : Number, T : List<out U>>(x: T) { val y: List<out Number> = x }                       *)
(*   f::<Int, ArrayList<Int>>(...)                                                                *)
(*                                                                                                *)
(* A bound that mentions another type parameter, a subclass bound to it, and the reference read  *)
(* through its bound: `T` is assignable to `List<out Number>` as `List<out U>` is, and the        *)
(* instances are.                                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Definition b2: Bindings := [(pU, arg invariant ref tInt); (pT, arg invariant ref (RootResolved None CArrayList [arg invariant ref tInt]))].
Definition t2: EType := RootResolved None CList [arg output ref tNumber].
Definition a2: EType := gref pT.

Example substitution_instance: exists n,
    is_assignable_to penv n (RootResolved None CArrayList [arg invariant ref tInt]) (RootResolved None CList [arg output ref tNumber])
    = Some true.
Proof.
    eexists.
    refine (substitution_lemma penv wf b2 10 3 10 t2 a2 ltac:(lia) _ _ eq_refl eq_refl ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    - intros p o x H. do 12 (destruct p as [|p]; [discriminate H || (injection H as <- <-; vm_compute; lia)|]). discriminate H.
    - intros p o x H. do 12 (destruct p as [|p]; [discriminate H || (injection H as <- <-; reflexivity)|]). discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 3. MemberAccess.member_read_sound, member_write_sound                                           *)
(*                                                                                                *)
(*   val b: Box<out Number> = Box<Int>(...)     // the object: mut Box<Int>                        *)
(*   val n: Number = b.value                    // what the object holds is an Int                 *)
(*                                                                                                *)
(*   val c: Box<in Int> = Box<Number>(...)      // the object: mut Box<Number>                     *)
(*   c.maybe = (x: Int?)                        // fits the `Number?` of the object                *)
(* ---------------------------------------------------------------------------------------------- *)

Example member_read_instance: exists fuel, unify penv fuel tNumber tInt (Ongoing []) = Some (Ongoing []).
Proof.
    exact (member_read_sound penv wf 10 [] (Some mutable) CBox [arg invariant ref tInt] None [arg output ref tNumber]
        (gref pB) tInt 10 ltac:(discriminate) eq_refl eq_refl
        ltac:(intros x [<-|[]]; reflexivity) ltac:(intros y [<-|[]]; reflexivity)
        ltac:(vm_compute; reflexivity) eq_refl eq_refl ltac:(vm_compute; reflexivity)).
Qed.

Example member_write_instance:
    (exists fuel, unify penv fuel (Nullable tNumber) (Nullable tInt) (Ongoing []) = Some (Ongoing []))
    \/ (holds_only_null penv (Nullable tInt) = true /\ is_nullable penv (Nullable tNumber) = true).
Proof.
    exact (member_write_sound penv wf 10 [] (Some mutable) CBox [arg invariant ref tNumber] None [arg input ref tInt]
        (Nullable (gref pB)) (Nullable tInt) 10 ltac:(discriminate) eq_refl eq_refl
        ltac:(intros x [<-|[]]; reflexivity) ltac:(intros y [<-|[]]; reflexivity)
        ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 4. Constraints.invocation_sound                                                                *)
(*                                                                                                *)
(*   fn put<V>(items: List<out V>, sink: Box<in V>)                                               *)
(*   put(ArrayList<Int>(), Box<Number>(...))                                                     *)
(*                                                                                                *)
(* The first argument gives V the lower bound Int, through the supertype List<Int> of             *)
(* ArrayList<Int>; the second the upper bound Number. Any type between fits; the example takes    *)
(* Number, not the final value Int.                                                                *)
(*                                                                                                *)
(* The types variables are replaced with, and their bounds, are the class types (xf); intersect   *)
(* and closestCommonSupertypeWith, meet and join, are the bounds they are meant to be for them    *)
(* (types), without a conjecture.                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* x is assignable to y, the variable states as they are *)
Definition below0 (x y: EType): Prop := exists n, unify penv n y x (Ongoing []) = Some (Ongoing []).

Lemma below0_trans: forall x y z, in_fragment penv x = true -> in_fragment penv y = true -> in_fragment penv z = true ->
    below0 x y -> below0 y z -> below0 x z.
Proof.
    intros x y z Hx Hy Hz [n1 H1] [n2 H2].
    pose proof (transitivity penv wf n1 n2 x y z Hx Hy Hz) as T. unfold is_assignable_to, empty_unification in T.
    rewrite H1, H2 in T. specialize (T eq_refl eq_refl).
    destruct (unify penv (n1 + n2) z x (Ongoing [])) as [[u|]|] eqn:E; try discriminate T.
    exists (n1 + n2). rewrite E. f_equal. f_equal.
    exact (proj1 (keeps_states_with_arguments penv wf (n1 + n2)) z x [] u Hz Hx E).
Qed.

Lemma below0_bottom: forall t, in_fragment penv t = true -> below0 bottom_type t.
Proof. intros t Ht. exists 2. exact (bottom_below penv wf t 2 [] Ht (le_n _)). Qed.

Lemma below0_top: forall t, in_fragment penv t = true -> below0 t top_type.
Proof. intros t Ht. exists 2. exact (top_above penv wf t 2 [] Ht (le_n _)). Qed.

Definition xf (t: EType): Prop := in_fragment penv t = true.

Lemma types: inference_types penv xf xf.
Proof.
    constructor.
    - exact (in_fragment_is_gfrag penv).
    - intros x Hx. exact Hx.
    - intros x Hx. exists (depth x). exact (proj1 (reflexivity_with_arguments penv (depth x)) x [] Hx (le_n _)).
    - intros x Hx. exact Hx.
    - intros a b Ha Hb. unfold xf. change (intersect penv a b) with (meet a b).
      destruct (meet_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|exact (bottom_in_fragment penv wf)].
    - intros a b Ha Hb. unfold xf. change (closest_common_supertype_with penv a b) with (join a b).
      destruct (join_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|exact (top_in_fragment penv wf)].
    - intros a b x n Ha Hb Hx H. assert (H0: below0 x (meet a b)) by (exists n; exact H). clear H. rename H0 into H.
      destruct (meet_cases a b) as [[E ->]|[[E ->]|[[E <-]|E]]]; rewrite E in H.
      + split; [exact (below0_top x Hx)|exact H].
      + split; [exact H|exact (below0_top x Hx)].
      + split; exact H.
      + split; [exact (below0_trans x _ a Hx (bottom_in_fragment penv wf) Ha H (below0_bottom a Ha))
               |exact (below0_trans x _ b Hx (bottom_in_fragment penv wf) Hb H (below0_bottom b Hb))].
    - intros a b x n Ha Hb Hx H. assert (H0: below0 (join a b) x) by (exists n; exact H). clear H. rename H0 into H.
      destruct (join_cases a b) as [[E ->]|[[E ->]|[[E <-]|E]]]; rewrite E in H.
      + split; [exact (below0_bottom x Hx)|exact H].
      + split; [exact H|exact (below0_bottom x Hx)].
      + split; exact H.
      + split; [exact (below0_trans a _ x Ha (top_in_fragment penv wf) Hx (below0_top a Ha) H)
               |exact (below0_trans b _ x Hb (top_in_fragment penv wf) Hx (below0_top b Hb) H)].
    - intros a b Ha Hb. change (intersect penv a b) with (meet a b).
      destruct (meet_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|reflexivity].
    - intros a b Ha Hb. change (closest_common_supertype_with penv a b) with (join a b).
      destruct (join_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|reflexivity].
    - intros gm nn x a n Hx Ha Hgm Hnn H. exists n. exact (class_reference_takes penv n gm nn x a [] Hx Ha Hgm Hnn H).
    - intros gm nn x a n Hx Ha H. exists n. exact (reference_takes_assignee penv n gm nn x a [] Hx Ha H).
    - intros gm nn x B n Hx HB H. exists n. exact (class_reference_within penv n gm nn x B [] Hx HB H).
Qed.

Lemma supertype_of_classes: closest_common_supertype_of_classes penv.
Proof.
    intros a b Ha Hca Hwa Hb Hcb Hwb. change (closest_common_supertype_with penv a b) with (join a b).
    destruct (join_is a b) as [->|[->| ->]]; [split; [|split]; assumption|split; [|split]; assumption|].
    split; [exact (top_in_afrag penv wf)|split; reflexivity].
Qed.

(* No supertype has an in-variant type argument: the arguments may be taken without contravariance *)
Lemma supertypes_wc: supertypes_without_contravariance penv.
Proof. intros sub super. classes sub; classes super; reflexivity. Qed.

Definition Ps4: list EType := [RootResolved None CList [arg output any_ownership (tvar pV)]; RootResolved None CBox [arg input any_ownership (tvar pV)]].
Definition As4: list EType := [RootResolved None CArrayList [arg invariant ref tInt]; RootResolved None CBox [arg invariant ref tNumber]].
Definition s4: VariableStates := match for_inference_of [(pV, top_type)] [] with Ongoing s => s | Failed => [] end.
(* The states inference ends with: V between Int and Number *)
Definition u4: VariableStates :=
    match fold_unify (fun inner '(P, A) => unify penv 20 P A inner) (combine Ps4 As4) (Ongoing s4) with
    | Some (Ongoing u) => u
    | _ => []
    end.
Definition b4: Bindings := [(pV, arg invariant ref tNumber)].

Lemma s4_wf: wf_states penv xf xf true s4.
Proof.
    intros p st H. cbn in H. destruct (param_eqb p pV) eqn:Ep; [|discriminate H]. injection H as <-.
    split; [reflexivity|]. split; [reflexivity|]. split; [|vm_compute; reflexivity].
    intros _. split; [reflexivity|]. split; [exists 2; vm_compute; reflexivity|].
    split; [exact (top_in_fragment penv wf)|]. split; [exact (bottom_in_fragment penv wf)|].
    unfold static_ok. cbn [static_upper_bound upper_bound no_vars]. intros x f _ Hx. exists f. exact Hx.
Qed.

Example invocation_instance:
    (exists n, is_assignable_to penv n (RootResolved None CArrayList [arg invariant ref tInt])
        (RootResolved None CList [arg output any_ownership tNumber]) = Some true)
    /\ (exists n, is_assignable_to penv n (RootResolved None CBox [arg invariant ref tNumber])
        (RootResolved None CBox [arg input any_ownership tNumber]) = Some true).
Proof.
    destruct (invocation_sound penv wf xf xf types supertype_of_classes true (fun _ => supertypes_wc) 20 Ps4 As4 s4 u4 s4_wf
        ltac:(intros P [<-|[<-|[]]]; reflexivity) ltac:(intros A [<-|[<-|[]]]; split; reflexivity)
        ltac:(intros _ A [<-|[<-|[]]]; reflexivity)
        ltac:(vm_compute; reflexivity)) as [_ Hall].
    assert (Hb: bindings_in_fragment penv b4).
    { intros p o x H. cbn in H. destruct (param_eqb p pV); [injection H as <- <-; reflexivity|discriminate H]. }
    assert (Hs: satisfies penv xf b4 u4).
    { intros p o x H. cbn in H. destruct (param_eqb p pV) eqn:Ep; [|discriminate H]. injection H as <- <-.
      apply Nat.eqb_eq in Ep. subst p.
      split; [reflexivity|]. eexists. split; [vm_compute; reflexivity|].
      unfold fits. cbn. split; exists 5; vm_compute; reflexivity. }
    specialize (Hall b4 10 ltac:(intros P [<-|[<-|[]]]; vm_compute; reflexivity) Hs (fun _ => Hb)).
    split; [exact (Hall _ _ (or_introl eq_refl))|exact (Hall _ _ (or_intror (or_introl eq_refl)))].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What the theorems of generic code take of the program, the conjectures of Conjectures.v and     *)
(* GenericCode.v among it, but unify_terminates_on                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma declared_wf: bounds_wellformed penv bound.
Proof.
    constructor; [reflexivity|]. intros p. do 15 (destruct p as [|p]; [vm_compute; reflexivity|]). vm_compute. reflexivity.
Qed.

Lemma intersect_no_vars: forall x y, no_vars x = true -> no_vars y = true -> no_vars (intersect penv x y) = true.
Proof. intros x y Ha Hb. change (intersect penv x y) with (meet x y). destruct (meet_is x y) as [->|[->| ->]]; auto. Qed.

Lemma supertype_no_vars: forall x y, no_vars x = true -> no_vars y = true -> no_vars (closest_common_supertype_with penv x y) = true.
Proof. intros x y Ha Hb. change (closest_common_supertype_with penv x y) with (join x y). destruct (join_is x y) as [->|[->| ->]]; auto. Qed.

(* Only ArrayList has supertypes with type arguments *)
Lemma finite: finitely_many_templates penv.
Proof.
    exists [CArrayList]. intros sub super H. classes sub; classes super; cbn in H |- *; try (contradiction H; reflexivity); left; reflexivity.
Qed.

(* The one edge, from the E of ArrayList to the E of List, isn't expansive *)
Lemma tame: tame_inheritance penv.
Proof.
    split.
    - exists (fun _ => 0). intros p q ex [sub [super [c [arguments [j [a [Hne [Hn [Hsub [Hin [Ha [Hq Hp]]]]]]]]]]]].
      destruct ex; [exfalso|lia].
      destruct (sub_cases _ _ Hsub) as [E1|[E1|[E1|[[E1 E2]|[E1 E2]]]]]; subst; try contradiction.
      + classes sub; try contradiction; cbn in Hin; destruct Hin as [Hin|[]]; injection Hin as <- <-; destruct j; discriminate Ha.
      + cbn in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. destruct j; discriminate Ha.
      + cbn in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. destruct j as [|[|j]]; try discriminate Ha.
        injection Ha as <-. cbn in Hp. destruct Hp as [Hp|[]]. discriminate Hp.
    - exact supertypes_wc.
Qed.

Lemma intersect_in_fragment: intersect_always_stays_in_fragment penv bound.
Proof.
    intros a b Ha Hb. change (intersect penv a b) with (meet a b).
    destruct (meet_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|split; [exact (bottom_gfrag penv wf)|exact I]].
Qed.

Lemma supertype_in_fragment: closest_common_supertype_stays_in_fragment penv bound.
Proof.
    intros a b Ha Hb. change (closest_common_supertype_with penv a b) with (join a b).
    destruct (join_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|split; [exact (top_gfrag penv wf)|exact I]].
Qed.

Lemma intersect_generic: intersect_stays_in_generic_code penv bound.
Proof.
    intros ps a b _ _ Ha Hb. change (intersect penv a b) with (meet a b).
    destruct (meet_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|exact (caller_bottom penv wf bound ps)].
Qed.

Lemma supertype_generic: closest_common_supertype_stays_in_generic_code penv bound.
Proof.
    intros ps a b _ _ Ha Hb. change (closest_common_supertype_with penv a b) with (join a b).
    destruct (join_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|exact (caller_top penv wf bound ps)].
Qed.

Lemma supertype_bottom_only: closest_common_supertype_keeps_bottom_only penv bound.
Proof.
    intros a b _ _ Ha Hb. change (closest_common_supertype_with penv a b) with (join a b).
    destruct (join_is a b) as [->|[->| ->]]; [exact Ha|exact Hb|reflexivity].
Qed.

(* Below both and above both: on the types of the fragment, with the lemmas of GenericArguments.v,
   which take unify_terminates_on for the reflexivity of unify, and for the bottom and the top type
   being below and above everything *)
Section Terminating.

Hypothesis terminates: unify_terminates_on penv bound.

Lemma assignable_of_below: forall x y, below penv x y -> exists n, is_assignable_to penv n x y = Some true.
Proof. intros x y [n H]. exists n. unfold is_assignable_to, empty_unification. rewrite H. reflexivity. Qed.

Let refl := below_refl penv wf bound declared_wf terminates .
Let up := below_top penv wf bound declared_wf terminates .
Let down := below_bottom penv wf bound declared_wf terminates .

Lemma intersect_below: intersect_is_below_both penv bound.
Proof.
    intros a b Ha Hb. change (intersect penv a b) with (meet a b).
    destruct (meet_cases a b) as [[-> ->]|[[-> ->]|[[-> <-]| ->]]]; split; apply assignable_of_below;
        first [apply refl|apply up|apply down]; assumption.
Qed.

Lemma supertype_above: closest_common_supertype_is_above_both penv bound.
Proof.
    intros a b Ha Hb. change (closest_common_supertype_with penv a b) with (join a b).
    destruct (join_cases a b) as [[-> ->]|[[-> ->]|[[-> <-]| ->]]]; split; apply assignable_of_below;
        first [apply refl|apply up|apply down]; assumption.
Qed.

End Terminating.

(* Props that computation leaves: conjunctions, memberships, ownerships that are no type parameters *)
Ltac props := repeat match goal with
    | |- True => exact I
    | |- _ /\ _ => split
    | |- ?x = ?x => reflexivity
    | |- ?a = ?a \/ _ => left; reflexivity
    | |- _ \/ _ => right
    | |- forall q, _ = _ -> _ => let q := fresh in let E := fresh in intros q E; discriminate E
    end.

(* ---------------------------------------------------------------------------------------------- *)
(* 5. GenericArguments.member_call_in_generic_code_sound                                          *)
(*                                                                                                *)
(*   interface List<E> { fn add<U : Number>(self, x: E, us: Box<out U>) }                          *)
(*   fn caller<W : Number>(list: List<Number>, w: W, ws: Box<out W>) { list.add(w, ws) }            *)
(*                                                                                                *)
(* The receiver, of the interface List, is an object of the subclass ArrayList: `mut              *)
(* ArrayList<Number>`. E is captured from the receiver, exactly Number, which takes the W of the  *)
(* caller by its bound; U is inferred from `Box<out W>`, its final value W, a type parameter of   *)
(* the caller. What the arguments and the bounds are besides (Qb, Qa) is left unconstrained.       *)
(* ---------------------------------------------------------------------------------------------- *)

Definition cvars5: list (TypeParameterId * EType) := [(pL, top_type)].
Definition ovars5: list (TypeParameterId * EType) := [(pU, tNumber)].
Definition ys5: list EType := [arg invariant ref tNumber].
Definition xs5: list EType := [arg invariant ref tNumber].
Definition zs5: list EType := if class_eqb CArrayList CList then xs5 else parameterized_supertype_arguments penv CArrayList xs5 CList.
Definition Ps5: list EType := [tvar pL; RootResolved None CBox [arg output any_ownership (tvar pU)]].
Definition As5: list EType := [gref pW; RootResolved None CBox [arg output ref (gref pW)]].
Definition u5: VariableStates :=
    match unify penv 20 (RootResolved None CList (map receiver_leaf cvars5)) (RootResolved None CList ys5)
        (for_inference_of (cvars5 ++ ovars5) (map fst cvars5)) with
    | Some (Ongoing u) => u
    | _ => []
    end.
Definition U5: VariableStates :=
    match fold_unify (fun inner '(P, A) => unify penv 20 P A inner) (combine Ps5 As5) (Ongoing u5) with
    | Some (Ongoing u) => u
    | _ => []
    end.
(* E bound to Number, U to W *)
Definition b5: Bindings := bindings_of penv CList zs5 ++ map (fun v => (fst v, TypeArgument invariant ref (final_value_of penv U5 (fst v)))) ovars5.

Example member_call_in_generic_code_instance: unify_terminates_on penv bound ->
    (exists n, is_assignable_to penv n (gref pW) tNumber = Some true)
    /\ (exists n, is_assignable_to penv n (RootResolved None CBox [arg output ref (gref pW)])
        (RootResolved None CBox [arg output any_ownership (gref pW)]) = Some true).
Proof.
    intros terminates.
    pose proof (member_call_in_generic_code_sound penv wf intersect_no_vars supertype_no_vars bound declared_wf terminates
        intersect_in_fragment supertype_in_fragment (intersect_below terminates) (supertype_above terminates)
        (fun _ => True) (fun _ => True)
        ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) I I ltac:(intros; exact I) ltac:(intros; exact I)
        ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I)
        ltac:(intros; exact I) ltac:(intros; exact I)
        20 None CList cvars5 ovars5 None CList ys5 u5 (Some mutable) CArrayList xs5 zs5 10 Ps5 As5 20 U5
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) eq_refl
        ltac:(cbn; constructor; [intros [H|[]]; discriminate H|constructor; [intros []|constructor]])
        ltac:(intros p bnd [H|[H|[]]]; injection H as <- <-; reflexivity)
        ltac:(intros p bnd [H|[H|[]]]; injection H as <- <-; reflexivity)
        eq_refl ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) eq_refl
        ltac:(intros x [<-|[]]; reflexivity)) as H.
    destruct H as [_ Hall].
    - (* the type argument of the object, Number, within the bound of E *)
      intros i p bnd z H1 H2. destruct i as [|i]; [|destruct i; discriminate H1]. cbn in H1. injection H1 as <- <-.
      vm_compute in H2. injection H2 as <-. exists ref, tNumber, 5. split; [reflexivity|vm_compute; reflexivity].
    - intros P [<-|[<-|[]]]; (split; [reflexivity|]); vm_compute;
        repeat split; try (left; reflexivity); try (right; left; reflexivity); try reflexivity; intros q Hq; discriminate Hq.
    - intros P [<-|[<-|[]]]; reflexivity.
    - intros A [<-|[<-|[]]]; (split; [split; [reflexivity|exact I]|]); (split; [reflexivity|]); (split; [|exact I]);
        vm_compute; tauto.
    - intros; exact I.
    - vm_compute. reflexivity.
    - destruct (Hall b5 eq_refl) as [_ [_ [_ [_ Hfin]]]].
      split; [exact (Hfin _ _ (or_introl eq_refl))|exact (Hfin _ _ (or_intror (or_introl eq_refl)))].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 6. GenericCode.generic_member_call_with_bounded_variables_instantiated                         *)
(*                                                                                                *)
(*   interface List<E> { fn pick<U : Number, T : List<out U>>(self, x: E, u: U, t: T) }             *)
(*   fn caller<W : Number>(list: List<Number>, w: W, ws: ArrayList<W>) { list.pick(w, w, ws) }      *)
(*   caller::<Int>(...)                                                                           *)
(*                                                                                                *)
(* The bound of T mentions the type variable U: it is the static upper bound of T, which the lower *)
(* bound ArrayList<W> is checked against with U in place, inferring U >= W from it as well. At run *)
(* time W is Int, and the final values, `W` for U and `ArrayList<W>` for T, instantiated so, are   *)
(* within the bounds, and the arguments fit the parameters.                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Definition ST: EType := RootResolved None CList [arg output ref (tvar pU)].
Definition ovars6: list (TypeParameterId * EType) := [(pU, tNumber); (pT, ST)].
Definition Ps6: list EType := [tvar pL; tvar pU; tvar pT].
Definition As6: list EType := [gref pW; gref pW; RootResolved None CArrayList [arg invariant ref (gref pW)]].
Definition sigma6: Bindings := [(pW, arg invariant ref tInt)].
Definition u6: VariableStates :=
    match unify penv 20 (RootResolved None CList (map receiver_leaf cvars5)) (RootResolved None CList ys5)
        (for_inference_of (cvars5 ++ ovars6) (map fst cvars5)) with
    | Some (Ongoing u) => u
    | _ => []
    end.
Definition U6: VariableStates :=
    match fold_unify (fun inner '(P, A) => unify penv 20 P A inner) (combine Ps6 As6) (Ongoing u6) with
    | Some (Ongoing u) => u
    | _ => []
    end.
Definition fv6 (p: TypeParameterId): EType := final_value_of penv U6 p.

Example generic_member_call_instance: unify_terminates_on penv bound ->
    (* the final values, instantiated, within the bounds so instantiated: Int below Number, and
       ArrayList<Int> below List<out Int> *)
    (exists n, is_assignable_to penv n tInt tNumber = Some true)
    /\ (exists n, is_assignable_to penv n (RootResolved None CArrayList [arg invariant ref tInt])
        (RootResolved None CList [arg output ref tInt]) = Some true)
    (* the arguments, instantiated, fit the parameters so instantiated *)
    /\ (exists n, is_assignable_to penv n tInt tNumber = Some true)
    /\ (exists n, is_assignable_to penv n tInt tInt = Some true)
    /\ (exists n, is_assignable_to penv n (RootResolved None CArrayList [arg invariant ref tInt])
        (RootResolved None CArrayList [arg invariant ref tInt]) = Some true).
Proof.
    intros terminates.
    edestruct (generic_member_call_with_bounded_variables_instantiated penv wf intersect_no_vars supertype_no_vars bound
        declared_wf terminates intersect_in_fragment supertype_in_fragment (intersect_below terminates)
        (supertype_above terminates) intersect_generic supertype_generic supertype_bottom_only
        [pW] sigma6 20 None CList cvars5 ovars6 None CList ys5 u6 (Some mutable) CArrayList xs5 zs5 10 Ps6 As6 20 U6 fv6)
        as [Hfv Hargs].
    - (* sigma binds the type parameter of the caller to a class type within its bound *)
      intros p o x E. cbn in E. destruct (param_eqb p pW); [injection E as <- <-; reflexivity|discriminate E].
    - intros p [<-|[]]. exists ref, tInt. split; [reflexivity|]. split; [reflexivity|]. exists 5. vm_compute. reflexivity.
    - intros p [<-|[]]. split; [reflexivity|]. split; [exact I|]. vm_compute. tauto.
    - intros q [<-|[]]. cbn. intros [E|[E|[E|[]]]]; discriminate E.
    - discriminate.
    - discriminate.
    - discriminate.
    - reflexivity.
    - cbn. constructor; [intros [E|[E|[]]]; discriminate E|]. constructor; [intros [E|[]]; discriminate E|].
      constructor; [intros []|constructor].
    - (* the static upper bounds: E's without type variables *)
      intros p S [E|[]]. injection E as <- <-. split; [reflexivity|]. split; [vm_compute; reflexivity|].
      split; [intros _; split; [split; [exact (top_gfrag penv wf)|exact I]|exact (caller_top penv wf bound [pW])]|].
      intros E. discriminate E.
    - (* U's without type variables, T's with *)
      intros p S [E|[E|[]]]; injection E as <- <-.
      + split; [reflexivity|]. split; [vm_compute; reflexivity|].
        split; [intros _; split; [split; [reflexivity|exact I]|]|intros E; discriminate E].
        split; [reflexivity|]. split; [exact I|]. vm_compute. tauto.
      + split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [intros E; discriminate E|].
        intros _. split; [intros C [<-|[]]; split; vm_compute; reflexivity|]. intros cs E. discriminate E.
    - constructor; constructor.
    - intros p S q S' [E|[]] [E'|[E'|[]]]; injection E as <- <-; injection E' as <- <-; vm_compute; lia.
    - reflexivity.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - vm_compute. reflexivity.
    - reflexivity.
    - intros x [<-|[]]. reflexivity.
    - intros P [<-|[<-|[<-|[]]]]; (split; [reflexivity|]); (split; [intros C [<-|[]]; reflexivity|reflexivity]).
    - intros P [<-|[<-|[<-|[]]]]; reflexivity.
    - intros A [<-|[<-|[<-|[]]]]; (split; [split; [reflexivity|exact I]|]); (split; [reflexivity|]);
        (split; [reflexivity|]); (split; [exact I|]); vm_compute; props.
    - vm_compute. reflexivity.
    - (* each variable whose bound has type variables has a lower bound *)
      intros p S st [E|[E|[]]]; injection E as <- <-; [intros E; discriminate E|intros _ E; discriminate E].
    - intros p S st [E|[E|[]]]; injection E as <- <-; [intros E; discriminate E|].
      intros _ E. vm_compute in E. injection E as <-. intros E. discriminate E.
    - (* fv6 are the final values *)
      intros p S st [E|[E|[]]]; injection E as <- <-; intros E; vm_compute in E; injection E as <-; vm_compute; reflexivity.
    - exact eq_refl.
    - intros i p S z E1 E2. destruct i as [|i]; [|destruct i; discriminate E1]. cbn in E1. injection E1 as <- <-.
      vm_compute in E2. injection E2 as <-. exists ref, tNumber. split; [reflexivity|]. cbn. exists 5. vm_compute. reflexivity.
    - split; [exact (Hfv pU tNumber (or_introl eq_refl) tNumber (or_introl eq_refl))|].
      split; [exact (Hfv pT ST (or_intror (or_introl eq_refl)) ST (or_introl eq_refl))|].
      split; [exact (Hargs _ _ (or_introl eq_refl))|].
      split; [exact (Hargs _ _ (or_intror (or_introl eq_refl)))|].
      exact (Hargs _ _ (or_intror (or_intror (or_introl eq_refl)))).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 7. Overrides.override_parameter                                                                *)
(*                                                                                                *)
(*   interface List<E> { fn addAll(self, from: Box<out E>) }                                        *)
(*   class ArrayList<E> : List<E> { override fn addAll(self, from: Box<out E>) }                    *)
(*   (list: List<Int>).addAll(...)               // the object: ArrayList<Int>                     *)
(*                                                                                                *)
(* The parameter of the override, its type parameters bound to the object's, is that of List with *)
(* E bound to the object's type argument as a List: `Box<out Int>`.                                *)
(* ---------------------------------------------------------------------------------------------- *)

Example override_parameter_instance:
    instantiate penv (bindings_of penv CArrayList [arg invariant ref tInt])
        (instantiate penv (bindings_of penv CList (supertype_arguments penv CArrayList CList))
            (RootResolved None CBox [arg output ref (gref pL)]))
    = instantiate penv (bindings_of penv CList (parameterized_supertype_arguments penv CArrayList [arg invariant ref tInt] CList))
        (RootResolved None CBox [arg output ref (gref pL)])
    /\ instantiate penv (bindings_of penv CList (parameterized_supertype_arguments penv CArrayList [arg invariant ref tInt] CList))
        (RootResolved None CBox [arg output ref (gref pL)])
       = RootResolved None CBox [arg output ref tInt].
Proof.
    split; [|vm_compute; reflexivity].
    exact (override_parameter penv wf CList CArrayList ltac:(discriminate) ltac:(discriminate) eq_refl
        [arg invariant ref tInt] eq_refl ltac:(intros x [<-|[]]; reflexivity)
        (RootResolved None CBox [arg output ref (gref pL)])
        ltac:(cbn; split; [|exact I]; split; [intros q Hq; discriminate Hq|eexists; reflexivity])).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify_always_terminates is false                                                               *)
(*                                                                                                *)
(*   interface Cn<X>                                                                              *)
(*   fn f<T : Cn<Cn<in T>>>(t: T) { val c: Cn<in T> = t }                                          *)
(*                                                                                                *)
(* T is assigned to `Cn<in T>` by its bound, `Cn<Cn<in T>>`; the in-variant type argument then     *)
(* asks whether `Cn<in T>` takes T, the question it started with. unify asks it again and again,   *)
(* and gives no answer with any fuel. The program is well-formed, its bounds of the fragment, its  *)
(* inheritance tame (it has none), and its class table finite: unify_always_terminates claims an    *)
(* answer. tame_inheritance rules out contravariance in the type arguments of supertypes, for the  *)
(* example of Kennedy and Pierce; an F-bound brings it in all the same. The theorems of generic    *)
(* code therefore take unify_terminates_on, about the environment at hand, and are about the       *)
(* programs where unify terminates. The frontend finishes on this one by failing a goal that comes *)
(* up again (RootResolvedTypeReference.unify), which the model doesn't have.                       *)
(* ---------------------------------------------------------------------------------------------- *)

Module Counterexample.

Definition Cn := some_class 1.
Definition pX: TypeParameterId := 1.
Definition pT: TypeParameterId := 2.
Definition refT: EType := Generic (mkGenericRef None false pT []).
Definition target: EType := RootResolved None Cn [TypeArgument input ref refT].
Definition boundT: EType := RootResolved None Cn [TypeArgument invariant ref target].

Definition kdecl (c: Class): ClassDecl :=
    match c with
    | nothing => {| kind := class_kind; is_const := true; is_non_token := true; type_parameters := []; supertypes := []; fields := [] |}
    | some_class 1 => {| kind := interface_kind; is_const := false; is_non_token := true; type_parameters := [{| param_id := pX; prescribed_ownership := None |}];
                         supertypes := []; fields := [] |}
    | _ => {| kind := interface_kind; is_const := false; is_non_token := true; type_parameters := []; supertypes := []; fields := [] |}
    end.

Definition kenv: Environment := {|
    declaration_of := kdecl;
    supertypes_of := fun _ => [];
    closest_common_super_class := fun _ => any;
    parameterized_supertype := fun _ super => RootResolved None super [];
    closest_common_supertype_with := fun a _ => a;
    intersect := fun a _ => a;
    parameter_bound := fun p => match p with 2 => boundT | _ => top_type end;
    parameter_rank := fun _ => 0;
|}.

Lemma ksub: forall a b, base_type_is_subtype_of kenv a b = true -> a = b \/ b = any \/ a = nothing.
Proof.
    intros a b H. unfold base_type_is_subtype_of in H. unfold class_eqb at 1 in H.
    destruct (Class_eq_dec b a) as [<-|Hne]; [left; reflexivity|].
    destruct a, b; cbn in H; try discriminate H; auto.
Qed.

Lemma kwf: wellformed kenv.
Proof.
    constructor.
    - intros a b c [].
    - reflexivity.
    - intros c c' H1 H2. destruct (ksub _ _ H1) as [E|[E|E]]; subst; [reflexivity| |];
        destruct (ksub _ _ H2) as [E|[E|E]]; subst; first [reflexivity|discriminate].
    - intros [|[|[|n]]|]; cbn; repeat constructor; cbn; tauto.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros sub super Hne Hn H. destruct (ksub _ _ H) as [E|[E|E]]; [contradiction|subst|contradiction].
      cbn. split; [reflexivity|intros t []].
    - intros a b c Hab Hbc Hac Ha Hb H1 H2. destruct (ksub _ _ H2) as [E|[E|E]]; [contradiction|subst|contradiction].
      reflexivity.
    - intros sub super t [].
    - intros sub super t [].
    - intros [|[|[|p]]]; reflexivity.
    - intros [|[|[|p]]]; reflexivity.
    - intros [|[|[|p]]]; reflexivity.
Qed.

Lemma kbounds: bounds_wellformed kenv (parameter_bound kenv).
Proof. constructor; [reflexivity|]. intros [|[|[|p]]]; reflexivity. Qed.

Lemma kfinite: finitely_many_templates kenv.
Proof. exists []. intros sub super H. contradiction H. reflexivity. Qed.

Lemma ktame: tame_inheritance kenv.
Proof.
    split.
    - exists (fun _ => 0). intros p q ex [sub [super [c [arguments [j [a [_ [_ [_ [Hin [Ha _]]]]]]]]]]].
      cbn in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. destruct j; discriminate Ha.
    - intros sub super. reflexivity.
Qed.

(* Three steps of fuel later, unify asks the same *)
Lemma loops: forall n, unify kenv n target refT (Ongoing []) = None.
Proof.
    intros n. induction n as [n IH] using (well_founded_induction lt_wf).
    destruct n as [|[|[|n]]]; [reflexivity|reflexivity|reflexivity|].
    simpl. unfold unify_arguments. simpl. unfold unify_type_argument. simpl. rewrite (IH n ltac:(lia)). reflexivity.
Qed.

End Counterexample.

Theorem unify_always_terminates_is_false: ~ unify_always_terminates.
Proof.
    intros H. destruct (H Counterexample.kenv (parameter_bound Counterexample.kenv) Counterexample.kwf Counterexample.kbounds
        Counterexample.kfinite Counterexample.ktame Counterexample.kwf Counterexample.kbounds
        Counterexample.target Counterexample.refT [] eq_refl eq_refl I I) as [n Hn].
    exact (Hn (Counterexample.loops n)).
Qed.
