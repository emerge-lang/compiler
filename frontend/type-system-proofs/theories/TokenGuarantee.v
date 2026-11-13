(* ---------------------------------------------------------------------------------------------- *)
(* What the token rules guarantee, at run time.                                                    *)
(*                                                                                                *)
(* The rest of the proofs is about unify: which assignments the frontend accepts. This file is     *)
(* about what follows for a running program, which no test of the frontend can show: that the      *)
(* rules of docs/tokens.md are enough for the guarantee they are there for.                        *)
(*                                                                                                *)
(*   types_stay_true        every reference leads to an object of its type, and where the type     *)
(*                          cannot be a token, to an object that is none and has no type argument  *)
(*                          that may be one (preservation)                                         *)
(*   no_token_behind_a_non_token                                                                  *)
(*                          nothing reachable through a reference whose type cannot be a token is  *)
(*                          a token                                                                *)
(*   no_token_no_effect     code that starts with no reference whose type may be a token never     *)
(*                          holds a token it did not construct itself, constructs none that takes  *)
(*                          authority, and leaves every token that was there as it was             *)
(*                                                                                                *)
(* The model is its own and small: it shares nothing with Model.v and Subtyping.v. It has classes  *)
(* with member variables, interfaces, the four mutabilities, `& NonToken`, one type parameter per  *)
(* class and per function, a heap, and statements that copy a reference, read and write a member   *)
(* variable, and construct an object. The code that runs is the body of a generic function; the    *)
(* theorems hold for every type its parameter is instantiated with.                                *)
(*                                                                                                *)
(* What it leaves out:                                                                             *)
(*   * more than one type parameter, bounds other than a class or interface without type           *)
(*     arguments, bounds on the parameter of a class, variance: type arguments are invariant       *)
(*   * member access through a reference whose type argument is neither free of the type parameter *)
(*     nor the parameter itself (`Box<Box<T>>` in generic code); such types can be passed on       *)
(*   * that the mutability of a reference limits its type arguments                                *)
(*   * nullability, intersections other than with NonToken, casts (which can forget a token, see   *)
(*     docs/tokens.md), closures, exceptions, function calls (a function is a list of statements   *)
(*     here, its parameters the variables that are set when it starts)                             *)
(*   * the rules of mutability and of ownership. Assignability is subtyping and the token rule     *)
(*     here, and nothing else: an assignment from `read` to `mut` is accepted. So the theorems     *)
(*     hold whatever the frontend rejects on top, and do not rest on the mutability rules being    *)
(*     sound.                                                                                      *)
(*                                                                                                *)
(* What the theorems turn out to need of the rules:                                                *)
(*   * rule 3 and rule 1, as one: a value that may be a token is not assignable to a type that     *)
(*     cannot be one (`assignable`), and a `const` type cannot be one (`may_be_token`)             *)
(*   * that a type argument counts: `Box<Clock>` may be a token. It is below NonToken by           *)
(*     inheritance, and only the token rule keeps it from being assigned there                     *)
(*   * rule 4, which is the token rule with the type parameter taken to be what its bound says     *)
(*   * of instantiation, that `m T` cannot be a token where `m` is `const` or the type for `T`     *)
(*     cannot be one (GenericTypeReference.instantiateAllParameters, `instantiate` here):          *)
(*     `const T` of a `mut Clock` is `own Clock & NonToken`                                        *)
(*   * of limitedTo, that a member variable read through any reference is `const` only if it is    *)
(*     declared `const` (`limited_const`)                                                          *)
(*   * of rule 5, that no token type is below NonToken, and that classes are final                 *)
(*   * rule 2, with the type parameter of the class taken to be no token, for the second and third *)
(*     theorem only: the first holds without it                                                    *)
(* They do not need that an implementation of a token interface is a token, nor that a class which *)
(* is no token class is below NonToken. Those serve the programmer: nothing unsound follows from   *)
(* a type that says "token" for a value that is none.                                              *)
(* ---------------------------------------------------------------------------------------------- *)

From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

Inductive Mutability := own | immutable | readonly | mutable.

Definition is_immutable (m: Mutability): bool :=
    match m with
    | immutable => true
    | _ => false
    end.

(* TypeMutability.limitedTo: the mutability of a member variable, seen through a reference *)
Definition limited_to (member limit: Mutability): Mutability :=
    match member with
    | own => readonly
    | mutable =>
        match limit with
        | mutable | own => mutable
        | readonly | immutable => readonly
        end
    | readonly => readonly
    | immutable => immutable
    end.

Lemma limited_const: forall member limit, is_immutable (limited_to member limit) = true -> is_immutable member = true.
Proof.
    intros [] []; simpl; intro H; exact H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Lists                                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

Fixpoint set_nth {T: Type} (l: list T) (i: nat) (a: T): list T :=
    match l with
    | [] => []
    | hd :: tl =>
        match i with
        | 0 => a :: tl
        | S i' => hd :: set_nth tl i' a
        end
    end.

Lemma set_nth_same: forall {T: Type} (l: list T) i a, i < length l -> nth_error (set_nth l i a) i = Some a.
Proof.
    induction l as [|hd tl IH]; intros i a Hn; simpl in Hn.
    - lia.
    - destruct i as [|i]; simpl.
      + reflexivity.
      + apply IH. lia.
Qed.

Lemma set_nth_other: forall {T: Type} (l: list T) i j a, i <> j -> nth_error (set_nth l i a) j = nth_error l j.
Proof.
    induction l as [|hd tl IH]; intros i j a Hne.
    - reflexivity.
    - destruct i as [|i], j as [|j]; simpl.
      + exfalso. apply Hne. reflexivity.
      + reflexivity.
      + reflexivity.
      + apply IH. lia.
Qed.

Lemma set_nth_length: forall {T: Type} (l: list T) i a, length (set_nth l i a) = length l.
Proof.
    induction l as [|hd tl IH]; intros i a.
    - reflexivity.
    - destruct i as [|i]; simpl.
      + reflexivity.
      + rewrite IH. reflexivity.
Qed.

Lemma in_bounds: forall {T: Type} (l: list T) i a, nth_error l i = Some a -> i < length l.
Proof.
    intros T l i a H. apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma nth_append_last: forall {T: Type} (l: list T) a, nth_error (l ++ [a]) (length l) = Some a.
Proof.
    intros T l a. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma append_back: forall {T: Type} (l: list T) a i b,
    nth_error (l ++ [a]) i = Some b -> nth_error l i = Some b \/ (i = length l /\ b = a).
Proof.
    intros T l a i b H. destruct (Nat.lt_ge_cases i (length l)) as [L|L].
    - left. rewrite nth_error_app1 in H by exact L. exact H.
    - right. rewrite nth_error_app2 in H by exact L.
      destruct (i - length l) as [|k] eqn:E; simpl in H.
      + split; [lia|congruence].
      + destruct k; discriminate.
Qed.

Lemma forall2_nth_left: forall {T0 T1: Type} (R: T0 -> T1 -> Prop) l1 l2 i a,
    Forall2 R l1 l2 -> nth_error l1 i = Some a -> exists b, nth_error l2 i = Some b /\ R a b.
Proof.
    intros T0 T1 R l1 l2 i a H. revert i. induction H as [|x y l1 l2 Hxy H IH]; intros i Hn.
    - destruct i; discriminate.
    - destruct i as [|i]; simpl in *.
      + assert (x = a) by congruence. subst x. exists y. split; [reflexivity|exact Hxy].
      + apply IH. exact Hn.
Qed.

Lemma forall2_nth_right: forall {T0 T1: Type} (R: T0 -> T1 -> Prop) l1 l2 i b,
    Forall2 R l1 l2 -> nth_error l2 i = Some b -> exists a, nth_error l1 i = Some a /\ R a b.
Proof.
    intros T0 T1 R l1 l2 i b H. revert i. induction H as [|x y l1 l2 Hxy H IH]; intros i Hn.
    - destruct i; discriminate.
    - destruct i as [|i]; simpl in *.
      + assert (y = b) by congruence. subst y. exists x. split; [reflexivity|exact Hxy].
      + apply IH. exact Hn.
Qed.

Lemma forall2_set: forall {T0 T1: Type} (R: T0 -> T1 -> Prop) l1 l2 i a b,
    Forall2 R l1 l2 -> nth_error l2 i = Some b -> R a b -> Forall2 R (set_nth l1 i a) l2.
Proof.
    intros T0 T1 R l1 l2 i a b H. revert i. induction H as [|x y l1 l2 Hxy H IH]; intros i Hn Hab.
    - constructor.
    - destruct i as [|i]; simpl in *.
      + assert (y = b) by congruence. subst y. constructor; assumption.
      + constructor; [exact Hxy|]. apply IH; assumption.
Qed.

Lemma forall2_impl: forall {T0 T1: Type} (R R': T0 -> T1 -> Prop) l1 l2,
    Forall2 R l1 l2 -> (forall a b, R a b -> R' a b) -> Forall2 R' l1 l2.
Proof.
    intros T0 T1 R R' l1 l2 H Himpl. induction H; constructor; auto.
Qed.

Lemma forall2_compose: forall {T0 T1 T2: Type} (R0: T0 -> T1 -> Prop) (R1: T0 -> T2 -> Prop) (R: T1 -> T2 -> Prop) xs ys zs,
    Forall2 R0 xs ys -> Forall2 R1 xs zs -> (forall x y z, R0 x y -> R1 x z -> R y z) -> Forall2 R ys zs.
Proof.
    intros T0 T1 T2 R0 R1 R xs ys zs H. revert zs. induction H as [|x y xs ys Hxy H IH]; intros zs HQ HR.
    - inversion HQ; subst. constructor.
    - inversion HQ; subst. constructor.
      + eapply HR; eassumption.
      + apply IH; assumption.
Qed.

(* TypeMutability.intersect, Model.intersect_mutability *)
Definition intersect_mutability (m0 m1: Mutability): Mutability :=
    match m0, m1 with
    | mutable, mutable => mutable
    | mutable, readonly => mutable
    | mutable, immutable => own
    | mutable, own => own
    | readonly, readonly => readonly
    | readonly, immutable => immutable
    | readonly, mutable => mutable
    | readonly, own => own
    | immutable, immutable => immutable
    | immutable, own => own
    | immutable, readonly => immutable
    | immutable, mutable => own
    | own, _ => own
    end.

Lemma intersect_not_const: forall m0 m1,
    is_immutable m0 = false -> is_immutable m1 = false -> is_immutable (intersect_mutability m0 m1) = false.
Proof.
    intros [] []; simpl; intros; try reflexivity; congruence.
Qed.

Section Guarantee.

(* The classes and interfaces of a program *)
Variable Base: Type.

(* A type. Classes and interfaces have no type parameter or one, functions have one: `T` is the parameter of
   the declaration the type is written in. *)
Inductive Ty :=
    (* a class or interface without a type argument, of a mutability, intersected with NonToken or not *)
    | Plain (m: Mutability) (b: Base) (nt: bool)
    (* one with a type argument: `m b<arg>` *)
    | Applied (m: Mutability) (b: Base) (arg: Ty) (nt: bool)
    (* `T`, or `m T` *)
    | Param (mo: option Mutability) (nt: bool).

Record Environment := mkEnvironment {
    (* inheritance, with every type below itself. A type with a type parameter passes it on to its supertypes
       that have one: `class ArrayIterator<T> : Iterator<T>` *)
    subtype: Base -> Base -> bool;
    (* emerge.core.NonToken *)
    non_token_type: Base;
    (* a class, and not an interface *)
    is_class: Base -> bool;
    (* declared `token` *)
    is_token: Base -> bool;
    (* a class that stands for state outside of the program: the root, which only the platform constructs, and
       the classes that take the root or another such token to construct (a unique class, through `take`) *)
    needs_authority: Base -> bool;
    (* the member variables of a class, which are the parameters of its constructor *)
    fields: Base -> list Ty;
}.

Variable env: Environment.

Definition is_non_token (b: Base): bool := subtype env b (non_token_type env).

Definition is_const_given (mo: option Mutability): bool :=
    match mo with
    | Some m => is_immutable m
    | None => false
    end.

(* BoundTypeReference.mayBeTokenUnless, Subtyping.may_be_token: a const type cannot be a token, nor can a type
   below NonToken none of whose type arguments may be one. pm: whether the type parameter may be bound to a
   token type. *)
Fixpoint may_be_token (pm: bool) (ty: Ty): bool :=
    match ty with
    | Plain m b nt => negb nt && negb (is_immutable m) && negb (is_non_token b)
    | Applied m b arg nt => negb nt && negb (is_immutable m) && (negb (is_non_token b) || may_be_token pm arg)
    | Param mo nt => negb nt && negb (is_const_given mo) && pm
    end.

(* mentions no type parameter *)
Fixpoint closed (ty: Ty): bool :=
    match ty with
    | Plain _ _ _ => true
    | Applied _ _ arg _ => closed arg
    | Param _ _ => false
    end.

Definition mutability_of (ty: Ty): Mutability :=
    match ty with
    | Plain m _ _ | Applied m _ _ _ => m
    | Param _ _ => readonly
    end.

Definition with_mutability (m: Mutability) (ty: Ty): Ty :=
    match ty with
    | Plain _ b nt => Plain m b nt
    | Applied _ b arg nt => Applied m b arg nt
    | Param _ nt => Param (Some m) nt
    end.

(* BoundIntersectionTypeReference.asNoToken *)
Definition as_non_token (ty: Ty): Ty :=
    match ty with
    | Plain m b _ => Plain m b true
    | Applied m b arg _ => Applied m b arg true
    | Param mo _ => Param mo true
    end.

(* GenericTypeReference.instantiateAllParameters: the type, with inst for the type parameter. A value of type
   `m T` is one of inst of a mutability that fits m. What is const is no token, and so is what inst says is
   none: `const T` of a `mut X` is an `own X`, which doesn't say so anymore, and is intersected with NonToken. *)
Fixpoint instantiate (inst: Ty) (ty: Ty): Ty :=
    match ty with
    | Plain _ _ _ => ty
    | Applied m b arg nt => Applied m b (instantiate inst arg) nt
    | Param None nt => if nt then as_non_token inst else inst
    | Param (Some m) nt =>
        if nt || is_immutable m || negb (may_be_token false inst)
        then as_non_token (with_mutability (intersect_mutability (mutability_of inst) m) inst)
        else with_mutability (intersect_mutability (mutability_of inst) m) inst
    end.

(* What the frontend makes sure of where classes and interfaces are declared *)
Record well_formed: Prop := {
    subtype_refl: forall a, subtype env a a = true;
    subtype_trans: forall a b c, subtype env a b = true -> subtype env b c = true -> subtype env a c = true;
    (* a class is inherited by nothing *)
    class_is_final: forall a c, is_class env c = true -> subtype env a c = true -> a = c;
    (* rule 5: no token type inherits from NonToken *)
    token_not_below_non_token: forall a, is_token env a = true -> is_non_token a = false;
    (* rule 2: a class that is no token class has no member variable whose type may be a token. The type
       parameter of the class is left to the instantiation, and taken to be none here. *)
    members_say: forall c, is_class env c = true -> is_token env c = false ->
        Forall (fun member => may_be_token false member = false) (fields env c);
    (* what stands for state outside of the program is a token class *)
    authority_is_token: forall c, needs_authority env c = true -> is_class env c = true /\ is_token env c = true;
}.

Hypothesis wf: well_formed.

Lemma non_token_is_no_token: forall b, is_non_token b = true -> is_token env b = false.
Proof.
    intros b H. destruct (is_token env b) eqn:E; [|reflexivity].
    rewrite (token_not_below_non_token wf b E) in H. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiation                                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma may_as_non_token: forall pm ty, may_be_token pm (as_non_token ty) = false.
Proof.
    intros pm []; reflexivity.
Qed.

Lemma closed_as_non_token: forall ty, closed (as_non_token ty) = closed ty.
Proof.
    intros []; reflexivity.
Qed.

Lemma closed_with_mutability: forall m ty, closed (with_mutability m ty) = closed ty.
Proof.
    intros m []; reflexivity.
Qed.

Lemma instantiate_closed: forall inst ty, closed ty = true -> instantiate inst ty = ty.
Proof.
    intros inst ty. induction ty as [m b nt|m b arg IH nt|mo nt]; simpl; intro H.
    - reflexivity.
    - rewrite (IH H). reflexivity.
    - discriminate.
Qed.

Lemma closed_instantiate: forall inst ty, closed inst = true -> closed (instantiate inst ty) = true.
Proof.
    intros inst ty H. induction ty as [m b nt|m b arg IH nt|mo nt]; simpl.
    - reflexivity.
    - exact IH.
    - destruct mo as [m|].
      + destruct (nt || is_immutable m || negb (may_be_token false inst));
          [rewrite closed_as_non_token|]; rewrite closed_with_mutability; exact H.
      + destruct nt; [rewrite closed_as_non_token|]; exact H.
Qed.

(* `m T` and `T & NonToken` may be a token only if they say so and the type for T may *)
Lemma param_instance_inv: forall inst mo nt,
    may_be_token false (instantiate inst (Param mo nt)) = true ->
    nt = false /\ is_const_given mo = false /\ may_be_token false inst = true.
Proof.
    intros inst mo nt H. destruct mo as [m|]; simpl in H; simpl.
    - destruct nt; simpl in H; [rewrite may_as_non_token in H; discriminate|].
      destruct (is_immutable m) eqn:Em; simpl in H; [rewrite may_as_non_token in H; discriminate|].
      destruct (may_be_token false inst) eqn:Ei; simpl in H; [|rewrite may_as_non_token in H; discriminate].
      repeat split; reflexivity.
    - destruct nt; simpl in H; [rewrite may_as_non_token in H; discriminate|].
      repeat split; try reflexivity. exact H.
Qed.

Lemma may_mutability: forall ty, closed ty = true -> may_be_token false ty = true -> is_immutable (mutability_of ty) = false.
Proof.
    intros [m b nt|m b arg nt|mo nt]; simpl; intros Hc H; try discriminate;
        destruct nt; simpl in H; try discriminate; destruct (is_immutable m); simpl in H; try discriminate; reflexivity.
Qed.

Lemma may_with_mutability: forall m ty,
    closed ty = true -> is_immutable m = false -> may_be_token false ty = true ->
    may_be_token false (with_mutability m ty) = true.
Proof.
    intros m' [m b nt|m b arg nt|mo nt]; simpl; intros Hc Hm H; try discriminate;
        rewrite Hm; destruct nt; simpl in *; try discriminate;
        destruct (is_immutable m); simpl in *; try discriminate; exact H.
Qed.

(* and then they do *)
Lemma param_instance_may: forall inst mo,
    closed inst = true -> may_be_token false inst = true -> is_const_given mo = false ->
    may_be_token false (instantiate inst (Param mo false)) = true.
Proof.
    intros inst mo Hc Hi Hcg. destruct mo as [m|]; simpl in *.
    - rewrite Hcg, Hi. simpl. apply may_with_mutability; [exact Hc| |exact Hi].
      apply intersect_not_const; [exact (may_mutability inst Hc Hi)|exact Hcg].
    - exact Hi.
Qed.

(* An instance may be a token only if the type says so, with the parameter taken for what its instance is *)
Lemma instantiate_says_no_more: forall pm inst ty,
    (may_be_token false inst = true -> pm = true) ->
    may_be_token false (instantiate inst ty) = true -> may_be_token pm ty = true.
Proof.
    intros pm inst ty Hpm. induction ty as [m b nt|m b arg IH nt|mo nt]; intro H.
    - exact H.
    - simpl in *. apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1. simpl.
      apply orb_true_iff in H2. apply orb_true_iff.
      destruct H2 as [H2|H2]; [left; exact H2|right; exact (IH H2)].
    - destruct (param_instance_inv _ _ _ H) as [Hnt [Hcg Hi]]. subst nt. simpl. rewrite Hcg. simpl.
      exact (Hpm Hi).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Assignability, and the types of statements                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* The bound of the type parameter of the function that runs: a class or interface without type arguments *)
Variable bound: Base.

(* rule 4: the parameter may be bound to a token type, unless its bound is below NonToken *)
Definition param_may: bool := negb (is_non_token bound).

(* Subtyping. Type arguments are invariant, and forgotten towards a type that has none; a type parameter is
   below what its bound is below. *)
Definition below (assignee target: Ty): Prop :=
    match assignee, target with
    | Plain _ ba _, Plain _ bt _ => subtype env ba bt = true
    | Applied _ ba _ _, Plain _ bt _ => subtype env ba bt = true
    | Applied _ ba arga _, Applied _ bt argt _ => subtype env ba bt = true /\ arga = argt
    | Param _ _, Param _ _ => True
    | Param _ _, Plain _ bt _ => subtype env bound bt = true
    | _, _ => False
    end.

(* Subtyping, and TokenRule.check: a value that may be a token is not assignable to a type that cannot be
   one. Nothing else: no rule of mutability. *)
Definition assignable (assignee target: Ty): Prop :=
    below assignee target
    /\ (may_be_token param_may assignee = true -> may_be_token param_may target = true).

(* What the type parameter of the function may be instantiated with: a type without type parameters that is
   assignable to the bound *)
Definition admissible (inst: Ty): Prop :=
    closed inst = true
    /\ match inst with
       | Plain _ b _ | Applied _ b _ _ => subtype env b bound = true
       | Param _ _ => False
       end
    /\ (may_be_token false inst = true -> is_non_token bound = false).

(* the type of a member variable, read through a reference *)
Definition seen_through (reference member: Ty): Ty :=
    match member with
    | Plain m b nt => Plain (limited_to m (mutability_of reference)) b nt
    | Applied m b arg nt => Applied (limited_to m (mutability_of reference)) b arg nt
    | Param mo nt => Param (option_map (fun m => limited_to m (mutability_of reference)) mo) nt
    end.

Definition base_of (ty: Ty): option Base :=
    match ty with
    | Plain _ b _ | Applied _ b _ _ => Some b
    | Param _ _ => None
    end.

(* The type of a member variable of the class of a reference, in the code that holds the reference: with the
   type argument of the reference for the parameter of the class. Where that argument is the parameter of the
   function, the member type reads as it is declared. Other type arguments that mention the parameter are left
   out. *)
Definition member_seen (reference member: Ty): option Ty :=
    match reference with
    | Plain _ _ _ => if closed member then Some member else None
    | Applied _ _ arg _ =>
        if closed arg then Some (instantiate arg member)
        else match arg with
             | Param None false => Some member
             | _ => None
             end
    | Param _ _ => None
    end.

(* the type of `C(...)`, or `C::<arg>(...)` *)
Definition new_type (c: Base) (arg: option Ty): Ty :=
    match arg with
    | None => Plain own c false
    | Some given => Applied own c given false
    end.

(* Variables are numbers; a context gives each its type *)
Definition Context := nat -> Ty.

Inductive Statement :=
    (* name = origin *)
    | Assign (name origin: nat)
    (* name = origin.i *)
    | ReadMember (name origin i: nat)
    (* set origin.i = value *)
    | WriteMember (origin i value: nat)
    (* name = c(values). A class that needs authority is constructed with a token that has it at hand, which is
       `take(world)` *)
    | Construct (name: nat) (c: Base) (arg: option Ty) (values: list nat) (lender: option nat).

Inductive typed (ctx: Context): Statement -> Prop :=
    | typed_assign: forall name origin,
        assignable (ctx origin) (ctx name) ->
        typed ctx (Assign name origin)
    | typed_read: forall name origin i c member seen,
        base_of (ctx origin) = Some c ->
        is_class env c = true ->
        nth_error (fields env c) i = Some member ->
        member_seen (ctx origin) member = Some seen ->
        assignable (seen_through (ctx origin) seen) (ctx name) ->
        typed ctx (ReadMember name origin i)
    | typed_write: forall origin i value c member seen,
        base_of (ctx origin) = Some c ->
        is_class env c = true ->
        nth_error (fields env c) i = Some member ->
        member_seen (ctx origin) member = Some seen ->
        assignable (ctx value) seen ->
        typed ctx (WriteMember origin i value)
    | typed_construct: forall name c arg values lender,
        is_class env c = true ->
        Forall2 (fun value member => exists seen,
            member_seen (new_type c arg) member = Some seen /\ assignable (ctx value) seen) values (fields env c) ->
        assignable (new_type c arg) (ctx name) ->
        (needs_authority env c = true ->
            exists holder granting, lender = Some holder /\ base_of (ctx holder) = Some granting
                /\ needs_authority env granting = true) ->
        typed ctx (Construct name c arg values lender).

(* ---------------------------------------------------------------------------------------------- *)
(* Running                                                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Record Object := mkObject {
    class_of: Base;
    (* the type argument the object was constructed with *)
    arg_of: option Ty;
    values_of: list nat;
}.

(* References are positions in the heap *)
Definition Heap := list Object.

(* The variables of the running code; one that is not set yet has no value *)
Definition Store := nat -> option nat.

Definition set (store: Store) (name addr: nat): Store :=
    fun other => if Nat.eqb other name then Some addr else store other.

(* inst: the type the parameter of the running function stands for *)
Inductive step (inst: Ty): Statement -> Heap -> Store -> Heap -> Store -> Prop :=
    | step_assign: forall h store name origin addr,
        store origin = Some addr ->
        step inst (Assign name origin) h store h (set store name addr)
    | step_read: forall h store name origin i addr obj addr',
        store origin = Some addr ->
        nth_error h addr = Some obj ->
        nth_error (values_of obj) i = Some addr' ->
        step inst (ReadMember name origin i) h store h (set store name addr')
    | step_write: forall h store origin i value addr obj addr',
        store origin = Some addr ->
        nth_error h addr = Some obj ->
        i < length (values_of obj) ->
        store value = Some addr' ->
        step inst (WriteMember origin i value) h store
            (set_nth h addr (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr'))) store
    | step_construct: forall h store name c arg values lender addrs,
        Forall2 (fun value addr => store value = Some addr) values addrs ->
        (forall holder, lender = Some holder -> exists addr, store holder = Some addr) ->
        step inst (Construct name c arg values lender) h store
            (h ++ [mkObject c (option_map (instantiate inst) arg) addrs]) (set store name (length h)).

Inductive runs (inst: Ty): list Statement -> Heap -> Store -> Heap -> Store -> Prop :=
    | runs_done: forall h store, runs inst [] h store h store
    | runs_step: forall statement rest h store h1 store1 h2 store2,
        step inst statement h store h1 store1 ->
        runs inst rest h1 store1 h2 store2 ->
        runs inst (statement :: rest) h store h2 store2.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant: types tell the truth                                                             *)
(* ---------------------------------------------------------------------------------------------- *)

(* An object that is no token, and whose type argument says that it holds none *)
Definition object_is_free (obj: Object): bool :=
    negb (is_token env (class_of obj))
    && match arg_of obj with
       | Some arg => negb (may_be_token false arg)
       | None => true
       end.

Lemma token_is_not_free: forall obj, is_token env (class_of obj) = true -> object_is_free obj = false.
Proof.
    intros obj H. unfold object_is_free. rewrite H. reflexivity.
Qed.

Definition shape_fits (obj: Object) (ty: Ty): Prop :=
    match ty with
    | Plain _ b _ => subtype env (class_of obj) b = true
    | Applied _ b arg _ => subtype env (class_of obj) b = true /\ arg_of obj = Some arg
    | Param _ _ => False
    end.

(* The reference leads to an object of the type, which has no type parameters; and if the type cannot be a
   token, to an object that is free of them *)
Definition fits (h: Heap) (addr: nat) (ty: Ty): Prop :=
    exists obj, nth_error h addr = Some obj
        /\ shape_fits obj ty
        /\ (may_be_token false ty = false -> object_is_free obj = true).

(* the type of a member variable of an object *)
Definition member_type (arg: option Ty) (member: Ty): Ty :=
    match arg with
    | Some given => instantiate given member
    | None => member
    end.

Definition arg_is_closed (arg: option Ty): Prop :=
    match arg with
    | Some given => closed given = true
    | None => True
    end.

Definition heap_ok (h: Heap): Prop :=
    forall addr obj, nth_error h addr = Some obj ->
        is_class env (class_of obj) = true
        /\ arg_is_closed (arg_of obj)
        /\ Forall2 (fun value member => fits h value (member_type (arg_of obj) member))
            (values_of obj) (fields env (class_of obj)).

Definition store_ok (inst: Ty) (h: Heap) (ctx: Context) (store: Store): Prop :=
    forall name addr, store name = Some addr -> fits h addr (instantiate inst (ctx name)).

(* every object of the one heap is in the other, of the same class and type argument *)
Definition keeps_kinds (h h': Heap): Prop :=
    forall addr obj, nth_error h addr = Some obj ->
        exists obj', nth_error h' addr = Some obj' /\ class_of obj' = class_of obj /\ arg_of obj' = arg_of obj.

Lemma fits_keeps: forall h h' addr ty, keeps_kinds h h' -> fits h addr ty -> fits h' addr ty.
Proof.
    intros h h' addr ty K [obj [Hn [Hs Ht]]]. destruct (K addr obj Hn) as [obj' [Hn' [Hc Ha]]].
    exists obj'. split; [exact Hn'|]. split.
    - destruct ty; simpl in *; rewrite ?Hc, ?Ha; exact Hs.
    - unfold object_is_free. rewrite Hc, Ha. exact Ht.
Qed.

Lemma keeps_append: forall h obj, keeps_kinds h (h ++ [obj]).
Proof.
    intros h obj addr obj0 Hn. exists obj0. split; [|split; reflexivity].
    rewrite nth_error_app1 by (eapply in_bounds; exact Hn). exact Hn.
Qed.

Lemma keeps_update: forall h addr obj obj',
    nth_error h addr = Some obj -> class_of obj' = class_of obj -> arg_of obj' = arg_of obj ->
    keeps_kinds h (set_nth h addr obj').
Proof.
    intros h addr obj obj' Hn Hc Ha addr0 obj0 Hn0. destruct (Nat.eq_dec addr addr0) as [E|E].
    - subst addr0. exists obj'. split.
      + apply set_nth_same. eapply in_bounds. exact Hn.
      + assert (obj0 = obj) by congruence. subst obj0. split; [exact Hc|exact Ha].
    - exists obj0. split; [|split; reflexivity]. rewrite set_nth_other by exact E. exact Hn0.
Qed.

(* the object at a position after one was replaced by another of its class and type argument *)
Lemma update_back: forall h addr obj obj' addr0 obj0,
    nth_error h addr = Some obj -> class_of obj' = class_of obj -> arg_of obj' = arg_of obj ->
    nth_error (set_nth h addr obj') addr0 = Some obj0 ->
    exists obj1, nth_error h addr0 = Some obj1
        /\ class_of obj1 = class_of obj0 /\ object_is_free obj1 = object_is_free obj0
        /\ (addr0 <> addr -> obj1 = obj0) /\ (addr0 = addr -> obj0 = obj').
Proof.
    intros h addr obj obj' addr0 obj0 Hn Hc Ha H0. destruct (Nat.eq_dec addr addr0) as [E|E].
    - subst addr0. rewrite set_nth_same in H0 by (eapply in_bounds; exact Hn).
      assert (obj0 = obj') by congruence. subst obj0.
      exists obj. split; [exact Hn|]. split; [symmetry; exact Hc|].
      split; [unfold object_is_free; rewrite Hc, Ha; reflexivity|].
      split; [intro C; exfalso; apply C; reflexivity|intros _; reflexivity].
    - rewrite set_nth_other in H0 by exact E.
      exists obj0. split; [exact H0|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; reflexivity|intro C; exfalso; apply E; symmetry; exact C].
Qed.

Lemma shape_as_non_token: forall obj ty, shape_fits obj (as_non_token ty) = shape_fits obj ty.
Proof.
    intros obj []; reflexivity.
Qed.

Lemma shape_with_mutability: forall obj m ty, shape_fits obj (with_mutability m ty) = shape_fits obj ty.
Proof.
    intros obj m []; reflexivity.
Qed.

Lemma shape_param: forall obj inst mo nt, shape_fits obj (instantiate inst (Param mo nt)) = shape_fits obj inst.
Proof.
    intros obj inst mo nt. destruct mo as [m|]; simpl.
    - destruct (nt || is_immutable m || negb (may_be_token false inst));
        [rewrite shape_as_non_token|]; apply shape_with_mutability.
    - destruct nt; [apply shape_as_non_token|reflexivity].
Qed.

Lemma shape_below: forall inst obj assignee target,
    admissible inst -> below assignee target ->
    shape_fits obj (instantiate inst assignee) -> shape_fits obj (instantiate inst target).
Proof.
    intros inst obj assignee target [_ [Hbase _]] Hb Hs.
    destruct assignee as [ma ba nta|ma ba arga nta|moa nta], target as [mt bt ntt|mt bt argt ntt|mot ntt];
        simpl in Hb; try contradiction.
    - simpl in *. exact (subtype_trans wf _ _ _ Hs Hb).
    - simpl in *. destruct Hs as [Hs _]. exact (subtype_trans wf _ _ _ Hs Hb).
    - simpl in *. destruct Hb as [Hb E]. subst arga. destruct Hs as [Hs Ha].
      split; [exact (subtype_trans wf _ _ _ Hs Hb)|exact Ha].
    - rewrite shape_param in Hs. simpl.
      destruct inst as [mi bi nti|mi bi argi nti|moi nti]; simpl in *; try contradiction.
      + exact (subtype_trans wf _ _ _ (subtype_trans wf _ _ _ Hs Hbase) Hb).
      + destruct Hs as [Hs _]. exact (subtype_trans wf _ _ _ (subtype_trans wf _ _ _ Hs Hbase) Hb).
    - rewrite shape_param in *. exact Hs.
Qed.

(* The token rule holds of the instances, where it holds of the types of the generic code *)
Lemma token_rule_instantiated: forall inst assignee target,
    admissible inst -> below assignee target ->
    (may_be_token param_may assignee = true -> may_be_token param_may target = true) ->
    may_be_token false (instantiate inst assignee) = true ->
    may_be_token false (instantiate inst target) = true.
Proof.
    intros inst assignee target [Hc [Hbase Hpm]] Hb Hrule Ha.
    assert (Hpm': may_be_token false inst = true -> param_may = true)
        by (intro Hi; unfold param_may; rewrite (Hpm Hi); reflexivity).
    pose proof (Hrule (instantiate_says_no_more _ _ _ Hpm' Ha)) as Ht.
    destruct target as [mt bt ntt|mt bt argt ntt|mot ntt].
    - exact Ht.
    - destruct assignee as [ma ba nta|ma ba arga nta|moa nta]; simpl in Hb; try contradiction.
      destruct Hb as [Hb E]. subst arga. simpl in Ht, Ha. simpl.
      apply andb_true_iff in Ht. destruct Ht as [Ht1 _]. rewrite Ht1. simpl.
      apply andb_true_iff in Ha. destruct Ha as [_ Ha2].
      apply orb_true_iff in Ha2. apply orb_true_iff.
      destruct Ha2 as [Ha2|Ha2]; [left|right; exact Ha2].
      apply negb_true_iff in Ha2. apply negb_true_iff.
      destruct (is_non_token bt) eqn:Ebt; [|reflexivity].
      unfold is_non_token in *. rewrite (subtype_trans wf _ _ _ Hb Ebt) in Ha2. discriminate.
    - destruct assignee as [ma ba nta|ma ba arga nta|moa nta]; simpl in Hb; try contradiction.
      destruct (param_instance_inv _ _ _ Ha) as [_ [_ Hi]].
      simpl in Ht. apply andb_true_iff in Ht. destruct Ht as [Ht1 _].
      apply andb_true_iff in Ht1. destruct Ht1 as [Hn Hcg].
      apply negb_true_iff in Hn. apply negb_true_iff in Hcg. subst ntt.
      exact (param_instance_may inst mot Hc Hi Hcg).
Qed.

(* The substitution lemma of this model: what generic code may assign, it may assign in every instance *)
Lemma fits_assignable: forall inst h addr assignee target,
    admissible inst -> assignable assignee target ->
    fits h addr (instantiate inst assignee) -> fits h addr (instantiate inst target).
Proof.
    intros inst h addr assignee target Hadm [Hb Hrule] [obj [Hn [Hs Hclaim]]].
    exists obj. split; [exact Hn|]. split.
    - exact (shape_below inst obj assignee target Hadm Hb Hs).
    - intro Hno. apply Hclaim.
      destruct (may_be_token false (instantiate inst assignee)) eqn:E; [|reflexivity].
      rewrite (token_rule_instantiated inst assignee target Hadm Hb Hrule E) in Hno. discriminate.
Qed.

(* Reading a member variable through a reference makes its type no promise that its declared type doesn't make *)
Lemma seen_through_says_no_more: forall inst reference member,
    closed inst = true ->
    may_be_token false (instantiate inst (seen_through reference member)) = false ->
    may_be_token false (instantiate inst member) = false.
Proof.
    intros inst reference member Hc. destruct member as [m b nt|m b arg nt|mo nt].
    - simpl. destruct nt; simpl; intro H; [reflexivity|].
      destruct (is_immutable (limited_to m (mutability_of reference))) eqn:E; simpl in H.
      + rewrite (limited_const _ _ E). reflexivity.
      + destruct (is_immutable m); simpl; [reflexivity|exact H].
    - simpl. destruct nt; simpl; intro H; [reflexivity|].
      destruct (is_immutable (limited_to m (mutability_of reference))) eqn:E; simpl in H.
      + rewrite (limited_const _ _ E). reflexivity.
      + destruct (is_immutable m); simpl; [reflexivity|exact H].
    - unfold seen_through. intro H.
      destruct (may_be_token false (instantiate inst (Param mo nt))) eqn:E; [|reflexivity].
      destruct (param_instance_inv _ _ _ E) as [Hnt [Hcg Hi]]. subst nt.
      rewrite param_instance_may in H; [discriminate|exact Hc|exact Hi|].
      destruct mo as [m|]; simpl in *; [|reflexivity].
      destruct (is_immutable (limited_to m (mutability_of reference))) eqn:E2; [|reflexivity].
      rewrite (limited_const _ _ E2) in Hcg. discriminate.
Qed.

Lemma fits_seen_through: forall inst h addr reference member,
    closed inst = true ->
    fits h addr (instantiate inst member) -> fits h addr (instantiate inst (seen_through reference member)).
Proof.
    intros inst h addr reference member Hc [obj [Hn [Hs Ht]]]. exists obj. split; [exact Hn|]. split.
    - destruct member as [m b nt|m b arg nt|mo nt].
      + exact Hs.
      + exact Hs.
      + unfold seen_through. rewrite shape_param in *. exact Hs.
    - intro H. apply Ht. exact (seen_through_says_no_more inst reference member Hc H).
Qed.

Lemma store_set: forall inst h ctx store name addr,
    store_ok inst h ctx store -> fits h addr (instantiate inst (ctx name)) ->
    store_ok inst h ctx (set store name addr).
Proof.
    intros inst h ctx store name addr Hs Hf origin addr0 Hy. unfold set in Hy.
    destruct (Nat.eqb origin name) eqn:E.
    - apply Nat.eqb_eq in E. subst origin. assert (addr0 = addr) by congruence. subst addr0. exact Hf.
    - exact (Hs origin addr0 Hy).
Qed.

(* the object a reference of a class type leads to is of that class *)
Lemma class_of_fits: forall inst h addr reference c obj,
    fits h addr (instantiate inst reference) -> base_of reference = Some c -> is_class env c = true ->
    nth_error h addr = Some obj ->
    class_of obj = c /\ shape_fits obj (instantiate inst reference).
Proof.
    intros inst h addr reference c obj [obj1 [Hn1 [Hs _]]] Hb Hc Hn.
    assert (obj1 = obj) by congruence. subst obj1. split; [|exact Hs].
    destruct reference as [m b nt|m b arg nt|mo nt]; simpl in *; try discriminate.
    - assert (b = c) by congruence. subst b. exact (class_is_final wf _ _ Hc Hs).
    - assert (b = c) by congruence. subst b. destruct Hs as [Hs _]. exact (class_is_final wf _ _ Hc Hs).
Qed.

(* What the code takes the type of a member variable to be is what the object says it is *)
Lemma member_seen_at_runtime: forall inst obj reference member seen,
    closed inst = true -> shape_fits obj (instantiate inst reference) ->
    member_seen reference member = Some seen ->
    member_type (arg_of obj) member = instantiate inst seen.
Proof.
    intros inst obj reference member seen Hc Hs Hseen.
    destruct reference as [m b nt|m b arg nt|mo nt]; simpl in Hseen.
    - destruct (closed member) eqn:E; [|discriminate].
      assert (seen = member) by congruence. subst seen. rewrite (instantiate_closed inst member E).
      unfold member_type. destruct (arg_of obj); [apply instantiate_closed; exact E|reflexivity].
    - simpl in Hs. destruct Hs as [_ Harg]. rewrite Harg. unfold member_type.
      destruct (closed arg) eqn:E.
      + assert (seen = instantiate arg member) by congruence. subst seen.
        rewrite (instantiate_closed inst arg E). symmetry. apply instantiate_closed.
        apply closed_instantiate. exact E.
      + destruct arg as [ma ba nta|ma ba arga nta|moa nta]; try discriminate.
        destruct moa; try discriminate. destruct nta; try discriminate.
        assert (seen = member) by congruence. subst seen. reflexivity.
    - discriminate.
Qed.

Lemma member_fits: forall inst h addr reference c obj i addr' member seen,
    closed inst = true -> heap_ok h -> fits h addr (instantiate inst reference) ->
    base_of reference = Some c -> is_class env c = true ->
    nth_error h addr = Some obj -> nth_error (values_of obj) i = Some addr' ->
    nth_error (fields env c) i = Some member -> member_seen reference member = Some seen ->
    fits h addr' (instantiate inst seen).
Proof.
    intros inst h addr reference c obj i addr' member seen Hc Hh Hfit Hb Hcl Hn Hv Hm Hseen.
    destruct (class_of_fits inst h addr reference c obj Hfit Hb Hcl Hn) as [Hcls Hs].
    destruct (Hh addr obj Hn) as [_ [_ Hf]].
    destruct (forall2_nth_left _ _ _ _ _ Hf Hv) as [member' [Hm' Hfit']].
    rewrite Hcls in Hm'. assert (member' = member) by congruence. subst member'.
    rewrite (member_seen_at_runtime inst obj reference member seen Hc Hs Hseen) in Hfit'. exact Hfit'.
Qed.

Lemma heap_ok_write: forall h addr obj i addr' member,
    heap_ok h -> nth_error h addr = Some obj -> nth_error (fields env (class_of obj)) i = Some member ->
    fits h addr' (member_type (arg_of obj) member) ->
    heap_ok (set_nth h addr (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr'))).
Proof.
    intros h addr obj i addr' member Hh Hn Hm Hfit.
    pose proof (keeps_update h addr obj
        (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr')) Hn eq_refl eq_refl) as K.
    intros addr0 obj0 Hn0. destruct (Nat.eq_dec addr addr0) as [E|E].
    - subst addr0. rewrite set_nth_same in Hn0 by (eapply in_bounds; exact Hn).
      assert (obj0 = mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr')) by congruence.
      subst obj0. simpl.
      destruct (Hh addr obj Hn) as [Hc [Hcl Hf]]. split; [exact Hc|]. split; [exact Hcl|].
      eapply forall2_set; [|exact Hm|eapply fits_keeps; [exact K|exact Hfit]].
      eapply forall2_impl; [exact Hf|]. intros a b Hab. eapply fits_keeps; [exact K|exact Hab].
    - rewrite set_nth_other in Hn0 by exact E.
      destruct (Hh addr0 obj0 Hn0) as [Hc [Hcl Hf]]. split; [exact Hc|]. split; [exact Hcl|].
      eapply forall2_impl; [exact Hf|]. intros a b Hab. eapply fits_keeps; [exact K|exact Hab].
Qed.

Lemma heap_ok_construct: forall h c arg addrs,
    heap_ok h -> is_class env c = true -> arg_is_closed arg ->
    Forall2 (fun value member => fits h value (member_type arg member)) addrs (fields env c) ->
    heap_ok (h ++ [mkObject c arg addrs]).
Proof.
    intros h c arg addrs Hh Hc Hcl Hf addr obj Hn. pose proof (keeps_append h (mkObject c arg addrs)) as K.
    destruct (append_back _ _ _ _ Hn) as [Hin|[_ E]].
    - destruct (Hh addr obj Hin) as [Hc' [Hcl' Hf']]. split; [exact Hc'|]. split; [exact Hcl'|].
      eapply forall2_impl; [exact Hf'|]. intros a b Hab. eapply fits_keeps; [exact K|exact Hab].
    - subst obj. simpl. split; [exact Hc|]. split; [exact Hcl|].
      eapply forall2_impl; [exact Hf|]. intros a b Hab. eapply fits_keeps; [exact K|exact Hab].
Qed.

Lemma preserve_assign: forall inst ctx h store name origin addr,
    admissible inst -> heap_ok h -> store_ok inst h ctx store ->
    assignable (ctx origin) (ctx name) -> store origin = Some addr ->
    heap_ok h /\ store_ok inst h ctx (set store name addr).
Proof.
    intros inst ctx h store name origin addr Hadm Hh Hs Ha Hy. split; [exact Hh|].
    apply store_set; [exact Hs|]. exact (fits_assignable inst h addr _ _ Hadm Ha (Hs origin addr Hy)).
Qed.

Lemma preserve_read: forall inst ctx h store name origin i c member seen addr obj addr',
    admissible inst -> heap_ok h -> store_ok inst h ctx store ->
    base_of (ctx origin) = Some c -> is_class env c = true ->
    nth_error (fields env c) i = Some member -> member_seen (ctx origin) member = Some seen ->
    assignable (seen_through (ctx origin) seen) (ctx name) ->
    store origin = Some addr -> nth_error h addr = Some obj -> nth_error (values_of obj) i = Some addr' ->
    heap_ok h /\ store_ok inst h ctx (set store name addr').
Proof.
    intros inst ctx h store name origin i c member seen addr obj addr' Hadm Hh Hs Hb Hc Hm Hseen Ha Hy Hn Hv.
    pose proof Hadm as [Hcl _].
    split; [exact Hh|]. apply store_set; [exact Hs|].
    eapply fits_assignable; [exact Hadm|exact Ha|]. apply fits_seen_through; [exact Hcl|].
    exact (member_fits inst h addr (ctx origin) c obj i addr' member seen Hcl Hh (Hs origin addr Hy) Hb Hc Hn Hv Hm Hseen).
Qed.

Lemma preserve_write: forall inst ctx h store origin i value c member seen addr obj addr',
    admissible inst -> heap_ok h -> store_ok inst h ctx store ->
    base_of (ctx origin) = Some c -> is_class env c = true ->
    nth_error (fields env c) i = Some member -> member_seen (ctx origin) member = Some seen ->
    assignable (ctx value) seen ->
    store origin = Some addr -> nth_error h addr = Some obj -> store value = Some addr' ->
    heap_ok (set_nth h addr (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr')))
    /\ store_ok inst (set_nth h addr (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr'))) ctx store.
Proof.
    intros inst ctx h store origin i value c member seen addr obj addr' Hadm Hh Hs Hb Hc Hm Hseen Ha Hy Hn Hz.
    pose proof Hadm as [Hcl _].
    destruct (class_of_fits inst h addr (ctx origin) c obj (Hs origin addr Hy) Hb Hc Hn) as [Hcls Hshape].
    pose proof (fits_assignable inst h addr' _ _ Hadm Ha (Hs value addr' Hz)) as Hfit.
    rewrite <- (member_seen_at_runtime inst obj (ctx origin) member seen Hcl Hshape Hseen) in Hfit.
    split.
    - apply heap_ok_write with (member := member); [exact Hh|exact Hn|rewrite Hcls; exact Hm|exact Hfit].
    - intros name lx Hx. eapply fits_keeps; [|exact (Hs name lx Hx)].
      exact (keeps_update h addr obj
          (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr')) Hn eq_refl eq_refl).
Qed.

Lemma new_shape: forall inst c arg addrs,
    shape_fits (mkObject c (option_map (instantiate inst) arg) addrs) (instantiate inst (new_type c arg)).
Proof.
    intros inst c arg addrs. destruct arg as [given|]; simpl.
    - split; [exact (subtype_refl wf c)|reflexivity].
    - exact (subtype_refl wf c).
Qed.

Lemma new_claim: forall inst c arg addrs,
    may_be_token false (instantiate inst (new_type c arg)) = false ->
    object_is_free (mkObject c (option_map (instantiate inst) arg) addrs) = true.
Proof.
    intros inst c arg addrs. unfold object_is_free. destruct arg as [given|]; simpl; intro H.
    - apply orb_false_iff in H. destruct H as [H1 H2]. apply negb_false_iff in H1.
      rewrite (non_token_is_no_token c H1), H2. reflexivity.
    - apply negb_false_iff in H. rewrite (non_token_is_no_token c H). reflexivity.
Qed.

Lemma preserve_construct: forall inst ctx h store name c arg values addrs,
    admissible inst -> heap_ok h -> store_ok inst h ctx store -> is_class env c = true ->
    Forall2 (fun value member => exists seen,
        member_seen (new_type c arg) member = Some seen /\ assignable (ctx value) seen) values (fields env c) ->
    assignable (new_type c arg) (ctx name) ->
    Forall2 (fun value addr => store value = Some addr) values addrs ->
    heap_ok (h ++ [mkObject c (option_map (instantiate inst) arg) addrs])
    /\ store_ok inst (h ++ [mkObject c (option_map (instantiate inst) arg) addrs]) ctx (set store name (length h)).
Proof.
    intros inst ctx h store name c arg values addrs Hadm Hh Hs Hc Hargs Ha Hvals.
    pose proof Hadm as [Hcl _].
    pose proof (keeps_append h (mkObject c (option_map (instantiate inst) arg) addrs)) as K.
    pose proof (new_shape inst c arg addrs) as Hshape.
    split.
    - apply heap_ok_construct; [exact Hh|exact Hc| |].
      + destruct arg as [given|]; simpl; [apply closed_instantiate; exact Hcl|exact I].
      + eapply forall2_compose; [exact Hvals|exact Hargs|].
        intros value addr member Hz [seen [Hseen Hzm]].
        pose proof (member_seen_at_runtime inst _ (new_type c arg) member seen Hcl Hshape Hseen) as E.
        simpl in E. rewrite E.
        exact (fits_assignable inst h addr _ _ Hadm Hzm (Hs value addr Hz)).
    - apply store_set.
      + intros origin addr Hy. eapply fits_keeps; [exact K|exact (Hs origin addr Hy)].
      + eapply fits_assignable; [exact Hadm|exact Ha|].
        exists (mkObject c (option_map (instantiate inst) arg) addrs). split; [apply nth_append_last|].
        split; [exact Hshape|exact (new_claim inst c arg addrs)].
Qed.

(* Preservation: a statement the frontend accepts leaves every reference leading to an object of its type, and
   where that type cannot be a token, to an object that is free of them. Whatever the type parameter of the
   function stands for. *)
Theorem types_stay_true: forall inst ctx statement h store h' store',
    admissible inst -> heap_ok h -> store_ok inst h ctx store ->
    typed ctx statement -> step inst statement h store h' store' ->
    heap_ok h' /\ store_ok inst h' ctx store'.
Proof.
    intros inst ctx statement h store h' store' Hadm Hh Hs Ht Hstep.
    inversion Hstep; subst; inversion Ht; subst.
    - eapply preserve_assign; eassumption.
    - eapply preserve_read; eassumption.
    - eapply preserve_write; eassumption.
    - eapply preserve_construct; eassumption.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Nothing behind a reference that cannot be a token is one                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Inductive reaches (h: Heap): nat -> nat -> Prop :=
    | reaches_self: forall addr, reaches h addr addr
    | reaches_member: forall addr obj i addr' addr'',
        nth_error h addr = Some obj ->
        nth_error (values_of obj) i = Some addr' ->
        reaches h addr' addr'' ->
        reaches h addr addr''.

(* rule 2 is what this takes *)
Theorem free_holds_only_free: forall h addr addr',
    heap_ok h -> reaches h addr addr' ->
    forall obj obj', nth_error h addr = Some obj -> object_is_free obj = true ->
    nth_error h addr' = Some obj' -> object_is_free obj' = true.
Proof.
    intros h addr addr' Hh R.
    induction R as [addr|addr obj1 i addr1 addr2 Hn Hv R IH]; intros obj obj' Ho Ht Ho'.
    - assert (obj' = obj) by congruence. subst obj'. exact Ht.
    - assert (obj1 = obj) by congruence. subst obj1.
      destruct (Hh addr obj Hn) as [Hc [_ Hf]].
      destruct (forall2_nth_left _ _ _ _ _ Hf Hv) as [member [Hm [obj2 [Hn2 [_ Hclaim]]]]].
      apply (IH obj2 obj' Hn2); [|exact Ho'].
      apply Hclaim. unfold object_is_free in Ht. apply andb_true_iff in Ht. destruct Ht as [Ht1 Ht2].
      apply negb_true_iff in Ht1.
      pose proof (members_say wf _ Hc Ht1) as Hall. rewrite Forall_forall in Hall.
      pose proof (Hall member (nth_error_In _ _ Hm)) as Hmember.
      unfold member_type. destruct (arg_of obj) as [given|]; [|exact Hmember].
      apply negb_true_iff in Ht2.
      destruct (may_be_token false (instantiate given member)) eqn:E; [|reflexivity].
      rewrite (instantiate_says_no_more false given member) in Hmember; [discriminate| |exact E].
      intro C. rewrite C in Ht2. discriminate.
Qed.

Theorem no_token_behind_a_non_token: forall inst ctx h store name addr addr' obj',
    heap_ok h -> store_ok inst h ctx store ->
    store name = Some addr -> may_be_token false (instantiate inst (ctx name)) = false ->
    reaches h addr addr' -> nth_error h addr' = Some obj' ->
    is_token env (class_of obj') = false.
Proof.
    intros inst ctx h store name addr addr' obj' Hh Hs Hx Hno R Ho'.
    destruct (Hs name addr Hx) as [obj [Hn [_ Hclaim]]].
    pose proof (free_holds_only_free h addr addr' Hh R obj obj' Hn (Hclaim Hno) Ho') as Hfree.
    destruct (is_token env (class_of obj')) eqn:E; [|reflexivity].
    rewrite (token_is_not_free obj' E) in Hfree. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* No token, no effect                                                                             *)
(* ---------------------------------------------------------------------------------------------- *)

(* The code that runs is cut off from the tokens of the heap it started with, h0:
   every object it has a reference to is free of tokens or one it constructed, the objects it constructed lead
   to no others either, none of them stands for state outside of the program, and what is not free of tokens
   in h0 is as it was. *)
Record isolated (h0 h: Heap) (store: Store): Prop := mkIsolated {
    iso_grown: length h0 <= length h;
    iso_store: forall name addr obj,
        store name = Some addr -> nth_error h addr = Some obj -> object_is_free obj = false -> length h0 <= addr;
    iso_members: forall addr obj i addr' obj',
        length h0 <= addr -> nth_error h addr = Some obj -> nth_error (values_of obj) i = Some addr' ->
        nth_error h addr' = Some obj' -> object_is_free obj' = false -> length h0 <= addr';
    iso_authority: forall addr obj,
        length h0 <= addr -> nth_error h addr = Some obj -> needs_authority env (class_of obj) = false;
    iso_untouched: forall addr obj,
        nth_error h0 addr = Some obj -> object_is_free obj = false -> nth_error h addr = Some obj;
}.

Lemma isolated_set: forall h0 h store name addr,
    isolated h0 h store ->
    (forall obj, nth_error h addr = Some obj -> object_is_free obj = false -> length h0 <= addr) ->
    isolated h0 h (set store name addr).
Proof.
    intros h0 h store name addr [G St M A U] Hl. constructor; try assumption.
    intros origin ly obj Hy Hn Ht. unfold set in Hy. destruct (Nat.eqb origin name).
    - assert (ly = addr) by congruence. subst ly. exact (Hl obj Hn Ht).
    - exact (St origin ly obj Hy Hn Ht).
Qed.

Lemma isolated_assign: forall h0 h store name origin addr,
    isolated h0 h store -> store origin = Some addr -> isolated h0 h (set store name addr).
Proof.
    intros h0 h store name origin addr Hiso Hy. apply isolated_set; [exact Hiso|].
    intros obj Hn Ht. exact (iso_store h0 h store Hiso origin addr obj Hy Hn Ht).
Qed.

Lemma isolated_read: forall h0 h store name origin i addr obj addr',
    heap_ok h -> isolated h0 h store ->
    store origin = Some addr -> nth_error h addr = Some obj -> nth_error (values_of obj) i = Some addr' ->
    isolated h0 h (set store name addr').
Proof.
    intros h0 h store name origin i addr obj addr' Hh Hiso Hy Hn Hv. apply isolated_set; [exact Hiso|].
    intros obj' Hn' Ht'. destruct (object_is_free obj) eqn:F.
    - exfalso.
      assert (object_is_free obj' = true) as Hfree.
      { apply (free_holds_only_free h addr addr' Hh) with (obj := obj); [|exact Hn|exact F|exact Hn'].
        eapply reaches_member; [exact Hn|exact Hv|apply reaches_self]. }
      congruence.
    - exact (iso_members h0 h store Hiso addr obj i addr' obj'
        (iso_store h0 h store Hiso origin addr obj Hy Hn F) Hn Hv Hn' Ht').
Qed.

Lemma isolated_write: forall h0 h store origin i value addr obj addr',
    isolated h0 h store ->
    store origin = Some addr -> nth_error h addr = Some obj -> i < length (values_of obj) ->
    store value = Some addr' ->
    isolated h0 (set_nth h addr (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr'))) store.
Proof.
    intros h0 h store origin i value addr obj addr' [G St M A U] Hy Hn Hf Hz.
    remember (mkObject (class_of obj) (arg_of obj) (set_nth (values_of obj) i addr')) as written eqn:EW.
    assert (HW: class_of written = class_of obj) by (rewrite EW; reflexivity).
    assert (HA: arg_of written = arg_of obj) by (rewrite EW; reflexivity).
    constructor.
    - rewrite set_nth_length. exact G.
    - intros name lx ox Hx Hnx Htx.
      destruct (update_back _ _ _ _ _ _ Hn HW HA Hnx) as [obj1 [Hn1 [_ [Hf1 _]]]].
      apply (St name lx obj1 Hx Hn1). rewrite Hf1. exact Htx.
    - intros la oa j lb ob Hla Hna Hva Hnb Htb.
      destruct (update_back _ _ _ _ _ _ Hn HW HA Hnb) as [ob1 [Hnb1 [_ [Hfb _]]]].
      assert (Tb: object_is_free ob1 = false) by (rewrite Hfb; exact Htb).
      destruct (update_back _ _ _ _ _ _ Hn HW HA Hna) as [oa1 [Hna1 [_ [_ [Hne Heq]]]]].
      destruct (Nat.eq_dec la addr) as [E|E].
      + specialize (Heq E). subst oa. rewrite EW in Hva. simpl in Hva.
        destruct (Nat.eq_dec i j) as [F|F].
        * subst j. rewrite set_nth_same in Hva by exact Hf.
          assert (lb = addr') by congruence. subst lb. exact (St value addr' ob1 Hz Hnb1 Tb).
        * rewrite set_nth_other in Hva by exact F. subst la.
          exact (M addr obj j lb ob1 Hla Hn Hva Hnb1 Tb).
      + specialize (Hne E). subst oa1. exact (M la oa j lb ob1 Hla Hna1 Hva Hnb1 Tb).
    - intros la oa Hla Hna.
      destruct (update_back _ _ _ _ _ _ Hn HW HA Hna) as [obj1 [Hn1 [Hc1 _]]].
      rewrite <- Hc1. exact (A la obj1 Hla Hn1).
    - intros addr0 obj0 H0 T0. pose proof (U addr0 obj0 H0 T0) as Hh0.
      destruct (Nat.eq_dec addr addr0) as [E|E].
      + exfalso. subst addr0. assert (obj0 = obj) by congruence. subst obj0.
        pose proof (St origin addr obj Hy Hn T0). pose proof (in_bounds _ _ _ H0). lia.
      + rewrite set_nth_other by exact E. exact Hh0.
Qed.

Lemma isolated_construct: forall inst ctx h0 h store name c arg values addrs,
    store_ok inst h ctx store -> isolated h0 h store ->
    Forall2 (fun value addr => store value = Some addr) values addrs ->
    (needs_authority env c = true ->
        exists holder granting addr, store holder = Some addr /\ base_of (ctx holder) = Some granting
            /\ needs_authority env granting = true) ->
    isolated h0 (h ++ [mkObject c arg addrs]) (set store name (length h)).
Proof.
    intros inst ctx h0 h store name c arg values addrs Hs [G St M A U] Hvals Hauth.
    assert (StoreVal: forall value lz obj, store value = Some lz ->
        nth_error (h ++ [mkObject c arg addrs]) lz = Some obj ->
        object_is_free obj = false -> length h0 <= lz).
    { intros value lz obj Hz Hn Ht. destruct (append_back _ _ _ _ Hn) as [Hin|[E _]].
      - exact (St value lz obj Hz Hin Ht).
      - lia. }
    constructor.
    - rewrite length_app. simpl. lia.
    - intros origin ly obj Hy Hn Ht. unfold set in Hy. destruct (Nat.eqb origin name).
      + assert (ly = length h) by congruence. lia.
      + exact (StoreVal origin ly obj Hy Hn Ht).
    - intros la oa j lb ob Hla Hna Hva Hnb Htb.
      destruct (append_back _ _ _ _ Hna) as [Hin|[E EO]].
      + destruct (append_back _ _ _ _ Hnb) as [Hinb|[Eb _]].
        * exact (M la oa j lb ob Hla Hin Hva Hinb Htb).
        * lia.
      + subst oa. simpl in Hva.
        destruct (forall2_nth_right _ _ _ _ _ Hvals Hva) as [value [_ Hz]].
        exact (StoreVal value lb ob Hz Hnb Htb).
    - intros la oa Hla Hna. destruct (append_back _ _ _ _ Hna) as [Hin|[E EO]].
      + exact (A la oa Hla Hin).
      + subst oa. simpl. destruct (needs_authority env c) eqn:NA; [|reflexivity]. exfalso.
        (* the token that is to lend its authority would have to be one of h0, and there is no reference to those *)
        destruct (Hauth eq_refl) as [holder [granting [lw [Hw [Hbase Hgr]]]]].
        destruct (authority_is_token wf _ Hgr) as [Hcw Htw].
        destruct (Hs holder lw Hw) as [ow [Hnw Hrest]].
        assert (Hfit: fits h lw (instantiate inst (ctx holder))) by (exists ow; split; [exact Hnw|exact Hrest]).
        destruct (class_of_fits inst h lw (ctx holder) granting ow Hfit Hbase Hcw Hnw) as [Hcls _].
        assert (Tw: object_is_free ow = false) by (apply token_is_not_free; rewrite Hcls; exact Htw).
        pose proof (A lw ow (St holder lw ow Hw Hnw Tw) Hnw) as Hno.
        rewrite Hcls in Hno. congruence.
    - intros addr0 obj0 H0 T0. pose proof (U addr0 obj0 H0 T0) as Hh0.
      rewrite nth_error_app1 by (eapply in_bounds; exact Hh0). exact Hh0.
Qed.

Lemma isolated_step: forall inst ctx h0 statement h store h' store',
    heap_ok h -> store_ok inst h ctx store -> isolated h0 h store ->
    typed ctx statement -> step inst statement h store h' store' ->
    isolated h0 h' store'.
Proof.
    intros inst ctx h0 statement h store h' store' Hh Hs Hiso Ht Hstep.
    inversion Hstep; subst; inversion Ht; subst.
    - eapply isolated_assign; eassumption.
    - eapply isolated_read; eassumption.
    - eapply isolated_write; eassumption.
    - eapply isolated_construct; try eassumption.
      intro NA.
      match goal with
      | Ha: needs_authority env _ = true -> exists holder granting, _ |- _ =>
          destruct (Ha NA) as [holder [granting [El [Hbase Hgr]]]]
      end.
      match goal with
      | Hl: forall holder, _ = Some holder -> exists addr, _ |- _ => destruct (Hl holder El) as [lw Hlw]
      end.
      exists holder, granting, lw. split; [exact Hlw|]. split; [exact Hbase|exact Hgr].
Qed.

Lemma isolated_start: forall inst ctx h store,
    admissible inst -> store_ok inst h ctx store ->
    (forall name addr, store name = Some addr -> may_be_token param_may (ctx name) = false) ->
    isolated h h store.
Proof.
    intros inst ctx h store [_ [_ Hpm]] Hs Hno. constructor.
    - apply le_n.
    - intros name addr obj Hx Hn Ht. exfalso.
      destruct (Hs name addr Hx) as [obj1 [Hn1 [_ Hc]]]. assert (obj1 = obj) by congruence. subst obj1.
      rewrite Hc in Ht; [discriminate|].
      pose proof (Hno name addr Hx) as Hstatic.
      destruct (may_be_token false (instantiate inst (ctx name))) eqn:E; [|reflexivity].
      rewrite (instantiate_says_no_more param_may inst (ctx name)) in Hstatic; [discriminate| |exact E].
      intro Hi. unfold param_may. rewrite (Hpm Hi). reflexivity.
    - intros addr obj i addr' obj' Hl Hn. pose proof (in_bounds _ _ _ Hn). exfalso. lia.
    - intros addr obj Hl Hn. pose proof (in_bounds _ _ _ Hn). exfalso. lia.
    - intros addr obj Hn _. exact Hn.
Qed.

Lemma runs_keep: forall inst ctx h0 program h store h' store',
    admissible inst ->
    runs inst program h store h' store' -> Forall (typed ctx) program ->
    heap_ok h -> store_ok inst h ctx store -> isolated h0 h store ->
    heap_ok h' /\ store_ok inst h' ctx store' /\ isolated h0 h' store'.
Proof.
    intros inst ctx h0 program h store h' store' Hadm R.
    induction R as [h store|statement rest h store h1 store1 h2 store2 Hstep R IH]; intros Ht Hh Hs Hiso.
    - split; [exact Hh|]. split; [exact Hs|exact Hiso].
    - inversion Ht as [|? ? Hst Hrest]; subst.
      destruct (types_stay_true inst ctx statement h store h1 store1 Hadm Hh Hs Hst Hstep) as [Hh1 Hs1].
      apply IH; [exact Hrest|exact Hh1|exact Hs1|].
      exact (isolated_step inst ctx h0 statement h store h1 store1 Hh Hs Hiso Hst Hstep).
Qed.

(* A function with no type in its signature that may be a token: of the variables set when it starts, its
   parameters, none has such a type, with a type parameter that is not bounded by NonToken counting as one
   that may. Whatever it runs, and whatever its type parameter stands for,
     * a token it has a reference to is one it constructed, and stands for no state outside of the program
     * every token that was there when it started is as it was. *)
Theorem no_token_no_effect: forall inst ctx program h store h' store',
    admissible inst -> heap_ok h -> store_ok inst h ctx store ->
    (forall name addr, store name = Some addr -> may_be_token param_may (ctx name) = false) ->
    Forall (typed ctx) program -> runs inst program h store h' store' ->
    (forall name addr obj,
        store' name = Some addr -> nth_error h' addr = Some obj -> is_token env (class_of obj) = true ->
        length h <= addr /\ needs_authority env (class_of obj) = false)
    /\ (forall addr obj,
        nth_error h addr = Some obj -> is_token env (class_of obj) = true -> nth_error h' addr = Some obj).
Proof.
    intros inst ctx program h store h' store' Hadm Hh Hs Hno Ht R.
    destruct (runs_keep inst ctx h program h store h' store' Hadm R Ht Hh Hs
        (isolated_start inst ctx h store Hadm Hs Hno)) as [_ [_ Hiso]].
    split.
    - intros name addr obj Hx Hn Htok.
      pose proof (iso_store h h' store' Hiso name addr obj Hx Hn (token_is_not_free obj Htok)) as Hle.
      split; [exact Hle|exact (iso_authority h h' store' Hiso addr obj Hle Hn)].
    - intros addr obj Hn Htok. exact (iso_untouched h h' store' Hiso addr obj Hn (token_is_not_free obj Htok)).
Qed.

End Guarantee.

(* ---------------------------------------------------------------------------------------------- *)
(* A program, so that the premises are known to be satisfiable                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Module TokenGuaranteeExample.

Inductive B := NonToken | AnyType | World | StandardOut | Stream | Buffered | InMemory | Data | Box.

(* interface Stream; unique class StandardOut : Stream; token class Buffered : Stream { inner: mut Stream };
   class InMemory : Stream { data: mut Data }; class Data; class Box<T> { value: T } *)
Definition example_subtype (a b: B): bool :=
    match a, b with
    | _, AnyType => true
    | NonToken, NonToken | World, World | StandardOut, StandardOut | Stream, Stream => true
    | Buffered, Buffered | InMemory, InMemory | Data, Data | Box, Box => true
    | StandardOut, Stream | Buffered, Stream | InMemory, Stream => true
    | InMemory, NonToken | Data, NonToken | Box, NonToken => true
    | _, _ => false
    end.

Definition example: Environment B := mkEnvironment B
    example_subtype
    NonToken
    (fun b => match b with World | StandardOut | Buffered | InMemory | Data | Box => true | _ => false end)
    (fun b => match b with World | StandardOut | Buffered => true | _ => false end)
    (fun b => match b with World | StandardOut => true | _ => false end)
    (fun b => match b with
        | Buffered => [Plain B mutable Stream false]
        | InMemory => [Plain B mutable Data false]
        | Box => [Param B None false]
        | _ => []
        end).

Example example_well_formed: well_formed B example.
Proof.
    constructor.
    - intros []; reflexivity.
    - intros [] [] []; cbv; intros; try reflexivity; congruence.
    - intros [] []; cbv; intros; try reflexivity; congruence.
    - intros []; cbv; intros; try reflexivity; congruence.
    - intros []; cbv; intros; try congruence; repeat constructor.
    - intros []; cbv; intros; try congruence; split; reflexivity.
Qed.

(* fn main(world: mut World) {
       out: mut StandardOut = StandardOut.take(world)
       buffered: mut Buffered = Buffered(out)
       stream: read Stream = buffered
   } *)
Definition main_context (name: nat): Ty B :=
    match name with
    | 0 => Plain B mutable World false
    | 1 => Plain B mutable StandardOut false
    | 2 => Plain B mutable Buffered false
    | _ => Plain B readonly Stream false
    end.

Definition main_body: list (Statement B) := [
    Construct B 1 StandardOut None [] (Some 0);
    Construct B 2 Buffered None [1] None;
    Assign B 3 2
].

Example main_is_typed: Forall (typed B example AnyType main_context) main_body.
Proof.
    unfold main_body. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply typed_construct.
      + reflexivity.
      + constructor.
      + split; [reflexivity|intros _; reflexivity].
      + intros _. exists 0, World. split; [reflexivity|split; reflexivity].
    - apply typed_construct.
      + reflexivity.
      + constructor; [|constructor]. exists (Plain B mutable Stream false).
        split; [reflexivity|]. split; [reflexivity|intros _; reflexivity].
      + split; [reflexivity|intros _; reflexivity].
      + intro H. discriminate H.
    - apply typed_assign. split; [reflexivity|intros _; reflexivity].
Qed.

(* fn put<T>(box: mut Box<T>, item: T) {
       set box.value = item
       back: T = box.value
   } *)
Definition put_context (name: nat): Ty B :=
    match name with
    | 0 => Applied B mutable Box (Param B None false) false
    | _ => Param B None false
    end.

Definition put_body: list (Statement B) := [
    WriteMember B 0 0 1;
    ReadMember B 2 0 0
].

Example put_is_typed: Forall (typed B example AnyType put_context) put_body.
Proof.
    unfold put_body. constructor; [|constructor; [|constructor]].
    - apply typed_write with (c := Box) (member := Param B None false) (seen := Param B None false);
        try reflexivity. split; [exact I|intro H; exact H].
    - apply typed_read with (c := Box) (member := Param B None false) (seen := Param B None false);
        try reflexivity. split; [exact I|intro H; exact H].
Qed.

(* rule 1: a value that may be a token does not freeze *)
Example a_token_is_not_frozen:
    ~ assignable B example AnyType (Plain B own Stream false) (Plain B immutable Stream false).
Proof.
    intros [_ H]. specialize (H eq_refl). discriminate H.
Qed.

(* rule 3: nor is it forgotten *)
Example a_token_is_not_forgotten:
    ~ assignable B example AnyType (Plain B mutable Stream false) (Plain B mutable Stream true).
Proof.
    intros [_ H]. specialize (H eq_refl). discriminate H.
Qed.

(* and a value that is none does both *)
Example a_non_token_freezes:
    assignable B example AnyType (Plain B own InMemory false) (Plain B immutable Stream false).
Proof.
    split; [reflexivity|intro H; discriminate H].
Qed.

(* a type argument counts: Box is below NonToken, a Box<StandardOut> is not assignable to it *)
Example a_box_of_tokens_is_not_forgotten:
    ~ assignable B example AnyType
        (Applied B mutable Box (Plain B mutable StandardOut false) false) (Plain B mutable NonToken false).
Proof.
    intros [_ H]. specialize (H eq_refl). discriminate H.
Qed.

Example a_box_of_data_is_forgotten:
    assignable B example AnyType
        (Applied B mutable Box (Plain B mutable Data false) false) (Plain B mutable NonToken false).
Proof.
    split; [reflexivity|intro H; discriminate H].
Qed.

(* rule 4: generic code does not freeze a T *)
Example a_type_parameter_is_not_frozen:
    ~ assignable B example AnyType (Param B (Some own) false) (Param B (Some immutable) false).
Proof.
    intros [_ H]. specialize (H eq_refl). discriminate H.
Qed.

(* unless T : NonToken *)
Example a_non_token_type_parameter_freezes:
    assignable B example NonToken (Param B (Some own) false) (Param B (Some immutable) false).
Proof.
    split; [exact I|intro H; discriminate H].
Qed.

(* `const T` of a `mut StandardOut` is `own StandardOut & NonToken`: a type without values *)
Example const_of_a_token_type:
    instantiate B example (Plain B mutable StandardOut false) (Param B (Some immutable) false)
    = Plain B own StandardOut true.
Proof.
    reflexivity.
Qed.

End TokenGuaranteeExample.
