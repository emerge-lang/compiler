From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From Stdlib Require Import Bool List.
Import ListNotations.

Section Ops.

Variable env: Environment.

Definition can_reassign_fields_on (t: EType): bool :=
    match (mutability_of env t) with
    | exclusive => true
    | mutable => true
    | readonly => false
    | immutable => false
    end.

Definition can_assume_immutable (t: EType): bool :=
    match mutability_of env t with
    | immutable => true
    | _ => false
    end.

Lemma negb_inj: forall a b: bool, negb a = negb b -> a = b.
Proof.
    intros [] [] H.
    - reflexivity.
    - discriminate.
    - discriminate.
    - reflexivity.
Qed.

Lemma immutability_precludes_reassignment: forall t: EType,
    can_assume_immutable t = true ->
    can_reassign_fields_on t = false.
Proof.
    intros t H.
    unfold can_assume_immutable in H.
    unfold can_reassign_fields_on.
    remember (mutability_of env t) as m.
    destruct m.
    - discriminate H.
    - reflexivity.
    - reflexivity.
    - discriminate H.
Qed.

(* Assigning a value doesn't preserve immutability: `immutable Any` is assignable to `readonly Any`.
   The reference assigned to promises less, which is fine; see may_coexist below for what matters. *)
Lemma immutability_is_affected_by_reassignment:
    is_core_scalar (declaration_of env any) = false ->
    ~ (forall a b: EType, forall fuel: nat,
        is_assignable_to env fuel a b = Some true ->
        can_assume_immutable a = true ->
        can_assume_immutable b = true).
Proof.
    intros Hany H.
    pose (a := RootResolved (Some immutable) any nil).
    pose (b := RootResolved (Some readonly) any nil).
    assert (Hassignable: is_assignable_to env 1 a b = Some true).
    { unfold is_assignable_to, a, b. simpl. rewrite Hany. reflexivity. }
    assert (Ha: can_assume_immutable a = true).
    { unfold can_assume_immutable, a. simpl. destruct (is_core_scalar _); reflexivity. }
    assert (Hb: can_assume_immutable b = false).
    { unfold can_assume_immutable, b. simpl. rewrite Hany. reflexivity. }
    rewrite (H a b 1 Hassignable Ha) in Hb. discriminate Hb.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about mutabilities                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma mutability_subtype_trans: forall a b c: Mutability,
    is_subtype_of a b = true -> is_subtype_of b c = true -> is_subtype_of a c = true.
Proof. intros [] [] []; simpl; congruence. Qed.

Lemma mutability_subtype_of_readonly: forall m, is_subtype_of m readonly = true.
Proof. intros []; reflexivity. Qed.

Lemma mutability_subtype_of_exclusive: forall m, is_subtype_of m exclusive = true -> m = exclusive.
Proof. intros []; simpl; congruence. Qed.

Lemma intersect_mutability_left: forall a b, is_subtype_of (intersect_mutability a b) a = true.
Proof. intros [] []; reflexivity. Qed.

Lemma intersect_mutability_right: forall a b, is_subtype_of (intersect_mutability a b) b = true.
Proof. intros [] []; reflexivity. Qed.

(* intersect_mutability is the greatest lower bound *)
Lemma intersect_mutability_greatest: forall x a b,
    is_subtype_of x a = true -> is_subtype_of x b = true -> is_subtype_of x (intersect_mutability a b) = true.
Proof. intros [] [] []; simpl; congruence. Qed.

(*
 * Whether two references to the same object can exist at the same time without one breaking the
 * promises of the other: a readonly reference promises nothing and allows nothing, mutable
 * references allow each other's mutations, immutable references can't mutate. An exclusive
 * reference promises that it is the only one that can mutate or rely on immutability.
 * This is assured by the subtyping rules on assignment, and variable lifetime rules:
 * * copying an exclusive reference into a non-readonly reference ends the lifetime of the exclusive reference
 * * while an exclusive reference is borrowed, it can only be borrowed again by references that may
 *   coexist with all active borrows. The borrows end when the invocation they were created for returns.
 *)
Definition may_coexist (a b: Mutability): bool :=
    match a, b with
    | readonly, _ | _, readonly => true
    | mutable, mutable | immutable, immutable => true
    | _, _ => false
    end.

(* the kotlin implementation of may_coexist *)
Definition kotlin_may_be_aliased_with (a b: Mutability): bool :=
    if Mutability_beq a readonly || Mutability_beq b readonly then true
    else if (Mutability_beq a immutable || Mutability_beq a mutable) && Mutability_beq a b then true
    else false.

Lemma may_coexist_in_kotlin_is_correct: forall a b, (may_coexist a b) = (kotlin_may_be_aliased_with a b).
Proof. intros [] []; reflexivity. Qed.

Lemma may_coexist_sym: forall a b, may_coexist a b = may_coexist b a.
Proof. intros [] []; reflexivity. Qed.

(* A reference with fewer promises coexists with whatever its subtype coexists with. *)
Lemma may_coexist_supertype: forall x m m',
    may_coexist x m = true -> is_subtype_of m m' = true -> may_coexist x m' = true.
Proof. intros [] [] []; simpl; congruence. Qed.

(* A reference coexists with the one it was created from, unless that is exclusive. *)
Lemma may_coexist_with_source: forall m m',
    m <> exclusive -> is_subtype_of m m' = true -> may_coexist m m' = true.
Proof. intros [] [] H; simpl; congruence. Qed.

Lemma may_coexist_exclusive: forall m, may_coexist exclusive m = true -> m = readonly.
Proof. intros []; simpl; congruence. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (a) The references to one object: no two of them can make conflicting promises                 *)
(*                                                                                                *)
(* This models the lifetime rules of compiler.binding.context.effect.VariableLifetime for a single *)
(* object, from its creation on.                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* The variable holding the exclusive reference, as long as there is one *)
Inductive Owner :=
    (* VariableLifetime.State.AliveExclusive *)
    | alive
    (* VariableLifetime.State.AliveExclusiveWithActiveBorrow; tracked is its withMutability *)
    | borrowed (tracked: Mutability)
    (* VariableLifetime.State.Dead: the exclusive reference has been given up *)
    | dead
    .

(* The other references to the object *)
Inductive Alias :=
    (* a reference that has been captured: assigned to a variable or member, passed to a
       capturing parameter, returned, ... *)
    | captured (mutability: Mutability)
    (* a borrowed parameter that refers to the object; it lives until the call returns *)
    | borrow (mutability: Mutability)
    .

Record Aliasing := mkAliasing {
    owner: Owner;
    aliases: list Alias;
}.

(* While the owner is borrowed it can do nothing but lend itself out again, so it acts as readonly *)
Definition owner_mutability (o: Owner): Mutability :=
    match o with
    | alive => exclusive
    | borrowed _ | dead => readonly
    end.

Definition alias_mutability (a: Alias): Mutability :=
    match a with captured m | borrow m => m end.

Definition is_captured (a: Alias): bool :=
    match a with captured _ => true | borrow _ => false end.

(* whether `R` holds for every two distinct elements of `l` *)
Fixpoint pairwise {A: Type} (R: A -> A -> bool) (l: list A): bool :=
    match l with
    | [] => true
    | x :: rest => forallb (R x) rest && pairwise R rest
    end.

(* Every two references to the object may coexist, the owner being one of them. *)
Definition conflict_free (s: Aliasing): bool :=
    forallb (fun a => may_coexist (owner_mutability (owner s)) (alias_mutability a)) (aliases s)
    && pairwise (fun a b => may_coexist (alias_mutability a) (alias_mutability b)) (aliases s).

Definition is_borrowed (o: Owner): bool :=
    match o with borrowed _ => true | _ => false end.

(* The things that can happen to the references within an invocation's arguments or in between invocations *)
Inductive transition: Aliasing -> Aliasing -> Prop :=
    (* the owner is captured as readonly: its lifetime goes on *)
    | capture_owner_as_readonly: forall l,
        transition (mkAliasing alive l) (mkAliasing alive (captured readonly :: l))
    (* the owner is captured as mutable or immutable: its lifetime ends. (Captured as exclusive,
       the exclusive reference merely moves to another variable, which changes nothing here.) *)
    | capture_owner: forall l m,
        m = mutable \/ m = immutable ->
        transition (mkAliasing alive l) (mkAliasing dead (captured m :: l))
    (* an alias is captured as a supertype of its own type; borrows can't be captured *)
    | capture_alias: forall o l1 l2 m m',
        is_subtype_of m m' = true ->
        transition (mkAliasing o (l1 ++ captured m :: l2)) (mkAliasing o (captured m' :: l1 ++ captured m :: l2))
    (* the owner is borrowed for the first time *)
    | start_borrow: forall l m,
        transition (mkAliasing alive l) (mkAliasing (borrowed m) (borrow m :: l))
    (* the owner is borrowed again, while borrowed already: the new borrow must coexist with the
       intersection of all active borrows, which is tracked from then on *)
    | add_borrow: forall b l m,
        may_coexist m b = true ->
        transition (mkAliasing (borrowed b) l) (mkAliasing (borrowed (intersect_mutability b m)) (borrow m :: l))
    (* a borrowed parameter is lent on. An exclusive one is an owner of its own in the called
       function, which this model leaves out. *)
    | reborrow: forall o l1 l2 m m',
        m <> exclusive ->
        is_subtype_of m m' = true ->
        transition (mkAliasing o (l1 ++ borrow m :: l2)) (mkAliasing o (borrow m' :: l1 ++ borrow m :: l2))
    (* an alias goes out of scope *)
    | drop: forall o l1 a l2,
        transition (mkAliasing o (l1 ++ a :: l2)) (mkAliasing o (l1 ++ l2))
    .

(* VariableLifetime.endInvocation *)
Definition owner_after_invocation (before after: Owner): Owner :=
    match after with
    | dead => dead
    | _ => match before with borrowed b => borrowed b | _ => alive end
    end.

(* The invoked function returns: the borrows created for its arguments end, the ones from before the
   invocation remain active. Captures from evaluating the arguments remain as well. *)
Definition return_from (before after: Aliasing): Aliasing :=
    mkAliasing (owner_after_invocation (owner before) (owner after))
        (filter is_captured (aliases after) ++ filter (fun a => negb (is_captured a)) (aliases before)).

Inductive step: Aliasing -> Aliasing -> Prop :=
    | transition_step: forall s s', transition s s' -> step s s'
    (* compiler.binding.context.InvocationJoinExecutionScopedCTContext: the arguments are evaluated,
       then the invoked function returns *)
    | invocation: forall s s', evaluates s s' -> step s (return_from s s')
(* evaluating code: any number of steps, one after the other *)
with evaluates: Aliasing -> Aliasing -> Prop :=
    | evaluates_nothing: forall s, evaluates s s
    | evaluates_more: forall s s' s'', evaluates s s' -> step s' s'' -> evaluates s s''
    .

Scheme step_mut := Minimality for step Sort Prop
with evaluates_mut := Minimality for evaluates Sort Prop.
Combined Scheme step_evaluates_mut from step_mut, evaluates_mut.

(* The references to an object over its lifetime. It starts out as the exclusive result of a
   constructor; the axiom that panic never returns means that Nothing is never one of them. *)
Definition reachable (s: Aliasing): Prop := evaluates (mkAliasing alive []) s.

(* sublists, to show that dropping references can't introduce a conflict *)
Inductive sublist {A: Type}: list A -> list A -> Prop :=
    | sublist_nil: sublist [] []
    | sublist_skip: forall x l1 l2, sublist l1 l2 -> sublist l1 (x :: l2)
    | sublist_keep: forall x l1 l2, sublist l1 l2 -> sublist (x :: l1) (x :: l2)
    .

Lemma sublist_refl: forall {A: Type} (l: list A), sublist l l.
Proof. intros A l. induction l; constructor; assumption. Qed.

Lemma sublist_in: forall {A: Type} (l1 l2: list A) x, sublist l1 l2 -> In x l1 -> In x l2.
Proof.
    intros A l1 l2 x H. induction H; simpl; intros Hin; [exact Hin | right; auto |].
    destruct Hin; [left | right; auto]; assumption.
Qed.

Lemma sublist_remove: forall {A: Type} (l1 l2: list A) x, sublist (l1 ++ l2) (l1 ++ x :: l2).
Proof.
    intros A l1 l2 x. induction l1; simpl.
    - apply sublist_skip, sublist_refl.
    - apply sublist_keep. assumption.
Qed.

Lemma sublist_filter: forall {A: Type} (f: A -> bool) l, sublist (filter f l) l.
Proof.
    intros A f l. induction l as [|x rest IH]; simpl; [constructor|].
    destruct (f x); constructor; assumption.
Qed.

Lemma pairwise_sublist: forall {A: Type} (R: A -> A -> bool) l1 l2,
    sublist l1 l2 -> pairwise R l2 = true -> pairwise R l1 = true.
Proof.
    intros A R l1 l2 H. induction H as [|x l1 l2 H IH|x l1 l2 H IH]; simpl; intros Hp; [reflexivity| |].
    - apply andb_true_iff in Hp. apply IH, Hp.
    - apply andb_true_iff in Hp. destruct Hp as [Hx Hp]. apply andb_true_iff. split; [|apply IH, Hp].
      rewrite forallb_forall in *. intros y Hy. apply Hx. eapply sublist_in; eassumption.
Qed.

Lemma forallb_sublist: forall {A: Type} (f: A -> bool) l1 l2,
    sublist l1 l2 -> forallb f l2 = true -> forallb f l1 = true.
Proof.
    intros A f l1 l2 H Hf. rewrite forallb_forall in *. intros x Hx. apply Hf. eapply sublist_in; eassumption.
Qed.

(* every element of a pairwise related list is related to all the others *)
Lemma pairwise_middle: forall {A: Type} (R: A -> A -> bool) l1 x l2,
    (forall a b, R a b = R b a) ->
    pairwise R (l1 ++ x :: l2) = true ->
    forall y, In y (l1 ++ l2) -> R x y = true.
Proof.
    intros A R l1 x l2 Hsym. induction l1 as [|z l1 IH]; simpl; intros Hp y Hy;
        apply andb_true_iff in Hp; destruct Hp as [Hz Hp]; rewrite forallb_forall in Hz.
    - apply Hz, Hy.
    - destruct Hy as [<-|Hy].
      + rewrite Hsym. apply Hz, in_or_app. right. left. reflexivity.
      + apply IH; assumption.
Qed.

Lemma pairwise_cons: forall {A: Type} (R: A -> A -> bool) x l,
    (forall y, In y l -> R x y = true) -> pairwise R l = true -> pairwise R (x :: l) = true.
Proof. intros. simpl. apply andb_true_iff. split; [apply forallb_forall|]; assumption. Qed.

Lemma pairwise_app: forall {A: Type} (R: A -> A -> bool) l1 l2,
    pairwise R l1 = true -> pairwise R l2 = true ->
    (forall x y, In x l1 -> In y l2 -> R x y = true) ->
    pairwise R (l1 ++ l2) = true.
Proof.
    intros A R l1 l2 H1 H2 Hcross. induction l1 as [|x l1 IH]; simpl in *; [exact H2|].
    apply andb_true_iff in H1. destruct H1 as [Hx H1]. apply andb_true_iff. split.
    - rewrite forallb_forall in *. intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
      + apply Hx, Hy.
      + apply Hcross; [left; reflexivity|exact Hy].
    - apply IH; [exact H1|]. intros a b Ha Hb. apply Hcross; [right; exact Ha|exact Hb].
Qed.

Lemma may_coexist_readonly: forall m, may_coexist readonly m = true.
Proof. intros []; reflexivity. Qed.

(* What keeps the references conflict-free from one step to the next *)
Definition invariant (s: Aliasing): Prop :=
    conflict_free s = true
    (* exclusive references are never captured as anything but the owner *)
    /\ (forall m, In (captured m) (aliases s) -> m <> exclusive)
    (* as long as there is an owner, all captured references are readonly *)
    /\ (owner s <> dead -> forall m, In (captured m) (aliases s) -> m = readonly)
    (* the tracked mutability is a lower bound of the active borrows *)
    /\ (forall b, owner s = borrowed b -> forall m, In (borrow m) (aliases s) -> is_subtype_of b m = true)
    (* as long as the owner isn't borrowed, all borrows are readonly *)
    /\ (is_borrowed (owner s) = false -> forall m, In (borrow m) (aliases s) -> m = readonly).

Lemma alias_coexists_with_owner: forall s a,
    conflict_free s = true -> In a (aliases s) ->
    may_coexist (owner_mutability (owner s)) (alias_mutability a) = true.
Proof.
    intros s a H Ha. unfold conflict_free in H. apply andb_true_iff in H.
    destruct H as [H _]. rewrite forallb_forall in H. apply H, Ha.
Qed.

Lemma aliases_coexist: forall s,
    conflict_free s = true ->
    pairwise (fun a b => may_coexist (alias_mutability a) (alias_mutability b)) (aliases s) = true.
Proof. intros s H. unfold conflict_free in H. apply andb_true_iff in H. apply H. Qed.

Lemma make_conflict_free: forall o l,
    (forall a, In a l -> may_coexist (owner_mutability o) (alias_mutability a) = true) ->
    pairwise (fun a b => may_coexist (alias_mutability a) (alias_mutability b)) l = true ->
    conflict_free (mkAliasing o l) = true.
Proof. intros o l Ho Hp. unfold conflict_free. simpl. apply andb_true_iff. split; [apply forallb_forall|]; assumption. Qed.

(* Adding an alias created from the existing alias `source`, keeping the source. *)
Lemma conflict_free_derived: forall o l1 l2 source new,
    conflict_free (mkAliasing o (l1 ++ source :: l2)) = true ->
    alias_mutability source <> exclusive ->
    is_subtype_of (alias_mutability source) (alias_mutability new) = true ->
    conflict_free (mkAliasing o (new :: l1 ++ source :: l2)) = true.
Proof.
    intros o l1 l2 source new H Hsource Hsub.
    pose proof (fun a => alias_coexists_with_owner _ a H) as Howner. pose proof (aliases_coexist _ H) as Hpairs.
    simpl in Howner, Hpairs.
    apply make_conflict_free.
    - intros a [<-|Ha]; [|apply Howner, Ha].
      eapply may_coexist_supertype; [|exact Hsub]. apply Howner, in_or_app. right. left. reflexivity.
    - apply pairwise_cons; [|exact Hpairs].
      intros y Hy. rewrite may_coexist_sym. apply in_app_or in Hy. destruct Hy as [Hy|[<-|Hy]].
      + eapply may_coexist_supertype; [|exact Hsub].
        rewrite may_coexist_sym. apply (pairwise_middle (fun a b => may_coexist (alias_mutability a) (alias_mutability b)) l1 source l2); [intros; apply may_coexist_sym|exact Hpairs|].
        apply in_or_app. left. exact Hy.
      + apply may_coexist_with_source; assumption.
      + eapply may_coexist_supertype; [|exact Hsub].
        rewrite may_coexist_sym. apply (pairwise_middle (fun a b => may_coexist (alias_mutability a) (alias_mutability b)) l1 source l2); [intros; apply may_coexist_sym|exact Hpairs|].
        apply in_or_app. right. exact Hy.
Qed.

Lemma in_derived: forall {A: Type} (x y: A) l1 source l2,
    In x (y :: l1 ++ source :: l2) -> x = y \/ In x (l1 ++ source :: l2).
Proof. intros. simpl in H. destruct H; [left; symmetry|right]; assumption. Qed.

Lemma invariant_transition: forall s s', invariant s -> transition s s' -> invariant s'.
Proof.
    intros s s' [Hfree [Hexcl [Hreadonly [Hbound Hborrows]]]] Htransition.
    destruct Htransition as [l|l m Hm|o l1 l2 m m' Hsub|l m|b l m Hallowed|o l1 l2 m m' Hm Hsub|o l1 a l2];
        simpl in Hexcl, Hreadonly, Hbound, Hborrows.
    - (* capture_owner_as_readonly *)
      pose proof (fun a => alias_coexists_with_owner _ a Hfree) as Howner. pose proof (aliases_coexist _ Hfree) as Hpairs.
      repeat split; simpl.
      + apply make_conflict_free; [intros a [<-|Ha]; [reflexivity|apply Howner, Ha]|].
        apply pairwise_cons; [intros; reflexivity|exact Hpairs].
      + intros m0 [Heq|Hin]; [injection Heq as <-; discriminate|apply Hexcl, Hin].
      + intros _ m0 [Heq|Hin]; [injection Heq as <-; reflexivity|apply Hreadonly; [discriminate|exact Hin]].
      + intros b0 Hb0. discriminate Hb0.
      + intros _ m0 [Heq|Hin]; [discriminate Heq|apply Hborrows; [reflexivity|exact Hin]].
    - (* capture_owner *)
      pose proof (fun a => alias_coexists_with_owner _ a Hfree) as Howner. pose proof (aliases_coexist _ Hfree) as Hpairs.
      simpl in Howner, Hpairs.
      repeat split; simpl.
      + apply make_conflict_free; [intros; reflexivity|].
        apply pairwise_cons; [|exact Hpairs].
        intros y Hy. rewrite (may_coexist_exclusive _ (Howner y Hy)). destruct m; reflexivity.
      + intros m0 [Heq|Hin]; [injection Heq as <-; destruct Hm as [->| ->]; discriminate|apply Hexcl, Hin].
      + intros Hdead. exfalso. apply Hdead. reflexivity.
      + intros b0 Hb0. discriminate Hb0.
      + intros _ m0 [Heq|Hin]; [discriminate Heq|apply Hborrows; [reflexivity|exact Hin]].
    - (* capture_alias *)
      assert (Hm: m <> exclusive). { apply Hexcl, in_or_app. right. left. reflexivity. }
      repeat split; simpl.
      + apply (conflict_free_derived _ _ _ (captured m) (captured m')); assumption.
      + intros m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [|apply Hexcl, Hin].
        injection Heq as ->. intros ->. apply Hm, mutability_subtype_of_exclusive, Hsub.
      + intros Ho m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [|apply Hreadonly; assumption].
        injection Heq as ->. assert (Hro: m = readonly). { apply Hreadonly; [exact Ho|]. apply in_or_app. right. left. reflexivity. }
        subst m. destruct m'; simpl in Hsub; congruence.
      + intros b0 Hb0 m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [discriminate Heq|]. apply (Hbound b0 Hb0), Hin.
      + intros Ho m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [discriminate Heq|]. apply Hborrows; assumption.
    - (* start_borrow *)
      pose proof (fun a => alias_coexists_with_owner _ a Hfree) as Howner. pose proof (aliases_coexist _ Hfree) as Hpairs.
      simpl in Howner, Hpairs.
      repeat split; simpl.
      + apply make_conflict_free; [intros; reflexivity|].
        apply pairwise_cons; [|exact Hpairs].
        intros y Hy. rewrite (may_coexist_exclusive _ (Howner y Hy)). destruct m; reflexivity.
      + intros m0 [Heq|Hin]; [discriminate Heq|apply Hexcl, Hin].
      + intros _ m0 [Heq|Hin]; [discriminate Heq|apply Hreadonly; [discriminate|exact Hin]].
      + intros b0 Hb0 m0 Hin. injection Hb0 as <-. destruct Hin as [Heq|Hin].
        * injection Heq as <-. apply mutability_is_subtype_of_refl.
        * pose proof (may_coexist_exclusive _ (Howner _ Hin)) as Hro. simpl in Hro. rewrite Hro.
          apply mutability_subtype_of_readonly.
      + intros Hb. discriminate Hb.
    - (* add_borrow *)
      pose proof (aliases_coexist _ Hfree) as Hpairs. simpl in Hpairs, Hallowed.
      repeat split; simpl.
      + apply make_conflict_free; [intros; reflexivity|].
        apply pairwise_cons; [|exact Hpairs].
        intros [m0|m0] Hy; simpl.
        * rewrite (Hreadonly ltac:(discriminate) m0 Hy). destruct m; reflexivity.
        * eapply may_coexist_supertype; [exact Hallowed|]. apply (Hbound b eq_refl), Hy.
      + intros m0 [Heq|Hin]; [discriminate Heq|apply Hexcl, Hin].
      + intros _ m0 [Heq|Hin]; [discriminate Heq|apply Hreadonly; [discriminate|exact Hin]].
      + intros b0 Hb0 m0 Hin. injection Hb0 as <-. destruct Hin as [Heq|Hin].
        * injection Heq as <-. apply intersect_mutability_right.
        * eapply mutability_subtype_trans; [apply intersect_mutability_left|]. apply (Hbound b eq_refl), Hin.
      + intros Hb. discriminate Hb.
    - (* reborrow *)
      repeat split; simpl.
      + apply (conflict_free_derived _ _ _ (borrow m) (borrow m')); assumption.
      + intros m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [discriminate Heq|apply Hexcl, Hin].
      + intros Ho m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [discriminate Heq|apply Hreadonly; assumption].
      + intros b0 Hb0 m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [|apply (Hbound b0 Hb0), Hin].
        injection Heq as ->. eapply mutability_subtype_trans; [|exact Hsub].
        apply (Hbound b0 Hb0), in_or_app. right. left. reflexivity.
      + intros Ho m0 Hin. apply in_derived in Hin. destruct Hin as [Heq|Hin]; [|apply Hborrows; assumption].
        injection Heq as ->. assert (Hro: m = readonly). { apply Hborrows; [exact Ho|]. apply in_or_app. right. left. reflexivity. }
        subst m. destruct m'; simpl in Hsub; congruence.
    - (* drop *)
      pose proof (fun a => alias_coexists_with_owner _ a Hfree) as Howner. pose proof (aliases_coexist _ Hfree) as Hpairs.
      simpl in Howner, Hpairs.
      assert (Hin: forall x, In x (l1 ++ l2) -> In x (l1 ++ a :: l2)).
      { intros x Hx. eapply sublist_in; [apply sublist_remove|exact Hx]. }
      repeat split; simpl.
      + apply make_conflict_free; [intros x Hx; apply Howner, Hin, Hx|].
        eapply pairwise_sublist; [apply sublist_remove|exact Hpairs].
      + intros m0 Hm0. apply Hexcl, Hin, Hm0.
      + intros Ho m0 Hm0. apply Hreadonly; [exact Ho|apply Hin, Hm0].
      + intros b0 Hb0 m0 Hm0. apply (Hbound b0 Hb0), Hin, Hm0.
      + intros Ho m0 Hm0. apply Hborrows; [exact Ho|apply Hin, Hm0].
Qed.

Lemma owner_after_invocation_alive: forall before after,
    owner_after_invocation before after = alive -> after <> dead /\ is_borrowed before = false.
Proof. intros [] [] H; simpl in H; try discriminate H; split; (congruence || reflexivity). Qed.

Lemma owner_after_invocation_not_dead: forall before after,
    owner_after_invocation before after <> dead -> after <> dead.
Proof. intros [] [] H; simpl in H; congruence. Qed.

Lemma owner_after_invocation_borrowed: forall before after b,
    owner_after_invocation before after = borrowed b -> before = borrowed b.
Proof. intros [] [] b H; simpl in H; congruence. Qed.

Lemma owner_after_invocation_not_borrowed: forall before after,
    is_borrowed (owner_after_invocation before after) = false -> after = dead \/ is_borrowed before = false.
Proof. intros [] [] H; simpl in H; auto. Qed.

(* An invocation that starts while the owner is borrowed can't end the borrow, nor the lifetime of the owner. *)
Lemma owner_stays_borrowed:
    (forall s s', step s s' -> is_borrowed (owner s) = true -> is_borrowed (owner s') = true)
    /\ (forall s s', evaluates s s' -> is_borrowed (owner s) = true -> is_borrowed (owner s') = true).
Proof.
    apply step_evaluates_mut.
    - intros s s' Htransition Hb. destruct Htransition; simpl in *; congruence.
    - intros s s' _ IH Hb. specialize (IH Hb). simpl.
      destruct (owner s), (owner s'); simpl in *; congruence.
    - intros s Hb. exact Hb.
    - intros s s' s'' _ IH1 _ IH2 Hb. apply IH2, IH1, Hb.
Qed.

Lemma invariant_return: forall before after,
    invariant before -> invariant after ->
    (is_borrowed (owner before) = true -> is_borrowed (owner after) = true) ->
    invariant (return_from before after).
Proof.
    intros before after [Hfree [Hexcl [Hreadonly [Hbound Hborrows]]]] [Hfree' [Hexcl' [Hreadonly' [Hbound' Hborrows']]]] Hstays.
    set (captures := filter is_captured (aliases after)).
    set (borrows := filter (fun a => negb (is_captured a)) (aliases before)).
    (* the captures from evaluating the arguments are readonly, unless the owner was captured *)
    assert (Hcaptures: owner after <> dead -> forall a, In a captures -> alias_mutability a = readonly).
    { intros Ho [m|m] Ha; apply filter_In in Ha; destruct Ha as [Ha Hc]; [|discriminate Hc]. apply (Hreadonly' Ho m Ha). }
    (* the borrows from before the invocation are readonly, unless the owner was borrowed *)
    assert (Hborrowed: is_borrowed (owner before) = false -> forall a, In a borrows -> alias_mutability a = readonly).
    { intros Ho [m|m] Ha; apply filter_In in Ha; destruct Ha as [Ha Hc]; [discriminate Hc|]. apply (Hborrows Ho m Ha). }
    (* the owner can't be captured while it is borrowed *)
    assert (Hcross: owner after <> dead \/ is_borrowed (owner before) = false).
    { destruct (is_borrowed (owner before)) eqn:Hb; [left|right; reflexivity].
      intros Hd. specialize (Hstays eq_refl). rewrite Hd in Hstays. discriminate Hstays. }
    assert (Hin: forall a, In a (captures ++ borrows) -> (In a captures /\ In a (aliases after)) \/ (In a borrows /\ In a (aliases before))).
    { intros a Ha. apply in_app_or in Ha. destruct Ha as [Ha|Ha]; [left|right]; split; try exact Ha; apply filter_In in Ha; apply Ha. }
    unfold return_from. fold captures borrows.
    repeat split; cbn [owner aliases].
    - apply make_conflict_free.
      + intros a Ha. destruct (owner_after_invocation (owner before) (owner after)) eqn:Ho; simpl; try reflexivity.
        apply owner_after_invocation_alive in Ho. destruct Ho as [Hafter Hbefore].
        destruct (Hin a Ha) as [[Ha' _]|[Ha' _]]; [rewrite (Hcaptures Hafter a Ha')|rewrite (Hborrowed Hbefore a Ha')]; reflexivity.
      + apply pairwise_app.
        * eapply pairwise_sublist; [apply sublist_filter|exact (aliases_coexist _ Hfree')].
        * eapply pairwise_sublist; [apply sublist_filter|exact (aliases_coexist _ Hfree)].
        * intros x y Hx Hy. cbv beta. destruct Hcross as [Ho|Ho].
          -- rewrite (Hcaptures Ho x Hx). apply may_coexist_readonly.
          -- rewrite (Hborrowed Ho y Hy), may_coexist_sym. apply may_coexist_readonly.
    - intros m Hm. destruct (Hin _ Hm) as [[_ Hm']|[Hm' _]]; [apply Hexcl', Hm'|].
      apply filter_In in Hm'. destruct Hm' as [_ Hc]. discriminate Hc.
    - intros Ho m Hm. destruct (Hin _ Hm) as [[_ Hm']|[Hm' _]].
      + apply Hreadonly'; [apply (owner_after_invocation_not_dead (owner before)), Ho|exact Hm'].
      + apply filter_In in Hm'. destruct Hm' as [_ Hc]. discriminate Hc.
    - intros b Hb m Hm. apply owner_after_invocation_borrowed in Hb.
      destruct (Hin _ Hm) as [[Hm' _]|[_ Hm']].
      + apply filter_In in Hm'. destruct Hm' as [_ Hc]. discriminate Hc.
      + apply (Hbound b Hb), Hm'.
    - intros Ho m Hm. destruct (Hin _ Hm) as [[Hm' _]|[Hm' _]].
      + apply filter_In in Hm'. destruct Hm' as [_ Hc]. discriminate Hc.
      + apply owner_after_invocation_not_borrowed in Ho.
        assert (Hbefore: is_borrowed (owner before) = false) by (destruct Ho as [Ho|Ho]; [destruct Hcross; [contradiction|assumption]|exact Ho]).
        apply (Hborrowed Hbefore _ Hm').
Qed.

(* What happens to the references keeps them conflict-free *)
Lemma invariant_steps:
    (forall s s', step s s' -> invariant s -> invariant s')
    /\ (forall s s', evaluates s s' -> invariant s -> invariant s').
Proof.
    apply step_evaluates_mut.
    - intros s s' Htransition Hinv. eapply invariant_transition; eassumption.
    - intros s s' Hevaluates IH Hinv. apply invariant_return; [exact Hinv|apply IH, Hinv|].
      apply (proj2 owner_stays_borrowed _ _ Hevaluates).
    - intros s Hinv. exact Hinv.
    - intros s s' s'' _ IH1 _ IH2 Hinv. apply IH2, IH1, Hinv.
Qed.

(* No two references to an object ever make conflicting promises. *)
Theorem references_are_conflict_free: forall s,
    reachable s -> conflict_free s = true.
Proof.
    intros s H. enough (Hinv: invariant s) by apply Hinv.
    apply (proj2 invariant_steps _ _ H).
    repeat split; simpl; intros; contradiction.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (b) Assignability respects mutability                                                           *)
(*                                                                                                *)
(* Model (a) creates every alias as a supertype of the reference it is created from. This shows    *)
(* that type checking guarantees that, for the types a reference to an object can have.            *)
(* ---------------------------------------------------------------------------------------------- *)

(*
 * Whether a reference of this type can refer to an object. Not if Nothing is in the way: by the
 * axiom that panic never returns, the constructor of Nothing never returns, so no object is of
 * type Nothing (generics bounded by Nothing included). Erroneous types fail to compile; type
 * arguments and type variables aren't the types of references.
 *)
Fixpoint can_refer_to_object (t: EType): bool :=
    match t with
    | RootResolved _ c _ => negb (class_eqb c nothing)
    | Nullable n => can_refer_to_object n
    | Generic (mkGenericRef _ _ bound) => can_refer_to_object bound
    | Error _ _ | TypeArgument _ _ | TypeVariable _ => false
    | Intersection components => forallb can_refer_to_object components
    end.

Lemma generic_mutability_below_bound: forall g p b,
    is_subtype_of (mutability_of env (Generic (mkGenericRef g p b))) (mutability_of env b) = true.
Proof.
    intros [m|] p b; simpl; [|apply mutability_is_subtype_of_refl].
    destruct (is_subtype_of m (mutability_of env b)) eqn:E; [exact E|apply mutability_is_subtype_of_refl].
Qed.

Lemma generic_is_subtype_of_mutability: forall t p m,
    generic_is_subtype_of env t p m = true -> is_subtype_of (mutability_of env t) m = true.
Proof.
    fix IH 1. intros t p m H.
    destruct t as [| |[g p' b]| | | |]; cbn [generic_is_subtype_of] in H; try discriminate H.
    destruct (param_eqb p' p); [exact H|].
    eapply mutability_subtype_trans; [apply generic_mutability_below_bound|]. eapply IH, H.
Qed.

Lemma fold_intersect_below_acc: forall l acc, is_subtype_of (fold_left intersect_mutability l acc) acc = true.
Proof.
    induction l as [|x rest IH]; intros acc; simpl; [apply mutability_is_subtype_of_refl|].
    eapply mutability_subtype_trans; [apply IH|apply intersect_mutability_left].
Qed.

Lemma fold_intersect_below_element: forall l acc x,
    In x l -> is_subtype_of (fold_left intersect_mutability l acc) x = true.
Proof.
    induction l as [|y rest IH]; intros acc x Hx; simpl; [contradiction|].
    destruct Hx as [<-|Hx]; [|apply IH, Hx].
    eapply mutability_subtype_trans; [apply fold_intersect_below_acc|apply intersect_mutability_right].
Qed.

Lemma fold_intersect_greatest: forall l acc x,
    is_subtype_of x acc = true -> (forall y, In y l -> is_subtype_of x y = true) ->
    is_subtype_of x (fold_left intersect_mutability l acc) = true.
Proof.
    induction l as [|y rest IH]; intros acc x Hacc Hl; simpl; [exact Hacc|].
    apply IH; [apply intersect_mutability_greatest; [exact Hacc|apply Hl; left; reflexivity]|].
    intros z Hz. apply Hl. right. exact Hz.
Qed.

Lemma intersection_mutability: forall components,
    mutability_of env (Intersection components) = fold_left intersect_mutability (map (mutability_of env) components) readonly.
Proof. reflexivity. Qed.

Lemma intersection_mutability_below_component: forall components c,
    In c components -> is_subtype_of (mutability_of env (Intersection components)) (mutability_of env c) = true.
Proof.
    intros components c Hc. rewrite intersection_mutability.
    apply fold_intersect_below_element, in_map, Hc.
Qed.

Lemma find_first_found: forall attempt candidates c states,
    find_first attempt candidates = Some (Some (c, states)) ->
    In c candidates /\ attempt c = Some (Ongoing states).
Proof.
    intros attempt candidates. induction candidates as [|x rest IH]; intros c states H; simpl in H.
    - discriminate H.
    - destruct (attempt x) as [[s|]|] eqn:E; try discriminate H.
      + injection H as <- <-. split; [left; reflexivity|exact E].
      + destruct (IH _ _ H) as [Hin Hc]. split; [right; exact Hin|exact Hc].
Qed.

Lemma intersection_flipped_unify_found: forall fuel target components states u,
    intersection_flipped_unify (unify env fuel) target components states = Some (Ongoing u) ->
    exists c, In c components /\ unify env fuel target c (Ongoing states) = Some (Ongoing u).
Proof.
    intros fuel target components states u H. unfold intersection_flipped_unify in H.
    destruct (find_first _ components) as [[[c s]|]|] eqn:E; try discriminate H.
    injection H as <-. apply find_first_found in E. exists c. exact E.
Qed.

Lemma fold_unify_stays_failed: forall fuel assignee l,
    fold_unify (fun inner c => unify env fuel c assignee inner) l Failed = Some Failed.
Proof. intros fuel assignee l. induction l; simpl; [reflexivity|]. rewrite unify_keeps_failure. assumption. Qed.

Lemma fold_unify_each: forall fuel assignee l states u,
    fold_unify (fun inner c => unify env fuel c assignee inner) l (Ongoing states) = Some (Ongoing u) ->
    forall c, In c l -> exists s s', unify env fuel c assignee (Ongoing s) = Some (Ongoing s').
Proof.
    intros fuel assignee l. induction l as [|x rest IH]; intros states u H c Hc; simpl in H, Hc; [contradiction|].
    destruct (unify env fuel x assignee (Ongoing states)) as [[s'|]|] eqn:E; try discriminate H.
    - destruct Hc as [<-|Hc]; [exists states, s'; exact E|]. eapply IH; eassumption.
    - rewrite fold_unify_stays_failed in H. discriminate H.
Qed.

Lemma no_type_variables: forall components,
    forallb can_refer_to_object components = true ->
    filter is_type_variable components = [] /\ filter (fun c => negb (is_type_variable c)) components = components.
Proof.
    induction components as [|c rest IH]; intros H; simpl in *; [split; reflexivity|].
    apply andb_true_iff in H. destruct H as [Hc H]. destruct (IH H) as [IH1 IH2].
    destruct c as [| |[]| | | |]; simpl in Hc; try discriminate Hc; simpl; rewrite IH1, IH2; split; reflexivity.
Qed.

(*
 * If a value can be assigned to a reference, and both types can refer to an object, then the
 * mutability of the reference is a supertype of the mutability of the value.
 *)
Theorem unify_respects_mutability: forall fuel target assignee states u,
    unify env fuel target assignee (Ongoing states) = Some (Ongoing u) ->
    can_refer_to_object target = true ->
    can_refer_to_object assignee = true ->
    is_subtype_of (mutability_of env assignee) (mutability_of env target) = true.
Proof.
    induction fuel as [|fuel IH]; intros target assignee states u H Ht Ha; [discriminate H|].
    change (unify env (S fuel) target assignee (Ongoing states))
        with (unify_step env (unify env fuel) target assignee states) in H.
    destruct target as [tm tc targs|tn|[tg tp tb]|tm tmsg|tv tt|[tg tp tb]|tcs]; simpl in Ht; try discriminate Ht;
        cbv beta iota delta [unify_step] in H.
    - (* RootResolved *)
      cbv beta iota delta [unify_root_resolved] in H.
      destruct assignee as [am ac aargs|an|[ag ap ab]|am amsg|av aty|[ag ap ab]|acs]; simpl in Ha; try discriminate Ha.
      + destruct (negb (base_type_is_subtype_of env ac tc)); [discriminate H|].
        match type of H with context [negb (is_subtype_of ?x ?y)] => destruct (is_subtype_of x y) eqn:E end;
            [reflexivity|discriminate H].
      + discriminate H.
      + eapply mutability_subtype_trans; [apply generic_mutability_below_bound|]. eapply IH; eassumption.
      + destruct (intersection_flipped_unify_found _ _ _ _ _ H) as [c [Hc Hu]].
        eapply mutability_subtype_trans; [apply intersection_mutability_below_component, Hc|].
        eapply IH; [exact Hu|exact Ht|]. rewrite forallb_forall in Ha. apply Ha, Hc.
    - (* Nullable *)
      cbv beta iota delta [unify_nullable] in H.
      change (mutability_of env (Nullable tn)) with (mutability_of env tn).
      destruct assignee as [am ac aargs|an|[ag ap ab]|am amsg|av aty|[ag ap ab]|acs]; simpl in Ha; try discriminate Ha.
      + eapply IH; eassumption.
      + change (mutability_of env (Nullable an)) with (mutability_of env an). eapply IH; eassumption.
      + (* depending on the nested type, the assignee is unified with it, or its bound with this *)
        assert (Hnested: unify env fuel tn (Generic (mkGenericRef ag ap ab)) (Ongoing states) = Some (Ongoing u) ->
            is_subtype_of (mutability_of env (Generic (mkGenericRef ag ap ab))) (mutability_of env tn) = true).
        { intros Hu. eapply IH; [exact Hu|exact Ht|exact Ha]. }
        assert (Hself: unify env fuel (Nullable tn) ab (Ongoing states) = Some (Ongoing u) ->
            is_subtype_of (mutability_of env (Generic (mkGenericRef ag ap ab))) (mutability_of env tn) = true).
        { intros Hu. eapply mutability_subtype_trans; [apply generic_mutability_below_bound|].
          change (mutability_of env tn) with (mutability_of env (Nullable tn)).
          eapply IH; [exact Hu|exact Ht|exact Ha]. }
        destruct tn as [| |[]| | | |]; first [exact (Hnested H) | exact (Hself H)].
      + eapply IH; eassumption.
    - (* Generic *)
      cbv beta iota delta [unify_generic] in H.
      destruct assignee as [am ac aargs|an|[ag ap ab]|am amsg|av aty|[ag ap ab]|acs]; simpl in Ha; try discriminate Ha.
      + simpl in H. apply negb_true_iff in Ha. rewrite Ha in H. discriminate H.
      + discriminate H.
      + destruct (generic_is_subtype_of _ _ _ _) eqn:E; [|discriminate H].
        apply generic_is_subtype_of_mutability in E. exact E.
      + destruct (intersection_flipped_unify_found _ _ _ _ _ H) as [c [Hc Hu]].
        eapply mutability_subtype_trans; [apply intersection_mutability_below_component, Hc|].
        eapply IH; [exact Hu|exact Ht|]. rewrite forallb_forall in Ha. apply Ha, Hc.
    - (* Intersection *)
      cbv beta iota zeta delta [unify_intersection] in H.
      destruct (no_type_variables _ Ht) as [Hvar Hnonvar].
      assert (Hcomponents: forall s', fold_unify (fun inner c => unify env fuel c assignee inner) tcs (Ongoing states) = Some (Ongoing s') ->
          is_subtype_of (mutability_of env assignee) (mutability_of env (Intersection tcs)) = true).
      { intros s' Hfold. rewrite intersection_mutability.
        apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
        intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]].
        destruct (fold_unify_each _ _ _ _ _ Hfold c Hc) as [s1 [s1' Hu]].
        eapply IH; [exact Hu| |exact Ha]. rewrite forallb_forall in Ht. apply Ht, Hc. }
      destruct assignee as [am ac aargs|an|[ag ap ab]|am amsg|av aty|[ag ap ab]|acs]; simpl in Ha; try discriminate Ha;
          try (simpl in H; discriminate H);
          rewrite Hnonvar in H;
          (destruct (fold_unify _ tcs (Ongoing states)) as [[s2|]|] eqn:Efold; try discriminate H);
          eapply Hcomponents; reflexivity.
Qed.

(* The same, in terms of is_assignable_to: a value can only ever be aliased by references that
   promise less. *)
Theorem assignability_respects_mutability: forall fuel sub super,
    is_assignable_to env fuel sub super = Some true ->
    can_refer_to_object sub = true ->
    can_refer_to_object super = true ->
    is_subtype_of (mutability_of env sub) (mutability_of env super) = true.
Proof.
    intros fuel sub super H Hsub Hsuper. unfold is_assignable_to in H.
    destruct (unify env fuel super sub empty_unification) as [[u|]|] eqn:E; try discriminate H.
    eapply unify_respects_mutability; eassumption.
Qed.

End Ops.
