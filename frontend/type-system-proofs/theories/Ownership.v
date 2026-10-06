From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Owned and ref slots                                                                              *)
(*                                                                                                *)
(* A slot is a field, or an element of a generic data structure. Where a type is used, each slot is *)
(* declared to either own the object in it, making it part of the holder's block, or to merely     *)
(* refer to it (see Ops.v, part (a), for blocks):                                                  *)
(*   class Order { customer: ref const Customer; lines: owned mut List<owned mut Line> }           *)
(*   Array<owned mut Order>, Array<ref mut Order>                                                  *)
(* In generic code, a slot can also have the ownership of a type parameter, `Array<T>`, or any      *)
(* ownership, `Array<any T>` (see Model.Ownership).                                                *)
(* A slot is described by its ownership and the mutability of its type. Owning only takes effect    *)
(* for mutable types: an owned const object is immutable, whoever holds it, so it can be shared     *)
(* like a referred one; owned const and ref const slots are the same.                              *)
(* This is not implemented in the Kotlin frontend, yet.                                            *)
(* ---------------------------------------------------------------------------------------------- *)

(* There are no exclusive slots. A ref slot read twice would yield two exclusive references (in terms
   of the blocks: a ref slot is a captured reference, and those are never exclusive). An owned one
   would add nothing to `owned mut`, which gives exclusive objects through an exclusive holder; and,
   viewed covariantly as `owned const`, it would claim immutable objects that the holder mutates. *)
Definition valid_slot (o: Ownership) (m: Mutability): bool :=
    negb (Mutability_beq m exclusive).

(* The mutability of an owned object, as read through a reference to its holder: a mutable one has
   that of the holder, being part of its block; a const one is immutable anyway; a read one might
   be either *)
Definition owned_element_mutability (holder m: Mutability): Mutability :=
    match m with
    | immutable => immutable
    | readonly => union holder immutable
    | mutable | exclusive => holder
    end.

(* The mutability of the object in a slot, as read through a reference to the holder: owned ones as
   above, a referred object with the mutability of the slot. Where the ownership isn't known to be
   one of them, only what both allow is sure. *)
Definition element_mutability (holder: Mutability) (o: Ownership) (m: Mutability): Mutability :=
    match o with
    | owned => owned_element_mutability holder m
    | ref => m
    | any_ownership | parameter_ownership _ => union (owned_element_mutability holder m) m
    end.

(* The mutability of the plain values that go into a slot. Owned slots of a mutable type take
   nothing but exclusive references: an object in such a slot has no other references than readonly
   ones, so that the block can be frozen. Owned slots of a const or read type never give out mutable
   access, so an immutable object is as good as an adopted one. Where the ownership isn't known,
   exclusive ones only: a slot of the ownership of a type parameter whose bound is read might be an
   owned mut one, and any slot might be one of those. *)
Definition stored_mutability (o: Ownership) (m: Mutability): Mutability :=
    match o with
    | owned => match m with immutable | readonly => immutable | mutable | exclusive => exclusive end
    | ref => m
    | any_ownership | parameter_ownership _ => exclusive
    end.

(* A value to be written into a slot *)
Inductive Value :=
    (* a value of a known mutability *)
    | plain (mutability: Mutability)
    (* a value of type T, for a type parameter T: it is what the instantiation of T makes it, an
       exclusive reference for an owned one, a reference of the type's mutability for a ref one *)
    | of_parameter (param: TypeParameterId)
    .

(* Whether a value can be written into a slot, through a reference to the holder with the given
   mutability. A value of type T fits slots with the ownership of T, and only those: in any other,
   the ownership might be a different one than T's. *)
Definition can_store (holder: Mutability) (o: Ownership) (m: Mutability) (value: Value): bool :=
    mutability_allows_mutation holder &&
    match value with
    | plain v => is_subtype_of v (stored_mutability o m)
    | of_parameter p => match o with parameter_ownership p' => param_eqb p p' | _ => false end
    end.

Lemma owned_slots_of_mutable_types_take_only_exclusive: forall holder value,
    can_store holder owned mutable value = true -> value = plain exclusive.
Proof. intros [] [[]|p] H; unfold can_store in H; simpl in H; congruence. Qed.

(* Owning only takes effect for mutable types *)
Lemma owned_const_is_ref_const: forall holder value,
    element_mutability holder owned immutable = element_mutability holder ref immutable
    /\ can_store holder owned immutable value = can_store holder ref immutable value.
Proof. intros holder value. split; [reflexivity|]. unfold can_store. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Writing into slots, and taking parts out of a block, in terms of the blocks                     *)
(* ---------------------------------------------------------------------------------------------- *)

(* All other references to a block with an exclusive owner are readonly *)
Lemma exclusively_owned_block_has_only_readonly_references: forall s,
    reachable s -> owner s = alive ->
    forall a, In a (aliases s) -> alias_mutability a = readonly.
Proof.
    intros s Hs Ho a Ha.
    pose proof (alias_coexists_with_owner s a (references_are_conflict_free s Hs) Ha) as H.
    rewrite Ho in H. change (may_coexist exclusive (alias_mutability a) = true) in H.
    apply may_coexist_exclusive, H.
Qed.

(* Writing an exclusive reference into an owned slot of a mutable type: the block it owned becomes part of the
   holder's block; that is the adopt transition on the holder's block, and the source block gives up
   its owner. *)
Theorem storing_into_an_owned_slot: forall source holder,
    reachable source -> owner source = alive ->
    transition source (mkAliasing dead (aliases source))
    /\ transition holder (mkAliasing (owner holder) (aliases source ++ aliases holder)).
Proof.
    intros [o l] [o' l'] Hs Ho. simpl in Ho |- *. subst o. split.
    - apply give_up_owner.
    - apply adopt. apply (exclusively_owned_block_has_only_readonly_references _ Hs eq_refl).
Qed.

(* Taking an owned part out of an exclusively owned block, as exclusive: the rest of the block gives
   up its owner, and the part becomes a block of its own, with an exclusive owner. *)
Theorem extracting_an_owned_part: forall s,
    reachable s -> owner s = alive ->
    transition s (mkAliasing dead (aliases s)) /\ initial (mkAliasing alive (aliases s)).
Proof.
    intros [o l] Hs Ho. simpl in Ho |- *. subst o. split.
    - apply give_up_owner.
    - split; [reflexivity|]. apply (exclusively_owned_block_has_only_readonly_references _ Hs eq_refl).
Qed.

(* Writing into a ref slot captures the value with the slot's mutability, as any other capture does
   (transitions capture_owner, capture_owner_as_readonly and capture_alias); the slot then is that
   captured reference. Reading from the slot creates aliases of it (capture_alias, reborrow).
   Neither touches the holder's block. Writing an immutable object into an owned slot of a const or
   read type is the same: it stays a block of its own, frozen already. *)

(* ---------------------------------------------------------------------------------------------- *)
(* Freezing                                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* Once there is a const reference to a block, e.g. because its exclusive owner was captured as
   const, no reference to any of its objects allows mutating it. *)
Theorem frozen_block_is_immutable: forall s,
    reachable s -> In (captured immutable) (aliases s) ->
    mutability_allows_mutation (owner_mutability (owner s)) = false
    /\ forall a, In a (aliases s) -> mutability_allows_mutation (alias_mutability a) = false.
Proof.
    intros s Hs Hin. pose proof (references_are_conflict_free s Hs) as Hfree. split.
    - pose proof (alias_coexists_with_owner s _ Hfree Hin) as H. simpl in H.
      destruct (owner s); simpl in *; congruence.
    - intros a Ha. apply in_split in Hin. destruct Hin as [l1 [l2 Hl]].
      pose proof (aliases_coexist s Hfree) as Hpairs. rewrite Hl in Hpairs, Ha.
      assert (Hc: forall b, In b (l1 ++ l2) -> may_coexist immutable (alias_mutability b) = true).
      { apply (pairwise_middle (fun a b => may_coexist (alias_mutability a) (alias_mutability b)) l1 (captured immutable) l2);
            [intros; apply may_coexist_sym|exact Hpairs]. }
      assert (Hmut: forall b, In b (l1 ++ l2) -> mutability_allows_mutation (alias_mutability b) = false).
      { intros b Hb. specialize (Hc b Hb). destruct (alias_mutability b); simpl in Hc |- *; congruence. }
      apply in_app_or in Ha. destruct Ha as [Ha|[<-|Ha]].
      + apply Hmut, in_or_app. left. exact Ha.
      + reflexivity.
      + apply Hmut, in_or_app. right. exact Ha.
Qed.

(* So no slot in a frozen block can be written *)
Corollary frozen_block_cannot_be_written: forall s o m value,
    reachable s -> In (captured immutable) (aliases s) ->
    can_store (owner_mutability (owner s)) o m value = false
    /\ forall a, In a (aliases s) -> can_store (alias_mutability a) o m value = false.
Proof.
    intros s o m value Hs Hin. destruct (frozen_block_is_immutable s Hs Hin) as [Ho Ha]. split.
    - unfold can_store. rewrite Ho. reflexivity.
    - intros a Hain. unfold can_store. rewrite (Ha a Hain). reflexivity.
Qed.

(* Freezing is deep across owned slots only: what a ref slot refers to keeps its own mutability *)
Example frozen_owned_parts_are_immutable: forall m, element_mutability immutable owned m = immutable.
Proof. intros []; reflexivity. Qed.

Example frozen_ref_parts_keep_their_mutability: element_mutability immutable ref mutable = mutable.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Any ownership is the weakest of all                                                             *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma union_left: forall a b, is_subtype_of a (union a b) = true.
Proof. intros [] []; reflexivity. Qed.

Lemma union_right: forall a b, is_subtype_of b (union a b) = true.
Proof. intros [] []; reflexivity. Qed.

Lemma union_least: forall a b x,
    is_subtype_of a x = true -> is_subtype_of b x = true -> is_subtype_of (union a b) x = true.
Proof. intros [] [] []; simpl; congruence. Qed.

Lemma union_monotone: forall a b b',
    is_subtype_of b b' = true -> is_subtype_of (union a b) (union a b') = true.
Proof. intros [] [] []; simpl; congruence. Qed.

Lemma param_eqb_eq: forall p p', param_eqb p p' = true -> p = p'.
Proof. intros p p' H. apply Nat.eqb_eq, H. Qed.

Lemma param_eqb_refl: forall p, param_eqb p p = true.
Proof. intros p. apply Nat.eqb_refl. Qed.

(*
 * No conflicts between what code can do with a slot through a supertype and what the slot it
 * actually is allows: where the ownership of the slot is assignable to that of the supertype
 * (as for Array<owned T>, Array<ref T> and Array<T> to Array<any T>), reading through the supertype
 * gives no more than the actual slot does, and writing through the supertype takes no more than the
 * actual slot takes. That is for type arguments of the same type; see no_conflicts_through_a_view
 * for type arguments with a variance.
 *)
Theorem no_conflicts_through_a_supertype: forall holder o_actual o m,
    ownership_is_assignable_to o_actual o = true ->
    is_subtype_of (element_mutability holder o_actual m) (element_mutability holder o m) = true
    /\ forall value, can_store holder o m value = true -> can_store holder o_actual m value = true.
Proof.
    intros holder o_actual o m Ho. split.
    - destruct o, o_actual; simpl in Ho; try discriminate Ho; destruct holder, m; reflexivity.
    - intros [v|q] H; unfold can_store in *; apply andb_true_iff in H; destruct H as [Hh Hv]; rewrite Hh; simpl;
        destruct o, o_actual; simpl in Ho, Hv |- *; try discriminate Ho; try discriminate Hv;
        first
            [ exact Hv
            | destruct v, m; simpl in *; try reflexivity; discriminate
            | apply param_eqb_eq in Ho; apply param_eqb_eq in Hv; subst; apply param_eqb_refl ].
Qed.

Corollary no_conflicts_between_owned_and_any: forall holder m,
    is_subtype_of (element_mutability holder owned m) (element_mutability holder any_ownership m) = true
    /\ forall value, can_store holder any_ownership m value = true -> can_store holder owned m value = true.
Proof. intros. apply no_conflicts_through_a_supertype. reflexivity. Qed.

Corollary no_conflicts_between_ref_and_any: forall holder m,
    is_subtype_of (element_mutability holder ref m) (element_mutability holder any_ownership m) = true
    /\ forall value, can_store holder any_ownership m value = true -> can_store holder ref m value = true.
Proof. intros. apply no_conflicts_through_a_supertype. reflexivity. Qed.

Corollary no_conflicts_between_parameter_and_any: forall holder p m,
    is_subtype_of (element_mutability holder (parameter_ownership p) m) (element_mutability holder any_ownership m) = true
    /\ forall value, can_store holder any_ownership m value = true -> can_store holder (parameter_ownership p) m value = true.
Proof. intros. apply no_conflicts_through_a_supertype. reflexivity. Qed.

(* And any ownership is no weaker than it has to be: reading gives exactly what reading both owned
   and ref slots gives. Writing, it takes exactly what both take for mutable types; for the others it
   is stricter than they are (see stored_mutability). *)
Theorem any_ownership_reads_the_least_upper_bound: forall holder m x,
    is_subtype_of (element_mutability holder owned m) x = true ->
    is_subtype_of (element_mutability holder ref m) x = true ->
    is_subtype_of (element_mutability holder any_ownership m) x = true.
Proof. intros holder m x Howned Href. apply union_least; assumption. Qed.

Theorem any_ownership_takes_what_both_take: forall holder value,
    can_store holder any_ownership mutable value = can_store holder owned mutable value && can_store holder ref mutable value.
Proof. intros [] [[]|p]; reflexivity. Qed.

(* So code that doesn't know the ownership can mutate the elements exactly if both the holder and the
   type of the slot allow mutation. An exclusive holder alone doesn't suffice, because a ref slot may
   be const or read. *)
Corollary elements_of_any_ownership_are_mutable: forall holder m,
    mutability_allows_mutation (element_mutability holder any_ownership m)
    = mutability_allows_mutation holder && mutability_allows_mutation m.
Proof. intros [] []; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The ownership of a type parameter: unknown, but the same wherever the generic code says T        *)
(* ---------------------------------------------------------------------------------------------- *)

(* What a type parameter T can be instantiated with, given its mutability bound: a type argument of
   any ownership, with a mutability within the bound *)
Definition satisfies_bound (bound: Mutability) (m: Mutability): bool := is_subtype_of m bound.

(* Reading: whatever T is instantiated with, the elements of a slot with T's ownership have (at
   least) the mutability the generic code sees, as for any ownership and the type of the bound *)
Theorem type_parameter_view_is_sound: forall holder bound p o m,
    valid_slot o m = true -> satisfies_bound bound m = true ->
    is_subtype_of (element_mutability holder o m) (element_mutability holder (parameter_ownership p) bound) = true.
Proof. intros holder bound p o m Hv H. destruct o, holder, m, bound; vm_compute in *; first [reflexivity|discriminate]. Qed.

(* Writing: a value of type T fits the slots with T's ownership... *)
Theorem parameter_values_fit_slots_of_the_parameter: forall holder p m,
    can_store holder (parameter_ownership p) m (of_parameter p) = mutability_allows_mutation holder.
Proof. intros holder p m. unfold can_store. rewrite param_eqb_refl, andb_true_r. reflexivity. Qed.

(* ... but no others: not those of another type parameter, and not owned, ref, or any ones *)
Theorem parameter_values_fit_no_other_slots: forall holder p o m,
    o <> parameter_ownership p -> can_store holder o m (of_parameter p) = false.
Proof.
    intros holder p o m Ho. unfold can_store. destruct o; try (rewrite andb_false_r; reflexivity).
    destruct (param_eqb p param) eqn:E; [|rewrite andb_false_r; reflexivity].
    apply param_eqb_eq in E. subst. contradiction.
Qed.

(* What a value of type T is, once T is instantiated with a type argument of ownership o and type
   mutability m: within more generic code, a value of the type parameter it is instantiated with;
   otherwise, what the slots of that type argument take *)
Definition instantiate_value (o: Ownership) (m: Mutability): Value :=
    match o with
    | parameter_ownership q => of_parameter q
    | owned | ref | any_ownership => plain (stored_mutability o m)
    end.

(* Storing a value of type T into a slot with T's ownership, as in
     class Cache<T> { items: Array<T>; fn put(self: mut _, v: T) { self.items.add(v) } }
   is right for every instantiation of T: the slot then has the ownership of the type argument, and
   the value is what that type argument takes. *)
Theorem parameter_values_fit_under_every_instantiation: forall holder p m o_inst m_inst,
    can_store holder (parameter_ownership p) m (of_parameter p) = true ->
    can_store holder o_inst m_inst (instantiate_value o_inst m_inst) = true.
Proof.
    intros holder p m o_inst m_inst H. rewrite parameter_values_fit_slots_of_the_parameter in H.
    unfold can_store. rewrite H. destruct o_inst; simpl;
        first [reflexivity | apply mutability_is_subtype_of_refl | apply param_eqb_refl].
Qed.

(* Plain values in slots with T's ownership are right for every instantiation, too: those slots take
   only exclusive ones, which all slots take *)
Theorem plain_values_fit_under_every_instantiation: forall holder p m v o_inst m_inst,
    can_store holder (parameter_ownership p) m (plain v) = true ->
    can_store holder o_inst m_inst (plain v) = true.
Proof.
    intros holder p m v o_inst m_inst H. unfold can_store in *. apply andb_true_iff in H.
    destruct H as [Hh Hv]. rewrite Hh. simpl in *. destruct v; try discriminate Hv. reflexivity.
Qed.

(* Why a value of type T can't go into a slot of any ownership: with T instantiated as `ref mut X`,
   the value is a mutable reference, and the slot might be an owned mut one *)
Example parameter_values_dont_fit_any_ownership:
    instantiate_value ref mutable = plain mutable
    /\ can_store mutable owned mutable (plain mutable) = false.
Proof. split; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Ownership and variance are independent                                                          *)
(*                                                                                                *)
(* no_conflicts_through_a_supertype keeps the type of the slot fixed. Viewed through a type        *)
(* argument with a variance, the type may differ, too; the variance rules govern that, just as they *)
(* did before there was ownership. Together, the two sets of rules keep every view free of          *)
(* conflicts, each covering its own dimension of the type argument.                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* Which variance can stand in for which, as unify_type_argument has it: invariant for all of them *)
Definition variance_is_assignable_to (sub super: Variance): bool :=
    match super, sub with
    | Model.invariant, Model.invariant => true
    | output, (output | Model.invariant) => true
    | input, (input | Model.invariant) => true
    | _, _ => false
    end.

(* How the mutability of the type of the actual slot must relate to that of the view, by the view's
   variance; as in unify_type_argument: both ways for invariant, covariant for out, contravariant for
   in. *)
Definition mutability_conforms (v: Variance) (m_actual m: Mutability): bool :=
    match v with
    | Model.invariant => Mutability_beq m_actual m
    | output => is_subtype_of m_actual m
    | input => is_subtype_of m m_actual
    end.

(* What reading an element through a view gives: an in-variant type argument gives the top type,
   `read Any?` *)
Definition read_mutability (v: Variance) (holder: Mutability) (o: Ownership) (m: Mutability): Mutability :=
    match v with
    | input => readonly
    | Model.invariant | output => element_mutability holder o m
    end.

(* Whether a value can be written through a view: nothing but Nothing is assignable to an out-variant
   type argument, and Nothing is never instantiated (the axiom that panic never returns) *)
Definition can_store_through (v: Variance) (holder: Mutability) (o: Ownership) (m: Mutability) (value: Value): bool :=
    match v with
    | output => false
    | Model.invariant | input => can_store holder o m value
    end.

Lemma mutability_beq_eq: forall a b, Mutability_beq a b = true -> a = b.
Proof. intros [] [] H; simpl in H; congruence. Qed.

(*
 * The actual slot of an object, of ownership o_actual and type mutability m_actual, viewed through a
 * type argument of variance v, ownership o and type mutability m: reading through the view gives no
 * more than the actual slot does, and writing through the view takes no more than the actual slot
 * takes. The ownership rule, the variance rule and the validity of the actual slot are separate
 * premises.
 *)
Theorem no_conflicts_through_a_view: forall holder v o_actual m_actual o m,
    ownership_is_assignable_to o_actual o = true ->
    mutability_conforms v m_actual m = true ->
    valid_slot o_actual m_actual = true ->
    is_subtype_of (element_mutability holder o_actual m_actual) (read_mutability v holder o m) = true
    /\ forall value, can_store_through v holder o m value = true -> can_store holder o_actual m_actual value = true.
Proof.
    intros holder v o_actual m_actual o m Ho Hv Hvalid. split.
    - destruct o, o_actual; simpl in Ho; try discriminate Ho;
        destruct v, holder, m_actual, m; vm_compute in Hv, Hvalid |- *; first [reflexivity|discriminate].
    - intros value H. destruct v; simpl in H; try discriminate H;
        unfold can_store in *; apply andb_true_iff in H; destruct H as [Hh Hvalue]; rewrite Hh; simpl;
        destruct value as [w|q]; destruct o, o_actual; simpl in Ho, Hvalue |- *; try discriminate Ho; try discriminate Hvalue;
        first
            [ destruct w, m_actual, m; vm_compute in Hv, Hvalid, Hvalue |- *; first [reflexivity|discriminate]
            | apply param_eqb_eq in Ho; apply param_eqb_eq in Hvalue; subst; apply param_eqb_refl ].
Qed.

(* All three are needed. Without the variance rule: a ref mut slot viewed as ref read, invariantly,
   would take readonly values the actual slot doesn't *)
Example the_variance_rule_is_needed:
    can_store_through Model.invariant mutable ref readonly (plain readonly) = true
    /\ can_store mutable ref mutable (plain readonly) = false.
Proof. split; reflexivity. Qed.

(* Without the ownership rule: a ref mut slot viewed as owned would give exclusive elements through
   an exclusive holder, where the actual slot only gives mutable ones *)
Example the_ownership_rule_is_needed:
    read_mutability Model.invariant exclusive owned mutable = exclusive
    /\ element_mutability exclusive ref mutable = mutable.
Proof. split; reflexivity. Qed.

(* Without the validity of the slot: an owned exclusive slot, viewed covariantly as owned const, would
   claim immutable elements, which a mutable holder mutates *)
Example the_validity_rule_is_needed:
    mutability_conforms output exclusive immutable = true
    /\ read_mutability output mutable owned immutable = immutable
    /\ element_mutability mutable owned exclusive = mutable.
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The same, for types                                                                             *)
(* ---------------------------------------------------------------------------------------------- *)

Section Types.

Variable env: Environment.

(* unify rejects type arguments whose ownership isn't assignable, before it looks at their types *)
Theorem unify_rejects_unassignable_ownership: forall fuel v v' o o' t t' states,
    ownership_is_assignable_to o' o = false ->
    unify env (S fuel) (TypeArgument v o t) (TypeArgument v' o' t') (Ongoing states) = Some Failed.
Proof.
    intros fuel v v' o o' t t' states H. unfold unify, unify_step, unify_type_argument.
    cbn -[ownership_is_assignable_to]. rewrite H. reflexivity.
Qed.

(* unify enforces variance_is_assignable_to: it rejects every other pair of variances outright, before
   looking at the types. (Where it accepts the variances, it unifies the types in the directions of
   mutability_conforms: both ways for invariant, covariantly for out, contravariantly for in.) *)
Theorem unify_rejects_unassignable_variances: forall fuel v v' o o' t t' states,
    ownership_is_assignable_to o' o = true ->
    variance_is_assignable_to v' v = false ->
    unify env (S fuel) (TypeArgument v o t) (TypeArgument v' o' t') (Ongoing states) = Some Failed.
Proof.
    intros fuel v v' o o' t t' states Ho Hv. unfold unify, unify_step, unify_type_argument.
    cbn -[ownership_is_assignable_to]. rewrite Ho. destruct v, v'; simpl in Hv; try discriminate Hv; reflexivity.
Qed.

(* A target with any ownership accepts whatever the target with the assignee's own ownership
   accepts: nothing an argument is assignable to stops being so with any ownership instead *)
Theorem any_ownership_accepts_what_owned_accepts: forall fuel v v' t t' carry,
    unify env (S fuel) (TypeArgument v any_ownership t) (TypeArgument v' owned t') carry
    = unify env (S fuel) (TypeArgument v owned t) (TypeArgument v' owned t') carry.
Proof. intros fuel v v' t t' []; [|reflexivity]. destruct v, v'; reflexivity. Qed.

Theorem any_ownership_accepts_what_ref_accepts: forall fuel v v' t t' carry,
    unify env (S fuel) (TypeArgument v any_ownership t) (TypeArgument v' ref t') carry
    = unify env (S fuel) (TypeArgument v ref t) (TypeArgument v' ref t') carry.
Proof. intros fuel v v' t t' []; [|reflexivity]. destruct v, v'; reflexivity. Qed.

Theorem any_ownership_accepts_what_the_parameter_accepts: forall fuel v v' p t t' carry,
    unify env (S fuel) (TypeArgument v any_ownership t) (TypeArgument v' (parameter_ownership p) t') carry
    = unify env (S fuel) (TypeArgument v (parameter_ownership p) t) (TypeArgument v' (parameter_ownership p) t') carry.
Proof.
    intros fuel v v' p t t' []; [|reflexivity]. unfold unify, unify_step, unify_type_argument.
    cbn -[ownership_is_assignable_to]. replace (ownership_is_assignable_to _ (parameter_ownership p)) with true.
    - reflexivity.
    - symmetry. apply param_eqb_refl.
Qed.

(* A type parameter is assignable to itself *)
Lemma generic_unifies_with_itself: forall fuel g states,
    unify env (S fuel) (Generic g) (Generic g) (Ongoing states) = Some (Ongoing states).
Proof.
    intros fuel [gm p b] states. simpl. unfold param_eqb. rewrite Nat.eqb_refl, mutability_is_subtype_of_refl.
    reflexivity.
Qed.

(* `Array<o T>` assignable to `Array<target_o T>`, for any class Array, any mutability of the array
   and any variance; the ownerships given as a condition *)
Lemma array_assignability: forall fuel m c v o target_o g,
    3 <= fuel ->
    ownership_is_assignable_to o target_o = true ->
    is_assignable_to env fuel
        (RootResolved m c [TypeArgument v o (Generic g)])
        (RootResolved m c [TypeArgument v target_o (Generic g)])
    = Some true.
Proof.
    intros fuel m c v o target_o g Hfuel Ho. destruct fuel as [|[|[|fuel]]]; try lia.
    unfold is_assignable_to. simpl. unfold unify_root_resolved, base_type_is_subtype_of.
    rewrite class_eqb_refl, mutability_is_subtype_of_refl. simpl.
    destruct (class_eqb c nothing); [reflexivity|]. unfold unify_arguments. simpl.
    unfold unify, unify_step, unify_type_argument. cbn -[ownership_is_assignable_to unify_generic].
    rewrite Ho. destruct g as [gm p b].
    destruct o, v; cbn -[ownership_is_assignable_to];
        try unfold param_eqb; rewrite ?Nat.eqb_refl, ?mutability_is_subtype_of_refl; cbn;
        rewrite ?Nat.eqb_refl, ?mutability_is_subtype_of_refl; reflexivity.
Qed.

Corollary owned_array_is_assignable_to_any_array: forall fuel m c v g,
    3 <= fuel ->
    is_assignable_to env fuel
        (RootResolved m c [TypeArgument v owned (Generic g)])
        (RootResolved m c [TypeArgument v any_ownership (Generic g)])
    = Some true.
Proof. intros. apply array_assignability; [assumption|reflexivity]. Qed.

Corollary ref_array_is_assignable_to_any_array: forall fuel m c v g,
    3 <= fuel ->
    is_assignable_to env fuel
        (RootResolved m c [TypeArgument v ref (Generic g)])
        (RootResolved m c [TypeArgument v any_ownership (Generic g)])
    = Some true.
Proof. intros. apply array_assignability; [assumption|reflexivity]. Qed.

Corollary array_is_assignable_to_any_array: forall fuel m c v p g,
    3 <= fuel ->
    is_assignable_to env fuel
        (RootResolved m c [TypeArgument v (parameter_ownership p) (Generic g)])
        (RootResolved m c [TypeArgument v any_ownership (Generic g)])
    = Some true.
Proof. intros. apply array_assignability; [assumption|reflexivity]. Qed.

Corollary array_is_assignable_to_itself: forall fuel m c v p g,
    3 <= fuel ->
    is_assignable_to env fuel
        (RootResolved m c [TypeArgument v (parameter_ownership p) (Generic g)])
        (RootResolved m c [TypeArgument v (parameter_ownership p) (Generic g)])
    = Some true.
Proof. intros. apply array_assignability; [assumption|apply param_eqb_refl]. Qed.

(* Array<owned T> and Array<ref T> aren't Array<T>: T might be instantiated with the other ownership.
   Nor is Array<T> one of them, or Array<any T> any of the others. *)
Corollary owned_and_ref_type_arguments_are_not_the_parameters: forall fuel v v' p t t' states o,
    o = owned \/ o = ref ->
    unify env (S fuel) (TypeArgument v (parameter_ownership p) t) (TypeArgument v' o t') (Ongoing states) = Some Failed
    /\ unify env (S fuel) (TypeArgument v o t) (TypeArgument v' (parameter_ownership p) t') (Ongoing states) = Some Failed.
Proof.
    intros fuel v v' p t t' states o Ho.
    split; apply unify_rejects_unassignable_ownership; destruct Ho as [->| ->]; reflexivity.
Qed.

Corollary any_type_arguments_are_nothing_else: forall fuel v v' t t' states o,
    o <> any_ownership ->
    unify env (S fuel) (TypeArgument v o t) (TypeArgument v' any_ownership t') (Ongoing states) = Some Failed.
Proof.
    intros fuel v v' t t' states o Ho. apply unify_rejects_unassignable_ownership.
    destruct o; try reflexivity. contradiction.
Qed.

Corollary owned_and_ref_are_unrelated: forall fuel v v' t t' states,
    unify env (S fuel) (TypeArgument v owned t) (TypeArgument v' ref t') (Ongoing states) = Some Failed
    /\ unify env (S fuel) (TypeArgument v ref t) (TypeArgument v' owned t') (Ongoing states) = Some Failed.
Proof. intros. split; apply unify_rejects_unassignable_ownership; reflexivity. Qed.

Corollary different_type_parameters_are_unrelated: forall fuel v v' p p' t t' states,
    p <> p' ->
    unify env (S fuel) (TypeArgument v (parameter_ownership p) t) (TypeArgument v' (parameter_ownership p') t') (Ongoing states) = Some Failed.
Proof.
    intros fuel v v' p p' t t' states Hp. apply unify_rejects_unassignable_ownership. simpl.
    destruct (param_eqb p p') eqn:E; [|reflexivity]. apply param_eqb_eq in E. congruence.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiation                                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma ownership_is_assignable_to_itself: forall o, ownership_is_assignable_to o o = true.
Proof. intros []; try reflexivity. apply param_eqb_refl. Qed.

(* The ownership of a type parameter becomes that of its type argument... *)
Lemma instantiating_a_bound_parameter_ownership: forall bindings p v o t,
    lookup_binding bindings p = Some (TypeArgument v o t) ->
    instantiate_ownership bindings (parameter_ownership p) = o.
Proof. intros bindings p v o t H. unfold instantiate_ownership. rewrite H. reflexivity. Qed.

(* ... the weakest of all, without one... *)
Lemma instantiating_an_unbound_parameter_ownership: forall bindings p,
    lookup_binding bindings p = None ->
    instantiate_ownership bindings (parameter_ownership p) = any_ownership.
Proof. intros bindings p H. unfold instantiate_ownership. rewrite H. reflexivity. Qed.

(* ... and explicit ownership stays as it is *)
Lemma instantiation_keeps_explicit_ownership: forall bindings o,
    (forall p, o <> parameter_ownership p) -> instantiate_ownership bindings o = o.
Proof. intros bindings [] H; try reflexivity. exfalso. apply (H param). reflexivity. Qed.

(* Instantiation keeps ownerships assignable: the ownership half of the substitution lemma *)
Theorem instantiation_preserves_ownership_assignability: forall bindings o_sub o_super,
    ownership_is_assignable_to o_sub o_super = true ->
    ownership_is_assignable_to (instantiate_ownership bindings o_sub) (instantiate_ownership bindings o_super) = true.
Proof.
    intros bindings o_sub o_super H.
    destruct o_super, o_sub; simpl in H; try discriminate H; try reflexivity.
    apply param_eqb_eq in H. subst. apply ownership_is_assignable_to_itself.
Qed.

Lemma class_eqb_false: forall a b, a <> b -> class_eqb a b = false.
Proof. intros a b H. unfold class_eqb. destruct (Class_eq_dec a b); [contradiction|reflexivity]. Qed.

(* A class `sub` with the type parameter T only, which has `super<os T>` as a supertype: as a
   supertype of `sub<o X>` (X a class without type arguments), that is `super<os' X>`, os' being os
   instantiated with T bound to `o X` *)
Lemma supertype_arguments_of_a_single_parameter_class: forall sub super T bound ms os o mt ct,
    map param_id (type_parameters (declaration_of env sub)) = [T] ->
    parameterized_supertype env sub super = RootResolved ms super [TypeArgument Model.invariant os (Generic (mkGenericRef None T bound))] ->
    parameterized_supertype_arguments env sub [TypeArgument Model.invariant o (RootResolved mt ct [])] super
    = [TypeArgument Model.invariant
        (instantiate_ownership [(T, TypeArgument Model.invariant o (RootResolved mt ct []))] os)
        (RootResolved mt ct [])].
Proof.
    intros sub super T bound ms os o mt ct Hparams Hsuper.
    unfold parameterized_supertype_arguments, bindings_of. rewrite Hsuper, Hparams. simpl.
    rewrite param_eqb_refl. reflexivity.
Qed.

(* `class OwnedList<T> : List<owned T>`: ownership declared explicitly in the supertype stays *)
Corollary explicit_ownership_of_supertype_arguments_stays: forall sub super T bound ms o mt ct,
    map param_id (type_parameters (declaration_of env sub)) = [T] ->
    parameterized_supertype env sub super = RootResolved ms super [TypeArgument Model.invariant owned (Generic (mkGenericRef None T bound))] ->
    parameterized_supertype_arguments env sub [TypeArgument Model.invariant o (RootResolved mt ct [])] super
    = [TypeArgument Model.invariant owned (RootResolved mt ct [])].
Proof. intros. erewrite supertype_arguments_of_a_single_parameter_class by eassumption. reflexivity. Qed.

(* `class MyList<T> : List<T>`: the ownership of the type argument carries over *)
Corollary ownership_of_type_arguments_carries_over_to_supertypes: forall sub super T bound ms o mt ct,
    map param_id (type_parameters (declaration_of env sub)) = [T] ->
    parameterized_supertype env sub super = RootResolved ms super [TypeArgument Model.invariant (parameter_ownership T) (Generic (mkGenericRef None T bound))] ->
    parameterized_supertype_arguments env sub [TypeArgument Model.invariant o (RootResolved mt ct [])] super
    = [TypeArgument Model.invariant o (RootResolved mt ct [])].
Proof.
    intros. erewrite supertype_arguments_of_a_single_parameter_class by eassumption.
    simpl. rewrite param_eqb_refl. reflexivity.
Qed.

(* A class type without type arguments is assignable to itself, as a type argument, too *)
Lemma class_type_argument_unifies_with_itself: forall fuel v o mt ct states,
    unify env (S (S fuel)) (TypeArgument v o (RootResolved mt ct [])) (TypeArgument v o (RootResolved mt ct [])) (Ongoing states)
    = Some (Ongoing states).
Proof.
    intros fuel v o mt ct states. unfold unify, unify_step, unify_type_argument.
    cbn -[ownership_is_assignable_to unify_root_resolved].
    rewrite ownership_is_assignable_to_itself.
    destruct o, v; cbn -[unify_root_resolved]; unfold unify_root_resolved, base_type_is_subtype_of;
        rewrite ?class_eqb_refl, ?mutability_is_subtype_of_refl; cbn;
        destruct (class_eqb ct nothing); reflexivity.
Qed.

(* one step of unify, without unfolding the recursive calls *)
Lemma unify_step_once: forall fuel target assignee states,
    unify env (S fuel) target assignee (Ongoing states) = unify_step env (unify env fuel) target assignee states.
Proof. reflexivity. Qed.

(* End to end: with `class MyList<T> : List<T>`, `MyList<o X>` is assignable to `List<o X>`, for every
   ownership o *)
Theorem subclass_is_assignable_with_the_same_ownership: forall fuel m sub super T bound ms o mt ct,
    3 <= fuel -> sub <> super -> sub <> nothing ->
    base_type_is_subtype_of env sub super = true ->
    is_core_scalar (declaration_of env sub) = is_core_scalar (declaration_of env super) ->
    map param_id (type_parameters (declaration_of env sub)) = [T] ->
    parameterized_supertype env sub super = RootResolved ms super [TypeArgument Model.invariant (parameter_ownership T) (Generic (mkGenericRef None T bound))] ->
    is_assignable_to env fuel
        (RootResolved m sub [TypeArgument Model.invariant o (RootResolved mt ct [])])
        (RootResolved m super [TypeArgument Model.invariant o (RootResolved mt ct [])])
    = Some true.
Proof.
    intros fuel m sub super T bound ms o mt ct Hfuel Hne Hnothing Hsub Hscalar Hparams Hsuper.
    destruct fuel as [|[|[|fuel]]]; try lia.
    unfold is_assignable_to, empty_unification. rewrite unify_step_once.
    unfold unify_step, unify_root_resolved. cbn beta iota.
    rewrite Hsub. cbn [mutability_of]. rewrite Hscalar, mutability_is_subtype_of_refl. cbn [negb].
    rewrite (class_eqb_false _ _ Hnothing), (class_eqb_false _ _ Hne).
    rewrite (ownership_of_type_arguments_carries_over_to_supertypes sub super T bound ms o mt ct Hparams Hsuper).
    unfold unify_arguments. cbn [fold_unify combine].
    rewrite class_type_argument_unifies_with_itself. reflexivity.
Qed.

(* ... and not to `List<o' X>` for an ownership o' that o isn't assignable to *)
Theorem subclass_keeps_the_ownership_apart: forall fuel m sub super T bound ms o o' mt ct,
    3 <= fuel -> sub <> super -> sub <> nothing ->
    base_type_is_subtype_of env sub super = true ->
    is_core_scalar (declaration_of env sub) = is_core_scalar (declaration_of env super) ->
    map param_id (type_parameters (declaration_of env sub)) = [T] ->
    parameterized_supertype env sub super = RootResolved ms super [TypeArgument Model.invariant (parameter_ownership T) (Generic (mkGenericRef None T bound))] ->
    ownership_is_assignable_to o o' = false ->
    is_assignable_to env fuel
        (RootResolved m sub [TypeArgument Model.invariant o (RootResolved mt ct [])])
        (RootResolved m super [TypeArgument Model.invariant o' (RootResolved mt ct [])])
    = Some false.
Proof.
    intros fuel m sub super T bound ms o o' mt ct Hfuel Hne Hnothing Hsub Hscalar Hparams Hsuper Ho.
    destruct fuel as [|[|[|fuel]]]; try lia.
    unfold is_assignable_to, empty_unification. rewrite unify_step_once.
    unfold unify_step, unify_root_resolved. cbn beta iota.
    rewrite Hsub. cbn [mutability_of]. rewrite Hscalar, mutability_is_subtype_of_refl. cbn [negb].
    rewrite (class_eqb_false _ _ Hnothing), (class_eqb_false _ _ Hne).
    rewrite (ownership_of_type_arguments_carries_over_to_supertypes sub super T bound ms o mt ct Hparams Hsuper).
    unfold unify_arguments. cbn [fold_unify combine].
    rewrite unify_rejects_unassignable_ownership by exact Ho. reflexivity.
Qed.

End Types.
