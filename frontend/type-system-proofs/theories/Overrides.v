From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import WithinBounds.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Overriding member functions                                                                    *)
(*                                                                                                *)
(* A call of a member function of class c is checked against its declaration in c. At run time,   *)
(* the object is of a class e below c, and dynamic dispatch runs the function e declares for it,  *)
(* where e overrides it. BoundDeclaredBaseTypeMemberFunction.findOverriddenFunctions takes a      *)
(* function of e for an override only where its parameter types are those of the function of c,   *)
(* with the type parameters of c bound to its type arguments as a supertype of e; its return type *)
(* must be assignable to that of c, so bound, and its declared receiver take that of c, so bound, *)
(* intersected with the receiver e implies. This shows that what the call is checked against      *)
(* holds of the override, with the type parameters of e bound to the type arguments of the        *)
(* object:                                                                                        *)
(* - an argument that fits the parameter of c, its type parameters bound to the type arguments of *)
(*   the object as c, fits that of the override (override_parameter, by instantiate_compose);     *)
(* - what the override returns fits the return type of c, so bound (override_return);             *)
(* - the object fits the declared receiver of the override (override_receiver).                   *)
(* The types are those the parameters of member functions have here: class types and references   *)
(* to the type parameters of c as written, nullable or as type arguments (composable). Kotlin     *)
(* can't override a function with type parameters of its own: theirs are never the same.          *)
(*                                                                                                *)
(* That dispatch finds a function at all is taken for granted; the model has no dispatch. A class *)
(* overrides every function it inherits, or a mixin provides it: BoundBaseType wraps each         *)
(* inherited function no function of the class overrides in a PossiblyMixedInBoundMemberFunction, *)
(* which reports AbstractInheritedFunctionNotImplementedDiagnostic in semanticAnalysisPhase3      *)
(* where no mixin is assigned to it. A mixin forwards the call to its object, whose type          *)
(* BoundMixinStatement checks to be assignable to the supertype it implements: that is a member   *)
(* call, too.                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Section Overrides.

Variable env: Environment.
Hypothesis wf: wellformed env.

(* Bindings to type arguments that aren't loose, whose types aren't type arguments *)
Definition exact_values (b: Bindings): Prop :=
    forall p a, lookup_binding b p = Some a -> is_loose a = false
        /\ exists o y, a = TypeArgument invariant o y /\ nests_argument y = false.

Lemma exact_not_loose: forall b, exact_values b -> forall p a, lookup_binding b p = Some a -> is_loose a = false.
Proof. intros b H p a E. exact (proj1 (H p a E)). Qed.

(* An ownership of a type parameter bound in b *)
Definition owner_bound (b: Bindings) (o: Ownership): Prop :=
    forall q, o = parameter_ownership q -> exists a, lookup_binding b q = Some a.

(* The types instantiating twice composes for: class types, references to type parameters bound in b
   as written (no mutability or `!` of their own), those nullable, and type arguments of those *)
Fixpoint composable (b: Bindings) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc =>
        match a with TypeArgument _ o n => owner_bound b o /\ composable b n | _ => False end /\ acc) True arguments
    | Nullable n => composable b n /\ match n with RootResolved _ _ _ | Generic _ => True | _ => False end
    | Generic (mkGenericRef None false p _) => exists a, lookup_binding b p = Some a
    | Error _ _ => True
    | _ => False
    end.

Lemma composable_transfer: forall b b', (forall p a, lookup_binding b p = Some a -> exists a', lookup_binding b' p = Some a') ->
    forall t, composable b t -> composable b' t.
Proof.
    intros b b' Hb. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; cbn [composable] in H |- *; try exact H; try contradiction.
    - induction args as [|a args IHa]; [exact I|]. cbn [fold_right] in H |- *. destruct H as [Ha Has]. split; [|exact (IHa Has)].
      destruct a as [| | | |v o n| |]; try contradiction. destruct Ha as [Ho Hn]. split; [|exact (IH n Hn)].
      intros q Eq. destruct (Ho q Eq) as [a Ha]. exact (Hb q a Ha).
    - destruct H as [Hn Hs]. split; [exact (IH n Hn)|exact Hs].
    - destruct gm as [m|], nn; simpl in H |- *; try contradiction. destruct H as [a Ha]. exact (Hb p a Ha).
Qed.

Lemma rewrap_idem: forall t, rewrap_nullable (rewrap_nullable t) = rewrap_nullable t.
Proof. intros [| | | | | |]; reflexivity. Qed.

Lemma instantiate_rewrap: forall b t, instantiate env b (rewrap_nullable t) = rewrap_nullable (instantiate env b t).
Proof.
    intros b [m c args|n|g|me msg|v o n|g|cs]; try reflexivity.
    cbn [rewrap_nullable instantiate]. rewrite rewrap_idem. reflexivity.
Qed.

(* Instantiated with exact bindings, a composable type is no type argument *)
Lemma instance_not_nested: forall b, exact_values b -> forall t, composable b t -> nests_argument (instantiate env b t) = false.
Proof.
    intros b Hb.
    assert (Hval: forall p a, lookup_binding b p = Some a ->
        nests_argument (instantiate env b (Generic (mkGenericRef None false p []))) = false
        /\ forall vs, instantiate env b (Generic (mkGenericRef None false p vs))
            = instantiate env b (Generic (mkGenericRef None false p []))).
    { intros p a Ha. destruct (Hb p a Ha) as [Hl [o [y [-> Hy]]]]. split.
      - cbn [instantiate]. rewrite Ha. unfold final_argument. rewrite Hl, Hy. exact Hy.
      - intros vs. cbn [instantiate]. rewrite Ha. reflexivity. }
    intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; cbn [composable] in H; try contradiction.
    - reflexivity.
    - destruct H as [Hn Hs]. destruct n as [m c args|n'|[gm nn p vs]|me msg|v o n'|g|cs]; try contradiction; [reflexivity|].
      destruct gm as [m|], nn; simpl in Hn; try contradiction. destruct Hn as [a Ha].
      destruct (Hval p a Ha) as [Hy Hvs].
      change (nests_argument (rewrap_nullable (instantiate env b (Generic (mkGenericRef None false p vs)))) = false).
      rewrite Hvs. destruct (instantiate env b (Generic (mkGenericRef None false p []))) as [| y'| | | | |];
          try reflexivity; try discriminate Hy. exact Hy.
    - destruct gm as [m|], nn; simpl in H; try contradiction. destruct H as [a Ha].
      destruct (Hval p a Ha) as [Hy Hvs]. rewrite Hvs. exact Hy.
    - reflexivity.
Qed.

Lemma argument_plain: forall b v o y, exact_values b -> composable b y ->
    instantiate env b (TypeArgument v o y) = TypeArgument v (instantiate_ownership b o) (instantiate env b y).
Proof.
    intros b v o y Hb Hn. pose proof (instance_not_nested b Hb y Hn) as E.
    apply (instantiate_unloose_argument env b v o y (exact_not_loose b Hb)).
    - destruct (instantiate env b y) as [| | | | | |]; try reflexivity; discriminate E.
    - intros x Ex. rewrite Ex in E. destruct x; try reflexivity; discriminate E.
Qed.

(* The bindings bL are those of bS, instantiated with bx *)
Definition composes (bS bx bL: Bindings): Prop :=
    forall p a, lookup_binding bS p = Some a ->
        exists o y, a = TypeArgument invariant o y
            /\ lookup_binding bL p = Some (TypeArgument invariant (instantiate_ownership bx o) (instantiate env bx y)).

(*
 * Instantiating a composable type with bS and then with bx is instantiating it with bS instantiated
 * with bx: the bindings of the type parameters of c as a supertype of e, in terms of the type
 * parameters of e, then the bindings of those to the type arguments of the object.
 *)
Lemma instantiate_compose: forall bsuper bobject bcomposed, exact_values bsuper -> exact_values bobject -> exact_values bcomposed -> composes bsuper bobject bcomposed ->
    forall t, composable bsuper t -> instantiate env bobject (instantiate env bsuper t) = instantiate env bcomposed t.
Proof.
    intros bsuper bobject bcomposed HS Hx HL Hc.
    assert (Hown: forall o, owner_bound bsuper o -> instantiate_ownership bobject (instantiate_ownership bsuper o) = instantiate_ownership bcomposed o).
    { intros [| | |q] Ho; try reflexivity. destruct (Ho q eq_refl) as [a Ha]. destruct (Hc q a Ha) as [o [y [-> HLq]]].
      cbn [instantiate_ownership]. rewrite Ha, HLq. reflexivity. }
    assert (Htr: forall t, composable bsuper t -> composable bcomposed t).
    { apply composable_transfer. intros p a Ha. destruct (Hc p a Ha) as [o [y [_ HLp]]]. eexists. exact HLp. }
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; cbn [composable] in H; try contradiction.
    - cbn [instantiate]. f_equal. rewrite map_map. induction args as [|a args IHa]; [reflexivity|].
      cbn [fold_right] in H. destruct H as [Ha Has]. cbn [map]. f_equal; [|exact (IHa Has)].
      destruct a as [| | | |v o n| |]; try contradiction. destruct Ha as [Ho Hn].
      rewrite (argument_plain bsuper v o n HS Hn).
      assert (En: instantiate env bobject (instantiate env bsuper n) = instantiate env bcomposed n) by exact (IH n Hn).
      pose proof (instance_not_nested bcomposed HL n (Htr n Hn)) as Enn. rewrite <- En in Enn.
      rewrite (instantiate_unloose_argument env bobject v _ _ (exact_not_loose bobject Hx)).
      + rewrite En, (argument_plain bcomposed v o n HL (Htr n Hn)), (Hown o Ho). reflexivity.
      + destruct (instantiate env bobject (instantiate env bsuper n)) as [| | | | | |]; try reflexivity; discriminate Enn.
      + intros x Ex. rewrite Ex in Enn. destruct x; try reflexivity; discriminate Enn.
    - destruct H as [Hn _]. cbn [instantiate]. rewrite instantiate_rewrap, (IH n Hn). reflexivity.
    - destruct gm as [m|], nn; simpl in H; try contradiction. destruct H as [a Ha].
      destruct (HS p a Ha) as [Hl [o [y [-> Hy]]]]. destruct (Hc p _ Ha) as [o' [y' [E HLp]]]. injection E as <- <-.
      destruct (HL p _ HLp) as [HlL [oL [yL [EL HyL]]]]. injection EL as _ <-.
      cbn [instantiate]. rewrite Ha, HLp. unfold final_argument. rewrite Hl, Hy, HlL, HyL. reflexivity.
    - reflexivity.
Qed.

Lemma lookup_map_combine: forall (ps: list TypeParameterId) (ys: list EType) (f: EType -> EType) p,
    lookup_binding (combine ps (map f ys)) p = option_map f (lookup_binding (combine ps ys) p).
Proof.
    intros ps. induction ps as [|q ps IH]; intros [|x ys] f p; try reflexivity.
    cbn [map combine lookup_binding]. destruct (param_eqb p q); [reflexivity|apply IH].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A class e below c, an object of e                                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Section Classes.

Variables c sub: Class.
Hypothesis Hec: sub <> c.
Hypothesis He: sub <> nothing.
Hypothesis Hsub: base_type_is_subtype_of env sub c = true.
(* the type arguments of the object, exact *)
Variable xs: list EType.
Hypothesis Hlx: length xs = length (parameter_ids env sub).
Hypothesis Hxs: forall x, In x xs -> exact_argument env x = true.

(* The type parameters of c bound to its type arguments as a supertype of e, in terms of the type
   parameters of e (the inherent type bindings of the parameterized supertype); those of e bound to
   the type arguments of the object; those of c bound to the type arguments of the object as c *)
Definition super_bindings: Bindings := bindings_of env c (supertype_arguments env sub c).
Definition object_bindings: Bindings := bindings_of env sub xs.
Definition object_as_super: Bindings := bindings_of env c (parameterized_supertype_arguments env sub xs c).

Lemma object_exact: exact_values object_bindings.
Proof.
    intros p a Ha. pose proof (Hxs a (lookup_combine_in _ _ _ _ Ha)) as Ex.
    destruct a as [| | | |v o x| |]; try discriminate Ex. destruct v; try discriminate Ex.
    cbn [exact_argument] in Ex. apply andb_true_iff in Ex. destruct Ex as [Ho Hx]. split.
    - destruct o; try discriminate Ho; reflexivity.
    - exists o, x. split; [reflexivity|].
      destruct (fragment_cases env x Hx) as [[m [c' [args ->]]]|[m [c' [args [-> _]]]]]; reflexivity.
Qed.

Lemma object_binds: forall q, existsb (param_eqb q) (parameter_ids env sub) = true -> exists a, lookup_binding object_bindings q = Some a.
Proof.
    intros q E. apply existsb_exists in E. destruct E as [q' [Hq Eq]]. apply param_eqb_eq in Eq. subst q'.
    destruct (In_nth_error _ _ Hq) as [i Hi].
    assert (Hl: i < length xs) by (rewrite Hlx; apply nth_error_Some; rewrite Hi; discriminate).
    destruct (nth_error xs i) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    exists x. exact (lookup_parameter env wf sub xs i q x Hi Ex).
Qed.

(* A type in the type arguments of a supertype of e, in terms of the type parameters of e *)
Lemma template_composable: forall y, template_type env sub y = true -> composable object_bindings y.
Proof.
    fix IH 1. intros [m c' args|n|g|me msg|v o n|g|cs] H; cbn [template_type] in H; try discriminate H.
    - apply andb_true_iff in H. destruct H as [_ H]. cbn [composable].
      induction args as [|a args IHa]; [exact I|]. cbn [forallb] in H. apply andb_true_iff in H. destruct H as [Ha Has].
      cbn [fold_right]. split; [|exact (IHa Has)].
      destruct (template_parameter a) as [q|] eqn:Etp.
      + destruct a as [| | | |v o n| |]; try discriminate Etp. destruct v; try discriminate Etp.
        destruct o as [| | |q0]; try discriminate Etp. destruct n as [| |[gm nn q' vs]| | | |]; try discriminate Etp.
        destruct gm; try discriminate Etp. destruct nn; try discriminate Etp.
        cbn [template_parameter] in Etp. destruct (param_eqb q0 q') eqn:Eq; [|discriminate Etp].
        injection Etp as ->. apply param_eqb_eq in Eq. subst q'. split.
        * intros q' Eq. injection Eq as <-. exact (object_binds q Ha).
        * exact (object_binds q Ha).
      + destruct a as [| | | |v o n| |]; try discriminate Ha. apply andb_true_iff in Ha. destruct Ha as [Ho Hn].
        split; [intros q Eq; subst o; discriminate Ho|exact (IH n Hn)].
    - apply andb_true_iff in H. destruct H as [Hc Hn]. cbn [composable]. split; [exact (IH n Hn)|].
      destruct n; try discriminate Hc; exact I.
Qed.

(* The type arguments of c as a supertype of e: exact, of types composable with the object's *)
Lemma super_argument: forall p a, lookup_binding super_bindings p = Some a ->
    is_loose a = false /\ exists o y, a = TypeArgument invariant o y /\ nests_argument y = false
        /\ owner_bound object_bindings o /\ composable object_bindings y.
Proof.
    intros p a Ha. pose proof (lookup_combine_in _ _ _ _ Ha) as Hin.
    pose proof (wf_supertypes_are_exact env wf sub c a Hin) as Hex.
    destruct (wf_supertypes_are_templates env wf sub c Hec He Hsub) as [_ Htpl]. pose proof (Htpl a Hin) as Ht.
    destruct a as [| | | |v o y| |]; try discriminate Hex. destruct v; try discriminate Hex.
    unfold template_argument in Ht. destruct (template_parameter (TypeArgument invariant o y)) as [q|] eqn:Etp.
    - destruct o as [| | |q0]; try discriminate Etp. destruct y as [| |[gm nn q' vs]| | | |]; try discriminate Etp.
      destruct gm; try discriminate Etp. destruct nn; try discriminate Etp.
      cbn [template_parameter] in Etp. destruct (param_eqb q0 q') eqn:Eq; [|discriminate Etp].
      injection Etp as ->. apply param_eqb_eq in Eq. subst q'.
      split; [reflexivity|]. exists (parameter_ownership q), (Generic (mkGenericRef None false q vs)).
      split; [reflexivity|]. split; [reflexivity|]. split.
      + intros q' Eq. injection Eq as <-. exact (object_binds q Ht).
      + exact (object_binds q Ht).
    - apply andb_true_iff in Ht. destruct Ht as [Ho Hy]. split; [destruct o; try discriminate Hex; reflexivity|].
      exists o, y. split; [reflexivity|]. split.
      + destruct y as [| [| | | | | |] | | | | |]; try reflexivity; cbn [template_type is_class] in Hy; try discriminate Hy;
            apply andb_true_iff in Hy; destruct Hy as [Hy _]; discriminate Hy.
      + split; [intros q Eq; subst o; discriminate Ho|exact (template_composable y Hy)].
Qed.

Lemma super_exact: exact_values super_bindings.
Proof.
    intros p a Ha. destruct (super_argument p a Ha) as [Hl [o [y [-> [Hy _]]]]].
    split; [exact Hl|]. exists o, y. split; [reflexivity|exact Hy].
Qed.

(* The type arguments of the object as c are those of c as a supertype of e, instantiated *)
Lemma object_as_super_lookup: forall p,
    lookup_binding object_as_super p = option_map (instantiate env object_bindings) (lookup_binding super_bindings p).
Proof.
    intros p. unfold object_as_super, super_bindings, bindings_of.
    rewrite parameterized_supertype_arguments_eq. apply lookup_map_combine.
Qed.

Lemma super_composes: composes super_bindings object_bindings object_as_super.
Proof.
    intros p a Ha. destruct (super_argument p a Ha) as [_ [o [y [-> [_ [_ Hcy]]]]]].
    exists o, y. split; [reflexivity|]. rewrite object_as_super_lookup, Ha. cbn [option_map].
    rewrite (argument_plain object_bindings invariant o y object_exact Hcy). reflexivity.
Qed.

Lemma object_as_super_exact: exact_values object_as_super.
Proof.
    intros p a Ha. rewrite object_as_super_lookup in Ha.
    destruct (lookup_binding super_bindings p) as [s|] eqn:Es; [|discriminate Ha]. cbn [option_map] in Ha. injection Ha as <-.
    destruct (super_argument p s Es) as [Hl [o [y [-> [_ [Ho Hcy]]]]]].
    rewrite (argument_plain object_bindings invariant o y object_exact Hcy). split.
    - destruct o as [| | |q]; try reflexivity; [discriminate Hl|].
      destruct (Ho q eq_refl) as [a Ha]. cbn [instantiate_ownership]. rewrite Ha.
      destruct (object_exact q a Ha) as [Hla [oa [ya [-> _]]]]. exact Hla.
    - eexists. eexists. split; [reflexivity|]. exact (instance_not_nested object_bindings object_exact y Hcy).
Qed.

(*
 * The parameter type of the override is that of the function of c, its type parameters bound as
 * a supertype of e (findOverriddenFunctions). With the type parameters of e bound to the type
 * arguments of the object, it is that of c with its type parameters bound to those as c: what an
 * argument is checked against. So whatever argument the call takes, the override takes.
 *)
Theorem override_parameter: forall P, composable super_bindings P ->
    instantiate env object_bindings (instantiate env super_bindings P) = instantiate env object_as_super P.
Proof.
    exact (instantiate_compose super_bindings object_bindings object_as_super super_exact object_exact
        object_as_super_exact super_composes).
Qed.

(* The type arguments of the object are of the fragment of Transitivity.v *)
Lemma object_in_fragment: bindings_in_fragment env object_bindings.
Proof.
    intros p o x Ha. pose proof (Hxs _ (lookup_combine_in _ _ _ _ Ha)) as Ex.
    cbn [exact_argument] in Ex. apply andb_true_iff in Ex. exact (proj2 Ex).
Qed.

(*
 * The return type of the override is assignable to that of the function of c, its type parameters
 * bound as a supertype of e, in the generic code of e (IncompatibleReturnTypeOnOverrideDiagnostic).
 * Where the type arguments of the object are within the bounds of the type parameters of e, as
 * Kotlin checks type arguments, what the override returns, with the type parameters of e bound to
 * them, is assignable to what the call expects: the return type of c, its type parameters bound to
 * the type arguments of the object as c.
 *)
Theorem override_return: forall V0 V1 fuel,
    (forall p, In p (parameter_ids env sub) -> exists o x, lookup_binding object_bindings p = Some (TypeArgument invariant o x)
        /\ is_exact_ownership o = true
        /\ exists n, unify env n (inst_nested env object_bindings (parameter_bound env p)) x (Ongoing []) = Some (Ongoing [])) ->
    (forall p, In p (parameter_ids env sub) ->
        tfrag env (parameter_bound env p) = true /\ mentions_only env (parameter_ids env sub) (parameter_bound env p)) ->
    composable super_bindings V0 -> tfrag env (instantiate env super_bindings V0) = true -> sfrag env V1 = true ->
    mentions_only env (parameter_ids env sub) (instantiate env super_bindings V0) -> mentions_only env (parameter_ids env sub) V1 ->
    is_assignable_to env fuel V1 (instantiate env super_bindings V0) = Some true ->
    exists n, is_assignable_to env n (instantiate env object_bindings V1) (instantiate env object_as_super V0) = Some true.
Proof.
    intros V0 V1 fuel Hwithin Hdeclared HR HtR HsRe HmR HmRe H.
    pose proof (bound_in_derived env wf object_bindings object_in_fragment (parameter_bound env) (parameter_ids env sub)
        Hwithin (fun p Hp => conj (proj1 (Hdeclared p Hp)) (conj I (proj2 (Hdeclared p Hp)))) (fun p => eq_refl)) as Hder.
    destruct (Hder _ I HmR) as [K1 HK1]. destruct (Hder _ I HmRe) as [K2 HK2].
    set (E := 2 + list_max (map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) xs)).
    assert (HE: forall p o x, lookup_binding object_bindings p = Some (TypeArgument invariant o x) -> depth x <= E).
    { intros p o x Ha. pose proof (lookup_combine_in _ _ _ _ Ha) as Hin.
      assert (Hm: Forall (fun k => k <= list_max (map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) xs))
          (map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) xs)) by (apply list_max_le; lia).
      rewrite Forall_forall in Hm. specialize (Hm _ (in_map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) _ _ Hin)).
      unfold E. lia. }
    pose proof (substitution_lemma env wf object_bindings (max K1 K2) E fuel _ _ ltac:(unfold E; lia) HE object_in_fragment
        HtR HsRe (bound_in_mono env wf object_bindings K1 _ _ (Nat.le_max_l _ _) HK1)
        (bound_in_mono env wf object_bindings K2 _ _ (Nat.le_max_r _ _) HK2) H) as Hs.
    rewrite (override_parameter V0 HR) in Hs. eexists. exact Hs.
Qed.

(* The object, a reference to e with its exact type arguments *)
Lemma object_in_fragment_type: forall mo, in_fragment env (RootResolved mo sub xs) = true.
Proof.
    intros mo. change (Nat.eqb (length xs) (length (parameter_ids env sub)) && forallb (argument_in_fragment env) xs = true).
    rewrite Hlx, Nat.eqb_refl. apply forallb_forall. intros x Hx. pose proof (Hxs x Hx) as Ex.
    destruct x as [| | | |v o n| |]; try discriminate Ex. destruct v; try discriminate Ex.
    cbn [exact_argument] in Ex. apply andb_true_iff in Ex. exact (proj2 Ex).
Qed.

(* What each of the receivers of the override and of c take, in turn, the object takes: the receiver
   of the override, its type parameters bound to the type arguments of the object *)
Lemma sfrag_class_mutability: forall m0 m1 c0 args,
    sfrag env (with_mutability env m0 (RootResolved m1 c0 args)) = sfrag env (RootResolved m1 c0 args).
Proof.
    intros m0 m1 c0 args. rewrite !(sfrag_top env). cbn [with_mutability sfrag_h]. reflexivity.
Qed.

(*
 * The declared receiver of the override takes the receiver of c, its type parameters bound as a
 * supertype of e, intersected with the receiver e implies (the class with its type parameters), in
 * the generic code of e. Kotlin builds that intersection with BoundIntersectionTypeReference.intersect:
 * ofComponents, simplified; this takes it as ofComponents builds it. Where the object fits the
 * receiver of c, as c (as the call is checked), and the receiver e implies, it fits the declared
 * receiver of the override, its type parameters bound to the type arguments of the object.
 *)
Theorem override_receiver: forall msuper sargs minst iargs mdecl dargs mo fuel n0 n1,
    (forall p, In p (parameter_ids env sub) -> exists o x, lookup_binding object_bindings p = Some (TypeArgument invariant o x)
        /\ is_exact_ownership o = true
        /\ exists n', unify env n' (inst_nested env object_bindings (parameter_bound env p)) x (Ongoing []) = Some (Ongoing [])) ->
    (forall p, In p (parameter_ids env sub) ->
        tfrag env (parameter_bound env p) = true /\ mentions_only env (parameter_ids env sub) (parameter_bound env p)) ->
    c <> nothing ->
    composable super_bindings (RootResolved msuper c sargs) ->
    sfrag env (instantiate env super_bindings (RootResolved msuper c sargs)) = true -> sfrag env (RootResolved minst sub iargs) = true ->
    sfrag env (RootResolved mdecl sub dargs) = true ->
    mentions_only env (parameter_ids env sub) (instantiate env super_bindings (RootResolved msuper c sargs)) ->
    mentions_only env (parameter_ids env sub) (RootResolved minst sub iargs) ->
    mentions_only env (parameter_ids env sub) (RootResolved mdecl sub dargs) ->
    is_assignable_to env fuel
        (of_components env [instantiate env super_bindings (RootResolved msuper c sargs); RootResolved minst sub iargs])
        (RootResolved mdecl sub dargs) = Some true ->
    is_assignable_to env n0 (RootResolved mo sub xs) (instantiate env object_as_super (RootResolved msuper c sargs)) = Some true ->
    is_assignable_to env n1 (RootResolved mo sub xs) (instantiate env object_bindings (RootResolved minst sub iargs)) = Some true ->
    exists n', is_assignable_to env n' (RootResolved mo sub xs) (instantiate env object_bindings (RootResolved mdecl sub dargs)) = Some true.
Proof.
    intros msuper sargs minst iargs mdecl dargs mo fuel n0 n1 Hwithin Hdeclared Hc HcS HsA HsI HsD HmA HmI HmD H H0 H1.
    set (A := instantiate env super_bindings (RootResolved msuper c sargs)) in *.
    set (Imp := RootResolved minst sub iargs) in *. set (D := RootResolved mdecl sub dargs) in *.
    assert (EA: A = RootResolved msuper c (map (instantiate env super_bindings) sargs)) by reflexivity.
    set (m := common_mutability env [A; Imp]).
    assert (Eo: of_components env [A; Imp] = Intersection [with_mutability env m A; with_mutability env m Imp]).
    { rewrite (of_components_many env [A; Imp]); [|simpl; lia|rewrite EA; reflexivity]. rewrite EA. reflexivity. }
    rewrite Eo in H.
    (* the component of the intersection the declared receiver takes *)
    unfold is_assignable_to, empty_unification in H.
    destruct (unify env fuel D (Intersection [with_mutability env m A; with_mutability env m Imp]) (Ongoing [])) as [[u|]|] eqn:Eu;
        try discriminate H.
    destruct fuel as [|f']; [discriminate Eu|]. rewrite unify_step_once in Eu. unfold D in Eu.
    cbn [unify_step unify_root_resolved] in Eu. unfold intersection_flipped_unify in Eu.
    destruct (find_first (fun component => unify env f' (RootResolved mdecl sub dargs) component (Ongoing []))
        [with_mutability env m A; with_mutability env m Imp]) as [[[X u']|]|] eqn:Ef; cbn beta iota in Eu; try discriminate Eu.
    destruct (find_first_found _ _ _ _ Ef) as [HX EX].
    (* the type arguments of the object within the bounds of the type parameters of e *)
    pose proof (bound_in_derived env wf object_bindings object_in_fragment (parameter_bound env) (parameter_ids env sub)
        Hwithin (fun p Hp => conj (proj1 (Hdeclared p Hp)) (conj I (proj2 (Hdeclared p Hp)))) (fun p => eq_refl)) as Hder.
    (* the object, below either of the receivers, instantiated, and assigned as no more than m *)
    unfold is_assignable_to, empty_unification in H0, H1.
    destruct (unify env n0 (instantiate env object_as_super (RootResolved msuper c sargs)) (RootResolved mo sub xs) (Ongoing []))
        as [[w0|]|] eqn:E0; try discriminate H0.
    destruct (unify env n1 (instantiate env object_bindings Imp) (RootResolved mo sub xs) (Ongoing [])) as [[w1|]|] eqn:E1;
        try discriminate H1.
    rewrite <- (override_parameter _ HcS) in E0. fold A in E0.
    destruct (Hder _ I HmA) as [KA HKA]. destruct (Hder _ I HmI) as [KI HKI]. destruct (Hder _ I HmD) as [KD HKD].
    pose proof (sfrag_tfrag env _ HsA) as HtA. pose proof (sfrag_tfrag env _ HsI) as HtI. pose proof (sfrag_tfrag env _ HsD) as HtD.
    pose proof (instance_in_fragment env wf object_bindings KA [] object_in_fragment A HsA HKA) as HfA.
    pose proof (instance_in_fragment env wf object_bindings KI [] object_in_fragment Imp HsI HKI) as HfI.
    pose proof (instance_in_fragment env wf object_bindings KD [] object_in_fragment D HsD HKD) as HfD.
    rewrite (inst_nested_instantiate env wf object_bindings KA [] A HtA HKA) in HfA.
    rewrite (inst_nested_instantiate env wf object_bindings KI [] Imp HtI HKI) in HfI.
    rewrite (inst_nested_instantiate env wf object_bindings KD [] D HtD HKD) in HfD.
    pose proof (object_in_fragment_type mo) as Hfo.
    assert (Hm: Model.is_subtype_of (assignment_mutability env (RootResolved mo sub xs)) m = true).
    { apply Ops.fold_intersect_greatest; [apply Ops.mutability_subtype_of_readonly|].
      intros k Hk. cbn [map In] in Hk. destruct Hk as [<-|[<-|[]]].
      - pose proof (accepted_mutability_classes env n0 _ _ [] w0 HfA Hfo E0) as Ek.
        rewrite EA in Ek |- *. cbn [instantiate] in Ek. exact Ek.
      - pose proof (accepted_mutability_classes env n1 _ _ [] w1 HfI Hfo E1) as Ek. exact Ek. }
    (* the component, instantiated, takes the object; and the declared receiver, instantiated, takes it *)
    assert (Hcomp: forall Y Ky, In Y [A; Imp] -> sfrag env Y = true -> bound_in env object_bindings Ky [] Y = true ->
        in_fragment env (instantiate env object_bindings Y) = true ->
        (exists n, unify env n (instantiate env object_bindings Y) (RootResolved mo sub xs) (Ongoing []) = Some (Ongoing [])) ->
        unify env f' D (with_mutability env m Y) (Ongoing []) = Some (Ongoing u') ->
        exists n', is_assignable_to env n' (RootResolved mo sub xs) (instantiate env object_bindings D) = Some true).
    { intros Y Ky HY HsY HbY HfY [nY EY] EDY.
      assert (EYs: exists my cy yargs, Y = RootResolved my cy yargs /\ cy <> nothing).
      { destruct HY as [<-|[<-|[]]]; [rewrite EA|]; eexists; eexists; eexists; split; try reflexivity; [exact Hc|exact He]. }
      destruct EYs as [my [cy [yargs [-> Hcy]]]].
      assert (HsYm: sfrag env (with_mutability env m (RootResolved my cy yargs)) = true) by (rewrite sfrag_class_mutability; assumption).
      assert (HbYm: bound_in env object_bindings Ky [] (with_mutability env m (RootResolved my cy yargs)) = true) by exact HbY.
      assert (Hs: is_assignable_to env (f' * S (S (max Ky KD)) + (2 + list_max (map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) xs)))
          (instantiate env object_bindings (with_mutability env m (RootResolved my cy yargs))) (instantiate env object_bindings D) = Some true).
      { apply (substitution_lemma env wf object_bindings (max Ky KD) _ f'); [lia| |exact object_in_fragment|exact HtD|exact HsYm| | |].
        - intros p o x Ha. pose proof (lookup_combine_in _ _ _ _ Ha) as Hin.
          assert (Hl: Forall (fun k => k <= list_max (map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) xs))
              (map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) xs)) by (apply list_max_le; lia).
          rewrite Forall_forall in Hl. specialize (Hl _ (in_map (fun a => match a with TypeArgument _ _ x => depth x | _ => 0 end) _ _ Hin)).
          cbn beta iota in Hl. lia.
        - exact (bound_in_mono env wf object_bindings KD _ _ (Nat.le_max_r _ _) HKD).
        - exact (bound_in_mono env wf object_bindings Ky _ _ (Nat.le_max_l _ _) HbYm).
        - unfold is_assignable_to, empty_unification. rewrite EDY. reflexivity. }
      assert (EYi: instantiate env object_bindings (with_mutability env m (RootResolved my cy yargs))
          = with_mutability env m (instantiate env object_bindings (RootResolved my cy yargs))) by reflexivity.
      rewrite EYi in Hs.
      assert (HfYm: in_fragment env (with_mutability env m (instantiate env object_bindings (RootResolved my cy yargs))) = true)
          by exact HfY.
      pose proof (accepts_with_mutability env nY m _ _ [] [] HfY Hfo Hm EY) as EYm.
      assert (A1: is_assignable_to env nY (RootResolved mo sub xs) (with_mutability env m (instantiate env object_bindings (RootResolved my cy yargs))) = Some true)
          by (unfold is_assignable_to, empty_unification; rewrite EYm; reflexivity).
      eexists. exact (Transitivity.transitivity env wf _ _ _ _ _ Hfo HfYm HfD A1 Hs). }
    destruct HX as [<-|[<-|[]]].
    - apply (Hcomp A KA (or_introl eq_refl) HsA HKA HfA); [|exact EX].
      exists n0. rewrite E0. destruct (keeps_free env wf n0 _ _ [] w0 (in_fragment_no_vars env _ HfA) (in_fragment_no_vars env _ Hfo) E0) as [-> _]. reflexivity.
    - apply (Hcomp Imp KI (or_intror (or_introl eq_refl)) HsI HKI HfI); [|exact EX].
      exists n1. rewrite E1. destruct (keeps_free env wf n1 _ _ [] w1 (in_fragment_no_vars env _ HfI) (in_fragment_no_vars env _ Hfo) E1) as [-> _]. reflexivity.
Qed.

End Classes.

End Overrides.
