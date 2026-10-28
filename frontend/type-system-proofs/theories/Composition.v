From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import SubstitutionWide.
From EmergeTypeSystem Require Import WithinBounds.
From EmergeTypeSystem Require Import GenericArguments.
From EmergeTypeSystem Require Import GenericCode.
From EmergeTypeSystem Require Import GenericReceivers.
From EmergeTypeSystem Require Import Overrides.
From EmergeTypeSystem Require Import MemberAccess.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating twice                                                                            *)
(*                                                                                                *)
(* A reference C<ys> in generic code has type arguments ys mentioning the type parameters ps of the *)
(* code; at run time, those are bound (sigma, within their declared bounds, as in GenericReceivers.v), *)
(* and the reference is a C<sigma ys>. A member of C, of a type f as MemberAccess.member_type has   *)
(* it, is read and written through C<ys> as f instantiated with ys; at run time, as f instantiated  *)
(* with sigma ys. This shows the two agree: f instantiated with ys and then with sigma is f         *)
(* instantiated with sigma ys (compose_member), for type arguments of any variance, the type        *)
(* parameters of C of any mutability given to them or narrowed in f. The same goes for an override: *)
(* the types of the overridden function, instantiated with the supertype arguments of the class of  *)
(* the override and then with the type arguments of the object, are those instantiated with the    *)
(* supertype arguments instantiated, as the call has them.                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Section Composition.

Variable env: Environment.
Hypothesis wf: wellformed env.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.

(* The conjectures of Conjectures.v *)
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis tame: tame_inheritance env.

(* The type parameters of the code, and what they are bound to at run time *)
Variable ps: list TypeParameterId.
Variable sigma: Bindings.
Hypothesis Hsf: bindings_in_fragment env sigma.
Hypothesis Hwithin: forall p, In p ps -> exists o x, lookup_binding sigma p = Some (TypeArgument Model.invariant o x)
    /\ is_exact_ownership o = true
    /\ exists f, unify env f (inst_nested env sigma (declared p)) x (Ongoing []) = Some (Ongoing []).
Hypothesis Hdeclared: forall p, In p ps -> tfrag env (declared p) = true /\ built env declared (declared p)
    /\ mentions_only env ps (declared p).

Let caller := caller_type env declared ps.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating with sigma                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma sig_caller: forall t, caller t -> ground env (instantiate env sigma t) = true
    /\ mentions_loosely_bound sigma t = false /\ mentions_loosely_bound_in_arguments sigma t = false
    /\ nests_argument (instantiate env sigma t) = false.
Proof.
    intros t Ht. destruct (instance_ground env wf declared declared_wf ps sigma Hsf Hwithin Hdeclared t Ht)
        as [K [HK Hg]].
    destruct (wide_instance env wf sigma K Hsf t (proj1 Ht) HK) as [_ [H1 [H2 [H3 _]]]]. auto.
Qed.

(* A type in an instance that sigma takes into type arguments as it is *)
Definition good (X: EType): Prop :=
    nests_argument X = false /\ mentions_loosely_bound sigma X = false
    /\ mentions_loosely_bound_in_arguments sigma X = false /\ nests_argument (instantiate env sigma X) = false.

Lemma good_caller: forall t, caller t -> good t.
Proof.
    intros t Ht. destruct (sig_caller t Ht) as [_ [H1 [H2 H3]]].
    split; [exact (caller_not_nested env declared ps t Ht)|auto].
Qed.

Lemma sig_rewrap: forall Y, instantiate env sigma (rewrap_nullable Y) = rewrap_nullable (instantiate env sigma Y).
Proof. exact (instantiate_rewrap env sigma). Qed.

Lemma good_rewrap: forall Z, good Z -> good (rewrap_nullable Z).
Proof.
    intros Z [H0 [H1 [H2 H3]]].
    assert (Hn: forall t, nests_argument t = false -> nests_argument (rewrap_nullable t) = false).
    { intros [| [] | | | | |] E; first [reflexivity|discriminate E]. }
    split; [exact (Hn Z H0)|]. rewrite sig_rewrap. split; [|split; [|exact (Hn _ H3)]].
    - destruct Z; first [exact H1|exact H1].
    - destruct Z; exact H2.
Qed.

Lemma sig_argument: forall v o X, is_parameter_ownership o = false -> good X ->
    instantiate env sigma (TypeArgument v o X) = TypeArgument v o (instantiate env sigma X).
Proof.
    intros v o X Ho [_ [_ [Hin Hn]]]. cbn [instantiate]. rewrite Hin.
    assert (Eo: instantiate_ownership sigma o = o) by (destruct o; first [reflexivity|discriminate Ho]). rewrite Eo.
    destruct (instantiate env sigma X) as [| [] | | | | |]; try discriminate Hn; reflexivity.
Qed.

Lemma sig_top: instantiate env sigma top_type = top_type.
Proof. reflexivity. Qed.

Lemma sig_bottom: instantiate env sigma bottom_type = bottom_type.
Proof. reflexivity. Qed.

Lemma good_closed: forall m c, good (RootResolved m c []).
Proof. intros m c. repeat split. Qed.

Lemma good_top: good top_type.
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Type arguments                                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

(* What instantiate makes of a type argument, by the instance of its type *)
Definition arg_of (w: Variance) (o': Ownership) (N: EType) (loose: bool): EType :=
    let is_nullable_instantiated := match N with Nullable _ => true | _ => false end in
    let n_non_null := match N with Nullable x => x | _ => N end in
    match n_non_null with
    | TypeArgument nested_variance _ nested_type =>
        if Variance_beq nested_variance Model.invariant || Variance_beq w Model.invariant || Variance_beq nested_variance w then
            TypeArgument (if Variance_beq nested_variance Model.invariant then w else nested_variance) o'
                (if is_nullable_instantiated then rewrap_nullable nested_type else nested_type)
        else
            match w with
            | output => TypeArgument output o' top_type
            | _ => TypeArgument input o' bottom_type
            end
    | _ =>
        if loose then
            match w with
            | input => TypeArgument input o' bottom_type
            | Model.invariant | output => TypeArgument output o' (if is_nullable_instantiated then Nullable n_non_null else n_non_null)
            end
        else TypeArgument w o' (if is_nullable_instantiated then Nullable n_non_null else n_non_null)
    end.

Lemma instantiate_argument_of: forall b w o n,
    instantiate env b (TypeArgument w o n) = arg_of w (instantiate_ownership b o) (instantiate env b n) (mentions_loosely_bound_in_arguments b n).
Proof. reflexivity. Qed.

Lemma arg_of_plain: forall w o N loose, nests_argument N = false ->
    arg_of w o N loose = if loose then match w with input => TypeArgument input o bottom_type | _ => TypeArgument output o N end
        else TypeArgument w o N.
Proof. intros w o N loose H. destruct N as [| [] | | | | |]; try discriminate H; destruct loose, w; reflexivity. Qed.

(* The instance of the type of a type argument: one sigma takes as it is, or a type argument of one,
   made nullable or not; of Pr, which holds of top and bottom and is kept by making types nullable *)
Section Arguments.

Variable Pr: EType -> Prop.
Hypothesis Pr_rewrap: forall Z, Pr Z -> Pr (rewrap_nullable Z).
Hypothesis Pr_top: Pr top_type.
Hypothesis Pr_bottom: Pr bottom_type.

Definition good_arg (N: EType): Prop :=
    (good N /\ Pr N)
    \/ exists v o Z, (N = TypeArgument v o Z \/ N = Nullable (TypeArgument v o Z)) /\ good Z /\ Pr Z /\ is_parameter_ownership o = false.

Lemma sig_arg_of: forall w o N loose, is_parameter_ownership o = false -> good_arg N ->
    instantiate env sigma (arg_of w o N loose) = arg_of w o (instantiate env sigma N) loose
    /\ exists w' X, arg_of w o N loose = TypeArgument w' o X /\ good X /\ Pr X.
Proof.
    intros w o N loose Ho [[HN HPN]|[v [o' [Z [[-> | ->] [HZ [HPZ Ho']]]]]]].
    - rewrite (arg_of_plain w o N loose (proj1 HN)), (arg_of_plain w o _ loose (proj2 (proj2 (proj2 HN)))).
      destruct loose; [destruct w|];
          (split; [|eexists; eexists; split; [reflexivity|first [exact (conj HN HPN)|exact (conj (good_closed _ _) Pr_bottom)]]]);
          rewrite sig_argument; first [exact Ho|exact HN|exact (good_closed _ _)|reflexivity].
    - rewrite (sig_argument v o' Z Ho' HZ). pose proof (proj2 (proj2 (proj2 HZ))) as HnZ.
      assert (E: forall Y, arg_of w o (TypeArgument v o' Y) loose
          = if Variance_beq v Model.invariant || Variance_beq w Model.invariant || Variance_beq v w
            then TypeArgument (if Variance_beq v Model.invariant then w else v) o Y
            else match w with output => TypeArgument output o top_type | _ => TypeArgument input o bottom_type end)
          by (intros Y; reflexivity).
      rewrite (E Z), (E _).
      destruct (Variance_beq v Model.invariant || Variance_beq w Model.invariant || Variance_beq v w);
          [|destruct w; (split; [rewrite sig_argument; first [exact Ho|exact good_top|exact (good_closed _ _)|reflexivity]|
                                 eexists; eexists; split; [reflexivity|first [exact (conj good_top Pr_top)|exact (conj (good_closed _ _) Pr_bottom)]]])].
      split; [rewrite (sig_argument _ o Z Ho HZ); reflexivity|eexists; eexists; split; [reflexivity|exact (conj HZ HPZ)]].
    - pose proof (good_rewrap Z HZ) as HrZ.
      change (instantiate env sigma (Nullable (TypeArgument v o' Z))) with (rewrap_nullable (instantiate env sigma (TypeArgument v o' Z))).
      rewrite (sig_argument v o' Z Ho' HZ). cbn [rewrap_nullable].
      assert (E: forall Y, arg_of w o (Nullable (TypeArgument v o' Y)) loose
          = if Variance_beq v Model.invariant || Variance_beq w Model.invariant || Variance_beq v w
            then TypeArgument (if Variance_beq v Model.invariant then w else v) o (rewrap_nullable Y)
            else match w with output => TypeArgument output o top_type | _ => TypeArgument input o bottom_type end)
          by (intros Y; reflexivity).
      rewrite (E Z), (E _).
      destruct (Variance_beq v Model.invariant || Variance_beq w Model.invariant || Variance_beq v w);
          [|destruct w; (split; [rewrite sig_argument; first [exact Ho|exact good_top|exact (good_closed _ _)|reflexivity]|
                                 eexists; eexists; split; [reflexivity|first [exact (conj good_top Pr_top)|exact (conj (good_closed _ _) Pr_bottom)]]])].
      split; [rewrite (sig_argument _ o _ Ho HrZ), sig_rewrap; reflexivity|eexists; eexists; split; [reflexivity|exact (conj HrZ (Pr_rewrap Z HPZ))]].
Qed.

End Arguments.

Lemma gfrag_not_nested: forall t, gfrag env t = true -> nests_argument t = false.
Proof.
    intros t H. destruct (gfrag_cases env t H) as [[? [? [? ->]]]|[[n [-> [_ Hn]]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; try reflexivity.
    destruct n; try reflexivity. discriminate Hn.
Qed.

(* A reference to a type parameter bound to a type argument: the type argument, of the mutability and
   nullability of the reference applied to its type *)
Lemma instance_ref_gen: forall b g v o A, lookup_binding b (param_of g) = Some (TypeArgument v o A) -> of_fragment env declared A ->
    instantiate env b (Generic g) = final_argument (TypeArgument v o (ref_apply env (given_mutability g) (is_narrowed g) A)).
Proof.
    intros b [gm nn p bp] v o A H HA. cbn [param_of given_mutability is_narrowed] in *.
    pose proof (gfrag_not_nested A (proj1 HA)) as Hn.
    pose proof (gfrag_not_nested _ (proj1 (ref_apply_of_fragment env wf declared declared_wf gm nn A HA))) as Hn'.
    cbn [instantiate]. rewrite H. unfold final_argument. rewrite Hn, Hn', !orb_false_r.
    change (is_loose (TypeArgument v o (ref_apply env gm nn A))) with (is_loose (TypeArgument v o A)).
    destruct (is_loose (TypeArgument v o A)); unfold ref_apply; destruct gm, nn; reflexivity.
Qed.

(* A class type of type arguments of types of generic code is one *)
Lemma caller_root_of: forall m d args, class_eqb d nothing = false -> length args = length (parameter_ids env d) ->
    (forall a, In a args -> exists w o X, a = TypeArgument w o X /\ caller X /\ is_parameter_ownership o = false) ->
    caller (RootResolved m d args).
Proof.
    intros m d args Hd Hl H. split; [|split; [exact I|]].
    - change (wfrag env (RootResolved m d args) = true). cbn [wfrag]. rewrite Hd, Hl, Nat.eqb_refl. cbn [andb].
      apply forallb_forall. intros a Ha. destruct (H a Ha) as [w [o [X [-> [[Hw _] _]]]]].
      destruct X as [| [] | | | | |]; unfold wtfrag in Hw; exact Hw.
    - cbn [mentions_only]. clear Hl Hd. induction args as [|a args IH]; [exact I|]. split.
      + destruct (H a (or_introl eq_refl)) as [w [o [X [-> [[_ [_ HmX]] Ho]]]]]. cbn [mentions_only].
        split; [intros q ->; discriminate Ho|exact HmX].
      + apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma good_root: forall m d args, (forall a, In a args -> exists w o X, a = TypeArgument w o X /\ good X) ->
    good (RootResolved m d args) /\ good (Nullable (RootResolved m d args)).
Proof.
    intros m d args H.
    assert (E: existsb (mentions_loosely_bound sigma) args = false).
    { apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [a [Ha Ea]].
      destruct (H a Ha) as [w [o [X [-> [_ [HX _]]]]]]. cbn [mentions_loosely_bound] in Ea. rewrite HX in Ea. discriminate Ea. }
    split; (split; [reflexivity|]); cbn [mentions_loosely_bound mentions_loosely_bound_in_arguments];
        (split; [exact E|]); (split; [exact E|reflexivity]).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The members of a reference in generic code                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Section Member.

Variables (c: Class) (ys: list EType).
Hypothesis Hly: length ys = length (parameter_ids env c).
Hypothesis Hys: forall y, In y ys -> exists v o Y, y = TypeArgument v o Y /\ caller Y /\ of_fragment env declared Y
    /\ is_parameter_ownership o = false.

Lemma lookup_sig: forall p, lookup_binding (bindings_of env c (map (instantiate env sigma) ys)) p
    = option_map (instantiate env sigma) (lookup_binding (bindings_of env c ys) p).
Proof. intros p. unfold bindings_of. apply lookup_map_combine. Qed.

Lemma lookup_value: forall p a, lookup_binding (bindings_of env c ys) p = Some a ->
    exists v o Y, a = TypeArgument v o Y /\ caller Y /\ of_fragment env declared Y /\ is_parameter_ownership o = false
        /\ lookup_binding (bindings_of env c (map (instantiate env sigma) ys)) p = Some (TypeArgument v o (instantiate env sigma Y)).
Proof.
    intros p a H. pose proof H as H'. unfold bindings_of in H'. destruct (lookup_combine_nth _ ys p a H') as [i [_ Ei]].
    destruct (Hys a (nth_error_In _ _ Ei)) as [v [o [Y [-> [HY [HfY Ho]]]]]].
    exists v, o, Y. split; [reflexivity|]. split; [exact HY|]. split; [exact HfY|]. split; [exact Ho|].
    rewrite lookup_sig, H. cbn [option_map]. rewrite (sig_argument v o Y Ho (good_caller Y HY)). reflexivity.
Qed.

Lemma own_same: forall o, instantiate_ownership (bindings_of env c (map (instantiate env sigma) ys)) o
    = instantiate_ownership (bindings_of env c ys) o.
Proof.
    intros [| | |q]; try reflexivity. cbn [instantiate_ownership].
    destruct (lookup_binding (bindings_of env c ys) q) as [a|] eqn:E.
    - destruct (lookup_value q a E) as [v [o [Y [-> [_ [_ [_ E']]]]]]]. rewrite E'. reflexivity.
    - rewrite lookup_sig, E. reflexivity.
Qed.

Lemma loose_lookup: forall p,
    match lookup_binding (bindings_of env c (map (instantiate env sigma) ys)) p with Some a => is_loose a | None => false end
    = match lookup_binding (bindings_of env c ys) p with Some a => is_loose a | None => false end.
Proof.
    intros p. destruct (lookup_binding (bindings_of env c ys) p) as [a|] eqn:E.
    - destruct (lookup_value p a E) as [v [o [Y [-> [_ [_ [_ E']]]]]]]. rewrite E'. reflexivity.
    - rewrite lookup_sig, E. reflexivity.
Qed.

Lemma loose_same: forall t, mentions_loosely_bound (bindings_of env c (map (instantiate env sigma) ys)) t
    = mentions_loosely_bound (bindings_of env c ys) t.
Proof.
    fix IH 1. intros [m d args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; cbn [mentions_loosely_bound].
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb]. rewrite (IH a), IHa. reflexivity.
    - exact (IH n).
    - exact (loose_lookup p).
    - reflexivity.
    - exact (IH n).
    - exact (loose_lookup p).
    - induction cs as [|c' cs IHc]; [reflexivity|]. cbn [existsb]. rewrite (IH c'), IHc. reflexivity.
Qed.

Lemma in_args_same: forall t, mentions_loosely_bound_in_arguments (bindings_of env c (map (instantiate env sigma) ys)) t
    = mentions_loosely_bound_in_arguments (bindings_of env c ys) t.
Proof.
    fix IH 1. intros [m d args|n|g|me msg|v o n|g|cs]; cbn [mentions_loosely_bound_in_arguments]; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. cbn [existsb]. rewrite (loose_same a), IHa. reflexivity.
    - exact (IH n).
    - induction cs as [|c' cs IHc]; [reflexivity|]. cbn [existsb]. rewrite (IH c'), IHc. reflexivity.
Qed.

Let Pr_rewrap := caller_rewrap env declared ps.
Let Pr_top := caller_top env wf declared ps.
Let Pr_bottom := caller_bottom env declared ps.

(* A type parameter of the class, of any mutability given to it or narrowed *)
Lemma leaf_compose: forall g, existsb (param_eqb (param_of g)) (parameter_ids env c) = true ->
    instantiate env sigma (instantiate env (bindings_of env c ys) (Generic g))
        = instantiate env (bindings_of env c (map (instantiate env sigma) ys)) (Generic g)
    /\ good_arg caller (instantiate env (bindings_of env c ys) (Generic g)).
Proof.
    intros g Hg. destruct (member_parameter env c (param_of g) Hg) as [i Hi].
    destruct (nth_error_same_length _ ys i _ (eq_sym Hly) Hi) as [y Ey].
    pose proof (lookup_parameter env wf c ys i (param_of g) y Hi Ey) as Ly.
    destruct (lookup_value _ _ Ly) as [v [o [Y [-> [HY [HfY [Ho Ly']]]]]]].
    destruct (sig_caller Y HY) as [GY _].
    assert (HfsY: of_fragment env declared (instantiate env sigma Y)) by exact (ground_of_fragment env declared _ GY).
    rewrite (instance_ref_gen _ g v o Y Ly HfY), (instance_ref_gen _ g v o _ Ly' HfsY).
    set (gm := given_mutability g). set (nn := is_narrowed g).
    pose proof (caller_ref_apply env wf declared ps gm nn Y HY) as HcR.
    pose proof (instance_ref_apply env wf declared declared_wf terminates finite tame ps sigma Hsf Hwithin Hdeclared gm nn Y HfY HY) as ER.
    pose proof (gfrag_not_nested _ (proj1 (ref_apply_of_fragment env wf declared declared_wf gm nn Y HfY))) as Hn1.
    pose proof (gfrag_not_nested _ (proj1 (ref_apply_of_fragment env wf declared declared_wf gm nn _ HfsY))) as Hn2.
    unfold final_argument. rewrite Hn1, Hn2, !orb_false_r.
    change (is_loose (TypeArgument v o (ref_apply env gm nn (instantiate env sigma Y))))
        with (is_loose (TypeArgument v o (ref_apply env gm nn Y))).
    destruct (is_loose (TypeArgument v o (ref_apply env gm nn Y))).
    - rewrite (sig_argument v o _ Ho (good_caller _ HcR)), ER. split; [reflexivity|].
      right. exists v, o, (ref_apply env gm nn Y). split; [left; reflexivity|].
      split; [exact (good_caller _ HcR)|]. split; [exact HcR|exact Ho].
    - split; [exact ER|]. left. split; [exact (good_caller _ HcR)|exact HcR].
Qed.

Lemma nullable_leaf_compose: forall g, existsb (param_eqb (param_of g)) (parameter_ids env c) = true ->
    instantiate env sigma (instantiate env (bindings_of env c ys) (Nullable (Generic g)))
        = instantiate env (bindings_of env c (map (instantiate env sigma) ys)) (Nullable (Generic g))
    /\ good_arg caller (instantiate env (bindings_of env c ys) (Nullable (Generic g))).
Proof.
    intros g Hg. destruct (leaf_compose g Hg) as [E HN].
    change (instantiate env (bindings_of env c ys) (Nullable (Generic g)))
        with (rewrap_nullable (instantiate env (bindings_of env c ys) (Generic g))).
    change (instantiate env (bindings_of env c (map (instantiate env sigma) ys)) (Nullable (Generic g)))
        with (rewrap_nullable (instantiate env (bindings_of env c (map (instantiate env sigma) ys)) (Generic g))).
    rewrite sig_rewrap, E. split; [reflexivity|].
    destruct HN as [[HN HPN]|[v [o [Z [[-> | ->] HZ]]]]].
    - left. split; [exact (good_rewrap _ HN)|exact (Pr_rewrap _ HPN)].
    - right. exists v, o, Z. split; [right; reflexivity|exact HZ].
    - right. exists v, o, Z. split; [right; reflexivity|exact HZ].
Qed.


Local Abbreviation bY := (bindings_of env c ys).
Local Abbreviation bS := (bindings_of env c (map (instantiate env sigma) ys)).

(* The ownership of a type argument, instantiated: none of a type parameter *)
Lemma own_not_parameter: forall o p, own_ownership o p = true -> existsb (param_eqb p) (parameter_ids env c) = true ->
    is_parameter_ownership (instantiate_ownership bY o) = false.
Proof.
    intros [| | |q] p Ho Hp; try reflexivity. cbn [own_ownership] in Ho. apply param_eqb_eq in Ho. subst q.
    destruct (member_parameter env c p Hp) as [i Hi].
    destruct (nth_error_same_length _ ys i _ (eq_sym Hly) Hi) as [y Ey].
    pose proof (lookup_parameter env wf c ys i p y Hi Ey) as Ly.
    destruct (lookup_value _ _ Ly) as [v [o [Y [-> [_ [_ [Ho _]]]]]]].
    cbn [instantiate_ownership]. rewrite Ly. exact Ho.
Qed.

(* The instances of member types, through C<ys> and then sigma, and through C<sigma ys> *)
Lemma compose_instances: forall k,
    (forall t, depth t <= k -> member_template env c t = true -> nothing_is_bottom t = true ->
        instantiate env sigma (instantiate env bY t) = instantiate env bS t
        /\ good (instantiate env bY t) /\ caller (instantiate env bY t))
    /\ (forall a, argument_depth a <= k -> member_argument env c a = true -> nothing_is_bottom a = true ->
        instantiate env sigma (instantiate env bY a) = instantiate env bS a
        /\ exists w o X, instantiate env bY a = TypeArgument w o X /\ good X /\ caller X /\ is_parameter_ownership o = false).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht. destruct (member_cases env c t Ht) as [[m [d [args ->]]]|[m [d [args [-> _]]]]]; simpl in Hd; lia.
      - intros a Hd Ha. destruct (member_argument_kind env c a Ha) as [w [o [n [-> _]]]]. simpl in Hd. lia. }
    assert (Hroot: forall m d args, depth (RootResolved m d args) <= S k -> member_template env c (RootResolved m d args) = true ->
        nothing_is_bottom (RootResolved m d args) = true ->
        instantiate env sigma (RootResolved m d (map (instantiate env bY) args)) = RootResolved m d (map (instantiate env bS) args)
        /\ good (RootResolved m d (map (instantiate env bY) args)) /\ good (Nullable (RootResolved m d (map (instantiate env bY) args)))
        /\ caller (RootResolved m d (map (instantiate env bY) args))).
    { intros m d args Hd Ht Hnb. destruct (member_root env c m d args Ht) as [Hl Hargs].
      cbn [nothing_is_bottom] in Hnb. apply andb_true_iff in Hnb. destruct Hnb as [Hnd Hnargs].
      assert (IH: forall a, In a args ->
          instantiate env sigma (instantiate env bY a) = instantiate env bS a
          /\ exists w o X, instantiate env bY a = TypeArgument w o X /\ good X /\ caller X /\ is_parameter_ownership o = false).
      { intros a Ha. apply IHa; [pose proof (argument_depth_below m d args a Ha); lia|exact (Hargs a Ha)|].
        exact (proj1 (forallb_forall _ args) Hnargs a Ha). }
      split.
      { cbn [instantiate]. f_equal. rewrite map_map. apply map_ext_in. intros a Ha. exact (proj1 (IH a Ha)). }
      assert (Hg: forall a', In a' (map (instantiate env bY) args) -> exists w o X, a' = TypeArgument w o X /\ good X).
      { intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        destruct (proj2 (IH a Ha)) as [w [o [X [E [HX _]]]]]. exists w, o, X. split; [exact E|exact HX]. }
      destruct (good_root m d _ Hg) as [G1 G2]. split; [exact G1|]. split; [exact G2|].
      destruct (class_eqb d nothing) eqn:En.
      - destruct m as [[]|], args; try discriminate Hnd. unfold class_eqb in En.
        destruct (Class_eq_dec d nothing) as [->|]; [|discriminate En]. exact (caller_bottom env declared ps).
      - apply caller_root_of; [exact En|rewrite length_map; exact Hl|].
        intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        destruct (proj2 (IH a Ha)) as [w [o [X [E [_ [HcX Ho]]]]]]. exists w, o, X. auto. }
    split.
    - intros t Hd Ht Hnb. destruct (member_cases env c t Ht) as [[m [d [args ->]]]|[m [d [args [-> Ht']]]]].
      + destruct (Hroot m d args Hd Ht Hnb) as [E [G _]]. split; [exact E|]. split; [exact G|]. apply Hroot; assumption.
      + rewrite depth_nullable in Hd. cbn [nothing_is_bottom] in Hnb.
        destruct (Hroot m d args ltac:(lia) Ht' Hnb) as [E [_ [G Hc]]].
        change (instantiate env bY (Nullable (RootResolved m d args))) with (Nullable (RootResolved m d (map (instantiate env bY) args))).
        change (instantiate env bS (Nullable (RootResolved m d args))) with (Nullable (RootResolved m d (map (instantiate env bS) args))).
        split; [change (rewrap_nullable (instantiate env sigma (RootResolved m d (map (instantiate env bY) args)))
                    = Nullable (RootResolved m d (map (instantiate env bS) args))); rewrite E; reflexivity|].
        split; [exact G|exact (Pr_rewrap _ Hc)].
    - intros a Hd Ha Hnb. destruct (member_argument_kind env c a Ha) as [w [o [n [-> [[p [Hn [Hp Ho]]]|[Hn [Ho Hnt]]]]]]].
      + (* a type parameter of the class, as it is or nullable, of any mutability given to it or narrowed *)
        destruct (leaf_cases n p Hn) as [g [nl [-> <-]]].
        assert (HN: instantiate env sigma (instantiate env bY (wrap_leaf nl (Generic g))) = instantiate env bS (wrap_leaf nl (Generic g))
            /\ good_arg caller (instantiate env bY (wrap_leaf nl (Generic g))))
            by (destruct nl; [exact (nullable_leaf_compose g Hp)|exact (leaf_compose g Hp)]).
        destruct HN as [EN GN].
        rewrite !instantiate_argument_of, own_same, in_args_same, <- EN.
        pose proof (own_not_parameter o (param_of g) Ho Hp) as Hop.
        destruct (sig_arg_of caller Pr_rewrap Pr_top Pr_bottom w _ _ (mentions_loosely_bound_in_arguments bY (wrap_leaf nl (Generic g))) Hop GN)
            as [E1 [w' [X [E2 [HX HcX]]]]].
        split; [exact E1|]. exists w', (instantiate_ownership bY o), X. auto.
      + (* a class type *)
        cbn [nothing_is_bottom] in Hnb. simpl in Hd.
        destruct (IHt n ltac:(lia) Hnt Hnb) as [EN [GN HcN]].
        rewrite !instantiate_argument_of, own_same, in_args_same, <- EN.
        assert (Eo: instantiate_ownership bY o = o) by (destruct o; first [reflexivity|discriminate Ho]). rewrite Eo.
        destruct (sig_arg_of caller Pr_rewrap Pr_top Pr_bottom w o _ (mentions_loosely_bound_in_arguments bY n) Ho (or_introl (conj GN HcN)))
            as [E1 [w' [X [E2 [HX HcX]]]]].
        split; [exact E1|]. exists w', o, X. auto.
Qed.

(* A member type, instantiated with ys and then with sigma, is instantiated with sigma ys *)
Lemma compose_member: forall f, member_type env c f = true -> nothing_is_bottom f = true ->
    instantiate env sigma (instantiate env bY f) = instantiate env bS f /\ good_arg caller (instantiate env bY f).
Proof.
    intros f Hf Hnb. unfold member_type in Hf. destruct (leaf_parameter f) as [p|] eqn:Hleaf.
    - destruct (leaf_cases f p Hleaf) as [g [[|] [-> <-]]]; [exact (nullable_leaf_compose g Hf)|exact (leaf_compose g Hf)].
    - destruct (proj1 (compose_instances (depth f)) f (le_n _) Hf Hnb) as [E [G Hc]].
      split; [exact E|left; exact (conj G Hc)].
Qed.

(* What read_member reads of an instance *)
Definition read_inst (t: EType): EType :=
    match t with
    | TypeArgument v _ x => read_type v x
    | Nullable (TypeArgument v _ x) => rewrap_nullable (read_type v x)
    | t => t
    end.

Lemma read_member_inst: forall b f, read_member env b f = read_inst (instantiate env b f).
Proof. intros b f. unfold read_member, read_inst. destruct (instantiate env b f) as [| [] | | | | |]; reflexivity. Qed.

Lemma read_inst_plain: forall t, nests_argument t = false -> read_inst t = t.
Proof. intros [| [] | | | | |] H; first [reflexivity|discriminate H]. Qed.

(* What is read through C<ys>, instantiated, is what is read through C<sigma ys> *)
Lemma compose_read: forall f, member_type env c f = true -> nothing_is_bottom f = true ->
    instantiate env sigma (read_member env bY f) = read_member env bS f.
Proof.
    intros f Hf Hnb. destruct (compose_member f Hf Hnb) as [E G]. rewrite !read_member_inst, <- E.
    destruct G as [[[Hn [_ [_ Hsn]]] _]|[v [o [Z [[-> | ->] [HZ [_ Ho]]]]]]].
    - rewrite (read_inst_plain _ Hn), (read_inst_plain _ Hsn). reflexivity.
    - rewrite (sig_argument v o Z Ho HZ). cbn [read_inst]. destruct v; reflexivity.
    - change (instantiate env sigma (Nullable (TypeArgument v o Z))) with (rewrap_nullable (instantiate env sigma (TypeArgument v o Z))).
      rewrite (sig_argument v o Z Ho HZ). cbn [read_inst rewrap_nullable]. rewrite sig_rewrap. destruct v; reflexivity.
Qed.

(* What is written through C<ys>, instantiated, is what is written through C<sigma ys> *)
Lemma compose_write: forall f, member_type env c f = true -> nothing_is_bottom f = true ->
    instantiate env sigma (write_member env bY f) = write_member env bS f.
Proof.
    intros f Hf Hnb. unfold write_member. rewrite in_args_same.
    destruct (mentions_loosely_bound_in_arguments bY f); [destruct f; reflexivity|].
    exact (proj1 (compose_member f Hf Hnb)).
Qed.


(* The instance of a member type through C<ys>: a type of generic code, or a type argument of one, made
   nullable or not *)
Lemma member_instance_cases: forall f, member_type env c f = true -> nothing_is_bottom f = true ->
    caller (instantiate env bY f)
    \/ exists v o Z, (instantiate env bY f = TypeArgument v o Z \/ instantiate env bY f = Nullable (TypeArgument v o Z))
        /\ caller Z /\ of_fragment env declared Z /\ is_parameter_ownership o = false.
Proof.
    intros f Hf Hnb. unfold member_type in Hf. destruct (leaf_parameter f) as [p|] eqn:Hleaf.
    - destruct (leaf_cases f p Hleaf) as [g [nl [-> <-]]].
      destruct (member_parameter env c (param_of g) Hf) as [i Hi].
      destruct (nth_error_same_length _ ys i _ (eq_sym Hly) Hi) as [y Ey].
      pose proof (lookup_parameter env wf c ys i (param_of g) y Hi Ey) as Ly.
      destruct (lookup_value _ _ Ly) as [v [o [Y [-> [HY [HfY [Ho _]]]]]]].
      set (gm := given_mutability g). set (nn := is_narrowed g).
      pose proof (caller_ref_apply env wf declared ps gm nn Y HY) as HcR.
      pose proof (ref_apply_of_fragment env wf declared declared_wf gm nn Y HfY) as HfR.
      assert (E: instantiate env bY (Generic g) = final_argument (TypeArgument v o (ref_apply env gm nn Y)))
          by exact (instance_ref_gen _ g v o Y Ly HfY).
      unfold final_argument in E. rewrite (gfrag_not_nested _ (proj1 HfR)), orb_false_r in E.
      destruct nl; cbn [wrap_leaf].
      + change (instantiate env bY (Nullable (Generic g))) with (rewrap_nullable (instantiate env bY (Generic g))). rewrite E.
        destruct (is_loose (TypeArgument v o (ref_apply env gm nn Y))).
        * right. exists v, o, (ref_apply env gm nn Y). split; [right; reflexivity|auto].
        * left. exact (Pr_rewrap _ HcR).
      + rewrite E. destruct (is_loose (TypeArgument v o (ref_apply env gm nn Y))).
        * right. exists v, o, (ref_apply env gm nn Y). split; [left; reflexivity|auto].
        * left. exact HcR.
    - left. exact (proj2 (proj2 (proj1 (compose_instances (depth f)) f (le_n _) Hf Hnb))).
Qed.

(* What is written through C<ys> in generic code, instantiated, is written through C<sigma ys> *)
Lemma write_preserved: forall f V0 fuel, member_type env c f = true -> nothing_is_bottom f = true ->
    caller V0 -> of_fragment env declared V0 -> is_non_nullable_nothing env V0 = false ->
    (is_non_nullable_nothing env (nullable_assignee env V0) = false \/ V0 = Nullable bottom_type) ->
    in_fragment env (instantiate env sigma V0) = true ->
    unify env fuel (write_member env bY f) V0 (Ongoing []) = Some (Ongoing []) ->
    exists f', unify env f' (write_member env bS f) (instantiate env sigma V0) (Ongoing []) = Some (Ongoing []).
Proof.
    intros f V0 fuel Hf Hnb HcV HfV HnV HnaV HinV H.
    assert (Hsub: forall W, caller W -> unify env fuel W V0 (Ongoing []) = Some (Ongoing []) ->
        exists f', unify env f' (instantiate env sigma W) (instantiate env sigma V0) (Ongoing []) = Some (Ongoing [])).
    { intros W HcW E. exact (subst_below env wf declared declared_wf terminates finite tame ps sigma Hsf Hwithin Hdeclared
          V0 W HcV HcW (ex_intro _ fuel E)). }
    rewrite <- (compose_write f Hf Hnb). unfold write_member in *.
    destruct (mentions_loosely_bound_in_arguments bY f).
    { apply Hsub; [|exact H]. destruct f; first [exact Pr_bottom|exact (Pr_rewrap _ Pr_bottom)]. }
    destruct (member_instance_cases f Hf Hnb) as [Hc|[v [o [Z [[EW|EW] [HcZ [HfZ Ho]]]]]]]; [exact (Hsub _ Hc H)| |];
        rewrite EW in H |- *.
    - (* a type argument: what it takes is below its type, unless it is out-variant *)
      rewrite (sig_argument v o Z Ho (good_caller Z HcZ)). destruct fuel as [|n]; [discriminate H|].
      destruct (Variance_beq v output) eqn:Ev.
      + rewrite (argument_takes_value env n v o Z V0 [] (proj1 HfV)), Ev, HnV in H. discriminate H.
      + pose proof (argument_value_below env wf declared declared_wf terminates finite tame n v o Z V0 Ev HfZ HfV H) as HB.
        destruct (subst_below env wf declared declared_wf terminates finite tame ps sigma Hsf Hwithin Hdeclared V0 Z HcV HcZ HB)
            as [f1 E1].
        exists (S f1). rewrite (unify_argument_value env f1 v o _ _ [] HinV), Ev. exact E1.
    - (* a type argument made nullable: what it takes without null is below its type, unless it is
         out-variant: then it takes null *)
      change (instantiate env sigma (Nullable (TypeArgument v o Z))) with (rewrap_nullable (instantiate env sigma (TypeArgument v o Z))).
      rewrite (sig_argument v o Z Ho (good_caller Z HcZ)). cbn [rewrap_nullable].
      destruct fuel as [|n]; [discriminate H|]. rewrite (nullable_target env n _ V0 [] (proj1 HfV)) in H.
      destruct (nullable_assignee_facts env wf declared declared_wf V0 (proj1 HfV)) as [HgA0 _].
      destruct n as [|n]; [discriminate H|].
      destruct (Variance_beq v output) eqn:Ev.
      + rewrite (argument_takes_value env n v o Z _ [] HgA0), Ev in H.
        destruct (is_non_nullable_nothing env (nullable_assignee env V0)) eqn:EA; [|discriminate H].
        destruct HnaV as [HnaV| ->]; [congruence|].
        exists 2. change (instantiate env sigma (Nullable bottom_type)) with (Nullable bottom_type).
        rewrite unify_nullable_nullable, (unify_argument_value env 0 v o _ bottom_type [] (bottom_in_fragment env wf)), Ev.
        reflexivity.
      + pose proof (argument_value_below env wf declared declared_wf terminates finite tame n v o Z _ Ev HfZ (conj HgA0 I) H) as HB.
        pose proof (caller_nullable_assignee env wf declared ps V0 (proj1 HfV) HcV) as HcA0.
        destruct (subst_below env wf declared declared_wf terminates finite tame ps sigma Hsf Hwithin Hdeclared _ Z HcA0 HcZ HB)
            as [f1 E1].
        destruct (sig_caller Z HcZ) as [GZ _]. destruct (sig_caller _ HcA0) as [GA0 _].
        pose proof (ground_assignee_without_null env f1 _ _ GZ GA0 E1) as E2.
        rewrite (instance_nullable_assignee env declared ps sigma Hsf Hwithin V0 (proj1 HfV) HcV) in E2.
        destruct (fragment_cases env _ HinV) as [[mv [cv [vargs Ev0]]]|[mv [cv [vargs [Ev0 _]]]]]; rewrite Ev0 in E2 |- *;
            cbn [without_null] in E2.
        * assert (HinR: in_fragment env (RootResolved mv cv vargs) = true) by (rewrite <- Ev0; exact HinV).
          exists (S (S f1)). rewrite unify_nullable_class, (unify_argument_value env f1 v o _ _ [] HinR), Ev.
          exact E2.
        * pose proof HinV as HinV'. rewrite Ev0 in HinV'.
          assert (Hr: in_fragment env (RootResolved mv cv vargs) = true)
              by (change (is_class (RootResolved mv cv vargs) && in_fragment env (RootResolved mv cv vargs) = true) in HinV';
                  apply andb_true_iff in HinV'; apply HinV').
          exists (S (S f1)). rewrite unify_nullable_nullable, (unify_argument_value env f1 v o _ _ [] Hr), Ev. exact E2.
Qed.

(*
 * Reading a member through a reference in generic code is sound: what the member of the object holds,
 * at run time, is assignable to what is read through the reference, instantiated.
 *)
Theorem generic_member_read_sound: forall n m xs m' f V fuel,
    c <> nothing -> length xs = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument env x = true) ->
    (forall y, In y (map (instantiate env sigma) ys) -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c (map (instantiate env sigma) ys)) (RootResolved m c xs) (Ongoing []) = Some (Ongoing []) ->
    member_type env c f = true -> nothing_is_bottom f = true ->
    in_fragment env V = true ->
    unify env fuel (read_member env (bindings_of env c xs) f) V (Ongoing []) = Some (Ongoing []) ->
    exists fuel', unify env fuel' (instantiate env sigma (read_member env bY f)) V (Ongoing []) = Some (Ongoing []).
Proof.
    intros n m xs m' f V fuel Hc Hlx Hxs Hys' H Hf Hnb HV HVx.
    rewrite (compose_read f Hf Hnb).
    exact (member_read_sound env wf n [] m c xs m' _ f V fuel Hc Hlx ltac:(rewrite length_map; exact Hly) Hxs Hys' H Hf HV HVx).
Qed.

(*
 * Writing a member through a reference in generic code is sound: what is assignable to the member
 * through the reference, instantiated, is assignable to the member of the object at run time; or
 * null, to a nullable member.
 *)
Theorem generic_member_write_sound: forall n m xs m' f V0 fuel,
    c <> nothing -> length xs = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument env x = true) ->
    (forall y, In y (map (instantiate env sigma) ys) -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c (map (instantiate env sigma) ys)) (RootResolved m c xs) (Ongoing []) = Some (Ongoing []) ->
    member_type env c f = true -> nothing_is_bottom f = true ->
    caller V0 -> of_fragment env declared V0 -> is_non_nullable_nothing env V0 = false ->
    (is_non_nullable_nothing env (nullable_assignee env V0) = false \/ V0 = Nullable bottom_type) ->
    in_fragment env (instantiate env sigma V0) = true -> is_non_nullable_nothing env (instantiate env sigma V0) = false ->
    unify env fuel (write_member env bY f) V0 (Ongoing []) = Some (Ongoing []) ->
    (exists fuel', unify env fuel' (read_member env (bindings_of env c xs) f) (instantiate env sigma V0) (Ongoing []) = Some (Ongoing []))
    \/ (holds_only_null env (instantiate env sigma V0) = true /\ is_nullable env (read_member env (bindings_of env c xs) f) = true).
Proof.
    intros n m xs m' f V0 fuel Hc Hlx Hxs Hys' H Hf Hnb HcV HfV HnV HnaV HinV HnsV HW.
    destruct (write_preserved f V0 fuel Hf Hnb HcV HfV HnV HnaV HinV HW) as [f' HW'].
    exact (member_write_sound env wf n [] m c xs m' _ f _ f' Hc Hlx ltac:(rewrite length_map; exact Hly) Hxs Hys' H Hf
        HinV HnsV HW').
Qed.


(* Of type arguments that aren't loose, as the supertype arguments of a class are, the instance of a
   member type is a type of generic code *)
Lemma member_instance_exact: forall f, (forall y, In y ys -> is_loose y = false) ->
    member_type env c f = true -> nothing_is_bottom f = true -> caller (instantiate env bY f).
Proof.
    intros f Hl Hf Hnb. unfold member_type in Hf. destruct (leaf_parameter f) as [p|] eqn:Hleaf.
    - destruct (leaf_cases f p Hleaf) as [g [nl [-> <-]]].
      destruct (member_parameter env c (param_of g) Hf) as [i Hi].
      destruct (nth_error_same_length _ ys i _ (eq_sym Hly) Hi) as [y Ey].
      pose proof (lookup_parameter env wf c ys i (param_of g) y Hi Ey) as Ly.
      pose proof (Hl y (nth_error_In _ _ Ey)) as Hly'.
      destruct (lookup_value _ _ Ly) as [v [o [Y [-> [HY [HfY [Ho _]]]]]]].
      set (gm := given_mutability g). set (nn := is_narrowed g).
      pose proof (caller_ref_apply env wf declared ps gm nn Y HY) as HcR.
      pose proof (ref_apply_of_fragment env wf declared declared_wf gm nn Y HfY) as HfR.
      assert (E: instantiate env bY (Generic g) = final_argument (TypeArgument v o (ref_apply env gm nn Y)))
          by exact (instance_ref_gen _ g v o Y Ly HfY).
      unfold final_argument in E. rewrite (gfrag_not_nested _ (proj1 HfR)), orb_false_r in E.
      change (is_loose (TypeArgument v o (ref_apply env gm nn Y))) with (is_loose (TypeArgument v o Y)) in E.
      rewrite Hly' in E. destruct nl; cbn [wrap_leaf].
      + change (instantiate env bY (Nullable (Generic g))) with (rewrap_nullable (instantiate env bY (Generic g))).
        rewrite E. exact (Pr_rewrap _ HcR).
      + rewrite E. exact HcR.
    - exact (proj2 (proj2 (proj1 (compose_instances (depth f)) f (le_n _) Hf Hnb))).
Qed.

(*
 * Overrides (Overrides.v, for types beyond plain references to type parameters): with c the class of
 * the overridden function, ys its supertype arguments as declared in the class e of the override,
 * mentioning the type parameters ps of e, and sigma the type arguments of the object, ys instantiated
 * with sigma are the type arguments c has as a supertype of the object (parameterized_supertype_arguments).
 *
 * The parameter type of the override is that of the function of c instantiated with ys
 * (findOverriddenFunctions); instantiated with sigma, it is that of c instantiated as the call has it
 * (compose_member). So whatever argument the call takes, the override takes.
 *)
Theorem override_parameter_composed: forall P, member_type env c P = true -> nothing_is_bottom P = true ->
    instantiate env sigma (instantiate env bY P) = instantiate env bS P.
Proof. intros P Hf Hnb. exact (proj1 (compose_member P Hf Hnb)). Qed.

(*
 * The return type of the override, Re, is assignable to that of the function of c instantiated with ys
 * (IncompatibleReturnTypeOnOverrideDiagnostic); instantiated with sigma, what the override returns is
 * assignable to what the call expects.
 *)
Theorem override_return_composed: forall R Re fuel, (forall y, In y ys -> is_loose y = false) ->
    member_type env c R = true -> nothing_is_bottom R = true -> caller Re ->
    unify env fuel (instantiate env bY R) Re (Ongoing []) = Some (Ongoing []) ->
    exists f, unify env f (instantiate env bS R) (instantiate env sigma Re) (Ongoing []) = Some (Ongoing []).
Proof.
    intros R Re fuel Hl Hf Hnb HcRe H. rewrite <- (proj1 (compose_member R Hf Hnb)).
    exact (subst_below env wf declared declared_wf terminates finite tame ps sigma Hsf Hwithin Hdeclared Re _ HcRe
        (member_instance_exact R Hl Hf Hnb) (ex_intro _ fuel H)).
Qed.

End Member.

End Composition.
