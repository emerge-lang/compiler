From Stdlib Require Import List String Ascii Bool Arith.
Import ListNotations.
From EmergeTypeSystem Require Import Model Subtyping Transitivity Fragment Generics Conjectures Constraints Inference
    Substitution SubstitutionWide WithinBounds GenericCode GenericArguments.
Local Open Scope string_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The model as the executable specification of the frontend                                      *)
(*                                                                                                *)
(* The proofs are about the model; the model is tied to the Kotlin code by review. This ties them *)
(* by computation, too: a Kotlin test (RocqOracleTests) writes Generated/Grid.v, the program of   *)
(* TypeGrid as an Environment, the types of the grid, and what the frontend answers of every pair  *)
(* of them: whether one is assignable to the other, and what intersect and                        *)
(* closestCommonSupertypeWith make of them. OracleGrid.v evaluates the model on the same pairs     *)
(* with vm_compute, and fails on any disagreement that isn't explained by a known divergence.     *)
(*                                                                                                *)
(* This file has what that takes, independent of the grid: the Environment made of the tables     *)
(* Grid.v holds, the comparison of the answers, and the checks of the conjectures about intersect  *)
(* and closestCommonSupertypeWith, each with the lemma that a check without violations is the     *)
(* conjecture, restricted to the types of the grid.                                                *)
(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)
(* The Environment, from tables                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Definition class_decl (kd: ClassKind) (is_const_class: bool) (ps: list TypeParameterId) (sups: list EType): ClassDecl :=
    {| kind := kd; is_const := is_const_class; type_parameters := map (fun p => {| param_id := p; prescribed_ownership := None |}) ps;
       supertypes := sups; fields := [] |}.

Definition lookup {T0 T1: Type} (R: T0 -> T0 -> bool) (default: T1) (table: list (T0 * T1)) (key: T0): T1 :=
    match find (fun e => R (fst e) key) table with Some (_, v) => v | None => default end.

(* class_eqb, without computing a proof of the equality *)
Definition class_beq (c0 c1: Class): bool :=
    match c0, c1 with
    | any, any | nothing, nothing => true
    | some_class x, some_class y => Nat.eqb x y
    | _, _ => false
    end.

Fixpoint classes_beq (l0 l1: list Class): bool :=
    match l0, l1 with
    | [], [] => true
    | x :: a', y :: b' => class_beq x y && classes_beq a' b'
    | _, _ => false
    end.

Definition class_pair_beq (left right: Class * Class): bool := class_beq (fst left) (fst right) && class_beq (snd left) (snd right).

(* A total order on types, for finding one among many in a search tree *)
Definition mutability_rank (m: option Mutability): nat :=
    match m with None => 0 | Some own => 1 | Some immutable => 2 | Some readonly => 3 | Some mutable => 4 end.
Definition class_rank (c: Class): nat := match c with any => 0 | nothing => 1 | some_class n => S (S n) end.
Definition variance_rank (v: Variance): nat := match v with Model.invariant => 0 | Model.input => 1 | Model.output => 2 end.
Definition ownership_rank (o: Ownership): nat :=
    match o with owned => 0 | ref => 1 | any_ownership => 2 | parameter_ownership p => S (S (S p)) end.
Definition constructor_rank (t: EType): nat :=
    match t with
    | RootResolved _ _ _ => 0 | Nullable _ => 1 | Generic _ => 2 | Error _ _ => 3 | TypeArgument _ _ _ => 4
    | TypeVariable _ => 5 | Intersection _ => 6
    end.

Definition then_compare (e0: comparison) (e1: comparison): comparison := match e0 with Eq => e1 | _ => e0 end.

Fixpoint nats_compare (l0 l1: list nat): comparison :=
    match l0, l1 with
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    | x :: a', y :: b' => then_compare (Nat.compare x y) (nats_compare a' b')
    end.

Definition generic_compare (g0 g1: GenericRef): comparison :=
    match g0, g1 with mkGenericRef m nn p vs, mkGenericRef m' nn' p' vs' =>
        then_compare (Nat.compare (mutability_rank m) (mutability_rank m'))
            (then_compare (Bool.compare nn nn') (then_compare (Nat.compare p p') (nats_compare vs vs')))
    end.

Fixpoint list_compare_with (f: EType -> EType -> comparison) (l l': list EType): comparison :=
    match l, l' with
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    | x :: r, y :: r' => match f x y with Eq => list_compare_with f r r' | c => c end
    end.

Fixpoint ety_compare (y z: EType): comparison :=
    match y, z with
    | RootResolved m c args, RootResolved m' c' args' =>
        match then_compare (Nat.compare (mutability_rank m) (mutability_rank m')) (Nat.compare (class_rank c) (class_rank c')) with
        | Eq => list_compare_with ety_compare args args'
        | x => x
        end
    | Nullable n, Nullable n' => ety_compare n n'
    | Generic g, Generic g' | TypeVariable g, TypeVariable g' => generic_compare g g'
    | Error m s, Error m' s' => then_compare (Nat.compare (mutability_rank m) (mutability_rank m')) (String.compare s s')
    | TypeArgument v o n, TypeArgument v' o' n' =>
        match then_compare (Nat.compare (variance_rank v) (variance_rank v')) (Nat.compare (ownership_rank o) (ownership_rank o')) with
        | Eq => ety_compare n n'
        | x => x
        end
    | Intersection cs, Intersection cs' => list_compare_with ety_compare cs cs'
    | _, _ => Nat.compare (constructor_rank y) (constructor_rank z)
    end.

Definition same (x y: EType): bool := match ety_compare x y with Eq => true | _ => false end.

(* The position of each of a list of types, the first where a type is there twice *)
Inductive Index := leaf | node (left: Index) (key: EType) (position: nat) (right: Index).

Fixpoint index_insert (x: EType) (i: nat) (tree: Index): Index :=
    match tree with
    | leaf => node leaf x i leaf
    | node l k' v' r =>
        match ety_compare x k' with
        | Lt => node (index_insert x i l) k' v' r
        | Gt => node l k' v' (index_insert x i r)
        | Eq => tree
        end
    end.

Fixpoint index_find (x: EType) (t: Index): option nat :=
    match t with
    | leaf => None
    | node l k' v r => match ety_compare x k' with Lt => index_find x l | Gt => index_find x r | Eq => Some v end
    end.

Definition index_of_all (types: list EType): Index :=
    fst (fold_left (fun acc k => (index_insert k (snd acc) (fst acc), S (snd acc))) types (leaf, 0)).

(* rows.(i).(j), for the i-th and the j-th of the types indexed *)
Definition lookup_pair (index: Index) (rows: list (list EType)) (default: EType) (x y: EType): EType :=
    match index_find x index, index_find y index with
    | Some i, Some j => nth j (nth i rows []) default
    | _, _ => default
    end.

(* What the frontend has of a program: the class declarations, their transitive supertypes but Any,
   BoundBaseType.closestCommonSupertypeOf of the lists of classes it was asked for, the parameterized
   supertypes, the bounds and ranks of the type parameters; and intersect and closestCommonSupertypeWith
   of the pairs of types of a grid, by position. Elsewhere, both are taken to be anything: the model's
   unify calls neither on types without type variables. Grid.v checks that each gives the entry of its
   table for every pair of the grid (tables_found, in OracleGrid.v). *)
Definition oracle_environment
    (classes: list (Class * ClassDecl)) (sups: list (Class * list Class)) (common: list (list Class * Class))
    (parameterized: list ((Class * Class) * EType)) (bounds: list (TypeParameterId * EType)) (ranks: list (TypeParameterId * nat))
    (types: list EType) (intersections common_supertypes: list (list EType)): Environment :=
    let index := index_of_all types in {|
    declaration_of := lookup class_beq (class_decl class_kind false [] []) classes;
    supertypes_of := lookup class_beq [] sups;
    closest_common_super_class := fun cs => lookup classes_beq (match cs with [c] => c | _ => any end) common cs;
    parameterized_supertype := fun sub super => lookup class_pair_beq (RootResolved None super []) parameterized (sub, super);
    closest_common_supertype_with := fun a b => lookup_pair index common_supertypes top_type a b;
    intersect := fun a b => lookup_pair index intersections (Intersection [a; b]) a b;
    parameter_bound := lookup Nat.eqb top_type bounds;
    parameter_rank := lookup Nat.eqb 0 ranks;
|}.

(* Abbreviations that keep Grid.v small *)
Module GridNotations.
Abbreviation R := RootResolved (only parsing).
Abbreviation N := Nullable (only parsing).
Abbreviation G m nn p := (Generic (mkGenericRef m nn p nil)) (only parsing).
Abbreviation A := TypeArgument (only parsing).
Abbreviation I := Intersection (only parsing).
Abbreviation K := some_class (only parsing).
Abbreviation mu := (Some mutable) (only parsing).
Abbreviation ro := (Some readonly) (only parsing).
Abbreviation im := (Some immutable) (only parsing).
Abbreviation ex := (Some own) (only parsing).
Abbreviation iv := Model.invariant (only parsing).
Abbreviation ii := Model.input (only parsing).
Abbreviation oo := Model.output (only parsing).
Abbreviation rf := Model.ref (only parsing).
Abbreviation po := Model.parameter_ownership (only parsing).
End GridNotations.

(* A type, written as in Emerge, for the reports of the checks *)
Section Show.

Variable class_names: list (Class * string).
Variable parameter_names: list (TypeParameterId * string).

Definition show_mutability (m: option Mutability): string :=
    match m with
    | None => ""
    | Some mutable => "mut "
    | Some readonly => "read "
    | Some immutable => "const "
    | Some own => "own "
    end.

Fixpoint join (sep: string) (l: list string): string :=
    match l with
    | [] => ""
    | [s] => s
    | s :: rest => String.append s (String.append sep (join sep rest))
    end.

Definition show_parameter (g: GenericRef): string :=
    String.append (show_mutability (given_mutability g))
        (String.append (lookup Nat.eqb "?" parameter_names (param_of g)) (if is_narrowed g then "!" else "")).

Fixpoint show (t: EType): string :=
    match t with
    | RootResolved m c arguments =>
        String.append (show_mutability m) (String.append (lookup class_eqb "?" class_names c)
            (match arguments with [] => "" | _ => String.append "<" (String.append (join ", " (map show arguments)) ">") end))
    | Nullable (Intersection cs) => String.append "(" (String.append (join " & " (map show cs)) ")?")
    | Nullable n => String.append (show n) "?"
    | Generic g => show_parameter g
    | Error _ message => String.append "error: " message
    | TypeArgument v _ n =>
        String.append (match v with Model.input => "in " | Model.output => "out " | Model.invariant => "" end) (show n)
    | TypeVariable g => String.append "_" (show_parameter g)
    | Intersection cs => join " & " (map show cs)
    end.

End Show.

(* ---------------------------------------------------------------------------------------------- *)
(* The type parameters a type mentions                                                             *)
(*                                                                                                *)
(* GenericCode.caller_type takes WithinBounds.mentions_only, a Prop. mentions_only_b decides it,  *)
(* and mentioned is the least list of type parameters a type mentions only, so that a check with  *)
(* that list covers every list (mentions_only_b_mono, mentions_only_mentioned).                   *)
(* ---------------------------------------------------------------------------------------------- *)

Section Mentions.

Variable env: Environment.

Definition mem (p: TypeParameterId) (ps: list TypeParameterId): bool := existsb (Nat.eqb p) ps.

Lemma mem_In: forall p ps, mem p ps = true <-> In p ps.
Proof.
    intros p ps. unfold mem. rewrite existsb_exists. split.
    - intros [q [Hq E]]. apply Nat.eqb_eq in E. subst q. exact Hq.
    - intros H. exists p. split; [exact H|apply Nat.eqb_refl].
Qed.

Definition ownership_in (ps: list TypeParameterId) (o: Ownership): bool :=
    match o with parameter_ownership q => mem q ps | _ => true end.

Definition without_variables (g: GenericRef): bool := match variables_of g with [] => true | _ => false end.

Fixpoint mentions_only_hb (ps: list TypeParameterId) (Q: TypeParameterId -> bool) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb (mentions_only_hb ps Q) arguments
    | Nullable n => mentions_only_hb ps Q n
    | Generic g => mem (param_of g) ps && without_variables g && Q (param_of g)
    | TypeArgument _ o n => ownership_in ps o && mentions_only_hb ps Q n
    | Intersection cs => forallb (mentions_only_hb ps Q) cs
    | _ => true
    end.

Definition mentions_only_b (ps: list TypeParameterId) (t: EType): bool :=
    mentions_only_hb ps (through_param env (mentions_only_hb ps) true) t.

Fixpoint mentioned_h (f: TypeParameterId -> list TypeParameterId) (t: EType): list TypeParameterId :=
    match t with
    | RootResolved _ _ arguments => flat_map (mentioned_h f) arguments
    | Nullable n => mentioned_h f n
    | Generic g => param_of g :: f (param_of g)
    | TypeArgument _ o n => match o with parameter_ownership q => q :: mentioned_h f n | _ => mentioned_h f n end
    | Intersection cs => flat_map (mentioned_h f) cs
    | _ => []
    end.

Definition mentioned (t: EType): list TypeParameterId := mentioned_h (through_param env mentioned_h []) t.

Lemma mentions_only_hb_iff: forall ps Q0 Q1, (forall q, Q0 q = true <-> Q1 q) ->
    forall t, mentions_only_hb ps Q0 t = true <-> mentions_only_h ps Q1 t.
Proof.
    intros ps Q0 Q1 HB. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs]; cbn [mentions_only_hb mentions_only_h].
    - induction args as [|a args IHa]; cbn [forallb fold_right]; [tauto|]. rewrite andb_true_iff, (IH a), IHa. tauto.
    - exact (IH n).
    - cbn [param_of]. unfold without_variables. cbn [variables_of]. rewrite !andb_true_iff, mem_In, HB.
      destruct vs as [|v vs]; [tauto|]. split; [intros [[_ H] _]; discriminate H|intros [_ [H _]]; discriminate H].
    - tauto.
    - rewrite andb_true_iff, (IH n). destruct o as [| | |q]; cbn [ownership_in]; try rewrite mem_In; split.
      1,3,5: intros [_ H]; split; [intros q' E; discriminate E|exact H].
      1,2,3: intros [_ H]; split; [reflexivity|exact H].
      + intros [H H']. split; [|exact H']. intros q' E. injection E as <-. exact H.
      + intros [H H']. split; [exact (H q eq_refl)|exact H'].
    - tauto.
    - induction cs as [|c cs IHc]; cbn [forallb fold_right]; [tauto|]. rewrite andb_true_iff, (IH c), IHc. tauto.
Qed.

Lemma mentions_only_b_iff: forall ps t, mentions_only_b ps t = true <-> mentions_only env ps t.
Proof.
    intros ps t. unfold mentions_only_b. rewrite mentions_only_top. apply mentions_only_hb_iff.
    intros q. unfold param_mentions_only, through_param. generalize (S (parameter_rank env q)) as k. intros k. revert q.
    induction k as [|k IHk]; intros q; cbn [param_level]; [tauto|].
    apply mentions_only_hb_iff. intros q'. destruct (param_eqb q' q); [tauto|apply IHk].
Qed.

Lemma mentions_only_hb_mono: forall ps ps', incl ps ps' -> forall Q Q', (forall q, Q q = true -> Q' q = true) ->
    forall t, mentions_only_hb ps Q t = true -> mentions_only_hb ps' Q' t = true.
Proof.
    intros ps ps' Hps Q Q' HB. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; cbn [mentions_only_hb] in H |- *;
        try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. cbn [forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - cbn [param_of] in H |- *. apply andb_true_iff in H. destruct H as [H Hb]. apply andb_true_iff in H. destruct H as [Hm Hv].
      rewrite mem_In in Hm. rewrite (proj2 (mem_In p ps') (Hps p Hm)), Hv, (HB p Hb). reflexivity.
    - apply andb_true_iff in H. destruct H as [Ho Hn]. rewrite (IH n Hn), andb_true_r.
      destruct o as [| | |q]; try reflexivity. cbn [ownership_in] in Ho |- *. rewrite mem_In in Ho |- *. exact (Hps q Ho).
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

Lemma mentions_only_b_mono: forall ps ps' t, incl ps ps' -> mentions_only_b ps t = true -> mentions_only_b ps' t = true.
Proof.
    intros ps ps' t Hps. unfold mentions_only_b. apply (mentions_only_hb_mono ps ps' Hps).
    intros q. unfold through_param. generalize (S (parameter_rank env q)) as k. intros k. revert q.
    induction k as [|k IHk]; intros q; cbn [param_level]; [tauto|].
    apply (mentions_only_hb_mono ps ps' Hps). intros q'. destruct (param_eqb q' q); [tauto|apply IHk].
Qed.

Lemma incl_flat_map: forall {T0 T1: Type} (f: T0 -> list T1) l ps, (forall x, In x l -> incl (f x) ps) -> incl (flat_map f l) ps.
Proof.
    intros T0 T1 f l ps H y Hy. apply in_flat_map in Hy. destruct Hy as [x [Hx Hy]]. exact (H x Hx y Hy).
Qed.

Lemma mentioned_h_incl: forall ps Q f, (forall q, Q q = true -> incl (f q) ps) ->
    forall t, mentions_only_hb ps Q t = true -> incl (mentioned_h f t) ps.
Proof.
    intros ps Q f HB. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; cbn [mentions_only_hb mentioned_h] in H |- *;
        try (intros y Hy; contradiction Hy).
    - induction args as [|a args IHa]; [intros y []|]. cbn [forallb flat_map] in H |- *. apply andb_true_iff in H.
      intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy]; [exact (IH a (proj1 H) y Hy)|exact (IHa (proj2 H) y Hy)].
    - exact (IH n H).
    - cbn [param_of] in H |- *. apply andb_true_iff in H. destruct H as [H Hb]. apply andb_true_iff in H. destruct H as [Hm _].
      rewrite mem_In in Hm. intros y [<-|Hy]; [exact Hm|exact (HB p Hb y Hy)].
    - apply andb_true_iff in H. destruct H as [Ho Hn]. destruct o as [| | |q]; try exact (IH n Hn).
      cbn [ownership_in] in Ho. rewrite mem_In in Ho. intros y [<-|Hy]; [exact Ho|exact (IH n Hn y Hy)].
    - induction cs as [|c cs IHc]; [intros y []|]. cbn [forallb flat_map] in H |- *. apply andb_true_iff in H.
      intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy]; [exact (IH c (proj1 H) y Hy)|exact (IHc (proj2 H) y Hy)].
Qed.

Lemma mentions_only_mentioned: forall ps t, mentions_only_b ps t = true -> incl (mentioned t) ps.
Proof.
    intros ps t. unfold mentions_only_b, mentioned. apply mentioned_h_incl.
    intros q. unfold through_param. generalize (S (parameter_rank env q)) as k. intros k. revert q.
    induction k as [|k IHk]; intros q; cbn [param_level]; [intros _ y []|].
    apply mentioned_h_incl. intros q'. destruct (param_eqb q' q); [intros _ y []|apply IHk].
Qed.

End Mentions.

(* ---------------------------------------------------------------------------------------------- *)
(* Checks over the pairs of a grid of types                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Section Checks.

Variable env: Environment.
Let declared := parameter_bound env.
(* unify is given this much fuel; where it gives no answer with it, that is an outcome of its own *)
Variable fuel: nat.
(* the types of the grid, by their names *)
Variable grid: list (string * EType).
(* how the checks print the types they report *)
Variable name_of: EType -> string.

Definition grid_types: list EType := map snd grid.

(* ---------------------------------------------------------------------------------------------- *)
(* Assignability                                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* model: is_assignable_to with the fuel, None where unify gives no answer; frontend:
   evaluateAssignabilityTo found no error *)
Record Disagreement := disagreement { assignee: string; target: string; model: option bool; frontend: bool }.

(* A divergence between the frontend and the model that is known, owned by an item of coverage.md or
   roadmap.md: its name, and whether it explains the model's answer of a below b where the frontend
   has the other *)
Definition Excuse := (string * (EType -> EType -> option bool -> bool -> bool))%type.

Fixpoint bits (str: string): list bool :=
    match str with
    | EmptyString => []
    | String c rest => Ascii.eqb c "1"%char :: bits rest
    end.

Definition option_bool_eqb (e0 e1: option bool): bool :=
    match e0, e1 with Some x, Some y => Bool.eqb x y | None, None => true | _, _ => false end.

(* Every pair the answers differ on, with the names of the excuses that explain it *)
Definition explain (excuses: list Excuse) (answers: list string): list (Disagreement * list string) :=
    flat_map (fun '((na, a), row) =>
        flat_map (fun '((nb, b), f) =>
            let m := is_assignable_to env fuel a b in
            if option_bool_eqb m (Some f) then []
            else [(disagreement na nb m f, map fst (filter (fun e => snd e a b m f) excuses))])
        (combine grid (bits row)))
    (combine grid answers).

(* The disagreements no excuse explains, and the excuses that explain none (stale, to be removed) *)
Definition comparison (excuses: list Excuse) (answers: list string): list Disagreement * list string :=
    let explained := explain excuses answers in
    (map fst (filter (fun d => match snd d with [] => true | _ => false end) explained),
     filter (fun name => negb (existsb (fun d => existsb (String.eqb name) (snd d)) explained)) (map fst excuses)).

(* Rows and columns as many as there are types *)
Definition answers_shaped (answers: list string): bool :=
    Nat.eqb (List.length answers) (List.length grid) && forallb (fun row => Nat.eqb (String.length row) (List.length grid)) answers.

(* intersect and closestCommonSupertypeWith of the environment are the tables of the frontend's results *)
Definition tables_found (intersections common_supertypes: list (list EType)): bool :=
    forallb (fun '(a, (ri, rs)) =>
        forallb (fun '(b, (i, s)) =>
            same (intersect env a b) i && same (closest_common_supertype_with env a b) s)
        (combine grid_types (combine ri rs)))
    (combine grid_types (combine intersections common_supertypes))
    && Nat.eqb (List.length intersections) (List.length grid) && Nat.eqb (List.length common_supertypes) (List.length grid)
    && forallb (fun r => Nat.eqb (List.length r) (List.length grid)) (intersections ++ common_supertypes)%list.

(* What the model derives of a type, written as the frontend's derivations are in Grid.v: mutability,
   assignment mutability, nullable, Nothing without null, the base type of the lower bound. Where the
   encoding of a type lost something the frontend takes into account, these are likely to differ *)
Definition mutability_letter (m: Mutability): ascii :=
    match m with mutable => "m"%char | readonly => "r"%char | immutable => "i"%char | own => "e"%char end.
Definition bool_letter (e: bool): ascii := if e then "1"%char else "0"%char.
Definition class_letter (c: Class): ascii :=
    match c with
    | any => "a"%char
    | nothing => "n"%char
    | some_class k => match String.get k "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ" with Some x => x | None => "?"%char end
    end.

Definition properties_of (t: EType): string :=
    String (mutability_letter (mutability_of env t)) (String (mutability_letter (assignment_mutability env t))
        (String (bool_letter (is_nullable env t)) (String (bool_letter (is_non_nullable_nothing env t))
            (String (class_letter (base_type_of_lower_bound env t)) EmptyString)))).

(* The types whose properties differ: the type, the frontend's, the model's. "-----" is a type the
   frontend threw on *)
Fixpoint property_mismatches (types: list EType) (properties: string): list (string * string * string) :=
    match types, properties with
    | t :: rest, String a (String b (String c (String d (String e more)))) =>
        let frontend := String a (String b (String c (String d (String e EmptyString)))) in
        let model := properties_of t in
        ((if String.eqb frontend "-----" || String.eqb frontend model then [] else [(name_of t, frontend, model)])
            ++ property_mismatches rest more)%list
    | [], EmptyString => []
    | _, _ => [("as many properties as types", "", "")]
    end.

(* ---------------------------------------------------------------------------------------------- *)
(* Conjectures                                                                                     *)
(*                                                                                                *)
(* A check of a conjecture `forall a b, ... -> P a b` is a function of a and b, and of what        *)
(* intersect and closestCommonSupertypeWith make of them: None where P a b holds, or why not. One  *)
(* pass over the pairs runs every check (report); without violations but those an excuse of the    *)
(* check explains, each conjecture holds of every pair of the grid that no excuse of it takes out   *)
(* (report_sound, and the lemma of each check).                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Record Check := check {
    conjecture: string;
    (* of a, b, intersect env a b, closest_common_supertype_with env a b *)
    run: EType -> EType -> EType -> EType -> option string;
    (* the known violations: a name, and whether it explains one, of a, b and the two results *)
    excuses: list (string * (EType -> EType -> EType -> EType -> bool));
}.

Record Violation := violation { of_conjecture: string; first: string; second: string; outcome: string; excused_by: list string }.

Definition all_violations (checks: list Check): list Violation :=
    flat_map (fun x =>
        flat_map (fun y =>
            let a := snd x in
            let b := snd y in
            let i := intersect env a b in
            let s := closest_common_supertype_with env a b in
            flat_map (fun c =>
                match run c a b i s with
                | Some why => [violation (conjecture c) (fst x) (fst y) why (map fst (filter (fun e => snd e a b i s) (excuses c)))]
                | None => []
                end) checks) grid) grid.

(* The violations no excuse explains, and the excuses that explain none (stale, to be removed), by the
   conjecture they are of *)
Definition report (checks: list Check): list Violation * list (string * string) :=
    let vs := all_violations checks in
    (filter (fun v => match excused_by v with [] => true | _ => false end) vs,
     flat_map (fun c =>
        map (fun e => (conjecture c, fst e))
            (filter (fun e => negb (existsb (fun v => String.eqb (of_conjecture v) (conjecture c) && existsb (String.eqb (fst e)) (excused_by v)) vs))
                (excuses c))) checks).

Definition excused (chk: Check) (x y: EType): bool :=
    existsb (fun e => snd e x y (intersect env x y) (closest_common_supertype_with env x y)) (excuses chk).

Lemma report_sound: forall checks, fst (report checks) = [] ->
    forall chk, In chk checks -> forall z y0, In z grid_types -> In y0 grid_types -> excused chk z y0 = false ->
    run chk z y0 (intersect env z y0) (closest_common_supertype_with env z y0) = None.
Proof.
    intros checks H chk Hc z y0 Ha Hb He. unfold excused in He.
    destruct (run chk z y0 (intersect env z y0) (closest_common_supertype_with env z y0)) as [why|] eqn:E; [exfalso|reflexivity].
    apply in_map_iff in Ha. destruct Ha as [x [Ex Hx]]. apply in_map_iff in Hb. destruct Hb as [y [Ey Hy]].
    set (v := violation (conjecture chk) (fst x) (fst y) why []).
    assert (Hv: In v (all_violations checks)).
    { unfold all_violations. apply in_flat_map. exists x. split; [exact Hx|]. apply in_flat_map. exists y. split; [exact Hy|].
      apply in_flat_map. exists chk. split; [exact Hc|]. rewrite Ex, Ey, E. left. unfold v. f_equal.
      destruct (filter _ (excuses chk)) as [|e es] eqn:F; [reflexivity|]. exfalso.
      assert (He': In e (filter (fun e => snd e z y0 (intersect env z y0) (closest_common_supertype_with env z y0)) (excuses chk)))
          by (rewrite F; left; reflexivity).
      apply filter_In in He'. destruct He' as [He1 He2].
      rewrite (proj2 (existsb_exists _ _) (ex_intro _ e (conj He1 He2))) in He. discriminate He. }
    unfold report in H. cbn [fst] in H.
    assert (Hf: In v (filter (fun v => match excused_by v with [] => true | _ => false end) (all_violations checks)))
        by (apply filter_In; split; [exact Hv|reflexivity]).
    rewrite H in Hf. exact Hf.
Qed.

(* A conjecture of pairs, of every pair of the grid an excuse of the check doesn't take out *)
Definition on_grid (c: Check) (Q: EType -> EType -> Prop): Prop :=
    forall a b, In a grid_types -> In b grid_types -> excused c a b = false -> Q a b.

Lemma checked: forall checks chk (Q: EType -> EType -> Prop), fst (report checks) = [] -> In chk checks ->
    (forall x y, run chk x y (intersect env x y) (closest_common_supertype_with env x y) = None -> Q x y) -> on_grid chk Q.
Proof. intros checks chk Q H Hc HP x y Ha Hb He. exact (HP x y (report_sound checks H chk Hc x y Ha Hb He)). Qed.

Definition why_not_below (what: string) (x y: EType): option string :=
    match is_assignable_to env fuel x y with
    | Some true => None
    | Some false => Some what
    | None => Some (what ++ ", or no answer within the fuel")
    end.

Lemma why_not_below_none: forall what x y, why_not_below what x y = None -> exists n, is_assignable_to env n x y = Some true.
Proof.
    intros what x y H. unfold why_not_below in H. exists fuel.
    destruct (is_assignable_to env fuel x y) as [[]|]; [reflexivity|discriminate H|discriminate H].
Qed.

Definition first_failure (first second: option string): option string := match first with Some _ => first | None => second end.

Lemma first_failure_none: forall first second, first_failure first second = None -> first = None /\ second = None.
Proof. intros [first|] second H; [discriminate H|split; [reflexivity|exact H]]. Qed.

Definition unless (holds: bool) (why: string): option string := if holds then None else Some why.

Lemma unless_none: forall holds why, unless holds why = None -> holds = true.
Proof. intros [] why H; [reflexivity|discriminate H]. Qed.

Definition result_named (what: string) (t: EType): string := what ++ name_of t.

(* Conjectures.intersect_stays_in_fragment *)
Definition intersect_in_fragment_check (x y z _: EType): option string :=
    if gfrag env x && gfrag env y && negb (keeps_nullability env x y)
    then unless (gfrag env z) (result_named "not of gfrag: " z)
    else None.

Definition intersect_in_fragment_on (x y: EType): Prop :=
    gfrag env x = true /\ refs_wf env declared x -> gfrag env y = true /\ refs_wf env declared y ->
    keeps_nullability env x y = false -> gfrag env (intersect env x y) = true /\ refs_wf env declared (intersect env x y).

Lemma intersect_in_fragment_checked: forall x y,
    intersect_in_fragment_check x y (intersect env x y) (closest_common_supertype_with env x y) = None -> intersect_in_fragment_on x y.
Proof.
    intros x y H [Ha _] [Hb _] Hk. unfold intersect_in_fragment_check in H. rewrite Ha, Hb, Hk in H. cbn in H.
    split; [exact (unless_none _ _ H)|exact I].
Qed.

(* Conjectures.intersect_always_stays_in_fragment *)
Definition intersect_always_in_fragment_check (x y z _: EType): option string :=
    if gfrag env x && gfrag env y then unless (gfrag env z) (result_named "not of gfrag: " z) else None.

Definition intersect_always_in_fragment_on (x y: EType): Prop :=
    gfrag env x = true /\ refs_wf env declared x -> gfrag env y = true /\ refs_wf env declared y ->
    gfrag env (intersect env x y) = true /\ refs_wf env declared (intersect env x y).

Lemma intersect_always_in_fragment_checked: forall x y,
    intersect_always_in_fragment_check x y (intersect env x y) (closest_common_supertype_with env x y) = None ->
    intersect_always_in_fragment_on x y.
Proof.
    intros x y H [Ha _] [Hb _]. unfold intersect_always_in_fragment_check in H. rewrite Ha, Hb in H. cbn in H.
    split; [exact (unless_none _ _ H)|exact I].
Qed.

(* Conjectures.intersect_makes_no_bare_nullable *)
Definition intersect_no_bare_nullable_check (x y z _: EType): option string :=
    if gfrag env x && gfrag env y && negb (bare_nullable env x) && negb (bare_nullable env y)
    then unless (negb (bare_nullable env z)) (result_named "bare nullable: " z)
    else None.

Definition intersect_no_bare_nullable_on (x y: EType): Prop :=
    gfrag env x = true /\ refs_wf env declared x -> gfrag env y = true /\ refs_wf env declared y ->
    bare_nullable env x = false -> bare_nullable env y = false -> bare_nullable env (intersect env x y) = false.

Lemma intersect_no_bare_nullable_checked: forall x y,
    intersect_no_bare_nullable_check x y (intersect env x y) (closest_common_supertype_with env x y) = None ->
    intersect_no_bare_nullable_on x y.
Proof.
    intros x y H [Ha _] [Hb _] Hna Hnb. unfold intersect_no_bare_nullable_check in H. rewrite Ha, Hb, Hna, Hnb in H. cbn in H.
    apply negb_true_iff. exact (unless_none _ _ H).
Qed.

(* Conjectures.closest_common_supertype_makes_no_bare_nullable *)
Definition supertype_no_bare_nullable_check (x y _ z: EType): option string :=
    if gfrag env x && gfrag env y && negb (bare_nullable env x) && negb (bare_nullable env y)
    then unless (negb (bare_nullable env z)) (result_named "bare nullable: " z)
    else None.

Definition supertype_no_bare_nullable_on (x y: EType): Prop :=
    gfrag env x = true /\ refs_wf env declared x -> gfrag env y = true /\ refs_wf env declared y ->
    bare_nullable env x = false -> bare_nullable env y = false -> bare_nullable env (closest_common_supertype_with env x y) = false.

Lemma supertype_no_bare_nullable_checked: forall x y,
    supertype_no_bare_nullable_check x y (intersect env x y) (closest_common_supertype_with env x y) = None ->
    supertype_no_bare_nullable_on x y.
Proof.
    intros x y H [Ha _] [Hb _] Hna Hnb. unfold supertype_no_bare_nullable_check in H. rewrite Ha, Hb, Hna, Hnb in H. cbn in H.
    apply negb_true_iff. exact (unless_none _ _ H).
Qed.

(* Conjectures.closest_common_supertype_stays_in_fragment *)
Definition supertype_in_fragment_check (x y _ z: EType): option string :=
    if gfrag env x && gfrag env y then unless (gfrag env z) (result_named "not of gfrag: " z) else None.

Definition supertype_in_fragment_on (x y: EType): Prop :=
    gfrag env x = true /\ refs_wf env declared x -> gfrag env y = true /\ refs_wf env declared y ->
    gfrag env (closest_common_supertype_with env x y) = true /\ refs_wf env declared (closest_common_supertype_with env x y).

Lemma supertype_in_fragment_checked: forall x y,
    supertype_in_fragment_check x y (intersect env x y) (closest_common_supertype_with env x y) = None ->
    supertype_in_fragment_on x y.
Proof.
    intros x y H [Ha _] [Hb _]. unfold supertype_in_fragment_check in H. rewrite Ha, Hb in H. cbn in H.
    split; [exact (unless_none _ _ H)|exact I].
Qed.

(* Conjectures.intersect_is_below_both *)
Definition intersect_below_check (x y z _: EType): option string :=
    if gfrag env x && gfrag env y
    then first_failure
        (why_not_below (result_named "not below the first: " z) z x)
        (why_not_below (result_named "not below the second: " z) z y)
    else None.

Definition intersect_below_on (x y: EType): Prop :=
    gfrag env x = true /\ refs_wf env declared x -> gfrag env y = true /\ refs_wf env declared y ->
    (exists n, is_assignable_to env n (intersect env x y) x = Some true)
    /\ (exists n, is_assignable_to env n (intersect env x y) y = Some true).

Lemma intersect_below_checked: forall x y,
    intersect_below_check x y (intersect env x y) (closest_common_supertype_with env x y) = None -> intersect_below_on x y.
Proof.
    intros x y H [Ha _] [Hb _]. unfold intersect_below_check in H. rewrite Ha, Hb in H. cbn in H.
    destruct (first_failure_none _ _ H) as [H1 H2]. split; [exact (why_not_below_none _ _ _ H1)|exact (why_not_below_none _ _ _ H2)].
Qed.

(* Conjectures.closest_common_supertype_is_above_both *)
Definition supertype_above_check (x y _ z: EType): option string :=
    if gfrag env x && gfrag env y
    then first_failure
        (why_not_below (result_named "not above the first: " z) x z)
        (why_not_below (result_named "not above the second: " z) y z)
    else None.

Definition supertype_above_on (x y: EType): Prop :=
    gfrag env x = true /\ refs_wf env declared x -> gfrag env y = true /\ refs_wf env declared y ->
    (exists n, is_assignable_to env n x (closest_common_supertype_with env x y) = Some true)
    /\ (exists n, is_assignable_to env n y (closest_common_supertype_with env x y) = Some true).

Lemma supertype_above_checked: forall x y,
    supertype_above_check x y (intersect env x y) (closest_common_supertype_with env x y) = None -> supertype_above_on x y.
Proof.
    intros x y H [Ha _] [Hb _]. unfold supertype_above_check in H. rewrite Ha, Hb in H. cbn in H.
    destruct (first_failure_none _ _ H) as [H1 H2]. split; [exact (why_not_below_none _ _ _ H1)|exact (why_not_below_none _ _ _ H2)].
Qed.

(* GenericCode.intersect_stays_in_generic_code and closest_common_supertype_stays_in_generic_code: for
   every list of type parameters of the caller. A type mentions only those of a list where it mentions
   only those it mentions (mentions_only_mentioned), so the check takes the least such list, that of
   both types, and covers the others by monotonicity *)
Definition in_generic_code (y z x: EType): option string :=
    let ps := (mentioned env y ++ mentioned env z)%list in
    if gfrag env y && gfrag env z && ktfrag env y && ktfrag env z
    then unless (ktfrag env x && mentions_only_b env ps x) (result_named "not of the generic code of both: " x)
    else None.

Definition in_generic_code_on (f: EType -> EType -> EType) (x y: EType): Prop :=
    forall ps, of_fragment env declared x -> of_fragment env declared y ->
    caller_type env declared ps x -> caller_type env declared ps y -> caller_type env declared ps (f x y).

Lemma in_generic_code_checked: forall f x y, in_generic_code x y (f x y) = None -> in_generic_code_on f x y.
Proof.
    intros f x y H ps [Ha _] [Hb _] [Hka [_ Hma]] [Hkb [_ Hmb]]. unfold in_generic_code in H. rewrite Ha, Hb, Hka, Hkb in H.
    cbn in H. apply unless_none, andb_true_iff in H. destruct H as [Hk Hm].
    split; [exact Hk|split; [exact I|]]. apply mentions_only_b_iff.
    apply (mentions_only_b_mono env (mentioned env x ++ mentioned env y)%list); [|exact Hm].
    intros q Hq. apply in_app_or in Hq. destruct Hq as [Hq|Hq].
    - exact (mentions_only_mentioned env ps x (proj2 (mentions_only_b_iff env ps x) Hma) q Hq).
    - exact (mentions_only_mentioned env ps y (proj2 (mentions_only_b_iff env ps y) Hmb) q Hq).
Qed.

Definition intersect_in_generic_code_check (x y z _: EType): option string := in_generic_code x y z.
Definition supertype_in_generic_code_check (x y _ z: EType): option string := in_generic_code x y z.

(* GenericArguments.closest_common_supertype_keeps_bottom_only *)
Definition bottom_only_check (x y _ z: EType): option string :=
    if gfrag env x && gfrag env y && bottom_only env x && bottom_only env y
    then unless (bottom_only env z) (result_named "not bottom_only: " z)
    else None.

Definition bottom_only_on (x y: EType): Prop :=
    of_fragment env declared x -> of_fragment env declared y -> bottom_only env x = true -> bottom_only env y = true ->
    bottom_only env (closest_common_supertype_with env x y) = true.

Lemma bottom_only_checked: forall x y,
    bottom_only_check x y (intersect env x y) (closest_common_supertype_with env x y) = None -> bottom_only_on x y.
Proof.
    intros x y H [Ha _] [Hb _] Hoa Hob. unfold bottom_only_check in H. rewrite Ha, Hb, Hoa, Hob in H. cbn in H.
    exact (unless_none _ _ H).
Qed.

(* Constraints.closest_common_supertype_of_classes: of class types without contravariance *)
Definition of_classes_check (x y _ z: EType): option string :=
    if afrag env x && closed x && without_contravariance x && afrag env y && closed y && without_contravariance y
    then unless (afrag env z && closed z && without_contravariance z)
        (result_named "not a class type without contravariance: " z)
    else None.

Definition of_classes_on (x y: EType): Prop :=
    afrag env x = true -> closed x = true -> without_contravariance x = true ->
    afrag env y = true -> closed y = true -> without_contravariance y = true ->
    afrag env (closest_common_supertype_with env x y) = true /\ closed (closest_common_supertype_with env x y) = true
    /\ without_contravariance (closest_common_supertype_with env x y) = true.

Lemma of_classes_checked: forall x y,
    of_classes_check x y (intersect env x y) (closest_common_supertype_with env x y) = None -> of_classes_on x y.
Proof.
    intros x y H Ha Hca Hwa Hb Hcb Hwb. unfold of_classes_check in H. rewrite Ha, Hca, Hwa, Hb, Hcb, Hwb in H. cbn in H.
    apply unless_none in H. apply andb_true_iff in H. destruct H as [H Hw]. apply andb_true_iff in H. destruct H as [Hf Hc].
    split; [exact Hf|split; [exact Hc|exact Hw]].
Qed.

End Checks.

(* ---------------------------------------------------------------------------------------------- *)
(* What the excuses look for                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Section Shapes.

Variable env: Environment.

(* An intersection of classes that have no common subtype, nullable or not: the frontend takes it
   for Nothing (BoundIntersectionTypeReference.isEffectivelyBottom) *)
Definition disjoint_intersection (t: EType): bool :=
    match t with
    | Intersection cs | Nullable (Intersection cs) => is_effectively_bottom_type env cs
    | _ => false
    end.

(* The type, with the intersections that are in-variant type arguments replaced by `read Any?` *)
Fixpoint without_contravariant_intersections (t: EType): EType :=
    match t with
    | RootResolved m c arguments => RootResolved m c (map without_contravariant_intersections arguments)
    | Nullable n => Nullable (without_contravariant_intersections n)
    | TypeArgument Model.input o (Intersection _ | Nullable (Intersection _)) => TypeArgument Model.input o top_type
    | TypeArgument v o n => TypeArgument v o (without_contravariant_intersections n)
    | Intersection cs => Intersection (map without_contravariant_intersections cs)
    | _ => t
    end.

End Shapes.
