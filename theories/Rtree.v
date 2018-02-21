Require Import List Program Arith Omega.

(** ========== Common library ========== *)

Ltac inv H := inversion H; subst; clear H.

(** === Indexed Forall === *)

(* Same as [Forall], but depending on the position in the list. *)
Inductive Foralli_aux {A : Type} (P : nat -> A -> Prop) : nat -> list A -> Prop :=
| Foralli_nil : forall (n : nat), Foralli_aux P n []
| Foralli_cons : forall (x : A) (l : list A) (i : nat),
    P i x -> Foralli_aux P (S i) l -> Foralli_aux P i (x :: l).
Definition Foralli {A} P (l : list A) := (Foralli_aux P 0 l).

(* Some lemmas about [Foralli], but also [Forall] which is lacking in the stdlib. *)

Lemma Forall_app {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; simpl; intros.
  - easy.
  - inv H. destruct (IHl1 H3).
    now repeat constructor.
Qed.

Lemma Forall_map {A B : Type} {P : B -> Prop} {f : A -> B} {l : list A} :
  Forall (fun x => P (f x)) l ->
  Forall P (map f l).
Proof.
  induction 1; now constructor.
Qed.

Lemma Forall_In {A : Type} {P : A -> Prop} {l : list A} {x : A} :
  Forall P l -> In x l -> P x.
Proof.
  intros.
  eapply Forall_forall; eassumption.
Qed.

Lemma Forall_forall' {A : Type} {P : A -> Prop} {l : list A} :
  Forall P l -> (forall x : A, In x l -> P x).
Proof.
  apply Forall_forall.
Qed.

Lemma Forall_Impl {A : Type} {P Q : A -> Prop} {l : list A} :
  Forall P l -> Forall (fun t => P t -> Q t) l -> Forall Q l.
Proof.
  induction 1; constructor.
  - inv H1; auto.
  - inv H1; auto.
Qed.

Lemma Foralli_map {A B : Type} {P : nat -> B -> Prop} {f : A -> B} {l : list A} :
  Foralli (fun i x => P i (f x)) l ->
  Foralli P (map f l).
Proof.
  unfold Foralli. generalize 0.
  induction 1; now constructor.
Qed.

Lemma Foralli_aux_impl {A : Type} (P Q : nat -> A -> Prop) {l : list A} {n : nat} :
(forall i a, i < n + length l -> In a l -> P i a -> Q i a) -> Foralli_aux P n l -> Foralli_aux Q n l.
Proof.
  induction 2; constructor.
  - apply H; simpl.
    + omega.
    + now left.
    + assumption.
  - apply IHForalli_aux. intros.
    apply H.
    + simpl. omega.
    + now right.
    + assumption.
Qed.

Lemma Foralli_impl {A : Type} (P Q : nat -> A -> Prop) {l : list A} :
(forall i a, i < length l -> In a l -> P i a -> Q i a) -> Foralli P l -> Foralli Q l.
Proof.
  rewrite <- (plus_O_n (length l)).
  apply Foralli_aux_impl.
Qed.


(** === Safe access in a list === *)

Notation "( x ; y )" := (exist _ x y).

Fixpoint safe_nth {A} (l : list A) (n : nat | n < length l) : A.
Proof.
  destruct l as [|hd tl].
  - exfalso. destruct n as [? H].
    inversion H.
  - destruct n as [[|n'] H].
    + exact hd.
    + refine (safe_nth _ tl (n'; _)).
      apply lt_S_n. assumption.
Defined.

(* Sometimes the [n < length l] proof is too big, we define this tactic for
   readability purposes. We do not actually care about the proof itself
   anyway, since it is provably irrelevant. *)
(* Additionally, we might need this if we want to rewrite the type of the proof. *)
Ltac gen_safe_proof :=
  match goal with
  |- context [safe_nth _ (_ ; ?H)] =>
      tryif is_var H then fail else
        let Hs := fresh "Hs" in
        generalize H as Hs
  end.

(* A few lemmas about [safe_nth] and standard list definitions. *)

Lemma safe_nth_app2 {A : Type} (l1 l2 : list A) (n : nat) H1 H2 :
  safe_nth (l1 ++ l2) (length l1 + n ; H1) = safe_nth l2 (n ; H2).
Proof.
  induction l1; simpl in *.
  - f_equal. f_equal. 
    (* We could do without [proof_irrelevance]. *) apply proof_irrelevance.
  - erewrite <- IHl1. reflexivity.
Qed.

Lemma safe_nth_app2' {A : Type} (l1 l2 : list A) (n : nat) H1 H2 :
  safe_nth (l1 ++ l2) (n + length l1 ; H1) = safe_nth l2 (n ; H2).
Proof.
  simpl in *. revert H1.
  rewrite plus_comm; intros H1.
  apply safe_nth_app2.
Qed.

Lemma safe_nth_app1 {A : Type} (l1 l2 : list A) (n : nat) H1 H2 :
  safe_nth (l1 ++ l2) (n ; H1) = safe_nth l1 (n ; H2).
Proof.
  revert n H1 H2;
  induction l1; simpl in *;
  intros n H1 H2.
  - inversion H2.
  - destruct n.
    + reflexivity.
    + erewrite <- IHl1. reflexivity.
Qed.

Lemma safe_nth_map {A B} (F : A -> B) (l : list A) (n : nat) H1 H2 :
  safe_nth (map F l) (n ; H1) = F (safe_nth l (n ; H2)).
Proof.
revert n H1 H2.
  induction l; simpl in *;
  intros n H1 H2.
  - inversion H1.
  - destruct n.
    + reflexivity.
    + erewrite <- IHl. reflexivity.
Qed.

Lemma safe_nth_In {A} (l : list A) (n : nat | n < length l) :
  In (safe_nth l n) l.
Proof.
  revert n.
  induction l; intros [n Hn]; simpl in *.
  - inversion Hn.
  - destruct n; [left | right].
    + reflexivity.
    + apply IHl.
Qed.

(* One useful lemma about [safe_nth] and [Forall]. *)

Lemma safe_nth_Forall {A} (P : A -> Prop) (l : list A) (n : nat | n < length l) :
  Forall P l -> P (safe_nth l n).
Proof.
  intros H.
  eapply Forall_In.
  - eassumption.
  - apply safe_nth_In.
Qed.


(** ========== Recursion on a set of variables. ========== *)

Require Import Sorting Orders Permutation.

Lemma Permutation_Forall {A : Type} {P : A -> Prop} {l l' : list A} :
  Permutation l l' -> Forall P l' -> Forall P l.
Proof.
  induction 1; intros Htmp;
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end; repeat constructor; auto.
Qed.

Fixpoint rseq (n : nat) :=
  match n with
  | O => []
  | S n => n :: rseq n
  end.

Lemma rseq_In (M : nat) (n : nat) : n < M <-> In n (rseq M).
Proof.
  induction M; split; intros; simpl in *.
  - inversion H.
  - inversion H.
  - destruct (le_lt_dec M n).
    + left. omega.
    + right. now apply IHM.
  - destruct H.
    + omega.
    + constructor. now apply IHM.
Qed.

Lemma SortedNoDup_seq : forall l, StronglySorted gt l ->
  forall M, NoDup l -> Forall (fun x => x < M) l ->
  length l >= M -> l = rseq M.
Proof.
  induction 1; intros; simpl in *.
  - now inv H1.
  - inv H1; inv H2.
    specialize (fun H => IHStronglySorted (length l) ltac:(assumption) H (le_n _)).
    assert (l = rseq (length l)) as Hl.
    { apply IHStronglySorted.
      apply Forall_forall; intros.
      pose proof (Forall_In H0 H1).
      omega. }
    assert (~ a < length l) as Ha.
    { contradict H6. rewrite Hl. now apply rseq_In. }
    assert (M = S (length l)) as -> by omega.
    simpl. f_equal.
    + omega.
    + assumption.
Qed.

Lemma SortedNoDup_In : forall l, StronglySorted gt l ->
  forall M j,
  NoDup l -> Forall (fun x => x < M) l ->
  length l >= M -> j < M -> In j l.
Proof.
  intros.
  rewrite SortedNoDup_seq with (M := M); try assumption.
  now apply rseq_In.
Qed.

Module NatOrder <: TotalLeBool.
  Definition t := nat.
  Definition leb x y := Nat.leb y x.
  Theorem leb_total : forall a1 a2, is_true (leb a1 a2) \/ is_true (leb a2 a1).
  Proof.
    unfold leb; intros.
    destruct (le_lt_dec a1 a2).
    - right. now apply leb_correct.
    - left. apply leb_correct. auto with arith.
  Qed.
End NatOrder.

Module Import NatSort := Sort NatOrder.

Lemma StronglySortedNoDup_ge_gt :
  forall l,
  StronglySorted (fun a b => is_true (Nat.leb b a)) l ->
  NoDup l ->
  StronglySorted gt l.
Proof.
  induction 1; intros.
  - constructor.
  - inv H1. specialize (IHStronglySorted H5).
    constructor.
    + assumption.
    + apply Forall_forall; intros.
      assert (a <> x).
      { contradict H4; now subst. }
      apply Forall_In with (2 := H1) in H0; simpl in H0.
      apply leb_complete in H0. omega.
Qed.

(* Main theorem that allows the recursion. *)
Theorem NoDupFull_In : forall l M j,
  NoDup l -> Forall (fun x => x < M) l ->
  length l >= M -> j < M -> In j l.
Proof.
  intros.
  pose proof (SortedNoDup_In (sort l)).
  assert (Permutation (sort l) l).
  { apply Permutation_sym. apply Permuted_sort. }
  eapply Permutation_in.
  { eassumption. }
  assert (NoDup (sort l)).
  { eapply Permutation_NoDup'; eassumption. }
  apply H3 with (M := length l).
  + assert (StronglySorted (fun a b => is_true (Nat.leb b a)) (sort l)).
    { apply StronglySorted_sort.
      unfold Transitive; intros.
      apply leb_correct. apply leb_complete in H6. apply leb_complete in H7.
      omega. }
    now apply StronglySortedNoDup_ge_gt.
  + assumption.
  + eapply Permutation_Forall.
    * eassumption.
    * eapply Forall_impl with (2 := H0); intros. omega.
  + erewrite Permutation_length; [|eassumption]. constructor.
  + omega.
Qed.

(* Induction principle to recurse on a set of variables. *)
Fixpoint seen_rect' (MAX : nat) (P : list nat -> Type)
  (f : forall (seen : list nat)
    (REC : forall (x : nat), x < MAX -> ~ In x seen -> P (x :: seen)), P seen)
  (fuel : nat) (seen : list nat)
  (Hseen : NoDup seen /\ Forall (fun x => x < MAX) seen)
  (Hfuel : MAX <= fuel + length seen)
    {struct fuel} : P seen.
Proof.
  apply (f seen).
  intros x Hx HxIn.
  destruct Hseen as [HseenNoDup HseenMAX].
  destruct fuel as [|fuel].
  - exfalso. apply HxIn.
    apply NoDupFull_In with (M := MAX); assumption.
  - apply (seen_rect' MAX P f fuel (x :: seen)).
    repeat split; repeat constructor; try assumption.
    simpl in *. rewrite <- plus_n_Sm. assumption.
Qed.

Definition seen_rect (MAX : nat) (P : list nat -> Type)
  (f : forall (seen : list nat)
    (REC : forall (x : nat), x < MAX -> ~ In x seen -> P (x :: seen)), P seen)
  (seen : list nat)
  (Hrec : NoDup seen /\ Forall (fun x => x < MAX) seen) : P seen.
Proof.
  apply seen_rect' with (MAX := MAX) (fuel := MAX); trivial.
  apply le_plus_l.
Qed.

(** ========== Regular trees ========== *)

(* The [crush] tactic is intended to solve most arithmetic goals we will
   encounter. It fails if it cannot solve the goal. *)
Ltac make_one_simpl :=
  rewrite map_length in * ||
  rewrite app_length in * ||
  match goal with
  | t := _ : _ |- _ => subst t
  | H : _ <=? _ = true |- _ => apply leb_complete in H
  | H : _ <=? _ = false |- _ => apply leb_complete_conv in H
  | |- _ <=? _ = true => apply leb_correct
  | |- _ <=? _ = false => apply leb_correct_conv
  | |- _ ?= _ = Eq => apply Nat.compare_eq_iff
  | |- _ ?= _ = Lt => apply Nat.compare_lt_iff
  | |- _ ?= _ = Gt => apply Nat.compare_gt_iff
  | H : _ ?= _ = Eq |- _ => apply Nat.compare_eq in H
  | H : _ ?= _ = Lt |- _ => apply Nat.compare_lt_iff in H
  | H : _ ?= _ = Gt |- _ => apply Nat.compare_gt_iff in H
  end.
Ltac crush := repeat (try assumption; make_one_simpl; simpl in *); auto; omega.

(** Regular trees. *)

Section Rtree.
  Context (X : Set).

  Inductive t : Set :=
  | rParam (i : nat) (j : nat) : t
  | rNode (x : X) (sons : list t) : t
  | rRec (j : nat) (defs : list t) : t.

  Fixpoint t_ind' (P : list nat -> t -> Prop)
    (fParam : forall stk i j, P stk (rParam i j))
    (fNode : forall stk x sons, Forall (P stk) sons -> P stk (rNode x sons))
    (fRec : forall stk j defs, Forall (P (length defs :: stk)) defs -> P stk (rRec j defs))
      (stk : list nat) (tree : t) : P stk tree :=
    let REC := t_ind' P fParam fNode fRec in
    match tree with
    | rParam i j => fParam stk i j
    | rNode x sons => fNode stk x sons ((fix aux l : Forall _ l :=
        match l with
        | [] => Forall_nil _
        | hd :: tl => Forall_cons hd (REC stk hd) (aux tl)
        end) sons)
    | rRec j defs => fRec stk j defs ((fix aux l : Forall _ l :=
        match l with
        | [] => Forall_nil _
        | hd :: tl => Forall_cons hd (REC (length defs :: stk) hd) (aux tl)
        end) defs)
    end.

  (** Invariants about this structure. *)

  (* Indices are well-scoped. *)
  (* Consider [wf_rtree_idx stk tree].
     The tree [tree] has free variables described by [stk]. *)
  Inductive wf_rtree_idx : forall (stk : list nat), t -> Prop :=
  | wfrParam : forall stk i j
      (Hi : i < length stk) (Hj : j < safe_nth stk (i ; Hi)),
      wf_rtree_idx stk (rParam i j)
  | wfrNode : forall stk x sons,
      Forall (wf_rtree_idx stk) sons ->
      wf_rtree_idx stk (rNode x sons)
  | wfrRec : forall stk j defs,
      j < length defs -> Forall (wf_rtree_idx (length defs :: stk)) defs ->
      wf_rtree_idx stk (rRec j defs).

  (* Recs are productive. *)
  (* Consider [wf_rtree_rec ctx defs seen stk tree].
     The tree [rRec j defs] is closed under [ctx].
     The tree [tree] has free variables described by [stk ++ [length defs] ++ ctx]. *)
  Inductive wf_rtree_rec (ctx : list nat) (defs : list t) : forall (seen : list nat) (stk : list nat), t -> Prop :=
  | wrrParam_nonrec : forall seen stk i j, i <> length stk -> wf_rtree_rec ctx defs seen stk (rParam i j)
  | wrrParam_rec : forall seen stk i j (Hj : j < length defs),
      i = length stk -> ~ In j seen ->
      wf_rtree_rec ctx defs (j :: seen) [] (safe_nth defs (j ; Hj)) ->
      wf_rtree_rec ctx defs seen stk (rParam i j)
  | wrrNode : forall seen stk x sons, wf_rtree_rec ctx defs seen stk (rNode x sons)
  | wrrRec : forall seen stk j loc_defs (Hj : j < length loc_defs),
      wf_rtree_rec ctx defs seen (length loc_defs :: stk) (safe_nth loc_defs (j ; Hj)) ->
      wf_rtree_rec ctx defs seen stk (rRec j loc_defs).

  Inductive wf_rtree_rec' : forall (stk : list nat), t -> Prop :=
  | wrr'Param : forall stk i j, wf_rtree_rec' stk (rParam i j)
  | wrr'Node : forall stk x sons,
      Forall (wf_rtree_rec' stk) sons ->
      wf_rtree_rec' stk (rNode x sons)
  | wrr'Rec : forall stk j defs,
      j < length defs -> Forall (wf_rtree_rec' (length defs :: stk)) defs ->
      Foralli (fun i => wf_rtree_rec stk defs [i] []) defs ->
      wf_rtree_rec' stk (rRec j defs).

  Definition wf_rtree (stk : list nat) (tree : t) : Prop :=
    wf_rtree_idx stk tree /\ wf_rtree_rec' stk tree.

  (** Lifting and substitution. *)
  Definition lift_rtree_rec_body (F : nat -> nat -> t -> t)
    (depth : nat) (n : nat) (tree : t) : t :=
    match tree with
    | rParam i j => if Nat.leb depth i then rParam (i + n) j else rParam i j
    | rNode x sons => rNode x (List.map (F depth n) sons)
    | rRec j defs => rRec j (List.map (F (S depth) n) defs)
    end.

  Fixpoint lift_rtree_rec (depth : nat) (n : nat) (tree : t) {struct tree} : t :=
    lift_rtree_rec_body lift_rtree_rec depth n tree.
  Definition lift_rtree n tree := (lift_rtree_rec 0 n tree).

  (* Lifting preserves scoping of indices. *)
  Lemma wf_lift_rtree_idx :
    forall ctx newstk (newd := length newstk) tree stk (d := length stk),
      wf_rtree_idx (stk ++ ctx) tree ->
      wf_rtree_idx ((stk ++ newstk) ++ ctx) (lift_rtree_rec d newd tree).
  Proof.
    intros ctx newstk newd tree stk.
    induction stk, tree using t_ind'; intros d Hidx;
    inv Hidx; simpl in *.
    - destruct (Nat.leb_spec d i); econstructor.
      + destruct (Nat.le_exists_sub d i ltac:(crush)) as [i' [-> _]].
        assert (i' < length ctx) as Hi' by (clear Hj; crush).
        gen_safe_proof.
        replace (i' + d + newd) with (length (stk ++ newstk) + i') by crush.
        intros. erewrite safe_nth_app2.
        subst d. erewrite safe_nth_app2' in Hj.
        eassumption.
      + gen_safe_proof.
        rewrite app_assoc_reverse.
        intros. erewrite safe_nth_app1.
        erewrite safe_nth_app1 in Hj.
        eassumption.
    - constructor. apply Forall_map.
      apply Forall_Impl with (1 := H2) (2 := H).
    - constructor.
      + crush.
      + apply Forall_map. rewrite map_length.
        apply Forall_Impl with (1 := H4) (2 := H).
    Unshelve. all: try crush. clear Hj; crush.
  Qed.

  (* Lifting preserves the productivity of a particular Rec node. *)
  Lemma wf_lift_rtree_rec :
    forall defs (ddefs := length defs) seen,
    NoDup seen /\ Forall (fun x => x < length defs) seen ->
    forall ctx stk' (d' := length stk'),
    Forall (wf_rtree_idx (ddefs :: stk' ++ ctx)) defs ->
    forall newstk (newd := length newstk),
    forall tree stk (d := length stk),
    wf_rtree_idx (stk ++ ddefs :: stk' ++ ctx) tree ->
    wf_rtree_rec (stk' ++ ctx) defs seen stk tree ->
    let F := lift_rtree_rec (d + S d') newd in
    let F' := lift_rtree_rec (S d') newd in
      wf_rtree_rec ((stk' ++ newstk) ++ ctx) (map F' defs) seen stk (F tree).
  Proof.
    intros defs ddefs seen Hrec ctk stk' d' Hidx_defs newstk newd.
    pattern seen. refine (seen_rect ddefs _ _ seen Hrec); clear seen Hrec;
    intros seen REC. intros tree stk.
    induction stk, tree using t_ind';
    intros d Hidx_tree Hwf_tree F F';
    inv Hidx_tree; inv Hwf_tree; unfold F; simpl in *.
    - destruct (Nat.leb_spec (d + S d') i).
      + constructor. crush.
      + constructor. crush.
    - assert (d + S d' <=? length stk = false) as -> by crush.
      econstructor 2; trivial.
      erewrite safe_nth_map.
      apply REC; try eassumption.
      apply Forall_In with (1 := Hidx_defs).
      apply safe_nth_In.
    - constructor.
    - rename defs0 into locdefs.
      econstructor.
      erewrite safe_nth_map.
      eapply Forall_forall' in H.
      + rewrite map_length. apply H; try eassumption.
        apply Forall_In with (1 := H4). apply safe_nth_In.
      + apply safe_nth_In.
    Unshelve. all: crush.
  Qed.

  (* Lifting preserves the productivity of Rec nodes. *)
  Lemma wf_lift_rtree_rec' :
    forall ctx newstk (newd := length newstk) tree stk (d := length stk),
      wf_rtree_idx (stk ++ ctx) tree ->
      wf_rtree_rec' (stk ++ ctx) tree ->
      wf_rtree_rec' ((stk ++ newstk) ++ ctx) (lift_rtree_rec d newd tree).
  Proof.
    intros ctx newstk newd tree stk.
    induction stk, tree using t_ind'; intros d Hidx Hwf;
    inv Hidx; inv Hwf; simpl in *.
    - destruct (Nat.leb_spec d i); constructor.
    - constructor. apply Forall_map.
      apply Forall_forall; intros.
      apply Forall_forall' with (2 := H0) in H.
      apply Forall_forall' with (2 := H0) in H2.
      apply Forall_forall' with (2 := H0) in H3.
      auto.
    - constructor.
      + now rewrite map_length.
      + rewrite map_length. apply Forall_map.
        apply Forall_forall; intros.
        apply Forall_forall with (2 := H0) in H.
        apply Forall_forall with (2 := H0) in H4.
        apply Forall_forall with (2 := H0) in H6.
        auto.
      + apply Foralli_map.
        apply Foralli_impl with (2 := H7); intros.
        apply wf_lift_rtree_rec; trivial.
        * repeat split; repeat constructor; crush.
        * apply Forall_In with (1 := H4). assumption.
  Qed.

  Theorem wf_lift_rtree :
    forall ctx newstk (newd := length newstk) tree stk (d := length stk),
    wf_rtree (stk ++ ctx) tree ->
    wf_rtree ((stk ++ newstk) ++ ctx) (lift_rtree_rec d newd tree).
  Proof.
    intros ctx newstk newd tree stk d [Hidx Hwf].
    split.
    - now apply wf_lift_rtree_idx.
    - now apply wf_lift_rtree_rec'.
  Qed.

  (* A tree that has been lifted above a Rec is productive for this Rec, since
     it does not have any free variable referring to this Rec. *)
  Lemma wf_rtree_rec_deep :
    forall defs (ddefs := length defs) seen ctx stk' (d' := length stk')
      stk'' (d'' := length stk''),
    Forall (wf_rtree_idx (ddefs :: stk' ++ ctx)) defs ->
    forall tree stk (d := length stk),
    wf_rtree_idx (stk ++ ctx) tree ->
    wf_rtree_rec (stk' ++ ctx) defs seen (stk ++ stk'') (lift_rtree_rec d (d'' + S d') tree).
  Proof.
    intros defs ddefs seen ctx stk' d' stk'' d'' Hidx_defs.
    intros tree stk.
    induction stk, tree using t_ind'; intros d Hidx;
    inv Hidx; unfold lift_rtree; simpl in *.
    - destruct (Nat.leb_spec d i); constructor; crush.
    - constructor.
    - rename defs0 into locdefs.
      econstructor. erewrite safe_nth_map.
      gen_safe_proof. rewrite map_length.
      intros. eapply Forall_forall' in H.
      + apply H. eapply Forall_In.
        * eassumption.
        * apply safe_nth_In.
      + apply safe_nth_In.
    Unshelve. all: crush.
  Qed.

  Definition subst_rtree_rec_body (F : nat -> list t -> t -> t)
    (depth : nat) (sub : list t) (tree : t) : t :=
    match tree with
    | rParam i j =>
      match nat_compare depth i with
      | Eq => lift_rtree depth (rRec j sub)
      | Gt => rParam i j
      | Lt => rParam (pred i) j
      end
    | rNode x sons => rNode x (List.map (F depth sub) sons)
    | rRec j defs => rRec j (List.map (F (S depth) sub) defs)
    end.

  Fixpoint subst_rtree_rec (depth : nat) (sub : list t) (tree : t) {struct tree} : t :=
    subst_rtree_rec_body subst_rtree_rec depth sub tree.
  Definition subst_rtree sub tree := (subst_rtree_rec 0 sub tree).

  (* Substitution preserves scoping of indices. *)
  Lemma wf_subst_rtree_idx :
    forall ctx sub (dsub := length sub),
    Forall (wf_rtree_idx (dsub :: ctx)) sub ->
    forall tree stk (d := length stk),
      wf_rtree_idx (stk ++ dsub :: ctx) tree ->
      wf_rtree_idx (stk ++ ctx) (subst_rtree_rec d sub tree).
  Proof.
    intros ctx sub dsub Hidx_sub tree stk.
    induction stk, tree using t_ind'; intros d Hidx;
    inv Hidx; simpl in *.
    - destruct (Nat.compare_spec d i).
      + subst. subst d.
        constructor; rewrite map_length.
        * pose proof (safe_nth_app2' stk (dsub :: ctx) O).
          simpl in H. erewrite H in Hj; clear H; crush.
        * fold lift_rtree_rec. apply Forall_map.
          apply Forall_impl with (2 := Hidx_sub); intros.
          apply wf_lift_rtree_idx with (stk := [dsub]).
          assumption.
      + econstructor.
        destruct (Nat.le_exists_sub d (pred i) ltac:(crush)) as [i' [Hi' _]].
        assert (i = i' + S d) by crush.
        gen_safe_proof. rewrite Hi'; clear Hi'; subst i.
        intros. subst d. erewrite safe_nth_app2'.
        revert Hi Hj.
        replace (stk ++ dsub :: ctx) with ((stk ++ [dsub]) ++ ctx)
        by (repeat rewrite app_assoc_reverse; reflexivity).
        replace (i' + S (length stk)) with (i' + length (stk ++ [dsub]))
        by crush.
        intros. erewrite safe_nth_app2' in Hj.
        eassumption.
      + econstructor.
        erewrite safe_nth_app1.
        erewrite safe_nth_app1 in Hj.
        eassumption.
    - constructor. apply Forall_map.
      apply Forall_Impl with (1 := H2) (2 := H).
    - constructor.
      + crush.
      + apply Forall_map. rewrite map_length.
        apply Forall_Impl with (1 := H4) (2 := H).
    Unshelve.
      clear Hj; crush.
      clear Hi; crush.
      all: crush.
  Qed.

  Lemma wf_subst_rtree_rec :
    forall defs (ddefs := length defs) seen,
    NoDup seen /\ Forall (fun x => x < length defs) seen ->
    forall ctx sub (dsub := length sub),
    Forall (wf_rtree_idx (dsub :: ctx)) sub ->
    forall stk' (d' := length stk'),
    Forall (wf_rtree_idx (ddefs :: stk' ++ dsub :: ctx)) defs ->
    forall tree stk (d := length stk),
    wf_rtree_idx (stk ++ ddefs :: stk' ++ dsub :: ctx) tree ->
    wf_rtree_rec (stk' ++ dsub :: ctx) defs seen stk tree ->
    let F := subst_rtree_rec (d + S d') sub in
    let F' := subst_rtree_rec (S d') sub in
      wf_rtree_rec (stk' ++ ctx) (map F' defs) seen stk (F tree).
  Proof.
    intros defs ddefs seen Hrec ctx sub dsub Hidx_sub stk' d' Hidx_defs.
    pattern seen. refine (seen_rect ddefs _ _ seen Hrec); clear seen Hrec;
    intros seen REC. intros tree stk.
    induction stk, tree using t_ind';
    intros d Hidx Hwf F F';
    inv Hidx; inv Hwf; unfold F; simpl in *.
    - destruct (Nat.compare_spec (d + S d') i).
      + apply wf_rtree_rec_deep with (stk := []).
        * apply Forall_map. apply Forall_impl with (2 := Hidx_defs).
          intros. rewrite map_length.
          apply wf_subst_rtree_idx with (stk := ddefs :: stk'); assumption.
        * constructor; trivial.
          subst i. revert Hi Hj.
          replace (d + S d') with (length (stk ++ ddefs :: stk') + 0) by crush.
          replace (stk ++ ddefs :: stk' ++ dsub :: ctx)
          with ((stk ++ ddefs :: stk') ++ dsub :: ctx)
          by (repeat rewrite app_assoc_reverse; reflexivity).
          intros. erewrite safe_nth_app2 in Hj.
          assumption.
      + constructor. crush.
      + constructor. assumption.
    - assert (d + S d' ?= length stk = Gt) as -> by crush.
      econstructor 2; trivial.
      erewrite safe_nth_map.
      apply REC; try eassumption.
      apply Forall_In with (1 := Hidx_defs).
      apply safe_nth_In.
    - constructor.
    - rename defs0 into locdefs.
      econstructor.
      erewrite safe_nth_map.
      eapply Forall_forall' in H.
      + rewrite map_length. apply H; try eassumption.
        apply Forall_In with (1 := H4). apply safe_nth_In.
      + apply safe_nth_In.
    Unshelve. all: crush.
  Qed.

  (* Substitution preserves the productivity of Rec nodes. *)
  Lemma wf_subst_rtree_rec' :
    forall ctx sub (dsub := length sub),
      Forall (wf_rtree_idx (dsub :: ctx)) sub ->
      Forall (wf_rtree_rec' (dsub :: ctx)) sub ->
      Foralli (fun i => wf_rtree_rec ctx sub [i] []) sub ->
      forall tree stk (d := length stk),
      wf_rtree_idx (stk ++ dsub :: ctx) tree ->
      wf_rtree_rec' (stk ++ dsub :: ctx) tree ->
      wf_rtree_rec' (stk ++ ctx) (subst_rtree_rec d sub tree).
  Proof.
    intros ctx sub dsub Hidx_sub Hwf_sub Hwfi_sub tree stk.
    induction stk, tree using t_ind'; intros d Hidx Hwf;
    inv Hidx; inv Hwf; simpl in *.
    - destruct (Nat.compare_spec d i); constructor; fold lift_rtree_rec.
      + rewrite map_length. subst i.
        subst d. erewrite safe_nth_app2' with (n := O) (l1 := stk) in Hj.
        assumption.
      + apply Forall_map. apply Forall_forall; intros.
        apply Forall_forall' with (2 := H0) in Hidx_sub.
        apply Forall_forall' with (2 := H0) in Hwf_sub.
        rewrite map_length.
        apply wf_lift_rtree_rec' with (stk := [dsub]); assumption.
      + apply Foralli_map. apply Foralli_impl with (2 := Hwfi_sub); intros.
        apply wf_lift_rtree_rec with (stk' := []); trivial.
        * repeat split; repeat constructor; crush.
        * apply Forall_In with (1 := Hidx_sub). assumption.
    - constructor. apply Forall_map.
      apply Forall_forall; intros.
      apply Forall_forall' with (2 := H0) in H.
      apply Forall_forall' with (2 := H0) in H2.
      apply Forall_forall' with (2 := H0) in H3.
      auto.
    - constructor.
      + now rewrite map_length.
      + rewrite map_length. apply Forall_map.
        apply Forall_forall; intros.
        apply Forall_forall with (2 := H0) in H.
        apply Forall_forall with (2 := H0) in H4.
        apply Forall_forall with (2 := H0) in H6.
        auto.
      + apply Foralli_map.
        apply Foralli_impl with (2 := H7); intros.
        apply wf_subst_rtree_rec; trivial.
        * repeat split; repeat constructor; crush.
        * apply Forall_In with (1 := H4). assumption.
    Unshelve. all: crush.
  Qed.

  Theorem wf_subst_rtree :
    forall ctx sub (dsub := length sub),
    Forall (wf_rtree_idx (dsub :: ctx)) sub ->
    Forall (wf_rtree_rec' (dsub :: ctx)) sub ->
    Foralli (fun i => wf_rtree_rec ctx sub [i] []) sub ->
    forall tree stk (d := length stk),
    wf_rtree (stk ++ dsub :: ctx) tree ->
    wf_rtree (stk ++ ctx) (subst_rtree_rec d sub tree).
  Proof.
    intros ctx sub dsub Hidx_sub Hwf_sub Hwfi_sub tree stk d [Hidx Hwf].
    split.
    - now apply wf_subst_rtree_idx.
    - now apply wf_subst_rtree_rec'.
  Qed.

  (* Alternative formulation. *)
  Corollary wf_subst_rtree' :
    forall ctx sub (dsub := length sub) j,
      wf_rtree ctx (rRec j sub) ->
    forall tree stk (d := length stk),
    wf_rtree (stk ++ dsub :: ctx) tree ->
    wf_rtree (stk ++ ctx) (subst_rtree_rec d sub tree).
  Proof.
    intros ctx sub dsub j [Hidx_rec Hwf_rec].
    inv Hidx_rec; inv Hwf_rec.
    now apply wf_subst_rtree.
  Qed.

  (* Even more specialized. *)
  Corollary wf_subst_rtree'' :
    forall ctx sub (dsub := length sub) j,
      wf_rtree ctx (rRec j sub) ->
    forall (Hj : j < dsub),
      let tree := subst_rtree sub (safe_nth sub (j; Hj)) in
      wf_rtree ctx tree.
  Proof.
    intros ctx sub dsub j Hwf Hj tree.
    apply wf_subst_rtree' with (j := j) (stk := []).
    - assumption.
    - destruct Hwf as [Hidx Hwf]; inv Hidx; inv Hwf.
      split.
      + apply Forall_In with (1 := H3).
        apply safe_nth_In.
      + apply Forall_In with (1 := H5).
        apply safe_nth_In.
  Qed.

  (* === Expansion === *)

  Inductive rtree_bar : t -> Prop :=
  | rtree_bar_param : forall i j, rtree_bar (rParam i j)
  | rtree_bar_node : forall x sons, rtree_bar (rNode x sons)
  | rtree_bar_rec : forall j defs,
      (forall (Hj : j < length defs), rtree_bar (subst_rtree defs (safe_nth defs (j; Hj)))) ->
      rtree_bar (rRec j defs).

  Program Fixpoint expand_rec (tree : t)
    (tree_wf : exists ctx, wf_rtree ctx tree) (bar : rtree_bar tree) {struct bar} : t :=
    match tree with
    | rRec j defs =>
        let Hj : j < length defs := _ in
        let def := safe_nth defs (j; Hj) in
        let tree' := subst_rtree defs def in
          expand_rec tree' _ _
    | t => t
    end.

  (* Providing [Hj]. *)
  Next Obligation.
    destruct H as [Hidx _].
    inv Hidx.
    assumption.
  Defined.

  (* Proving the recursive argument is well-formed. *)
  Next Obligation.
    rename tree_wf into ctx.
    exists ctx. apply wf_subst_rtree''.
    assumption.
  Defined.

  (* Providing a termination certificate for the recursive argument. *)
  Next Obligation.
    simpl.
    inv bar.
    apply H1.
  Defined.

  Definition expand (tree : t) (tree_wf : exists ctx, wf_rtree ctx tree) : t.
  Proof.
    refine (expand_rec tree tree_wf _).
    destruct tree; constructor.
    intros.
  Defined.

  (* TODO Try to define an equivalent [expand'] which maintains a stack of
     explicit substitutions, and use it to derive the termination certificate? *)

End Rtree.