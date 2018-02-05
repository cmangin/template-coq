Require Import List Program Arith Omega.

(** Common library. *)

Notation "( x ; y )" := (exist _ x y).

Program Fixpoint safe_nth {A} (l : list A) (n : nat | n < length l) : A :=
  match l with
  | nil => !
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth tl n
    end
  end.

Next Obligation.
  simpl in H. inversion H.
Qed.
Next Obligation.
  simpl in H. auto with arith.
Qed.

Ltac gen_safe_proof :=
  match goal with
  |- context [safe_nth _ (_ ; ?H)] =>
      tryif is_var H then fail else
        let Hs := fresh "Hs" in
        generalize H as Hs
  end.

(* We could do without [proof_irrelevance]. *)
Lemma safe_nth_app2 {A : Type} (l1 l2 : list A) (n : nat) H1 H2 :
  safe_nth (l1 ++ l2) (length l1 + n ; H1) = safe_nth l2 (n ; H2).
Proof.
  induction l1; simpl in *.
  - f_equal. f_equal. apply proof_irrelevance.
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

Inductive Foralli_aux {A : Type} (P : nat -> A -> Prop) : nat -> list A -> Prop :=
| Foralli_nil : forall (n : nat), Foralli_aux P n []
| Foralli_cons : forall (x : A) (l : list A) (i : nat),
    P i x -> Foralli_aux P (S i) l -> Foralli_aux P i (x :: l).
Definition Foralli {A} P (l : list A) := (Foralli_aux P 0 l).

Lemma safe_nth_Forall {A} (P : A -> Prop) (l : list A) (n : nat | n < length l) :
  Forall P l -> P (safe_nth l n).
Proof.
  intros H; revert n. induction H; intros [n Hn]; [inversion Hn|].
  now destruct n; simpl.
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

Lemma Forall_app {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; simpl; intros.
  - easy.
  - inversion H; subst.
    destruct (IHl1 H3).
    now repeat constructor.
Qed.

Lemma Forall_map {A B : Type} {P : B -> Prop} {f : A -> B} {l : list A} :
  Forall (fun x => P (f x)) l ->
  Forall P (map f l).
Proof.
  induction 1; now constructor.
Qed.

Lemma Forall_In' {A : Type} {P : A -> Prop} {l : list A} {x : A} :
  Forall P l -> In x l -> P x.
Proof.
  intros.
  eapply Forall_forall; eassumption.
Qed.

Lemma Forall_Impl {A : Type} {P Q : A -> Prop} {l : list A} :
  Forall P l -> Forall (fun t => P t -> Q t) l -> Forall Q l.
Proof.
  induction 1; constructor.
  - inversion H1; subst. auto.
  - inversion H1; subst; auto.
Qed.

Lemma Foralli_map {A B : Type} {P : nat -> B -> Prop} {f : A -> B} {l : list A} :
  Foralli (fun i x => P i (f x)) l ->
  Foralli P (map f l).
Proof.
  unfold Foralli. generalize 0.
  induction 1; now constructor.
Qed.

Lemma Foralli_aux_impl {A : Type} (P Q : nat -> A -> Prop) {l : list A} {n : nat} :
(forall i a, i < n + length l -> P i a -> Q i a) -> Foralli_aux P n l -> Foralli_aux Q n l.
Proof.
  induction 2; constructor.
  - apply H; simpl. omega. assumption.
  - apply IHForalli_aux. intros.
    apply H. simpl. omega. assumption.
Qed.

Lemma Foralli_impl {A : Type} (P Q : nat -> A -> Prop) {l : list A} :
(forall i a, i < length l -> P i a -> Q i a) -> Foralli P l -> Foralli Q l.
Proof.
  rewrite <- (plus_O_n (length l)).
  apply Foralli_aux_impl.
Qed.

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
  - inversion H1; now subst.
  - inversion H1; subst; clear H1; simpl in *.
    inversion H2; subst; clear H2; simpl in *.
    specialize (fun H => IHStronglySorted (length l) ltac:(assumption) H (le_n _)).
    assert (l = rseq (length l)) as Hl.
    { apply IHStronglySorted.
      apply Forall_forall; intros.
      pose proof (Forall_In' H0 H1).
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
  - inversion H1; subst; clear H1. specialize (IHStronglySorted H5).
    constructor.
    + assumption.
    + apply Forall_forall; intros.
      assert (a <> x).
      { contradict H4; now subst. }
      apply Forall_In' with (2 := H1) in H0; simpl in H0.
      apply leb_complete in H0. omega.
Qed.

Lemma NoDupFull_In : forall l M j,
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
    (fRec : forall stk j defs, Forall (P (j :: stk)) defs -> P stk (rRec j defs))
      (stk : list nat) (tree : t) : P stk tree.
  Proof.
    destruct tree.
    - apply fParam.
    - apply fNode.
      revert sons; fix aux 1; destruct sons.
      + constructor.
      + constructor.
        * apply t_ind'; assumption.
        * apply aux.
    - apply fRec.
      revert defs; fix aux 1; destruct defs.
      + constructor.
      + constructor.
        * apply t_ind'; assumption.
        * apply aux.
  Defined.

  (** Invariants about this structure. *)
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
      wf_rtree_rec ctx defs seen (j :: stk) (safe_nth loc_defs (j ; Hj)) ->
      wf_rtree_rec ctx defs seen stk (rRec j loc_defs).

  (* Indices are within range and Rec nodes are well-formed. *)
  (* Consider [wf_rtree_aux stk tree].
     The tree [tree] has free variables described by [stk]. *)
  Inductive wf_rtree_aux : forall (stk : list nat), t -> Prop :=
  | wfrParam : forall stk i j
      (Hi : i < length stk) (Hj : j < safe_nth stk (i ; Hi)),
      wf_rtree_aux stk (rParam i j)
  | wfrNode : forall stk x sons,
      Forall (wf_rtree_aux stk) sons ->
      wf_rtree_aux stk (rNode x sons)
  | wfrRec : forall stk j defs,
      j < length defs -> Forall (wf_rtree_aux (j :: stk)) defs ->
      Foralli (fun i => wf_rtree_rec stk defs [i] []) defs ->
      wf_rtree_aux stk (rRec j defs).
  Definition wf_rtree tree := (wf_rtree_aux [] tree).

(*
  Fixpoint t_ind_wf (P : list nat -> t -> Prop)
    (fParam : forall stk i j (Hi : i < length stk) (Hj : j < safe_nth stk (i ; Hi)),
      P stk (rParam i j))
    (fNode : forall stk x sons,
      Forall (wf_rtree_aux stk) sons ->
      Forall (P stk) sons ->
      P stk (rNode x sons))
    (fRec : forall stk j defs (Hj : j < length defs),
      Forall (wf_rtree_aux (j :: stk)) defs ->
      Foralli (fun i => wf_rtree_rec stk defs [i] []) defs ->
      Forall (P (j :: stk)) defs -> P stk (rRec j defs))
    (stk : list nat) (tree : t) : wf_rtree_aux stk tree -> P stk tree.
  Proof.
    destruct tree; intros Hwf; inversion Hwf; subst; clear Hwf.
    - eapply fParam; eassumption.
    - apply fNode; try assumption.
      induction sons; [constructor|].
      inversion H1; subst; clear H1.
      constructor.
      + apply t_ind_wf; assumption.
      + apply IHsons; assumption.
    - apply fRec; try assumption.
      clear H1 H4.
      induction defs; [constructor|].
      inversion H3; subst; clear H3.
      constructor.
      + apply t_ind_wf; assumption.
      + apply IHdefs; assumption.
  Defined.
*)

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

  Fixpoint wf_lift_rtree_rec' (f : nat) :
    forall ctx tree stk defs seen stk' newstk d d' newd,
    NoDup seen /\ Forall (fun x => x < length defs) seen ->
    f + length seen >= length defs ->
    d = length stk ->
    d' = length stk' ->
    newd = length newstk ->
    wf_rtree_rec (stk' ++ ctx) defs seen stk tree ->
    let F := lift_rtree_rec (d + S d') newd in
    let F' := lift_rtree_rec (S d') newd in
    wf_rtree_rec ((stk' ++ newstk) ++ ctx) (map F' defs) seen stk (F tree).
  Proof.
    intros ctx tree stk.
    induction stk, tree using t_ind'; intros defs' seen stk' newstk d d' newd Hseen Hf Hd Hd' Hnewd Hwf;
    inversion Hwf; subst; clear Hwf; simpl in *.
    - destruct (length stk + S (length stk') <=? i) eqn:?.
      + unshelve econstructor. apply leb_complete in Heqb. omega.
      + econstructor. assumption.
    - assert (length stk + S (length stk') <=? length stk = false) as ->.
      { apply leb_correct_conv. omega. }
      unshelve econstructor 2; auto.
      + now rewrite map_length.
      + gen_safe_proof. intros.
        unshelve erewrite safe_nth_map.
        { assumption. }
        destruct f.
        { exfalso. clear H5 Hs. revert j Hj seen Hseen Hf H4; clear; simpl; intros.
          destruct Hseen. apply H4. apply NoDupFull_In with (M := length defs'); auto. }
        assert (f + length (j :: seen) >= length defs') as Hf'.
        { simpl. omega. }
        assert (NoDup (j :: seen) /\ Forall (fun x => x < length defs') (j :: seen)) as Hseen'.
        { destruct Hseen; split; simpl; constructor; auto. }
        specialize (wf_lift_rtree_rec' f ctx (safe_nth defs' (j; Hj)) [] defs' (j :: seen)
          stk' newstk _ _ _ Hseen' Hf' eq_refl eq_refl eq_refl).
        apply wf_lift_rtree_rec'. assumption.
    - constructor.
    - unshelve econstructor.
      { now rewrite map_length. }
      unshelve erewrite safe_nth_map.
      { assumption. }
    match goal with
    | H : Forall ?P ?l |- _ => pose proof (iff_and (Forall_forall P l)) as Htmp
    end.
    destruct Htmp as [Htmp _].
    specialize (Htmp H); clear H.
    specialize (fun x H => Htmp x H defs' seen stk' newstk _ _ _ Hseen Hf eq_refl eq_refl eq_refl).
    apply Htmp; trivial.
    apply safe_nth_In.
  Qed.


  Theorem wf_lift_rtree_rec :
    forall ctx defs tree stk newstk i,
    i < length defs ->
    wf_rtree_rec (stk ++ ctx) defs [i] [] tree ->
    let F := lift_rtree_rec (S (length stk)) (length newstk) in
    wf_rtree_rec ((stk ++ newstk) ++ ctx) (map F defs) [i] [] (F tree).
  Proof.
    intros.
    assert (pred (length defs) + length [i] >= length defs) as Hf.
    { simpl. omega. }
    assert (NoDup [i] /\ Forall (fun x => x < length defs) [i]) as Hseen.
    { split; repeat constructor; auto. }
    eapply (wf_lift_rtree_rec' (pred (length defs)) ctx tree [] defs [i] stk newstk _ _ _
      Hseen Hf eq_refl eq_refl eq_refl).
    assumption.
  Qed.

  Lemma wf_lift_rtree_aux :
    forall tree stk newstk ctx d newd,
    d = length stk ->
    newd = length newstk ->
    wf_rtree_aux (stk ++ ctx) tree ->
    wf_rtree_aux ((stk ++ newstk) ++ ctx) (lift_rtree_rec d newd tree).
  Proof.
    intros tree stk.
    induction stk, tree using t_ind'; intros newstk ctx d newd Hd Hnewd Hwf;
    inversion Hwf; subst; clear Hwf; simpl in *.
    - destruct (length stk <=? i) eqn:?.
      + apply leb_complete in Heqb.
        unshelve econstructor.
        { clear Hj. repeat rewrite app_length.
          rewrite app_length in Hi.
          rewrite Nat.add_shuffle0.
          apply plus_lt_compat_r. assumption. }
        destruct (Nat.le_exists_sub _ _ Heqb) as [i' [H _]]; subst.
        gen_safe_proof.
        assert (i' < length ctx) as Hi'.
        { clear Hj. rewrite app_length in Hi. rewrite plus_comm in Hi.
          apply plus_lt_reg_l in Hi. assumption. }
        rewrite (Nat.add_comm i' (length stk)). rewrite <- Nat.add_assoc.
        rewrite app_assoc_reverse.
        intros.
        unshelve erewrite safe_nth_app2.
        { rewrite app_length. rewrite plus_comm. auto with arith. }
        unshelve erewrite safe_nth_app2'.
        { assumption. }
        unshelve erewrite safe_nth_app2' in Hj; assumption.
      + assert (i < length stk).
        { now apply leb_complete_conv. }
        clear Heqb.
        unshelve econstructor.
        { rewrite app_assoc_reverse. rewrite app_length.
          now apply Nat.lt_lt_add_r. }
        unshelve erewrite safe_nth_app1.
        { rewrite app_length. now apply lt_plus_trans. }
        unshelve erewrite safe_nth_app1.
        { assumption. }
        unshelve erewrite safe_nth_app1 in Hj.
        { assumption. }
        assumption.
  - constructor.
    apply Forall_map.
    apply Forall_Impl with (1 := H2).
    apply Forall_Impl with (1 := H).
    apply Forall_forall. auto.
  - set (F := lift_rtree_rec (S (length stk)) (length newstk)) in *.
    constructor.
    + now rewrite map_length.
    + apply Forall_map. apply Forall_Impl with (1 := H4).
      apply Forall_Impl with (1 := H). apply Forall_forall.
      intros. now apply H1.
    + apply Foralli_map.
      apply Foralli_impl with (2 := H5).
      intros. apply wf_lift_rtree_rec; assumption.
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

  Lemma wf_subst_rtree_rec : forall tree nb_recs depth J sub,
    depth = length nb_recs -> J = length sub ->
    Forall (wf_rtree_aux (nb_recs ++ [J])) sub -> wf_rtree_aux (nb_recs ++ [J]) tree ->
    wf_rtree_aux nb_recs (subst_rtree_rec depth sub tree).
  Proof. Admitted.

  Theorem wf_subst_rtree : forall nb_recs j sub tree,
    Forall (wf_rtree_aux (j :: nb_recs)) sub -> wf_rtree_aux (j :: nb_recs) tree ->
    wf_rtree_aux nb_recs (subst_rtree sub tree).
  Admitted.

  (** Constructors. *)
  Definition mk_rec_calls (i : nat) : list t :=
    let fix aux (k : nat) (acc : list t) :=
      match k with
      | O => acc
      | S k' => aux k' (rParam 0 k' :: acc)
      end
    in aux i [].

  Definition mk_node (x : X) (sons : list t) : t := rNode x sons.

  Axiom R : t -> t -> Prop.

  Program Fixpoint expand (tree : t) (tree_wf : wf_rtree tree) {measure tree (R)} : t :=
    match tree with
    | rRec j defs =>
        let def := safe_nth defs (exist _ j _) in
        let tree' := subst_rtree defs def in
        expand tree' _
    | t => t
    end.

  Next Obligation.
    now inversion tree_wf.
  Qed.

  Next Obligation.
    inversion tree_wf; subst.
    eapply wf_subst_rtree.
    - eassumption.
    - apply safe_nth_Forall. assumption.
  Qed.

  Next Obligation. Admitted.

  Next Obligation. Admitted.

End Rtree.