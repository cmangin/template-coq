Require Import List Program Arith Omega.

(** ========== Common library ========== *)

Arguments skipn [_] !n !l.
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

Lemma Forall_snoc {A : Type} {P : A -> Prop} (x : A) {l : list A} :
  Forall P l -> P x -> Forall P (l ++ [x]).
Proof.
  induction 1; constructor; auto.
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

Lemma le_n_irrelevant {n : nat} (p : n <= n) : p = le_n n.
Proof.
  enough (forall m (q : n <= m) (e : n = m), eq_ind _ _ p _ e = q -> p = le_n _).
  { apply (H n p eq_refl eq_refl). }
  intros m q.
  destruct q; intros e.
  - rewrite Eqdep_dec.UIP_refl_nat with n e. now intros.
  - exfalso. subst. now elim Nat.nle_succ_diag_l with m.
Qed.

Definition noConf_nat_S {n m : nat} : S n = S m -> n = m.
Proof.
  now inversion 1.
Qed.

Lemma noConf_nat_S_f_equal {n m : nat} (p : S n = S m) :
  p = f_equal S (noConf_nat_S p).
Proof.
  apply UIP_nat.
Qed.

Fixpoint le_irrelevant {n m : nat} (p q : n <= m) {struct p} : p = q.
Proof.
  destruct p.
  - symmetry. apply le_n_irrelevant.
  - enough (forall m' (q' : n <= m') (e : S m = m'), eq_ind _ _ q _ e = q' -> le_S n m p = q).
    { apply (H (S m) q eq_refl eq_refl). }
    intros m' q'.
    destruct q'; intros e.
    + exfalso. subst. now elim Nat.nle_succ_diag_l with m.
    + rewrite noConf_nat_S_f_equal with e.
      generalize (noConf_nat_S e); clear e; intros e.
      destruct e. simpl. intros ->.
      f_equal. apply le_irrelevant.
Qed.

Lemma lt_irrelevant {n m : nat} (p q : n < m) : p = q.
Proof.
  apply le_irrelevant.
Qed.

Ltac prove_lt_irrelevance := apply lt_irrelevant.
Ltac unify_lt_proofs :=
  repeat match goal with
  | H1 : ?x < ?y, H2 : ?x < ?y |- _ =>
      revert dependent H2; intros H2;
      assert (H1 = H2) as <- by prove_lt_irrelevance
  end.

(* A few lemmas about [safe_nth] and standard list definitions. *)

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

Lemma safe_nth_app2 {A : Type} (l1 l2 : list A) (n : nat) (Hn : n >= length l1) H1 H2 :
  safe_nth (l1 ++ l2) (n ; H1) = safe_nth l2 (n - length l1 ; H2).
Proof.
  revert n Hn H1 H2.
  induction l1; intros.
  - f_equal. revert H2. rewrite <- minus_n_O.
    intros. now unify_lt_proofs.
  - destruct n; simpl.
    + inversion Hn.
    + unshelve erewrite IHl1; auto with arith.
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

(* A few lemmas about [safe_nth], [Forall], [skipn] and [firstn]. *)

Lemma safe_nth_Forall {A} (P : A -> Prop) (l : list A) (n : nat | n < length l) :
  Forall P l -> P (safe_nth l n).
Proof.
  intros H.
  eapply Forall_In.
  - eassumption.
  - apply safe_nth_In.
Qed.

Lemma safe_nth_Foralli_aux {A} (P : nat -> A -> Prop) (l : list A)
  (i : nat)
  (n : nat) (Hn : n < length l) :
  Foralli_aux P i l -> P (i + n) (safe_nth l (n; Hn)).
Proof.
  intros Hl; revert n Hn.
  induction Hl; intros [|n'] Hn'; simpl in *.
  - inversion Hn'.
  - inversion Hn'.
  - now rewrite <- plus_n_O.
  - rewrite <- plus_n_Sm.
    apply IHHl.
Qed.

Lemma safe_nth_Foralli {A} (P : nat -> A -> Prop) (l : list A)
  (n : nat) (Hn : n < length l) :
  Foralli P l -> P n (safe_nth l (n; Hn)).
Proof.
  intros.
  rewrite <- plus_O_n with (n := n) at 1.
  now apply safe_nth_Foralli_aux.
Qed.

Lemma skipn_length_le {A : Type} (l : list A) {n : nat} :
  n <= length l -> length (skipn n l) = length l - n.
Proof.
  revert n.
  induction l as [|x l]; intros [|n] **; trivial; simpl.
  apply IHl. simpl in H. omega.
Qed.

Lemma skipn_app_1 {A : Type} (n : nat) (l1 l2 : list A) :
  n <= length l1 -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  revert n.
  induction l1; intros [|n] **; simpl in *; auto with arith.
  inv H.
Qed.

Lemma skipn_app_2 {A : Type} (n : nat) (l1 l2 : list A) :
  skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof.
  now induction l1.
Qed.

Lemma skipn_skipn {A : Type} (n m : nat) (l : list A) :
  skipn n (skipn m l) = skipn (n + m) l.
Proof.
  revert n m.
  induction l; intros [|n] [|m]; simpl; auto.
  - now rewrite <- plus_n_O.
  - rewrite <- plus_n_Sm.
    apply IHl.
Qed.

Lemma skipn_firstn {A : Type} (n m : nat) (l : list A) :
  skipn n (firstn m l) = firstn (m - n) (skipn n l).
Proof.
  revert n m.
  induction l; intros [|n] [|m]; simpl; auto.
  now rewrite firstn_nil.
Qed.

Lemma safe_nth_skipn {A : Type} (n i : nat) (l : list A) (H : i >= n) H1 H2:
  safe_nth l (i; H1) = safe_nth (skipn n l) (i - n; H2).
Proof.
  revert n i H H1 H2.
  induction l; intros.
  - inversion H1.
  - destruct i, n; simpl in *; auto.
    + inversion H.
    + now unify_lt_proofs.
    + erewrite IHl; auto with arith.
Qed.

Lemma safe_nth_firstn {A : Type} (n i : nat) (l : list A) (H : i < n) H1 H2:
  safe_nth l (i; H1) = safe_nth (firstn n l) (i; H2).
Proof.
  revert n i H H1 H2.
  induction l; intros.
  - inversion H1.
  - destruct i, n; simpl in *; auto.
    + inversion H.
    + now unify_lt_proofs.
    + erewrite IHl; auto with arith.
Qed.

Lemma safe_nth_trans {A : Type} (n m : nat) (l : list A) (H : n = m) H1 H2:
  safe_nth l (n; H1) = safe_nth l (m; H2).
Proof.
  revert H2. destruct H.
  intros. simpl in H1. unify_lt_proofs.
  reflexivity.
Qed.

(** === Map with the length. *)

Section map_with_length.
  Context {A B : Type}.
  Context (f : nat -> A -> B).

  Fixpoint map_with_length (l : list A) : list B :=
    match l with
    | [] => []
    | hd :: tl => f (length l) hd :: map_with_length tl
    end.

  Lemma map_with_length_length (l : list A) : length (map_with_length l) = length l.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma map_with_length_skipn (l : list A) (i : nat) (Hi : i <= length l) :
    skipn i (map_with_length l) = map_with_length (skipn i l).
  Proof.
    revert i Hi.
    induction l; intros [|i]; intros; auto.
    apply IHl. auto with arith.
  Qed.

  Lemma safe_nth_map_with_length (l : list A) (n : nat) H1 H2 :
    safe_nth (map_with_length l) (n; H1) = f (length l - n) (safe_nth l (n; H2)).
  Proof.
    revert n H1 H2.
    induction l; intros [|n] H1 H2; try solve [inversion H1]; auto; simpl.
    apply IHl.
  Qed.
End map_with_length.

Lemma map_with_length_ext {A B : Type} (f g : nat -> A -> B) (H : forall n x, f n x = g n x)
  (l : list A) :
  map_with_length f l = map_with_length g l.
Proof.
  induction l; simpl; auto.
  f_equal; auto.
Qed.

Lemma map_map_with_length {A B C : Type} (f : nat -> A -> B) (g : B -> C) (l : list A) :
  map g (map_with_length f l) = map_with_length (fun n x => g (f n x)) l.
Proof.
  induction l; simpl; auto.
  now rewrite IHl.
Qed.

Lemma map_with_length_map {A B C : Type} (f : A -> B) (g : B -> C) (l : list A) :
  map_with_length (fun _ x => g x) (map f l) = map (fun x => g (f x)) l.
Proof.
  induction l; simpl; auto.
  now rewrite IHl.
Qed.

Lemma map_with_length_map_ext {A B : Type} (f : nat -> A -> B) (g : A -> B)
  (H : forall n x, f n x = g x) (l : list A) :
  map_with_length f l = map g l.
Proof.
  induction l; simpl; auto.
  f_equal; auto.
Qed.

Lemma map_id {A : Type} (l : list A) :
  map id l = l.
Proof.
  induction l; simpl; f_equal; auto.
Qed.

(** ========== Regular trees ========== *)

(* The [crush] tactic is intended to solve most arithmetic goals we will
   encounter. It fails if it cannot solve the goal. *)
Ltac make_one_simpl :=
  autorewrite with rtree in * ||
  autounfold with rtree in * ||
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
Ltac crush := repeat (try eassumption; try make_one_simpl; simpl in *); auto; abstract omega.

Hint Rewrite map_length app_length : rtree.
Hint Rewrite @skipn_length_le firstn_length_le using crush : rtree.
Hint Rewrite @map_with_length_length : rtree.
Hint Rewrite @map_with_length_skipn using crush : rtree.

Ltac reset id :=
  let id' := constr:(id) in
  let body := eval unfold id in id' in
  subst id; set (id := body) in *.

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

  Fixpoint t_ind'' (P : t -> Prop)
    (fParam : forall i j, P (rParam i j))
    (fNode : forall x sons, Forall P sons ->  P (rNode x sons))
    (fRec : forall j defs, Forall P defs -> P (rRec j defs))
      (tree : t) : P tree :=
    let REC := t_ind'' P fParam fNode fRec in
    match tree with
    | rParam i j => fParam i j
    | rNode x sons => fNode x sons ((fix aux l : Forall _ l :=
        match l with
        | [] => Forall_nil _
        | hd :: tl => Forall_cons hd (REC hd) (aux tl)
        end) sons)
    | rRec j defs => fRec j defs ((fix aux l : Forall _ l :=
        match l with
        | [] => Forall_nil _
        | hd :: tl => Forall_cons hd (REC hd) (aux tl)
        end) defs)
    end.

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

  (* A few permutation lemmas. *)
  Lemma lift0 :
    forall tree k,
    lift_rtree_rec k 0 tree = tree.
  Proof.
    induction tree using t_ind''; intros; simpl in *;
    only 2-3: (f_equal; rewrite <- map_id;
      apply map_ext_in; intros tree HtreeIn; apply (Forall_In H HtreeIn)).
    destruct (Nat.leb_spec k i); f_equal; crush.
  Qed.

  Lemma simpl_lift :
    forall tree i p k n,
    i <= k + n ->
    k <= i ->
    lift_rtree_rec i p (lift_rtree_rec k n tree) = lift_rtree_rec k (p + n) tree.
  Proof.
    induction tree using t_ind''; intros; simpl in *;
    only 2-3: (f_equal; rewrite !map_map; apply map_ext_in; intros tree HtreeIn).
    - repeat (try (f_equal; crush);
      match goal with
      | |- context [if ?a <=? ?b then _ else _] => destruct (Nat.leb_spec a b)
      | |- context [match ?a ?= ?b with _ => _ end] => destruct (Nat.compare_spec a b)
      end; subst; simpl; unfold subst_rtree, lift_rtree).
    - apply (Forall_In H HtreeIn); crush.
    - apply (Forall_In H HtreeIn); crush.
  Qed.

  Lemma commut_lift_subst :
    forall tree sub k n p,
    k <= p ->
    lift_rtree_rec k n (subst_rtree_rec p sub tree) =
    subst_rtree_rec (n + p) sub (lift_rtree_rec k n tree).
  Proof.
    induction tree using t_ind''; intros; simpl in *;
    only 2-3: (f_equal; rewrite !map_map; apply map_ext_in; intros tree HtreeIn).
    - repeat (try (f_equal; crush);
      match goal with
      | |- context [if ?a <=? ?b then _ else _] => destruct (Nat.leb_spec a b)
      | |- context [match ?a ?= ?b with _ => _ end] => destruct (Nat.compare_spec a b)
      end; subst; simpl; unfold subst_rtree, lift_rtree).
      f_equal; rewrite map_map; apply map_ext; intros tree.
      apply simpl_lift; crush.
    - apply (Forall_In H HtreeIn); crush.
    - rewrite plus_n_Sm. apply (Forall_In H HtreeIn); crush.
  Qed.

  Lemma simpl_subst :
    forall tree sub n k p,
    p <= n + k ->
    k <= p ->
    subst_rtree_rec p sub (lift_rtree_rec k (S n) tree) =
    lift_rtree_rec k n tree.
  Proof.
    induction tree using t_ind''; intros; simpl in *;
    only 2-3: (f_equal; rewrite !map_map; apply map_ext_in; intros tree HtreeIn).
    - repeat (try (f_equal; crush);
      match goal with
      | |- context [if ?a <=? ?b then _ else _] => destruct (Nat.leb_spec a b)
      | |- context [match ?a ?= ?b with _ => _ end] => destruct (Nat.compare_spec a b)
      end; subst; simpl; unfold subst_rtree, lift_rtree).
    - apply (Forall_In H HtreeIn); crush.
    - apply (Forall_In H HtreeIn); crush.
  Qed.

  Lemma distr_subst :
    forall tree P N p n,
    subst_rtree_rec (p + n) P (subst_rtree_rec p N tree) =
    subst_rtree_rec p (map (subst_rtree_rec (S n) P) N) (subst_rtree_rec (S (p + n)) P tree).
  Proof.
    induction tree using t_ind''; intros; simpl in *;
    only 2-3: (f_equal; rewrite !map_map; apply map_ext_in; intros tree HtreeIn).
    - destruct (Nat.compare_spec p i); subst; simpl.
      + destruct i; subst.
        * simpl; unfold lift_rtree; simpl.
          f_equal; rewrite !map_map; apply map_ext; intros tree.
          rewrite commut_lift_subst; crush.
        * assert (S i + n ?= i = Gt) as -> by crush.
          simpl. assert (i ?= i = Eq) as -> by crush.
          unfold lift_rtree; simpl.
          f_equal; rewrite !map_map; apply map_ext; intros tree.
          rewrite commut_lift_subst; f_equal; crush.
      + destruct (Nat.compare_spec (p + n) (pred i)).
        * destruct i; try crush.
          assert (p + n ?= i = Eq) as -> by crush.
          unfold lift_rtree; simpl.
          f_equal; rewrite !map_map; apply map_ext; intros tree.
          rewrite simpl_subst; crush.
        * destruct i; try crush.
          assert (p + n ?= i = Lt) as -> by crush.
          simpl. assert (p ?= i = Lt) as -> by crush.
          crush.
        * destruct i; try crush.
          assert (p + n ?= i = Gt) as -> by crush.
          simpl. assert (p ?= S i = Lt) as -> by crush.
          crush.
      + assert (p + n ?= i = Gt) as -> by crush.
        destruct i.
        * simpl. assert (p ?= 0 = Gt) as -> by crush.
          crush.
        * assert (p + n ?= i = Gt) as -> by crush.
          simpl. assert (p ?= S i = Gt) as -> by crush.
          crush.
    - apply (Forall_In H HtreeIn).
    - apply (Forall_In H HtreeIn _ _ (S p)).
  Qed.

  (** Invariants about this structure. *)

  (* We will consider any tree under a context made of a list of free variables,
     and then a list of definitions and seen variables. *)
  Definition Context : Set := list nat.
  Definition Stack : Set := list (list t * list nat).

  (* We can convert a Stack to a Context simply by forgetting every information
     except the number of mutally recursive definitions. *)
  Definition Context_of_Stack : Stack -> Context := map (fun '(x, _) => length x).
  Hint Unfold Context_of_Stack : rtree.

  Definition map_Stack (f : nat -> t -> t) : Stack -> Stack :=
    map_with_length (fun m '(defs, seen) =>
      (map (f m) defs, seen)).
  Hint Unfold map_Stack : rtree.

  Lemma map_Stack_seen :
    forall f stk i (Hi : i < length stk) (Hi' : i < length (map_Stack f stk)),
      snd (safe_nth (map_Stack f stk) (i; Hi')) = snd (safe_nth stk (i; Hi)).
  Proof.
    intros.
    unfold map_Stack.
    rewrite safe_nth_map_with_length with (H2 := Hi).
    destruct safe_nth. reflexivity.
  Qed.

  Lemma map_Stack_safe_nth f g stk i (Hi : i < length stk) (Hi' : i < length (map_Stack f stk)) :
      (forall x, g x = f (length stk - i) x) ->
      fst (safe_nth (map_Stack f stk) (i; Hi')) = map g (fst (safe_nth stk (i; Hi))).
  Proof.
    intros.
    unfold map_Stack.
    rewrite safe_nth_map_with_length with (H2 := Hi).
    destruct safe_nth.
    now apply map_ext.
  Qed.

  Lemma Context_of_map_Stack f stk :
    Context_of_Stack (map_Stack f stk) = Context_of_Stack stk.
  Proof.
    unfold Context_of_Stack, map_Stack.
    rewrite map_map_with_length.
    apply map_with_length_map_ext.
    intros n0 [defs seen].
    now rewrite map_length.
  Qed.

  Lemma lt_in_Ctx {ctx : Context} {stk : Stack} {i} (Hi : i < length stk + length ctx)
    (Hi' : length stk <= i) : i - length stk < length ctx.
  Proof. omega. Qed.

  Inductive wf_rtree : forall (ctx : Context) (stk : Stack), t -> Prop :=
  | wfParam_free : forall ctx stk i j (Hi : i < length stk + length ctx)
      (Hi' : length stk <= i) (Hj : j < safe_nth ctx (i - length stk; lt_in_Ctx Hi Hi')),
      wf_rtree ctx stk (rParam i j)
  | wfParam_rec : forall ctx stk i j (Hi : i < length stk),
      let defs_seen := safe_nth stk (i; Hi) in
      let defs := fst defs_seen in
      let seen := snd defs_seen in
      let stk' := skipn (S i) stk in
      forall (Hj : j < length defs),
      ~ In j seen ->
      wf_rtree ctx ((defs, j :: seen) :: stk') (safe_nth defs (j; Hj)) ->
      wf_rtree ctx stk (rParam i j)
  | wfNode : forall ctx stk x sons,
      Forall (wf_rtree (Context_of_Stack stk ++ ctx) []) sons ->
      wf_rtree ctx stk (rNode x sons)
  | wfRec : forall ctx stk defs,
      (Foralli (fun j => wf_rtree ctx ((defs, [j]) :: stk)) defs) ->
      forall j (Hj : j < length defs),
      wf_rtree ctx stk (rRec j defs).

  Definition wf_rtree_ind' (P : Context -> Stack -> t -> Prop)
    (fwfParam_free :
      forall (ctx : list nat) (stk : list (list t * list nat))
        (i j : nat) (Hi : i < length stk + length ctx) (Hi' : length stk <= i),
        j < safe_nth ctx (i - length stk; lt_in_Ctx Hi Hi') ->
        P ctx stk (rParam i j))
    (fwfParam_rec :
      forall (ctx : Context) (stk : list (list t * list nat))
        (i j : nat) (Hi : i < length stk),
        let defs_seen := safe_nth stk (i; Hi) in
        let defs := fst defs_seen in
        let seen := snd defs_seen in
        let stk' := skipn (S i) stk in
        forall Hj : j < length defs,
        ~ In j seen ->
        wf_rtree ctx ((defs, j :: seen) :: stk') (safe_nth defs (j; Hj)) ->
        P ctx ((defs, j :: seen) :: stk') (safe_nth defs (j; Hj)) ->
        P ctx stk (rParam i j))
    (fwfNode :
      forall (ctx : list nat) (stk : Stack) (x : X) (sons : list t),
        Forall (wf_rtree (Context_of_Stack stk ++ ctx) []) sons ->
        Forall (P (Context_of_Stack stk ++ ctx) []) sons ->
        P ctx stk (rNode x sons))
    (fwfRec :
      forall (ctx : Context) (stk : list (list t * list nat))
        (defs : list t),
        Foralli (fun j => wf_rtree ctx ((defs, [j]) :: stk)) defs ->
        Foralli (fun j => P ctx ((defs, [j]) :: stk)) defs ->
        forall j (Hj : j < length defs),
        P ctx stk (rRec j defs)) :
    forall (ctx : Context) (stk : Stack) (tree : t) (Hwf : wf_rtree ctx stk tree),
      P ctx stk tree :=
  fix F ctx stk tree Hwf : P ctx stk tree :=
  match Hwf with
  | wfParam_free ctx stk i j Hi Hi' Hj =>
      fwfParam_free ctx stk i j Hi Hi' Hj
  | wfParam_rec ctx stk i j Hi _ defs seen stk' Hj HjNotIn Hwf =>
      fwfParam_rec ctx stk i j Hi Hj HjNotIn Hwf
        (F ctx ((defs, j :: seen) :: stk') (safe_nth defs (j; Hj)) Hwf)
  | wfNode ctx stk x sons Hwf =>
      fwfNode ctx stk x sons Hwf (Forall_ind
        (fun sons => _ sons)
        (Forall_nil _)
        (fun _ _ Htree _ Hrec => Forall_cons _ (F _ _ _ Htree) Hrec) Hwf)
  | wfRec ctx stk defs Hdefs j Hj =>
      fwfRec ctx stk defs Hdefs (Foralli_aux_ind _ _
    (fun n defs' => Foralli_aux (fun j => P ctx ((defs, [j]) :: stk)) n defs')
    (fun n => Foralli_nil _ _)
    (fun _ _ _ Htree _ Hrec => Foralli_cons _ _ _ _ (F _ _ _ Htree) Hrec)
    0 defs Hdefs) j Hj
  end.

  Lemma wf_weaken :
    forall ctx stk tree,
    wf_rtree ctx stk tree ->
    forall n (Hn : n <= length stk),
    wf_rtree (Context_of_Stack (skipn n stk) ++ ctx) (firstn n stk) tree.
  Proof.
    induction 1 using wf_rtree_ind'; intros.
    - econstructor.
      erewrite safe_nth_app2; only 2: crush.
      erewrite safe_nth_trans.
      + eassumption.
      + crush.
    - destruct (le_lt_dec (n) i).
      + econstructor 1.
        erewrite safe_nth_app1.
        unfold Context_of_Stack.
        erewrite safe_nth_map.
        gen_safe_proof.
        rewrite firstn_length_le; only 2: crush.
        intros. erewrite <- safe_nth_skipn; only 2: crush.
        gen_safe_proof; intros; unify_lt_proofs.
        destruct safe_nth.
        assumption.
      + econstructor 2.
        * erewrite <- safe_nth_firstn; only 2: crush.
          gen_safe_proof; intros; unify_lt_proofs.
          assumption.
        * repeat gen_safe_proof.
          intros Hs.
          erewrite <- safe_nth_firstn; only 2: crush.
          gen_safe_proof; intros; unify_lt_proofs.
          intros; unify_lt_proofs.
          reset defs_seen; reset defs; reset seen.
          specialize (IHwf_rtree (n - i) ltac:(crush)).
          subst stk'.
          replace (skipn n stk)
             with (skipn (n - i) ((defs, j :: seen) :: skipn (S i) stk));
          swap 1 2.
          { rewrite <- Nat.succ_pred_pos with (n := n - i); only 2: crush.
            simpl. rewrite skipn_skipn. f_equal. crush. }
          replace ((defs, j :: seen) :: skipn (S i) (firstn n stk))
             with (firstn (n - i) ((defs, j :: seen) :: skipn (S i) stk));
          swap 1 2.
          { rewrite <- Nat.succ_pred_pos with (n := n - i); only 2: crush.
            simpl. f_equal. replace (pred (n - i)) with (n - S i) by crush.
            now rewrite skipn_firstn. }
          assumption.
    - constructor.
      unfold Context_of_Stack.
      rewrite app_assoc.
      rewrite <- map_app.
      rewrite firstn_skipn.
      assumption.
    - constructor; only 2: crush.
      apply Foralli_impl with (2 := H0).
      intros i tree Hi HtreeIn Hwf.
      specialize (Hwf (S n) ltac:(crush)).
      assumption.
  Unshelve.
    all: try crush.
      gen_safe_proof; intros.
      erewrite <- safe_nth_firstn; only 2: crush.
      eassumption.
  Qed.

  Definition lift_Stack (d n : nat) : Stack -> Stack :=
    map_Stack (fun m def => lift_rtree_rec (m + d) n def).
  Hint Unfold lift_Stack : rtree.

  Lemma lift_Stack_seen :
    forall d n stk i (Hi : i < length stk) (Hi' : i < length (lift_Stack d n stk)),
      snd (safe_nth (lift_Stack d n stk) (i; Hi')) = snd (safe_nth stk (i; Hi)).
  Proof.
    intros. apply map_Stack_seen.
  Qed.

  Lemma lift_Stack_safe_nth (d : nat) (n : nat) (stk : Stack)
    (i : nat) (Hi : i < length stk) (Hi' : i < length (lift_Stack d n stk)) :
    let hd := safe_nth (lift_Stack d n stk) (i; Hi') in
    let stk' := skipn (S i) (lift_Stack d n stk) in
    let F := lift_rtree_rec (length (hd :: stk') + d) n in
      fst hd = map F (fst (safe_nth stk (i; Hi))).
  Proof.
    apply map_Stack_safe_nth.
    intros.
    f_equal. crush.
  Qed.

  Lemma Context_of_lift_Stack (d : nat) (n : nat) (stk : Stack) :
    Context_of_Stack (lift_Stack d n stk) = Context_of_Stack stk.
  Proof.
    apply Context_of_map_Stack.
  Qed.

  Lemma wf_lift_rtree :
    forall newctx ctx stk tree,
      wf_rtree ctx stk tree ->
      forall n (Hn : n <= length ctx),
      let F := lift_rtree_rec (length stk + n) (length newctx) in
      let FS := lift_Stack n (length newctx) in
      wf_rtree (firstn n ctx ++ newctx ++ skipn n ctx) (FS stk) (F tree).
  Proof.
    induction 1 using wf_rtree_ind'; intros; subst F; simpl.
    - destruct (Nat.leb_spec (length stk + n) i).
      + econstructor.
        erewrite safe_nth_app2; only 2: crush.
        erewrite safe_nth_app2; only 2: crush.
        erewrite safe_nth_skipn with (n0 := n) in H; only 2: crush.
        erewrite safe_nth_trans.
        * eassumption.
        * clear H; crush.
      + econstructor.
        erewrite safe_nth_app1.
        erewrite safe_nth_firstn with (n0 := n) in H; only 2: crush.
        erewrite safe_nth_trans.
        * eassumption.
        * clear; crush.
    - assert (length stk + n <=? i = false) as -> by crush.
      econstructor 2.
      + unfold FS. erewrite lift_Stack_seen. eassumption.
      + specialize (IHwf_rtree n Hn).
        simpl in IHwf_rtree. unfold FS.
        erewrite lift_Stack_seen.
        gen_safe_proof. gen_safe_proof.
        erewrite lift_Stack_safe_nth.
        gen_safe_proof. intros Hp.
        change (length
           (safe_nth (lift_Stack n (length newctx) stk) (i; Hp)
            :: skipn (S i) (lift_Stack n (length newctx) stk)) + n) with
            (S (length (skipn (S i) (lift_Stack n (length newctx) stk))) + n).
        clear Hp.
        gen_safe_proof; intros. unify_lt_proofs.
        intros Hp. erewrite safe_nth_map. clear Hp.
        crush.
    - constructor. apply Forall_map.
      apply Forall_Impl with (1 := H0).
      apply Forall_forall. intros tree HtreeIn.
      apply Forall_forall' with (x0 := tree) in H0; trivial.
      intros.
      specialize (H0 (length (Context_of_Stack stk) + n) ltac:(crush)).
      simpl in H0.
      unfold Context_of_Stack in H0 at 1 3 5.
      subst FS.
      rewrite Context_of_lift_Stack.
      replace (length stk) with (length (Context_of_Stack stk)) in H0 at 1 2 by crush.
      repeat rewrite firstn_app_2 in H0.
      rewrite skipn_app_2 in H0.
      rewrite app_assoc_reverse in H0.
      crush.
    - econstructor; only 2: crush.
      apply Foralli_map.
      apply Foralli_impl with (2 := H0); clear H0.
      intros i tree Hi HtreeIn Hwf.
      specialize (Hwf n Hn). simpl in *.
      assumption.
    Unshelve.
      all: try crush.
      subst FS. erewrite lift_Stack_safe_nth. crush.
  Qed.

  Lemma wf_lift_rtree_deep :
    forall newstk ctx stk tree,
    wf_rtree ctx stk tree ->
    let FS := lift_Stack 0 (length newstk) in
    let F := lift_rtree_rec (length stk) (length newstk) in
    wf_rtree ctx (FS stk ++ newstk) (F tree).
  Proof.
    induction 1 using wf_rtree_ind'; intros; subst F; simpl in *.
    - assert (length stk <=? i = true) as -> by crush.
      econstructor.
      erewrite safe_nth_trans.
      + eassumption.
      + crush.
    - assert (length stk <=? i = false) as -> by crush.
      econstructor 2.
      + erewrite safe_nth_app1. subst FS.
        erewrite lift_Stack_seen. eassumption.
      + gen_safe_proof. erewrite safe_nth_app1.
        subst FS. erewrite lift_Stack_safe_nth.
        intros.
        erewrite safe_nth_map.
        gen_safe_proof. gen_safe_proof.
        gen_safe_proof.
        intros ?; unify_lt_proofs.
        intros ?; unify_lt_proofs.
        intros Hs'.
        erewrite lift_Stack_seen.
        gen_safe_proof; intros; unify_lt_proofs.
        reset defs_seen; reset defs; reset seen; reset stk'.
        simpl.
        replace (length (skipn (S i) (lift_Stack 0 (length newstk) stk)))
        with (length stk') by crush.
        replace (skipn (S i) (lift_Stack 0 (length newstk) stk ++ newstk))
        with (lift_Stack 0 (length newstk) stk' ++ newstk); swap 1 2.
        { rewrite skipn_app_1; only 2: crush.
          unfold lift_Stack, map_Stack.
          rewrite map_with_length_skipn; crush. }
        rewrite <- plus_n_O at 2. apply IHwf_rtree.
    - constructor. apply Forall_map.
      apply Forall_impl with (2 := H).
      intros tree Htree.
      replace (Context_of_Stack (FS stk ++ newstk) ++ ctx) with
              (Context_of_Stack stk ++ Context_of_Stack newstk ++ ctx); swap 1 2.
      { subst FS. rewrite app_assoc. f_equal.
        unfold Context_of_Stack. rewrite map_app.
        f_equal. rewrite Context_of_lift_Stack. reflexivity. }
      replace (Context_of_Stack stk) with
              (firstn (length stk) (Context_of_Stack stk ++ ctx)); swap 1 2.
      { rewrite firstn_app.
        assert (length stk - length (Context_of_Stack stk) = 0) as -> by crush.
        rewrite firstn_O. rewrite app_nil_r.
        rewrite firstn_all2; crush. }
      replace (ctx) with
              (skipn (length stk) (Context_of_Stack stk ++ ctx)) at 2; swap 1 2.
      { replace (length stk) with (length (Context_of_Stack stk) + 0) by crush.
        now rewrite skipn_app_2. }
      replace (length newstk) with (length (Context_of_Stack newstk)) by crush.
      apply wf_lift_rtree with (stk := []); crush.
    - econstructor; only 2: crush.
      apply Foralli_map.
      apply Foralli_impl with (2 := H0); clear H0.
      intros i tree Hi HtreeIn Hwf.
      rewrite plus_n_O with (n := length stk) at 1.
      assumption.
    Unshelve.
      all: try crush.
      erewrite safe_nth_app1. subst FS. erewrite lift_Stack_safe_nth. crush.
    Unshelve.
      all: try crush.
  Qed.

  Definition subst_Stack (d : nat) (sub : list t) : Stack -> Stack :=
    map_Stack (fun m def => subst_rtree_rec (m + d) sub def).
  Hint Unfold subst_Stack : rtree.

  Lemma subst_Stack_seen :
    forall d sub stk i (Hi : i < length stk) (Hi' : i < length (subst_Stack d sub stk)),
      snd (safe_nth (subst_Stack d sub stk) (i; Hi')) = snd (safe_nth stk (i; Hi)).
  Proof.
    intros.
    apply map_Stack_seen.
  Qed.

  Lemma subst_Stack_safe_nth d sub stk i (Hi : i < length stk) (Hi' : i < length (subst_Stack d sub stk)) :
    let hd := safe_nth (subst_Stack d sub stk) (i; Hi') in
    let stk' := skipn (S i) (subst_Stack d sub stk) in
    let F := subst_rtree_rec (length (hd :: stk') + d) sub in
      fst hd = map F (fst (safe_nth stk (i; Hi))).
  Proof.
    apply map_Stack_safe_nth.
    intros. f_equal. crush.
  Qed.

  Lemma Context_of_subst_Stack (d : nat) (sub : list t) (stk : Stack) :
    Context_of_Stack (subst_Stack d sub stk) = Context_of_Stack stk.
  Proof.
    apply Context_of_map_Stack.
  Qed.

  Lemma wf_subst_rtree :
    forall sub (ctx : Context) (stk : Stack) (tree : t),
      wf_rtree ctx stk tree ->
      forall n (Hn : n < length ctx)
      (Hsub : Foralli (fun j => wf_rtree (skipn (S n) ctx) [(sub, [j])]) sub)
      (Hnsub : safe_nth ctx (n; Hn) = length sub),
      let F := subst_rtree_rec (length stk + n) sub in
      let FS := subst_Stack n sub in
      wf_rtree (firstn n ctx ++ skipn (S n) ctx) (FS stk) (F tree).
  Proof.
    induction 1 using wf_rtree_ind'; intros; subst F; simpl.
    - destruct (Nat.compare_spec (length stk + n) i).
      + subst.
        unfold lift_rtree.
        revert H. gen_safe_proof.
        rewrite minus_plus. intros; unify_lt_proofs.
        intros.
        rewrite <- simpl_lift with (i := 0); try crush.
        replace (length stk) with (length (FS stk)) by crush.
        apply wf_lift_rtree_deep with (stk := []).
        replace n with (length (firstn n ctx)) at 3 by crush.
        apply wf_lift_rtree with (newctx := firstn n ctx) (ctx := skipn (S n) ctx)
          (stk := []) (n := 0); only 2: crush.
        econstructor; crush.
      + econstructor.
        erewrite safe_nth_app2; only 2: crush.
        erewrite safe_nth_skipn with (n0 := S n) in H; only 2: crush.
        erewrite safe_nth_trans.
        * eassumption.
        * clear H. crush.
      + econstructor.
        erewrite safe_nth_app1.
        erewrite safe_nth_firstn with (n0 := n) in H; only 2: crush.
        erewrite safe_nth_trans.
        * eassumption.
        * clear; crush.
    - assert (length stk + n ?= i = Gt) as -> by crush.
      econstructor 2.
      + unfold FS. erewrite subst_Stack_seen. eassumption.
      + specialize (IHwf_rtree n Hn Hsub Hnsub).
        simpl in IHwf_rtree. unfold FS.
        erewrite subst_Stack_seen.
        gen_safe_proof. gen_safe_proof.
        erewrite subst_Stack_safe_nth.
        gen_safe_proof. intros Hp.
        change (length
           (safe_nth (subst_Stack n sub stk) (i; Hp)
            :: skipn (S i) (subst_Stack n sub stk)) + n) with
            (S (length (skipn (S i) (subst_Stack n sub stk))) + n).
        clear Hp.
        gen_safe_proof; intros; unify_lt_proofs.
        intros Hp. erewrite safe_nth_map. clear Hp.
        crush.
    - constructor. apply Forall_map.
      apply Forall_Impl with (1 := H).
      apply Forall_forall. intros tree HtreeIn.
      apply Forall_forall' with (x0 := tree) in H0; trivial.
      intros. simpl in H0.
      subst FS. rewrite Context_of_subst_Stack.
      rewrite app_assoc.
      rewrite <- firstn_app_2.
      rewrite <- skipn_app_2 with (l1 := Context_of_Stack stk).
      unfold Context_of_Stack at 1 3. rewrite map_length.
      rewrite <- plus_n_Sm.
      unshelve eapply H0.
      + crush.
      + intros. rewrite plus_n_Sm.
        replace (length stk) with (length (Context_of_Stack stk)) by crush.
        rewrite skipn_app_2. auto.
      + gen_safe_proof.
        replace (length stk) with (length (Context_of_Stack stk)) by crush.
        intros.
        erewrite safe_nth_app2; only 2: crush.
        gen_safe_proof.
        rewrite minus_plus.
        intros; unify_lt_proofs.
        assumption.
    - econstructor; only 2: crush.
      apply Foralli_map.
      apply Foralli_impl with (2 := H0); clear H0.
      intros i tree Hi HtreeIn Hwf.
      specialize (Hwf n Hn). simpl in *.
      apply Hwf; assumption.
  Unshelve.
    all: try crush.
    subst FS. erewrite subst_Stack_safe_nth. crush.
  Qed.

(* Not needed?
  Lemma wf_subst_rtree_deep :
    forall sub ctx stk tree,
    wf_rtree ctx stk tree ->
    forall n (Hn : n < length stk)
    (Hsub : Foralli (fun j => wf_rtree (Context_of_Stack (skipn (S n) stk) ++ ctx)
      ((sub, [j]) :: stk)) sub)
    (Hnsub : fst (safe_nth stk (n; Hn)) = sub),
    let F := subst_rtree_rec n sub in
    let FS := subst_Stack 0 sub in
    wf_rtree ctx (FS (firstn n stk) ++ skipn (S n) stk) (F tree).
  Proof.
    induction 1 using wf_rtree_ind'; intros; subst F; simpl in *.
  Admitted.
*)

  Corollary wf_subst_rtree' :
    forall ctx sub (dsub := length sub)
    (Hsub : Foralli (fun j => wf_rtree ctx [(sub, [j])]) sub)
    tree stk (d := length stk),
    wf_rtree (stk ++ dsub :: ctx) [] tree ->
    wf_rtree (stk ++ ctx) [] (subst_rtree_rec d sub tree).
  Proof.
    intros ctx sub dsub Hsub.
    intros.
    pose proof (wf_subst_rtree).
    specialize (H0 sub (stk ++ dsub :: ctx) [] tree H d).
    simpl in H0.
    replace (stk ++ ctx) with (firstn d (stk ++ dsub :: ctx) ++
      skipn (S d) (stk ++ dsub :: ctx)); swap 1 2.
    { f_equal.
      - rewrite firstn_app.
        subst d. rewrite Nat.sub_diag.
        rewrite firstn_all. simpl.
        apply app_nil_r.
      - change (dsub :: ctx) with ([dsub] ++ ctx).
        rewrite app_assoc. rewrite plus_n_O with (n := S d).
        replace (S d) with (length (stk ++ [dsub])) by crush.
        apply skipn_app_2. }
    eapply H0.
    - intros.
      change (dsub :: ctx) with ([dsub] ++ ctx).
      rewrite app_assoc. rewrite plus_n_O with (n := S d).
      replace (S d) with (length (stk ++ [dsub])) by crush.
      rewrite skipn_app_2. now apply Hsub.
    - erewrite safe_nth_app2; only 2: crush.
      subst d.
      gen_safe_proof. rewrite Nat.sub_diag.
      intros. reflexivity.
  Unshelve.
    all: crush.
  Qed.

  (* Even more specialized. *)
  Corollary wf_subst_rtree'' :
    forall ctx sub (dsub := length sub) j (Hj : j < dsub),
      wf_rtree ctx [] (rRec j sub) ->
      let tree := subst_rtree sub (safe_nth sub (j; Hj)) in
      wf_rtree ctx [] tree.
  Proof.
    intros ctx sub dsub j Hj Hsub tree.
    apply wf_subst_rtree' with (stk := []).
    - now inv Hsub.
    - simpl.
      apply wf_weaken with (ctx := ctx) (stk := [(sub, [j])]) (n := 0); only 2: crush.
      inv Hsub.
      now apply safe_nth_Foralli.
  Qed.

  (* === Expansion === *)

  Inductive rtree_bar : t -> Prop :=
  | rtree_bar_param : forall i j, rtree_bar (rParam i j)
  | rtree_bar_node : forall x sons, rtree_bar (rNode x sons)
  | rtree_bar_rec : forall j defs,
      (forall (Hj : j < length defs), rtree_bar (subst_rtree defs (safe_nth defs (j; Hj)))) ->
      rtree_bar (rRec j defs).

  Program Fixpoint expand_rec (tree : t) (Hctx : exists ctx, wf_rtree ctx [] tree)
    (bar : rtree_bar tree) {struct bar} : t :=
      match tree with
      | rRec j defs =>
        let Hj : j < length defs := _ in
        let def := safe_nth defs (j; Hj) in
        let tree' := subst_rtree defs def in
          expand_rec tree' _ _
      | t => t
      end.

  Next Obligation.
    now inv H.
  Defined.

  Next Obligation.
    rename Hctx into ctx.
    exists ctx.
    now apply wf_subst_rtree''.
  Defined.

  Next Obligation.
    simpl.
    inv bar.
    apply H1.
  Defined.

  Fixpoint wf_expand_rec (tree : t) (ctx : Context)
    (Hwf : wf_rtree ctx [] tree)
    (bar : rtree_bar tree) {struct bar} :
    forall Hctx,
    wf_rtree ctx [] (expand_rec tree Hctx bar).
  Proof.
    destruct bar; intros; try assumption.
    apply wf_expand_rec with (tree := subst_rtree _ _).
    now apply wf_subst_rtree''.
  Qed.

  Theorem wf_bar (ctx : Context) (stk : Stack) (tree : t) :
    wf_rtree ctx stk tree ->
      let tree' := fold_left (fun tree '(defs, seen) => subst_rtree defs tree) stk tree in
      rtree_bar tree'.
  Proof.
    induction 1 using wf_rtree_ind'; simpl in *.
    - revert dependent i.
      induction stk as [|[defs seen] stk']; intros; simpl.
      + constructor.
      + unfold subst_rtree; simpl.
        destruct i; only 1: (crush).
        apply (IHstk' i ltac:(crush) ltac:(crush)).
        erewrite safe_nth_trans.
        * eassumption.
        * crush.
    - revert dependent i.
      induction stk as [|[defs' seen'] stk]; intros; simpl in *.
      + constructor.
      + unfold subst_rtree; simpl.
        destruct i.
        * clear IHstk.
          unfold skipn in stk'; subst stk' defs_seen defs seen; simpl in *.
          unfold lift_rtree. rewrite lift0.
          clear H0 Hi H.
          revert dependent defs'.
          induction stk as [|[defs seen] stk']; intros; simpl in *.
          -- constructor. intros; unify_lt_proofs. assumption.
          -- eapply IHstk'; clear IHstk'.
             erewrite safe_nth_map.
             gen_safe_proof; intros; unify_lt_proofs.
             unfold subst_rtree.
             rewrite <- distr_subst.
             apply IHwf_rtree.
        * eapply IHstk; eauto.
    - clear H H0. revert sons.
      induction stk as [|[defs seen] stk']; intros; simpl; try constructor.
      apply IHstk'.
    - clear H. revert dependent defs.
      induction stk as [|[defs' seen] stk']; intros; simpl in *.
      + constructor. intros; unify_lt_proofs.
        now apply safe_nth_Foralli.
      + unfold subst_rtree; simpl.
        eapply IHstk'; only 2: crush; clear IHstk'.
        apply Foralli_map.
        apply Foralli_impl with (2 := H0); clear H0.
        intros i tree Hi HtreeIn Hwf.
        unfold subst_rtree.
        rewrite <- distr_subst.
        apply Hwf.
  Unshelve.
    all: crush.
  Qed.

  Definition expand (tree : t) (tree_wf : exists ctx, wf_rtree ctx [] tree) : t.
  Proof.
    refine (expand_rec tree tree_wf _).
    destruct tree_wf as [ctx Hwf].
    apply wf_bar with (ctx := ctx) (stk := []).
    assumption.
  Defined.

  Theorem wf_expand (tree : t) (ctx : Context) (Hwf : wf_rtree ctx [] tree) :
    forall Hctx,
    wf_rtree ctx [] (expand tree Hctx).
  Proof.
    intros.
    now apply wf_expand_rec.
  Qed.

  Fixpoint expand_rec_notRec (tree : t) Hctx bar :
    match expand_rec tree Hctx bar with
    | rParam i j => True
    | rNode x sons => True
    | rRec j defs => False
    end.
  Proof.
    destruct bar; try constructor.
    apply expand_rec_notRec with (tree := subst_rtree _ _).
  Qed.

  (* What the user will see. *)

  Definition wf_closed : t -> Prop := wf_rtree [] [].

  Definition closed_expand (tree : t) (Hwf : wf_closed tree) : t :=
    expand tree (ex_intro _ [] Hwf).

  Lemma wf_closed_expand (tree : t) (Hwf : wf_closed tree) :
    wf_closed (closed_expand tree Hwf).
  Proof.
    now apply wf_expand.
  Qed.

  Program Definition dest_node (tree : t) (Hwf : wf_closed tree) : X * list t :=
    match closed_expand tree Hwf with
    | rNode x sons => (x, sons)
    | _ => !
    end.

  Next Obligation.
    set (expand tree (ex_intro _ [] Hwf)) as res.
    change (forall x sons, rNode x sons <> res) in H.
    assert (wf_rtree [] [] res) as Hwfres by now apply wf_expand.
    assert (match res with
            | rParam i j => True
            | rNode x sons => True
            | rRec j defs => False
            end) as HnotRec by apply expand_rec_notRec.
    clearbody res. clear Hwf.
    inv Hwfres.
    - inversion Hi.
    - inversion Hi.
    - now eapply H.
    - assumption.
  Defined.

  Definition mk_node (x : X) (sons : list t) := rNode x sons.

  Lemma wf_mk_node (x : X) (sons : list t) :
    forall ctx stk,
    Forall (wf_rtree (Context_of_Stack stk ++ ctx) []) sons ->
    wf_rtree ctx stk (mk_node x sons).
  Proof.
    intros. now constructor.
  Qed.

  Definition mk_rec_calls (i : nat) : list t :=
    let fix aux j :=
      match j with
      | O => []
      | S j => rParam 0 j :: aux j
      end
    in rev (aux i).

  Lemma wf_mk_rec_calls (i : nat) :
    forall ctx,
    Forall (wf_rtree (i :: ctx) []) (mk_rec_calls i).
  Proof.
    intros.
    enough (forall j, j <= i -> Forall (wf_rtree (i :: ctx) []) (mk_rec_calls j)).
    { now apply H. }
    induction j; intros Hj.
    - constructor.
    - apply Forall_snoc.
      + apply IHj. crush.
      + econstructor. crush.
    Unshelve.
      all: crush.
  Qed.

  Definition mk_rec (defs : list t) : list t :=
    let fix aux j :=
      match j with
      | O => []
      | S j => rRec j defs :: aux j
      end
    in rev (aux (length defs)).

  Lemma wf_mk_rec (defs : list t) :
    forall ctx stk,
      Foralli (fun j => wf_rtree ctx ((defs, [j]) :: stk)) defs -> 
      Forall (wf_rtree ctx stk) (mk_rec defs).
  Proof.
    intros.
    unfold mk_rec.
    enough (forall j, j <= length defs ->
      Forall (wf_rtree ctx stk) (rev (
        (fix aux j :=
            match j with
            | O => []
            | S j => rRec j defs :: aux j
            end) j))).
    { now apply H0. }
    induction j; intros Hj.
    - constructor.
    - apply Forall_snoc.
      + apply IHj. crush.
      + constructor; crush.
  Qed.

End Rtree.
