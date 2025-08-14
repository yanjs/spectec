From Stdlib Require Import List Bool Nat Arith.
Import ListNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.

Notation "tf1 :-> tf2" :=
(mk_functype (mk_list _ tf1) (mk_list _ tf2)) (at level 40).

Notation "t1 <tv: t2" := (Valtype_sub t1 t2) (at level 30).
Definition Resulttype_subtype ts1 ts2 := Resulttype_sub (mk_list _ ts1) (mk_list _ ts2).
Notation "ts1 <ts: ts2" := (Resulttype_subtype ts1 ts2) (at level 60).

Definition Ftype_sub tf1 tf2 : Prop :=
  match tf1, tf2 with
  | ts11 :-> ts12,
    ts21 :-> ts22 =>
        (ts21 <ts: ts11) /\
        (ts12 <ts: ts22)
  end.

Definition instrtype_sub tf tf' : Prop :=
  match tf, tf' with
  | ts11 :-> ts12,
    ts21 :-> ts22 =>
        exists ts_sub ts ts11_sub ts12_sup,
        ts21 = ts_sub ++ ts11_sub /\
        ts22 = ts ++ ts12_sup /\
        (ts_sub <ts: ts) /\
        (ts11_sub <ts: ts11) /\
        (ts12 <ts: ts12_sup)
  end.

Notation "tf1 <tf: tf2" := (Ftype_sub tf1 tf2) (at level 60).
Notation "tf1 <ti: tf2" := (instrtype_sub tf1 tf2) (at level 60).

Lemma size_length : forall {A : Type} (xs : seq A),
  size xs = length xs.
Proof. auto. Qed.

Lemma valtype_sub_refl : forall t, (t <tv: t).
Proof.
  move => t.
  apply refl.
Qed.

Lemma valtype_sub_trans: forall t1 t2 t3,
    t1 <tv: t2 ->
    t2 <tv: t3 ->
    t1 <tv: t3.
Proof.
  move => t1 t2 t3 H12 H23.
  destruct t1, t2, t3; eauto; try apply refl; try apply bot;
  try inversion H23; try inversion H12.
Qed.

Lemma resulttype_sub_refl : forall ts, ts <ts: ts.
Proof.
  intros ts.
  constructor; auto.
  induction ts as [|t ts IH]; simpl; auto.
  constructor; auto.
  apply valtype_sub_refl.
Qed.

Lemma resulttype_sub_size_eq: forall ts1 ts2,
    ts1 <ts: ts2 ->
    size ts1 = size ts2.
Proof.
  move => ts1 ts2 H.
  inversion H; subst.
  auto.
Qed.

Lemma resulttype_sub_trans: forall ts1 ts2 ts3,
    ts1 <ts: ts2 ->
    ts2 <ts: ts3 ->
    ts1 <ts: ts3.
Proof.
  move => ts1 ts2 ts3 H12 H23.
  inversion H12; inversion H23; subst.
  constructor.
  - by rewrite H1.
  - move : ts2 ts3 H12 H23 H1 H2 H5 H6.
    induction ts1 as [| t1 ts1 IH];
    destruct ts2 as [| t2 ts2];
    destruct ts3 as [| t3 ts3]; try discriminate;
    try constructor.
    + inversion H2; inversion H6; subst.
      eapply valtype_sub_trans; eauto.
    + rewrite !length_cons in H1;
      inversion H1.
      rewrite !length_cons in H5;
      inversion H5.
      inversion H2; inversion H6; subst.
      apply (IH ts2 ts3);
      auto; constructor; auto.
Qed.

Lemma resulttype_sub_app_trans: forall ts_sub ts ts1 ts2,
    ts_sub <ts: ts ->
    (ts ++ ts1) <ts: (ts2) ->
    (ts_sub ++ ts1) <ts: (ts2).
Proof.
  move => ts_sub ts ts1 ts2 H1 H2.
  constructor.
  - inversion H1; inversion H2; subst.
    rewrite -H7.
    rewrite -!size_length.
    rewrite !size_cat.
    rewrite !size_length.
    by rewrite H3.
  - move: ts ts1 ts2 H1 H2. 
    induction ts_sub as [| t_sub ts_sub IH];
    destruct ts as [| t ts];
    destruct ts2 as [| t2 ts2];
    move=> H1 H2;
    try (inversion H1; inversion H2; discriminate);
    try (by inversion H2).
    rewrite cat_cons.
    rewrite cat_cons in H2.
    inversion H1; inversion H2; subst; clear H1 H2.
    inversion H4; inversion H8; subst; clear H4 H8.
    constructor.
    { eapply valtype_sub_trans; eauto. } 
    eapply IH.
    + inversion H3.
      econstructor ; eauto.
    * inversion H7.
      econstructor; auto.
Qed.

Lemma all2_cat' : forall A (f : A -> A -> bool) l1 l2 l3 l4,
  size l1 = size l2 ->
  all2 f (l1 ++ l3) (l2 ++ l4) ->
  all2 f l1 l2 /\ all2 f l3 l4.
Proof.
  induction l1 as [| a1 l1 IH];
  destruct l2 as [| a2 l2]; move => l3 l4 HSize H; split;
  simpl in H; try discriminate HSize; auto;
  move/andP: H => [H1 H2];
  inversion HSize;
  eapply IH in H0 as [H3 H4].
  - simpl. apply/andP; split; auto.
  eauto. eauto. eauto.
Qed.

Lemma all2_cat : forall A (f : A -> A -> bool) l1 l2 l3 l4,
  all2 f l1 l2 -> all2 f l3 l4 ->
  all2 f (l1 ++ l3) (l2 ++ l4).
Proof.
  induction l1 as [| a1 l1 IH];
  destruct l2 as [| a2 l2];
  destruct l3 as [| a3 l3];
  destruct l4 as [| a4 l4];
  auto.
  - move => H12 _.
    by repeat rewrite cats0.
  - move => H1 H2.
    rewrite cat_cons.
    simpl.
    apply/andP; split.
    + simpl in H1. by move/andP: H1 => [H1 _].
    + apply IH.
      * simpl in H1. by move/andP: H1 => [_ H1].
      * auto.
Qed.

Lemma resulttype_sub_app: forall ts1_sub ts2_sub ts1 ts2,
  (ts1_sub <ts: ts1) ->
  (ts2_sub <ts: ts2) ->
  (ts1_sub ++ ts2_sub) <ts: (ts1 ++ ts2).
Proof.
  induction ts1_sub as [| t1_sub ts1_sub IH];
  move=> ts2_sub ts1 ts2 H1 H2.
  - inversion H1; subst.
    simpl in H3; symmetry in H3.
    rewrite length_zero_iff_nil in H3.
    subst.
    by rewrite !cat0s.
  - destruct ts1 as [| t1 ts1].
    { inversion H1; discriminate. }
    rewrite !cat_cons.
    inversion H1; subst; clear H1.
    constructor.
    + simpl; f_equal.
      inversion H2; subst.
      simpl in H3; inversion H3.
      rewrite -!size_length.
      rewrite !size_cat.
      rewrite !size_length.
      rewrite H1; rewrite H0; reflexivity.
    + inversion H4; subst; clear H4.
      constructor; auto.
      simpl in H3; inversion H3; subst; clear H3.
      apply Forall2_app.
      { by apply H7. }
      by inversion H2.
Qed.

Lemma Forall2_app': forall {A B : Type} (R : A -> B -> Prop)
  (l1 l2 : seq A) (l1' l2' : seq B),
  length l1 = length l1' ->
  Forall2 R (l1 ++ l2) (l1' ++ l2') ->
  Forall2 R l1 l1' /\ Forall2 R l2 l2'.
Proof.
  induction l1 as [| x l1 IH];
  destruct l1' as [| x' l1']; auto; try discriminate.
  move=> l2' Hsize H1.
  rewrite !cat_cons in H1.
  inversion Hsize; clear Hsize.
  eapply IH in H0 as [Hl1 Hl2].
  split.
  - constructor. by inversion H1.
  - by apply Hl1.
  - eauto.
  - by inversion H1.
Qed.

Lemma resulttype_sub_app': forall ts1_sub ts2_sub ts1 ts2,
  length ts1_sub = length ts1 ->
  (ts1_sub ++ ts2_sub) <ts: (ts1 ++ ts2) ->
  (ts1_sub <ts: ts1) /\
  (ts2_sub <ts: ts2).
Proof.
  move => ts1_sub ts2_sub ts1 ts2 Hsize Happ.
  inversion Happ; subst.
  split; constructor; auto; 
  eapply (Forall2_app' Valtype_sub) in H2 as [HF1 HF2]; eauto.
  rewrite -!size_length in Hsize H1.
  rewrite -!size_length.
  rewrite !size_cat in H1.
  rewrite Hsize in H1.
  by rewrite Nat.add_cancel_l in H1.
Qed.

Lemma Forall2_take : forall {A B: Type} (R : A -> B -> Prop) l1 l2 n,
  Forall2 R l1 l2 ->
  Forall2 R (take n l1) (take n l2).
Proof.
  induction l1 as [| e1 l1 IH]; destruct l2 as [| e2 l2];
  move => n H; try inversion H; subst;
  destruct n as [|n]; simpl; auto.
Qed.

Lemma Forall2_drop : forall {A B: Type} (R : A -> B -> Prop) l1 l2 n,
  Forall2 R l1 l2 ->
  Forall2 R (drop n l1) (drop n l2).
Proof.
  induction l1 as [| e1 l1 IH]; destruct l2 as [| e2 l2];
  move => n H; try inversion H; subst;
  destruct n as [|n]; simpl; auto.
Qed.

Lemma resulttype_sub_split: forall ts1 ts2 n,
    (ts1 <ts: ts2) ->
    ((take n ts1) <ts: (take n ts2)) /\
    ((drop n ts1) <ts: (drop n ts2)).
Proof.
  move => ts1 ts2 n Hsub.
  have Hsize: size ts1 = size ts2 by apply resulttype_sub_size_eq.
  inversion Hsub; subst.
  split.
  - constructor.
    + eapply Forall2_length.
      eapply Forall2_take.
      eauto.
    + by eapply Forall2_take.
  - constructor.
    + eapply Forall2_length.
      eapply Forall2_drop.
      eauto.
    + by eapply Forall2_drop.
Qed.

Lemma lt_irrefl: forall x, x < x = false.
Proof.
  move => x.
  induction x as [| n IH]; simpl; auto.
Qed.

Lemma drop_size_cat : forall A (x y : seq A),
  drop (size x) (x ++ y) = y.
Proof.
  move => A x y.
  rewrite drop_cat.
  rewrite ltnn.
  rewrite subnn.
  by rewrite drop0.
Qed.

Lemma take_size_cat : forall A (x y : seq A),
  take (size x) (x ++ y) = x.
Proof.
  move => A x y.
  rewrite take_cat.
  rewrite ltnn.
  rewrite subnn.
  rewrite take0.
  apply cats0.
Qed.

Lemma resulttype_sub_split_sup: forall ts ts1 ts2,
    ts <ts: (ts1 ++ ts2) ->
    ((take (size ts1) ts) <ts: ts1) /\
    ((drop (size ts1) ts) <ts: ts2).
Proof.
  move => ts ts1 ts2 Hsub.
  assert (ts1 = take (size ts1) (ts1 ++ ts2)) as Htake.
  { symmetry. apply take_size_cat.  }
  assert (ts2 = drop (size ts1) (ts1 ++ ts2)) as Hdrop.
  { symmetry. apply drop_size_cat. }
  eapply resulttype_sub_split in Hsub.
  rewrite <- Htake in Hsub.
  rewrite <- Hdrop in Hsub.
  auto.
Qed.

Lemma ftype_sub_refl : forall tf, tf <tf: tf.
Proof.
  move => [[ts1] [ts2]].
  unfold Ftype_sub.
  split; apply resulttype_sub_refl.
Qed.

Lemma ftype_sub_trans: forall tf1 tf2 tf3,
    tf1 <tf: tf2 ->
    tf2 <tf: tf3 ->
    tf1 <tf: tf3.
Proof.
  move => [[ts11] [ts12]] [[ts21] [ts22]] [[ts31] [ts32]] H12 H23.
  unfold Ftype_sub in *; simpl in *.
  destruct H12 as [H12_1 H12_2];
  destruct H23 as [H23_1 H23_2].
  split; eapply resulttype_sub_trans; eauto.
Qed.

Lemma instrtype_sub_refl: forall tf, tf <ti: tf.
Proof.
  move => [[ts1] [ts2]].
  unfold instrtype_sub.
  exists [], [], ts1, ts2.
  assert (forall ts, Forall2 (Valtype_sub) ts ts).
  move => ts.
  induction ts as [| t ts IH]; auto.
  constructor.
  apply valtype_sub_refl.
  auto.
  repeat split; auto.
Qed.

Lemma instrtype_sub_trans: forall tf1 tf2 tf3,
    tf1 <ti: tf2 ->
    tf2 <ti: tf3 ->
    tf1 <ti: tf3.
Proof.
  move => [[ts11] [ts12]] [[ts21] [ts22]] [[ts31] [ts32]] H12 H23.
  unfold instrtype_sub in *.
  destruct H12 as [ts_sub_H12 [ts_H12 [ts11_sub_H12 [ts12_sup_H12 [
    H12_1 [H12_2 [H12_3 [H12_4 H12_5]]]]]]]];
  destruct H23 as [ts_sub_H23 [ts_H23 [ts11_sub_H23 [ts12_sup_H23 [
    H23_1 [H23_2 [H23_3 [H23_4 H23_5]]]]]]]];
  subst.

  (* Think:

  [     ts12supH23      ]
  [tsH12      ts12supH12]
  [???        ts12      ]

  [tsH12      ts11      ]
  [tssubH12   ts11subH12]
  [     ts11subH23      ]

  tsH23
  tssubH23

  *)

  eexists
    (ts_sub_H23 ++ take (List.length ts_H12) ts11_sub_H23),
    (ts_H23  ++ take (List.length ts_H12) ts12_sup_H23),
    (drop (List.length ts_H12) ts11_sub_H23),
    (drop (List.length ts_H12) ts12_sup_H23).
  split.
  - rewrite -catA.
    by rewrite cat_take_drop.
  split.
  - rewrite -catA.
    by rewrite cat_take_drop.
  split.
  - apply resulttype_sub_app. { auto. }
    {
      apply (resulttype_sub_trans _ ts_sub_H12).
      {
        inversion H12_3; subst.
        eapply (resulttype_sub_split _ _ (length ts_H12)) in H23_4 as [H23_41 H23_42].
        rewrite <- H1 in H23_41 at 2.
        rewrite take_size_cat in H23_41.
        auto.
      }
      {
        apply (resulttype_sub_trans _ ts_H12). { auto. }
        eapply (resulttype_sub_split _ _ (length ts_H12)) in H23_5 as [H23_51 H23_52].
        rewrite take_size_cat in H23_51.
        auto.
      }
    }
  split.
  - apply (resulttype_sub_trans _ ts11_sub_H12).
    {
      eapply (resulttype_sub_split _ _ (length ts_H12)) in H23_4 as [H23_41 H23_42].
      inversion H12_3; subst.
      rewrite <- H1 in H23_42 at 2.
      rewrite drop_size_cat in H23_42.
      auto.
    }
    { auto. }
  - apply (resulttype_sub_trans _ ts12_sup_H12). { auto. }
    {
      eapply (resulttype_sub_split _ _ (length ts_H12)) in H23_5 as [H23_51 H23_52].
      rewrite drop_size_cat in H23_52.
      auto.
    }
Qed.

#[global]
Instance valuetype_sub_preorder: RelationClasses.PreOrder Valtype_sub.
Proof.
  constructor.
  - move => x. by apply valtype_sub_refl.
  - move => x y z Hxy Hyz. eapply valtype_sub_trans; eauto.
Qed.

#[global]
Instance resulttype_sub_preorder: RelationClasses.PreOrder Resulttype_sub.
Proof.
  constructor.
  - move => x. destruct x. apply resulttype_sub_refl.
  - move => x y z Hxy Hyz. destruct x, y, z. eapply resulttype_sub_trans; eauto.
Qed.

#[global]
Instance ftype_sub_preorder: RelationClasses.PreOrder Ftype_sub.
Proof.
  constructor.
  - move => x. by apply ftype_sub_refl.
  - move => x y z Hxy Hyz. eapply ftype_sub_trans; eauto.
Qed.

#[global]
Instance instrtype_sub_preorder: RelationClasses.PreOrder instrtype_sub.
Proof.
  constructor.
  - move => x. by apply instrtype_sub_refl.
  - move => x y z Hxy Hyz. eapply instrtype_sub_trans; eauto.
Qed.

Lemma resulttype_sub_empty : forall ts,
  (ts <ts: []) ->
  (ts = []).
Proof.
  move => ts H.
  inversion H; subst.
  simpl in H2.
  by eapply length_zero_iff_nil.
Qed.

Lemma resulttype_empty_sub : forall ts,
  ([] <ts: ts) ->
  (ts = []).
Proof.
  move => ts H.
  inversion H; subst.
  simpl in H2.
  by eapply length_zero_iff_nil.
Qed.