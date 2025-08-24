
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.

Lemma inst_t_context_local_empty: forall s i C,
	Module_instance_ok s i C ->
    C_LOCALS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma inst_t_context_labels_empty: forall s i C,
	Module_instance_ok s i C ->
    C_LABELS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.


Ltac construct_ais_typing :=
  repeat lazymatch goal with
    | H: (?ts1 <ts: ?ts2) |-
        Admin_instrs_ok _ _ [] (?ts1 :-> ?ts2) =>
        try by eapply ais_empty_typing
	| _ : _ |- _ => idtac
  end.

Ltac extract_premise :=
  repeat match goal with
  | H: (_ :-> _) = (_ :-> _) |- _ =>
    inversion H; subst; clear H
  | H: ?x = ?x -> _ |- _ =>
    specialize (H erefl)
  | H: forall x, ?x0 = x -> _ |- _ =>
    try specialize (H _ erefl)
  | H: forall x, _ = _ -> _ |- _ =>
    try specialize (H _ erefl)
  | H: forall x y, _ = _ -> _ |- _ =>
    try specialize (H _ _ erefl)
  | H: forall x y z, _ = _ -> _ |- _ =>
    try specialize (H _ _ _ erefl)
  | H: exists t, ?P |- _ =>
    let extr := fresh "extr" in
    let Hextr := fresh "Hextr" in  
    destruct H as [extr Hextr]
  | H: ?P /\ ?Q |- _ =>
    let H1 := fresh "H1" in  
    let H2 := fresh "H2" in  
    destruct H as [H1 H2]
  | _ => idtac
end.

Ltac destruct_all :=
  repeat match goal with
  | H: exists t, ?P |- _ =>
    let extr := fresh "extr" in
    let Hextr := fresh "Hextr" in
    destruct H as [extr Hextr]
  | H: ?P /\ ?Q |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [H1 H2]
  | _ => idtac
end.

Ltac invert_ais_typing :=
  destruct_functypes;
  repeat match goal with
  | H: Admin_instrs_ok _ _ [] _ |- _ =>
    eapply ais_empty_typing in H;
	idtac "invert_empty"
  | H: Admin_instrs_ok _ _ [fun_coec_val__admininstr ?v_val] ( ?t1s :-> ?t2s ) |- _ =>
    let t1s' := fresh "t1s'" in
	let t2s' := fresh "t2s'" in
	let Hai := fresh "Hai" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_typing_inversion in H
	  as [t1s' [t2s' [Hai Hsub]]];
	eapply value_principal_typing_iff_ai in Hai;
	eapply value_principal_typing_inversion in Hai as [v_t [He1 [He2 [Hve Hnb]]]];
	subst;
	idtac "invert_single_val"
  | H: Admin_instrs_ok _ _ [?v_ai] ( ?t1s :-> ?t2s ) |- _ =>
    let t1s' := fresh "t1s'" in
	let t2s' := fresh "t2s'" in
	let Hai := fresh "Hai" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_typing_inversion in H
	  as [t1s' [t2s' [Hai Hsub]]];
	simpl in Hai;
	idtac "invert_single"
  | H: Admin_instrs_ok _ _ (_ ++ _) _ |- _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
	eapply ais_composition_typing in H as [t3s [H1 H2]];
	idtac "invert_composition"
  | H: Admin_instrs_ok _ _ (_ :: ( _ :: _)) _ |- _ =>
    try rewrite -cat1s in H
  | _ => idtac
  end.

Ltac invert_instrtype_sub :=
  repeat match goal with
  | H: ((?txs :-> ?tys) <ti: ([] :-> []) ) |- _ =>
	eapply instrtype_sub_sub_empty in H
  | H: (([] :-> []) <ti: (?txs :-> ?tys) ) |- _ =>
	eapply instrtype_sub_empty in H
  | H: ((?txs :-> ?tys) <ti: (?tzs :-> []) ) |- _ =>
	eapply instrtype_sub_sub_empty2 in H
  | H: ((?txs :-> ?tys) <ti: ([] :-> ?tzs) ) |- _ =>
	eapply instrtype_sub_sub_empty1 in H
  | _ => idtac
  end.

Lemma Step_pure__nop_preserves : forall v_S v_C v_ft,
	Admin_instrs_ok v_S v_C [(AI_NOP )] v_ft ->
	Step_pure [(AI_NOP )] [] ->
	Admin_instrs_ok v_S v_C [] v_ft.
Proof.
	move => v_S v_C v_ft HType _.
	invert_ais_typing.
	extract_premise.
	invert_instrtype_sub.

	construct_ais_typing.
Qed.

Lemma Step_pure__drop_preserves : forall v_S v_C (v_val : wasm.val) v_ft,
	Admin_instrs_ok v_S v_C [(v_val : admininstr); (AI_DROP )] v_ft ->
	Step_pure [(v_val : admininstr); (AI_DROP )] [] ->
	Admin_instrs_ok v_S v_C [] v_ft.
Proof.
	move => v_S v_C v_val v_ft HType HReduce.
	invert_ais_typing.
	extract_premise.
	rewrite -(cat0s [extr]) in Hsub0.
	specialize (instrtype_sub_compose_le _ _ _ _ _ _ _ _ Hsub Hsub0) as [Hsub1 Hsub2]; auto.
	rewrite cat0s in Hsub1.
	invert_instrtype_sub.

	construct_ais_typing.
Qed.

Lemma Step_pure__select_preserves_helper : forall v_S v_C (v_val_1 : wasm.val) (v_val_2 : wasm.val) (v_c : iN 32) v_t v_ft,
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 (v_c));(AI_SELECT v_t)] v_ft ->
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr)] v_ft /\
	Admin_instrs_ok v_S v_C [(v_val_2 : admininstr)] v_ft.
Proof.
	move => v_S v_C v_val_1 v_val_2 v_c v_t v_ft HType.
    typing_inversion HType.
	eapply value_principal_typing_iff_ai in Hai.
	typing_inversion H4.
	eapply value_principal_typing_iff_ai in Hai0.
	typing_inversion H3.
	typing_inversion H2.
	pose proof Hai as Hai_0.
	pose proof Hai0 as Hai0_0.
	vp_typing_inversion Hai.
	vp_typing_inversion Hai0.
	unfold_principal_typing Hai1;
	inversion Hai1; subst; clear Hai1.
	destruct v_t.
	{ (* Some *)
	  destruct l.
	  { (* Some [] *)
	    inversion Hai2.
	  }
	  destruct l.
	  { (* Some [_] *)
		unfold_principal_typing Hai2.
		inversion Hai2; subst; clear Hai2.
		eapply (instrtype_sub_compose1 _ _ [v; v] _ _ _ _ Hsub1) in Hsub2.
		rewrite cats0 in Hsub2.

		eapply (instrtype_sub_compose_le _ _ _ [v] _ _ _ _ Hsub0) in Hsub2
		  as [Hsub2 Hvsub1]; auto.
		rewrite cats0 in Hsub2.
		eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub2
		  as [Hsub2 Hvsub2]; auto.
		rewrite cats0 in Hsub2.

		eapply resulttype_sub_single_inversion in Hvsub1.
		eapply resulttype_sub_single_inversion in Hvsub2.
		eapply (valtype_sub_non_bot _ _ Hvsub1) in Hnb0.
		eapply (valtype_sub_non_bot _ _ Hvsub2) in Hnb; subst.
		clear Hvsub1 Hvsub2.

		split;
		eapply construct_ais_typing_single; eauto;
		eapply construct_ai_val; eauto;
		by eapply instrtype_sub_refl.
	  }
	  { (* Some (_ :: _ :: _)*)
		inversion Hai2.
	  }
	}
	(* None *)
	unfold_principal_typing Hai2.
	destruct Hai2 as [t [t' [He [Hvs _]]]]; subst.
	inversion He; subst; clear He.
	eapply (instrtype_sub_compose1 _ _ [t; t] _ _ _ _ Hsub1) in Hsub2.
	rewrite cats0 in Hsub2.

	eapply (instrtype_sub_compose_le _ _ _ [t] _ _ _ _ Hsub0) in Hsub2
		as [Hsub2 Hvsub1]; auto.
	rewrite cats0 in Hsub2.
	eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub2
		as [Hsub2 Hvsub2]; auto.
	rewrite cats0 in Hsub2.

	eapply resulttype_sub_single_inversion in Hvsub1.
	eapply resulttype_sub_single_inversion in Hvsub2.
	eapply (valtype_sub_non_bot _ _ Hvsub1) in Hnb0.
	eapply (valtype_sub_non_bot _ _ Hvsub2) in Hnb; subst.
	clear Hvsub1 Hvsub2.

	split;
	eapply construct_ais_typing_single; eauto;
	eapply construct_ai_val; eauto;
	by eapply instrtype_sub_refl.
Qed.

Lemma Step_pure__select_true_preserves : forall v_S v_C (v_val_1 : wasm.val) (v_val_2 : wasm.val) (v_c : iN 32) v_t v_ft,
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 (v_c));(AI_SELECT v_t)] v_ft ->
	Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 (v_c));(AI_SELECT v_t)] [(v_val_1 : admininstr)] ->
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr)] v_ft.
Proof.
	move=> v_S v_C v_val_1 v_val_2 v_c v_t v_ft HType HReduce.
	apply Step_pure__select_preserves_helper in HType as [H1 _].
	auto.
Qed.

Lemma Step_pure__select_false_preserves : forall v_S v_C (v_val_1 : wasm.val) (v_val_2 : wasm.val) (v_c : iN 32) v_t v_ft,
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 (v_c));(AI_SELECT v_t)] v_ft ->
	Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 (v_c));(AI_SELECT v_t)] [(v_val_2 : admininstr)] ->
	Admin_instrs_ok v_S v_C [(v_val_2 : admininstr)] v_ft.
Proof.
	move=> v_S v_C v_val_1 v_val_2 v_c v_t v_ft HType HReduce.
	apply Step_pure__select_preserves_helper in HType as [_ H2].
	auto.
Qed.

Lemma Step_pure__if_preserves_helper : forall v_S v_C (v_c : iN 32) (v_bt: blocktype) (v_instrs_1 : (list instr)) (v_instrs_2 : (list instr)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_IFELSE v_bt v_instrs_1 v_instrs_2)] v_ft ->
	(Admin_instrs_ok v_S v_C [(AI_BLOCK v_bt v_instrs_1)] v_ft /\
	Admin_instrs_ok v_S v_C [(AI_BLOCK v_bt v_instrs_2)] v_ft).
Proof.
	move => v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft HType.
	typing_inversion HType.
	typing_inversion H1.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	unfold_principal_typing Hai0.
	destruct Hai0 as [t [t' [He [H2 [H3 H4]]]]].
	inversion He; subst; clear He.
	
	eapply instrtype_sub_compose1 in Hsub0.
	2: apply Hsub.
	rewrite cats0 in Hsub0.
	split;
	eapply construct_ais_typing_single; [| eauto| |eauto].
	all: eapply (AI_ok_instr _ _ (instr_BLOCK _ _));
	constructor; eauto.
Qed.

Lemma Step_pure__if_true_preserves : forall v_S v_C (v_c : iN 32) (v_bt: blocktype) (v_instrs_1 : (list instr)) (v_instrs_2 : (list instr)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_IFELSE v_bt v_instrs_1 v_instrs_2)] v_ft ->
	Step_pure [(AI_CONST I32 v_c);(AI_IFELSE v_bt v_instrs_1 v_instrs_2)] [(AI_BLOCK v_bt v_instrs_1)] ->
	Admin_instrs_ok v_S v_C [(AI_BLOCK v_bt v_instrs_1)] v_ft.
Proof.
	move => v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft HType HReduce.
	eapply (Step_pure__if_preserves_helper) in HType.
	by destruct HType.
Qed.

Lemma Step_pure__if_false_preserves : forall v_S v_C (v_c : iN 32) (v_bt: blocktype) (v_instrs_1 : (list instr)) (v_instrs_2 : (list instr)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_IFELSE v_bt v_instrs_1 v_instrs_2)] v_ft ->
	Step_pure [(AI_CONST I32 v_c);(AI_IFELSE v_bt v_instrs_1 v_instrs_2)] [(AI_BLOCK v_bt v_instrs_2)] ->
	Admin_instrs_ok v_S v_C [(AI_BLOCK v_bt v_instrs_2)] v_ft.
Proof.
	move => v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft HType HReduce.
	eapply (Step_pure__if_preserves_helper) in HType.
	by destruct HType.
Qed.

(*
Lemma construct_ai_from_ais_val_single : forall v_S v_C (v_val: wasm.val) t1s t2s t1s' t2s',
	Admin_instrs_ok v_S v_C [v_val: admininstr] (t1s :-> t2s) ->
	((t1s' :-> t2s') <ti: (t1s :-> t2s)) ->
	ai_principal_typing v_S v_C (v_val: admininstr) (t1s' :-> t2s') ->
	Admin_instr_ok v_S v_C (v_val: admininstr) (t1s' :-> t2s').
Proof.
	move=> v_S v_C v_val t1s t2s t1s' t2s' HType Hsub Hpt.
	unfold_principal_typing Hpt;
	destruct v_val.
	4: destruct Hpt as [v_ft [Hpt Headdr]].
	all: inversion Hpt; subst; clear Hpt.
	- eapply (AI_ok_instr _ _ (instr_CONST _ _)).
	  eapply instr_ok_const.
	- eapply (AI_ok_instr _ _ (instr_VCONST _ _)).
	  destruct v_vectype.
	  eapply instr_ok_vconst.
	- eapply (AI_ok_instr _ _ (instr_REF_NULL _)).
	  eapply instr_ok_ref_null.
	all: econstructor. eauto.
Qed. *)

Lemma Step_pure__label_vals_preserves : forall v_S v_C (v_n : n) (v_instrs : (list instr)) (v_val : (list wasm.val)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instrs (map fun_coec_val__admininstr v_val))] v_ft ->
	Step_pure [(AI_LABEL_ v_n v_instrs (map fun_coec_val__admininstr v_val))] (map fun_coec_val__admininstr v_val) ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_val) v_ft.
Proof.
	move => v_S v_C v_n v_instrs v_val v_ft HType HReduce.
	typing_inversion HType.
	unfold ai_principal_typing in Hai.
	destruct Hai as [t [t' [He [Hitype [Hatype Hlen]]]]].
	inversion He; subst; clear He.
	
	unfold_instrtype_sub Hsub; subst.
	eapply resulttype_sub_empty in Hsub1; subst.
	eapply (AIs_ok_sub _ _ _ _ _ (ts_sub ++ []) (ts_sub ++ t')).
	2: by rewrite !cats0.
	2: {
		apply resulttype_sub_app; auto.
		by apply resulttype_sub_refl.
	}
	eapply (AIs_ok_frame).
	eapply construct_ais_vals'.
	eauto.
Qed.

Lemma Step_pure__br_zero_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val' : (list wasm.val)) (v_val : (list wasm.val)) (v_instr : (list instr)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val') (@app _ (map fun_coec_val__admininstr v_val) (@app _ [AI_BR 0] (map fun_coec_instr__admininstr v_instr)))))] v_ft ->
	((List.length v_val) = v_n) ->
	Admin_instrs_ok v_S v_C (@app _ (map fun_coec_val__admininstr v_val) (map fun_coec_instr__admininstr v_instr')) v_ft.
Proof.
	move => v_S v_C v_n v_instr' v_val' v_val v_instr v_ft HType Hlength.
	destruct_functypes.
	typing_inversion HType;
	unfold ai_principal_typing in Hai;
	destruct Hai as [t [t' [Heq [Hi [Hai Hlen]]]]];
	inversion Heq; subst; clear Heq.
	typing_inversion Hai;
	typing_inversion H2;
	typing_inversion H3.
	typing_inversion H2;
	unfold_principal_typing Hai;
	destruct Hai as [t1 [t2 [v_t [H5 [H6 H7]]]]];
	inversion H5; subst; clear H5;
	rewrite lookup_label_0 in Hsub0;
	unfold fun_proj_list_0, fun_list__res_list in Hsub0.
	vals_typing_inversion H1.
	vals_typing_inversion H0.
	eapply (instrtype_sub_compose_le _ _ _ _ _ _ _ _ Hsub2) in Hsub0
	  as [Hsub0 Hs].
	2: eapply Forall2_length in Hforall0;
	   by rewrite Hlen in Hforall0.

	eapply construct_ais_instrtype_sub.
	2: eapply Hsub.
	eapply (construct_ais_compose _ _ _ _ _ t).
	2: by eapply (AIs_ok_instrs).
	eapply construct_ais_vals.
	2: by apply Hforall0.
	by eapply instrtype_sub_iff_resulttype_sub.
Qed.

Lemma Step_pure__br_succ_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list wasm.val)) (v_l : labelidx) (v_instr : (list instr)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [AI_BR (v_l + 1)] (map fun_coec_instr__admininstr v_instr))))] v_ft ->
	Step_pure [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [AI_BR (v_l + 1)] (map fun_coec_instr__admininstr v_instr))))] (@app _ (map fun_coec_val__admininstr v_val) [(AI_BR v_l)]) ->
	Admin_instrs_ok v_S v_C (@app _ (map fun_coec_val__admininstr v_val) [(AI_BR v_l)]) v_ft.
Proof.
	move => v_S v_C v_n v_instr' v_val v_l v_instr v_ft HType HReduce.
	typing_inversion HType;
	simpl in Hai;
	extract_premise.
	typing_inversion H2.
	eapply construct_ais_instrtype_sub.
	eapply construct_ais_compose.
	{
		eapply construct_ais_vals'.
		eapply H0.
	}
	2: eapply Hsub.

	rewrite -cat1s in H4.
	typing_inversion H4.
	typing_inversion H2;
	simpl in Hai;
	extract_premise.
	unfold_instrtype_sub Hsub0.
	subst.
	eapply construct_ais_typing_single.
	2: {
		eexists [], [], (ts ++ ts11_sub), extr0.
		split. auto.
		split. auto.
		split. eapply resulttype_sub_refl.
		split. eapply resulttype_sub_app; eauto.
		eapply resulttype_sub_refl.
	}
	eapply (AI_ok_instr _ _ (instr_BR _)).


	assert (([extr: resulttype] @@ C_LABELS v_C) =
		(C_LABELS (prepend_label v_C extr))).
	{
	simpl. auto.
	}
	rewrite H.
	rewrite lookup_label_1.
	rewrite catA.
	constructor.
	{
		rewrite addn1 in H2.
		move/ltP in H2.
		apply/ltP.
		eapply Nat.succ_lt_mono in H2.
		by apply H2.
	}
	reflexivity.
Qed.

Lemma Step_pure__br_if_true_preserves : forall v_S v_C (v_c : iN 32) (v_l : labelidx) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_BR_IF v_l)] v_ft ->
	Step_pure [(AI_CONST I32 v_c);(AI_BR_IF v_l)] [(AI_BR v_l)] ->
	Admin_instrs_ok v_S v_C [(AI_BR v_l)] v_ft.
Proof.
	move => v_S v_C v_c v_l v_ft HType HReduce.
	typing_inversion HType.
	typing_inversion H1.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	unfold_principal_typing Hai0.
	destruct Hai0 as [t [He1 [H1 H2]]].
	inversion He1; subst; clear He1.

	eapply construct_ais_typing_single.
	eapply (AI_ok_instr _ _ (instr_BR _)).
	eapply (instr_ok_br _ _ []).
	auto.
	auto.
	eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub) in Hsub0.
	rewrite cats0 in Hsub0.
	eapply Hsub0.
Qed.

Lemma Step_pure__br_if_false_preserves : forall v_S v_C (v_c : iN 32) (v_l : labelidx) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_BR_IF v_l)] v_ft ->
	Step_pure [(AI_CONST I32 v_c);(AI_BR_IF v_l)] [] ->
	Admin_instrs_ok v_S v_C [] v_ft.
Proof.
	move => v_S v_C v_c v_l v_ft HType HReduce.
	typing_inversion HType.
	typing_inversion H1.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	unfold_principal_typing Hai0.
	destruct Hai0 as [t [He1 [H1 H2]]].
	inversion He1; subst; clear He1.

	eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub) in Hsub0.
	rewrite cats0 in Hsub0.
	eapply ais_empty_typing.
	unfold_instrtype_sub Hsub0; subst.
	apply resulttype_sub_app.
	auto.
	eapply resulttype_sub_trans; eauto.
Qed.

Lemma proj_identity : forall A a, mk_list A (fun_proj_list_0 A a) = a.
Proof.
	destruct a.
	auto.
Qed.

Lemma Step_pure__br_table_lt_preserves : forall v_S v_C (v_i : uN 32) (v_l : (list labelidx)) (v_l' : labelidx) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_i);(AI_BR_TABLE v_l v_l')] v_ft ->
	Step_pure [(AI_CONST I32 (v_i : u32));(AI_BR_TABLE v_l v_l')] [(AI_BR (lookup_total v_l (fun_u32__nat v_i)))] ->
	(fun_u32__nat v_i < Datatypes.length v_l) -> 
	Admin_instrs_ok v_S v_C [(AI_BR (lookup_total v_l (fun_u32__nat v_i)))] v_ft.
Proof.
	move => v_S v_C v_i v_l v_l' v_ft HType HReduce H.
	typing_inversion HType.

	typing_inversion H1.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	destruct Hai as [t [t' [v_t [H1 [H2 [H3 [H4 H5]]]]]]].
	inversion H1; subst; clear H1.
	rewrite catA in Hsub0.
	eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub) in Hsub0.
	rewrite cats0 in Hsub0.

	eapply construct_ais_typing_single.
	eapply (AI_ok_instr _ _ (instr_BR _)).
	eapply (instr_ok_br _ _ t _ t').
	{
	  eapply Forall_nth in H2.
	  apply H2.
	  by apply/ltP.
	}
    {
		reflexivity.		
	}
	eapply (instrtype_sub_trans _ ((t ++ v_t) :-> t')).
	{
	  exists [], [], (t ++ v_t), t'.
	  do 4 split; auto. 2: eapply resulttype_sub_refl.
	  eapply resulttype_sub_app. eapply resulttype_sub_refl.
	  eapply (Forall_nth) in H3.
	  unfold Resulttype_subtype.
	  rewrite proj_identity.
	  eapply H3.
	  by apply/ltP.
	}
	auto.
Qed.

Lemma Step_pure__br_table_ge_preserves : forall v_S v_C (v_i : uN 32) (v_l : (list labelidx)) (v_l' : labelidx) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_i);(AI_BR_TABLE v_l v_l')] v_ft ->
	Step_pure [(AI_CONST I32 v_i);(AI_BR_TABLE v_l v_l')] [(AI_BR v_l')] ->
	(List.length v_l <= fun_u32__nat v_i) ->
	Admin_instrs_ok v_S v_C [(AI_BR v_l')] v_ft.
Proof.
	move => v_S v_C v_i v_l v_l' v_ft HType HReduce H.
	typing_inversion HType.

	typing_inversion H1.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	destruct Hai as [t [t' [v_t [H1 [H2 [H3 [H4 H5]]]]]]].
	inversion H1; subst; clear H1.
	rewrite catA in Hsub0.
	eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub) in Hsub0.
	rewrite cats0 in Hsub0.

	eapply (construct_ais_typing_single).
	eapply (AI_ok_instr _ _ (instr_BR _)).
	eapply (instr_ok_br _ _ t _ t').
	{
	  apply H4.
	}
    {
		reflexivity.		
	}
	eapply (instrtype_sub_trans _ ((t ++ v_t) :-> t')).
	{
	  exists [], [], (t ++ v_t), t'.
	  do 4 split; auto. 2: eapply resulttype_sub_refl.
	  eapply resulttype_sub_app. eapply resulttype_sub_refl.
	  unfold Resulttype_subtype.
	  rewrite proj_identity.
	  eapply H5.
	}
	auto.
Qed.

Lemma Step_pure__frame_vals_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val : (list wasm.val)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_FRAME_ v_n v_f (map fun_coec_val__admininstr v_val))] v_ft ->
	Step_pure [(AI_FRAME_ v_n v_f (map fun_coec_val__admininstr v_val))] (map fun_coec_val__admininstr v_val) ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_val) v_ft.
Proof.
	move => v_S v_C v_n v_f v_val v_ft HType HReduce.
	typing_inversion HType.
	simpl in Hai;
	extract_premise.
	inversion H1; subst.
	eapply construct_ais_instrtype_sub.
	eapply construct_ais_vals'. eauto.
	eauto.
Qed.

Lemma Step_pure__return_frame_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val' : (list wasm.val)) (v_val : (list wasm.val)) (v_instr : (list instr)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_FRAME_ v_n v_f (@app _ (map fun_coec_val__admininstr v_val') (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr)))))] v_ft ->
	Step_pure [(AI_FRAME_ v_n v_f (@app _ (map fun_coec_val__admininstr v_val') (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr)))))] (map fun_coec_val__admininstr v_val) ->
	((List.length v_val) = v_n) ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_val) v_ft.
Proof.
	move => v_S v_C v_n v_f v_val' v_val v_instr v_ft HType HReduce HLength.
	typing_inversion HType.
	simpl in Hai.
	extract_premise.
	inversion H1; subst; clear H1.
	typing_inversion H7.
	typing_inversion H3.
	rewrite -cat1s in H5.
	typing_inversion H5.

	typing_inversion H3.
	simpl in Hai.
	extract_premise.
	inversion H7; subst; clear H7.
	simpl in H9.
	rewrite H3 in H9.
	inversion H9; subst; clear H9.
	eapply app_inv_tail in H; subst.
	vals_typing_inversion H4.
	unfold _append, Append_Option, option_append in H3.
	inversion H3; subst; clear H3.

	eapply construct_ais_instrtype_sub.
	eapply construct_ais_vals.
	- by eapply instrtype_sub_refl.
	- by eapply Hforall.

	eapply (instrtype_sub_compose_le _ _ _ _ _ _ _ _ Hsub1) in Hsub0
	  as [Hsub0 Hsub2].
	2: {
		eapply Forall2_length in Hforall.
		rewrite H0 in Hforall.
		auto.
	}
	eapply instrtype_sub_trans.
	{
		eapply instrtype_sub_iff_resulttype_sub in Hsub2.
		eauto.
	}
	auto.
Qed.

Lemma Step_pure__return_label_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list wasm.val)) (v_instr : (list instr)) v_ft,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr))))] v_ft ->
	Step_pure [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr))))] (@app _ (map fun_coec_val__admininstr v_val) [(AI_RETURN )]) ->
	Admin_instrs_ok v_S v_C (@app _ (map fun_coec_val__admininstr v_val) [(AI_RETURN )]) v_ft.
Proof.
	move => v_S v_C v_n v_instr' v_val v_instr v_ft HType HReduce.
	typing_inversion HType.
	simpl in Hai; extract_premise; subst.
	typing_inversion H2.
	rewrite -cat1s in H3.
	typing_inversion H3.
	typing_inversion H2.
	simpl in Hai; extract_premise; subst.
	inversion H5; subst; clear H5.
	simpl in H7.
	rewrite H2 in H7.
	inversion H7; subst; clear H7.
	eapply app_inv_tail in H; subst.
	unfold_instrtype_sub Hsub0; subst.

	eapply construct_ais_instrtype_sub.
	2: eapply Hsub.
	eapply construct_ais_compose with (t2s := (ts_sub ++ extr1 ++ v_t)).
	{
		eapply construct_ais_instrtype_sub.
		eapply construct_ais_vals'.
		eapply H0.
		eapply instrtype_sub_iff_resulttype_sub.
		eapply resulttype_sub_app; eauto.
	}
	eapply construct_ais_typing_single.
	2: by eapply instrtype_sub_refl.
	eapply AI_ok_instr with (v_instr := instr_RETURN).
	rewrite catA.
	econstructor.
	auto.
Qed.

Lemma Step_pure__unop_val_preserves : forall v_S v_C v_t v_c_1 v_unop v_c v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_UNOP v_t v_unop)] v_ft ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_UNOP v_t v_unop)] [(AI_CONST v_t v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c)] v_ft.
Proof.
	move => v_S v_C t v unop_op v_c tf HType HReduce.
	typing_inversion HType.
	typing_inversion H1.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.

	eapply construct_ais_typing_single.
	eapply (AI_ok_instr _ _ (instr_CONST _ _)).
	constructor.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__binop_val_preserves : forall v_S v_C v_t v_c_1 v_c_2 v_binop v_c v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_BINOP v_t v_binop)] v_ft ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_BINOP v_t v_binop)] [(AI_CONST v_t v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c)] v_ft.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_binop v_c v_ft HType HReduce.
	typing_inversion HType.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H3.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	unfold_principal_typing Hai0.
	inversion Hai0; subst; clear Hai0.
	eapply (instrtype_sub_compose1 _ _ [v_t: valtype] _ _ _ _ Hsub1) in Hsub0.
	rewrite cats0 in Hsub0.

	eapply construct_ais_typing_single.
	eapply (AI_ok_instr _ _ (instr_CONST _ _)).
	constructor.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__testop_preserves : forall v_S v_C v_t v_c_1 v_testop (v_c : iN 32) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_TESTOP v_t v_testop)] v_ft ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_TESTOP v_t v_testop)] [(AI_CONST I32 v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c)] v_ft.
Proof.
	move => v_S v_C t v unop_op v_c tf HType HReduce.
	typing_inversion HType.
	typing_inversion H1.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.

	eapply construct_ais_typing_single.
	eapply (AI_ok_instr _ _ (instr_CONST _ _)).
	constructor.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__relop_preserves : forall v_S v_C v_t v_c_1 v_c_2 v_relop (v_c : iN 32) v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_RELOP v_t v_relop)] v_ft ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_RELOP v_t v_relop)] [(AI_CONST I32 v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c)] v_ft.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_relop v_c v_ft HType HReduce.
	typing_inversion HType.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H3.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	unfold_principal_typing Hai0.
	inversion Hai0; subst; clear Hai0.
	eapply (instrtype_sub_compose1 _ _ [v_t: valtype] _ _ _ _ Hsub1) in Hsub0.
	rewrite cats0 in Hsub0.

	eapply construct_ais_typing_single.
	eapply (AI_ok_instr _ _ (instr_CONST _ _)).
	constructor.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__cvtop_val_preserves : forall v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_c v_ft,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t_1 v_c_1);(AI_CVTOP v_t_2 v_t_1 v_cvtop)] v_ft ->
	Step_pure [(AI_CONST v_t_1 v_c_1);(AI_CVTOP v_t_2 v_t_1 v_cvtop)] [(AI_CONST v_t_2 v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST v_t_2 v_c)] v_ft.
Proof.
	move => v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_c v_ft HType HReduce.
	typing_inversion HType.
	typing_inversion H1.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.

	eapply construct_ais_typing_single.
	eapply (AI_ok_instr _ _ (instr_CONST _ _)).
	constructor.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma size_eq_cat: forall A (l1 l2 l1' l2': list A),
  size l1 = size l2 ->
  l1' ++ l1 = l2' ++ l2 ->
  l1' = l2' /\ l1 = l2.
Proof.
  move=> A l1 l2 l1' l2' Hsize Hcat.
  
  have Hsize_cat: size (l1' ++ l1) = size (l2' ++ l2) by rewrite Hcat.
  rewrite !size_cat in Hsize_cat.
  
  have Hsize': size l1' = size l2'.
  {
	rewrite Hsize in Hsize_cat.
    move/eqP in Hsize_cat.
	rewrite eqn_add2r in Hsize_cat.
	by apply/eqP.
  }
  
  have Htake: take (size l1') (l1' ++ l1) = take (size l1') (l2' ++ l2).
  { by rewrite Hcat. }
  
  rewrite take_size_cat // in Htake.
  rewrite Hsize' take_size_cat // in Htake.
  
  split; first by exact Htake.
  
  have Hdrop: drop (size l1') (l1' ++ l1) = drop (size l1') (l2' ++ l2).
  { by rewrite Hcat. }
  
  rewrite drop_size_cat // in Hdrop.
  rewrite Hsize' drop_size_cat // in Hdrop.
Qed.


Lemma Step_pure__local_tee_preserves : forall v_S v_C (v_val : wasm.val) (v_x : idx) v_ft,
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(AI_LOCAL_TEE v_x)] v_ft ->
	Step_pure [(v_val : admininstr);(AI_LOCAL_TEE v_x)] [(v_val : admininstr);(v_val : admininstr);(AI_LOCAL_SET v_x)] ->
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(v_val : admininstr);(AI_LOCAL_SET v_x)] v_ft.
Proof.
	move => v_S v_C v_val v_x v_ft HType HReduce.
	typing_inversion HType.

	pose proof H1 as H1_0.
	eapply ais_single_typing_inversion' in H1_0.
	typing_inversion H1.
	eapply value_principal_typing_iff_ai in Hai.
	typing_inversion H2.
	unfold_principal_typing Hai0.
	destruct Hai0 as [v_t [H1 [H2 H3]]].
	inversion H1; subst; clear H1.

	destruct v_val.
	2: destruct v_vectype.
	all: unfold_principal_typing Hai.
	4: destruct Hai as [Hai [v_ft Heok]].
	{	inversion Hai; subst; clear Hai;
		unfold_instrtype_sub Hsub; subst;
		eapply resulttype_sub_empty in Hsub2; subst;
		eapply (construct_ais_compose _ _
		[_ ; _] [_]).
		eapply (construct_ais_compose _ _
		[_] [_]).

		instantiate (1 := ts_sub ++ ts12_sup).
		eapply construct_ais_typing_single.
		eapply H1_0.
		eapply instrtype_sub_refl.

		typing_inversion H1_0.
		unfold_principal_typing Hpt.
		inversion Hpt; subst; clear Hpt.
		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_CONST _ _)).
		constructor.
		instantiate (1 := (ts_sub ++ ts12_sup) ++ ts12_sup).
		unfold instrtype_sub.
		eexists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), [], (ts12_sup).
		split. by rewrite cats0.
		split. auto.
		split. by apply resulttype_sub_refl.
		split. by apply resulttype_sub_refl.
		by apply Hsub3.

		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_LOCAL_SET _)).
		constructor.
		auto.
		reflexivity.

		pose proof Hsub0 as Hsub0_0.
		apply instrtype_sub_cancel_left in Hsub0.
		eapply (instrtype_sub_compose1) with (ts3 := []).
		2: eapply Hsub0.
		exists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), ts12_sup, [].
		split. auto.
		split. by rewrite cats0.
		split. by apply resulttype_sub_refl.
		split. 2: by apply resulttype_sub_refl.
		unfold_instrtype_sub Hsub0_0; subst.
		eapply resulttype_sub_trans.
		2: by apply Hsub2.
		eapply size_eq_cat in H as [_ H]; subst.
		eapply resulttype_sub_refl.
		inversion Hsub3. inversion Hsub2. subst.
		rewrite !size_length.
		rewrite H7. rewrite -H3. reflexivity.
	}
	{   inversion Hai; subst; clear Hai;		
		unfold_instrtype_sub Hsub; subst.
		eapply resulttype_sub_empty in Hsub2; subst.
		eapply (construct_ais_compose _ _
		[_ ; _] [_]).
		eapply (construct_ais_compose _ _
		[_] [_]).

		instantiate (1 := ts_sub ++ ts12_sup).
		eapply construct_ais_typing_single.
		eapply H1_0.
		eapply instrtype_sub_refl.

		typing_inversion H1_0.
		unfold_principal_typing Hpt.
		inversion Hpt; subst; clear Hpt.
		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_VCONST _ _)).
		constructor.
		instantiate (1 := (ts_sub ++ ts12_sup) ++ ts12_sup).
		unfold instrtype_sub.
		eexists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), [], (ts12_sup).
		split. by rewrite cats0.
		split. auto.
		split. by apply resulttype_sub_refl.
		split. by apply resulttype_sub_refl.
		by apply Hsub3.

		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_LOCAL_SET _)).
		constructor.
		auto.
		reflexivity.

		pose proof Hsub0 as Hsub0_0.
		apply instrtype_sub_cancel_left in Hsub0.
		eapply (instrtype_sub_compose1) with (ts3 := []).
		2: eapply Hsub0.
		exists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), ts12_sup, [].
		split. auto.
		split. by rewrite cats0.
		split. by apply resulttype_sub_refl.
		split. 2: by apply resulttype_sub_refl.
		unfold_instrtype_sub Hsub0_0; subst.
		eapply resulttype_sub_trans.
		2: by apply Hsub2.
		eapply size_eq_cat in H as [_ H]; subst.
		eapply resulttype_sub_refl.
		inversion Hsub3. inversion Hsub2. subst.
		rewrite !size_length.
		rewrite H7. rewrite -H3. reflexivity.
	}
	{   inversion Hai; subst; clear Hai;		
		unfold_instrtype_sub Hsub; subst.
		eapply resulttype_sub_empty in Hsub2; subst.
		eapply (construct_ais_compose _ _
		[_ ; _] [_]).
		eapply (construct_ais_compose _ _
		[_] [_]).

		instantiate (1 := ts_sub ++ ts12_sup).
		eapply construct_ais_typing_single.
		eapply H1_0.
		eapply instrtype_sub_refl.

		typing_inversion H1_0.
		unfold_principal_typing Hpt.
		inversion Hpt; subst; clear Hpt.
		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_REF_NULL _)).
		constructor.
		instantiate (1 := (ts_sub ++ ts12_sup) ++ ts12_sup).
		unfold instrtype_sub.
		eexists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), [], (ts12_sup).
		split. by rewrite cats0.
		split. auto.
		split. by apply resulttype_sub_refl.
		split. by apply resulttype_sub_refl.
		by apply Hsub3.

		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_LOCAL_SET _)).
		constructor.
		auto.
		reflexivity.

		pose proof Hsub0 as Hsub0_0.
		apply instrtype_sub_cancel_left in Hsub0.
		eapply (instrtype_sub_compose1) with (ts3 := []).
		2: eapply Hsub0.
		exists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), ts12_sup, [].
		split. auto.
		split. by rewrite cats0.
		split. by apply resulttype_sub_refl.
		split. 2: by apply resulttype_sub_refl.
		unfold_instrtype_sub Hsub0_0; subst.
		eapply resulttype_sub_trans.
		2: by apply Hsub2.
		eapply size_eq_cat in H as [_ H]; subst.
		eapply resulttype_sub_refl.
		inversion Hsub3. inversion Hsub2. subst.
		rewrite !size_length.
		rewrite H7. rewrite -H3. reflexivity.
	}

	{
		inversion Hai; subst; clear Hai.
		unfold_instrtype_sub Hsub; subst.
		eapply resulttype_sub_empty in Hsub2; subst.
		eapply (construct_ais_compose _ _
		[_ ; _] [_]).
		eapply (construct_ais_compose _ _
		[_] [_]).

		instantiate (1 := ts_sub ++ ts12_sup).
		eapply construct_ais_typing_single.
		eapply H1_0.
		eapply instrtype_sub_refl.

		typing_inversion H1_0.
		unfold_principal_typing Hpt.
		inversion Hpt; subst; clear Hpt.
		eapply construct_ais_typing_single.
		econstructor. eapply Heok.
		instantiate (1 := (ts_sub ++ ts12_sup) ++ ts12_sup).
		unfold instrtype_sub.
		eexists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), [], (ts12_sup).
		split. by rewrite cats0.
		split. auto.
		split. by apply resulttype_sub_refl.
		split. by apply resulttype_sub_refl.
		by apply Hsub3.

		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_LOCAL_SET _)).
		constructor.
		auto.
		reflexivity.

		pose proof Hsub0 as Hsub0_0.
		apply instrtype_sub_cancel_left in Hsub0.
		eapply (instrtype_sub_compose1) with (ts3 := []).
		2: eapply Hsub0.
		exists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), ts12_sup, [].
		split. auto.
		split. by rewrite cats0.
		split. by apply resulttype_sub_refl.
		split. 2: by apply resulttype_sub_refl.
		unfold_instrtype_sub Hsub0_0; subst.
		eapply resulttype_sub_trans.
		2: by apply Hsub2.
		eapply size_eq_cat in H as [_ H]; subst.
		eapply resulttype_sub_refl.
		inversion Hsub3. inversion Hsub2. subst.
		rewrite !size_length.
		rewrite H7. rewrite -H3. reflexivity.
	}
	{   inversion Hai; subst; clear Hai;		
		unfold_instrtype_sub Hsub; subst.
		eapply resulttype_sub_empty in Hsub2; subst.
		eapply (construct_ais_compose _ _
		[_ ; _] [_]).
		eapply (construct_ais_compose _ _
		[_] [_]).

		instantiate (1 := ts_sub ++ ts12_sup).
		eapply construct_ais_typing_single.
		eapply H1_0.
		eapply instrtype_sub_refl.

		typing_inversion H1_0.
		unfold_principal_typing Hpt.
		inversion Hpt; subst; clear Hpt.
		eapply construct_ais_typing_single.
		econstructor.
		instantiate (1 := (ts_sub ++ ts12_sup) ++ ts12_sup).
		unfold instrtype_sub.
		eexists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), [], (ts12_sup).
		split. by rewrite cats0.
		split. auto.
		split. by apply resulttype_sub_refl.
		split. by apply resulttype_sub_refl.
		by apply Hsub3.

		eapply construct_ais_typing_single.
		eapply (AI_ok_instr _ _ (instr_LOCAL_SET _)).
		constructor.
		auto.
		reflexivity.

		pose proof Hsub0 as Hsub0_0.
		apply instrtype_sub_cancel_left in Hsub0.
		eapply (instrtype_sub_compose1) with (ts3 := []).
		2: eapply Hsub0.
		exists (ts_sub ++ ts12_sup), (ts_sub ++ ts12_sup), ts12_sup, [].
		split. auto.
		split. by rewrite cats0.
		split. by apply resulttype_sub_refl.
		split. 2: by apply resulttype_sub_refl.
		unfold_instrtype_sub Hsub0_0; subst.
		eapply resulttype_sub_trans.
		2: by apply Hsub2.
		eapply size_eq_cat in H as [_ H]; subst.
		eapply resulttype_sub_refl.
		inversion Hsub3. inversion Hsub2. subst.
		rewrite !size_length.
		rewrite H7. rewrite -H3. reflexivity.
	}
Qed.

Lemma Step_pure__ref_is_null_helper : forall v_S v_C v_rt v_ft v_n,
	Admin_instrs_ok v_S v_C [REF_NULL v_rt: admininstr; AI_REF_IS_NULL] v_ft ->
	Step_pure [REF_NULL v_rt: admininstr; AI_REF_IS_NULL] [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) v_n)] ->
	Admin_instrs_ok v_S v_C [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) v_n)] v_ft.
Proof.
	move => v_S v_C v_rt v_ft v_n HType HReduce.
	typing_inversion HType.
	typing_inversion H1.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	destruct Hai as [rt Ht].
	inversion Ht; subst; clear Ht.
	eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub0
	  as [Hsub0 Hsub1].
	2: auto.
	eapply construct_ais_typing_single.
	2: eapply Hsub0.
	eapply AI_ok_instr with (v_instr := instr_CONST _ _).
	constructor.
Qed.

Lemma Step_pure__ref_is_null_true_preserves : forall v_S v_C v_rt v_ft,
	Admin_instrs_ok v_S v_C [REF_NULL v_rt: admininstr; AI_REF_IS_NULL] v_ft ->
	Step_pure [REF_NULL v_rt: admininstr; AI_REF_IS_NULL] [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) 1)] ->
	Admin_instrs_ok v_S v_C [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) 1)] v_ft.
Proof.
	intros.
	by apply Step_pure__ref_is_null_helper with (v_n := 1) in H.
Qed.

Lemma Step_pure_before_ref_is_null_false_iff : forall (v_ref: ref),
    ~(Step_pure_before_ref_is_null_false [v_ref: admininstr; AI_REF_IS_NULL]) <->
	(forall v_rt, v_ref <> REF_NULL v_rt).
Proof.
	move => v_ref.
	assert (Hallex: forall U P, (∀ n : U, ¬ P n) <-> ¬ ∃ n : U, P n). {
		split.
		apply Classical_Pred_Type.all_not_not_ex.
		apply Classical_Pred_Type.not_ex_all_not.
	}
	rewrite Hallex.
	eapply not_iff_compat.
	split.
	{
		move=> H.
		inversion H; subst.
		exists v_rt.
		destruct v_ref; unfold fun_coec_ref__admininstr in H0.
		injection H0 as H1; subst; auto.
		all: discriminate.
	}
	{
		move=> [v_rt Heq]; subst.
		econstructor. eauto.
	}
Qed.

Lemma Step_pure__ref_is_null_false_preserves : forall v_S v_C (v_ref: ref) v_ft,
	Admin_instrs_ok v_S v_C [v_ref: admininstr; AI_REF_IS_NULL] v_ft ->
	Step_pure [v_ref: admininstr; AI_REF_IS_NULL] [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) 0)] ->
	¬ Step_pure_before_ref_is_null_false [v_ref: admininstr; AI_REF_IS_NULL] ->
	Admin_instrs_ok v_S v_C [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) 0)] v_ft.
Proof.
	move => v_S v_C v_ref v_ft HType HReduce Hnotnull.
	destruct v_ref.
	{
		contradict Hnotnull.
		econstructor.
		eauto.
	}
	{
		typing_inversion HType.
		typing_inversion H1.
		unfold_principal_typing Hai.
		destruct Hai as [v_ft [Hai Heok]].
		inversion Hai; subst; clear Hai.
		typing_inversion H2.
		unfold_principal_typing Hai.
		destruct Hai as [rt Ht].
		inversion Ht; subst; clear Ht.
		eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub0
		as [Hsub0 Hsub1].
		2: auto.
		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		eapply AI_ok_instr with (v_instr := instr_CONST _ _).
		constructor.
	}
	{
		typing_inversion HType.
		typing_inversion H1.
		unfold_principal_typing Hai.
		inversion Hai; subst; clear Hai.
		typing_inversion H2.
		unfold_principal_typing Hai.
		destruct Hai as [rt Ht].
		inversion Ht; subst; clear Ht.
		eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub0
		as [Hsub0 Hsub1].
		2: auto.
		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		eapply AI_ok_instr with (v_instr := instr_CONST _ _).
		constructor.
	}
Qed.

(*



v_s : store
v_f : frame
v_t1 : seq valtype
v_val : seq wasm.val
v_bt : blocktype
v_instr : seq instr
v_k : nat
v_n : n
v_t_1, v_t_2 : seq valtype
H : fun_blocktype (mk_state v_s v_f) v_bt = v_t_1 :-> v_t_2
HST : Store_ok v_s
C : context
ret : option resulttype
lab : seq resulttype
tx, ty : resulttype
HIT1 : Module_instance_ok v_s (F_MODULE v_f) C
HValOK : Forall2 (λ (v_t : valtype) (v_val : wasm.val), Val_ok v_s v_val v_t) v_t1 (F_LOCALS v_f)
HType :
Admin_instrs_ok v_s (upd_label (upd_local_return C (v_t1 ++ C_LOCALS C) ret) lab)
(ListDef.map [eta fun_coec_val__admininstr] v_val ++ [AI_BLOCK v_bt v_instr]) (mk_functype tx ty)

Admin_instrs_ok v_s (upd_label (upd_local_return C (v_t1 ++ C_LOCALS C) ret) lab)
[AI_LABEL_ v_n [] (ListDef.map [eta fun_coec_val__admininstr] v_val ++
ListDef.map [eta fun_coec_instr__admininstr] v_instr)] (mk_functype tx ty)
*)

Lemma bt_inversion : forall v_S v_C v_C' r_v_f (v_bt: blocktype) ts1 ts2 bt1 bt2,
	Module_instance_ok v_S (F_MODULE r_v_f) v_C ->
	Blocktype_ok v_C' v_bt (ts1 :-> ts2) ->
	fun_blocktype (mk_state v_S r_v_f) v_bt = (bt1 :-> bt2) ->
	inst_match v_C v_C' ->
	(ts1 = bt1 /\ ts2 = bt2).
Proof.
	move=> v_S v_C v_C' r_v_f v_bt ts1 ts2 bt1 bt2 HM HB Hf Him.
	inversion HM; subst.
	unfold inst_match in Him.
	simpl in *; subst.
	unfold fun_blocktype in Hf;
	destruct v_bt.
	{
		destruct o;
		inversion Hf; subst;
		inversion HB; subst; auto.
	}
	unfold fun_type.
	inversion Hf; subst;
	inversion HB; subst.
	rewrite -H in H16; simpl in H16.
	destruct_all; subst.
	rewrite H21 in H16.
	by inversion H16.
Qed.

Lemma Step_read__block_preserves : forall v_S (r_v_f : frame) v_C v_bt (v_instr : (list instr)) ts1 ts2 v_t1 lab ret v_val bt_1 bt_2,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) (ListDef.map [eta fun_coec_val__admininstr] v_val ++ [AI_BLOCK v_bt v_instr]) (ts1 :-> ts2) ->
	Store_ok v_S ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_S v_val v_t) v_t1 (F_LOCALS r_v_f) ->
	fun_blocktype (mk_state v_S r_v_f) v_bt = bt_1 :-> bt_2 ->
	(Datatypes.length bt_1 = Datatypes.length v_val) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [AI_LABEL_ (Datatypes.length bt_2) [] (ListDef.map [eta fun_coec_val__admininstr] v_val ++
	ListDef.map [eta fun_coec_instr__admininstr] v_instr)] (ts1 :-> ts2).
Proof.
	move => v_S r_v_f v_C v_bt v_instr ts1 ts2 v_t1 lab ret v_val bt_1 bt_2 HType HStore HMinst HValOK Hbt HLength.
	typing_inversion HType.
	typing_inversion H2;
	simpl in Hai;
	extract_premise.
	vals_typing_inversion H1.
Admitted. (*

	assert (extr :-> extr0 = bt_1 :-> bt_2). {
		eapply bt_inversion; eauto.
		resolve_inst_match.
	}
	inversion H; subst; clear H.


	eapply construct_ais_typing_single with (ts1 := ts1) (ts2 := ts2).
	eapply AI_ok_label.
	eapply instrs_empty_typing.
	by eapply resulttype_sub_refl.
	2: by reflexivity.

	all: 
	inversion H0; subst;
	inversion Hbt; subst.
	eapply construct_ais_compose with (t2s := bt_1).
	{
		destruct v_valtype;
		inversion H1; subst; clear H1;
		symmetry in HLength;
		rewrite length_zero_iff_nil in HLength; subst;
		eapply AIs_ok_empty.
	}
	{
		destruct v_valtype;
		inversion H1; subst; clear H1;
		symmetry in HLength;
		rewrite length_zero_iff_nil in HLength; subst;
		eapply AIs_ok_instrs;
		auto.
	}
		}
	}

		    Opaque instrtype_sub.
			simpl in Hsub.
			rewrite -(cats0 v_ts) in Hsub0.
			eapply (instrtype_sub_compose_ge _ _ _ _ _ _ _ _ Hsub0) in Hsub
			  as [Hsub _].

	vals_typing_inversion H1.


Admitted.
*)
(*
Lemma Step_read__loop_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_LOOP v_t v_instr)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_LABEL_ 0 [(LOOP v_t v_instr)] (map fun_coec_instr__admininstr v_instr))] v_ft.
Proof.
	move => v_S r_v_f v_C v_z v_t v_instr v_ft v_t1 lab ret HType HMinst H HValOK.
	destruct v_ft as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Loop_typing in HType; destruct HType as [ts [? [? ?]]]; subst.
	simpl in H2.
	rewrite <- admin_instrs_ok_eq.
	apply admin_instr_weakening_empty_1.
	apply AI_ok_label with (v_t_1 := None).
	repeat split => //=.
	- simpl.
		rewrite app_left_single_nil.
		apply (instrs_seq _ [] (LOOP v_t v_instr) [] v_t []).
		- apply instrs_empty.
		- apply loop.
(* TODO *)
Admitted.
(*
		apply H2. 
	- apply AIs_ok_instrs with (v_S := v_S) in H2.
		apply H2. auto.
Qed. *)

Lemma Step_read__call_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CALL v_x)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(v_x < (List.length (fun_funcaddr v_z))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CALL_ADDR (lookup_total (fun_funcaddr v_z) v_x))] v_ft.
Proof.
	move => v_S r_v_f v_C v_z v_x v_ft v_t1 lab ret HType HMinst H H1 HValOK.
	destruct v_ft as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Call_typing in HType; destruct HType as [ts [t1s' [t2s' [? [? [? ?]]]]]]; subst.
	simpl in *.
	apply AIs_ok_frame.
	rewrite <- admin_instrs_ok_eq.
	eapply AI_ok_call_addr.
	inversion HMinst.
	simpl in *.
	rewrite <- H in H1. simpl in H1.
	apply Forall2_lookup in H5. destruct H5.
	move/ltP: H1 => H1.
	apply H15 in H1. rewrite <- H2. rewrite <- H14.
	apply H1.
Qed.

Lemma tc_func_reference2: forall v_S v_C v_minst idx tf v_type,
  lookup_total (MODULE_TYPES v_minst) idx = FUNC_TYPE v_type ->
  Module_instance_ok v_S v_minst v_C ->
  lookup_total (C_TYPES v_C) idx = tf ->
  tf = FUNC_TYPE v_type.
Proof.
	move => v_S v_C v_minst idx tf v_type H HMinst H1.
	inversion HMinst. subst. simpl in *. auto.
Qed.


Lemma store_typed_exterval_types: forall v_S v_f v_a,
	(v_a < List.length (FUNCS v_S))%coq_nat ->
	lookup_total (FUNCS v_S) v_a = v_f ->
    Store_ok v_S ->
    Externaddrs_ok v_S (EXTADDR_FUNC v_a) (EXT_FUNC (FUNC_TYPE v_f)).
Proof.
	move => v_S v_f v_a HLength H HST.
	inversion HST; subst; simpl in *.
	
	apply Forall2_lookup in H2; destruct H2.
	apply H0 in HLength as HFunc.
	simpl in *.
	inversion HFunc; subst; simpl in *.
	apply extaddr_ok_func with (v_minst := v_moduleinst) (v_func := v_func).
	- move/ltP: HLength => Hprop. auto.
	- simpl in *. auto.
Qed.

Lemma Step_read__call_indirect_call_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : uN 32) (v_x : idx) (v_a : addr) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 v_i);(AI_CALL_INDIRECT v_x)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	Store_ok v_S ->
	v_z = mk_state v_S r_v_f ->
	(fun_u32__nat v_i < (List.length (REFS (fun_table v_z 0)))) ->
	(v_a < (List.length (fun_funcinst v_z))) ->
	((lookup_total (REFS (fun_table v_z 0)) (fun_u32__nat v_i)) = (Some v_a)) ->
	((fun_type v_z v_x) = (FUNC_TYPE (lookup_total (fun_funcinst v_z) v_a))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CALL_ADDR v_a)] v_ft.
Proof.
	move => v_S r_v_f v_C v_z v_i v_x v_a v_ft v_t1 lab ret HType HMinst HST H1 H2 H3 H4 H5 HValOK.
	destruct v_ft as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply AI_const_typing in H4_comp0.
	rewrite <- admin_instrs_ok_eq in H4_comp.
	apply Call_indirect_typing in H4_comp; destruct H4_comp as [tn [tm [ts [? [? [? ?]]]]]]; subst.
	repeat rewrite -> app_assoc in H1. apply split_append_last in H1; destruct H1.
	rewrite H1.
	repeat rewrite -> app_assoc.
	apply AIs_ok_frame.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_call_addr.
	unfold fun_table in H4.
	unfold fun_type in H5.
	unfold fun_table in H2.
	simpl in *.
	assert ((mk_functype tn tm) = FUNC_TYPE (lookup_total (FUNCS v_S) v_a)) as HFType; first by eapply tc_func_reference2; eauto.
	rewrite -> HFType.
	move/ltP: H3 => H3.
	eapply store_typed_exterval_types; eauto.
Qed.

Lemma Step_read__call_indirect_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : val_ I32) (v_x : idx) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 v_i);(AI_CALL_INDIRECT v_x)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(~(Step_read_before_call_indirect_trap (mk_config v_z [(AI_CONST I32 v_i);(AI_CALL_INDIRECT v_x)]))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_TRAP )] v_ft.
Proof.
	intros.
	destruct v_ft.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_read__call_addr_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_val : (list wasm.val)) (v_k : nat) (v_a : addr) (v_n : n) (v_f : frame) (v_instr : (list instr)) (v_t_1 v_t_2 : (list wasm.valtype)) (v_mm : moduleinst) (v_func : func) (v_x : idx) (v_t : (list wasm.valtype)) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)(@app _ (map fun_coec_val__admininstr v_val) [(AI_CALL_ADDR v_a)]) v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	Store_ok v_S -> 
	v_z = mk_state v_S r_v_f ->
	(v_a < (List.length (fun_funcinst v_z))) ->
	((lookup_total (fun_funcinst v_z) v_a) = {| FUNC_TYPE := (mk_functype v_t_1 v_t_2); FUNC_MODULE := v_mm; CODE := v_func |}) ->
	(v_func = (FUNC v_x (List.map (fun v_t => (LOCAL v_t)) (v_t)) v_instr)) ->
	(v_f = {| LOCALS := (@app _ v_val (List.map (fun v_t => (fun_default_ v_t)) (v_t))); F_MODULE := v_mm |}) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_FRAME_ v_n v_f [(AI_LABEL_ v_n [] (map fun_coec_instr__admininstr v_instr))])] v_ft.
Admitted.
(* Proof.
	move => v_S r_v_f v_C v_z v_val v_k v_a v_n v_f v_instr v_t_1 v_t_2 v_mm v_func v_x v_t v_ft v_t1 lab ret HType HMinst H1 H2 H3 H4 H5 H6 H7 H8 H9.
	destruct v_ft as [ts1 ts2].
	apply_composition_typing_single HType.
	apply Val_Const_list_typing in H3_comp.
	rewrite -> H3 in H4. simpl in H4.
	rewrite -> H3 in H5. simpl in H5.
	eapply CALL_ADDR_invoke_typing with (v_t_1 := v_t_1) (v_t_2 := v_t_2) (v_mm := v_mm) in H4_comp; eauto;
	try apply H5. 
	destruct H4_comp as [ts' [C' [? [? [??]]]]].
	subst.
	apply concat_cancel_last_n in H; last by (repeat rewrite length_is_size in H2; rewrite List.map_length).
	destruct H; subst.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_frame. auto. split => //=.
	eapply Thread_ok__. split. 
	apply Frame_ok__ with (v_t := ((List.map typeof v_val) ++ v_t)). repeat split => //=.
	repeat rewrite -> List.app_length.
	repeat rewrite -> List.map_length => //=.
	apply H10.
	apply Forall2_Val_ok_is_same_as_map.
	rewrite List.map_app.
	rewrite List.app_inv_head_iff.
	apply typeof_default_inverse.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_label with (v_t_1 := v_t_2); repeat split => //=.
	- apply instrs_weakening_empty_both. apply instrs_empty.
	- rewrite fold_append. simpl.
		repeat rewrite _append_option_none_left.
		apply AIs_ok_instrs.
		apply H11. 
Qed. *)

Lemma Step_read__local_get_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_LOCAL_GET v_x)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [((fun_local v_z v_x) : admininstr)] v_ft.
Proof.
	move => v_S r_v_f v_C v_z v_x v_ft v_t1 lab ret HType HMinst H1 HValOK.
	destruct v_ft as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in HType.
	apply Get_local_typing in HType; destruct HType as [t [? [? ?]]]. 
	simpl in *.
	subst.
	apply admin_instr_weakening_empty_1.
	unfold fun_local.
	apply inst_t_context_local_empty in HMinst.
	rewrite HMinst in H2.
	rewrite HMinst.
	apply Forall2_lookup in HValOK; destruct HValOK.
	rewrite <- app_right_nil in H2.
	rewrite <- app_right_nil.
	apply H0 in H2. 
	inversion H2.
	subst.
	unfold fun_localidx__nat in H3 at 2.
	unfold fun_proj_uN_0.
	rewrite <- H3.
	apply (AI_ok_instr v_S (upd_label (upd_local_return v_C v_t1 ret) lab)
	(CONST (@lookup_total valtype Inhabited__valtype v_t1 (fun_localidx__nat v_x)) v_c_t)
	(mk_functype [] [(lookup_total v_t1 v_x)])).
	apply const.
Qed.

Lemma global_type_reference: forall v_S v_i v_x v_C mut v t,
    Module_instance_ok v_S v_i v_C ->
	(v_x < Datatypes.length (C_GLOBALS v_C))%coq_nat -> 
    (VALUE (lookup_total (GLOBALS v_S) (lookup_total (MODULE_GLOBALS v_i) v_x))) = v ->
    lookup_total (C_GLOBALS v_C) v_x = mk_globaltype mut t ->
    exists v_val_, typeof v = t /\ v = VAL_CONST t v_val_.
Admitted.
(* Proof.
	move => v_S i v_x v_C mut v t HMinst HLength HVal HTypeLookup.
	inversion HMinst; decomp; subst.
	simpl in *.
	apply Forall2_lookup2 in H9; destruct H9.
	apply H1 in HLength.
	inversion HLength; destruct H13.
	rewrite H14.
	simpl.
	rewrite HTypeLookup in H12. injection H12 as ?; eauto.
	exists v_val_.
	split => //=.
	f_equal => //=.
Qed. *)

Lemma Step_read__global_get_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_GLOBAL_GET v_x)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [((VALUE (fun_global v_z v_x)) : admininstr)] v_ft.
Proof.
	move => v_S r_v_f v_C v_z v_x v_ft v_t1 lab ret HType HMinst H HValOK.
	destruct v_ft as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	rewrite <- admin_instrs_ok_eq.
	apply Get_global_typing in HType.
	destruct HType as [mut [t [? [? ?]]]].
	simpl in *.
	subst.
	unfold fun_global.

	remember ((VALUE
	(lookup_total (GLOBALS v_S)
	   (lookup_total (MODULE_GLOBALS (F_MODULE r_v_f)) (fun_proj_uN_0 32 v_x))))) as v.
	eapply global_type_reference in HMinst; eauto; destruct HMinst as [v_val_ [? ?]].
	rewrite H1 in Heqv.
	apply admin_instr_weakening_empty_1.
	rewrite Heqv.
	eapply (AI_ok_instr v_S _ (CONST t v_val_) (mk_functype [] [t])).
	apply const.
Qed.

Lemma Step_read__load_num_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : uN 32) (v_t : valtype) (v_mo : memarg) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 v_i);(AI_LOAD v_t None v_mo)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((List.length (BYTES (fun_mem v_z 0))) < ((v_i + (OFFSET v_mo)) + ((fun_size v_t) / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_TRAP )] v_ft.
Proof.
	intros.
	destruct v_ft.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_read__load_num_val_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : uN 32) (v_t : valtype) (v_mo : memarg) v_c v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 v_i);(AI_LOAD v_t None v_mo)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((fun_bytes_ v_t v_c) = (list_slice (BYTES (fun_mem v_z 0)) (fun_u32__nat v_i + (OFFSET v_mo)) ((fun_size v_t) / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CONST v_t v_c)] v_ft.
Proof.
	move => v_S r_v_f v_C v_z v_i v_t v_mo v_c v_ft v_t1 lab ret HType HMinst HState H HValOK.
	destruct v_ft as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply AI_const_typing in H4_comp0.
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in H4_comp.
Admitted. (*
	apply Load_typing in H4_comp; destruct H4_comp as [ts [v_n [v_sx [v_inn [v_mt [? [? [? [? [? [? [? [??]]]]]]]]]]]]].
	subst.
	repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
	subst.
	repeat rewrite -> app_assoc.
	apply admin_instr_weakening_empty_1.
	eapply (AI_ok_instr v_S _ (CONST v_t v_c) (mk_functype [] [v_t])).
	apply const.
Qed. *)

Lemma Step_read__load_pack_trap_I32_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : uN 32) (v_n : n) (v_sx : sx) (v_mo : memarg) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 v_i);(AI_LOAD INN_I32 (Some (op__ INN_I32 (mk_sz v_n) v_sx)) v_mo)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((List.length (BYTES (fun_mem v_z 0))) < ((fun_u32__nat v_i + (OFFSET v_mo)) + (v_n / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_TRAP )] v_ft.
Admitted.

Lemma Step_read__load_pack_trap_I64_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : uN 32) (v_n : n) (v_sx : sx) (v_mo : memarg) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 v_i);(AI_LOAD INN_I64 (Some (op__ INN_I64 (mk_sz v_n) v_sx)) v_mo)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((List.length (BYTES (fun_mem v_z 0))) < ((fun_u32__nat v_i + (OFFSET v_mo)) + (v_n / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_TRAP )] v_ft.
Admitted.

(*
Proof.
	intros.
	destruct v_ft.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed. *)

Lemma Step_read__load_pack_val_I32_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : uN 32) (v_n : n) (v_sx : sx) (v_mo : memarg) (v_c : iN v_n) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST INN_I32 v_i);(AI_LOAD INN_I32 (Some (op__ INN_I32 (mk_sz v_n) v_sx)) v_mo)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((fun_ibytes_ v_n v_c) = (list_slice (BYTES (fun_mem v_z 0)) (fun_u32__nat v_i + (OFFSET v_mo)) (v_n / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CONST INN_I32 (fun_extend__ v_n (fun_size INN_I32) v_sx v_c))] v_ft.
Admitted.

Lemma Step_read__load_pack_val_I64_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : uN 32) (v_n : n) (v_sx : sx) (v_mo : memarg) (v_c : iN v_n) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST INN_I32 v_i);(AI_LOAD INN_I64 (Some (op__ INN_I64 (mk_sz v_n) v_sx)) v_mo)] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((fun_ibytes_ v_n v_c) = (list_slice (BYTES (fun_mem v_z 0)) (fun_u32__nat v_i + (OFFSET v_mo)) (v_n / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CONST INN_I64 (fun_extend__ v_n (fun_size INN_I64) v_sx v_c))] v_ft.
Admitted.
(*
Proof.
	move => v_S r_v_f v_C v_z v_i v_inn v_n v_sx v_mo v_c v_ft v_t1 lab ret HType HMinst HState H HValOK.
	destruct v_ft as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply AI_const_typing in H4_comp0.
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in H4_comp.
	apply Load_typing in H4_comp; destruct H4_comp as [ts [v_n' [v_sx' [v_inn' [v_mt [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
	subst.
	repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
	subst.
	repeat rewrite -> app_assoc.
	apply admin_instr_weakening_empty_1.
	eapply (AI_ok_instr v_S _ (CONST (valtype__INN v_inn) ((fun_ext v_n (fun_size (valtype__INN v_inn)) v_sx v_c))) (mk_functype [] [(valtype__INN v_inn)])).
	apply const.
Qed. *)

Lemma Step_read__memory_size_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_n : n) v_ft v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_MEMORY_SIZE )] v_ft ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(((v_n * 64) * (fun_Ki )) = (List.length (BYTES (fun_mem v_z 0)))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CONST I32 (fun_nat__u32 v_n : val_ I32))] v_ft.
Proof.
	move => v_S r_v_f v_C v_z v_n v_ft v_t1 lab ret HType HMinst HState HLength HValOK.
	destruct v_ft as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in HType.
	apply Memory_size_typing in HType; destruct HType as [v_mt [? [? ?]]].
	subst.
	apply admin_instr_weakening_empty_1.
	eapply (AI_ok_instr v_S _ (CONST (I32) (fun_nat__u32 v_n)) (mk_functype [] [(I32)])).
	apply const.
Qed. *)

Lemma func_extension_same: forall f,
	Forall2 (fun v s => Func_extension v s) f f.
Proof.
	move => f.
	induction f => //.
	apply Forall2_cons_iff. split.
	- apply mk_Func_extension.
	- apply IHf.
Qed.

Lemma table_extension_same: forall t,
	Forall2 (fun v s => Table_extension v s) t t.
Proof.
	move => t.
	induction t => //.
	apply Forall2_cons_iff. split.
	- destruct a as [type refs]. destruct type.
	  destruct v_limits.
	  destruct v__.
	  by constructor.
	- apply IHt.
Qed.

Lemma mem_extension_same: forall m,
	Forall2 (fun v s => Mem_extension v s) m m.
Proof.
	move => m.
	induction m => //.
	apply Forall2_cons_iff. split.
	- destruct a as [type bytes]. destruct type.
	  destruct v_limits.
	  destruct v__.
	  by constructor.
	- apply IHm.
Qed.

Lemma global_extension_same: forall s g v_globaltype,
	Forall2
	(fun (v_globalinst : globalinst) (v_globaltype : globaltype) => Global_instance_ok s v_globalinst v_globaltype) g v_globaltype ->
	Forall2 (fun v s => Global_extension v s) g g.
Proof.
	move => s g v_globaltype HGlobalInstOk.
	generalize dependent v_globaltype.
	induction g => //; move => v_globaltype HGlobalInstOk.
	apply Forall2_cons_iff. split.
	-
		apply Forall2_length in HGlobalInstOk as ?. 
		destruct v_globaltype => //=.
		inversion HGlobalInstOk.
		inversion H3; decomp; subst.
		constructor. by right.
	- destruct v_globaltype; inversion HGlobalInstOk. eapply IHg; eauto. 
Qed.

Lemma store_extension_same: forall s,
	Store_ok s ->
    Store_extension s s.
Proof.
  move => s HST. 
  inversion HST; decomp.
Admitted.
(*
  apply (mk_Store_extension s s (FUNCS s) (TABLES s) (MEMS s) (GLOBALS s) (FUNCS s) [] (TABLES s) [] (MEMS s) [] (GLOBALS s) []).
  repeat (split => //; try rewrite -> app_nil_r).
  + by apply func_extension_same.
  + by apply table_extension_same.
  + by apply mem_extension_same.
  + subst. eapply global_extension_same; eauto.
Qed. *)

Lemma config_same: forall s f ais s' f' ais',
	(mk_config (mk_state s f) ais) = (mk_config (mk_state s' f') ais') ->
	s = s' /\ f = f' /\ ais = ais'.
Proof.
	move => s f ais s' f' ais' H.
	injection H as H1 => //=.
Qed.

Lemma config_same2: forall s f ais s' f' ais',
	s = s' /\ f = f' /\ ais = ais' ->
 	(mk_config (mk_state s f) ais) = (mk_config (mk_state s' f') ais').
Proof.
	move => s f ais s' f' ais' [? [? ?]].
	f_equal => //=. f_equal => //=.
Qed.

(*
Lemma Forall2_global: forall v_S v_globaltype v_idx v_valtype v_val_0 v_val_,
	Forall2
	(fun (v_globalinst : globalinst) (v_globaltype : globaltype) => Global_instance_ok v_S v_globalinst v_globaltype) (GLOBALS v_S) v_globaltype -> 
	(v_idx < length (GLOBALS v_S))%coq_nat ->
	lookup_total (GLOBALS v_S) v_idx = 
	{| GLOB_TYPE := mk_globaltype (Some MUT) v_valtype; VALUE := VAL_CONST v_valtype v_val_0 |} ->
	Forall2 (fun v s => Global_extension v s) (GLOBALS v_S) (list_update_func (GLOBALS v_S) v_idx 
		(fun g => g <| VALUE := (VAL_CONST v_valtype v_val_) |> )).
Admitted.
(* Proof.
	move => v_S v_globaltype v_idx v_val0 v_valtype v_val_.
	destruct v_S as [funcs globals tables mems]; simpl.
	move: v_idx v_globaltype.
	induction globals; move => v_idx v_globaltype HGlobalInstOk H H2 => //=.
	destruct v_idx => //=.
	
	apply Forall2_cons_iff. unfold lookup_total in H2; simpl in H2; subst. split.
	- unfold set. simpl. apply Global_extension__. left => //.
		destruct v_globaltype; inversion HGlobalInstOk.
		eapply global_extension_same; eauto. 
	- apply Forall2_cons. 
		-
			apply Forall2_length in HGlobalInstOk as ?. 
			destruct v_globaltype => //=.
			inversion HGlobalInstOk.
			inversion H5; decomp; subst.
			inversion H13; subst.
			apply Global_extension__. right => //.
		- unfold lookup_total in H2. simpl in H2. 
			destruct v_globaltype; inversion HGlobalInstOk.
			eapply IHglobals => //=.
			- 
				apply Forall2_length in H6.
				apply Forall2_forall2; split => //=.
				apply H6.
				move => x0 y0 Hin.
				inversion HGlobalInstOk; subst.
				apply Forall2_forall2 in H12; destruct H12.
				apply H1 in Hin.
				inversion Hin; decomp; subst.
				inversion H11.
				eapply Global_instance_ok__; repeat split => //=.
			- simpl in H. apply Nat.succ_lt_mono in H. apply H.
Qed. *)

Lemma update_global_unchagned: forall v_S v_S' v_f v_x v_valtype v_val_,
	v_S' =
	v_S <| GLOBALS :=
	list_update_func (GLOBALS v_S)
	(lookup_total (MODULE_GLOBALS (F_MODULE v_f)) v_x)
	[eta set VALUE (fun=> VAL_CONST v_valtype v_val_)] |> ->
	FUNCS v_S = FUNCS v_S' /\
	TABLES v_S = TABLES v_S' /\
	length (GLOBALS v_S) = length (GLOBALS v_S') /\
	MEMS v_S = MEMS v_S'.
Proof. 
	move => v_S v_S' v_f v_x v_valtype v_val' H.
	destruct v_S'. unfold set in H. simpl in *.
	injection H as ?; subst; repeat split => //=.
	by erewrite <- list_update_length_func.
Qed.

Lemma update_mem_unchagned_func: forall v_S v_S' func v_idx,
	v_S' = v_S <| MEMS := list_update_func (MEMS v_S) v_idx func |> ->
	FUNCS v_S = FUNCS v_S' /\
	TABLES v_S = TABLES v_S' /\
	length (MEMS v_S) = length (MEMS v_S') /\
	GLOBALS v_S = GLOBALS v_S'.
Proof.
	move => v_S v_S' func v_idx H.
	destruct v_S'. unfold set in H. simpl in *.
	injection H as ?; subst; repeat split => //=.
	by erewrite <- list_update_length_func.
Qed.

Lemma update_mem_unchagned: forall v_S v_S' func v_idx,
	v_S' = v_S <| MEMS := list_update (MEMS v_S) v_idx func |> ->
	FUNCS v_S = FUNCS v_S' /\
	TABLES v_S = TABLES v_S' /\
	length (MEMS v_S) = length (MEMS v_S') /\
	GLOBALS v_S = GLOBALS v_S'.
Proof.
	move => v_S v_S' func v_idx H.
	destruct v_S'. unfold set in H. simpl in *.
	injection H as ?; subst; repeat split => //=.
	by erewrite <- list_update_length.
Qed. *)

Lemma func_agree_extension: forall v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_ft,
	Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_ft) ->
	length (FUNCS v_S) = length v_funcinst_1' ->
	FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2)%list -> 
    Forall2 (fun v s => Func_extension v s) (FUNCS v_S) v_funcinst_1' ->
    Externaddrs_ok v_S' (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_ft).
Admitted.
(* Proof.
	move => v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_ft HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst.
	apply Forall2_nth in Hext; destruct Hext.
	apply (H0 _ default_val default_val) in H2 as H2'.
	unfold lookup_total in H3.
	apply (Externaddrs_ok__func _ _ _ v_minst v_code_func).
	apply (length_app_lt) with (l':=(FUNCS v_S')) (l2':= v_funcinst_2) in HLength => //=.
	split. 
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	- unfold lookup_total.
		rewrite H in H2.
		apply app_nth1 with (l' := v_funcinst_2) (d := default_val) in H2.
		rewrite <- HApp in H2.
		destruct default_val.
		inversion H2'.
		rewrite H2. 
		rewrite <- H5.
		apply H3.
Qed. *)

Lemma table_agree_extension: forall v_S v_S' v_tableaddr v_tableinst_1' v_tableinst_2 v_tabletype,
    Externaddrs_ok v_S (EXTADDR_TABLE v_tableaddr) (EXT_TABLE v_tabletype) ->
	length (TABLES v_S) = length v_tableinst_1' ->
	TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2) -> 
	Forall2 (fun v s => Table_extension v s) (TABLES v_S) v_tableinst_1' ->
    Externaddrs_ok v_S' (EXTADDR_TABLE v_tableaddr) (EXT_TABLE v_tabletype).
Admitted.
(* Proof.
	move => v_S v_S' v_tableaddr v_tableinst_1' v_tableinst_2 v_tabletype HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst; destruct H3.
	apply Forall2_lookup in Hext; destruct Hext.
	apply H3 in H2 as H2'.
	inversion H2'. 
	eapply Externaddrs_ok__table.
	apply (length_app_lt) with (l':=(TABLES v_S')) (l2':= v_tableinst_2) in HLength => //=.
	split.
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	-  
		rewrite H1 in H2.
		apply lookup_app with (l' := v_tableinst_2) in H2.
		rewrite <- HApp in H2.
		rewrite <- H2.
		rewrite <- H5. split => //=.
		rewrite <- H4 in H.
		injection H as ?.
		inversion H0. inversion H8. destruct H11.
		subst.
		injection H12 as ?.
		apply Tabletype_sub__.
		apply Limits_sub__.
		subst.
		unfold ge in H11. split.
		unfold ge.
		eapply Nat.le_trans; eauto.
		apply H14.
Qed. *)

Lemma global_agree_extension: forall v_S v_S' v_globaladdr v_globalinst_1' v_globalinst_2 v_globaltype,
    Externaddrs_ok v_S (EXTADDR_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype) ->
	length (GLOBALS v_S) = length v_globalinst_1' ->
	GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2) -> 
	Forall2 (fun v s => Global_extension v s) (GLOBALS v_S) v_globalinst_1' ->
    Externaddrs_ok v_S' (EXTADDR_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype).
Admitted.
(* Proof.
	move => v_S v_S' v_globaladdr v_globalinst_1' v_globalinst_2 v_globaltype HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst.
	apply Forall2_lookup in Hext; destruct Hext.
	apply H0 in H2 as H2'.
	inversion H2'.
	eapply Externaddrs_ok__global with (v_val_ := v_c2).
	apply (length_app_lt) with (l':=(GLOBALS v_S')) (l2':= v_globalinst_2) in HLength => //=.
	split.
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	- 
		rewrite H in H2.
		apply lookup_app with (l' := v_globalinst_2) in H2.
		rewrite <- HApp in H2.
		rewrite <- H2.
		rewrite <- H1 in H3.
		injection H3 as ?.
		subst => //=.
Qed. *)

Lemma mem_agree_extension: forall v_S v_S' v_memaddr v_meminst_1' v_meminst_2 v_memtype,
    Externaddrs_ok v_S (EXTADDR_MEM v_memaddr) (EXT_MEM v_memtype) ->
	length (MEMS v_S) = length v_meminst_1' ->
	MEMS v_S' = (v_meminst_1' ++ v_meminst_2) -> 
	Forall2 (fun v s => Mem_extension v s) (MEMS v_S) v_meminst_1' ->
    Externaddrs_ok v_S' (EXTADDR_MEM v_memaddr) (EXT_MEM v_memtype).
Admitted.
(* Proof.
	move => v_S v_S' v_memaddr v_meminst_1' v_meminst_2 v_memtype HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst; destruct H3 as [? ?].
	apply Forall2_lookup in Hext; destruct Hext.
	apply H3 in H2 as H2'.
	inversion H2'. 
	eapply Externaddrs_ok__mem.
	apply (length_app_lt) with (l':=(MEMS v_S')) (l2':= v_meminst_2) in HLength => //=.
	split.
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	-  
		rewrite H1 in H2.
		apply lookup_app with (l' := v_meminst_2) in H2.
		rewrite <- HApp in H2.
		rewrite <- H2.
		rewrite <- H5. repeat split => //=. 
		rewrite <- H4 in H.
		injection H as ?.
		inversion H0. inversion H8. destruct H11.
		subst.
		injection H12 as ?.
		apply Limits_sub__.
		subst.
		unfold ge in H11. split.
		unfold ge.
		eapply Nat.le_trans; eauto.
		apply H14.
Qed. *)

Lemma func_extension_C: forall v_S v_S' v_funcaddrs v_funcinst_1' v_funcinst_2 tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_FUNC v) (EXT_FUNC s)) v_funcaddrs tcf ->
	length (FUNCS v_S) = length v_funcinst_1' ->
	FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2)%list -> 
	Forall2 (fun v s => Func_extension v s) (FUNCS v_S) v_funcinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_FUNC v) (EXT_FUNC s)) v_funcaddrs tcf.
Proof.
	move => v_S v_S' v_funcaddrs v_funcinst_1' v_funcinst_2.
	move: v_S v_S'.
	induction v_funcaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (func_agree_extension v_S) with (v_funcinst_1' := v_funcinst_1') (v_funcinst_2 := v_funcinst_2) => //.
	- eapply IHv_funcaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma table_extension_C: forall v_S v_S' v_tableaddrs v_tableinst_1' v_tableinst_2 tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_TABLE v) (EXT_TABLE s)) v_tableaddrs tcf ->
	length (TABLES v_S) = length v_tableinst_1' ->
	TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2)%list -> 
	Forall2 (fun v s => Table_extension v s) (TABLES v_S) v_tableinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_TABLE v) (EXT_TABLE s)) v_tableaddrs tcf.
Proof.
	move => v_S v_S' v_tableaddrs v_tableinst_1' v_tableinst_2.
	move: v_S v_S'.
	induction v_tableaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (table_agree_extension v_S) with (v_tableinst_1' := v_tableinst_1') (v_tableinst_2 := v_tableinst_2) => //.
	- eapply IHv_tableaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma global_extension_C: forall v_S v_S' v_globaladdrs v_globalinst_1' v_globalinst_2 tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_GLOBAL v) (EXT_GLOBAL s)) v_globaladdrs tcf ->
	length (GLOBALS v_S) = length v_globalinst_1' ->
	GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2)%list -> 
	Forall2 (fun v s => Global_extension v s) (GLOBALS v_S) v_globalinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_GLOBAL v) (EXT_GLOBAL s)) v_globaladdrs tcf.
Proof.
	move => v_S v_S' v_globaladdrs v_globalinst_1' v_globalinst_2.
	move: v_S v_S'.
	induction v_globaladdrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (global_agree_extension v_S) with (v_globalinst_1' := v_globalinst_1') (v_globalinst_2 := v_globalinst_2) => //.
	- eapply IHv_globaladdrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed.


Lemma mem_extension_C: forall v_S v_S' v_memaddrs v_meminst_1' v_meminst_2 tcf,
	Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_MEM v) (EXT_MEM s)) v_memaddrs tcf ->
	length (MEMS v_S) = length v_meminst_1' ->
	MEMS v_S' = (v_meminst_1' ++ v_meminst_2)%list -> 
	Forall2 (fun v s => Mem_extension v s) (MEMS v_S) v_meminst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_MEM v) (EXT_MEM s)) v_memaddrs tcf.
Proof.
	move => v_S v_S' v_memaddrs v_meminst_1' v_meminst_2.
	move: v_S v_S'.
	induction v_memaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (mem_agree_extension v_S) with (v_meminst_1' := v_meminst_1') (v_meminst_2 := v_meminst_2) => //.
	- eapply IHv_memaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed.

Lemma ext_extension_C: forall v_S v_S' v_exportinst,
	Store_extension v_S v_S' ->
	Forall (Export_instance_ok v_S) v_exportinst -> 
	Forall (Export_instance_ok v_S') v_exportinst.
Proof.
	move => v_S v_S' v_exportinst.
	move: v_S v_S'.
	induction v_exportinst;
	move => v_S v_S' Hext HOk => //=.
	subst. inversion HOk. 
	apply Forall_cons_iff. split.
	-	inversion H1.
		subst.
		eapply mk_Export_instance_ok with (v_ext := v_ext).
		inversion Hext; decomp. 
		inversion H3; subst; destruct H20.
		- inversion H6.
		- inversion H7.
		- inversion H8.
		- inversion H9.
	- eapply IHv_exportinst; eauto.
Qed.

Lemma module_inst_typing_extension: forall v_S v_S' v_i v_C,
    Store_extension v_S v_S' ->
    Module_instance_ok v_S v_i v_C ->
    Module_instance_ok v_S' v_i v_C.
Proof.
	move => v_S v_S' v_i v_C HStoreExtension HMIT.
	inversion HStoreExtension.
	inversion HMIT; decomp.
	subst.
	apply mk_Module_instance_ok; repeat split => //=; auto.
Admitted. (*
	- eapply func_extension_C; eauto.
	- eapply table_extension_C; eauto.
	- eapply global_extension_C ; eauto.
	- eapply mem_extension_C; eauto.
	- eapply ext_extension_C; eauto.
Qed. *)
(*
Lemma global_instance_fine: forall s s' v_globaltype v_f v_x v_valtype v_val_,
    Forall2 (fun v vt => Global_instance_ok s v vt) (GLOBALS s) v_globaltype ->
	Forall2 (fun g g' => Global_extension g g') (GLOBALS s) (GLOBALS s') ->
	(FUNCS s = FUNCS s') ->
	(TABLES s = TABLES s') ->
	(MEMS s = MEMS s') ->
	(GLOBALS s') = list_update_func (GLOBALS s)
	(lookup_total (MODULE_GLOBALS (F_MODULE v_f)) v_x)
	[eta set VALUE (fun=> VAL_CONST v_valtype v_val_)] -> 
	Forall2 (fun v vt => Global_instance_ok s' v vt) (GLOBALS s) v_globaltype.
Admitted.
(* Proof.
	move => s s' v_globaltype v_f v_x v_valtype v_val_ HGlobalInstOk HGlobExt HFEq HTab HMems HGlob.

	destruct s as [funcs1 globals1 tables1 mems1]. destruct s' as [funcs2 globals2 tables2 mems2].
	simpl in *. subst funcs1. subst tables1. subst mems1.
	generalize dependent v_globaltype.
	induction globals1; move => v_globaltype HGlobalInstOk; apply Forall2_length in HGlobalInstOk as H'.
	- symmetry in H'. 
		apply List.length_zero_iff_nil in H'. 
		subst. 
		apply Forall2_nil.
	- destruct v_globaltype => //=.
		apply Forall2_cons_iff. split.
		- inversion HGlobalInstOk; subst.
			inversion H2. destruct H as [? [? ?]].
			inversion H6; subst.
			eapply Global_instance_ok__; eauto.
		- apply Forall2_forall2; split.
			- simpl in H'. by injection H' as ?.
			- move => x y Hin.
				inversion HGlobalInstOk.
				subst.
				apply Forall2_forall2 in H4; destruct H4.
				apply H0 in Hin.
				inversion Hin; subst. destruct H1 as [? [? ?]].
				inversion H4; subst.
				eapply Global_instance_ok__; eauto.
Qed. *)

Lemma store_global_extension_store_typed: forall s s' v_f v_C v_valtype v_val_ v_x v_mut v_valtype0 v_val_0,
    Store_ok s ->
    Store_extension s s' ->
	Module_instance_ok s (F_MODULE v_f) v_C ->
	Module_instance_ok s' (F_MODULE v_f) v_C ->
	(GLOBALS s') = list_update_func (GLOBALS s)
	(lookup_total (MODULE_GLOBALS (F_MODULE v_f)) v_x)
	[eta set VALUE (fun=> VAL_CONST v_valtype v_val_)] ->
	lookup_total (GLOBALS s) (lookup_total (MODULE_GLOBALS (F_MODULE v_f)) v_x) =
	{|
	GLOB_TYPE := mk_globaltype v_mut v_valtype0;
	VALUE := VAL_CONST v_valtype0 v_val_0
	|} ->
	Datatypes.length (GLOBALS s) = Datatypes.length (GLOBALS s') ->
    (FUNCS s = FUNCS s') ->
    (TABLES s = TABLES s') ->
    (MEMS s = MEMS s') ->
	((lookup_total (MODULE_GLOBALS (F_MODULE v_f)) v_x) < length (GLOBALS s))%coq_nat ->
    Store_ok s'.
Admitted.
(* Proof.
	move => s s' f C v_valtype v_val_ v_x v_mut v_valtype0 v_val_0 HSOK Hext HIT HITS' HUpdate HGlobInst HLGlobal HFeq HTeq HMeq HLength.
	inversion HSOK; decomp.
	inversion Hext; decomp; subst.
	destruct s' as [funcs2 globals2 tables2 mems2].
	apply f_equal with (f := fun t => List.length t) in HMeq as ?.
	apply f_equal with (f := fun t => List.length t) in HTeq as ?.
	apply f_equal with (f := fun t => List.length t) in HFeq as ?.
	removeinst2 H22. 
	removeinst2 H20.
	removeinst2 H19.
	removeinst2 H21. subst.
	simpl in *.
	eapply Store_ok__OK with (v_funcinst := v_funcinst) (v_ft := v_ft)
		(v_tableinst := v_tableinst) (v_tabletype := v_tabletype)
		(v_meminst := v_meminst) (v_memtype := v_memtype)
		(v_globalinst := globals2) (v_globaltype := v_globaltype); subst; repeat split => //=.
	- rewrite HLGlobal in H1 => //=. 
	- f_equal => //=.
	- apply Forall2_forall2; split => //=. move => x y HIn.
		apply Forall2_forall2 in H5; destruct H5. apply H11 in HIn. inversion HIn; destruct H15 as [? [? ?]].
		eapply Function_instance_ok__ with (v_C := v_C); repeat split => //=.
		eapply module_inst_typing_extension; eauto.
	- eapply Forall2_list_update_func; eauto.
		- remember ({|
				FUNCS := funcs2;
				GLOBALS := v_globalinst;
				TABLES := tables2;
				MEMS := mems2
			|}) as s.
			assert (v_globalinst = (GLOBALS s)). {by subst. }
			rewrite H11.
			eapply global_instance_fine; subst; simpl; eauto.
			apply Forall2_lookup in H26; destruct H26.
			apply H15 in HLength as H''.
			rewrite HGlobInst in H''.
			inversion H''.
			subst.
			apply Forall2_lookup in H6; destruct H6.
			apply H16 in HLength as H'''.
			rewrite HGlobInst in H'''.
			inversion H'''.
			destruct H22 as [? [? ?]].
			eapply Global_instance_ok__; repeat split => //=.
			inversion H29. subst.
			eapply lookup_list_update_func in H21; eauto; destruct H21 as [y ?].
			unfold set in H18.
			injection H18 as ?; subst.
			apply Val_ok__.
	- apply Forall2_forall2; split => //=. move => x y HIn.
		apply Forall2_forall2 in H7; destruct H7. apply H11 in HIn. inversion HIn; decomp; subst.
		eapply Table_instance_ok__; repeat split => //=; eauto.
		apply Forall2_forall2; split => //=. move => x y HIn'. apply Forall2_forall2 in H21; destruct H21.
		apply H17 in HIn'. apply Forall2_forall2 in HIn'; destruct HIn'.
		apply Forall2_forall2; split => //=. move => x' y' HIn''.
		apply H20 in HIn''. inversion HIn''; decomp; subst. eapply Externaddrs_ok__func; eauto.
	- apply Forall2_forall2; split => //=. move => x y HIn.
		apply Forall2_forall2 in H8; destruct H8. apply H11 in HIn. inversion HIn; decomp; subst. 
		eapply Memory_instance_ok__; repeat split => //=; eauto.
Qed. *) *)

Lemma fold_prepend_label : forall C lab lab1,
	prepend_label (upd_label C lab) lab1 =
	upd_label C ([lab1] ++ lab).
Proof.
	auto.
Qed.

Lemma t_preservation_vs_type: forall s f ais s' f' ais' C C' v_t1 lab ret t1s t2s,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Store_ok s -> 
	Store_ok s' ->
	Store_extension s s' ->
    Module_instance_ok s (F_MODULE f) C ->
    Module_instance_ok s' (F_MODULE f') C' ->
	v_t1 = (C_LOCALS (upd_label (upd_local_return C (v_t1 ++ (C_LOCALS C)) ret) lab)) -> 
	Forall2 (fun v_t v_val => Val_ok s v_val v_t) v_t1 (F_LOCALS f) ->
    Admin_instrs_ok s (upd_label (upd_local_return C (v_t1 ++ (C_LOCALS C)) ret) lab) ais (t1s :-> t2s) ->
    Forall2 (fun v_t v_val => Val_ok s' v_val v_t) v_t1 (F_LOCALS f').
Proof.
	move => s f ais s' f' ais' C C' v_t1 
		lab ret t1s t2s HReduce HStore HStore' HStoreExt HMInst HMInst' HValTypeEq HValOK HType.
	simpl in HValTypeEq;
	rewrite -HValTypeEq in HType; clear HValTypeEq.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent t2s. generalize dependent t1s.
	generalize dependent lab. generalize dependent ais'. generalize dependent ais.
	induction HReduce; try intros;
	try (destruct v_z; subst);
	try (destruct v_z'; subst);
	try (apply config_same in Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]];
		apply config_same in Heqc2 as [Hafter1  [Hafter2  Hafter3]]);
	subst; auto;
	try apply Forall2_length in HValOK as ?; auto.
Admitted.
(*
	{ (* Label Context *)
		typing_inversion HType.
		Opaque fun_coec_instr__admininstr.
		unfold_principal_typing Hai.
		destruct_all.
		rewrite fold_prepend_label in H2.
		eapply IHHReduce; eauto.
	}
	{ (* Frame Context *)
		typing_inversion HType.
		Opaque fun_coec_instr__admininstr.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H0; subst.
		inversion H4; subst.
		eapply IHHReduce; eauto.


	}
	{ (* Local Set *)
		rewrite -> Forall2_Val_ok_is_same_as_map in HValOK;
		rewrite -> Forall2_Val_ok_is_same_as_map.
		induction v_val.
		apply_composition_typing_and_single HType.
		apply AI_const_typing in  H4_comp0.
		apply_composition_typing_single H4_comp.
		apply Set_local_typing in H4_comp1; destruct H4_comp1 as [t [HLookup [H0' H1']]].
		subst.
		repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
		replace (C_LOCALS C) with ([::]: list wasm.valtype) in *; last by symmetry; eapply inst_t_context_local_empty; eauto.
		rewrite -> cats0 in *.
		simpl in H1'; simpl in H0. rewrite -> List.map_length in H1'. 
		apply list_update_map with (f := typeof) (val := (VAL_CONST v_valtype v_val_)) in H1' as HUpdate.
		rewrite HUpdate.
		rewrite list_update_same_unchanged => //=; try rewrite List.map_length => //=.
		simpl. by rewrite list_update_length.
	}
Qed. *)

Lemma store_extension_reduce: forall s f ais s' f' ais' C C' tf,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Module_instance_ok s (F_MODULE f) C ->
    Admin_instrs_ok s C' ais tf ->
	inst_match C C' ->
    Store_ok s ->
    Store_extension s s' /\ Store_ok s'.
Proof.
	move => s f ais s' f' ais' C C' tf HReduce HIT HType HMatch HStore.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent C. generalize dependent C'.
	generalize dependent tf.
	generalize dependent ais. generalize dependent ais'. 
	generalize dependent f. generalize dependent f'.
	induction HReduce;
	move => f' f ais' Heqc2 ais Heqc1 tf C' HType C HIT HMatch;
	destruct tf as [[tf1] [tf2]].
	all: try (destruct v_z; 
	apply config_same in Heqc1; apply config_same in Heqc2; 
	destruct Heqc1; destruct Heqc2;
	subst; try (split => //; eapply store_extension_same; eauto)).
	- (* Label Context *) 
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H in HType.
		typing_inversion HType.
		Opaque fun_coec_instr__admininstr.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H3; subst; clear H3.
		eapply IHHReduce; eauto.
	- (* Label Frame *)
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H0 in HType.
		typing_inversion HType.
		Opaque fun_coec_instr__admininstr.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H5; subst; clear H5.
		inversion H7; subst; clear H7.
		inversion H0; subst; clear H0.
		eapply IHHReduce; eauto.
		resolve_inst_match.
	- (* Global Set *) 
		destruct_all; subst.
		typing_inversion HType.
		typing_inversion H2.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H0; subst; clear H0.
		remember  (s <| GLOBALS :=
			list_update_func (GLOBALS s)
		  	(lookup_total (MODULE_GLOBALS (F_MODULE f)) (fun_proj_uN_0 32 v_x))
		  	[eta set GLOB_VALUE (fun=> v_val)] |>) as s'.
Admitted.
(*
		split.
		{
			subst.
			econstructor.
		}
		assert (Store_extension s s'). 
		{
			eapply Store_extension__ with (v_globalinst_1 := (GLOBALS s)) (v_globalinst_1' := (GLOBALS s')) (v_globalinst_2 := []); 
			repeat split => //=; subst; simpl => //=; try rewrite <- app_right_nil => //=.
			- by rewrite list_update_length_func.
			- by eapply func_extension_same.
			- by eapply table_extension_same.
			- by eapply mem_extension_same.
			- inversion HIT; decomp; subst; simpl in *. 
				remember ((lookup_total v_globaladdr v_x)) as v.
				apply Forall2_lookup2 in H12; destruct H12.
				apply H5 in H1. inversion H1; destruct H17.
				repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
				subst.
				rewrite H in H16. injection H16 as ?; subst.
				inversion HStore; decomp; subst. 
				eapply Forall2_global; eauto. 
		}
		split => //=.
		eapply module_inst_typing_extension with (v_S' := s') in HIT as HITS'; eauto.
		apply update_global_unchagned in Heqs' as ?.
		destruct H3 as [? [? [??]]].
		inversion HIT; decomp; subst.
		simpl in *.
		inversion HStore; decomp; subst; simpl in *.
		apply Forall2_lookup2 in H17; destruct H17.
		apply H17 in H1.
		inversion H1. destruct H29. simpl in *.
		destruct H30.
		eapply store_global_extension_store_typed; eauto.
		- unfold set. simpl. reflexivity.
		- rewrite <- H7. simpl. apply H30.
		- simpl. by rewrite <- H7.
	- (* Store Num Val *)
		destruct H3; destruct H1; subst.
		apply_composition_typing_and_single HType.
		apply_composition_typing_and_single H4_comp.
		apply AI_const_typing in H4_comp0.
		apply AI_const_typing in H4_comp.
		rewrite <- admin_instrs_ok_eq in H4_comp1.
		apply Store_typing in H4_comp1; destruct H4_comp1 as [v_n [v_mt [v_inn [? [? [? [? [? ?]]]]]]]].
		subst.
		remember ((s <| MEMS :=
		list_update_func (MEMS s)
		  (lookup_total (MODULE_MEMS (F_MODULE f)) 0)
		  (λ v_1 : meminst,
			 v_1 <| BYTES :=
			 list_slice_update (BYTES v_1) (v_i + OFFSET v_mo)%coq_nat
			   (fun_size v_t / 8) (fun_bytes_ v_t v_c) |>) |>)) as s'.
		assert (Store_extension s s').
		{
			eapply Store_extension__ with (v_meminst_1 := (MEMS s)) (v_meminst_1' := (MEMS s')) (v_meminst_2 := []);
			repeat split; subst; simpl; try rewrite <- app_right_nil => //=.
			- by rewrite list_update_length_func.
			- by eapply func_extension_same.
			- by eapply table_extension_same.
			- (* Mem extension *)
				inversion HIT; decomp; subst; simpl in *.
				apply Forall2_lookup2 in H15; destruct H15. apply H7 in H0.
				inversion H0; decomp; subst.
				inversion HStore; decomp; subst; simpl in *.
				eapply Forall2_list_update_func2; eauto.
				- by apply mem_extension_same.
				- unfold set; simpl. destruct v_mt'. apply mk_Mem_extension => //=.
			- inversion HStore; decomp; subst; simpl in *.
				eapply global_extension_same; eauto.
		}
		split => //=.
		eapply update_mem_unchagned_func in Heqs' as ?; decomp.
		subst; simpl in *.
		destruct s. simpl in *.
		inversion HStore; decomp; subst. 
		injection H14 as ?; subst.
		eapply Store_ok__OK; repeat split; simpl; eauto.
		- erewrite list_update_length_func; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H15; destruct H15. apply H14 in HIn. inversion HIn; destruct H15 as [? [? ?]].
			eapply Function_instance_ok__ with (v_C := v_C); repeat split => //=.
			eapply module_inst_typing_extension; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H16; destruct H16. apply H14 in HIn. inversion HIn. destruct H16 as [? [? ?]].
			eapply Global_instance_ok__; repeat split; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H17; destruct H17. apply H14 in HIn. inversion HIn; decomp; subst.
			inversion H25. inversion H19; subst; destruct H27.
			eapply Table_instance_ok__; repeat split; eauto.
			apply Forall2_forall2; split => //=; move => x' y' HIn'. 
			apply Forall2_forall2 in H24; destruct H24.
			apply H24 in HIn'. 
			apply Forall2_forall2 in HIn'; destruct HIn'.
			apply Forall2_forall2; split => //=; move => x'' y'' HIn''.
			apply H27 in HIn''. 
			inversion HIn''; decomp; subst.
			eapply Externaddrs_ok__func; eauto.
		- eapply Forall2_list_update_func; eauto.
			- apply Forall2_forall2; split => //=; move => x y HIn.
				apply Forall2_forall2 in H18. apply H18 in HIn.
				inversion HIn; decomp; subst.
				eapply Memory_instance_ok__; eauto.
			- 	
				inversion H1; decomp; subst. simpl in *.
				removeinstSimpler H27.
				removeinstSimpler H28.
				removeinstSimpler H30.
				rewrite H7 in H21.
				removeinstSimpler H29.
				subst.
				simpl in *.
				apply Forall2_lookup in H33; destruct H33.
				inversion HIT; decomp; subst; simpl in *.
				apply Forall2_lookup2 in H37; destruct H37.
				apply H26 in H0. inversion H0. destruct H41 as [? [? ?]]; simpl in H41.
				simpl in H42. 
				apply H19 in H41 as H'.
				rewrite H42 in H'.
				inversion H'. subst.
				unfold set.
				rewrite H42. simpl.
				apply Forall2_lookup in H18; destruct H18.
				apply H37 in H41.
				inversion H41; decomp; subst.
				rewrite H42 in H39.
				injection H39 as ?.
				rewrite H39.
				rewrite H39 in H48.
				inversion H48. inversion H46; decomp.
				eapply Memory_instance_ok__; repeat split; eauto.
	- (* Store Pack Val *)
		destruct H3; destruct H1; subst.
		apply_composition_typing_and_single HType.
		apply_composition_typing_and_single H4_comp.
		apply AI_const_typing in H4_comp0.
		apply AI_const_typing in H4_comp.
		rewrite <- admin_instrs_ok_eq in H4_comp1.
		apply Store_typing in H4_comp1; destruct H4_comp1 as [v_n' [v_mt' [v_inn' [? [? [? [? [? ?]]]]]]]].
		subst.
		remember (s <| MEMS :=
		list_update_func (MEMS s)
		  (lookup_total (MODULE_MEMS (F_MODULE f)) 0)
		  (λ v_1 : meminst,
			 v_1 <| BYTES :=
			 list_slice_update (BYTES v_1)
			   (v_i + OFFSET v_mo)%coq_nat (v_n / 8)
			   (fun_ibytes v_n
				  (fun_wrap (fun_size (valtype__INN v_inn)) v_n v_c)) |>) |>) as s'.
		assert (Store_extension s s').
		{
			eapply Store_extension__ with (v_meminst_1 := (MEMS s)) (v_meminst_1' := (MEMS s')) (v_meminst_2 := []);
			repeat split; subst; simpl; try rewrite <- app_right_nil => //=.
			- by rewrite list_update_length_func.
			- by eapply func_extension_same.
			- by eapply table_extension_same.
			- (* Mem extension *)
				inversion HIT; decomp; subst; simpl in *.
				apply Forall2_lookup2 in H15; destruct H15. apply H7 in H0.
				inversion H0; decomp; subst.
				inversion HStore; decomp; subst; simpl in *.
				eapply Forall2_list_update_func2; eauto.
				- by apply mem_extension_same.
				- unfold set; simpl. destruct v_mt'. apply mk_Mem_extension => //=.
			- inversion HStore; decomp; subst; simpl in *.
				eapply global_extension_same; eauto.
		}
		split => //=.
		eapply update_mem_unchagned_func in Heqs' as ?; decomp.
		subst; simpl in *.
		destruct s. simpl in *.
		inversion HStore; decomp; subst. 
		injection H14 as ?; subst.
		eapply Store_ok__OK; repeat split; simpl; eauto.
		- erewrite list_update_length_func; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H15; destruct H15. apply H14 in HIn. inversion HIn; destruct H15 as [? [? ?]].
			eapply Function_instance_ok__ with (v_C := v_C); repeat split => //=.
			eapply module_inst_typing_extension; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H16; destruct H16. apply H14 in HIn. inversion HIn. destruct H16 as [? [? ?]].
			eapply Global_instance_ok__; repeat split; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H17; destruct H17. apply H14 in HIn. inversion HIn; decomp; subst.
			inversion H25. inversion H19; subst. destruct H27.
			eapply Table_instance_ok__; repeat split; eauto.
			apply Forall2_forall2; split => //=; move => x' y' HIn'. 
			apply Forall2_forall2 in H24; destruct H24.
			apply H24 in HIn'. 
			apply Forall2_forall2 in HIn'; destruct HIn'.
			apply Forall2_forall2; split => //=; move => x'' y'' HIn''.
			apply H27 in HIn''. 
			inversion HIn''; decomp; subst.
			eapply Externaddrs_ok__func; eauto.
		- eapply Forall2_list_update_func; eauto.
			- apply Forall2_forall2; split => //=; move => x y HIn.
				apply Forall2_forall2 in H18. apply H18 in HIn.
				inversion HIn; decomp; subst.
				eapply Memory_instance_ok__; eauto.
			- 	
				inversion H1; decomp; subst. simpl in *.
				removeinstSimpler H27.
				removeinstSimpler H28.
				removeinstSimpler H30.
				rewrite H7 in H21.
				removeinstSimpler H29.
				subst.
				simpl in *.
				apply Forall2_lookup in H33; destruct H33.
				inversion HIT; decomp; subst; simpl in *.
				apply Forall2_lookup2 in H37; destruct H37.
				apply H26 in H0. inversion H0. destruct H41 as [? [? ?]]; simpl in H41.
				simpl in H42. 
				apply H19 in H41 as H'.
				rewrite H42 in H'.
				inversion H'. subst.
				unfold set.
				rewrite H42. simpl.
				apply Forall2_lookup in H18; destruct H18.
				apply H37 in H41.
				inversion H41; decomp; subst.
				rewrite H42 in H39.
				injection H39 as ?.
				rewrite H39.
				rewrite H39 in H48.
				inversion H48. inversion H46; decomp.
				eapply Memory_instance_ok__; repeat split; eauto.
	- (* Memory Grow Succeed *)
		destruct H3; destruct H1; subst.
		apply_composition_typing_and_single HType.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Grow_memory_typing in H4_comp; destruct H4_comp as [v_mt' [ts' [? [? [? ?]]]]].
		subst.
		remember (s <| MEMS :=
		list_update (MEMS s)
		  (lookup_total (MODULE_MEMS (F_MODULE f)) 0) v_mi |>) as s'.

		assert (Store_extension s s').
		{
			eapply Store_extension__ with (v_meminst_1 := (MEMS s)) (v_meminst_1' := (MEMS s')) (v_meminst_2 := []);
			repeat split; subst s'; simpl; try rewrite <- app_right_nil => //=.
			- by rewrite list_update_length.
			- by eapply func_extension_same.
			- by eapply table_extension_same.
			- (* Mem extension *)
				inversion HIT; decomp; subst; simpl in *.
				apply Forall2_lookup2 in H13; destruct H13. apply H5 in H0.
				inversion H0; decomp; subst.
				inversion HStore; decomp; subst; simpl in *.
				eapply Forall2_list_update2; eauto.
				- by apply mem_extension_same.
				- unfold fun_mem in H.
					inversion H; decomp; subst.
					simpl in H15. rewrite <- H1 in H15. simpl in H15. rewrite H15 in H18.
					injection H18 as ?; subst.
					apply mk_Mem_extension => //=.
					apply leadd.
			- inversion HStore; decomp; subst; simpl in *.
				eapply global_extension_same; eauto.
		}
		split => //=.
		eapply update_mem_unchagned in Heqs' as ?; decomp.
		subst; simpl in *.
		destruct s. simpl in *.
		inversion HStore; decomp; subst. 
		injection H12 as ?; subst.
		inversion H; decomp.
		unfold fun_mem in H8.

		eapply Store_ok__OK with (v_memtype := list_update v_memtype ((lookup_total (MODULE_MEMS (F_MODULE f)) 0)) (limits__ (v_i + v_n)%coq_nat v_j)); repeat split; simpl; eauto.
		- erewrite list_update_length; rewrite list_update_length; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H13; destruct H13. apply H22 in HIn. inversion HIn. destruct H23 as [? [? ?]].
			eapply Function_instance_ok__ with (v_C := v_C); repeat split => //=.
			eapply module_inst_typing_extension; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H14; destruct H14. apply H22 in HIn. inversion HIn. destruct H23 as [? [? ?]].
			eapply Global_instance_ok__; repeat split; eauto.
		- apply Forall2_forall2; split => //=. move => x y HIn.
			apply Forall2_forall2 in H15; destruct H15. apply H22 in HIn. inversion HIn; decomp; subst.
			inversion H30. inversion H12; subst. destruct H24.
			eapply Table_instance_ok__; repeat split; eauto.
			apply Forall2_forall2; split => //=; move => x' y' HIn'. 
			apply Forall2_forall2 in H29; destruct H29.
			apply H20 in HIn'. 
			apply Forall2_forall2 in HIn'; destruct HIn'.
			apply Forall2_forall2; split => //=; move => x'' y'' HIn''.
			apply H25 in HIn''. 
			inversion HIn''; decomp; subst.
			eapply Externaddrs_ok__func; eauto.
		- 	
			eapply Forall2_list_update_both; eauto.
			- apply Forall2_forall2; split => //=; move => x y HIn.
				apply Forall2_forall2 in H16; destruct H16. apply H22 in HIn.
				inversion HIn; decomp; subst.
				eapply Memory_instance_ok__; eauto.
			-
				subst.
				eapply Memory_instance_ok__; split; eauto.
				eapply Memtype_ok__OK.
				eapply Limits_ok__; split; eauto.
				simpl in H8.
				inversion HIT; decomp; subst.
				rewrite <- H12 in H8.
				simpl in H8.
				apply Forall2_lookup in H16; destruct H16.
				simpl in H0.
				apply Forall2_lookup2 in H28; destruct H28.
				apply H28 in H0. inversion H0; decomp.
				simpl in H33.
				apply H17 in H33.
				rewrite H8 in H33.
				inversion H33.
				destruct H38.
				inversion H41.
				inversion H42.
				decomp.
				apply H48.
Qed. *)
	
Lemma reduce_inst_unchanged: forall s f ais s' f' ais',
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    F_MODULE f = F_MODULE f'.
Proof.
	move => s f ais s' f' ais' HReduce.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent ais. generalize dependent ais'.
	induction HReduce; try intros; try (induction v_z); try induction v_z'; try (apply config_same in Heqc1;
	apply config_same in Heqc2; destruct Heqc1 as [? [? ?]];
	destruct Heqc2 as [? [? ?]]; subst => //).
	eapply IHHReduce; eauto.
Qed.

(* Preservation of Admin_instrs_ok under pure steps *)

Theorem t_pure_preservation: forall v_s v_minst v_ais v_ais' v_C loc lab ret tf,
    Module_instance_ok v_s v_minst v_C ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C loc ret) lab) v_ais tf ->
    Step_pure v_ais v_ais' ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C loc ret) lab) v_ais' tf.
Proof.
	move => v_s v_minst v_ais v_ais' v_C loc lab ret tf HInstType HType HReduce.
	inversion HReduce; subst.
	all: try by eapply construct_ais_trap.
	- eapply Step_pure__nop_preserves; eauto.
	- eapply Step_pure__drop_preserves; eauto.
	- eapply Step_pure__select_true_preserves; eauto.
	- eapply Step_pure__select_false_preserves; eauto.
	- eapply Step_pure__if_true_preserves; eauto.
	- eapply Step_pure__if_false_preserves; eauto.
	- eapply Step_pure__label_vals_preserves; eauto.
	- eapply Step_pure__br_zero_preserves; eauto.
	- eapply Step_pure__br_succ_preserves; eauto.
	- eapply Step_pure__br_if_true_preserves; eauto.
	- eapply Step_pure__br_if_false_preserves; eauto.
	- eapply Step_pure__br_table_lt_preserves; eauto.
	- eapply Step_pure__br_table_ge_preserves; eauto.
	- eapply Step_pure__frame_vals_preserves; eauto.
	- eapply Step_pure__return_frame_preserves; eauto.
	- eapply Step_pure__return_label_preserves; eauto.
	- eapply Step_pure__unop_val_preserves; eauto.
	- eapply Step_pure__binop_val_preserves; eauto.
	- eapply Step_pure__testop_preserves; eauto.
	- eapply Step_pure__relop_preserves; eauto.
	- eapply Step_pure__cvtop_val_preserves; eauto.
	- eapply Step_pure__ref_is_null_true_preserves; eauto.
	- eapply Step_pure__ref_is_null_false_preserves; eauto.
	72: eapply Step_pure__local_tee_preserves; eauto.
Admitted.

Lemma t_read_preservation: forall v_s v_f v_ais v_ais' v_C v_C' v_t1 t1s t2s,
    Step_read (mk_config (mk_state v_s v_f) v_ais) v_ais' ->
    Store_ok v_s ->
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) v_t1 (F_LOCALS v_f) ->
	inst_match v_C v_C' ->
    Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
    Admin_instrs_ok v_s v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_ais' v_C v_C' v_t1 t1s t2s HReduce HST.
	move: v_C v_C' t1s t2s.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	induction HReduce;
	move => v_C v_C' tx ty HIT1 HValOK Him HType; decomp; destruct v_z; try eauto;
	try (apply config_same in Heqc1; destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; subst => //).
	all: try by eapply construct_ais_trap.
	{ (* Block *)
		typing_inversion HType.
		typing_inversion H2.
		simpl in Hai;
		extract_premise.
		vals_typing_inversion H1.

		assert (extr = v_t_1 /\ extr0 = v_t_2) as [He1 He2]. {
			by eapply bt_inversion; eauto.
		}
		subst.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub0) in Hsub
		as [Hsubi Hsubs].
		2: {
			eapply Forall2_length in Hforall.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_typing_single with (ts1 := []) (ts2 := v_t_2).
		2: auto.
		eapply AI_ok_label; auto.
		{ eapply instrs_empty_typing. eapply resulttype_sub_refl. }

		eapply construct_ais_compose.
		{
			eapply construct_ais_vals; eauto.
			by eapply instrtype_sub_refl.
		}
		eapply construct_ais_instrtype_sub.
		{
			eapply AIs_ok_instrs.
			eapply H4.
		}
		by eapply instrtype_sub_iff_resulttype_sub'.
	}
	{ (* Loop *)
		typing_inversion HType.
		typing_inversion H2.
		simpl in Hai;
		extract_premise.
		vals_typing_inversion H1.

		assert (extr = v_t_1 /\ extr0 = v_t_2) as [He1 He2]. {
			by eapply bt_inversion; eauto.
		}
		subst.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub0) in Hsub
		as [Hsubi Hsubs].
		2: {
			eapply Forall2_length in Hforall.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_typing_single with (ts1 := []) (ts2 := v_t_2).
		2: auto.
		eapply AI_ok_label; auto.
		{
			eapply construct_instrs_typing_single.
			2: {
				eapply instrtype_sub_refl.
			}
			econstructor. eauto. eauto.
		}
		{
			eapply construct_ais_compose.
			{
				eapply construct_ais_vals; eauto.
				eapply instrtype_sub_iff_resulttype_sub.
				eapply Hsubs.
			}
			eapply construct_ais_instrtype_sub.
			{
				eapply AIs_ok_instrs.
				eapply H4.
			}
			by eapply instrtype_sub_refl.
		}
		eauto.
	}
	{ (* Call *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		Opaque instrtype_sub.
		destruct v_f; simpl in *;
		destruct F_MODULE; simpl in *;
		destruct v_s; simpl in *;
		destruct v_C; simpl in *;
		destruct v_C'; simpl in *;
		unfold inst_match in Him; destruct_all; simpl in *; subst.
		inversion HIT1; subst.
		econstructor.
		eapply Forall2_nth in H23 as [_ H23];
		eapply (H23 _ _ _ ) in H.
		inversion H; subst; simpl in *.

		eapply extaddr_ok_func with (v_minst := v_minst) (v_func := v_func).
		{ eauto. }
		simpl in *.
		rewrite H6.
		unfold lookup_total in *.
		by erewrite H0.
	}
	{ (* Call_indirect *)
		typing_inversion HType.
		typing_inversion H3;
		simpl in Hai;
		extract_premise.
		typing_inversion H4;
		simpl in Hai;
		extract_premise.
		eapply (instrtype_sub_compose_le _ _ _ _ _ _ _ _ Hsub) in Hsub0
		as [Hsub0 _].
		rewrite cats0 in Hsub0.

		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		2: auto.

		destruct v_f; simpl in *;
		destruct F_MODULE; simpl in *;
		destruct v_s; simpl in *;
		destruct v_C; simpl in *;
		destruct v_C'; simpl in *;
		unfold inst_match in Him; destruct_all; simpl in *; subst.
		inversion HIT1; subst.
		econstructor.
		unfold lookup_total in *.
		simpl in *.

		eapply Forall2_nth in H30 as [_ H30].
		rewrite H29 in H30.
		eapply (H30) in H3.
		inversion H3; subst; simpl in *.
		unfold lookup_total in *.
		rewrite H11 in H0.
		rewrite H11 in H.
		simpl in *.


		inversion HST; subst; simpl in *.
		inversion H6; subst; clear H6.

		eapply Forall2_nth in H28 as [_ H28].

		
		econstructor.
		admit.
		admit.
	}
	{ (* Call_addr *)
		typing_inversion HType.
		vals_typing_inversion H1.
		typing_inversion H3.
		simpl in Hai;
		extract_premise.

		inversion H3; subst; clear H3.
		unfold fun_funcinst in *.
		rewrite H0 in H8.
		inversion H8; subst; clear H8.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub) in Hsub0
		as [Hsub0 Hsubs].
		2: {
			eapply Forall2_length in Hforall.
			rewrite H5 in Hforall.
			auto.
		}

		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		eapply AI_ok_frame.
		2: auto.

		inversion HST.
		eapply Forall2_nth in H4 as [_ H4].
		simpl in *.
		rewrite H1 in H.
		eapply H4 in H.
		rewrite H1 in H0; simpl in H0.
		inversion H. unfold lookup_total in H0.
		erewrite H0 in H17.
		inversion H17.
		rewrite H25 in H19.
		subst.
		Search v_C0.

		eapply mk_Thread_ok with (v_C := v_C0).
		{
			eapply mk_Frame_ok with (v_t := (List.map typeof v_val) ++ v_t).
			2: {
				rewrite -!size_length.
				rewrite !size_cat.
				rewrite !size_map.
				auto.
			}
			2: {
				eapply Forall2_app.
				{
					clear Hsub Hsubs H5.
					move: v_ts Hforall.
					induction v_val; eauto.
					move=> v_ts Hforall.
					destruct v_ts; inversion Hforall; subst.
					simpl; econstructor.
					{
						rewrite value_pt_iff_Val_ok in H5.
						inversion H5; subst; unfold typeof; eauto.
						inversion H1; subst; eauto.
					}
					eapply IHv_val; eauto.
				}
				{
					clear H0.
					induction v_t; eauto.
					simpl.
					econstructor.
					{
						destruct a; unfold fun_default_, the.
						all: try econstructor.
						
						eapply ok_reftype with (v_r := REF_NULL _) (v_rt := FUNCREF); econstructor.
						eapply ok_reftype with (v_r := REF_NULL _) (v_rt := EXTERNREF); econstructor.
						inversion H2; subst; contradiction.
					}
					eapply IHv_t; eauto.
					by inversion H2.
				}
			}
			Search v_a.
			econstructor.
			{
				destruct v_s, v_minst.
				econstructor.
			}
			econstructor.
		}
		2: {
			eapply construct_ais_typing_single.
			2: eapply instrtype_sub_refl.
			econstructor.
			eapply instrs_empty_typing; eapply resulttype_sub_refl.
		}
		{
			econstructor.
			Search v_minst.
			inversion HIT1; subst.
		}
		Opaque instrtype_sub.
		destruct v_f; simpl in *;
		destruct F_MODULE; simpl in *;
		destruct v_s; simpl in *;
		destruct v_C; simpl in *;
		destruct v_C'; simpl in *;
		unfold inst_match in Him; destruct_all; simpl in *; subst.
		inversion HIT1; subst.
		econstructor.
		eapply Forall2_nth in H23 as [_ H23];
		eapply (H23 _ _ _ ) in H.
		inversion H; subst; simpl in *.

		eapply extaddr_ok_func with (v_minst := v_minst) (v_func := v_func).
		{ eauto. }
		simpl in *.
		rewrite H6.
		unfold lookup_total in *.
		by erewrite H0.

	}
	{

	}
Admitted. (*
	- eapply Step_read__local_get_preserves; eauto.
	- eapply Step_read__global_get_preserves; eauto.
	- eapply Step_read__load_num_trap_preserves; eauto.
	- eapply Step_read__load_num_val_preserves; eauto.
	- eapply Step_read__load_pack_trap_I32_preserves; eauto.
	- eapply Step_read__load_pack_trap_I64_preserves; eauto.
	- eapply Step_read__load_pack_val_I32_preserves; eauto.
	- eapply Step_read__load_pack_val_I64_preserves; eauto.
	- eapply Step_read__memory_size_preserves; eauto.
Qed. *)

Lemma t_preservation_type: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_t1 t1s t2s lab ret,
    Step (mk_config (mk_state v_s v_f) v_ais) (mk_config (mk_state v_s' v_f') v_ais') ->
    Store_ok v_s ->
    Store_ok v_s' ->
	Store_extension v_s v_s' -> 
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
    Module_instance_ok v_s' (F_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) v_t1 (F_LOCALS v_f) ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) v_ais (t1s :-> t2s) ->
    Admin_instrs_ok v_s' (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_s' v_f' v_ais' v_C v_t1 t1s t2s lab ret HReduce HST1 HST2 HSExt.
	move: v_C ret lab t1s t2s.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	remember (mk_config (mk_state v_s' v_f') v_ais') as c2.
	generalize dependent v_ais.
	generalize dependent v_ais'.
	generalize dependent v_t1.
	generalize dependent v_f.
	generalize dependent v_f'.
	induction HReduce; move => r_v_f' r_v_f v_t1 v_ais' Heqc2 v_ais Heqc1 v_C ret lab tx ty HIT1 HIT2 HValOK HType; try (destruct v_z; subst);  try (destruct v_z'; subst); try eauto;
	try (apply config_same in Heqc1; apply config_same in Heqc2; 
		destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; 
		destruct Heqc2 as [Hafter1 [Hafter2 Hafter3]]; subst => //).
	- (* Step_pure *) eapply t_pure_preservation; eauto.
	- (* Step_read *) eapply t_read_preservation; eauto.
	- (* Context Label *) 
(*
		rewrite <- admin_instrs_ok_eq in HType.
		apply Label_typing in HType as H. destruct H as [ts [ts2' [? [? [? ?]]]]].
		subst.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		apply AI_ok_label with (v_t_1 := ts).
		repeat split => //=.
		eapply IHHReduce => //=.
	- (* Context Frame *)
		rewrite <- admin_instrs_ok_eq in HType.
		apply Frame_typing in HType as H. destruct H as [ts [? [? ?]]].
		subst.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		apply AI_ok_frame.
		split => //.
		inversion H0. subst. destruct H.
		apply Thread_ok__ with (v_C := v_C0).
		inversion H; destruct H2 as [? [? ?]]. 
		split.
		- apply Frame_ok__.
			repeat split => //=.
			eapply module_inst_typing_extension; eauto.
		-
			apply inst_t_context_local_empty in H6 as H'.
			rewrite upd_label_unchanged_typing.
			remember v_t as val.
			rewrite -> app_right_nil in Heqval.
			rewrite <- H' in Heqval. subst.
			eapply IHHReduce => //=.
			eapply module_inst_typing_extension; eauto.
	- (* Local set *)
		apply_composition_typing_and_single HType.
		destruct v_val.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Set_local_typing in H4_comp; destruct H4_comp as [t [? [? ?]]].
		subst.
		repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
		subst.
		apply admin_weakening_empty_both.
		apply AIs_ok_empty.
	- (* Global set *)
		apply_composition_typing_and_single HType.
		destruct v_val.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Set_global_typing in H4_comp. destruct H4_comp as [t [? [? ?]]].
		subst.
		repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
		subst.
		apply admin_weakening_empty_both.
		apply AIs_ok_empty.
	- (* Store Num Trap *)
		rewrite <- admin_instrs_ok_eq.
		apply AI_ok_trap.
	- (* Store Num Val *)
		apply_composition_typing HType.
		apply_composition_typing_and_single H4_comp.
		rewrite <- admin_instrs_ok_eq in H3_comp.
		apply AI_const_typing in H3_comp.
		apply AI_const_typing in H4_comp.
		rewrite <- admin_instrs_ok_eq in H4_comp0.
		apply Store_typing in H4_comp0; destruct H4_comp0 as [v_n [v_mt [v_inn [? [? [? [? [? ?]]]]]]]].
		subst.
		remember [:: I32; v_t] as v_t'.
		rewrite -cat1s in Heqv_t'.
		subst.
		repeat rewrite -> app_assoc in H; apply split_append_last in H; destruct H; subst.
		rewrite H in H1_comp0.
		repeat rewrite -> app_assoc in H1_comp0; apply split_append_last in H1_comp0; destruct H1_comp0; subst.
		subst.
		apply admin_weakening_empty_both.
		apply AIs_ok_empty.
	- (* Store Pack Trap *)
		rewrite <- admin_instrs_ok_eq.
		apply AI_ok_trap.
	- (* Store Pack Val *)
		apply_composition_typing HType.
		apply_composition_typing_and_single H4_comp.
		rewrite <- admin_instrs_ok_eq in H3_comp.
		apply AI_const_typing in H3_comp.
		apply AI_const_typing in H4_comp.
		rewrite <- admin_instrs_ok_eq in H4_comp0.
		apply Store_typing in H4_comp0; destruct H4_comp0 as [v_n' [v_mt' [v_inn' [? [? [? [? [? ?]]]]]]]].
		subst.
		remember [:: I32; valtype__INN v_inn] as v_t'.
		rewrite -cat1s in Heqv_t'.
		subst.
		repeat rewrite -> app_assoc in H; apply split_append_last in H; destruct H; subst.
		rewrite H in H1_comp0.
		repeat rewrite -> app_assoc in H1_comp0; apply split_append_last in H1_comp0; destruct H1_comp0; subst.
		subst.
		apply admin_weakening_empty_both.
		apply AIs_ok_empty.
	- (* Memory Grow Succeed *)
		apply_composition_typing_and_single HType.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Grow_memory_typing in H4_comp; destruct H4_comp as [v_mt [ts [? [? [? ?]]]]].
		subst.
		repeat rewrite -> app_assoc in H3; apply split_append_last in H3; destruct H3; subst.
		repeat rewrite -> app_assoc.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		remember (Datatypes.length (BYTES (fun_mem (mk_state v_s r_v_f) 0)) / (64 * fun_Ki)%coq_nat) as v_n'.
		eapply (AI_ok_instr _ _ (CONST (I32) v_n') (mk_functype [] [(I32)])).
		apply const.
	- (* Memory Grow Fail *)
		apply_composition_typing_and_single HType.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Grow_memory_typing in H4_comp; destruct H4_comp as [v_mt [ts [? [? [? ?]]]]].
		subst.
		repeat rewrite -> app_assoc in H2; apply split_append_last in H2; destruct H2; subst.
		repeat rewrite -> app_assoc.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		remember (fun_invsigned 32 (0 - 1)%coq_nat) as v_n'.
		eapply (AI_ok_instr _ _ (CONST (I32) v_n') (mk_functype [] [(I32)])).
		apply const.
Qed. *)
Admitted.


(* Ultimate goal of project *)				
Theorem t_preservation: forall c1 ts c2,
	Step c1 c2 ->
	Config_ok c1 ts ->
	Config_ok c2 ts.
Proof.
	move => c1 ts c2 HReduce HConfig1.
	destruct c1; destruct v_state as [store1 frame1].
	destruct c2; destruct v_state as [store2 frame2].
	(* Config_ok c1 *)
	inversion HConfig1; clear HConfig1.
	rename H3 into HStore1.
	rename H4 into HThread1.
	(* Store_ok store1 *)
	inversion HStore1.
	(* Thread_ok store1 None frame1 l (mk_list _ v_t) *)
	inversion HThread1; clear HThread1.
	rename H17 into HFrame1.
	(* Frame_ok store1 frame1 v_C *)
	inversion HFrame1; clear HFrame1.
	rename H17 into HModuleInst1.
	rename H22 into HAIs1.
	(* Module_instance_ok store1 v_moduleinst v_C0 *)
	inversion HModuleInst1.
	subst.

	remember {|
		FUNCS := v_funcinst; GLOBALS := v_globalinst; TABLES := v_tableinst;
		MEMS := v_meminst; ELEMS := v_eleminst;	DATAS := v_datainst
	|} as store1.
	remember {|
		MODULE_TYPES := v_functype0;
		MODULE_FUNCS := v_funcaddr;
		MODULE_GLOBALS := v_globaladdr;
		MODULE_TABLES := v_tableaddr;
		MODULE_MEMS := v_memaddr;
		MODULE_ELEMS := v_elemaddr;
		MODULE_DATAS := v_dataaddr;
		MODULE_EXPORTS := v_exportinst
	|} as v_moduleinst.
	remember {|
		F_LOCALS := v_val;
		F_MODULE := v_moduleinst
	|} as frame1.
	remember {|
		C_TYPES := v_functype0;
		C_FUNCS := v_functype';
		C_GLOBALS := v_globaltype0;
		C_TABLES := v_tabletype0;
		C_MEMS := v_memtype0;
		C_ELEMS := v_reftype0;
		C_DATAS := [];
		C_LOCALS := [];
		C_LABELS := [];
		C_RETURN := None
	|} as v_C0.

	assert (Store_extension store1 store2 /\ Store_ok store2) as
	[HStore_extension HStore2].
	{
		apply (store_extension_reduce 
			store1  
			{|F_LOCALS := v_val;F_MODULE := v_moduleinst|} 
			l
			store2
			frame2
			l0
			v_C0
			(upd_local_return v_C0
					(_append v_t1 (C_LOCALS v_C0))
					(_append (option_map [eta (mk_list _)] None)
						(C_RETURN v_C0)))
			([] :-> (mk_list valtype v_t)) 
			); auto; subst; auto.
		by resolve_inst_match.
	}
	apply reduce_inst_unchanged in HReduce as HModuleInst.
	destruct frame2 as [locals2 module2].
	simpl in HModuleInst.
	assert (Module_instance_ok store2 v_moduleinst v_C0). {
		apply (module_inst_typing_extension store1); eauto.
	}

	apply mk_Config_ok; auto.
	rewrite Heqframe1 in HModuleInst; simpl in HModuleInst.
	rewrite <- HModuleInst.
	eapply mk_Thread_ok; auto.
	{
		eapply (mk_Frame_ok store2 locals2 v_moduleinst v_C0 v_t1); eauto;
		apply (t_preservation_vs_type) with
			(v_t1 := v_t1)
			(C := v_C0)
			(C' := v_C0) 
			(lab:= (C_LABELS (upd_local_return v_C0
				(_append v_t1 (C_LOCALS v_C0))
				(_append (option_map [eta (mk_list _)] None) (C_RETURN v_C0))))) 
			(ret:= (_append (None) (C_RETURN v_C0)))
			(t1s := [])
			(t2s := (mk_list valtype v_t))
			in HReduce as HVals2;
			try (solve [subst; auto | subst; simpl; try rewrite cats0; auto]).
			simpl in HVals2; eapply Forall2_length; eauto.
	}
	subst.

	(* Actual Typing proof *)
	eapply t_preservation_type; eauto.
Qed.