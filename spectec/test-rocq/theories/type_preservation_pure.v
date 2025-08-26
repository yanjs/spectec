
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.

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


(* Preservation of Admin_instrs_ok under pure steps *)

Theorem t_pure_preservation: forall v_s v_ais v_ais' v_C tf,
    Admin_instrs_ok v_s v_C v_ais tf ->
    Step_pure v_ais v_ais' ->
    Admin_instrs_ok v_s v_C v_ais' tf.
Proof.
	move => v_s v_ais v_ais' v_C tf HType HReduce.
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
	(* Rest are all simd instructions *)
Admitted.