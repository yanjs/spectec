
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

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

		
Lemma Step_pure__unreachable_preserves : forall v_S v_C  v_func_type,
	Admin_instrs_ok v_S v_C [(AI_UNREACHABLE )] v_func_type ->
	Step_pure [(AI_UNREACHABLE )] [(AI_TRAP )] ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	move => v_S v_C v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (AIs_ok_seq v_S v_C [] (AI_TRAP) tf1 tf2 tf1).
	- apply admin_weakening_empty_both. apply AIs_ok_empty.
	- apply AI_ok_trap.
Qed.

Lemma Step_pure__nop_preserves : forall v_S v_C  v_func_type,
	Admin_instrs_ok v_S v_C [(AI_NOP )] v_func_type ->
	Step_pure [(AI_NOP )] [] ->
	Admin_instrs_ok v_S v_C [] v_func_type.
Proof.
	move => v_S v_C v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_single HType; subst.
	apply AIs_ok_frame.
	apply Nop_typing in H4_comp; subst.
	apply admin_weakening_empty_both.
	apply AIs_ok_empty.
Qed.

Lemma Step_pure__drop_preserves : forall v_S v_C (v_val : val) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(AI_DROP )] v_func_type ->
	Step_pure [(v_val : admininstr);(AI_DROP )] [] ->
	Admin_instrs_ok v_S v_C [] v_func_type.
Proof.
	move => v_S v_C v_val v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.

	apply Drop_typing in H4_comp1; destruct H4_comp1 as [t H1]; subst.
	apply_const_typing_to_val H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1; subst.
	rewrite H.
	apply admin_weakening_empty_both.
	apply AIs_ok_empty.
Qed.

Lemma Step_pure__select_true_preserves : forall v_S v_C (v_val_1 : val) (v_val_2 : val) (v_c : iN 32) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 (v_c));(AI_SELECT )] v_func_type ->
	Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 (v_c));(AI_SELECT )] [(v_val_1 : admininstr)] ->
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr)] v_func_type.
Proof.
	move => v_S v_C v_val_1 v_val_2 v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_and_single H4_comp1.
	apply_composition_typing_single H4_comp2.
	induction v_val_1.
	apply AI_const_typing in H4_comp0.
	apply_const_typing_to_val H4_comp.
	apply AI_const_typing in H4_comp1.
	apply Select_typing in H4_comp3; destruct H4_comp3 as [v_ts [v_t [H4_comp3 H4_comp3']]].
	subst.
	remember [:: v_t; v_t; I32] as v_select.
	rewrite -cat1s in Heqv_select.
	remember [:: v_t; I32] as v_select2.
	rewrite -cat1s in Heqv_select2; subst.
	repeat rewrite -> app_assoc in H1_comp2.
	apply split_append_last in H1_comp2; destruct H1_comp2.
	rewrite H in H1_comp0.
	repeat rewrite -> app_assoc in H1_comp0.
	apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H1 in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H3.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (VAL_CONST v_valtype v_val_) [] [v_t] []). 
	apply AIs_ok_empty.
	unfold fun_coec_val__admininstr.
	apply (AI_ok_instr v_S v_C (CONST v_valtype v_val_) (mk_functype [] [v_t])); subst.
	apply const.
Qed.

Lemma Step_pure__select_false_preserves : forall v_S v_C (v_val_1 : val) (v_val_2 : val) (v_c : iN 32) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 v_c);(AI_SELECT )] v_func_type ->
	Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(AI_CONST I32 v_c);(AI_SELECT )] [(v_val_2 : admininstr)] ->
	Admin_instrs_ok v_S v_C [(v_val_2 : admininstr)] v_func_type.
Proof.
	move => v_S v_C v_val_1 v_val_2 v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_and_single H4_comp1.
	apply_composition_typing_single H4_comp2.
	apply_const_typing_to_val H4_comp0.
	induction v_val_2.
	apply AI_const_typing in H4_comp.
	apply AI_const_typing in H4_comp1.
	apply Select_typing in H4_comp3; destruct H4_comp3 as [v_ts [v_t [H4_comp3 H4_comp3']]].
	subst.
	remember [:: v_t; v_t; I32] as v_select.
	rewrite -cat1s in Heqv_select.
	remember [:: v_t; I32] as v_select2.
	rewrite -cat1s in Heqv_select2; subst.
	repeat rewrite -> app_assoc in H1_comp2.
	apply split_append_last in H1_comp2; destruct H1_comp2.
	rewrite H in H1_comp0.
	repeat rewrite -> app_assoc in H1_comp0.
	apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H1 in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H3.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (VAL_CONST v_valtype0 v_val_0) [] [v_t] []). 
	apply AIs_ok_empty.
	unfold fun_coec_val__admininstr.
	apply (AI_ok_instr v_S v_C (CONST v_valtype0 v_val_0) (mk_functype [] [v_t])); subst.
	apply const.
Qed.

Lemma Step_pure__if_true_preserves : forall v_S v_C (v_c : iN 32) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_IFELSE v_t v_instr_1 v_instr_2)] v_func_type ->
	Step_pure [(AI_CONST I32 v_c);(AI_IFELSE v_t v_instr_1 v_instr_2)] [(AI_BLOCK v_t v_instr_1)] ->
	Admin_instrs_ok v_S v_C [(AI_BLOCK v_t v_instr_1)] v_func_type.
Proof.
	move => v_S v_C v_c v_t v_instr_1 v_instr_2 v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply If_typing in H4_comp1; destruct H4_comp1 as [ts0 [H1 [H2 [H3 H4]]]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (AI_BLOCK v_t v_instr_1) [] v_t []). 
	apply AIs_ok_empty.
	apply (AI_ok_instr v_S v_C (BLOCK v_t v_instr_1) (mk_functype [::] v_t)).
	apply (block).
	rewrite <- upd_label_is_same_as_append.
	apply H3.
Qed.

Lemma Step_pure__if_false_preserves : forall v_S v_C (v_c : iN 32) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_IFELSE v_t v_instr_1 v_instr_2)] v_func_type ->
	Step_pure [(AI_CONST I32 v_c);(AI_IFELSE v_t v_instr_1 v_instr_2)] [(AI_BLOCK v_t v_instr_2)] ->
	Admin_instrs_ok v_S v_C [(AI_BLOCK v_t v_instr_2)] v_func_type.
Proof.
	move => v_S v_C v_c v_t v_instr_1 v_instr_2 v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply If_typing in H4_comp1; destruct H4_comp1 as [H1 [H2 [H3 H4]]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (AI_BLOCK v_t v_instr_2) [] v_t []). 
	apply AIs_ok_empty.
	apply (AI_ok_instr v_S v_C (BLOCK v_t v_instr_2) (mk_functype [::] v_t)).
	apply block.
	rewrite <- upd_label_is_same_as_append.
	apply H4.
Qed.

Lemma Step_pure__label_vals_preserves : forall v_S v_C (v_n : n) (v_instr : (list instr)) (v_val : (list val)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr (map fun_coec_val__admininstr v_val))] v_func_type ->
	Step_pure [(AI_LABEL_ v_n v_instr (map fun_coec_val__admininstr v_val))] (map fun_coec_val__admininstr v_val) ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_val) v_func_type.
Proof.
	move => v_S v_C v_n v_instr v_val v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_single HType.
	apply Label_typing in H4_comp; destruct H4_comp as [ts [ts2' [H1 [H2 [H3 H4]]]]].
	subst.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply Val_Const_list_typing in H4; subst.
	rewrite H4.
	simpl.
	apply Const_list_typing_empty.
Qed.

Lemma Step_pure__br_zero_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val') (@app _ (map fun_coec_val__admininstr v_val) (@app _ [AI_BR 0] (map fun_coec_instr__admininstr v_instr)))))] v_func_type ->
	((List.length v_val) = v_n) ->
	Admin_instrs_ok v_S v_C (@app _ (map fun_coec_val__admininstr v_val) (map fun_coec_instr__admininstr v_instr')) v_func_type.
Proof.
	move => v_S v_C v_n v_instr' v_val' v_val v_instr v_func_type HType HLength.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Label_typing in HType; destruct HType as [ts [ts2' [? [? [? ?]]]]].
	apply_composition_typing H2.
	apply_composition_typing H4_comp.
	apply_composition_typing H4_comp0.
	repeat rewrite <- app_right_nil in *.
	rewrite <- admin_instrs_ok_eq in H3_comp1.
	apply Break_typing in H3_comp1; destruct H3_comp1 as [ts0' [ts1' [? [? ?]]]].
	apply Val_Const_list_typing in H3_comp.
	apply Val_Const_list_typing in H3_comp0.
	apply empty_append in H1_comp; destruct H1_comp.
	subst. simpl in *.
	unfold upd_label, lookup_total in H1_comp1.
	simpl in H1_comp1.
	apply admin_instrs_weakening_empty_1.
	apply admin_composition' with (t2s := ts).
	repeat rewrite -> app_assoc in H1_comp1.
	eapply concat_cancel_last_n in H1_comp1; destruct H1_comp1; subst.
	rewrite <- H2.
	apply Const_list_typing_empty.
	rewrite List.map_length.
	destruct ts => //=. 
	eapply AIs_ok_instrs in H0; eauto.
Qed.


Lemma Step_pure__br_succ_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_l : labelidx) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [AI_BR (v_l + 1)] (map fun_coec_instr__admininstr v_instr))))] v_func_type ->
	Step_pure [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [AI_BR (v_l + 1)] (map fun_coec_instr__admininstr v_instr))))] (@app _ (map fun_coec_val__admininstr v_val) [(AI_BR v_l)]) ->
	Admin_instrs_ok v_S v_C (@app _ (map fun_coec_val__admininstr v_val) [(AI_BR v_l)]) v_func_type.
Proof.
	move => v_S v_C v_n v_instr' v_val v_l v_instr v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Label_typing in HType; destruct HType as [ts [ts2' [? [? [? ?]]]]].
	apply_composition_typing H2.
	apply_composition_typing H4_comp.
	rewrite <- admin_instrs_ok_eq in H3_comp0.
	repeat rewrite <- app_right_nil in *.
	apply Val_Const_list_typing in H3_comp.
	apply Break_typing in H3_comp0. destruct H3_comp0 as [ts0 [ts1' [? [? ?]]]].
	subst.
	apply empty_append in H1_comp; destruct H1_comp; subst.
	simpl in *.
	apply admin_instrs_weakening_empty_1.
	eapply admin_composition'.
	apply Const_list_typing_empty.
	rewrite H1_comp0.
	rewrite H2_comp.
	apply AIs_ok_frame.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_instr with (v_instr := BR v_l).
	apply br.
	- rewrite addn1 in H.
	  unfold lt in H.
	  move: H => /leP Hbool. auto.
	- unfold lookup_total. by rewrite addn1.
Qed.

Lemma Step_pure__preserves__br_if_true : 
  forall (v_l : labelidx) (v_c : iN 32) (v_ft : functype) (v_C : context) (v_s : store), 
  ((Admin_instrs_ok v_s v_C [(AI_CONST I32 v_c);(AI_BR_IF v_l)] v_ft) -> 
  ((Step_pure [(AI_CONST I32 v_c);(AI_BR_IF v_l)] [(AI_BR v_l)]) -> 
  ((v_c <> mk_uN 32 0) -> 
  (Admin_instrs_ok v_s v_C [(AI_BR v_l)] v_ft)))).
Proof.
  move => l c ft C s Hadmin Hstep Hval.
  destruct ft as [ts1 ts2].
	apply_composition_typing_and_single Hadmin.
	apply_composition_typing_single H4_comp.
  destruct l.
  apply Br_if_typing in H4_comp1; destruct H4_comp1 as [ts [ts' [H1 [H2 [H3 H4]]]]].
  apply AI_const_typing in H4_comp0.
  subst.
  repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
  rewrite H.
  repeat rewrite -> app_assoc.
  apply AIs_ok_frame.
  remember (lookup_total (C_LABELS C) v_i) as ts'.
  apply (AIs_ok_seq s C [] (AI_BR v_i) ts' ts' ts').
  apply admin_weakening_empty_both. apply AIs_ok_empty.
  apply (AI_ok_instr _ _ (BR v_i) (mk_functype ts' ts')).
  apply (br C (v_i) [] ts' ts') => //=.
  move: H3 => /leP Hbool. auto. 
Qed.

(* TODO: Example of migrating proofs using auto-translated statements (SSReflect) *)
Lemma cat_app : 
  forall {A : Type} (s1 s2 : seq A),
  app s1 s2 = cat s1 s2.
Proof. by []. Qed.

Lemma cat_inv : 
  forall {A : Type} (s1 : seq A) (s2 : seq A) (x1 : A) (x2 : A),
	s1 ++ [:: x1] = s2 ++ [::x2] ->
	s1 = s2 /\ x1 = x2.
Proof. by apply: app_inj_tail. Qed.

Lemma Admin_instrs_ok_admin_instr_ok : forall s C e ts1 ts2,
  Admin_instrs_ok s C [:: e] (mk_functype ts1 ts2) ->
  exists ts ts1' ts2', 
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Admin_instr_ok s C e (mk_functype ts1' ts2').
Proof.
  move=> s C e ts1 ts2 Hadmin.
  rewrite -[[:: _]]cat0s -cat_app in Hadmin.
  move/admin_composition_typing_single: Hadmin => [ts [ts1' [ts2' [ts3 [Hts1 [Hts2 [Hempty Hadmin]]]]]]].
  exists ts, ts1', ts2'; do ? split.
  - by rewrite -cat_app.
  - by rewrite -cat_app.
  - move/admin_empty_same_type: Hempty => Hts3. 
    by rewrite -{}Hts3 in Hadmin.
Qed.

Lemma Step_pure__br_if_true_preserves : forall v_S v_C (v_c : iN 32) (v_l : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_BR_IF v_l)] v_func_type ->
	Step_pure [(AI_CONST I32 v_c);(AI_BR_IF v_l)] [(AI_BR v_l)] ->
	Admin_instrs_ok v_S v_C [(AI_BR v_l)] v_func_type.
Proof.
	move => v_S v_C v_c v_l v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	destruct v_l.
	apply Br_if_typing in H4_comp1; destruct H4_comp1 as [ts [ts' [H1 [H2 [H3 H4]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply AIs_ok_frame.
	remember (lookup_total (C_LABELS v_C) v_i) as ts'.
	apply (AIs_ok_seq v_S v_C [] (AI_BR v_i) ts' ts' ts').
	apply admin_weakening_empty_both. apply AIs_ok_empty.
	apply (AI_ok_instr _ _ (BR v_i) (mk_functype ts' ts')).
	apply (br v_C v_i [] ts' ts').
	move: H3 => /leP Hbool. auto.
	subst. reflexivity.
Qed.

Lemma Step_pure__br_if_false_preserves : forall v_S v_C (v_c : iN 32) (v_l : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c);(AI_BR_IF v_l)] v_func_type ->
	Step_pure [(AI_CONST I32 v_c);(AI_BR_IF v_l)] [] ->
	Admin_instrs_ok v_S v_C [] v_func_type.
Proof.
	move => v_S v_C v_c v_l v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	destruct v_l.
	apply Br_if_typing in H4_comp1; destruct H4_comp1 as [ts [ts' [H1 [H2 [H3 H4]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_weakening_empty_both. apply AIs_ok_empty.
Qed.

Lemma Step_pure__br_table_lt_preserves : forall v_S v_C (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 (v_i : u32));(AI_BR_TABLE v_l v_l')] v_func_type ->
	Step_pure [(AI_CONST I32 (v_i : u32));(AI_BR_TABLE v_l v_l')] [(AI_BR (lookup_total v_l v_i))] ->
	(v_i < Datatypes.length v_l) -> 
	Admin_instrs_ok v_S v_C [(AI_BR (lookup_total v_l v_i))] v_func_type.
Proof.
	move => v_S v_C v_i v_l v_l' v_func_type HType HReduce H.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply Br_table_typing in H4_comp1.
	destruct H4_comp1 as [ts1' [ts [H1 [H2 [H3 [H4 H5]]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H0.
	repeat rewrite <- app_assoc.
	apply AIs_ok_frame.
	apply AIs_ok_frame.
	remember (ts1' ++ lookup_total (C_LABELS v_C) v_l')%list as ts. (* Just for convencience *)
	apply (AIs_ok_seq v_S v_C [] (AI_BR (lookup_total v_l v_i)) ts ts3_comp1 ts).
	+ (* Empty *) apply admin_weakening_empty_both. apply AIs_ok_empty.
	+ (* BR *) apply (AI_ok_instr _ _ (BR (lookup_total v_l v_i)) (mk_functype ts ts3_comp1)).
		subst. apply (br v_C (lookup_total v_l v_i) ts1' (lookup_total (C_LABELS v_C) v_l') ts3_comp1).
		rewrite Forall_nth in H5.
		rewrite Forall_nth in H2.
	  	move: H => /leP H.
		apply (H5 _ default_val) in H as H6.
		apply (H2 _ default_val) in H as H7.

	  	move: H7 => /leP Hbool. auto.
		rewrite -> Forall_forall in H5.
		assert (In (lookup_total v_l v_i) v_l) as H4.
		{ induction v_l as [| a l].
		  - inversion H; subst.
		  - move: H => /leP H.
		    eapply nth_In in H.
			unfold lookup_total.
			apply H.
		}
		eapply H5 in H4. auto.
Qed.

Lemma Step_pure__br_table_ge_preserves : forall v_S v_C (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST I32 (v_i : u32));(AI_BR_TABLE v_l v_l')] v_func_type ->
	Step_pure [(AI_CONST I32 (v_i : u32));(AI_BR_TABLE v_l v_l')] [(AI_BR v_l')] ->
	(v_i >= (List.length v_l))%coq_nat ->
	Admin_instrs_ok v_S v_C [(AI_BR v_l')] v_func_type.
Proof.
	move => v_S v_C v_i v_l v_l' v_func_type HType HReduce H.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply Br_table_typing in H4_comp1; destruct H4_comp1 as [ts1' [ts [H1 [H2 [H3 [H4 H5]]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H0.
	repeat rewrite <- app_assoc.
	apply AIs_ok_frame.
	apply AIs_ok_frame.
	remember (ts1' ++ lookup_total (C_LABELS v_C) v_l')%list as ts. (* Just for convencience *)
	apply (AIs_ok_seq v_S v_C [] (AI_BR v_l') ts ts3_comp1 ts).
	+ (* Empty *) apply admin_weakening_empty_both. apply AIs_ok_empty.
	+ (* BR *) apply (AI_ok_instr _ _ (BR v_l') (mk_functype ts ts3_comp1)).
		subst. apply (br v_C v_l' ts1' (lookup_total (C_LABELS v_C) v_l') ts3_comp1).

	  	move: H3 => /leP Hbool. auto.
		split => //.
Qed.

Lemma Step_pure__frame_vals_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val : (list val)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_FRAME_ v_n v_f (map fun_coec_val__admininstr v_val))] v_func_type ->
	Step_pure [(AI_FRAME_ v_n v_f (map fun_coec_val__admininstr v_val))] (map fun_coec_val__admininstr v_val) ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_val) v_func_type.
Proof.
	move => v_S v_C v_n v_f v_val v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Frame_typing in HType; destruct HType as [ts [? [? ?]]].
	inversion H0. destruct H2.
	apply Val_Const_list_typing in H3; simpl in *; subst.
	apply admin_instrs_weakening_empty_1.
	rewrite H3.
	apply Const_list_typing_empty.
Qed.

Lemma Step_pure__return_frame_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_FRAME_ v_n v_f (@app _ (map fun_coec_val__admininstr v_val') (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr)))))] v_func_type ->
	Step_pure [(AI_FRAME_ v_n v_f (@app _ (map fun_coec_val__admininstr v_val') (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr)))))] (map fun_coec_val__admininstr v_val) ->
	((List.length v_val) = v_n) ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_val) v_func_type.
Proof.
	move => v_S v_C v_n v_f v_val' v_val v_instr v_func_type HType HReduce H.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Frame_typing in HType; destruct HType as [ts [? [? ?]]].
	inversion H1; destruct H3.
	apply_composition_typing H4.
	apply_composition_typing H4_comp.
	apply_composition_typing H4_comp0.
	repeat rewrite <- app_right_nil in *.
	rewrite <- admin_instrs_ok_eq in H3_comp1.
	apply Val_Const_list_typing in H3_comp.
	apply Val_Const_list_typing in H3_comp0.
	apply empty_append in H1_comp; destruct H1_comp.
	subst. simpl in *.
	apply Return_typing in H3_comp1; destruct H3_comp1 as [ts0 [ts' [? ?]]].
	subst.
	inversion H3.
Admitted. (*
    destruct H0 as [? [? ?]].
	subst.
	inversion H7.
	subst. simpl in *. rewrite _append_option_none_left in H2.
	rewrite _append_option_none in H2.
	injection H2 as ?; subst.
	clear H4.
	repeat rewrite -> app_assoc in H1_comp1.
	eapply concat_cancel_last_n in H1_comp1; destruct H1_comp1.
	rewrite <- H4.
	apply admin_instrs_weakening_empty_1.
	apply Const_list_typing_empty.
	rewrite List.map_length.
	rewrite H.
	by destruct ts0.
Qed. *)

Lemma Step_pure__return_label_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr))))] v_func_type ->
	Step_pure [(AI_LABEL_ v_n v_instr' (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_RETURN )] (map fun_coec_instr__admininstr v_instr))))] (@app _ (map fun_coec_val__admininstr v_val) [(AI_RETURN )]) ->
	Admin_instrs_ok v_S v_C (@app _ (map fun_coec_val__admininstr v_val) [(AI_RETURN )]) v_func_type.
Proof.
	move => v_S v_C v_n v_instr' v_val v_instr v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Label_typing in HType; destruct HType as [ts [ts2' [? [? [? ?]]]]].
	apply_composition_typing H2.
	apply_composition_typing H4_comp.
	repeat rewrite <- app_right_nil in *.
	rewrite <- admin_instrs_ok_eq in H3_comp0.
	apply Return_typing in H3_comp0; destruct H3_comp0 as [ts0 [ts' [? ?]]].
	unfold upd_label, set in H1. simpl in H1.
	apply Val_Const_list_typing in H3_comp.
	apply empty_append in H1_comp; destruct H1_comp.
	subst. simpl in *.
	apply admin_instrs_weakening_empty_1.
	eapply admin_composition'.
	apply Const_list_typing_empty.
	rewrite H1_comp0.
	rewrite H2_comp.
	apply AIs_ok_frame.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_instr with (v_instr := RETURN).
	by apply res_return.
Qed.

Lemma Step_pure__trap_vals_preserves : forall v_S v_C (v_val : (list val)) (v_admininstr : (list admininstr)) v_func_type,
	Admin_instrs_ok v_S v_C (@app _ (map fun_coec_val__admininstr v_val) (@app _ [(AI_TRAP )] v_admininstr)) v_func_type ->
	((v_val <> []) \/ (v_admininstr <> [])) ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	move => v_S v_C v_val v_instr v_func_type HType H.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_pure__trap_label_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_LABEL_ v_n v_instr' [(AI_TRAP )])] v_func_type ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	move => v_S v_C n v_instr' v_func_type HType.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_pure__trap_frame_preserves : forall v_S v_C (v_n : n) (v_f : frame) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_FRAME_ v_n v_f [(AI_TRAP )])] v_func_type ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_pure__unop_val_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_ v_t) (v_unop : unop_ v_t) v_c v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_UNOP v_t v_unop)] v_func_type ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_UNOP v_t v_unop)] [(AI_CONST v_t v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c)] v_func_type.
Proof.
	move => v_S v_C t v unop_op v_c tf HType HReduce.
	destruct tf as [tf1 tf2].
	rewrite -cat1s in HType; subst.
	apply admin_composition_typing_single in HType; destruct HType as [ts1 [ts2 [ts3 [ts4 [H1 [H3 [H4 H5]]]]]]].
	rewrite -> app_left_single_nil in H4; subst.
	apply admin_composition_typing_single in H4; destruct H4 as [ts5 [ts6 [ts7 [ts8 [H6 [H7 [H8 H9]]]]]]].
	apply AI_const_typing in H9.
	apply Unop_typing in H5; destruct H5 as [H10 [ts H11]]. 
	apply admin_empty_same_type in H8; subst.
	repeat rewrite app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (AI_CONST t v_c) [] [t] []).
	apply AIs_ok_empty.
	apply (AI_ok_instr v_S v_C (CONST t v_c) (mk_functype [] [t])).
	by apply const.
Qed.

Lemma Step_pure__unop_trap_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_ v_t) (v_unop : unop_ v_t) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_UNOP v_t v_unop)] v_func_type ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_UNOP v_t v_unop)] [(AI_TRAP )] ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_unop v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (AIs_ok_seq v_S v_C [] (AI_TRAP) tf1 tf2 tf1).
	- (* Empty *) apply admin_weakening_empty_both. apply AIs_ok_empty.
	- (* TRAP *) apply AI_ok_trap.
Qed.


Lemma Step_pure__binop_val_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_ v_t) (v_c_2 : val_ v_t) (v_binop : binop_ v_t) v_c v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_BINOP v_t v_binop)] v_func_type ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_BINOP v_t v_binop)] [(AI_CONST v_t v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c)] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_binop v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_single H4_comp1.
	apply AI_const_typing in H4_comp0.
	apply AI_const_typing in H4_comp.
	apply Binop_typing in H4_comp2; destruct H4_comp2 as [H [ts H0]].
	subst.
	repeat rewrite -> app_assoc in H1_comp0.
	apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H1.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (AI_CONST v_t v_c) [] [v_t] []).
	apply AIs_ok_empty.
	apply (AI_ok_instr v_S v_C (CONST v_t v_c) (mk_functype [] [v_t])).
	by apply const.
Qed.

Lemma Step_pure__binop_trap_preserves : forall v_S v_C (v_t : valtype) v_c_1 v_c_2 v_binop v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_BINOP v_t v_binop)] v_func_type ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_BINOP v_t v_binop)] [(AI_TRAP )] ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_binop v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (AIs_ok_seq v_S v_C [] (AI_TRAP) tf1 tf2 tf1).
	- (* Empty *) apply admin_weakening_empty_both. apply AIs_ok_empty.
	- (* TRAP *) apply AI_ok_trap.
Qed.



Lemma Step_pure__testop_preserves : forall v_S v_C (v_t : valtype) v_c_1 (v_testop : testop_ v_t) (v_c : iN 32) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_TESTOP v_t v_testop)] v_func_type ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_TESTOP v_t v_testop)] [(AI_CONST I32 v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c)] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_testop v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply Testop_typing in H4_comp1; destruct H4_comp1 as [ts [H1 H2]]; subst.
	repeat rewrite -> app_assoc in H1_comp1. apply split_append_last in H1_comp1; destruct H1_comp1; subst.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (AI_CONST (I32) v_c) [] [I32] []). 
	- (* Empty *) apply AIs_ok_empty.
	- (* Const *) apply (AI_ok_instr v_S v_C (CONST (I32) v_c) (mk_functype [] [I32])).
		by apply const.
Qed.

Lemma Step_pure__relop_preserves : forall v_S v_C (v_t : valtype) v_c_1 v_c_2 (v_relop : relop_ v_t) (v_c : iN 32) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_RELOP v_t v_relop)] v_func_type ->
	Step_pure [(AI_CONST v_t v_c_1);(AI_CONST v_t v_c_2);(AI_RELOP v_t v_relop)] [(AI_CONST I32 v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST I32 v_c)] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_relop v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_single H4_comp1.
	apply AI_const_typing in H4_comp0.
	apply AI_const_typing in H4_comp.
	apply Relop_typing in H4_comp2; destruct H4_comp2 as [ts [H1 H2]].
	subst.
	rewrite split_cons in H1_comp0.
	repeat rewrite -> app_assoc in H1_comp0; apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H1.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (AI_CONST (I32) v_c) [] [I32] []).
	- (* Empty *) apply AIs_ok_empty.
	- (* Const *) apply (AI_ok_instr v_S v_C (CONST (I32) v_c) (mk_functype [] [I32])).
	by apply const.
Qed.

Lemma Step_pure__cvtop_val_preserves : forall v_S v_C (v_t_1 : valtype) v_c_1 (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)) v_c v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t_1 v_c_1);(AI_CVTOP v_t_2 v_t_1 v_cvtop)] v_func_type ->
	Step_pure [(AI_CONST v_t_1 v_c_1);(AI_CVTOP v_t_2 v_t_1 v_cvtop)] [(AI_CONST v_t_2 v_c)] ->
	Admin_instrs_ok v_S v_C [(AI_CONST v_t_2 v_c)] v_func_type.
Proof.
	move => v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_sx v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply Cvtop_typing in H4_comp1; destruct H4_comp1 as [ts [H1 H2]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (AIs_ok_seq v_S v_C [] (AI_CONST v_t_2 v_c) [] [v_t_2] []).
	- (* Empty *) apply AIs_ok_empty.
	- (* Const *) apply (AI_ok_instr v_S v_C (CONST v_t_2 v_c) (mk_functype [] [v_t_2])).
	by apply const.
Qed.

Lemma Step_pure__cvtop_trap_preserves : forall v_S v_C (v_t_1 : valtype) v_c_1 (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)) v_func_type,
	Admin_instrs_ok v_S v_C [(AI_CONST v_t_1 v_c_1);(AI_CVTOP v_t_2 v_t_1 v_cvtop)] v_func_type ->
	Step_pure [(AI_CONST v_t_1 v_c_1);(AI_CVTOP v_t_2 v_t_1 v_cvtop)] [(AI_TRAP )] ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	move => v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_sx v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (AIs_ok_seq v_S v_C [] (AI_TRAP) tf1 tf2 tf1).
	- (* Empty *) apply admin_weakening_empty_both. apply AIs_ok_empty.
	- (* TRAP *) apply AI_ok_trap.
Qed.

Lemma Step_pure__local_tee_preserves : forall v_S v_C (v_val : val) (v_x : idx) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(AI_LOCAL_TEE v_x)] v_func_type ->
	Step_pure [(v_val : admininstr);(AI_LOCAL_TEE v_x)] [(v_val : admininstr);(v_val : admininstr);(AI_LOCAL_SET v_x)] ->
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(v_val : admininstr);(AI_LOCAL_SET v_x)] v_func_type.
Proof.
	move => v_S v_C v_val v_x v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	induction v_val.
	apply AI_const_typing in H4_comp0.
	apply Local_tee_typing in H4_comp1; destruct H4_comp1 as [ts [t [H1 [H2 [H3 H4]]]]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	unfold fun_coec_val__admininstr.
	rewrite <- H0.
	apply (AIs_ok_seq v_S v_C [AI_CONST v_valtype v_val_; AI_CONST v_valtype v_val_] 
		(AI_LOCAL_SET v_x) [] [v_valtype] ([v_valtype] ++ [v_valtype])).
	apply (AIs_ok_seq v_S v_C [AI_CONST v_valtype v_val_] 
		(AI_CONST v_valtype v_val_) [] ([v_valtype] ++ [v_valtype]) [v_valtype]).
	apply (AIs_ok_seq v_S v_C [] 
	(AI_CONST v_valtype v_val_) [] [v_valtype] []).
	- (* Empty *) apply AIs_ok_empty.
	- (* Const 1 *) apply (AI_ok_instr v_S v_C (CONST v_valtype v_val_) (mk_functype [] [v_valtype])).
		apply const.
	- (* Const 2 *) apply admin_instr_weakening_empty_1. 
		apply (AI_ok_instr v_S v_C (CONST v_valtype v_val_) (mk_functype [] [v_valtype])).
		apply const.
	- (* Set *) apply admin_instr_weakening_empty_2. 
		apply (AI_ok_instr v_S v_C (LOCAL_SET v_x) (mk_functype [v_valtype] [])).
		apply local_set.
		move : H3 => /leP Hbool. auto. auto.
Qed.

Lemma Step_read__block_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) (v_n : n) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_BLOCK v_t v_instr)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(((v_t = None) /\ (v_n = 0)) \/ ((v_t <> None) /\ (v_n = 1))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_LABEL_ v_n [] (map fun_coec_instr__admininstr v_instr))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_t v_instr v_n v_func_type v_t1 lab ret HType HMinst HState H1 HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Block_typing in HType; destruct HType as [ts [? [? ?]]]; subst. simpl in H2.
	rewrite <- admin_instrs_ok_eq.
	apply admin_instr_weakening_empty_1.
	apply AI_ok_label with (v_t_1 := v_t).
	repeat split => //=.
	apply instrs_weakening_empty_both.
	Check instrs_empty.
	apply instrs_empty.
	apply AIs_ok_instrs with (v_S := v_S) in H2.
	apply H2.
	destruct H1; destruct H => //=; subst => //=.
	destruct v_t => //=.
Qed.

Lemma Step_read__loop_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_LOOP v_t v_instr)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_LABEL_ 0 [(LOOP v_t v_instr)] (map fun_coec_instr__admininstr v_instr))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_t v_instr v_func_type v_t1 lab ret HType HMinst H HValOK.
	destruct v_func_type as [ts1 ts2].
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

Lemma Step_read__call_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CALL v_x)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(v_x < (List.length (fun_funcaddr v_z)))%coq_nat ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CALL_ADDR (lookup_total (fun_funcaddr v_z) v_x))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_x v_func_type v_t1 lab ret HType HMinst H H1 HValOK.
	destruct v_func_type as [ts1 ts2].
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
    Externaddrs_ok v_S (EXTVAL_FUNC v_a) (EXT_FUNC (FUNC_TYPE v_f)).
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

Lemma Step_read__call_indirect_call_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_x : idx) (v_a : addr) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 (fun_nat__u32 v_i));(AI_CALL_INDIRECT v_x)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	Store_ok v_S ->
	v_z = mk_state v_S r_v_f ->
	(v_i < (List.length (REFS (fun_table v_z 0))))%coq_nat ->
	(v_a < (List.length (fun_funcinst v_z)))%coq_nat ->
	((lookup_total (REFS (fun_table v_z 0)) v_i) = (Some v_a)) ->
	((fun_type v_z v_x) = (FUNC_TYPE (lookup_total (fun_funcinst v_z) v_a))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CALL_ADDR v_a)] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_i v_x v_a v_func_type v_t1 lab ret HType HMinst HST H1 H2 H3 H4 H5 HValOK.
	destruct v_func_type as [ts1 ts2].
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
	eapply store_typed_exterval_types; eauto.
Qed.

Lemma Step_read__call_indirect_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : val_ I32) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 v_i);(AI_CALL_INDIRECT v_x)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(~(Step_read_before_call_indirect_trap (mk_config v_z [(AI_CONST I32 v_i);(AI_CALL_INDIRECT v_x)]))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_read__call_addr_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_val : (list val)) (v_k : nat) (v_a : addr) (v_n : n) (v_f : frame) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : resulttype) (v_mm : moduleinst) (v_func : func) (v_x : idx) (v_t : (list valtype)) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)(@app _ (map fun_coec_val__admininstr v_val) [(AI_CALL_ADDR v_a)]) v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	Store_ok v_S -> 
	Datatypes.length v_val = Datatypes.length v_t_1 -> 
	v_z = mk_state v_S r_v_f ->
	(v_a < (List.length (fun_funcinst v_z)))%coq_nat ->
	((lookup_total (fun_funcinst v_z) v_a) = {| FUNC_TYPE := (mk_functype v_t_1 v_t_2); FUNC_MODULE := v_mm; CODE := v_func |}) ->
	(v_n = fun_optionSize v_t_2) ->
	(v_func = (FUNC v_x (List.map (fun v_t => (LOCAL v_t)) (v_t)) v_instr)) ->
	(v_f = {| LOCALS := (@app _ v_val (List.map (fun v_t => (fun_default_ v_t)) (v_t))); F_MODULE := v_mm |}) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_FRAME_ v_n v_f [(AI_LABEL_ v_n [] (map fun_coec_instr__admininstr v_instr))])] v_func_type.
Admitted.
(* Proof.
	move => v_S r_v_f v_C v_z v_val v_k v_a v_n v_f v_instr v_t_1 v_t_2 v_mm v_func v_x v_t v_func_type v_t1 lab ret HType HMinst H1 H2 H3 H4 H5 H6 H7 H8 H9.
	destruct v_func_type as [ts1 ts2].
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

Lemma Step_read__local_get_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_LOCAL_GET v_x)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [((fun_local v_z v_x) : admininstr)] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_x v_func_type v_t1 lab ret HType HMinst H1 HValOK.
	destruct v_func_type as [ts1 ts2].
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

Lemma Step_read__global_get_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_GLOBAL_GET v_x)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [((VALUE (fun_global v_z v_x)) : admininstr)] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_x v_func_type v_t1 lab ret HType HMinst H HValOK.
	destruct v_func_type as [ts1 ts2].
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

Lemma Step_read__load_num_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memarg) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 (fun_nat__u32 v_i : val_ I32));(AI_LOAD v_t None v_mo)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(((v_i + (OFFSET v_mo)) + ((fun_size v_t) / 8)) > (List.length (BYTES (fun_mem v_z 0))))%coq_nat ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_read__load_num_val_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memarg) v_c v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 (fun_nat__u32 v_i : val_ I32));(AI_LOAD v_t None v_mo)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((fun_bytes_ v_t v_c) = (list_slice (BYTES (fun_mem v_z 0)) (v_i + (OFFSET v_mo)) ((fun_size v_t) / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CONST v_t v_c)] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_i v_t v_mo v_c v_func_type v_t1 lab ret HType HMinst HState H HValOK.
	destruct v_func_type as [ts1 ts2].
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

(*
Lemma Step_read__load_pack_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_valtype : valtype) (v_n : n) (v_sx : sx) (v_mo : memarg) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 (fun_nat__u32 v_i));(AI_LOAD v_valtype (Some (op__ INN_I32 (mk_sz v_n) v_sx)) v_mo)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(((v_i + (OFFSET v_mo)) + (v_n / 8)) > (List.length (BYTES (fun_mem v_z 0))))%coq_nat ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type.
	rewrite <- admin_instrs_ok_eq.
	apply AI_ok_trap.
Qed.

Lemma Step_read__load_pack_val_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_inn : inn) (v_n : n) (v_sx : sx) (v_mo : memarg) (v_c : iN 32) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_CONST I32 (v_i : val_));(AI_LOAD (valtype__INN v_inn) (Some ((packsize__ v_n), v_sx)) v_mo)] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	((fun_ibytes v_n v_c) = (list_slice (BYTES (fun_mem v_z 0)) (v_i + (OFFSET v_mo)) (v_n / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CONST (valtype__INN v_inn) (fun_ext v_n (fun_size (valtype__INN v_inn)) v_sx v_c))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_i v_inn v_n v_sx v_mo v_c v_func_type v_t1 lab ret HType HMinst HState H HValOK.
	destruct v_func_type as [ts1 ts2].
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

Lemma Step_read__memory_size_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_n : n) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab)[(AI_MEMORY_SIZE )] v_func_type ->
	Module_instance_ok v_S (F_MODULE r_v_f) v_C  ->
	v_z = mk_state v_S r_v_f ->
	(((v_n * 64) * (fun_Ki )) = (List.length (BYTES (fun_mem v_z 0)))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) [(AI_CONST I32 (fun_nat__u32 v_n : val_ I32))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_n v_func_type v_t1 lab ret HType HMinst HState HLength HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in HType.
	apply Memory_size_typing in HType; destruct HType as [v_mt [? [? ?]]].
	subst.
	apply admin_instr_weakening_empty_1.
	eapply (AI_ok_instr v_S _ (CONST (I32) (fun_nat__u32 v_n)) (mk_functype [] [(I32)])).
	apply const.
Qed.

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
	  destruct v__.
	  apply mk_Table_extension => //.
	- apply IHt.
Qed.

Lemma mem_extension_same: forall m,
	Forall2 (fun v s => Mem_extension v s) m m.
Proof.
	move => m.
	induction m => //.
	apply Forall2_cons_iff. split.
	- destruct a as [type bytes]. destruct type.
	  destruct v__.
	  apply mk_Mem_extension => //.
	- apply IHm.
Qed.

Lemma global_extension_same: forall s g v_globaltype,
	Forall2
	(fun (v_globalinst : globalinst) (v_globaltype : globaltype) => Global_instance_ok s v_globalinst v_globaltype) g v_globaltype ->
	Forall2 (fun v s => Global_extension v s) g g.
Admitted.
(* Proof.
	move => s g v_globaltype HGlobalInstOk.
	generalize dependent v_globaltype.
	induction g => //; move => v_globaltype HGlobalInstOk.
	apply Forall2_cons_iff. split.
	-
		apply Forall2_length in HGlobalInstOk as ?. 
		destruct v_globaltype => //=.
		inversion HGlobalInstOk.
		inversion H3; decomp; subst.
		inversion H11; subst.
		apply Global_extension__. right => //.
	- destruct v_globaltype; inversion HGlobalInstOk. eapply IHg; eauto. 
Qed. *)

Lemma store_extension_same: forall s,
	Store_ok s ->
    Store_extension s s.
Admitted.
(* Proof.
  move => s HST. 
  inversion HST; decomp.
  apply (Store_extension__ s s (FUNCS s) (TABLES s) (MEMS s) (GLOBALS s) (FUNCS s) [] (TABLES s) [] (MEMS s) [] (GLOBALS s) []).
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
Qed.

Lemma func_agree_extension: forall v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_functype,
	Externaddrs_ok v_S (EXTVAL_FUNC v_funcaddr) (EXT_FUNC v_functype) ->
	length (FUNCS v_S) = length v_funcinst_1' ->
	FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2)%list -> 
    Forall2 (fun v s => Func_extension v s) (FUNCS v_S) v_funcinst_1' ->
    Externaddrs_ok v_S' (EXTVAL_FUNC v_funcaddr) (EXT_FUNC v_functype).
Admitted.
(* Proof.
	move => v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_functype HOk HLength HApp Hext.
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
    Externaddrs_ok v_S (EXTVAL_TABLE v_tableaddr) (EXT_TABLE v_tabletype) ->
	length (TABLES v_S) = length v_tableinst_1' ->
	TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2) -> 
	Forall2 (fun v s => Table_extension v s) (TABLES v_S) v_tableinst_1' ->
    Externaddrs_ok v_S' (EXTVAL_TABLE v_tableaddr) (EXT_TABLE v_tabletype).
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
    Externaddrs_ok v_S (EXTVAL_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype) ->
	length (GLOBALS v_S) = length v_globalinst_1' ->
	GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2) -> 
	Forall2 (fun v s => Global_extension v s) (GLOBALS v_S) v_globalinst_1' ->
    Externaddrs_ok v_S' (EXTVAL_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype).
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
    Externaddrs_ok v_S (EXTVAL_MEM v_memaddr) (EXT_MEM v_memtype) ->
	length (MEMS v_S) = length v_meminst_1' ->
	MEMS v_S' = (v_meminst_1' ++ v_meminst_2) -> 
	Forall2 (fun v s => Mem_extension v s) (MEMS v_S) v_meminst_1' ->
    Externaddrs_ok v_S' (EXTVAL_MEM v_memaddr) (EXT_MEM v_memtype).
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
    Forall2 (fun v s => Externaddrs_ok v_S (EXTVAL_FUNC v) (EXT_FUNC s)) v_funcaddrs tcf ->
	length (FUNCS v_S) = length v_funcinst_1' ->
	FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2)%list -> 
	Forall2 (fun v s => Func_extension v s) (FUNCS v_S) v_funcinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTVAL_FUNC v) (EXT_FUNC s)) v_funcaddrs tcf.
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
    Forall2 (fun v s => Externaddrs_ok v_S (EXTVAL_TABLE v) (EXT_TABLE s)) v_tableaddrs tcf ->
	length (TABLES v_S) = length v_tableinst_1' ->
	TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2)%list -> 
	Forall2 (fun v s => Table_extension v s) (TABLES v_S) v_tableinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTVAL_TABLE v) (EXT_TABLE s)) v_tableaddrs tcf.
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
    Forall2 (fun v s => Externaddrs_ok v_S (EXTVAL_GLOBAL v) (EXT_GLOBAL s)) v_globaladdrs tcf ->
	length (GLOBALS v_S) = length v_globalinst_1' ->
	GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2)%list -> 
	Forall2 (fun v s => Global_extension v s) (GLOBALS v_S) v_globalinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTVAL_GLOBAL v) (EXT_GLOBAL s)) v_globaladdrs tcf.
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
	Forall2 (fun v s => Externaddrs_ok v_S (EXTVAL_MEM v) (EXT_MEM s)) v_memaddrs tcf ->
	length (MEMS v_S) = length v_meminst_1' ->
	MEMS v_S' = (v_meminst_1' ++ v_meminst_2)%list -> 
	Forall2 (fun v s => Mem_extension v s) (MEMS v_S) v_meminst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTVAL_MEM v) (EXT_MEM s)) v_memaddrs tcf.
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
Admitted.
(* Proof.
	move => v_S v_S' v_i v_C HStoreExtension HMIT.
	inversion HStoreExtension. 
	inversion HMIT; decomp.
	subst.
	apply Module_instance_ok__; repeat split => //=.
	- eapply func_extension_C; eauto.
	- eapply table_extension_C; eauto.
	- eapply global_extension_C ; eauto.
	- eapply mem_extension_C; eauto.
	- eapply ext_extension_C; eauto.
Qed. *)

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
	eapply Store_ok__OK with (v_funcinst := v_funcinst) (v_functype := v_functype)
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
Qed. *)

Lemma t_preservation_vs_type: forall s f ais s' f' ais' C C' v_t1 lab ret t1s t2s,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Store_ok s -> 
	Store_ok s' ->
    Module_instance_ok s (F_MODULE f) C ->
    Module_instance_ok s' (F_MODULE f') C' ->
	v_t1 = (C_LOCALS (upd_label (upd_local_return C (v_t1 ++ (C_LOCALS C)) ret) lab)) -> 
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS f) ->
    Admin_instrs_ok s (upd_label (upd_local_return C (v_t1 ++ (C_LOCALS C)) ret) lab) ais (mk_functype t1s t2s) ->
    Forall2 (fun v_t v_val0 => Val_ok v_val0 v_t) v_t1 (LOCALS f') 
	/\ length v_t1 = length (LOCALS f').
Admitted.
(* Proof.
	move => s f ais s' f' ais' C C' v_t1 
		lab ret t1s t2s HReduce HStore HStore' HMInst HMInst' HValTypeEq HValOK HType.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent t2s. generalize dependent t1s.
	generalize dependent lab. generalize dependent ais'. generalize dependent ais.
	induction HReduce; try intros; try (induction v_z; subst); 
	try (apply config_same in Heqc1; apply config_same in Heqc2; 
		destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; 
		destruct Heqc2 as [Hafter1 [Hafter2 Hafter3]]; split; subst => //; try apply Forall2_length in HValOK as ? => //).
	- (* Label Context *)
		injection Heqc1 as ?.
		injection Heqc2 as ?; subst.
		apply_composition_typing_single HType.
		apply Label_typing in H4_comp; destruct H4_comp as [ts [ts2' [? [? [? ?]]]]]; subst.
		rewrite upd_label_overwrite in H2; simpl in H2.
		simpl in HValTypeEq.
		eapply IHHReduce; eauto.
	- (* Local Set *)
		rewrite -> Forall2_Val_ok_is_same_as_map in HValOK; rewrite -> Forall2_Val_ok_is_same_as_map.
		induction v_val.
		apply_composition_typing_and_single HType.
		apply AI_const_typing in  H4_comp0.
		apply_composition_typing_single H4_comp.
		apply Set_local_typing in H4_comp1; destruct H4_comp1 as [t [HLookup [H0' H1']]].
		subst.
		repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
		replace (C_LOCALS C) with ([::]: list valtype) in *; last by symmetry; eapply inst_t_context_local_empty; eauto.
		rewrite -> cats0 in *.
		simpl in H1'; simpl in H0. rewrite -> List.map_length in H1'. 
		apply list_update_map with (f := typeof) (val := (VAL_CONST v_valtype v_val_)) in H1' as HUpdate.
		rewrite HUpdate.
		rewrite list_update_same_unchanged => //=; try rewrite List.map_length => //=.
		simpl. by rewrite list_update_length.
Qed. *)

Lemma store_extension_reduce: forall s f ais s' f' ais' C tf loc lab ret,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Module_instance_ok s (F_MODULE f) C ->
    Admin_instrs_ok s (upd_label (upd_local_return C loc ret) lab) ais tf ->
    Store_ok s ->
    Store_extension s s' /\ Store_ok s'.
Admitted.
(* Proof.
	move => s f ais s' f' ais' C tf loc lab ret HReduce HIT HType HStore.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent C. generalize dependent tf.
  	generalize dependent loc. generalize dependent lab. generalize dependent ret.
	generalize dependent ais. generalize dependent ais'. 
	generalize dependent f. generalize dependent f'.
	induction HReduce; try move => f' f ais' Heqc2 ais Heqc1 ret lab loc tf C HIT HType HST; try intros; destruct tf;
	try (destruct v_z; 
	apply config_same in Heqc1; apply config_same in Heqc2; 
	destruct Heqc1; destruct Heqc2;
	subst; try (split => //; eapply store_extension_same; eauto)).
	- (* Label Context *) 
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H in HType.
		apply_composition_typing_single HType.
		apply Label_typing in H4_comp; destruct H4_comp as [ts [ts2' [? [? [? ?]]]]]; subst.
		rewrite upd_label_overwrite in H6; simpl in H6.
		eapply IHHReduce; eauto.
	- (* Label Frame *)
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H0 in HType.
		apply_composition_typing_single HType.
		apply Frame_typing in H4_comp. destruct H4_comp as [ts [? [? ?]]].
		inversion H6. destruct H8.
		inversion H8. destruct H15 as [? [? ?]]; subst.
		simpl in H14.
		rewrite <- upd_return_is_same_as_append in H14; simpl in H14.
		rewrite <- upd_local_is_same_as_append in H14; simpl in H14.
		rewrite -> _append_option_none_left in H14.
		apply upd_label_unchanged_typing in H14.
		eapply IHHReduce; eauto.
	- (* Global Set *) 
		destruct H2; destruct H0; subst.
		apply_composition_typing_and_single HType.
		destruct v_val.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Set_global_typing in H4_comp; destruct H4_comp as [t [? [?  ?]]].
		remember  (s <| GLOBALS :=
			list_update_func (GLOBALS s)
		  	(lookup_total (MODULE_GLOBALS (F_MODULE f)) v_x)
		  	[eta set VALUE (fun=> VAL_CONST v_valtype v_val_)] |>) as s'.
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
Admitted.
(* Proof.
	move => s f ais s' f' ais' HReduce.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent ais. generalize dependent ais'.
	induction HReduce; try intros; try (induction v_z); try induction v_z'; try (apply config_same in Heqc1;
	apply config_same in Heqc2; destruct Heqc1 as [? [? ?]];
	destruct Heqc2 as [? [? ?]]; subst => //).
	eapply IHHReduce; eauto.
Qed. *)

Theorem t_pure_preservation: forall v_s v_minst v_ais v_ais' v_C loc lab ret tf,
    Module_instance_ok v_s v_minst v_C ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C loc ret) lab) v_ais tf ->
    Step_pure v_ais v_ais' ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C loc ret) lab) v_ais' tf.
Proof.
	move => v_s v_minst v_ais v_ais' v_C loc lab ret tf HInstType HType HReduce.
	inversion HReduce; subst.
	- eapply Step_pure__unreachable_preserves; eauto.
	- eapply Step_pure__nop_preserves; eauto.
	- eapply Step_pure__drop_preserves; eauto.
	- eapply Step_pure__select_true_preserves; eauto.
	- eapply Step_pure__select_false_preserves; eauto.
	- eapply Step_pure__if_true_preserves; eauto.
	- eapply Step_pure__if_false_preserves; eauto.
	- eapply Step_pure__label_vals_preserves; eauto.
Admitted. (*
	- eapply Step_pure__br_zero_preserves; eauto.
	- eapply Step_pure__br_succ_preserves; eauto.
	- eapply Step_pure__br_if_true_preserves; eauto.
	- eapply Step_pure__br_if_false_preserves; eauto.
	- eapply Step_pure__br_table_lt_preserves; eauto.
	- eapply Step_pure__br_table_ge_preserves; eauto.
	- eapply Step_pure__frame_vals_preserves; eauto.
	- eapply Step_pure__return_frame_preserves; eauto.
	- eapply Step_pure__return_label_preserves; eauto.
	- eapply Step_pure__trap_vals_preserves; eauto.
	- eapply Step_pure__trap_label_preserves; eauto.
	- eapply Step_pure__trap_frame_preserves; eauto.
	- eapply Step_pure__unop_val_preserves; eauto.
	- eapply Step_pure__unop_trap_preserves; eauto.
	- eapply Step_pure__binop_val_preserves; eauto.
	- eapply Step_pure__binop_trap_preserves; eauto.
	- eapply Step_pure__testop_preserves; eauto.
	- eapply Step_pure__relop_preserves; eauto.
	- eapply Step_pure__cvtop_val_preserves; eauto.
	- eapply Step_pure__cvtop_trap_preserves; eauto.
	- eapply Step_pure__local_tee_preserves; eauto.
Qed. *)

Lemma t_read_preservation: forall v_s v_f v_ais v_ais' v_C v_t1 t1s t2s lab ret,
    Step_read (mk_config (mk_state v_s v_f) v_ais) v_ais' ->
    Store_ok v_s ->
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS v_f) ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) v_ais (mk_functype t1s t2s) ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) v_ais' (mk_functype t1s t2s).
Proof.
	move => v_s v_f v_ais v_ais' v_C v_t1 t1s t2s lab ret HReduce HST.
	move: v_C ret lab t1s t2s.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	induction HReduce; move => C ret lab tx ty HIT1 HValOK HType; decomp; destruct v_z; try eauto;
	try (apply config_same in Heqc1; destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; subst => //).
	- eapply Step_read__block_preserves; eauto.
	- Admitted. (* eapply Step_read__loop_preserves; eauto.
	- eapply Step_read__call_preserves; eauto.
	- eapply Step_read__call_indirect_call_preserves; eauto.
	- eapply Step_read__call_indirect_trap_preserves; eauto.
	- eapply Step_read__call_addr_preserves; eauto.
	- eapply Step_read__local_get_preserves; eauto.
	- eapply Step_read__global_get_preserves; eauto.
	- eapply Step_read__load_num_trap_preserves; eauto.
	- eapply Step_read__load_num_val_preserves; eauto.
	- eapply Step_read__load_pack_trap_preserves; eauto.
	- eapply Step_read__load_pack_val_preserves; eauto.
	- eapply Step_read__memory_size_preserves; eauto.
Qed. *)

Lemma t_preservation_type: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_t1 t1s t2s lab ret,
    Step (mk_config (mk_state v_s v_f) v_ais) (mk_config (mk_state v_s' v_f') v_ais') ->
    Store_ok v_s ->
    Store_ok v_s' ->
	Store_extension v_s v_s' -> 
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
    Module_instance_ok v_s' (F_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (LOCALS v_f) ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) v_ais (mk_functype t1s t2s) ->
    Admin_instrs_ok v_s' (upd_label (upd_local_return v_C (v_t1 ++ C_LOCALS v_C) ret) lab) v_ais' (mk_functype t1s t2s).
Admitted.
(* Proof.
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

(* Ultimate goal of project *)				
Theorem t_preservation: forall c1 ts c2,
	Step c1 c2 ->
	Config_ok c1 ts ->
	Config_ok c2 ts.
Admitted.
(* Proof.
	move => c1 ts c2 HReduce HType.
	destruct c1; destruct v_state as [store1 frame1].
	destruct c2; destruct v_state as [store2 frame2].
	inversion HType; destruct H3.
	inversion H4; destruct H5.
	rewrite <- upd_return_is_same_as_append in H11.
	inversion H5. destruct H12 as [H0' [H1' H2']].
	rewrite <- upd_local_is_same_as_append in H15.
	subst.
	rewrite <- upd_local_return_is_same_as_append in H11.
	apply upd_label_unchanged_typing in H11.
	assert (Store_extension store1 store2 /\ Store_ok store2).
	{
		apply (store_extension_reduce 
			store1  
			{|LOCALS := v_val;F_MODULE := v_moduleinst|} 
			v__ store2 frame2 v__0 v_C0 (mk_functype [::] ts) 
			(_append v_t1 (C_LOCALS v_C0)) 
			(C_LABELS (upd_local_return v_C0 (_append v_t1 (C_LOCALS v_C0)) (_append (option_map [eta Some] None) (C_RETURN v_C0))))
			(_append (Some None) (C_RETURN v_C0))) => //.
	}
	destruct H.
	apply reduce_inst_unchanged in HReduce as HModuleInst.
	destruct frame2 as [locals2 module2].
	simpl in HModuleInst.
	remember {|LOCALS := v_val;F_MODULE := v_moduleinst|} as f.
	assert (Module_instance_ok store2 v_moduleinst v_C0). { apply (module_inst_typing_extension store1); eauto. }
	apply Config_ok__; split => //=.
	eapply Thread_ok__; split => //=.
	rewrite <- HModuleInst.
	eapply (Frame_ok__ store2 locals2 v_moduleinst v_C0 v_t1); eauto.
	apply (t_preservation_vs_type) with (v_t1 := v_t1) (C := v_C0) (C' := v_C0) 
		(lab:= (C_LABELS (upd_local_return v_C0 (_append v_t1 (C_LOCALS v_C0)) (_append (option_map [eta Some] None) (C_RETURN v_C0))))) 
		(ret:= (_append (Some None) (C_RETURN v_C0))) (t1s := []) (t2s := ts) in HReduce as H10; try destruct H10; try apply Forall2_length in H10; repeat split => //.
	- apply H3.
	- apply H0.
	- by rewrite Heqf.
	- by rewrite <- HModuleInst.
	- simpl. apply inst_t_context_local_empty in H1. rewrite H1. by rewrite -> app_nil_r.
	- by rewrite Heqf.
	- apply H11.
	(* Actual Typing proof *)
	rewrite <- upd_return_is_same_as_append; simpl.
	rewrite <- upd_local_is_same_as_append; simpl.
	fold_upd_context.
	rewrite -> _append_option_none_left.
	rewrite upd_label_unchanged_typing.
	eapply t_preservation_type; eauto; try rewrite -> Heqf; eauto.
Qed. *)