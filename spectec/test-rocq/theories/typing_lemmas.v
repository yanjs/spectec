From Coq Require Import String List Unicode.Utf8 NArith Arith.
Require Import Stdlib.Program.Equality.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

Definition upd_label C labs :=
	C <| C_LABELS := labs |>.

Definition upd_local C locs :=
	C <| C_LOCALS := locs |>.

Definition upd_return C ret :=
	C <| C_RETURN := ret |>.

Definition upd_local_return C loc ret :=
	upd_return (upd_local C loc) ret. 

Definition upd_label_local_return C loc lab ret := 
	upd_label (upd_local_return C loc ret) lab.

Definition upd_local_label_return C loc lab ret := 
	upd_return (upd_label (upd_local C loc) lab) ret.

Ltac fold_upd_context :=
	lazymatch goal with
	| |- context [upd_local (upd_return ?C ?ret) ?loc] =>
		replace (upd_local (upd_return C ret) loc) with
			(upd_local_return C ret loc); try by destruct C
	| |- context [upd_return (upd_local ?C ?ret) ?loc] =>
		replace (upd_return (upd_local C ret) loc) with
			(upd_local_return C ret loc); try by destruct C
	end.
	  
Lemma upd_label_overwrite: forall C l1 l2,
	upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Lemma upd_label_is_same_as_append: forall v_C lab,
	upd_label v_C (_append lab (C_LABELS v_C)) = _append {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := lab; C_RETURN := None |} v_C.
Proof.
	move => v_C lab. reflexivity.
Qed.

Lemma upd_local_is_same_as_append: forall v_C loc,
	upd_local v_C (_append loc (C_LOCALS v_C))  = _append {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := loc; C_LABELS := []; C_RETURN := None |} v_C.
Proof.
	move => v_C loc. reflexivity.
Qed.

Lemma upd_local_return_is_same_as_append: forall v_C loc ret,
	upd_local_return v_C (_append loc (C_LOCALS v_C)) (_append ret (C_RETURN v_C)) 
	= upd_return (upd_local v_C (_append loc (C_LOCALS v_C))) (_append ret (C_RETURN ((upd_local v_C (_append loc (C_LOCALS v_C)))))).
Proof. reflexivity. Qed.


Lemma upd_return_is_same_as_append: forall v_C ret,
	upd_return v_C (_append ret (C_RETURN v_C)) = _append {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := ret |} v_C.
Proof.
	move => v_C ret. reflexivity.
Qed.

Lemma upd_label_unchanged: forall C lab,
    C_LABELS C = lab ->
    upd_label C lab = C.
Proof.
	move => C lab HLab.
	rewrite -HLab. unfold upd_label. by destruct C.
Qed.

Lemma upd_label_unchanged_typing: forall v_S v_C v_admininstrs v_func_type,
    Admin_instrs_ok v_S v_C v_admininstrs v_func_type <->
    Admin_instrs_ok v_S (upd_label v_C (C_LABELS v_C)) v_admininstrs v_func_type.
Proof.
	move => s C es tf.
	split.
	- move => HType.
		by rewrite upd_label_unchanged.
	- move => HType.
		simpl in HType.
		remember (C_LABELS C) as lab.
		symmetry in Heqlab.
		apply upd_label_unchanged in Heqlab.
		rewrite <- Heqlab => //=. 
Qed.

Definition typeof (v_val : val): valtype :=
	match v_val with
		| VAL_CONST t _ => t
	end.
	
Lemma typeof_default_inverse: forall (v_t : list valtype),
	List.map typeof (List.map [eta fun_default_] v_t) = v_t.
Proof.
	move => v_t.
	induction v_t => //=.
	f_equal.
	destruct a; destruct v_t => //=.
	apply IHv_t.
Qed.

Lemma Forall2_Val_ok_is_same_as_map: forall v_t1 v_local_vals,
	Forall2 (fun v s => Val_ok s v) v_t1 v_local_vals <->
	List.map typeof v_local_vals = v_t1.
Proof.
	split.
	- move => H.
		generalize dependent v_local_vals.
		induction v_t1; move => v_local_vals H; destruct v_local_vals => //=; inversion H.
		subst. f_equal. 
		- inversion H3 => //=.
		- by apply IHv_t1.
	- move => H.
		generalize dependent v_local_vals.
		induction v_t1; move => v_local_vals H; destruct v_local_vals => //=.
		simpl in H. inversion H.
		apply Forall2_cons. 
		- induction v. apply mk_Val_ok.
		- rewrite H2. by apply IHv_t1.
Qed.

Lemma instrs_empty: forall C t1 t2,
	Instrs_ok C [] (mk_functype t1 t2) ->
	t1 = t2.
Proof.
	move => C t t2 H. gen_ind_subst H => //.
	- (* Seq *) symmetry in Enil. apply app_cons_not_nil in Enil. exfalso. apply Enil. 
	- (* Frame *) f_equal. by eapply IHInstrs_ok.
Qed. 

Lemma admin_empty: forall v_S C t1 t2,
	Admin_instrs_ok v_S C [] (mk_functype t1 t2) ->
	t1 = t2.
Proof.
	move => v_S C t t2 H. gen_ind_subst H => //.
		- (* Seq *) symmetry in Enil. apply app_cons_not_nil in Enil. exfalso. apply Enil. 
		- (* Frame *) f_equal. by eapply IHAdmin_instrs_ok.
		- (* Instrs *) apply (instrs_empty C). apply map_eq_nil in Enil. subst. apply H.
Qed. 

Lemma val_is_same_as_admin_const: forall v_S v_C (v : val) ts,
	Admin_instr_ok v_S v_C (v : admininstr) ts ->
	exists v_valtype v_val_, Admin_instr_ok v_S v_C (AI_CONST v_valtype v_val_) ts.
Proof. 
	move => v_S v_C val ts HType.
	induction val.
	exists v_valtype, v_val_. done.
Qed.

Lemma admin_weakening_empty_both: forall v_S v_C v_ais ts,
    Admin_instrs_ok v_S v_C v_ais (mk_functype [::] [::]) ->
    Admin_instrs_ok v_S v_C v_ais (mk_functype ts ts).
Proof.
  move => v_S v_C v_ais ts HType.
  assert (Admin_instrs_ok v_S v_C v_ais (mk_functype (ts ++ [::]) (ts ++ [::]))); first by apply AIs_ok_frame.
  by rewrite cats0 in H.
Qed.

Lemma instrs_weakening_empty_both: forall v_C v_ais ts,
    Instrs_ok v_C v_ais (mk_functype [::] [::]) ->
    Instrs_ok v_C v_ais (mk_functype ts ts).
Proof.
  move => v_C v_ais ts HType.
  assert (Instrs_ok v_C v_ais (mk_functype (ts ++ [::]) (ts ++ [::]))); first by apply instrs_frame.
  by rewrite cats0 in H.
Qed.

Lemma admin_instrs_weakening_empty_1: forall v_S v_C instrs ts t2s,
    Admin_instrs_ok v_S v_C instrs (mk_functype [::] t2s) ->
    Admin_instrs_ok v_S v_C instrs (mk_functype ts (ts ++ t2s)).
Proof.
  move => v_S v_C instrs ts t2s HType.
  assert (Admin_instrs_ok v_S v_C instrs (mk_functype (ts ++ [::]) (ts ++ t2s))); first by apply AIs_ok_frame.
  by rewrite cats0 in H.
Qed.

Lemma instrs_weakening_empty_1: forall v_C instrs ts t2s,
    Instrs_ok v_C instrs (mk_functype [::] t2s) ->
    Instrs_ok v_C instrs (mk_functype ts (ts ++ t2s)).
Proof.
  move => v_C instrs ts t2s HType.
  assert (Instrs_ok v_C instrs (mk_functype (ts ++ [::]) (ts ++ t2s))); first by apply instrs_frame.
  by rewrite cats0 in H.
Qed.

Lemma admin_instr_weakening_empty_1: forall v_S v_C instr ts t2s,
    Admin_instr_ok v_S v_C instr (mk_functype [::] t2s) ->
    Admin_instr_ok v_S v_C instr (mk_functype ts (ts ++ t2s)).
Proof.
  move => v_S v_C instr ts t2s HType.
  assert (Admin_instr_ok v_S v_C instr (mk_functype (ts ++ [::]) (ts ++ t2s))); first by apply AI_ok_weakening.
  by rewrite cats0 in H.
Qed.

Lemma admin_instr_weakening_empty_2: forall v_S v_C instr ts t1s,
    Admin_instr_ok v_S v_C instr (mk_functype t1s []) ->
    Admin_instr_ok v_S v_C instr (mk_functype (ts ++ t1s) (ts)).
Proof.
  move => v_S v_C instr ts t1s HType.
  assert (Admin_instr_ok v_S v_C instr (mk_functype (ts ++ t1s) (ts ++ []))); first by apply AI_ok_weakening.
  by rewrite cats0 in H.
Qed.

Lemma composition_typing_single: forall v_C v_ais v_ai t1s t2s,
   	Instrs_ok v_C (@app _ v_ais [v_ai]) (mk_functype t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = @app _ ts t1s' /\
                             t2s = @app _ ts t2s' /\
                             Instrs_ok v_C v_ais (mk_functype t1s' t3s) /\
                             Instr_ok v_C v_ai (mk_functype t3s t2s').
Proof.
	move => v_C v_ais v_ai t1s t2s HType. 
	gen_ind_subst HType => //.
		+ (* Empty *) apply empty_append in H1; destruct H1. discriminate.
		+ (* Seq *) apply split_append_last in Eapp; destruct Eapp; subst.
			by exists [], t1s, t2s, v_t_2.
		+ (* Frame *) edestruct IHHType; eauto.
			destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
			exists (@app _ v_t x), t1s', t2s', t3s'.
			by repeat split => //=; rewrite <- app_assoc; reflexivity.
Qed.

Lemma admin_composition_typing_single: forall v_S v_C v_ais v_ai t1s t2s,
    Admin_instrs_ok v_S v_C (@app _ v_ais [v_ai]) (mk_functype t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = @app _ ts t1s' /\
                             t2s = @app _ ts t2s' /\
                             Admin_instrs_ok v_S v_C v_ais (mk_functype t1s' t3s) /\
                             Admin_instr_ok v_S v_C v_ai (mk_functype t3s t2s').
Proof.
	move => v_S v_C v_ais v_ai t1s t2s HType.
	gen_ind_subst HType.
	    + (* Empty *) apply empty_append in H2; destruct H2. discriminate.
		+ (* Seq *) apply split_append_last in H3; destruct H3; subst.
			by exists [], t1s, t2s, v_t_2.
		+ (* Frame *) edestruct IHHType; eauto.
			destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
			exists (@app _ v_t x), t1s', t2s', t3s'.
			by repeat split => //=; rewrite <- app_assoc; reflexivity.
		+ (* Instrs *) apply map_eq_app in H3; destruct H3 as [l1 [l2 [H4 [H5 H6]]]]. 
			apply map_eq_cons in H6; destruct H6 as [a [t1 [H7 [H8 H9]]]].
			apply map_eq_nil in H9.
			subst. apply composition_typing_single in H; destruct H as [ts [t1s' [t2s' [t3s [H1 [H2 [H3 H4]]]]]]].
			exists ts, t1s', t2s', t3s. repeat split => //.
			eapply AIs_ok_instrs; eauto.
			eapply AI_ok_instr; eauto.
Qed.

Ltac apply_instrs_composition_typing_single H := 
	let ts1 := fresh "ts1_comp" in
    let ts2 := fresh "ts2_comp" in
    let ts3 := fresh "ts3_comp" in
    let ts4 := fresh "ts4_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    let H3 := fresh "H3_comp" in
    let H4 := fresh "H4_comp" in
	rewrite -> app_left_single_nil in H;
    apply composition_typing_single in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]];
	try apply instrs_empty in H3.

Ltac apply_composition_typing_single H := 
	let ts1 := fresh "ts1_comp" in
    let ts2 := fresh "ts2_comp" in
    let ts3 := fresh "ts3_comp" in
    let ts4 := fresh "ts4_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    let H3 := fresh "H3_comp" in
    let H4 := fresh "H4_comp" in
	rewrite -> app_left_single_nil in H;
    apply admin_composition_typing_single in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]];
	try apply admin_empty in H3.
	
Lemma admin_composition_typing: forall v_S v_C v_ais1 v_ais2 t1s t2s,
	Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (mk_functype t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             Admin_instrs_ok v_S v_C v_ais1 (mk_functype t1s' t3s) /\
                             Admin_instrs_ok v_S v_C v_ais2 (mk_functype t3s t2s').
Admitted.
(* Proof.
	move => v_S v_C v_ais1 v_ais2.
	remember (rev v_ais2) as v_ais2'.
	assert (v_ais2 = rev v_ais2'); first by (rewrite Heqv_ais2'; symmetry; apply revK).
	generalize dependent v_ais1.
	clear Heqv_ais2'. subst.
	induction v_ais2' => //=; move => v_ais1 t1s t2s HType.
	- unfold rev in HType; simpl in HType. subst.
	  rewrite cats0 in HType.
	  exists [::], t1s, t2s, t2s.
	  repeat split => //=.
	  apply admin_weakening_empty_both.
	  by apply AIs_ok_empty.
	- rewrite rev_cons in HType.
	  rewrite -cats1 in HType. subst.
	  rewrite catA in HType.
	  apply admin_composition_typing_single in HType.
	  destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
	  apply IHv_ais2' in H3.
	  destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
	  exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
	  repeat split => //.
	  + by apply AIs_ok_frame.
	  + rewrite rev_cons. rewrite -cats1.
		eapply AIs_ok_seq; split; eauto.
		by apply AIs_ok_frame.
Qed. *)

Ltac apply_composition_typing_and_single H :=
	let ts1 := fresh "ts1_comp" in
    let ts2 := fresh "ts2_comp" in
    let ts3 := fresh "ts3_comp" in
    let ts4 := fresh "ts4_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    let H3 := fresh "H3_comp" in
    let H4 := fresh "H4_comp" in
	try rewrite -cat1s in H; subst;
    apply admin_composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]];
	apply_composition_typing_single H3.
	
Ltac apply_composition_typing H :=
	let ts1 := fresh "ts1_comp" in
	let ts2 := fresh "ts2_comp" in
	let ts3 := fresh "ts3_comp" in
	let ts4 := fresh "ts4_comp" in
	let H1 := fresh "H1_comp" in
	let H2 := fresh "H2_comp" in
	let H3 := fresh "H3_comp" in
	let H4 := fresh "H4_comp" in
	try rewrite -cat1s in H; subst;
	apply admin_composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]].

Lemma admin_instrs_ok_eq: forall v_S v_C v_ai tf,
	Admin_instr_ok v_S v_C v_ai tf <-> 
	Admin_instrs_ok v_S v_C [v_ai] tf.
Proof.
	split; move => H; destruct tf as [ts1 ts2].
	- (* -> *)
		assert (Admin_instrs_ok v_S v_C [] (mk_functype [] [])). { apply AIs_ok_empty. }
		apply admin_weakening_empty_both with (ts := ts1) in H0.
		apply (AIs_ok_seq v_S v_C [] v_ai ts1 ts2 ts1); eauto.
	- (* <- *) 
		apply_composition_typing_single H; subst.
		apply AI_ok_weakening. apply H4_comp.
Qed.

Lemma admin_composition': forall v_S v_C v_ais1 v_ais2 t1s t2s t3s,
	Admin_instrs_ok v_S v_C v_ais1 (mk_functype t1s t2s) ->
	Admin_instrs_ok v_S v_C v_ais2 (mk_functype t2s t3s) ->
	Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (mk_functype t1s t3s).
Admitted.
(* Proof.
	move => v_S v_C v_ais1 v_ais2.
	move: v_ais1.
	induction v_ais2 using List.rev_ind; move => v_ais1 t1s t2s t3s HType1 HType2.
		- apply admin_empty in HType2; by rewrite cats0; subst.
		- apply_composition_typing_single HType2.
	subst.
	rewrite catA. eapply AIs_ok_seq; split.
	eapply IHv_ais2; eauto.
	apply AIs_ok_frame with (v_t := ts1_comp) in H3_comp.
	apply H3_comp.
	apply AI_ok_weakening; eauto.
Qed. *)

Lemma AI_const_typing: forall v_S v_C v_t v_v t1s t2s,
    Admin_instr_ok v_S v_C (AI_CONST v_t v_v) (mk_functype t1s t2s) ->
    t2s = @app _ t1s [v_t].
Admitted.
(* Anomaly "File "tactics/tactics.ml", line 2172, characters 16-22: Assertion failed."
Please report at http://coq.inria.fr/bugs/.
Proof.
  	move => v_S v_C v_t v_val t1s t2s HType.
	gen_ind_subst HType.
		- (* Const *) inversion H; subst; try discriminate. injection H3 as H1. rewrite -> cat0s. f_equal. apply H1.
		- (* Weakening *) rewrite <- app_assoc. f_equal. by eapply IHHType.
Qed. *)

Ltac apply_const_typing_to_val H :=
	let v_valtype := fresh "v_valtype" in
    let v_val_ := fresh "v_val_" in
	apply val_is_same_as_admin_const in H; destruct H as [v_valtype [v_val_ H]];
	apply AI_const_typing in H.

Lemma Nop_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C AI_NOP (mk_functype t1s t2s) ->
    t1s = t2s.
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Nop *) by inversion H; subst; try discriminate.
	- (* Weakening *) f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (AI_DROP) (mk_functype t1s t2s) ->
    exists t, t1s = t2s ++ [t].
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Drop *) by inversion H; subst; try discriminate; exists v_t.
	- (* Weakening *) edestruct IHHType as [? ?] => //=; subst.
	exists x. by repeat rewrite <- app_assoc.
Qed.

Lemma Unop_typing: forall v_S v_C v_t v_op t1s t2s,
    Admin_instr_ok v_S v_C (AI_UNOP v_t v_op) (mk_functype t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = @app _ ts [v_t].
Admitted. (*
Proof.
	move => v_S v_C v_t v_op t1s t2s HType.
	gen_ind_subst HType.
	- (* Unop *) inversion H; subst; try discriminate.
		split. 
		- reflexivity.
		- exists []. simpl. injection H3 as H1. f_equal. apply H1.
	- (* Weakening *) edestruct IHHType as [? [??]] => //=; subst.
	repeat split => //=. exists (v_t ++ x). by rewrite <- app_assoc.
Qed. *)

Lemma Binop_typing: forall v_S v_C v_t v_op t1s t2s,
	Admin_instr_ok v_S v_C (AI_BINOP v_t v_op) (mk_functype t1s t2s) ->
    t1s = t2s ++ [v_t] /\ exists ts, t2s = ts ++ [v_t].
Admitted. (*
Proof.
	move => v_S v_C v_t v_op t1s t2s HType.
	gen_ind_subst HType.
	- (* Binop *) inversion H; subst; try discriminate.
		injection H3 as H1; subst.
		split => //. exists []. eauto.
	- (* Weakening *) edestruct IHHType as [? [??]] => //=; subst.
	split. 
		- repeat rewrite <- app_assoc. reflexivity.
		- exists (v_t ++ x). by rewrite <- app_assoc.
Qed. *)

Lemma Testop_typing : forall v_S v_C v_t v_testop ts1 ts2,
	Admin_instr_ok v_S v_C (AI_TESTOP v_t v_testop) (mk_functype ts1 ts2) ->
	exists ts, ts1 = ts ++ [v_t] /\ ts2 = ts ++ [I32].
Admitted. (*
Proof.
	move => v_S v_C v_t v_testop ts1 ts2 HType.

	gen_ind_subst HType.
	- (* Testop *) inversion H; subst; try discriminate.
		exists []. simpl. injection H3 as H1. subst. eauto.
	- (* Weakening *) edestruct IHHType as [? [??]] => //=; subst.
	exists (v_t ++ x). by repeat split => //=; rewrite <- app_assoc.
Qed. *)

Lemma Select_typing: forall v_S v_C t1s t2s,
	Admin_instr_ok v_S v_C (AI_SELECT) (mk_functype t1s t2s) ->
    exists ts t, t1s = ts ++ [t; t; I32] /\ t2s = ts ++ [t].
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Select *) inversion H; subst; try discriminate.
	exists [], v_t. eauto.
	- (* Weakening *) edestruct IHHType as [? [? [??]]] => //=; subst.
	exists (v_t ++ x), x0. by repeat split => //=; rewrite <- app_assoc.
Qed.

Lemma Val_Const_list_typing: forall v_S v_C v_vals t1s t2s,
    Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) (mk_functype t1s t2s) ->
    t2s = t1s ++ (List.map typeof v_vals).
Proof.
	move => v_S v_C v_vals.
	induction v_vals => //=; move => t1s t2s HType.
	- apply admin_empty in HType. subst. by rewrite cats0.
	- destruct a.
	  apply_composition_typing_and_single HType.
	  apply AI_const_typing in H4_comp0.
	  subst.
	  apply IHv_vals in H4_comp.
	  subst. simpl.
	  repeat rewrite <- app_assoc.  
	  by f_equal.
Qed.

Lemma If_typing: forall v_S v_C t1s v_ais1 v_ais2 ts ts',
	Admin_instr_ok v_S v_C (AI_IFELSE t1s v_ais1 v_ais2) (mk_functype ts ts') ->
	exists ts0,
   	ts = ts0 ++ [I32] /\ ts' = ts0 ++ t1s /\
				Instrs_ok (upd_label v_C ([t1s] ++ C_LABELS v_C)) (v_ais1) (mk_functype [] t1s) /\
                Instrs_ok (upd_label v_C ([t1s] ++ C_LABELS v_C)) (v_ais2) (mk_functype [] t1s).
Admitted.
(* Proof.
	move => v_S v_C t1s v_ais1 v_ais2 ts ts' HType.
	gen_ind_subst HType. 
	- (* IF *) inversion H; subst; try discriminate.
		destruct H4.
		exists [].
		simpl. injection H3 as H10. subst. 
		repeat split => //. 
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]]=> //=; subst.
	exists (v_t ++ x). 
	destruct H1.
	repeat split => //=; try rewrite <- app_assoc; try reflexivity.
Qed. *)

Definition fun_nat__u32 : nat -> u32 := mk_uN 32.

Definition fun_u32__nat : u32 -> nat := fun x => match x with
    |  mk_uN v => v
	end.


Lemma Br_if_typing: forall v_S v_C ts1 ts2 v_memaddr, 
	Admin_instr_ok v_S v_C (AI_BR_IF (fun_nat__u32 v_memaddr)) (mk_functype ts1 ts2) ->
    exists ts (ts' : resulttype), ts2 = ts ++ ts' /\ ts1 = ts2 ++ [I32] /\ (v_memaddr < List.length (C_LABELS v_C))%coq_nat
	/\ lookup_total (C_LABELS v_C) v_memaddr = ts'.
Admitted.
(* Proof.
	move => v_S v_C ts1 ts2 v_memaddr HType.
	gen_ind_subst HType.
	- (* BR_if *) inversion H; subst; try discriminate.
		injection H3 as H1. destruct H4. exists [], v_t. simpl. 
		repeat split => //; subst. apply H0. reflexivity.
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]] => //=; subst.
	exists (v_t ++ x), x0. destruct H0; subst. 
	repeat split => //=; try repeat rewrite <- app_assoc; try reflexivity.
Qed. *)

Lemma Br_table_typing: forall v_S v_C ts1 ts2 ids i0,
    Admin_instr_ok v_S v_C (AI_BR_TABLE (map fun_nat__u32 ids) (fun_nat__u32 i0)) (mk_functype ts1 ts2) ->
    exists ts1' (ts : resulttype) , ts1 = ts1' ++ ts ++ [I32] /\
                        List.Forall (fun i => (i < length (C_LABELS v_C))%coq_nat) (ids) /\
						(i0 < length (C_LABELS v_C))%coq_nat /\
						(ts = (lookup_total (C_LABELS v_C) i0)) /\
						List.Forall (fun i => ts = lookup_total (C_LABELS v_C) i) (ids).
Admitted.
(* Proof.
	move => v_S v_C ts1 ts2 ids i0 HType.
	gen_ind_subst HType.
	- (* Br_table *) inversion H; subst; try discriminate.
		injection H3 as H1. destruct H4 as [H5 [H6 [H7 H8]]]. subst.
		exists v_t_1, (lookup_total (C_LABELS v_C0) i0). repeat split => //.
	- (* Weakening *) edestruct IHHType as [? [? [? [? [? [? ?]]]]]] => //=; subst.
	exists (v_t ++ x), (lookup_total (C_LABELS v_C0) i0).
	repeat split => //=; try repeat rewrite <- app_assoc; try reflexivity.
Qed. *)

Lemma Relop_typing: forall v_S v_C v_t v_op t1s t2s,
    Admin_instr_ok v_S v_C (AI_RELOP v_t v_op) (mk_functype t1s t2s) ->
    exists ts, t1s = ts ++ [v_t; v_t] /\ t2s = ts ++ [I32].
Admitted. (*
Proof.
	move => v_S v_C v_t v_op t1s t2s HType.
	gen_ind_subst HType.
	- (* Relop *) inversion H; subst; try discriminate.
		exists []. injection H3 as H1. subst. eauto.
	- (* Weakening *) edestruct IHHType as [? [? ?]] => //=; subst.
	exists (v_t ++ x). by repeat split => //=; try rewrite <- app_assoc.
Qed. *)

Lemma Cvtop_typing: forall v_S v_C t1 t2 v_op t1s t2s,
    Admin_instr_ok v_S v_C (AI_CVTOP t2 t1 v_op) (mk_functype t1s t2s) ->
    exists ts, t1s = ts ++ [t1] /\ t2s = ts ++ [t2].
Proof.
	move => v_S v_C t1 t2 v_op t1s t2s HType.
	gen_ind_subst HType. 
	- (* Cvtop *) exists [].
		simpl. 
		inversion H; subst; try discriminate; injection H3 as H1; subst => //.
	- (* Weakening *) edestruct IHHType as [? [? ?]] => //=; subst.
	exists (v_t ++ x). by repeat split => //=; try rewrite <- app_assoc.
Qed.


Lemma Local_tee_typing: forall v_S v_C v_memaddr ts1 ts2,
    Admin_instr_ok v_S v_C (AI_LOCAL_TEE (fun_nat__u32 v_memaddr)) (mk_functype ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [t] /\ (v_memaddr < length (C_LOCALS v_C))%coq_nat /\
                lookup_total (C_LOCALS v_C) v_memaddr = t.
Admitted.
(* Proof.
	move => v_S v_C v_memaddr ts1 ts2 HType.
	gen_ind_subst HType.
	- (* Local Tee *) inversion H; subst; try discriminate.
		destruct H4.
		injection H3 as H10; subst.
		exists [], (lookup_total (C_LOCALS v_C0) v_memaddr).
		repeat split => //=.
	- (* Weakening *) edestruct IHHType as [? [? [? [? [? ?]]]]] => //=; subst.
	exists (v_t ++ x), (lookup_total (C_LOCALS v_C0) v_memaddr).
	by repeat split => //=; try rewrite <- app_assoc.
Qed. *)

Lemma Label_typing: forall v_S v_C n v_instrs v_admininstrs ts1 ts2,
    Admin_instr_ok v_S v_C (AI_LABEL_ n v_instrs v_admininstrs) (mk_functype ts1 ts2) ->
    exists (ts : resulttype) (ts2' : option valtype), ts2 = ts1 ++ ts2' /\
					Instrs_ok v_C v_instrs (mk_functype ts ts2') /\
					fun_optionSize ts = n /\
                    Admin_instrs_ok v_S (upd_label v_C ([ts] ++ (C_LABELS v_C))) v_admininstrs (mk_functype [] ts2').
Admitted.
(* Proof.
	move => v_S v_C n v_instrs v_admininstrs ts1 ts2 HType.
	gen_ind_subst HType => //=.
		- (* Instr *) inversion H; subst; try discriminate.
		- (* Label *) destruct H as [? [? ?]]. exists v_t_1, v_t_2. repeat split => //=.
		- (* Weakening *) edestruct IHHType as [? [? [? [? ?]]]] => //=; subst. exists x, x0. by repeat split => //=; try rewrite <- app_assoc.
Qed. *)

(* Lemma Frame_typing: forall v_S v_C n v_F v_ais t1s t2s,
    Admin_instr_ok v_S v_C (AI_FRAME_ n v_F v_ais) (mk_functype t1s t2s) ->
    exists (ts : resulttype), t2s = t1s ++ ts /\
               Thread_ok v_S ts v_F v_ais ts /\ 
			   (n = (fun_optionSize ts)). 
Proof.
	move => v_S v_C n v_F v_ais t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Instr *) inversion H; subst; try discriminate.
	- (* Frame *)  exists v_t => //=.
	- (* Weakening *) edestruct IHHType as [ts2 [??]]; eauto. subst.
		exists ts2. by repeat split => //=; try rewrite <- app_assoc.
Qed. *)

Lemma Set_local_typing: forall v_S C i t1s t2s,
    Admin_instr_ok v_S C (AI_LOCAL_SET (fun_nat__u32 i)) (mk_functype t1s t2s) ->
    exists t, lookup_total (C_LOCALS C) i = t /\
    t1s = t2s ++ [t] /\
    (i < length (C_LOCALS C))%coq_nat.
Admitted.
(* Proof.
	move => v_S C i t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Set Local *) inversion H; subst; try discriminate. destruct H4.
		injection H3 as H2. exists v_t. subst; repeat split => //.
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]] => //=; subst.
		exists (lookup_total (C_LOCALS C) i).
		by repeat split => //=; try rewrite <- app_assoc.
Qed. *)

Lemma Get_local_typing: forall v_S v_C i t1s t2s,
    Admin_instr_ok v_S v_C (AI_LOCAL_GET (fun_nat__u32 i)) (mk_functype t1s t2s) ->
    exists t, lookup_total (C_LOCALS v_C) i = t /\
    t2s = t1s ++ [::t] /\
    (i < length (C_LOCALS v_C))%coq_nat.
Admitted.
(* Proof.
	move => v_S v_C i t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Get Local *) inversion H; subst; try discriminate. destruct H4.
		injection H3 as H2. exists v_t. subst; repeat split => //.
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]] => //=; subst.
		exists (lookup_total (C_LOCALS v_C0) i).
		by repeat split => //=; try rewrite <- app_assoc.
Qed. *)


Lemma Get_global_typing: forall v_S v_C i t1s t2s,
    Admin_instr_ok v_S v_C (AI_GLOBAL_GET (fun_nat__u32 i)) (mk_functype t1s t2s) ->
    exists mut t, (lookup_total (C_GLOBALS v_C) i) = mk_globaltype mut t /\
    t2s = t1s ++ [::t] /\
    (i < length (C_GLOBALS v_C))%coq_nat.
Admitted.
(* Proof.
	move => ????? HType.
	gen_ind_subst HType => //=.
	 - (* Get Global *) inversion H; subst; try discriminate.
		destruct H4. injection H3 as ?. subst. exists v_mut, v_t. repeat split => //=.

	 - (* Weakening *) edestruct IHHType as [?[?[?[??]]]]; eauto => //=. exists x, x0; subst.
	 	repeat split => //; by rewrite <- app_assoc.
Qed. *)

Lemma Set_global_typing: forall v_S v_C i t1s t2s,
	Admin_instr_ok v_S v_C (AI_GLOBAL_SET (fun_nat__u32 i)) (mk_functype t1s t2s) ->
    exists t, lookup_total (C_GLOBALS v_C) i = mk_globaltype (some MUT) t /\
    t1s = t2s ++ [t] /\
    (i < length (C_GLOBALS v_C))%coq_nat.
Admitted.
(* Proof.
	intros ????? HType.
	gen_ind_subst HType => //=.
	 - (* Set Global *) inversion H; subst; try discriminate.
		destruct H4 as [? ?]. injection H3 as ?; subst. exists v_t. repeat split => //=.
	- edestruct IHHType as [? [? [? ?]]]; subst => //=. exists (x).
		repeat split => //=; by rewrite <- app_assoc.
Qed. *)

Lemma Return_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (AI_RETURN) (mk_functype t1s t2s) ->
    exists (ts : resulttype) ts', t1s = ts' ++ ts /\
                   C_RETURN v_C = Some ts.
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Return *) inversion H; subst; try discriminate. exists v_t, v_t_1 => //=.
	- (* Weakening *) edestruct IHHType as [? [? [?  ?]]] => //=; subst.
		exists x, (v_t ++ x0). by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Const_list_typing_empty: forall v_S v_C v_vals,
    Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) (mk_functype [::] (List.map typeof v_vals)).
Admitted.
(* Proof.
	move => v_S v_C.
	induction v_vals => //=.
	- apply AIs_ok_empty.
	- rewrite -cat1s.
		replace (typeof a :: List.map typeof v_vals) with ([::typeof a] ++ List.map typeof v_vals) => //.
		apply admin_composition' with (t2s := [::typeof a]); eauto.
		- destruct a.
			simpl.
			apply (AIs_ok_seq v_S v_C [] (AI_CONST v_valtype v_val_) [] [v_valtype] []).
			split.
			- apply AIs_ok_empty.
			- apply (AI_ok_instr v_S v_C (instr__CONST v_valtype v_val_) (mk_functype [] [v_valtype])); subst.
				apply Instr_ok__const.
		- by apply admin_instrs_weakening_empty_1.
Qed. *)

Lemma Break_typing: forall n v_S v_C t1s t2s,
	Admin_instr_ok v_S v_C (AI_BR (fun_nat__u32 n)) (mk_functype t1s t2s) ->
	exists ts ts0, 
				(n < length (C_LABELS v_C))%coq_nat /\
				lookup_total (C_LABELS v_C) n = ts /\
				t1s = ts0 ++ ts.
Admitted.
(* Proof.
	move => n v_S v_C t1s t2s HType.
	gen_ind_subst HType.
	- (* BREAK *) 
		inversion H; subst; try discriminate. destruct H4.
		exists v_t, v_t_1.
		injection H3 as ?; subst; repeat split => //=.
	- (* Weakening *)
		edestruct IHHType as [ts [ts0 [? ?]]] => //=.
		destruct H0; subst.
		exists (lookup_total (C_LABELS v_C0) n), (v_t ++ ts0).
		repeat split => //=; by repeat rewrite <- app_assoc.
Qed. *)

Lemma CALL_ADDR_typing: forall v_S v_C a t1s t2s,
    Admin_instr_ok v_S v_C (AI_CALL_ADDR a) (mk_functype t1s t2s) ->
    exists v_funcinst, lookup_total (FUNCS v_S) a = v_funcinst.
Admitted.
(* Proof.
  move => s C a t1s t2s HType.
  gen_ind_subst HType => //.
  - (* Instr *) inversion H; subst; try discriminate.
  - (* Call Addr *) inversion H; destruct H3. exists (lookup_total (store__FUNCS s) a) => //=.
  - (* Weakening *) by eapply IHHType => //=.
Qed. *)

Lemma map_eq_local: forall (l l' : list valtype) ,
	List.map [eta LOCAL] l = List.map [eta LOCAL] l' -> l = l'.
Proof.
	move => l l' H.
	generalize dependent l'.
	induction l; move => l' H.
	- destruct l' => //=.
	- destruct l' => //=. repeat rewrite List.map_cons in H.
		injection H as ?.
		f_equal. 
		apply H.
		apply IHl; eauto.
Qed.

Lemma fold_append: forall v_C v_t v_func v_glob v_tab v_mem v_local v_lab v_ret,
	_append {| C_TYPES := v_t;
	C_FUNCS := v_func;
	C_GLOBALS := v_glob;
	C_TABLES := v_tab;
	C_MEMS := v_mem;
	C_LOCALS := v_local;
	C_LABELS := v_lab;
	C_RETURN := v_ret|} v_C = 
	{| C_TYPES := v_t ++ C_TYPES v_C;
	C_FUNCS := v_func ++ C_FUNCS v_C;
	C_GLOBALS := v_glob ++ C_GLOBALS v_C;
	C_TABLES := v_tab ++ C_TABLES v_C;
	C_MEMS := v_mem ++ C_MEMS v_C;
	C_LOCALS := v_local ++ C_LOCALS v_C;
	C_LABELS := v_lab ++ C_LABELS v_C;
	C_RETURN := _append v_ret (C_RETURN v_C)|}.
Proof. reflexivity. Qed.

Lemma CALL_ADDR_invoke_typing: forall v_S v_C v_a t1s t2s v_t_1 (v_t_2 : resulttype) v_mm v_func v_x v_t v_instrs,
    Admin_instr_ok v_S v_C (AI_CALL_ADDR v_a) (mk_functype t1s t2s) ->
	((lookup_total (FUNCS v_S) v_a) = {| FUNC_TYPE := (mk_functype v_t_1 v_t_2); FUNC_MODULE := v_mm; CODE := v_func |}) ->
	(v_func = (FUNC v_x (List.map (fun v_t => (LOCAL v_t)) (v_t)) v_instrs)) ->
	Store_ok v_S ->
    exists ts' C', t1s = ts' ++ v_t_1 /\ t2s = ts' ++ v_t_2 /\
	Module_instance_ok v_S v_mm C' /\
	Instrs_ok (upd_local_label_return C' ((v_t_1 ++ v_t) ++ (C_LOCALS C')) (_append ([v_t_2]) (C_LABELS C')) (_append (Some v_t_2) (C_RETURN C'))) v_instrs (mk_functype [::] v_t_2).
Admitted.
(* Proof.
	move => v_S v_C v_a t1s t2s v_t_1 v_t_2 v_mm v_func v_x v_t v_instrs HType Hfinst HFunc HST.
	gen_ind_subst HType => //.
	- (* Instr *) inversion H; subst; try discriminate.
	- (* Call Addr *) inversion H; destruct H4. subst. rewrite H5 in H3. injection H3 as ?. subst. inversion HST; decomp.
		apply Forall2_lookup in H9; destruct H9.
		rewrite H8 in H4. simpl in H4.
		apply H13 in H4.
		rewrite H8 in H5.
		simpl in H5.
		rewrite H5 in H4.
		inversion H4. destruct H16 as [? [? ?]].
		inversion H21. destruct H24 as [? [? ?]].
		inversion H30.
		exists [], v_C. repeat split => //=; subst. 
		- rewrite H1 in H28. apply H28.
		- apply map_eq_local in H25; subst.
		rewrite fold_append in H31; simpl in H31.
		repeat rewrite _append_option_none_left in H31.
		rewrite H1 in H28.
		destruct v_t_2; destruct v_t_4; try discriminate. 
		- unfold option_to_list in H28; injection H28 as ?; subst. apply H31.
		- apply H31.
	- (* Weakening *) edestruct IHHType as [ts0' [C' [? [? [? ?]]]]]; subst => //=.
		- apply HST.
		- apply Hfinst.
		- exists (v_t0 ++ ts0'), C'; repeat split => //=; by rewrite <- app_assoc.  
Qed. *)

Lemma option_zip_with_same_pack: forall (v_n0 : option nat) (v_sx0 : option sx) (v_ww_sx : option (sz * sx)),
	option_zipWith (fun (v : nat) (s : sx) => (mk_sz v, s)) v_n0 v_sx0 = v_ww_sx ->
	v_n0 = (None : option nat) <-> v_sx0 = (None : option sx) -> (exists v s, v_ww_sx = Some ((mk_sz v, s)))
	\/ (v_ww_sx = None).
Proof.
	move => v_n0 v_sx0 v_ww_sx H H2.
	assert ((None : option sx) = (None : option sx)). { reflexivity. } 
	assert ((None : option nat) = (None : option nat)). { reflexivity. } 
	destruct v_n0 => //=; destruct v_sx0 => //=; simpl in H.
	- left. exists n, s; eauto.
	- rewrite <- H2 in H0; subst. discriminate.
	- rewrite H2 in H1. discriminate.
	- right; eauto.
Qed. 

(*
Lemma Load_typing: forall v_S v_C t v_memop v_ww_sx t1s t2s,
    Admin_instr_ok v_S v_C (AI_LOAD t v_ww_sx v_memop) (mk_functype t1s t2s) ->
    exists ts v_n v_sx v_inn v_mt, t1s = ts ++ [I32] /\ t2s = ts ++ [t] /\
	(v_ww_sx = option_zipWith (fun (v : nat) (s : sx) => (loadop_  v s)) v_n v_sx ) /\
	(0 < (List.length (C_MEMS v_C)))%coq_nat /\ ((v_n = None) <-> (v_sx = (None : option sx))) 
	/\ ((lookup_total (C_MEMS v_C) 0) = v_mt) 
	/\ ((Nat.pow 2 (ALIGN v_memop))%coq_nat <= ((fun_size t) / 8)%coq_nat)%coq_nat 
	/\ List.Forall (fun v_n => ((((Nat.pow 2 (ALIGN v_memop)) <= (v_n / 8))%coq_nat) 
	/\ ((v_n / 8) < ((fun_size t) / 8))%coq_nat)) (option_to_list v_n) 
	/\ ((v_n = None) \/ ([t] = [v_inn])).          
Admitted.
(* Proof.
	move => v_S v_C t v_memop v_ww_sx t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Load *) inversion H; subst; try discriminate; destruct H4 as [? [? [? [? [? ?]]]]].
		injection H3 as ?. exists [], v_n, v_sx, v_inn, v_mt. subst. repeat split => //=.
		destruct H6. 
		- left => //=. 
		- right. f_equal. apply H2.
	- (* Weakening *) edestruct IHHType as [ts [v_n [v_sx [v_inn [v_mt [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]] => //=.
	exists (v_t ++ ts), v_n, v_sx, v_inn, v_mt. subst. repeat split => //=; try repeat rewrite <- app_assoc; eauto.
Qed. *) *)

Lemma Store_typing: forall v_S v_C t v_ww v_memop t1s t2s,
    Admin_instr_ok v_S v_C (AI_STORE t v_ww v_memop) (mk_functype t1s t2s) ->
	exists v_n v_mt v_inn,
    t1s = t2s ++ [::I32; t] /\
	(0 < (List.length (C_MEMS v_C)))%coq_nat 
	/\ ((lookup_total (C_MEMS v_C) 0) = v_mt) 
	/\ ((Nat.pow 2 (fun_u32__nat (ALIGN v_memop))) <= ((fun_size t) / 8))%coq_nat 
	/\ List.Forall (fun v_n => (((Nat.pow 2 (fun_u32__nat (ALIGN v_memop))) <= (v_n / 8))%coq_nat 
	/\ ((v_n / 8) < ((fun_size t) / 8))%coq_nat)) (option_to_list v_n) 
	/\ ((v_n = None) \/ (t = v_inn)).
Admitted.
(* Proof.
	move => v_S v_C t v_ww v_memop t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Store *) inversion H; subst; try discriminate. destruct H4 as [? [? [? [? ?]]]].
		injection H3 as ?. exists v_n, v_mt, v_inn. subst. repeat split => //=.
	- (* Weakening *) edestruct IHHType as [v_n [v_mt [v_inn [? [? [? [? [? ?]]]]]]]] => //=.
	exists v_n, v_mt, v_inn. subst. repeat split => //=; try repeat rewrite <- app_assoc; eauto.
Qed. *)

Lemma Memory_size_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (AI_MEMORY_SIZE) (mk_functype t1s t2s) ->
	exists v_mt, 
	(0 < (List.length (C_MEMS v_C)))%coq_nat /\ 
	((lookup_total (C_MEMS v_C) 0) = v_mt) /\
    t2s = t1s ++ [I32].
Admitted.
(* Proof.
	intros v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Memory Size *) inversion H; subst; try discriminate. destruct H3.
  		exists v_mt. repeat split => //=.
	- (* Weakening *) edestruct IHHType as [v_mt [? ?]]; subst=> //=. exists v_mt. destruct H0. repeat split => //=.
		rewrite H1. by repeat rewrite <- app_assoc.
Qed. *)

Lemma Grow_memory_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (AI_MEMORY_GROW) (mk_functype t1s t2s) ->
	exists v_mt ts, 
	(0 < (List.length (C_MEMS v_C)))%coq_nat /\ 
	((lookup_total (C_MEMS v_C) 0) = v_mt) /\
    t2s = t1s /\ t1s = ts ++ [I32].
Admitted.
(* Proof.
	intros v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Memory Grow *) inversion H; subst; try discriminate. destruct H3.
		exists v_mt, []. repeat split => //=.
	- (* Weakening *) edestruct IHHType as [v_mt [v_ts [? [? [? ?]]]]] => //=.
		exists v_mt, (v_t ++ v_ts). subst. repeat split => //=; by repeat rewrite <- app_assoc.
Qed. *)
		
Lemma Block_typing: forall v_S v_C t2s v_instrs tn tm,
    Admin_instr_ok v_S v_C (AI_BLOCK t2s v_instrs) (mk_functype tn tm) ->
    exists ts, tn = ts /\ tm = ts ++ t2s /\
		Instrs_ok (upd_label v_C ([t2s] ++ (C_LABELS v_C))) v_instrs (mk_functype [] t2s).
Proof.
	move => v_S v_C t2s v_instrs tn tm HType.
	gen_ind_subst HType => //=.
	- (* Block *) 
		inversion H; subst; try discriminate. exists []. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [? [? ?]]] => //=; subst.
		exists (v_t ++ ts). repeat split => //=; by rewrite <- app_assoc.
Qed.

Lemma Loop_typing: forall v_S v_C t2s v_instrs tn tm,
    Admin_instr_ok v_S v_C (AI_LOOP t2s v_instrs) (mk_functype tn tm) ->
    exists ts, tn = ts /\ tm = ts ++ t2s /\
		Instrs_ok (upd_label v_C ([None] ++ (C_LABELS v_C))) v_instrs (mk_functype [] t2s).
Admitted.
(* Proof.
	move => v_S v_C t2s v_instrs tn tm HType.
	gen_ind_subst HType => //=.
	- (* Loop *) 
		inversion H; subst; try discriminate. exists []. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [? [? ?]]] => //=; subst.
		exists (v_t ++ ts). repeat split => //=; by rewrite <- app_assoc.
Qed. *)

Lemma Call_typing: forall j v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (AI_CALL j) (mk_functype t1s t2s) ->
    exists ts t1s' (t2s' : option valtype), (fun_u32__nat j < length (C_FUNCS v_C))%coq_nat /\
    lookup_total (C_FUNCS v_C) (fun_u32__nat j) = mk_functype t1s' t2s' /\
                         t1s = ts ++ t1s' /\
                         t2s = ts ++ t2s'.
Admitted.
(* Proof.
	move => j v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Call *) 
		inversion H; subst; try discriminate. destruct H4. exists [], t1s, v_t_2. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [t1s'' [t2s'' [? [? [? ?]]]]]] => //=; subst.
		exists (v_t ++ ts), t1s'', t2s''. repeat split => //=; by rewrite <- app_assoc.
Qed. *)

Lemma Call_indirect_typing: forall v_S i v_C t1s t2s,
    Admin_instr_ok v_S v_C (AI_CALL_INDIRECT i) (mk_functype t1s t2s) ->
    exists tn (tm : option valtype) ts,
    (fun_u32__nat i < length (C_TYPES v_C))%coq_nat /\
    lookup_total (C_TYPES v_C) (fun_u32__nat i) = mk_functype tn tm /\
    t1s = ts ++ tn ++ [I32] /\ t2s = ts ++ tm.
Admitted.
(* Proof.
	move => j v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Call Indirect *) 
		inversion H; subst; try discriminate. destruct H4. exists v_t_1, v_t_2, []. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [t1s'' [t2s'' [? [? [? ?]]]]]] => //=; subst.
		exists ts, t1s'', (v_t ++ t2s''). repeat split => //=; by rewrite <- app_assoc.
Qed. *)
