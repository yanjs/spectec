
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure.
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

(*
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
Qed. *) *)

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
Admitted. (*
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
Qed. *)

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

Lemma vals_typing_extension: forall v_S v_S' v_t v_val,
	Store_extension v_S v_S' ->
	Vals_ok v_S v_val v_t ->
	Vals_ok v_S' v_val v_t.
Proof.
	move => v_S v_S' v_t v_val Hs Hv1.
Admitted.
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

Lemma t_preservation_vs_type': forall s f ais s' f' ais' C C' t1s t2s,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Store_ok s -> 
    Module_instance_ok s (F_MODULE f) C ->
	Vals_ok s (F_LOCALS f) (C_LOCALS C') ->
	inst_match C C' ->
    Admin_instrs_ok s C' ais (t1s :-> t2s) ->
    Vals_ok s (F_LOCALS f') (C_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' t1s t2s HReduce HST HIT.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	move: C' t1s t2s.
	generalize dependent ais.
	generalize dependent ais'.

	induction HReduce => //;
	move => ais' Heqc1 ais Heqc2 C' t1s t2s HVals1 Hmatch HType;
	try (destruct v_z; subst);
	try (destruct v_z'; subst);
	try (apply config_same in Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]];
		apply config_same in Heqc2 as [Hafter1  [Hafter2  Hafter3]]);
	try (specialize (IHHReduce _ erefl _ erefl));
	subst; auto.
	{
		invert_ais_typing.
		eapply IHHReduce; eauto.
	}
	{
		invert_ais_typing.
		resolve_all_pt.
		assert (Vals_ok s (F_LOCALS f') (C_LOCALS C') =
			Vals_ok s (F_LOCALS f') (C_LOCALS (prepend_label C' extr))).
		{
			destruct C'; auto.
		}
		rewrite H.
		eapply IHHReduce; destruct C'; eauto.
	}
	{
		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_eq Hsub Hsub0.
		eapply Val_ok_non_bot in HValok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv; eauto.
		subst.

		destruct f. simpl.
		eapply Forall2_list_update_func2; eauto.
	}
Qed.

Lemma t_preservation_vs_type: forall s f ais s' f' ais' C C' C'' t1s t2s,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Store_ok s -> 
	Store_ok s' ->
	Store_extension s s' ->
    Module_instance_ok s (F_MODULE f) C ->
    Module_instance_ok s' (F_MODULE f') C'' ->
	Vals_ok s (F_LOCALS f) (C_LOCALS C') ->
	inst_match C C' ->
    Admin_instrs_ok s C' ais (t1s :-> t2s) ->
    Vals_ok s' (F_LOCALS f') (C_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' C'' t1s t2s HReduce HST HIT
		HStoreExt HMInst HMinst' HValOK Him HType.
	eapply t_preservation_vs_type' in HValOK; eauto.
	eapply vals_typing_extension in HValOK; eauto.
Qed.
(*
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
	try (specialize (IHHReduce _ erefl _ erefl)).
	{ (* Label Context *)
		invert_ais_typing.
		eapply IHHReduce.
		eauto.
	}
	{ (* Frame Context *)
		invert_ais_typing.
		resolve_all_pt.
		eapply IHHReduce;
		eauto.
		Opaque fun_coec_instr__admininstr.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H0; subst.
		inversion H4; subst.
		eapply IHHReduce; eauto.
	}
Admitted.
(*
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
Qed. *) *)

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
	{ (* Label Seq *)
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		subst.
		typing_inversion HType.
		typing_inversion H2.
		eapply IHHReduce; eauto.
	}
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
	destruct Heqc2 as [? [? ?]]; subst => //);
	eapply IHHReduce; eauto.
Qed.

Lemma t_read_preservation: forall v_s v_f v_ais v_ais' v_C v_C' t1s t2s,
    Step_read (mk_config (mk_state v_s v_f) v_ais) v_ais' ->
    Store_ok v_s ->
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) (C_LOCALS v_C') (F_LOCALS v_f) ->
	inst_match v_C v_C' ->
    Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
    Admin_instrs_ok v_s v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_ais' v_C v_C' t1s t2s HReduce HST.
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
		assert (v_ts = extr). {
			eapply Vals_ok_non_bot in Hforall as Hnonbot.
			eapply (resulttype_sub_non_bot _ _ Hnonbot) in Hsubs; subst.
			auto.
		}
		subst.

		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		eapply AI_ok_frame.
		2: auto.

		(* Thread_ok *)
		inversion HST; subst.
		eapply Forall2_nth in H4 as [_ H4].
		simpl in *.
		eapply H4 with (d' := default_val) in H as Hfiok.
		unfold lookup_total in H0;
		erewrite H0 in Hfiok.
		inversion Hfiok; subst.

		eapply mk_Thread_ok with (v_C := ({|
			C_TYPES := [];
			C_FUNCS := [];
			C_GLOBALS := [];
			C_TABLES := [];
			C_MEMS := [];
			C_ELEMS := [];
			C_DATAS := [];
			C_LOCALS := extr ++ v_t;
			C_LABELS := [];
			C_RETURN := None
			|} @@ v_C0)).
		{
			eapply mk_Frame_ok with (v_t := extr ++ v_t); auto.
			{
				rewrite -!size_length.
				rewrite !size_cat.
				rewrite !size_map.
				auto.
			}
			subst.
			eapply Forall2_app; auto.
			clear H22 H0 Hfiok.
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
		subst.
		eapply construct_ais_typing_single.
		2: eapply instrtype_sub_refl.
		econstructor.
		3: eauto.
		{
			eapply instrs_empty_typing; eapply resulttype_sub_refl.
		}
		subst.

		eapply AIs_ok_instrs.

		inversion H22; subst.
		inversion H27; subst.
		inversion H21; subst.
		unfold _append, Append_context, _append_context, _append, Append_List_.
		simpl.
		unfold _append, Append_context, _append_context, _append, Append_List_ in H23.
		simpl in H23.
		rewrite !app_nil_r in H23.
		rewrite !app_nil_r.
		assert (injective (ListDef.map [eta LOCAL])) as map_local_inj.
		{
			eapply inj_map.
			unfold injective.
			move=> x1 x2 Hconstructor.
			by inversion Hconstructor.
		}
		eapply map_local_inj in H16; subst.
		auto.
	}
	{ (* Ref_func *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise. subst.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		unfold fun_funcaddr in *; subst.

		destruct v_f, v_s, v_C.
		inversion HIT1; subst.
		simpl in *; subst.
		simpl in *.
		eapply Forall2_nth in H13 as [_ H13].
		eapply (H13 _ default_val default_val) in H.
		inversion H; subst; simpl in *.

		eapply AI_ok_ref with
			(v_functype := ListDef.nth (fun_proj_uN_0 32 v_x) C_FUNCS default_val).

		econstructor; simpl in *; eauto.
	}
	{ (* Local_get *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise. subst.

		eapply Forall2_nth in HValOK as [HLength HValOK].

		destruct v_f; destruct v_C'; destruct v_C; destruct v_s;
		unfold inst_match in Him; destruct_all;
		subst; simpl in *; subst.
		eapply HValOK with (d := default_val) (d' := default_val) in H1.
		inversion HIT1; subst; simpl in *; subst.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		inversion H1; subst; unfold fun_coec_val__admininstr;
			unfold lookup_total in *.
		1,2:
			rewrite -H2;
			rewrite -H3.
		{
			eapply AI_ok_instr with (v_instr := (instr_CONST v_nt v_c_t)).
			econstructor.
		}
		{
			eapply AI_ok_instr with (v_instr := (instr_VCONST v_vt v_c_t)).
			destruct v_vt.
			econstructor.
		}
		rewrite -H; rewrite -H2.
		destruct v_r.
		{
			simpl.
			inversion H3; subst.
			eapply AI_ok_instr with (v_instr := (instr_REF_NULL v_rt)).
			constructor.
		}
		all:
			simpl;
			inversion H3; subst;
			econstructor; eauto.
	}
	{ (* Global_get *)
		invert_ais_typing.
		resolve_all_pt.

		eapply construct_ais_typing_single.
		2: eapply Hsub.

		destruct v_f; destruct v_C'; destruct v_C; destruct v_s;
		unfold inst_match in Him; destruct_all;
		subst; simpl in *; subst.
		inversion HIT1; subst; simpl in *; subst.

		unfold fun_global, lookup_total in *.
		eapply Forall2_nth in H21 as [_ Hglobal].
		rewrite H20 in Hglobal.
		eapply Hglobal with (d := default_val) (d' := default_val) in H1 as Hextglobal.

		inversion Hextglobal; subst; unfold lookup_total in *; simpl in *.
		rewrite H0 in H2; simpl in *.
		rewrite H5; simpl in *.
		inversion H2; subst; clear H2.

		inversion HST; subst.
		eapply Forall2_nth in H7 as [_ Hglobals].

		rewrite H6 in Hglobals.

		(* Failed to check if v_val has proper type. *)
		admit.
	}
	{ (* Table_get *)
		typing_inversion HType.
		typing_inversion H2.
		simpl in Hai;
		extract_premise; subst.
		typing_inversion H1;
		simpl in Hai;
		extract_premise; subst.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub0) in Hsub.

		eapply construct_ais_typing_single.
		2: eapply Hsub.

		destruct v_f; destruct v_C'; destruct v_C; destruct v_s;
		unfold inst_match in Him; destruct_all;
		subst; simpl in *; subst.
		inversion HIT1; subst; simpl in *; subst.
		unfold fun_table in *.

		rewrite -H15 in H0.
		eapply Forall2_nth in H16 as [_ H16].
		eapply H16 with (d := default_val) (d' := default_val) in H0.

		inversion H0; unfold lookup_total in *; subst; simpl in *.
		rewrite H6; simpl.
		rewrite H6 in H; simpl in H.
		rewrite H3 in H7.

		destruct v_tt'.
		admit.
	}
	{ (* Table_size *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise; subst.
		
		eapply construct_ais_typing_single.
		2: eapply Hsub.
		
		eapply AI_ok_instr with (v_instr := (instr_CONST I32 (mk_uN (fun_sizenn INN_I32)
		(Datatypes.length (TAB_REFS (fun_table (mk_state v_s v_f) v_x)))))).
		econstructor.
	}
	{ (* Table_fill *)
		typing_inversion HType.

		simpl in Hai; extract_premise.

		typing_inversion H4.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H3.
		simpl in Hai; extract_premise.
		rewrite -(cats0 [VALTYPE_I32; t]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
		as [Hsub2 Hsubs].
		2: auto.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_fill succ *)
		typing_inversion HType.

		simpl in Hai; extract_premise.
		pose proof H4 as H4_0.

		typing_inversion H4.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		pose proof Hsub0 as Hsub0_0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H3.
		simpl in Hai; extract_premise.
		rewrite -(cats0 [VALTYPE_I32; t]) in Hsub0.
		pose proof Hsub1 as Hsub1_0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.
		rewrite cats0 in Hsub0.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		pose proof Hsub2 as Hsub2_0.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
		as [Hsub2 Hsubs].
		2: auto.

		unfold_instrtype_sub Hsub0.
		assert ([VALTYPE_I32; t] = ts12_sup).
		{
			eapply resulttype_sub_non_bot.
			constructor. discriminate.
			constructor. eapply Val_ok_non_bot; eauto.
			constructor. auto.
		}
		eapply resulttype_sub_empty in Hsub4.
		subst.

		rewrite !cats0 in Hsub.

		pose proof Hsub as Hsub_0.
		unfold_instrtype_sub Hsub.
		eapply resulttype_sub_empty in Hsub4; subst.
		rewrite cats0 in Hsub_0.

		assert ([AI_CONST I32 v_i; v_val: admininstr; AI_TABLE_SET v_x;
			AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr;
			AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (v_n - 1)); AI_TABLE_FILL v_x] =
			[AI_CONST I32 v_i; v_val: admininstr; AI_TABLE_SET v_x] ++
			[AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr;
			AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (v_n - 1)); AI_TABLE_FILL v_x]) as Happ. { auto. }

		rewrite Happ.
		rewrite !cats0.
		eapply construct_ais_compose.
		{
			eapply construct_ais_compose with
				(v_ais1 := [AI_CONST I32 v_i; v_val: admininstr]).
			{
				eapply construct_ais_compose with
					(v_ais1 := [AI_CONST I32 v_i]).
				{
					eapply construct_ais_typing_single.
					2: eapply Hsub_0.
					eapply AI_ok_instr with (v_instr := (instr_CONST I32 v_i)).
					econstructor.
				}
				eapply H4_0.
			}
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := (instr_TABLE_SET v_x)).
			econstructor. eauto. eauto.
			{
				eapply instrtype_sub_trans with (tf2 := ([VALTYPE_I32; t] :-> [])).
				{
					eapply instrtype_sub_iff_resulttype_sub'.
					eapply resulttype_sub_app' with
					(ts1_sub := [VALTYPE_I32; t])
					(ts1 := [VALTYPE_I32; extr: valtype])
					in Hsubs as [Hsubs1 Hsubs2]; auto.
				}
				by eapply instrtype_sub_add_same.
			}
		}
		eapply construct_ais_compose with
			(v_ais1 := [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr;
		AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (v_n - 1))]).
		{
			eapply construct_ais_compose with
			(v_ais1 := [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr]).
			{
				eapply construct_ais_compose with
			(v_ais1 := [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1))]).
				{
					eapply construct_ais_typing_single.
					eapply AI_ok_instr with (v_instr := (instr_CONST I32
						(mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1))
					)).
					econstructor.
					by eapply instrtype_sub_add_same.
				}
				eapply construct_ais_typing_single.
				eapply construct_ai_val. eauto.

				rewrite -(cats0 (ts_sub ++ [VALTYPE_I32])).
				by eapply instrtype_sub_add_same.
			}
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := (instr_CONST I32
				(mk_uN (fun_sizenn INN_I32) (v_n - 1))
			)).
			econstructor.
			rewrite -(cats0 ((ts_sub ++ [VALTYPE_I32]) ++ [t])).
			by eapply instrtype_sub_add_same.
		}
		eapply construct_ais_typing_single.
		eapply AI_ok_instr with (v_instr := (instr_TABLE_FILL v_x)).
		econstructor; eauto.

		eapply instrtype_sub_trans.
		eapply Hsub2_0.

		eapply instrtype_sub_iff_resulttype_sub'.
		unfold_instrtype_sub Hsub1_0; eapply resulttype_sub_empty in Hsub4; subst.

		eapply resulttype_sub_app.
		2: eapply Hsub7.
		rewrite -catA; simpl.
		rewrite H2.
		by rewrite cats0.
	}
	{ (* Table_copy *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub1) in Hsub2.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_copy le *)
		(* Too boring and complicated. Similar to Table_fill succ *)
		admit.
	}
	{ (* Table_copy gt *)
		(* Too boring and complicated. Similar to Table_fill succ *)
		admit.
	}
	{ (* Table_init zero *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub1) in Hsub2.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_init succ *)
		(* Too boring and complicated. Similar to Table_fill succ *)
		admit.
	}
	{ (* Load None *)
		typing_inversion HType.
		typing_inversion H1.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		destruct v_nt;
		simpl in Hai; extract_premise.
		all: eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		
		all: eapply construct_ais_typing_single; eauto.
		all: eapply AI_ok_instr with (v_instr := (instr_CONST _ v_c)).
		all: econstructor.
	}
	{ (* Load INN_I32 *)
		typing_inversion HType.
		typing_inversion H1.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		
		eapply construct_ais_typing_single; eauto.
		eapply AI_ok_instr with (v_instr := (instr_CONST INN_I32
			(fun_extend__ v_n (the (fun_size INN_I32)) v_sx v_c))).
		econstructor.
	}
	{ (* Load INN_I64 *)
		typing_inversion HType.
		typing_inversion H1.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		
		eapply construct_ais_typing_single; eauto.
		eapply AI_ok_instr with (v_instr := (instr_CONST INN_I64
			(fun_extend__ v_n (the (fun_size INN_I64)) v_sx v_c))).
		econstructor.
	}
	(* SIMD instructions *) 
	admit.	admit.	admit.	admit.	admit.
	admit.	admit.	admit.	admit.	admit.
	admit.	admit.	admit.	admit.
	{ (* Memory_size *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		eapply AI_ok_instr with
			(v_instr := (instr_CONST I32 (mk_uN (fun_sizenn INN_I32) v_n))).
		econstructor.
	}
	{ (* Memory_fill *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; t]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
			as [Hsub2 Hsubs].
		2: eauto.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Memory_fill succ *)
		(* Too boring and complicated. Similar to Table_fill succ *)
		admit.
	}
	{ (* Memory_copy *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
			as [Hsub2 Hsubs].
		2: eauto.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Memory_copy le *)
		(* Too boring and complicated. Similar to Table_fill succ *)
		admit.
	}
	{ (* Memory_copy gt *)
		(* Too boring and complicated. Similar to Table_fill succ *)
		admit.
	}
	{ (* Memory_init 0 *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
			as [Hsub2 Hsubs].
		2: eauto.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Memory_init succ *)
		(* Too boring and complicated. Similar to Table_fill succ *)
		admit.
	}
Admitted.

Lemma t_preservation_type: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s,
    Step (mk_config (mk_state v_s v_f) v_ais) (mk_config (mk_state v_s' v_f') v_ais') ->
    Store_ok v_s ->
    Store_ok v_s' ->
	Store_extension v_s v_s' -> 
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
    Module_instance_ok v_s' (F_MODULE v_f) v_C ->
	Vals_ok v_s (F_LOCALS v_f) (C_LOCALS v_C')->
	inst_match v_C v_C' ->
    Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
    Admin_instrs_ok v_s' v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s HReduce HST1 HST2 HSExt HIT1 HIT2 HValOK Him.
	move: v_C v_C' HIT1 HIT2 HValOK Him t1s t2s.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	remember (mk_config (mk_state v_s' v_f') v_ais') as c2.
	generalize dependent v_ais.
	generalize dependent v_ais'.
	generalize dependent v_f.
	generalize dependent v_f'.
	dependent induction HReduce;
	move => r_v_f' r_v_f v_ais' Heqc2 v_ais Heqc1 v_C v_C' HIT1 HIT2 HValOK Him tx ty HType;
	try (destruct v_z; subst);
	try (destruct v_z'; subst); try eauto;
	try (apply config_same in Heqc1; apply config_same in Heqc2; 
		destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; 
		destruct Heqc2 as [Hafter1 [Hafter2 Hafter3]]; subst => //);
	try (specialize (IHHReduce _ _ _ erefl _ erefl));
	try (by eapply construct_ais_trap);
	try solve [
		invert_ais_typing;
		resolve_all_pt;
		first [
			join_subtyping_ge Hsub Hsub1;
			join_subtyping_eq Hsubi Hsub0 |
			join_subtyping_ge Hsub Hsub0;
			join_subtyping_eq Hsubi Hsub1 |
			join_subtyping_eq Hsub Hsub0 |
			join_subtyping_eq Hsub0 Hsub |
			idtac
		];
		first [
			construct_ais_typing;
			eapply construct_ai_const_I32 |
			resolve_subtyping;
			construct_ais_typing;
			auto
		]
	].
	- (* Step_pure *) eapply t_pure_preservation; eauto.
	- (* Step_read *) eapply t_read_preservation; eauto.
	{ (* Context Seq *)
		admit.
	}
	{ (* Context Label *) 
		typing_inversion HType.
		unfold_principal_typing Hai; extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		econstructor; eauto.
	}
	{ (* Context Frame *)

		typing_inversion HType.
		unfold_principal_typing Hai; extract_premise.
		admit.

(*

		inversion H1; subst.
		inversion H2; subst.
		destruct r_v_f.
		(* inversion HIT1; inversion HIT2; subst. *)

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		econstructor; eauto.
		eapply mk_Thread_ok with (v_C := {|
			C_TYPES := [];
			C_FUNCS := [];
			C_GLOBALS := [];
			C_TABLES := [];
			C_MEMS := [];
			C_ELEMS := [];
			C_DATAS := [];
			C_LOCALS := v_t;
			C_LABELS := [];
			C_RETURN := None
			|} @@ v_C1).
		{
			destruct v_f''.
			eapply mk_Frame_ok; eauto.
			eapply reduce_inst_unchanged in HReduce.
			simpl in HReduce; subst.
			eapply module_inst_typing_extension; eauto.
			eapply vals_typing_extension; eauto.
		}
		eapply IHHReduce; eauto; simpl.
		- eapply module_inst_typing_extension; eauto.
		- eapply inst_t_context_local_empty in H.
		  rewrite H.
		  rewrite /_append /Append_List_.
		  simpl.
		  by rewrite app_nil_r.
		- resolve_inst_match. *)
	}
	(* The rest are all SIMD instructions *)
	admit. admit. admit. admit. admit.
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
		assert (Vals_ok store2 locals2 v_t1).
		apply (t_preservation_vs_type) with
			(C := v_C0)
			(C' :=
				{|
				C_TYPES := v_functype0;
				C_FUNCS := v_functype';
				C_GLOBALS := v_globaltype0;
				C_TABLES := v_tabletype0;
				C_MEMS := v_memtype0;
				C_ELEMS := v_reftype0;
				C_DATAS := [];
				C_LOCALS := v_t1;
				C_LABELS := [];
				C_RETURN := None
				|})
			(C'' := v_C0)
			(t1s := [])
			(t2s := (mk_list valtype v_t))
			(s := store1)
			(f := frame1)
			(f' := {| F_LOCALS := locals2; F_MODULE := module2 |})
			(ais := l)
			(ais' := l0)
			; eauto;
		try (subst; solve [
			auto |
			simpl; try rewrite cats0; auto |
			resolve_inst_match |
			subst; rewrite /_append /Append_context /_append_context
			/_append /Append_List_ (app_nil_r v_t1) in HAIs1; simpl in HAIs1; auto
		]).

		eapply (mk_Frame_ok store2 locals2 v_moduleinst v_C0 v_t1); eauto;
		by eapply Forall2_length in H0.
	}
	subst.

	(* Actual Typing proof *)
	eapply t_preservation_type; eauto.
	simpl in *.
	by rewrite /_append /Append_List_ app_nil_r /=.
	by resolve_inst_match.
Qed.