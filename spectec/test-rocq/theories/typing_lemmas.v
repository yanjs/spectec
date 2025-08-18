From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
Require Import Stdlib.Program.Equality.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics subtyping.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

Definition fun_nat__u32 : nat -> u32 := mk_uN 32.
Definition fun_u32__nat : u32 -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__u32 : nat >-> u32.
Coercion fun_u32__nat : u32 >-> nat.

Definition fun_nat__labelidx : nat -> labelidx := mk_uN 32.
Definition fun_labelidx__nat : labelidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__labelidx : nat >-> labelidx.
Coercion fun_labelidx__nat : labelidx >-> nat.

Definition fun_nat__localidx : nat -> localidx := mk_uN 32.
Definition fun_localidx__nat : localidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__localidx : nat >-> localidx.
Coercion fun_localidx__nat : localidx >-> nat.

Definition fun_nat__globalidx : nat -> globalidx := mk_uN 32.
Definition fun_globalidx__nat : globalidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__globalidx : nat >-> globalidx.
Coercion fun_globalidx__nat : globalidx >-> nat.

Definition fun_nat__memidx : nat -> memidx := mk_uN 32.
Definition fun_memidx__nat : memidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__memidx : nat >-> memidx.
Coercion fun_memidx__nat : memidx >-> nat.


Definition fun_nat__tableidx : nat -> tableidx := mk_uN 32.
Definition fun_tableidx__nat : tableidx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__tableidx : nat >-> tableidx.
Coercion fun_tableidx__nat : tableidx >-> nat.

Definition fun_nat__idx : nat -> idx := mk_uN 32.
Definition fun_idx__nat : idx -> nat := fun x => match x with
    |  mk_uN v => v
	end.
Coercion fun_nat__idx : nat >-> idx.
Coercion fun_idx__nat : idx >-> nat.

Definition fun_res_list__list :
forall T, res_list T -> list T := fun _ x => match x with
	| mk_list l => l
end.
Definition fun_list__res_list : forall T, list T -> res_list T := fun T => mk_list T.
Coercion fun_res_list__list : res_list >-> list.
Coercion fun_list__res_list : list >-> res_list.

Definition functype_from_lists (t1s t2s : list valtype) : functype :=
  mk_functype t1s t2s.

Definition prepend_label (v_C: context) v_t :=
({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := [(mk_list _ v_t)]; C_RETURN := None |} @@ v_C).

Notation "tf1 :-> tf2" :=
(mk_functype (mk_list _ tf1) (mk_list _ tf2)) (at level 40).

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


(*

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
	upd_label v_C (_append lab (C_LABELS v_C)) = _append {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := [];
	C_DATAS := []; C_LOCALS := []; C_LABELS := lab; C_RETURN := None |} v_C.
Proof.
	move => v_C lab. reflexivity.
Qed.

Lemma upd_local_is_same_as_append: forall v_C loc,
	upd_local v_C (_append loc (C_LOCALS v_C))  = _append {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := [];
	C_DATAS := []; C_LOCALS := loc; C_LABELS := []; C_RETURN := None |} v_C.
Proof.
	move => v_C loc. reflexivity.
Qed.

Lemma upd_local_return_is_same_as_append: forall v_C loc ret,
	upd_local_return v_C (_append loc (C_LOCALS v_C)) (_append ret (C_RETURN v_C)) 
	= upd_return (upd_local v_C (_append loc (C_LOCALS v_C))) (_append ret (C_RETURN ((upd_local v_C (_append loc (C_LOCALS v_C)))))).
Proof. reflexivity. Qed.


Lemma upd_return_is_same_as_append: forall v_C ret,
	upd_return v_C (_append ret (C_RETURN v_C)) = _append {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := [];
	C_DATAS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := ret |} v_C.
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

(*
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
*) *)
(*
Lemma instrs_empty_same_type: forall C t1 t2,
	Instrs_ok C [] (mk_functype t1 t2) ->
	t1 = t2.
Proof.
	move => C t t2 H. gen_ind_subst H => //.
	- (* Seq *) symmetry in Enil. apply app_cons_not_nil in Enil. exfalso. apply Enil.
	- (* Sub *)
	    eapply IHInstrs_ok; eauto.
		reflexivity.
	- (* Frame *) f_equal. by eapply IHInstrs_ok.
Qed.

Lemma admin_empty_same_type: forall v_S C t1 t2,
	Admin_instrs_ok v_S C [] (functype_from_lists t1 t2) ->
	t1 = t2.
Proof.
	move => v_S C t t2 H. gen_ind_subst H => //.
		- (* Seq *) symmetry in Enil. apply app_cons_not_nil in Enil. exfalso. apply Enil. 
		- (* Frame *) f_equal. by eapply IHAdmin_instrs_ok.
		- (* Instrs *) apply (instrs_empty_same_type C). apply map_eq_nil in Enil. subst. apply H.
Qed.

Lemma val_is_same_as_admin_const: forall v_S v_C (v : val) ts,
	Admin_instr_ok v_S v_C (v : admininstr) ts ->
	exists v_valtype v_val_, Admin_instr_ok v_S v_C (AI_CONST v_valtype v_val_) ts.
Proof. 
	move => v_S v_C val ts HType.
	induction val.
	exists v_valtype, v_val_. done.
Qed. *)


Notation "tf1 :-> tf2" :=
(mk_functype (mk_list _ tf1) (mk_list _ tf2)) (at level 40).

Lemma admin_weakening_empty_both: forall v_S v_C v_ais ts,
    Admin_instrs_ok v_S v_C v_ais ( nil :-> nil ) ->
    Admin_instrs_ok v_S v_C v_ais ( ts :-> ts ).
Proof.
  move => v_S v_C v_ais ts HType.
  assert (Admin_instrs_ok v_S v_C v_ais ((ts ++ []) :-> (ts ++ []))); first by apply AIs_ok_frame.
  by rewrite cats0 in H.
Qed.

(*
Lemma instrs_weakening_empty_both: forall v_C v_ais ts,
    Instrs_ok v_C v_ais (functype_from_lists [::] [::]) ->
    Instrs_ok v_C v_ais (functype_from_lists ts ts).
Proof.
  move => v_C v_ais ts HType.
  assert (Instrs_ok v_C v_ais (functype_from_lists (ts ++ [::]) (ts ++ [::]))); first by apply instrs_frame.
  by rewrite cats0 in H.
Qed.

Lemma admin_instrs_weakening_empty_1: forall v_S v_C instrs ts t2s,
    Admin_instrs_ok v_S v_C instrs (functype_from_lists [::] t2s) ->
    Admin_instrs_ok v_S v_C instrs (functype_from_lists ts (ts ++ t2s)).
Proof.
  move => v_S v_C instrs ts t2s HType.
  assert (Admin_instrs_ok v_S v_C instrs (functype_from_lists (ts ++ [::]) (ts ++ t2s))); first by apply AIs_ok_frame.
  by rewrite cats0 in H.
Qed.

Lemma instrs_weakening_empty_1: forall v_C instrs ts t2s,
    Instrs_ok v_C instrs (functype_from_lists [::] t2s) ->
    Instrs_ok v_C instrs (functype_from_lists ts (ts ++ t2s)).
Proof.
  move => v_C instrs ts t2s HType.
  assert (Instrs_ok v_C instrs (functype_from_lists (ts ++ [::]) (ts ++ t2s))); first by apply instrs_frame.
  by rewrite cats0 in H.
Qed.

Lemma admin_instr_weakening_empty_1: forall v_S v_C instr ts t2s,
    Admin_instr_ok v_S v_C instr (functype_from_lists [::] t2s) ->
    Admin_instr_ok v_S v_C instr (functype_from_lists ts (ts ++ t2s)).
Proof.
  move => v_S v_C instr ts t2s HType.
  assert (Admin_instr_ok v_S v_C instr (functype_from_lists (ts ++ [::]) (ts ++ t2s))); first by apply AI_ok_weakening.
  by rewrite cats0 in H.
Qed.

Lemma admin_instr_weakening_empty_2: forall v_S v_C instr ts t1s,
    Admin_instr_ok v_S v_C instr (functype_from_lists t1s []) ->
    Admin_instr_ok v_S v_C instr (functype_from_lists (ts ++ t1s) (ts)).
Proof.
  move => v_S v_C instr ts t1s HType.
  assert (Admin_instr_ok v_S v_C instr (functype_from_lists (ts ++ t1s) (ts ++ []))); first by apply AI_ok_weakening.
  by rewrite cats0 in H.
Qed.
*)

Lemma instrs_composition_typing_single: forall v_C v_instrs v_instr t1s t2s,
	Instrs_ok v_C (v_instrs ++ [v_instr]) ( t1s :-> t2s ) ->
	exists t3s, Instrs_ok v_C v_instrs ( t1s :-> t3s ) /\
				Instrs_ok v_C [v_instr] ( t3s :-> t2s ).
Proof.
	move => v_C v_instrs v_instr t1s t2s HType.
	dependent induction HType.
	- destruct_list_eq x.
	- destruct_list_eq x; subst.
	  exists v_t_2.
	  split; auto.
	  eapply (instrs_ok_seq _ [] v_instr v_t_2 t2s v_t_2).
	  + rewrite -(cats0 v_t_2).
	    eapply (instrs_ok_frame _ _ v_t_2 [] []).
		apply instrs_ok_empty.
	  + auto.
	- specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists t3s.
	  split;
	  eapply instrs_ok_sub; eauto;
      apply resulttype_sub_refl.
	- specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (v_t ++ t3s).
	  split;
	  eapply instrs_ok_frame; eauto.
Qed.

Lemma ais_composition_typing_single: forall v_S v_C v_ais v_ai t1s t2s,
	Admin_instrs_ok v_S v_C (v_ais ++ [v_ai]) ( t1s :-> t2s ) ->
	exists t3s, Admin_instrs_ok v_S v_C v_ais ( t1s :-> t3s ) /\
				Admin_instrs_ok v_S v_C [v_ai] ( t3s :-> t2s ).
Proof.
	move => v_S v_C v_ais v_ai t1s t2s HType.
	dependent induction HType.
	{ (* empty *)
	  destruct_list_eq x.
	}
	{ (* seq *)
	  exists v_t_2.
	  destruct_list_eq x; subst.
	  split.
	  + auto.
	  + assert ( [v_ai] = [] ++ [v_ai] ). { by rewrite cat0s. }
	    assert ( v_t_2 = v_t_2 ++ [] ). { by rewrite cats0. }
	    rewrite H0.
	    eapply (AIs_ok_seq) with (v_t_2 := v_t_2).
		* rewrite H1.
		  eapply AIs_ok_frame. by apply AIs_ok_empty.
		* auto.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists t3s.
	  split; eapply AIs_ok_sub; eauto; by apply resulttype_sub_refl.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (v_t ++ t3s).
	  split; by eapply AIs_ok_frame.
	}
	{ (* instrs *)
	  move: v_ais v_ai x t1s t2s H.
	  induction v_instr using rev_ind;
	  move => v_ais v_ai H t1s t2s Hinstr.
	  + inversion H.
	    destruct_list_eq H1.
	  + rewrite map_last in H.
	    destruct_list_eq H; subst.
		apply instrs_composition_typing_single in Hinstr as [t3s [H1 H2]].
	    exists t3s.
		split.
		* eapply AIs_ok_instrs; auto.
		* assert ([ (x: admininstr)] =
		  ListDef.map [eta fun_coec_instr__admininstr] [ x]).
		  { auto. }
		  rewrite H.
		  eapply AIs_ok_instrs.
		  auto.
	}
Qed.

Lemma instrs_empty_typing : forall v_C t1s t2s,
	Instrs_ok v_C ([]) ( t1s :-> t2s ) <->
	( t1s <ts: t2s ).
Proof.
  move => v_C t1s t2s.
  split.
  - move => Hempty.
    dependent induction Hempty; subst.
	+ apply resulttype_sub_refl.
	+ destruct_list_eq x.
	+ eapply resulttype_sub_trans.
	apply H.
	eapply resulttype_sub_trans.
	apply IHHempty; auto.
	apply H0.
	eapply resulttype_sub_app.
	apply resulttype_sub_refl.
	apply IHHempty; auto.
  - move: t1s.
    move => t1s H.
	eapply (instrs_ok_sub _ _ _ _ t2s t2s).
	+ rewrite -(cats0 t2s).
	  apply instrs_ok_frame.
	  apply instrs_ok_empty.
	  apply H.
	  apply resulttype_sub_refl.
Qed.

Lemma ais_empty_typing : forall v_S v_C t1s t2s,
	Admin_instrs_ok v_S v_C ([]) ( t1s :-> t2s ) <->
	( t1s <ts: t2s ).
Proof.
  move => v_S v_C t1s t2s.
  split.
  {
	move => Hempty.
	dependent induction Hempty; subst.
	+ apply resulttype_sub_refl.
	+ destruct_list_eq x.
	+ specialize (IHHempty _ _ erefl erefl). 
	  eapply resulttype_sub_trans.
	  eapply H.
	  eapply resulttype_sub_trans.
	  eapply IHHempty.
	  eapply H0.
	+ eapply resulttype_sub_app.
	  apply resulttype_sub_refl.
	  apply IHHempty; auto.
	+ destruct v_instr.
	  * by apply instrs_empty_typing in H.
	  * discriminate.
  }
  {
	move => Hsub.
	assert ([] = (ListDef.map [eta fun_coec_instr__admininstr] [])). { auto. }
	rewrite H.
    apply AIs_ok_instrs.
	by apply instrs_empty_typing.
  }
Qed.


Definition ai_principal_typing (v_S: store) (v_C: context) v_ai v_ft : Prop :=
match v_ai with
	| AI_NOP => v_ft = ([] :-> [])
	| AI_UNREACHABLE => True
	| AI_DROP => exists t1, v_ft = ([t1] :-> [])
	| (AI_SELECT (Some [v_t])) => v_ft = ([v_t; v_t; VALTYPE_I32] :-> [v_t])
	| (AI_SELECT None) => exists (t t': valtype),
		v_ft = ([t; t; VALTYPE_I32] :-> [t]) /\
		t <tv: t' /\
		((exists nt: numtype, t' = nt) \/ (exists vt: vectype, t' = vt))
	| (AI_SELECT _) => False
	| (AI_BLOCK v_bt v_instr) =>
	    exists t t',
	    v_ft = (t :-> t') /\
		(Blocktype_ok v_C v_bt (t :-> t')) /\
		(Instrs_ok (prepend_label v_C t') v_instr (t :-> t'))
	(*| (AI_LOOP v_0 v_1)*)
	| (AI_IFELSE v_bt v_instrs1 v_instrs2) => exists (t t': seq valtype),
	  	v_ft = ((t ++ [VALTYPE_I32]) :-> t') /\
		(Blocktype_ok v_C v_bt (t :-> t')) /\
		Instrs_ok (prepend_label v_C t') v_instrs1 (t :-> t') /\
		Instrs_ok (prepend_label v_C t') v_instrs2 (t :-> t')
	| (AI_BR v_l) =>
	  exists t t' v_t,
	    v_ft = (t ++ v_t) :-> t' /\
	    ((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C))) /\
		((fun_proj_list_0 valtype (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l))) = v_t)
	| (AI_BR_IF v_l) =>
	  exists t,
	    v_ft = ((t ++ [VALTYPE_I32]) :-> t) /\
	    ((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C))) /\
		((fun_proj_list_0 valtype (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l))) = t)
	| (AI_BR_TABLE v_l v_l') =>
      exists t t' v_t,
	    v_ft = ((t ++ v_t ++ [VALTYPE_I32]) :-> t') /\
	    List.Forall (fun (v_l : labelidx) => ((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C)))) (v_l) /\
		List.Forall (fun (v_l : labelidx) => (Resulttype_sub (mk_list _ v_t) (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l)))) (v_l) /\
		((fun_proj_uN_0 32 v_l') < (List.length (C_LABELS v_C))) /\
		(Resulttype_sub (mk_list _ v_t) (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l')))
	(*| (AI_CALL v_0)
	| (AI_CALL_INDIRECT v_0 v_1) *)
	| AI_RETURN =>
	  exists t t' v_t,
	    v_ft = ((t ++ v_t) :-> t') /\
		((C_RETURN v_C) = (Some (mk_list _ v_t))) /\
		Instr_ok v_C instr_RETURN ((t ++ v_t) :-> t')
	| (AI_CONST v_nt _) =>
	  v_ft = ([] :-> ([v_nt: valtype]))
	| (AI_UNOP v_nt _) =>
	  v_ft = ([v_nt: valtype] :-> [v_nt: valtype])
	| (AI_BINOP v_nt _) =>
	  v_ft = ([v_nt: valtype; v_nt: valtype] :-> [v_nt: valtype])
	| (AI_TESTOP v_nt _) =>
	  v_ft = ([v_nt: valtype] :-> [VALTYPE_I32])
	| (AI_RELOP v_nt v_1) =>
	  v_ft = ([v_nt: valtype; v_nt: valtype] :-> [VALTYPE_I32])
	| (AI_CVTOP v_nt_1 v_nt_2 _) =>
	  v_ft = ([v_nt_2: valtype] :-> [v_nt_1: valtype])
	(*| (AI_EXTEND v_0 v_1) *)
	| (AI_VCONST (v_vectype) _ ) =>
	  v_ft = ([] :-> [v_vectype : valtype])
	(*| (AI_VVUNOP v_0 v_1)
	| (AI_VVBINOP v_0 v_1)
	| (AI_VVTERNOP v_0 v_1)
	| (AI_VVTESTOP v_0 v_1)
	| (AI_VUNOP v_0 v_1)
	| (AI_VBINOP v_0 v_1)
	| (AI_VTESTOP v_0 v_1)
	| (AI_VRELOP v_0 v_1)
	| (AI_VSHIFTOP v_0 v_1)
	| (AI_VBITMASK v_0)
	| (AI_VSWIZZLE v_0)
	| (AI_VSHUFFLE v_0 v_1)
	| (AI_VSPLAT v_0)
	| (AI_VEXTRACT_LANE v_0 v_1 v_2)
	| (AI_VREPLACE_LANE v_0 v_1)
	| (AI_VEXTUNOP v_0 v_1 v_2)
	| (AI_VEXTBINOP v_0 v_1 v_2)
	| (AI_VNARROW v_0 v_1 v_2)
	| (AI_VCVTOP v_0 v_1 v_2)*)
	| (AI_REF_NULL (v_rt)) =>
	  v_ft = ([] :-> [v_rt : valtype])
	(*| (AI_REF_FUNC v_0)*)
	| AI_REF_IS_NULL =>
	  exists v_rt,
	  v_ft = ([v_rt] :-> [VALTYPE_I32])
	(*| (AI_LOCAL_GET v_0)
	| (AI_LOCAL_SET v_0)
	| (AI_LOCAL_TEE v_0)
	| (AI_GLOBAL_GET v_0)
	| (AI_GLOBAL_SET v_0)
	| (AI_TABLE_GET v_0)
	| (AI_TABLE_SET v_0)
	| (AI_TABLE_SIZE v_0)
	| (AI_TABLE_GROW v_0)
	| (AI_TABLE_FILL v_0)
	| (AI_TABLE_COPY v_0 v_1)
	| (AI_TABLE_INIT v_0 v_1)
	| (AI_ELEM_DROP v_0)
	| (AI_LOAD v_0 v_1 v_2)
	| (AI_STORE v_0 v_1 v_2)
	| (AI_VLOAD v_0 v_1 v_2)
	| (AI_VLOAD_LANE v_0 v_1 v_2 v_3)
	| (AI_VSTORE v_0 v_1)
	| (AI_VSTORE_LANE v_0 v_1 v_2 v_3)
	| AI_MEMORY_SIZE
	| AI_MEMORY_GROW
	| AI_MEMORY_FILL
	| AI_MEMORY_COPY
	| (AI_MEMORY_INIT v_0)
	| (AI_DATA_DROP v_0) *)
	| (AI_REF_FUNC_ADDR v_funcaddr) =>
	  exists v_functype,
	  v_ft = ([] :-> [VALTYPE_FUNCREF]) /\
	  (Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_functype))
	| (AI_REF_HOST_ADDR _) =>
	  v_ft = ([] :-> [VALTYPE_EXTERNREF])
	(*| AI_CALL_ADDR (v_funcaddr : funcaddr) : admininstr *)
	| (AI_LABEL_ v_n v_instrs v_ais) =>
	  exists t t',
	  v_ft = ([] :-> t') /\
	  (Instrs_ok v_C v_instrs (t :-> t')) /\
	  (Admin_instrs_ok v_S (prepend_label v_C t) v_ais ([] :-> t')) /\
	  (v_n = (length t))
	| (AI_FRAME_ v_n v_F v_ais) =>
	  exists t,
	    v_ft = ([] :-> t) /\
	    (Thread_ok v_S (Some (mk_list _ t)) v_F v_ais (mk_list _ t)) /\
		(v_n = (List.length t))
	| AI_TRAP => True
	| _ => True
end.

(* v_ft must be the subtype of v_instr's type *)
Definition instr_principal_typing (v_C : context) v_instr v_ft : Prop :=
ai_principal_typing default_val v_C (v_instr : admininstr) v_ft.

Lemma instr_typing_inversion: forall (v_C: context) v_instr t1s t2s,
  Instr_ok v_C v_instr (t1s :-> t2s) ->
  instr_principal_typing v_C v_instr (t1s :-> t2s).
Proof.
	move=> v_C v_instr t1s t2s HType.
	inversion HType; subst.
	all: unfold instr_principal_typing;
		unfold ai_principal_typing;
		unfold fun_coec_instr__admininstr.
	all: try exact.
	all: try repeat eexists; eauto.
	{
	 (* SELECT *)
	  solve [destruct_disjunctions;
	  repeat eexists; eauto].
	}
Qed.

Lemma ai_typing_inversion: forall (v_S: store) (v_C: context) v_ai t1s t2s,
	Admin_instr_ok v_S v_C v_ai (t1s :-> t2s) ->
	exists t1s' t2s',
	ai_principal_typing v_S v_C v_ai (t1s' :-> t2s') /\
	((t1s' :-> t2s') <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C v_ai t1s t2s.
	move => HType.
	dependent induction HType.
	{ (* instr *)
		destruct v_instr.
		all: unfold ai_principal_typing;
		unfold fun_coec_instr__admininstr.
		all: inversion H; subst.
		all: do 2 eexists.
		all: split;
		[
			first [
				solve exact
			|
				solve [simpl; eauto]
			|
				solve [destruct_disjunctions; repeat eexists; eauto]
			]
		|
			solve [
				exists []; do 3 eexists;
				split; [|split; [|split; [|split]]];
				try apply resulttype_sub_refl;
				simpl; try exact
			]
	  	].
	}
	{ (* trap *)
	  exists t1s, t2s.
	  split.
	  - unfold ai_principal_typing; exact.
	  - apply instrtype_sub_refl.
	}
	{ (* ref_extern *)
	  exists [], [VALTYPE_EXTERNREF].
	  split.
	  - unfold ai_principal_typing; auto.
	  - apply instrtype_sub_refl. 
	}
	{ (* ref *)
	  exists [], [VALTYPE_FUNCREF].
	  split.
	  - unfold ai_principal_typing;
	    do 2 eexists; eauto.
	  - apply instrtype_sub_refl.
	}
	{ (* call_addr *) (* TODO *)
	  eexists _, _.
	  split.
	  - unfold ai_principal_typing; exact.
	  - apply instrtype_sub_refl.
	}
	{ (* label *) (* TODO *)
	  eexists _, _.
	  split.
	  - unfold ai_principal_typing; repeat eexists; eauto.
	  - apply instrtype_sub_refl.
	}
	{ (* frame *) (* TODO *)
	  eexists _, _.
	  split.
	  - unfold ai_principal_typing.
		eexists.
		split; [|split]; eauto.
	  - apply instrtype_sub_refl.
	}
	{ (* weakening *)
		specialize (IHHType _ _ erefl) as [t1' [t2' [Hpt His]]].
		exists t1', t2'.
		split. exact.
		eapply instrtype_sub_trans.
		eapply His.
		unfold instrtype_sub.
		eexists
		(v_t'),
		(v_t),
		(v_t'_1),
		(v_t'_2).
		split; [|split; [|split; [|split]]]; auto.
	}
Qed.

Lemma instrs_single_typing_inversion: forall (v_C: context) v_instr t1s t2s,
Instrs_ok v_C [v_instr] (t1s :-> t2s) ->
exists t1s_sup t2s_sub,
	Instr_ok v_C v_instr (t1s_sup :-> t2s_sub) /\
	(t1s_sup :-> t2s_sub) <ti: (t1s :-> t2s).
Proof.
	move=> v_C v_instr t1s t2s HType.
	dependent induction HType.
	{ (* seq *)
	  destruct_list_eq x; subst.
	  apply instrs_empty_typing in HType.
	  exists v_t_2, t2s.
	  split. auto.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split. auto.
	  by apply resulttype_sub_refl.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split. by apply H.
	  by apply H0.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists v_t, v_t, v_t_1, v_t_2.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split; by apply resulttype_sub_refl.
	}
Qed.

Lemma ais_single_typing_inversion' : forall (v_S: store) (v_C: context) v_ai t1s t2s,
	Admin_instrs_ok v_S v_C [v_ai] (t1s :-> t2s) ->
	Admin_instr_ok v_S v_C v_ai (t1s :-> t2s).
Proof.
	move=> v_S v_C v_ai t1s t2s HType.
	dependent induction HType.
	- destruct_list_eq x; subst.
	  eapply ais_empty_typing in HType.
	  eapply (AI_ok_weakening _ _ _ [] _ []).
	  eapply H.
	  eapply resulttype_sub_refl.
	  eapply HType.
	  eapply resulttype_sub_refl.
	- eapply (AI_ok_weakening _ _ _ [] _ []); eauto.
	  eapply resulttype_sub_refl.
	- eapply (AI_ok_weakening _ _ _ v_t _ v_t); eauto;
	  eapply resulttype_sub_refl.
	- destruct v_instr. discriminate.
	  simpl in x.
	  destruct_list_eq x; subst.
	  destruct v_instr. 2: discriminate.
	  eapply instrs_single_typing_inversion in H
	    as [t1s_sup [t2s_sub [Hi Hsub]]].
	  unfold instrtype_sub in Hsub.
	  destruct Hsub as [ts_sub [ts [ts1 [ts2 [
		H1 [H2 [H3 [H4 H5]]]
	  ]]]]]; subst.
	  eapply (AI_ok_weakening _ _ _ ); eauto.
	  eapply AI_ok_instr.
	  eapply Hi.
Qed.



Lemma ais_single_typing_inversion: forall (v_S: store) (v_C: context) v_ai t1s t2s,
Admin_instrs_ok v_S v_C [v_ai] (t1s :-> t2s) ->
exists t1s_sup t2s_sub,
	ai_principal_typing v_S v_C v_ai (t1s_sup :-> t2s_sub) /\
	(t1s_sup :-> t2s_sub) <ti: (t1s :-> t2s).
Proof.
	move=> v_S v_C v_ai t1s t2s HType.
	dependent induction HType.
	{ (* seq *)
	  destruct_list_eq x; subst.
	  apply ais_empty_typing in HType.
	  eapply ai_typing_inversion in H as [t1s' [t2s' [Hpt Hsub]]].
	  exists (t1s'), (t2s').
	  split. auto.
	  eapply instrtype_sub_trans. eapply Hsub.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split. auto.
	  by apply resulttype_sub_refl.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists [], [], t1s, t2s.
	  split; auto.
	  split; auto.
	  split; auto.
	  by apply resulttype_sub_refl.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ erefl erefl) as [t1s_sup [t2s_sub [Hpt Hsub]]].
	  exists t1s_sup, t2s_sub.
	  split. auto.
	  eapply instrtype_sub_trans.
	  apply Hsub.
	  unfold instrtype_sub.
	  exists v_t, v_t, v_t_1, v_t_2.
	  split. auto.
	  split. auto.
	  split. by apply resulttype_sub_refl.
	  split; by apply resulttype_sub_refl.
	}
	{ (* instrs *)
	  destruct v_instr. discriminate x.
	  simpl in x.
	  destruct_list_eq x;
	  apply map_eq_nil in x_body;
	  subst.

	  eapply instrs_single_typing_inversion in H
	    as [t1s_sup [t2s_sub [Hi H1]]].
	  eapply instr_typing_inversion in Hi.
	  unfold instr_principal_typing in Hi.
	  exists t1s_sup, t2s_sub.
	  split. 2: auto.
	  destruct i;
	  auto.
	}
Qed.

Lemma instrs_seq_typing_inversion: forall (v_C: context) v_instrs v_instr t1s t2s,
Instrs_ok v_C (v_instrs ++ [v_instr]) (t1s :-> t2s) ->
exists t3s, Instrs_ok v_C v_instrs (t1s :-> t3s) /\
	Instrs_ok v_C [v_instr] (t3s :-> t2s).
Proof.
	move=> v_C v_instrs v_instr t1s t2s HType.
	dependent induction HType.
	{ (* empty *) destruct_list_eq x. }
	{ (* seq *)
	  destruct_list_eq x; subst.
	  exists v_t_2.
	  split. auto.
	  rewrite -(cat0s [v_instr]).
	  eapply instrs_ok_seq.
	  apply instrs_empty_typing.
	  apply resulttype_sub_refl. auto.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists t3s. split.
	  - eapply instrs_ok_sub.
	    eapply H1. eauto. apply resulttype_sub_refl.
	  - eapply instrs_ok_sub.
	    eapply H2. apply resulttype_sub_refl. eauto.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (v_t ++ t3s). split.
	  - eapply instrs_ok_frame. auto.
	  - eapply instrs_ok_frame. auto.
	}
Qed.

Lemma ais_seq_typing_inversion: forall (v_S: store) (v_C: context) v_ais v_ai t1s t2s,
Admin_instrs_ok v_S v_C (v_ais ++ [v_ai]) (t1s :-> t2s) ->
exists t3s, Admin_instrs_ok v_S v_C v_ais (t1s :-> t3s) /\
	Admin_instrs_ok v_S v_C [v_ai] (t3s :-> t2s).
Proof.
	move=> v_S v_C v_ais v_ai t1s t2s HType.
	dependent induction HType.
	{ (* empty *) destruct_list_eq x. }
	{ (* seq *)
	  destruct_list_eq x; subst.
	  exists v_t_2.
	  split. auto.
	  rewrite -(cat0s [v_ai]).
	  eapply AIs_ok_seq.
	  - apply ais_empty_typing.
	    apply resulttype_sub_refl.
	  - auto.
	}
	{ (* sub *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (t3s).
	  split; eapply AIs_ok_sub; eauto; apply resulttype_sub_refl.
	}
	{ (* frame *)
	  specialize (IHHType _ _ _ _ erefl erefl) as [t3s [H1 H2]].
	  exists (v_t ++ t3s).
	  split; eapply AIs_ok_frame; auto.
	}
	{ (* instrs *)
	  destruct v_instr using rev_ind.
	  - simpl in x. destruct_list_eq x.
	  - rewrite map_last in x.
	    destruct_list_eq x; subst.
		eapply instrs_seq_typing_inversion in H as [t3s [H1 H2]].
		exists t3s. split.
		- eapply AIs_ok_instrs. auto.
	    - assert (ListDef.map [eta fun_coec_instr__admininstr] [x0] =
		  [fun_coec_instr__admininstr x0]).
		  { auto. }
		  rewrite -H.
		  eapply AIs_ok_instrs. auto.
	}
Qed.

Ltac do_instr_typing_inversion H :=
  lazymatch type of H with
  | Instr_ok _ ?v_instr _ =>
    let Hpt := fresh "Hpt" in
    eapply instr_typing_inversion in H as Hpt;
	clear H
  | _ => idtac
end.

Ltac do_instrs_typing_inversion H :=
  lazymatch type of H with
  | Instrs_ok _ [] _ =>
    eapply instrs_empty_typing in H
  | Instrs_ok _ [?v_instr] ( ?t1s :-> ?t2s ) =>
    let t1s_sup := fresh t1s "_sup" in
	let t2s_sub := fresh t2s "_sub" in
	let Hinstr := fresh "Hinstr" in
	let Hsub := fresh "Hsub" in
    eapply instrs_single_typing_inversion in H
	  as [t1s_sup [t2s_sub [Hinstr Hsub]]]
  | Instrs_ok _ [?v_instr1; ?v_instr2] _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (instrs_seq_typing_inversion _ [v_instr1] v_instr2) in H
	  as [t3s [H1 H2]]
  | Instrs_ok _ (?v_instrs ++ [?v_instr]) _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (instrs_seq_typing_inversion _ v_instrs v_instr) in H
	  as [t3s [H1 H2]];
	do_instrs_typing_inversion H1
  | Instrs_ok _ _ (_ :: _) _ =>
    repeat rewrite -(cat1s _ (_ :: _)) in H;
	repeat rewrite !catA in H;
	do_instrs_typing_inversion H
  | _ => idtac
  end.

Ltac do_ai_typing_inversion H :=
  lazymatch type of H with
  | Admin_instr_ok _ _ _ _ =>
    let Hpt := fresh "Hpt" in
	let t1s' := fresh "t1s'" in
	let t2s' := fresh "t2s'" in
	let Hsub := fresh "Hsub" in
    eapply ai_typing_inversion in H as [t1s' [t2s' [Hpt Hsub]]]
  | _ => idtac
  end.

Ltac do_ais_typing_inversion H :=
  lazymatch type of H with
  | Admin_instrs_ok _ _ [] _ =>
    eapply ais_empty_typing in H
  | Admin_instrs_ok _ _ [?v_ai] ( ?t1s :-> ?t2s ) =>
    let t1s_sup := fresh t1s "_sup" in
	let t2s_sub := fresh t2s "_sub" in
	let Hai := fresh "Hai" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_typing_inversion in H
	  as [t1s_sup [t2s_sub [Hai Hsub]]]
  | Admin_instrs_ok _ _ [?v_ai1; ?v_ai2] _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (ais_seq_typing_inversion _ _ [v_ai1] v_ai2) in H
	  as [t3s [H1 H2]]
  | Admin_instrs_ok _ _ (?v_ais ++ [?v_ai]) _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
    eapply (ais_seq_typing_inversion _ _ v_ais v_ai) in H
	  as [t3s [H1 H2]];
	do_ais_typing_inversion H1
  | Admin_instrs_ok _ _ (_ :: _) _ =>
    repeat rewrite -(cat1s _ (_ :: _)) in H;
	repeat rewrite !catA in H;
	do_ais_typing_inversion H
  | _ => idtac
  end.

Ltac typing_inversion H :=
  destruct_functypes;
  lazymatch type of H with
  | Admin_instrs_ok _ _ _ _ =>
    do_ais_typing_inversion H
  | Admin_instr_ok _ _ _ _ =>
    do_ai_typing_inversion H
  | Instrs_ok _ _ _ =>
    do_instrs_typing_inversion H
  | Instr_ok _ _ _ =>
    do_instr_typing_inversion H
  | _ => idtac
end.

Lemma ai_val_principal_typing_inversion: forall (v_S: store) (v_C: context) (v_val: wasm.val) t1s t2s,
ai_principal_typing v_S v_C (v_val: admininstr) (t1s :-> t2s) ->
exists v_t,
	([] = t1s) /\ ([v_t] = t2s).
Proof.
  move=> v_S v_C v_val t1s t2s HType.
  destruct v_val;
  [
	exists v_numtype |
	exists v_vectype |
	exists v_reftype |
	exists VALTYPE_FUNCREF |
	exists VALTYPE_EXTERNREF
  ].
  all: unfold ai_principal_typing, fun_coec_val__admininstr in HType; 
  inversion HType; auto.
  destruct HType as [v_functype [H1 H2]].
  inversion H1; auto.
Qed.

Ltac unfold_principal_typing H :=
  unfold instr_principal_typing in H;
  unfold fun_coec_instr__admininstr in H;
  unfold ai_principal_typing in H;
  unfold fun_coec_val__admininstr in H.

Ltac unfold_instrtype_sub H :=
  destruct_functypes;
  match type of H with
  | ((?ts11 :-> ?ts12) <ti: (?ts21 :-> ?ts22)) =>
	let ts := fresh "ts" in
	let ts_sub := fresh ts "_sub" in
	let ts11_sub := fresh "ts11_sub" in
	let ts12_sup := fresh "ts12_sup" in
	let H1 := fresh "H" in
	let H2 := fresh "H" in
	let Hsub1 := fresh "Hsub" in
	let Hsub2 := fresh "Hsub" in
	let Hsub3 := fresh "Hsub" in
	destruct H as [ts [ts_sub [ts11_sub [ts12_sup [
	  H1 [H2 [Hsub1 [Hsub2 Hsub3]]]
	]]]]]
  end.

Lemma injective_fun_coec_instr__admininstr : injective fun_coec_instr__admininstr.
Proof.
	unfold injective.
	move=> x1 x2 H.
	destruct x1; destruct x2; try discriminate; inversion H; auto.
Qed.

(*
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
	try apply instrs_empty_same_type in H3.

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
	try apply admin_empty_same_type in H3.
*)

(*

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
		assert (Admin_instrs_ok v_S v_C [] (functype_from_lists [] [])). { apply AIs_ok_empty. }
		apply admin_weakening_empty_both with (ts := ts1) in H0.
		apply (AIs_ok_seq v_S v_C [] v_ai ts1 ts2 ts1); eauto.
	- (* <- *) 
		apply_composition_typing_single H; subst.
		apply AI_ok_weakening. apply H4_comp.
Qed.

Lemma admin_composition': forall v_S v_C v_ais1 v_ais2 t1s t2s t3s,
	Admin_instrs_ok v_S v_C v_ais1 (functype_from_lists t1s t2s) ->
	Admin_instrs_ok v_S v_C v_ais2 (functype_from_lists t2s t3s) ->
	Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (functype_from_lists t1s t3s).
Admitted.
(* Proof.
	move => v_S v_C v_ais1 v_ais2.
	move: v_ais1.
	induction v_ais2 using List.rev_ind; move => v_ais1 t1s t2s t3s HType1 HType2.
		- apply admin_empty_same_type in HType2; by rewrite cats0; subst.
		- apply_composition_typing_single HType2.
	subst.
	rewrite catA. eapply AIs_ok_seq; split.
	eapply IHv_ais2; eauto.
	apply AIs_ok_frame with (v_t := ts1_comp) in H3_comp.
	apply H3_comp.
	apply AI_ok_weakening; eauto.
Qed. *)

Lemma AI_const_typing: forall v_S v_C v_t v_v t1s t2s,
    Admin_instr_ok v_S v_C (AI_CONST v_t v_v) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C AI_NOP (functype_from_lists t1s t2s) ->
    t1s = t2s.
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Nop *) by inversion H; subst; try discriminate.
	- (* Weakening *) f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (AI_DROP) (functype_from_lists t1s t2s) ->
    exists t, t1s = t2s ++ [t].
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Drop *) by inversion H; subst; try discriminate; exists v_t.
	- (* Weakening *) edestruct IHHType as [? ?] => //=; subst.
	exists x. by repeat rewrite <- app_assoc.
Qed.

Lemma Unop_typing: forall v_S v_C v_t v_op t1s t2s,
    Admin_instr_ok v_S v_C (AI_UNOP v_t v_op) (functype_from_lists t1s t2s) ->
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
	Admin_instr_ok v_S v_C (AI_BINOP v_t v_op) (functype_from_lists t1s t2s) ->
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
	Admin_instr_ok v_S v_C (AI_TESTOP v_t v_testop) (functype_from_lists ts1 ts2) ->
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
	Admin_instr_ok v_S v_C (AI_SELECT) (functype_from_lists t1s t2s) ->
    exists ts t, t1s = ts ++ [t; t; I32] /\ t2s = ts ++ [t].
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Select *) inversion H; subst; try discriminate.
	exists [], v_t. eauto.
	- (* Weakening *) edestruct IHHType as [? [? [??]]] => //=; subst.
	exists (v_t ++ x), x0. by repeat split => //=; rewrite <- app_assoc.
Qed.

(*
Lemma Val_Const_list_typing: forall v_S v_C v_vals t1s t2s,
    Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) (functype_from_lists t1s t2s) ->
    t2s = t1s ++ (List.map typeof v_vals).
Proof.
	move => v_S v_C v_vals.
	induction v_vals => //=; move => t1s t2s HType.
	- apply admin_empty_same_type in HType. subst. by rewrite cats0.
	- destruct a.
	  apply_composition_typing_and_single HType.
	  apply AI_const_typing in H4_comp0.
	  subst.
	  apply IHv_vals in H4_comp.
	  subst. simpl.
	  repeat rewrite <- app_assoc.  
	  by f_equal.
Qed.
*)

Lemma If_typing: forall v_S v_C t1s v_ais1 v_ais2 ts ts',
	Admin_instr_ok v_S v_C (AI_IFELSE t1s v_ais1 v_ais2) (functype_from_lists ts ts') ->
	exists ts0,
   	ts = ts0 ++ [I32] /\ ts' = ts0 ++ t1s /\
				Instrs_ok (upd_label v_C ([t1s] ++ C_LABELS v_C)) (v_ais1) (functype_from_lists [] t1s) /\
                Instrs_ok (upd_label v_C ([t1s] ++ C_LABELS v_C)) (v_ais2) (functype_from_lists [] t1s).
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



Lemma Br_if_typing: forall v_S v_C ts1 ts2 v_memaddr, 
	Admin_instr_ok v_S v_C (AI_BR_IF (fun_nat__u32 v_memaddr)) (functype_from_lists ts1 ts2) ->
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
    Admin_instr_ok v_S v_C (AI_BR_TABLE ids i0) (functype_from_lists ts1 ts2) ->
    exists ts1' (ts : resulttype) , ts1 = ts1' ++ ts ++ [I32] /\
                        List.Forall (fun i => (fun_labelidx__nat i < length (C_LABELS v_C))%coq_nat) (ids) /\
						(i0 < length (C_LABELS v_C))%coq_nat /\
						(ts = (lookup_total (C_LABELS v_C) i0)) /\
						List.Forall (fun i => ts = lookup_total (C_LABELS v_C) (fun_labelidx__nat i)) (ids).
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
    Admin_instr_ok v_S v_C (AI_RELOP v_t v_op) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_CVTOP t2 t1 v_op) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_LOCAL_TEE v_memaddr) (functype_from_lists ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [t] /\ (fun_u32__nat v_memaddr < length (C_LOCALS v_C))%coq_nat /\
                lookup_total (C_LOCALS v_C) (fun_u32__nat v_memaddr) = t.
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
    Admin_instr_ok v_S v_C (AI_LABEL_ n v_instrs v_admininstrs) (functype_from_lists ts1 ts2) ->
    exists (ts : resulttype) (ts2' : option valtype), ts2 = ts1 ++ ts2' /\
					Instrs_ok v_C v_instrs (functype_from_lists ts ts2') /\
					fun_optionSize ts = n /\
                    Admin_instrs_ok v_S (upd_label v_C ([ts] ++ (C_LABELS v_C))) v_admininstrs (functype_from_lists [] ts2').
Admitted.
(* Proof.
	move => v_S v_C n v_instrs v_admininstrs ts1 ts2 HType.
	gen_ind_subst HType => //=.
		- (* Instr *) inversion H; subst; try discriminate.
		- (* Label *) destruct H as [? [? ?]]. exists v_t_1, v_t_2. repeat split => //=.
		- (* Weakening *) edestruct IHHType as [? [? [? [? ?]]]] => //=; subst. exists x, x0. by repeat split => //=; try rewrite <- app_assoc.
Qed. *)

Lemma Frame_typing: forall v_S v_C n v_F v_ais t1s t2s,
    Admin_instr_ok v_S v_C (AI_FRAME_ n v_F v_ais) (functype_from_lists t1s t2s) ->
    exists (ts : resulttype), t2s = t1s ++ ts /\
               Thread_ok v_S (Some ts) v_F v_ais ts /\ 
			   (n = (fun_optionSize ts)). 
Proof.
	move => v_S v_C n v_F v_ais t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Instr *) inversion H; subst; try discriminate.
	- (* Frame *)  exists v_t => //=.
	- (* Weakening *) edestruct IHHType as [ts2 [??]]; eauto. subst.
		exists ts2. by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Set_local_typing: forall v_S C i t1s t2s,
    Admin_instr_ok v_S C (AI_LOCAL_SET (fun_nat__u32 i)) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_LOCAL_GET i) (functype_from_lists t1s t2s) ->
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


Lemma Get_global_typing: forall v_S v_C (i: globalidx) t1s t2s,
    Admin_instr_ok v_S v_C (AI_GLOBAL_GET i) (functype_from_lists t1s t2s) ->
    exists mut t, (lookup_total (C_GLOBALS v_C) i) = mk_globaltype mut t /\
    t2s = t1s ++ [t] /\
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
	Admin_instr_ok v_S v_C (AI_GLOBAL_SET (fun_nat__u32 i)) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_RETURN) (functype_from_lists t1s t2s) ->
    exists (ts : resulttype) ts', t1s = ts' ++ ts /\
                   C_RETURN v_C = Some ts.
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Return *) inversion H; subst; try discriminate. exists v_t, v_t_1 => //=.
	- (* Weakening *) edestruct IHHType as [? [? [?  ?]]] => //=; subst.
		exists x, (v_t ++ x0). by repeat split => //=; try rewrite <- app_assoc.
Qed.

(*
Lemma Const_list_typing_empty: forall v_S v_C v_vals,
    Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) (functype_from_lists [::] (List.map typeof v_vals)).
Admitted.
Proof.
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
			- apply (AI_ok_instr v_S v_C (instr__CONST v_valtype v_val_) (functype_from_lists [] [v_valtype])); subst.
				apply Instr_ok__const.
		- by apply admin_instrs_weakening_empty_1.
Qed. *)

Lemma Break_typing: forall n v_S v_C t1s t2s,
	Admin_instr_ok v_S v_C (AI_BR (fun_nat__u32 n)) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_CALL_ADDR a) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_CALL_ADDR v_a) (functype_from_lists t1s t2s) ->
	((lookup_total (FUNCS v_S) v_a) = {| FUNC_TYPE := (functype_from_lists v_t_1 v_t_2); FUNC_MODULE := v_mm; CODE := v_func |}) ->
	(v_func = (FUNC v_x (List.map (fun v_t => (LOCAL v_t)) (v_t)) v_instrs)) ->
	Store_ok v_S ->
    exists ts' C', t1s = ts' ++ v_t_1 /\ t2s = ts' ++ v_t_2 /\
	Module_instance_ok v_S v_mm C' /\
	Instrs_ok (upd_local_label_return C' ((v_t_1 ++ v_t) ++ (C_LOCALS C')) (_append ([v_t_2]) (C_LABELS C')) (_append (Some v_t_2) (C_RETURN C'))) v_instrs (functype_from_lists [::] v_t_2).
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
    Admin_instr_ok v_S v_C (AI_LOAD t v_ww_sx v_memop) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_STORE t v_ww v_memop) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_MEMORY_SIZE) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_MEMORY_GROW) (functype_from_lists t1s t2s) ->
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
    Admin_instr_ok v_S v_C (AI_BLOCK t2s v_instrs) (functype_from_lists tn tm) ->
    exists ts, tn = ts /\ tm = ts ++ t2s /\
		Instrs_ok (upd_label v_C ([t2s] ++ (C_LABELS v_C))) v_instrs (functype_from_lists [] t2s).
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
    Admin_instr_ok v_S v_C (AI_LOOP t2s v_instrs) (functype_from_lists tn tm) ->
    exists ts, tn = ts /\ tm = ts ++ t2s /\
		Instrs_ok (upd_label v_C ([None] ++ (C_LABELS v_C))) v_instrs (functype_from_lists [] t2s).
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
    Admin_instr_ok v_S v_C (AI_CALL j) (functype_from_lists t1s t2s) ->
    exists ts t1s' (t2s' : option valtype), (fun_u32__nat j < length (C_FUNCS v_C))%coq_nat /\
    lookup_total (C_FUNCS v_C) (fun_u32__nat j) = functype_from_lists t1s' t2s' /\
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
    Admin_instr_ok v_S v_C (AI_CALL_INDIRECT i) (functype_from_lists t1s t2s) ->
    exists tn (tm : option valtype) ts,
    (fun_u32__nat i < length (C_TYPES v_C))%coq_nat /\
    lookup_total (C_TYPES v_C) (fun_u32__nat i) = functype_from_lists tn tm /\
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
*)