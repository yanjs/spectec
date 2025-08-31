From Stdlib Require Import String List Unicode.Utf8 NArith Arith Logic.Eqdep.
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
	*)
	  
Lemma upd_label_overwrite: forall C l1 l2,
	upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Lemma upd_label_is_same_as_append: forall v_C lab,
	upd_label v_C (lab @@ (C_LABELS v_C)) = {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := [];
	C_DATAS := []; C_LOCALS := []; C_LABELS := lab; C_RETURN := None |} @@ v_C.
Proof.
	move => v_C lab. reflexivity.
Qed.

Lemma upd_local_is_same_as_append: forall v_C loc,
	upd_local v_C (loc @@ (C_LOCALS v_C))  = {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := [];
	C_DATAS := []; C_LOCALS := loc; C_LABELS := []; C_RETURN := None |} @@ v_C.
Proof.
	move => v_C loc. reflexivity.
Qed.

Lemma upd_local_return_is_same_as_append: forall v_C loc ret,
	upd_local_return v_C (loc @@ (C_LOCALS v_C)) (ret @@ (C_RETURN v_C)) 
	= {|
		C_TYPES := [];
		C_FUNCS := [];
		C_GLOBALS := [];
		C_TABLES := [];
		C_MEMS := [];
		C_ELEMS := [];
		C_DATAS := [];
		C_LOCALS := loc;
		C_LABELS := [];
		C_RETURN := ret
	|} @@ v_C.
Proof. reflexivity. Qed.


Lemma upd_return_is_same_as_append: forall v_C ret,
	upd_return v_C (ret @@ (C_RETURN v_C)) =
	{| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := [];
	C_DATAS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := ret |} @@ v_C.
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
		| VAL_VCONST t _ => t
		| VAL_REF_NULL t => t
		| VAL_REF_FUNC_ADDR _ => VALTYPE_FUNCREF
		| VAL_REF_HOST_ADDR _ => VALTYPE_EXTERNREF
		end.
	
(*
Lemma typeof_default_inverse: forall (v_t : list valtype),
	List.map typeof (List.map [fun t => the (fun_default_ t)] v_t) = v_t.
Proof.
	move => v_t.
	induction v_t => //=.
	f_equal.
	destruct a; destruct v_t => //=.
	apply IHv_t.
Qed.
*)

Lemma Forall2_Val_ok_is_same_as_map: forall v_S v_t1 v_local_vals,
	Forall2 (fun v s => Val_ok v_S s v) v_t1 v_local_vals ->
	List.map typeof v_local_vals = v_t1.
Proof.
	move => v_S v_t1 v_local_vals H.
	generalize dependent v_local_vals.
	induction v_t1; move => v_local_vals H; destruct v_local_vals => //=; inversion H.
	subst. f_equal. 
	- inversion H3 => //=.
		inversion H0 => //=.
	- by apply IHv_t1.
Qed.

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
	| (AI_LOOP v_bt v_instr) =>
	    exists t t',
		v_ft = (t :-> t') /\
	    (Blocktype_ok v_C v_bt (t :-> t')) /\
		(Instrs_ok (prepend_label v_C t) v_instr (t :-> t'))
	| (AI_IFELSE v_bt v_instrs1 v_instrs2) =>
	    exists (t t': seq valtype),
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
	| (AI_CALL v_x) =>
		exists t t',
		v_ft = (t :-> t') /\
		((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) /\
		((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = (t :-> t'))
	| (AI_CALL_INDIRECT v_x v_y) =>
		exists t t' v_lim,
		v_ft = ((t ++ [VALTYPE_I32]) :-> t') /\
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim FUNCREF)) /\
		((fun_proj_uN_0 32 v_y) < (List.length (C_TYPES v_C))) /\
		((lookup_total (C_TYPES v_C) (fun_proj_uN_0 32 v_y)) = (t :-> t'))
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
	| (AI_REF_FUNC v_x) =>
	  exists v_fty, v_ft = ([] :-> [VALTYPE_FUNCREF]) /\
		((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) /\
		((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = v_fty)
	| AI_REF_IS_NULL =>
	  exists v_rt,
	  v_ft = ([v_rt] :-> [VALTYPE_I32])
	| (AI_LOCAL_GET v_x) =>
	  exists v_t, v_ft = ([] :-> [v_t]) /\
	    ((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) /\
		((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t)
	| (AI_LOCAL_SET v_x) =>
	  exists v_t, v_ft = ([v_t] :-> []) /\
	    ((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) /\
		((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t)
	| (AI_LOCAL_TEE v_x) =>
	  exists v_t, v_ft = ([v_t] :-> [v_t]) /\
	    ((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) /\
	    ((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t)
	| (AI_GLOBAL_GET v_x) =>
	  exists v_t v_mut, v_ft = ([] :-> [v_t]) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) /\
		((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype v_mut v_t))
	| (AI_GLOBAL_SET v_x) =>
	  exists v_t, v_ft = ([v_t] :-> []) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) /\
		((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype (Some MUT) v_t))
	| (AI_TABLE_GET v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([VALTYPE_I32] :-> [(v_rt : valtype)]) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt))
	| (AI_TABLE_SET v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([VALTYPE_I32; (v_rt : valtype)] :-> []) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt))
	| (AI_TABLE_SIZE v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([] :-> [VALTYPE_I32]) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt))
	| (AI_TABLE_GROW v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([(v_rt : valtype); VALTYPE_I32] :-> [VALTYPE_I32]) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt))
	| (AI_TABLE_FILL v_x) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([VALTYPE_I32; (v_rt : valtype); VALTYPE_I32] :-> []) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt))
	| (AI_TABLE_COPY v_x_1 v_x_2) =>
	  exists (v_rt: reftype) v_lim_1 v_lim_2, v_ft = ([VALTYPE_I32; VALTYPE_I32; VALTYPE_I32] :-> []) /\
	  	((fun_proj_uN_0 32 v_x_1) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x_1)) = (mk_tabletype v_lim_1 v_rt))/\
	  	((fun_proj_uN_0 32 v_x_2) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x_2)) = (mk_tabletype v_lim_2 v_rt))
	| (AI_TABLE_INIT v_x_1 v_x_2) =>
	  exists (v_rt: reftype) v_lim, v_ft = ([VALTYPE_I32; VALTYPE_I32; VALTYPE_I32] :-> []) /\
	  	((fun_proj_uN_0 32 v_x_1) < (List.length (C_TABLES v_C))) /\
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x_1)) = (mk_tabletype v_lim v_rt))/\
	  	((fun_proj_uN_0 32 v_x_2) < (List.length (C_ELEMS v_C))) /\
		((lookup_total (C_ELEMS v_C) (fun_proj_uN_0 32 v_x_2)) = v_rt)
	| (AI_ELEM_DROP v_x) =>
	  exists (v_rt: reftype), v_ft = ([] :-> []) /\
	  	((fun_proj_uN_0 32 v_x) < (List.length (C_ELEMS v_C))) /\
		((lookup_total (C_ELEMS v_C) (fun_proj_uN_0 32 v_x)) = v_rt)
	| (AI_LOAD v_nt None v_memarg) =>
	  exists v_mt, v_ft = ([VALTYPE_I32] :-> [(v_nt : valtype)]) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt) /\
		((fun_size (v_nt : valtype)) <> None) /\
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((the (fun_size (v_nt : valtype))) : nat) / (8 : nat)))
	| (AI_LOAD I32 (Some (op_ (mk_sz v_M) v_sx)) v_memarg) =>
	  exists v_mt, v_ft = ([VALTYPE_I32] :-> [(VALTYPE_I32)]) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt) /\
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat)))
	| (AI_LOAD I64 (Some (op_ (mk_sz v_M) v_sx)) v_memarg) =>
	  exists v_mt, v_ft = ([VALTYPE_I32] :-> [VALTYPE_I64]) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt) /\
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat)))
	| (AI_STORE v_nt None v_memarg) =>
	  exists v_mt, v_ft = ([VALTYPE_I32; (v_nt : valtype)] :-> []) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt) /\
		((fun_size (v_nt : valtype)) <> None) /\
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((the (fun_size (v_nt : valtype))) : nat) / (8 : nat)))
	| (AI_STORE v_Inn (Some (mk_sz v_M)) v_memarg) =>
	  exists v_mt, v_ft = ([VALTYPE_I32; (v_Inn : valtype)] :-> []) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt) /\
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat)))
	(*| (AI_VLOAD v_0 v_1 v_2)
	| (AI_VLOAD_LANE v_0 v_1 v_2 v_3)
	| (AI_VSTORE v_0 v_1)
	| (AI_VSTORE_LANE v_0 v_1 v_2 v_3)*)
	| AI_MEMORY_SIZE =>
	  exists v_mt, v_ft = ([] :-> [VALTYPE_I32]) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt)
	| AI_MEMORY_GROW =>
	  exists v_mt, v_ft = ([VALTYPE_I32] :-> [VALTYPE_I32]) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt)
	| AI_MEMORY_FILL =>
	  exists v_mt, v_ft = ([VALTYPE_I32; VALTYPE_I32; VALTYPE_I32] :-> []) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt)
	| AI_MEMORY_COPY =>
	  exists v_mt, v_ft = ([VALTYPE_I32; VALTYPE_I32; VALTYPE_I32] :-> []) /\
	  	(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt)
	| (AI_MEMORY_INIT v_x) =>
	  exists v_mt, v_ft = ([VALTYPE_I32; VALTYPE_I32; VALTYPE_I32] :-> []) /\
		(0 < (List.length (C_MEMS v_C))) /\
		((lookup_total (C_MEMS v_C) 0) = v_mt) /\
		((fun_proj_uN_0 32 v_x) < (List.length (C_DATAS v_C))) /\
		((lookup_total (C_DATAS v_C) (fun_proj_uN_0 32 v_x)) = OK)
	| (AI_DATA_DROP v_x) =>
	  v_ft = ([] :-> []) /\
		((fun_proj_uN_0 32 v_x) < (List.length (C_DATAS v_C))) /\
		((lookup_total (C_DATAS v_C) (fun_proj_uN_0 32 v_x)) = OK)
	| (AI_REF_FUNC_ADDR v_funcaddr) =>
	  exists v_functype,
	  v_ft = ([] :-> [VALTYPE_FUNCREF]) /\
	  (Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_functype))
	| (AI_REF_HOST_ADDR _) =>
	  v_ft = ([] :-> [VALTYPE_EXTERNREF])
	| (AI_CALL_ADDR v_funcaddr) =>
		exists t t', v_ft = (t :-> t') /\
		(Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC (t :-> t')))
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
	{ (* LOAD None *)
		destruct v_nt; repeat eexists; eauto.
	}
	{ (* STORE Some *)
		destruct v_Inn; auto.
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
		57: { (* LOAD *)
			admit. (* Inversion not working for some reason
			destruct o.
			admit. 
			{
				destruct v_numtype;
				destruct l; try destruct v_sz.
				unfold op_ in H.
				remember (op_ INN_I32 (mk_sz v_i) v_sx) as op.
				inversion H; subst.
				inversion H.
				inversion_clear H.
				all: inversion H.
				all: do 2 eexists.
				all: split; try eapply instrtype_sub_refl.
				all: eexists.
			}
		    inversion H; subst.
			(* I don't like this *)
			apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
			all: do 2 eexists; split; try eapply instrtype_sub_refl.
			destruct v_numtype; repeat eexists; auto.
			all: destruct o; try destruct l; try destruct v_sz.
			inversion H1.
			assert (o = None). {
				
			}
			do 2 eexists.
			destruct v_numtype.
			all: split; try eapply instrtype_sub_refl.
			all: destruct o; try auto.
			all: try destruct l; try destruct v_sz.
			remember (op_ INN_I32 (mk_sz v_i) v_sx) as so.
			inversion H.
			eexists.
			repeat eexists; auto.
			all: inversion H.
			all: eexists v_mt.
			inversion H.
			all: inversion H; subst.
			all: repeat eexists; auto.
			inversion H.
			{
				do 2 eexists.
			}
			destruct o; destruct v_numtype; try (destruct l); try (destruct v_sz);
			inversion H; subst.
			do 2 eexists;
			split; try eapply instrtype_sub_refl.
			all: eexists.
			1,2: destruct l; destruct v_sz.
			all: repeat eexists; eauto.
			inversion H; subst.
			{
				injection H1 as H2.
			}
			inversion H1.
			do 2 eexists;
			split.
			2: eapply instrtype_sub_refl.
			3: eapply instrtype_sub_refl.
			all: eexists; split; auto.
			destruct v_Inn; auto.
			*)
		}
		all: inversion H; subst.
		all: do 2 eexists.
		all: try (split;
		[
			first [
				solve exact
			|
				solve [simpl; eauto]
			|
				solve [destruct_disjunctions; repeat eexists; eauto]
			|
				solve [destruct v_numtype; repeat eexists; eauto]
			]
		|
				exists []; do 3 eexists;
				split; [|split; [|split; [|split]]];
				try apply resulttype_sub_refl;
				simpl; try exact;
				try destruct v_Inn; auto
	  	]).
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
	  - unfold ai_principal_typing; repeat eexists; eauto.
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
Admitted.

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

Lemma ais_single_ref_typing_inversion: forall v_S v_C (v_ref: wasm.ref) ts1 ts2,
  Admin_instrs_ok v_S v_C [v_ref: admininstr] (ts1 :-> ts2) ->
  exists (t: reftype), 
	(([] :-> [t: valtype]) <ti: (ts1 :-> ts2)) /\
   	Ref_ok v_S v_ref t.
Proof.
	move => v_S v_C v_ref ts1 ts2 HType.
	eapply ais_single_typing_inversion in HType as [t1 [t2 [Hai Hsub]]].
	destruct v_ref; unfold ai_principal_typing, fun_coec_ref__admininstr in Hai.
	2: destruct Hai as [v_ft [Hai Heok]].
	all: inversion Hai; subst.
	- exists v_reftype. split; auto. by constructor.
	- exists FUNCREF. split; auto. econstructor; eauto.
	- exists EXTERNREF. split; auto. econstructor; eauto.
Qed.


Lemma ais_single_val_typing_inversion: forall v_S v_C (v_val: wasm.val) ts1 ts2,
  Admin_instrs_ok v_S v_C [v_val: admininstr] (ts1 :-> ts2) ->
  exists t, 
	(([] :-> [t]) <ti: (ts1 :-> ts2)) /\
   	Val_ok v_S v_val t.
Proof.
	move => v_S v_C v_val ts1 ts2 HType.
	eapply ais_single_typing_inversion in HType as [t1 [t2 [Hai Hsub]]].
	destruct v_val; unfold ai_principal_typing, fun_coec_val__admininstr in Hai.
	4: destruct Hai as [v_ft [Hai Heok]].
	all: inversion Hai; subst.
	- exists v_numtype. split; auto. by constructor.
	- exists v_vectype. split; auto. by constructor.
	- exists v_reftype. split; auto.
	  eapply ok_reftype with (v_r := REF_NULL v_reftype).
	  econstructor.
	- exists VALTYPE_FUNCREF. split; auto.
	  eapply ok_reftype with
	  	(v_r := REF_FUNC_ADDR v_funcaddr)
		(v_rt := FUNCREF).
	  econstructor. eauto.
	- exists VALTYPE_EXTERNREF. split; auto.
	  eapply ok_reftype with
	  	(v_r := REF_HOST_ADDR v_hostaddr)
		(v_rt := EXTERNREF).
	  econstructor.
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

Lemma ais_composition_typing: forall (v_S: store) (v_C: context) v_ais1 v_ais2 t1s t2s,
Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (t1s :-> t2s) ->
exists t3s, Admin_instrs_ok v_S v_C v_ais1 (t1s :-> t3s) /\
	Admin_instrs_ok v_S v_C v_ais2 (t3s :-> t2s).
Proof.
	move=> v_S v_C v_ais1 v_ais2 t1s t2s HType.
	move: v_ais1 t1s t2s HType.
	induction v_ais2 using last_ind.
	{
		move=> v_ais1 t1s t2s HType.
		exists t2s.
		split.
		rewrite cats0 in HType. auto.
		eapply ais_empty_typing.
		eapply resulttype_sub_refl.
	}
	{
		move=> v_ais1 t1s t2s HType.
		rewrite -cats1 in HType.
		rewrite catA in HType.
		eapply ais_seq_typing_inversion in HType as [t3s [H1 H2]].
		eapply IHv_ais2 in H1 as [t3s' [H3 H4]].
		exists t3s'.
		split. auto.
		rewrite -cats1.
		eapply AIs_ok_seq. eauto.
		eapply ais_single_typing_inversion'.
		eauto.
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
  | Admin_instrs_ok _ _ [map fun_coec_val__admininstr ?v_vals] ( ?t1s :-> ?t2s ) =>
    let t1s_sup := fresh t1s "_sup" in
	let t2s_sub := fresh t2s "_sub" in
	let Hai := fresh "Hai" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_typing_inversion in H
	  as [t1s_sup [t2s_sub [Hai Hsub]]]
  | Admin_instrs_ok _ _ [fun_coec_val__admininstr ?v_val] ( ?t1s :-> ?t2s ) =>
    let t := fresh "t" in
	let HValok := fresh "HValok" in
	let Hsub := fresh "Hsub" in
    eapply ais_single_val_typing_inversion in H
	  as [t [Hsub HValok]]
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
  | Admin_instrs_ok _ _ (_ :: (_ :: _)) _ =>
    repeat rewrite -(cat1s _ (_ :: _)) in H;
	repeat rewrite !catA in H;
	do_ais_typing_inversion H
  | Admin_instrs_ok _ _ (_ ++ _) _ =>
    let t3s := fresh "t3s" in
	let H1 := fresh "H1" in
	let H2 := fresh "H2" in
	eapply ais_composition_typing in H as [t3s [H1 H2]]
  | _ => idtac
  end.

Ltac typing_inversion H :=
  destruct_functypes;
  try rewrite !app_cat in H;
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

Lemma construct_instrs_typing_single : forall v_C v_ai ts1 ts2 ts1' ts2',
	Instr_ok v_C v_ai (ts1 :-> ts2) ->
	((ts1 :-> ts2) <ti: (ts1' :-> ts2')) ->
	Instrs_ok v_C [v_ai] (ts1' :-> ts2').
Proof.
	move=> v_C v_ai ts1 ts2 ts1' ts2' Hai Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (instrs_ok_sub).
	2: { eapply resulttype_sub_app; eauto. }
	2: {
		eapply resulttype_sub_app.
		eapply resulttype_sub_refl.
		eauto.
	}
	{
		eapply instrs_ok_frame.
		eapply (instrs_ok_seq _ []).
		{
			eapply instrs_empty_typing.
			eapply resulttype_sub_refl.
		}
		eauto.
	}
Qed.

Lemma construct_ais_typing_single : forall v_S v_C v_ai ts1 ts2 ts1' ts2',
	Admin_instr_ok v_S v_C v_ai (ts1 :-> ts2) ->
	((ts1 :-> ts2) <ti: (ts1' :-> ts2')) ->
	Admin_instrs_ok v_S v_C [v_ai] (ts1' :-> ts2').
Proof.
	move=> v_S v_C v_ai ts1 ts2 ts1' ts2' Hai Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (AIs_ok_sub _ _); [
		eapply (AIs_ok_frame) |
		eapply resulttype_sub_refl |
		eapply resulttype_sub_app; eauto
	].
	eapply (AIs_ok_seq _ _ []).
	- apply ais_empty_typing. by apply Hsub1.
	- eauto.
Qed.

Lemma construct_ais_subtyping : forall v_S v_C v_ais ts1 ts2 ts1' ts2',
	Admin_instrs_ok v_S v_C v_ais (ts1 :-> ts2) ->
	((ts1 :-> ts2) <ti: (ts1' :-> ts2')) ->
	Admin_instrs_ok v_S v_C v_ais (ts1' :-> ts2').
Proof.
	move=> v_S v_C v_ais ts1 ts2 ts1' ts2' Hai Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (AIs_ok_sub _ _).
	- eapply AIs_ok_frame. by eapply Hai.
	- eapply resulttype_sub_app; eauto.
	- eapply resulttype_sub_app; eauto.
	  by eapply resulttype_sub_refl.
Qed.

Ltac unfold_principal_typing H :=
  unfold instr_principal_typing in H;
  try (unfold fun_coec_instr__admininstr in H);
  unfold ai_principal_typing in H;
  try (unfold fun_coec_val__admininstr in H);
  try (unfold fun_coec_ref__admininstr in H).

Lemma injective_fun_coec_numtype__valtype: injective fun_coec_numtype__valtype.
Proof.
	unfold injective.
	move=> x1 x2 H.
	destruct x1; destruct x2; try discriminate; auto.
Qed.

Ltac valtype_discriminate_helper H :=
  lazymatch type of H with
  | (_ ?x) = (_ ?y) =>
    destruct x; destruct y
  | (_ ?x) = _ =>
    destruct x
  | _ = (_ ?y) =>
    destruct y
  | _ = _ => idtac
  end;
  first [discriminate H | subst].

Lemma construct_ais_compose : forall v_S v_C v_ais1 v_ais2 t1s t2s t3s,
	Admin_instrs_ok v_S v_C v_ais1 (t1s :-> t2s) ->
	Admin_instrs_ok v_S v_C v_ais2 (t2s :-> t3s) ->
	Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (t1s :-> t3s).
Proof.
	move => v_S v_C v_ais1 v_ais2 t1s t2s t3s H1 H2.
	move: v_ais1 t1s t2s t3s H1 H2.
	induction v_ais2 using last_ind.
	{
		move=> v_ais1 t1s t2s t3s H1 H2.
		rewrite cats0.
		eapply AIs_ok_sub.
		eapply H1.
		eapply resulttype_sub_refl.
		eapply ais_empty_typing in H2.
		eapply H2.
	}
	{
		move=> v_ais1 t1s t2s t3s H1 H2.
		rewrite -cats1.
		rewrite catA.
		rewrite -cats1 in H2.
		typing_inversion H2.

		eapply AIs_ok_seq.
		eapply IHv_ais2.
		eapply H1.
		eapply H0.
		by eapply ais_single_typing_inversion'.
	}
Qed.

Lemma construct_ai_const_I32 : forall v_S v_C v_num,
	Admin_instr_ok v_S v_C (AI_CONST I32 v_num) ([] :-> [VALTYPE_I32]).
Proof.
	move => v_S v_C v_num.
	eapply AI_ok_instr with (v_instr := instr_CONST _ _).
	econstructor.
Qed.

Lemma construct_ai_ref : forall v_S v_C (v_ref: wasm.ref) v_t,
	Ref_ok v_S v_ref v_t ->
	Admin_instr_ok v_S v_C (v_ref: admininstr) ([] :-> [v_t: valtype]).
Proof.
	move => v_S v_C v_ref v_t HRef.
	destruct HRef.
	{
		eapply AI_ok_instr with (v_instr := instr_REF_NULL v_rt).
		econstructor.
	}
	{
		eapply AI_ok_ref; eauto.
	}
	{
		eapply AI_ok_ref_extern.
	}
Qed.

Lemma construct_ai_val : forall v_S v_C (v_val: wasm.val) v_t,
	Val_ok v_S v_val v_t ->
	Admin_instr_ok v_S v_C (v_val: admininstr) ([] :-> [v_t]).
Proof.
	move => v_S v_C v_val v_t HValok.
	inversion HValok; subst.
	- eapply AI_ok_instr with (v_instr := (instr_CONST v_nt v_c_t)).
	  by econstructor.
	- eapply AI_ok_instr with (v_instr := (instr_VCONST v_vt v_c_t)).
	  destruct v_vt.
	  by econstructor.
	- inversion H; subst.
	  + eapply AI_ok_instr with (v_instr := (instr_REF_NULL v_rt)).
	    by econstructor.
	  + eapply AI_ok_ref. by eauto.
	  + by eapply AI_ok_ref_extern.
Qed.



Lemma construct_ais_vals' : forall v_S v_C v_C' (v_vals: seq wasm.val) v_ft,
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) v_ft ->
	Admin_instrs_ok v_S v_C' (map fun_coec_val__admininstr v_vals) v_ft.
Proof.
	move=> v_S v_C v_C' v_vals v_ft HType.
	generalize dependent v_ft.
	induction v_vals using last_ind.
	{ (* v_vals = [] *)
	  move=> v_ft HType.
	  unfold map.
	  destruct_functypes.
	  eapply ais_empty_typing.
	  eapply ais_empty_typing in HType.
	  auto.
	}
	{ (* v_vals = xs ++ [x] *)
	  move=> v_ft HType.
	  destruct_functypes.
	  rewrite map_rcons in HType.
	  rewrite -cats1 in HType.
	  rewrite map_rcons.
	  rewrite -cats1.
	  typing_inversion HType.
	  typing_inversion H2.

	  eapply construct_ais_compose.
	  - eapply IHv_vals. eauto.
	  - eapply construct_ais_typing_single.
	    eapply construct_ai_val; eauto.
		by eauto.
	}
Qed.

Lemma construct_ais_vals'' : forall v_S v_S' v_C v_C' (v_vals: seq wasm.val) v_ft,
	Store_extension v_S v_S' ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) v_ft ->
	Admin_instrs_ok v_S' v_C' (map fun_coec_val__admininstr v_vals) v_ft.
Admitted.

Lemma construct_ais_trap : forall v_S v_C v_ft,
Admin_instrs_ok v_S v_C [(AI_TRAP )] v_ft.
Proof.
	move=> v_S v_C v_ft.
	destruct_functypes.
	eapply (AIs_ok_seq _ _ [] AI_TRAP).
	eapply ais_empty_typing.
	eapply resulttype_sub_refl.
	eapply AI_ok_trap.
Qed.


Definition value_extra (v_S: store) (v_val: wasm.val) : Prop :=
  match v_val with
  | VAL_REF_FUNC_ADDR v_funcaddr => ∃ v_ft : functype, 
    Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_ft)
  | _ => True
  end.

Definition Vals_ok v_S v_vals v_ts: Prop :=
List.Forall2 (fun (v_t : valtype) (v_val : val) => (Val_ok v_S v_val v_t)) (v_ts) (v_vals).

Lemma ais_vals_typing_inversion: forall v_S v_C v_vals t1s t2s,
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) (t1s :-> t2s) ->
	exists (v_ts: list valtype),
	(([] :-> v_ts) <ti: (t1s :-> t2s)) /\
	(Vals_ok v_S v_vals v_ts).
Proof.
	move=> v_S v_C v_vals t1s t2s HType.
	move: t1s t2s HType.

	induction v_vals using last_ind.
	{
		move => t1s t2s HType.
		exists [].
		split.
		- eapply ais_empty_typing in HType.
		  exists t1s, t2s, [], [].
		  split. by rewrite cats0.
		  split. by rewrite cats0.
		  split; auto.
		  split; by eapply resulttype_sub_refl.
		- constructor.
	}
	{
		move => t1s t2s HType.
		rewrite map_rcons in HType.
		rewrite -cats1 in HType.
		typing_inversion HType.
		eapply IHv_vals in H1 as [v_ts [Hsub Hforall]].
		typing_inversion H2.
		rewrite -(cats0 v_ts) in Hsub.
		eapply (instrtype_sub_compose2 _ _ [] _ _ _ _ Hsub) in Hsub0.
		  
		exists (v_ts ++ [t]).
		split. auto.
		rewrite -cats1.
		eapply Forall2_app. eauto.
		constructor. auto.
		constructor.
	}
Qed.

Ltac vals_typing_inversion H :=
  match type of H with
  | Admin_instrs_ok ?v_S ?v_C (map fun_coec_val__admininstr ?v_vals) (?t1s :-> ?t2s) =>
	let v_ts := fresh "v_ts" in
	let Hsub := fresh "Hsub" in
	let Hforall := fresh "Hforall" in
	eapply ais_vals_typing_inversion in H as [v_ts [Hsub Hforall]]
  | Admin_instrs_ok ?v_S ?v_C (ListDef.map (fun x => fun_coec_val__admininstr x) ?v_vals) (?t1s :-> ?t2s) =>
	let v_ts := fresh "v_ts" in
	let Hsub := fresh "Hsub" in
	let Hforall := fresh "Hforall" in
	eapply ais_vals_typing_inversion in H as [v_ts [Hsub Hforall]]
  | _ => idtac
  end.

Lemma construct_ais_vals: forall v_S v_C (v_vals: list wasm.val) t1s t2s ts,
	(([] :-> ts) <ti: (t1s :-> t2s)) ->
	(Vals_ok v_S v_vals ts) ->
	Admin_instrs_ok v_S v_C (map fun_coec_val__admininstr v_vals) (t1s :-> t2s).
Proof.
	move => v_S v_C v_vals t1s t2s ts Hsub Hforall.
	move: t1s t2s ts Hsub Hforall.
	induction v_vals using last_ind.
	{
		move => t1s t2s ts Hsub Hforall.
		inversion Hforall; subst.
		unfold_instrtype_sub Hsub; subst.
		eapply ais_empty_typing.
		eapply resulttype_sub_app; auto.
		eapply resulttype_sub_trans; eauto.
	}
	{
		induction ts using last_ind.
		{
			move => Hsub Hforall.
			inversion Hforall; subst.
			rewrite -cats1 in H.
			destruct_list_eq H.
		}
		{
			clear IHts.
			move => Hsub Hforall.
			rewrite -!cats1 in Hforall.
			eapply Forall2_app' in Hforall as [H1 H2].
			2: {
				apply Forall2_length in Hforall.
				rewrite !last_length in Hforall.
				by inversion Hforall.
			} 
			rewrite map_rcons.
			rewrite -cats1.
			induction t2s using last_ind.
			{
				unfold_instrtype_sub Hsub.
				destruct_list_eq H0; subst.
				inversion Hsub2.
				rewrite -size_length in H3.
				rewrite size_rcons in H3.
				discriminate.
			}
			clear IHt2s.

			rewrite -!cats1 in Hsub.
			unfold_instrtype_sub Hsub; subst.
			eapply resulttype_sub_empty in Hsub1; subst.
			eapply (resulttype_sub_app _ _ _ _ Hsub0) in Hsub2.
			rewrite -H0 in Hsub2.
			rewrite catA in Hsub2.
			eapply (resulttype_sub_app') in Hsub2 as [Hsub3 Hsub4].
			2: {
				inversion Hsub2.
				rewrite !last_length in H4.
				by inversion H4.
			}

			rewrite cats0.
			eapply (AIs_ok_seq _ _ _ _ _ _ t2s).
			2: {
				rewrite -cats1.
				rewrite <-(cats0 t2s) at 1.
				eapply AI_ok_weakening.
				2: by apply resulttype_sub_refl.
				2: by apply resulttype_sub_refl.
				2: by apply Hsub4.
				inversion H2.
				by eapply construct_ai_val.
			}
			eapply (IHv_vals _ t2s ts); auto.
			eexists ts0, ts0_sub, [], (drop (size ts0) t2s).
			split. by rewrite cats0.
			split.
			{
				rewrite <-(cat_take_drop (size ts0) t2s) at 1.
				rewrite -!app_cat.
				rewrite app_inv_tail_iff.
				assert (take (size ts0) (t2s ++ [x1]) = take (size ts0) t2s).
				{
					eapply takel_cat.
					inversion Hsub3.
					rewrite -!size_length in H4.
					rewrite -H4.
					rewrite size_cat.
					eapply leq_addr.
				}
				rewrite -H.
				rewrite H0.
				inversion Hsub0.
				rewrite -size_length in H5.
				by rewrite take_size_cat.
			}
			split. auto.
			split. by apply resulttype_sub_refl.
			pose proof Hsub3 as Hsub3_0.
			rewrite -(cat_take_drop (size ts0) t2s) in Hsub3.
			eapply resulttype_sub_app' in Hsub3 as [Hsub5 Hsub6]; auto.
			rewrite -!size_length.
			rewrite size_takel; auto.
			inversion Hsub3_0.
			rewrite -!size_length in H4.
			rewrite -H4.
			rewrite size_cat.
			eapply leq_addr.
		}
	}
Qed.

Lemma resulttype_sub_single_inversion: forall t1 t2,
	([t1] <ts: [t2]) ->
	(t1 <tv: t2).
Proof.
	move => t1 t2 Hsub.
	inversion Hsub; subst; clear Hsub.
	inversion H2; subst.
	auto.
Qed.

Lemma construct_ais_instrtype_sub: forall v_S v_C v_ais t1s t2s t1s' t2s',
	Admin_instrs_ok v_S v_C v_ais (t1s :-> t2s) ->
	((t1s :-> t2s) <ti: (t1s' :-> t2s')) ->
	Admin_instrs_ok v_S v_C v_ais (t1s' :-> t2s').
Proof.
	move => v_S v_C v_ais t1s t2s t1s' t2s' HType Hsub.
	unfold_instrtype_sub Hsub; subst.
	eapply (AIs_ok_sub _ _ _ _ _ (ts_sub ++ t1s) (ts_sub ++ t2s)).
	- eapply AIs_ok_frame; eauto.
	- eapply resulttype_sub_app; eauto.
	- eapply resulttype_sub_app; eauto.
	  eapply resulttype_sub_refl.
Qed.



Definition inst_match C C' : Prop :=
	C_TYPES C = C_TYPES C' /\
	C_FUNCS C = C_FUNCS C' /\
	C_GLOBALS C = C_GLOBALS C' /\
	C_TABLES C = C_TABLES C' /\
	C_MEMS C = C_MEMS C' /\
	C_ELEMS C = C_ELEMS C' /\
	C_DATAS C = C_DATAS C'.

Lemma construct_inst_match_label : forall C C' lab,
	inst_match C C' -> inst_match C (upd_label C' lab).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_match_return : forall C C' ret,
	inst_match C C' -> inst_match C (upd_return C' ret).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_match_local : forall C C' loc,
	inst_match C C' -> inst_match C (upd_local C' loc).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_match_local_return : forall C C' loc ret,
	inst_match C C' -> inst_match C (upd_local_return C' loc ret).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Lemma construct_inst_prepend_label : forall C C' lab,
	inst_match C C' -> inst_match C (prepend_label C' lab).
Proof.
	intros.
	unfold inst_match.
	unfold inst_match in H.
	destruct C'; simpl in *.
	auto.
Qed.

Ltac resolve_inst_match :=
	repeat lazymatch goal with
	| _ : _ |- inst_match _ (prepend_label _ _) =>
		eapply construct_inst_prepend_label
	| _ : _ |- inst_match _ (upd_local_return _ _ _) =>
		eapply construct_inst_match_local_return
	| _ : _ |- inst_match _ (upd_local _ _) =>
		eapply construct_inst_match_local
	| _ : _ |- inst_match _ (upd_return _ _) =>
		eapply construct_inst_match_return
	| _ : _ |- inst_match _ (upd_label _ _) =>
		eapply construct_inst_match_label
	| _ => idtac
	end;
	unfold inst_match;
	simpl;
	unfold _append;
	simpl;
	repeat eexists; auto.

Lemma Val_ok_non_bot : forall v_S v_val v_t,
	Val_ok v_S v_val v_t ->
	v_t <> VALTYPE_BOT.
Proof.
	move=> v_S v_val v_t HValok.
	inversion HValok; subst.
	- destruct v_nt; discriminate.
	- destruct v_vt; discriminate.
	- destruct v_rt; discriminate.
Qed.



Lemma Vals_ok_non_bot : forall v_S v_val v_ts,
	Forall2	(λ (v_t0 : valtype) (v_val0 : wasm.val),
		Val_ok v_S v_val0 v_t0) v_ts v_val ->
	Forall (λ (v_t : valtype),
		v_t <> VALTYPE_BOT) v_ts.
Proof.
	move=> v_S v_val v_ts H.
	move : v_ts H.
	induction v_val.
	{
		move=> v_ts H.
		inversion H; subst; econstructor.
	}
	{
		move=> v_ts H.
		destruct v_ts.
		{
			inversion H.
		}
		inversion H; subst; econstructor.
		2: by eapply IHv_val.
		eapply Val_ok_non_bot; eauto.
	}
Qed.

Lemma Ref_ok_non_bot : forall v_S v_val (v_t: reftype),
	Ref_ok v_S v_val v_t ->
	(v_t: valtype) <> VALTYPE_BOT.
Proof.
	move=> v_S v_val v_t HRefok.
	inversion HRefok; subst; try discriminate.
	destruct v_t; discriminate.
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

*)