(* Proof Start *)

From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

(* Theorems *)

Theorem t_pure_preservation: forall v_S v_C  v_func_type,
	Admin_instrs_ok v_S v_C [(AI_UNREACHABLE )] v_func_type ->
	Step_pure [(AI_UNREACHABLE )] [(AI_TRAP )] ->
	Admin_instrs_ok v_S v_C [(AI_TRAP )] v_func_type.
Proof.
	move=> v_S v_C v_func_type HType HReduce.
	destruct v_func_type as [v_t_1 v_t_2].
	apply (AIs_ok_seq v_S v_C [] (AI_TRAP) v_t_1 v_t_2 v_t_1).
    - apply admin_weakening_empty_both.
	    apply AIs_ok_empty.
	- apply AI_ok_trap.
Qed.

Lemma Step_pure__nop_preserves : forall v_S v_C  v_func_type,
	Admin_instrs_ok v_S v_C [(AI_NOP )] v_func_type ->
	Step_pure [(AI_NOP )] [] ->
	Admin_instrs_ok v_S v_C [] v_func_type.
Proof.
	move => v_S v_C v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].

	let ts1 := fresh "ts1_comp" in
    let ts2 := fresh "ts2_comp" in
    let ts3 := fresh "ts3_comp" in
    let ts4 := fresh "ts4_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    let H3 := fresh "H3_comp" in
    let H4 := fresh "H4_comp" in
	rewrite -> app_left_single_nil in HType;
    apply admin_composition_typing_single in HType; destruct HType as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]];
	try apply admin_empty in H3.
	
	subst.
	apply Admin_instrs_ok__frame.
	apply Nop_typing in H4_comp; subst.
	apply admin_weakening_empty_both.
	apply Admin_instrs_ok__empty.
Qed.


Theorem t_preservation: forall c1 ts c2,
	Step c1 c2 ->
	Config_ok c1 ts ->
	Config_ok c2 ts.
Proof.
	move=> c1 ts c2 HStep HType.
Admitted.