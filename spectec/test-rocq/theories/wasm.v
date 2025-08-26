(* Imported Code *)
From Stdlib Require Import String List Unicode.Utf8 Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From HB Require Import structures.
From RecordUpdate Require Import RecordSet.
Declare Scope wasm_scope.

Class Inhabited (T: Type) := { default_val : T }.

Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=
	List.nth n l default_val.

Definition the {T : Type} {_ : Inhabited T} (arg : option T) : T :=
	match arg with
		| None => default_val
		| Some v => v
	end.

Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
	List.map (fun '(x, y) => f x y) (List.combine xs ys).

Definition option_zipWith {α β γ: Type} (f: α -> β -> γ) (x: option α) (y: option β): option γ := 
	match x, y with
		| Some x, Some y => Some (f x y)
		| _, _ => None
	end.

Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=
	match l, n with
		| nil, _ => nil
		| x :: l', O => y :: l'
		| x :: l', S n => x :: list_update l' n y
	end.

Definition option_append {α: Type} (x y: option α) : option α :=
	match x with
		| Some _ => x
		| None => y
	end.

Definition option_map {α β : Type} (f : α -> β) (x : option α) : option β :=
	match x with
		| Some x => Some (f x)
		| _ => None
	end.

Fixpoint list_update_func {α: Type} (l: list α) (n: nat) (y: α -> α): list α :=
	match l, n with
		| nil, _ => nil
		| x :: l', O => (y x) :: l'
		| x :: l', S n => x :: list_update_func l' n y
	end.

Fixpoint list_slice {α: Type} (l: list α) (i: nat) (j: nat): list α :=
	match l, i, j with
		| nil, _, _ => nil
		| x :: l', O, O => nil
		| x :: l', S n, O => nil
		| x :: l', O, S m => x :: list_slice l' 0 m
		| x :: l', S n, m => list_slice l' n m
	end.

Fixpoint list_slice_update {α: Type} (l: list α) (i: nat) (j: nat) (update_l: list α): list α :=
	match l, i, j, update_l with
		| nil, _, _, _ => nil
		| l', _, _, nil => l'
		| x :: l', O, O, _ => nil
		| x :: l', S n, O, _ => nil
		| x :: l', O, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'
		| x :: l', S n, m, _ => x :: list_slice_update l' n m update_l
	end.

Definition list_extend {α: Type} (l: list α) (y: α): list α :=
	y :: l.

Class Append (α: Type) := _append : α -> α -> α.

Infix "@@" := _append (right associativity, at level 60) : wasm_scope.

Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.

Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.

Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.

Global Instance Inh_unit : Inhabited unit := { default_val := tt }.

Global Instance Inh_nat : Inhabited nat := { default_val := O }.

Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.

Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.

Global Instance Inh_Z : Inhabited Z := { default_val := Z0 }.

Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.

Global Instance Inh_type : Inhabited Type := { default_val := nat }.

Definition option_to_list {T: Type} (arg : option T) : list T :=
	match arg with
		| None => nil
		| Some a => a :: nil
	end.

Coercion option_to_list: option >-> list.

Coercion Z.to_nat: Z >-> nat.

Coercion Z.of_nat: nat >-> Z.

Coercion ratz: int >-> rat.

Create HintDb eq_dec_db.

Ltac decidable_equality_step :=
  do [ by eauto with eq_dec_db | decide equality ].

Lemma eq_dec_Equality_axiom :
  forall (T : Type) (eq_dec : forall (x y : T), decidable (x = y)),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in Equality.axiom eqb.
Proof.
  move=> T eq_dec eqb x y. rewrite /eqb.
  case: (eq_dec x y); by [apply: ReflectT | apply: ReflectF].
Qed.

Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.

(* Generated Code *)
(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:7.1-7.15 *)
Definition res_N := nat.

Definition res_N_eq_dec : forall (v1 v2 : res_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition res_N_eqb (v1 v2 : res_N) : bool :=
	is_left(res_N_eq_dec v1 v2).
Definition eqres_NP : Equality.axiom (res_N_eqb) :=
	eq_dec_Equality_axiom (res_N) (res_N_eq_dec).

HB.instance Definition _ := hasDecEq.Build (res_N) (eqres_NP).
Hint Resolve res_N_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:8.1-8.15 *)
Definition M := nat.

Definition M_eq_dec : forall (v1 v2 : M),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition M_eqb (v1 v2 : M) : bool :=
	is_left(M_eq_dec v1 v2).
Definition eqMP : Equality.axiom (M_eqb) :=
	eq_dec_Equality_axiom (M) (M_eq_dec).

HB.instance Definition _ := hasDecEq.Build (M) (eqMP).
Hint Resolve M_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:9.1-9.15 *)
Definition n := nat.

Definition n_eq_dec : forall (v1 v2 : n),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition n_eqb (v1 v2 : n) : bool :=
	is_left(n_eq_dec v1 v2).
Definition eqnP : Equality.axiom (n_eqb) :=
	eq_dec_Equality_axiom (n) (n_eq_dec).

HB.instance Definition _ := hasDecEq.Build (n) (eqnP).
Hint Resolve n_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:10.1-10.15 *)
Definition m := nat.

Definition m_eq_dec : forall (v1 v2 : m),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition m_eqb (v1 v2 : m) : bool :=
	is_left(m_eq_dec v1 v2).
Definition eqmP : Equality.axiom (m_eqb) :=
	eq_dec_Equality_axiom (m) (m_eq_dec).

HB.instance Definition _ := hasDecEq.Build (m) (eqmP).
Hint Resolve m_eq_dec : eq_dec_db.

(* Global Declaration Definition at: ../specification/wasm-2.0/0-aux.spectec:15.1-15.14 *)
Definition fun_Ki : nat := 1024.

(* Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:21.1-21.25 *)
Axiom fun_min : forall (v_nat : nat) (v_nat_0 : nat), nat.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 *)
Fixpoint fun_sum (var_0 : (list nat)) : nat :=
	match var_0 return nat with
		| [] => 0
		| (v_n :: v_n') => (v_n + (fun_sum v_n'))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.44 *)
Definition fun_opt_ (v_X : Type) (var_0 : (list v_X)) : (option v_X) :=
	match v_X, var_0 return (option v_X) with
		| _, [] => None
		| _, [v_w] => (Some v_w)
		| _, (v_w :: v_w') => (Some v_w)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:37.1-37.45 *)
Definition fun_list_ (v_X : Type) (var_0 : (option v_X)) : (list v_X) :=
	match v_X, var_0 return (list v_X) with
		| _, None => []
		| _, (Some v_w) => [v_w]
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:41.1-41.86 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:41.1-41.86 *)
Fixpoint fun_concat_ (v_X : Type) (var_0 : (list (list v_X))) : (list v_X) :=
	match v_X, var_0 return (list v_X) with
		| _, [] => []
		| _, (v_w :: v_w') => (v_w ++ (fun_concat_ v_X v_w'))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:45.1-45.39 *)
Axiom fun_inv_concat_ : forall (v_X : Type) (var_0 : (list v_X)), (list (list v_X)).

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:52.1-52.46 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:52.1-52.46 *)
Fixpoint fun_setproduct2_ (v_X : Type) (v_X_0 : v_X) (var_0 : (list (list v_X))) : (list (list v_X)) :=
	match v_X, v_X_0, var_0 return (list (list v_X)) with
		| _, v_w_1, [] => []
		| _, v_w_1, (v_w' :: v_w) => ([([v_w_1] ++ v_w')] ++ (fun_setproduct2_ v_X v_w_1 v_w))
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.47 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.47 *)
Fixpoint fun_setproduct1_ (v_X : Type) (var_0 : (list v_X)) (var_1 : (list (list v_X))) : (list (list v_X)) :=
	match v_X, var_0, var_1 return (list (list v_X)) with
		| _, [], v_w => []
		| _, (v_w_1 :: v_w'), v_w => ((fun_setproduct2_ v_X v_w_1 v_w) ++ (fun_setproduct1_ v_X v_w' v_w))
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.84 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.84 *)
Fixpoint fun_setproduct_ (v_X : Type) (var_0 : (list (list v_X))) : (list (list v_X)) :=
	match v_X, var_0 return (list (list v_X)) with
		| _, [] => [[]]
		| _, (v_w_1 :: v_w) => (fun_setproduct1_ v_X v_w_1 (fun_setproduct_ v_X v_w))
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
Inductive res_list (v_X : Type) : Type :=
	| mk_list (_ : (list v_X)) : res_list v_X.

Global Instance Inhabited__res_list (v_X : Type) : Inhabited (res_list v_X) := { default_val := mk_list v_X default_val }.

(* FIXME - No clear way to do decidable equality *)
Definition res_list_eq_dec : forall (v_X : Type) (v1 v2 : res_list v_X),
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition res_list_eqb (v_X : Type) (v1 v2 : res_list v_X) : bool :=
	is_left(res_list_eq_dec v_X v1 v2).
Definition eqres_listP (v_X : Type) : Equality.axiom (res_list_eqb v_X) :=
	eq_dec_Equality_axiom (res_list v_X) (res_list_eq_dec v_X).

HB.instance Definition _ (v_X : Type) := hasDecEq.Build (res_list v_X) (eqres_listP v_X).
Hint Resolve res_list_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
Definition wf_list (v_X : Type) (v_x : (res_list v_X)) : Prop :=
	match v_X, v_x return Prop with
		| _, (mk_list v_X) => ((List.length v_X) < (2 ^ 32))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
Definition fun_proj_list_0 (v_X : Type) (v_x : (res_list v_X)) : (list v_X) :=
	match v_X, v_x return (list v_X) with
		| _, (mk_list v_v_X_list_0) => v_v_X_list_0
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 *)
Inductive bit : Type :=
	| mk_bit (v_i : nat) : bit.

Global Instance Inhabited__bit : Inhabited (bit) := { default_val := mk_bit default_val }.

Definition bit_eq_dec : forall (v1 v2 : bit),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition bit_eqb (v1 v2 : bit) : bool :=
	is_left(bit_eq_dec v1 v2).
Definition eqbitP : Equality.axiom (bit_eqb) :=
	eq_dec_Equality_axiom (bit) (bit_eq_dec).

HB.instance Definition _ := hasDecEq.Build (bit) (eqbitP).
Hint Resolve bit_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 *)
Definition wf_bit (v_x : bit) : Prop :=
	match v_x return Prop with
		| (mk_bit v_i) => ((v_i = 0) \/ (v_i = 1))
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
Inductive byte : Type :=
	| mk_byte (v_i : nat) : byte.

Global Instance Inhabited__byte : Inhabited (byte) := { default_val := mk_byte default_val }.

Definition byte_eq_dec : forall (v1 v2 : byte),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition byte_eqb (v1 v2 : byte) : bool :=
	is_left(byte_eq_dec v1 v2).
Definition eqbyteP : Equality.axiom (byte_eqb) :=
	eq_dec_Equality_axiom (byte) (byte_eq_dec).

HB.instance Definition _ := hasDecEq.Build (byte) (eqbyteP).
Hint Resolve byte_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
Definition wf_byte (v_x : byte) : Prop :=
	match v_x return Prop with
		| (mk_byte v_i) => ((v_i >= 0) /\ (v_i <= 255))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
Definition fun_proj_byte_0 (v_x : byte) : nat :=
	match v_x return nat with
		| (mk_byte v_v_num_0) => v_v_num_0
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
Inductive uN (v_N : res_N) : Type :=
	| mk_uN (v_i : nat) : uN v_N.

Global Instance Inhabited__uN (v_N : res_N) : Inhabited (uN v_N) := { default_val := mk_uN v_N default_val }.

Definition uN_eq_dec : forall (v_N : res_N) (v1 v2 : uN v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition uN_eqb (v_N : res_N) (v1 v2 : uN v_N) : bool :=
	is_left(uN_eq_dec v_N v1 v2).
Definition equNP (v_N : res_N) : Equality.axiom (uN_eqb v_N) :=
	eq_dec_Equality_axiom (uN v_N) (uN_eq_dec v_N).

HB.instance Definition _ (v_N : res_N) := hasDecEq.Build (uN v_N) (equNP v_N).
Hint Resolve uN_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
Definition wf_uN (v_N : res_N) (v_x : (uN v_N)) : Prop :=
	match v_N, v_x return Prop with
		| v_N, (mk_uN v_i) => ((v_i >= 0) /\ (v_i <= ((((2 ^ v_N) : nat) - (1 : nat)) : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
Definition fun_proj_uN_0 (v_N : res_N) (v_x : (uN v_N)) : nat :=
	match v_N, v_x return nat with
		| v_N, (mk_uN v_v_num_0) => v_v_num_0
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
Inductive sN (v_N : res_N) : Type :=
	| mk_sN (v_i : nat) : sN v_N.

Global Instance Inhabited__sN (v_N : res_N) : Inhabited (sN v_N) := { default_val := mk_sN v_N default_val }.

Definition sN_eq_dec : forall (v_N : res_N) (v1 v2 : sN v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition sN_eqb (v_N : res_N) (v1 v2 : sN v_N) : bool :=
	is_left(sN_eq_dec v_N v1 v2).
Definition eqsNP (v_N : res_N) : Equality.axiom (sN_eqb v_N) :=
	eq_dec_Equality_axiom (sN v_N) (sN_eq_dec v_N).

HB.instance Definition _ (v_N : res_N) := hasDecEq.Build (sN v_N) (eqsNP v_N).
Hint Resolve sN_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
Definition wf_sN (v_N : res_N) (v_x : (sN v_N)) : Prop :=
	match v_N, v_x return Prop with
		| v_N, (mk_sN v_i) => ((((v_i >= (0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat))) /\ (v_i <= (0 - (1 : nat)))) \/ (v_i = (0 : nat))) \/ ((v_i >= (0 + (1 : nat))) /\ (v_i <= (((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat) - (1 : nat)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
Definition fun_proj_sN_0 (v_N : res_N) (v_x : (sN v_N)) : nat :=
	match v_N, v_x return nat with
		| v_N, (mk_sN v_v_num_0) => v_v_num_0
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:22.1-23.8 *)
Definition iN (v_N : res_N) := (uN v_N).

Definition iN_eq_dec : forall (v_N : res_N) (v1 v2 : iN v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition iN_eqb (v_N : res_N) (v1 v2 : iN v_N) : bool :=
	is_left(iN_eq_dec v_N v1 v2).
Definition eqiNP (v_N : res_N) : Equality.axiom (iN_eqb v_N) :=
	eq_dec_Equality_axiom (iN v_N) (iN_eq_dec v_N).

HB.instance Definition _ (v_N : res_N) := hasDecEq.Build (iN v_N) (eqiNP v_N).
Hint Resolve iN_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:25.1-25.18 *)
Definition u8 := (uN 8).

Definition u8_eq_dec : forall (v1 v2 : u8),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition u8_eqb (v1 v2 : u8) : bool :=
	is_left(u8_eq_dec v1 v2).
Definition equ8P : Equality.axiom (u8_eqb) :=
	eq_dec_Equality_axiom (u8) (u8_eq_dec).

HB.instance Definition _ := hasDecEq.Build (u8) (equ8P).
Hint Resolve u8_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:26.1-26.20 *)
Definition u16 := (uN 16).

Definition u16_eq_dec : forall (v1 v2 : u16),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition u16_eqb (v1 v2 : u16) : bool :=
	is_left(u16_eq_dec v1 v2).
Definition equ16P : Equality.axiom (u16_eqb) :=
	eq_dec_Equality_axiom (u16) (u16_eq_dec).

HB.instance Definition _ := hasDecEq.Build (u16) (equ16P).
Hint Resolve u16_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:27.1-27.20 *)
Definition u31 := (uN 31).

Definition u31_eq_dec : forall (v1 v2 : u31),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition u31_eqb (v1 v2 : u31) : bool :=
	is_left(u31_eq_dec v1 v2).
Definition equ31P : Equality.axiom (u31_eqb) :=
	eq_dec_Equality_axiom (u31) (u31_eq_dec).

HB.instance Definition _ := hasDecEq.Build (u31) (equ31P).
Hint Resolve u31_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:28.1-28.20 *)
Definition u32 := (uN 32).

Definition u32_eq_dec : forall (v1 v2 : u32),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition u32_eqb (v1 v2 : u32) : bool :=
	is_left(u32_eq_dec v1 v2).
Definition equ32P : Equality.axiom (u32_eqb) :=
	eq_dec_Equality_axiom (u32) (u32_eq_dec).

HB.instance Definition _ := hasDecEq.Build (u32) (equ32P).
Hint Resolve u32_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:29.1-29.20 *)
Definition u64 := (uN 64).

Definition u64_eq_dec : forall (v1 v2 : u64),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition u64_eqb (v1 v2 : u64) : bool :=
	is_left(u64_eq_dec v1 v2).
Definition equ64P : Equality.axiom (u64_eqb) :=
	eq_dec_Equality_axiom (u64) (u64_eq_dec).

HB.instance Definition _ := hasDecEq.Build (u64) (equ64P).
Hint Resolve u64_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:30.1-30.22 *)
Definition u128 := (uN 128).

Definition u128_eq_dec : forall (v1 v2 : u128),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition u128_eqb (v1 v2 : u128) : bool :=
	is_left(u128_eq_dec v1 v2).
Definition equ128P : Equality.axiom (u128_eqb) :=
	eq_dec_Equality_axiom (u128) (u128_eq_dec).

HB.instance Definition _ := hasDecEq.Build (u128) (equ128P).
Hint Resolve u128_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:31.1-31.20 *)
Definition s33 := (sN 33).

Definition s33_eq_dec : forall (v1 v2 : s33),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition s33_eqb (v1 v2 : s33) : bool :=
	is_left(s33_eq_dec v1 v2).
Definition eqs33P : Equality.axiom (s33_eqb) :=
	eq_dec_Equality_axiom (s33) (s33_eq_dec).

HB.instance Definition _ := hasDecEq.Build (s33) (eqs33P).
Hint Resolve s33_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:38.1-38.35 *)
Definition fun_signif (v_N : res_N) : (option nat) :=
	match v_N return (option nat) with
		| 32 => (Some 23)
		| 64 => (Some 52)
		| v_x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:42.1-42.34 *)
Definition fun_expon (v_N : res_N) : (option nat) :=
	match v_N return (option nat) with
		| 32 => (Some 8)
		| 64 => (Some 11)
		| v_x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:46.1-46.30 *)
Definition fun_M (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (the (fun_signif v_N))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:49.1-49.30 *)
Definition fun_E (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (the (fun_expon v_N))
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:56.1-56.30 *)
Definition exp := nat.

Definition exp_eq_dec : forall (v1 v2 : exp),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition exp_eqb (v1 v2 : exp) : bool :=
	is_left(exp_eq_dec v1 v2).
Definition eqexpP : Equality.axiom (exp_eqb) :=
	eq_dec_Equality_axiom (exp) (exp_eq_dec).

HB.instance Definition _ := hasDecEq.Build (exp) (eqexpP).
Hint Resolve exp_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:57.1-61.84 *)
Inductive fNmag (v_N : res_N) : Type :=
	| NORM (v_m : m) (v_exp : exp) : fNmag v_N
	| SUBNORM (v_m : m) : fNmag v_N
	| INF : fNmag v_N
	| NAN (v_m : m) : fNmag v_N.

Global Instance Inhabited__fNmag (v_N : res_N) : Inhabited (fNmag v_N) := { default_val := NORM v_N default_val default_val }.

Definition fNmag_eq_dec : forall (v_N : res_N) (v1 v2 : fNmag v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition fNmag_eqb (v_N : res_N) (v1 v2 : fNmag v_N) : bool :=
	is_left(fNmag_eq_dec v_N v1 v2).
Definition eqfNmagP (v_N : res_N) : Equality.axiom (fNmag_eqb v_N) :=
	eq_dec_Equality_axiom (fNmag v_N) (fNmag_eq_dec v_N).

HB.instance Definition _ (v_N : res_N) := hasDecEq.Build (fNmag v_N) (eqfNmagP v_N).
Hint Resolve fNmag_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:57.1-61.84 *)
Definition wf_fNmag (v_N : res_N) (v_x : (fNmag v_N)) : Prop :=
	match v_N, v_x return Prop with
		| v_N, (NORM v_m v_exp) => ((v_m < (2 ^ (fun_M v_N))) /\ ((((2 : nat) - ((2 ^ ((((fun_E v_N) : nat) - (1 : nat)) : nat)) : nat)) <= v_exp) /\ (v_exp <= (((2 ^ ((((fun_E v_N) : nat) - (1 : nat)) : nat)) : nat) - (1 : nat)))))
		| v_N, (SUBNORM v_m) => forall (v_exp : exp), ((v_m < (2 ^ (fun_M v_N))) /\ (((2 : nat) - ((2 ^ ((((fun_E v_N) : nat) - (1 : nat)) : nat)) : nat)) = v_exp))
		| v_N, (NAN v_m) => ((1 <= v_m) /\ (v_m < (2 ^ (fun_M v_N))))
		| _, _ => true
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:52.1-54.35 *)
Inductive fN (v_N : res_N) : Type :=
	| POS (v_fNmag : (fNmag v_N)) : fN v_N
	| NEG (v_fNmag : (fNmag v_N)) : fN v_N.

Global Instance Inhabited__fN (v_N : res_N) : Inhabited (fN v_N) := { default_val := POS v_N default_val }.

(* FIXME - No clear way to do decidable equality *)
Definition fN_eq_dec : forall (v_N : res_N) (v1 v2 : fN v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition fN_eqb (v_N : res_N) (v1 v2 : fN v_N) : bool :=
	is_left(fN_eq_dec v_N v1 v2).
Definition eqfNP (v_N : res_N) : Equality.axiom (fN_eqb v_N) :=
	eq_dec_Equality_axiom (fN v_N) (fN_eq_dec v_N).

HB.instance Definition _ (v_N : res_N) := hasDecEq.Build (fN v_N) (eqfNP v_N).
Hint Resolve fN_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:63.1-63.20 *)
Definition f32 := (fN 32).

Definition f32_eq_dec : forall (v1 v2 : f32),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition f32_eqb (v1 v2 : f32) : bool :=
	is_left(f32_eq_dec v1 v2).
Definition eqf32P : Equality.axiom (f32_eqb) :=
	eq_dec_Equality_axiom (f32) (f32_eq_dec).

HB.instance Definition _ := hasDecEq.Build (f32) (eqf32P).
Hint Resolve f32_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:64.1-64.20 *)
Definition f64 := (fN 64).

Definition f64_eq_dec : forall (v1 v2 : f64),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition f64_eqb (v1 v2 : f64) : bool :=
	is_left(f64_eq_dec v1 v2).
Definition eqf64P : Equality.axiom (f64_eqb) :=
	eq_dec_Equality_axiom (f64) (f64_eq_dec).

HB.instance Definition _ := hasDecEq.Build (f64) (eqf64P).
Hint Resolve f64_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:66.1-66.39 *)
Definition fun_fzero (v_N : res_N) : (fN v_N) :=
	match v_N return (fN v_N) with
		| v_N => (POS _ (SUBNORM _ 0))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:69.1-69.39 *)
Definition fun_fone (v_N : res_N) : (fN v_N) :=
	match v_N return (fN v_N) with
		| v_N => (POS _ (NORM _ 1 (0 : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:72.1-72.21 *)
Definition fun_canon_ (v_N : res_N) : nat :=
	match v_N return nat with
		| v_N => (2 ^ ((((the (fun_signif v_N)) : nat) - (1 : nat)) : nat))
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:78.1-79.8 *)
Definition vN (v_N : res_N) := (iN v_N).

Definition vN_eq_dec : forall (v_N : res_N) (v1 v2 : vN v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vN_eqb (v_N : res_N) (v1 v2 : vN v_N) : bool :=
	is_left(vN_eq_dec v_N v1 v2).
Definition eqvNP (v_N : res_N) : Equality.axiom (vN_eqb v_N) :=
	eq_dec_Equality_axiom (vN v_N) (vN_eq_dec v_N).

HB.instance Definition _ (v_N : res_N) := hasDecEq.Build (vN v_N) (eqvNP v_N).
Hint Resolve vN_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:86.1-86.85 *)
Inductive char : Type :=
	| mk_char (v_i : nat) : char.

Global Instance Inhabited__char : Inhabited (char) := { default_val := mk_char default_val }.

Definition char_eq_dec : forall (v1 v2 : char),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition char_eqb (v1 v2 : char) : bool :=
	is_left(char_eq_dec v1 v2).
Definition eqcharP : Equality.axiom (char_eqb) :=
	eq_dec_Equality_axiom (char) (char_eq_dec).

HB.instance Definition _ := hasDecEq.Build (char) (eqcharP).
Hint Resolve char_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:86.1-86.85 *)
Definition wf_char (v_x : char) : Prop :=
	match v_x return Prop with
		| (mk_char v_i) => (((v_i >= 0) /\ (v_i <= 55295)) \/ ((v_i >= 57344) /\ (v_i <= 1114111)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:86.1-86.85 *)
Definition fun_proj_char_0 (v_x : char) : nat :=
	match v_x return nat with
		| (mk_char v_v_num_0) => v_v_num_0
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.25 *)
(* Axiom Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.25 *)
Axiom fun_utf8 : forall (var_0 : (list char)), (list byte).

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.70 *)
Inductive name : Type :=
	| mk_name (_ : (list char)) : name.

Global Instance Inhabited__name : Inhabited (name) := { default_val := mk_name default_val }.

Definition name_eq_dec : forall (v1 v2 : name),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition name_eqb (v1 v2 : name) : bool :=
	is_left(name_eq_dec v1 v2).
Definition eqnameP : Equality.axiom (name_eqb) :=
	eq_dec_Equality_axiom (name) (name_eq_dec).

HB.instance Definition _ := hasDecEq.Build (name) (eqnameP).
Hint Resolve name_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.70 *)
Definition wf_name (v_x : name) : Prop :=
	match v_x return Prop with
		| (mk_name v_char) => ((List.length (fun_utf8 v_char)) < (2 ^ 32))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.70 *)
Definition fun_proj_name_0 (v_x : name) : (list char) :=
	match v_x return (list char) with
		| (mk_name v_v_char_list_0) => v_v_char_list_0
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:99.1-99.36 *)
Definition idx := u32.

Definition idx_eq_dec : forall (v1 v2 : idx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition idx_eqb (v1 v2 : idx) : bool :=
	is_left(idx_eq_dec v1 v2).
Definition eqidxP : Equality.axiom (idx_eqb) :=
	eq_dec_Equality_axiom (idx) (idx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (idx) (eqidxP).
Hint Resolve idx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:100.1-100.44 *)
Definition laneidx := u8.

Definition laneidx_eq_dec : forall (v1 v2 : laneidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition laneidx_eqb (v1 v2 : laneidx) : bool :=
	is_left(laneidx_eq_dec v1 v2).
Definition eqlaneidxP : Equality.axiom (laneidx_eqb) :=
	eq_dec_Equality_axiom (laneidx) (laneidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (laneidx) (eqlaneidxP).
Hint Resolve laneidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:102.1-102.45 *)
Definition typeidx := idx.

Definition typeidx_eq_dec : forall (v1 v2 : typeidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition typeidx_eqb (v1 v2 : typeidx) : bool :=
	is_left(typeidx_eq_dec v1 v2).
Definition eqtypeidxP : Equality.axiom (typeidx_eqb) :=
	eq_dec_Equality_axiom (typeidx) (typeidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (typeidx) (eqtypeidxP).
Hint Resolve typeidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:103.1-103.49 *)
Definition funcidx := idx.

Definition funcidx_eq_dec : forall (v1 v2 : funcidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition funcidx_eqb (v1 v2 : funcidx) : bool :=
	is_left(funcidx_eq_dec v1 v2).
Definition eqfuncidxP : Equality.axiom (funcidx_eqb) :=
	eq_dec_Equality_axiom (funcidx) (funcidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (funcidx) (eqfuncidxP).
Hint Resolve funcidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:104.1-104.49 *)
Definition globalidx := idx.

Definition globalidx_eq_dec : forall (v1 v2 : globalidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globalidx_eqb (v1 v2 : globalidx) : bool :=
	is_left(globalidx_eq_dec v1 v2).
Definition eqglobalidxP : Equality.axiom (globalidx_eqb) :=
	eq_dec_Equality_axiom (globalidx) (globalidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globalidx) (eqglobalidxP).
Hint Resolve globalidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:105.1-105.47 *)
Definition tableidx := idx.

Definition tableidx_eq_dec : forall (v1 v2 : tableidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tableidx_eqb (v1 v2 : tableidx) : bool :=
	is_left(tableidx_eq_dec v1 v2).
Definition eqtableidxP : Equality.axiom (tableidx_eqb) :=
	eq_dec_Equality_axiom (tableidx) (tableidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tableidx) (eqtableidxP).
Hint Resolve tableidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:106.1-106.46 *)
Definition memidx := idx.

Definition memidx_eq_dec : forall (v1 v2 : memidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memidx_eqb (v1 v2 : memidx) : bool :=
	is_left(memidx_eq_dec v1 v2).
Definition eqmemidxP : Equality.axiom (memidx_eqb) :=
	eq_dec_Equality_axiom (memidx) (memidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memidx) (eqmemidxP).
Hint Resolve memidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:107.1-107.45 *)
Definition elemidx := idx.

Definition elemidx_eq_dec : forall (v1 v2 : elemidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elemidx_eqb (v1 v2 : elemidx) : bool :=
	is_left(elemidx_eq_dec v1 v2).
Definition eqelemidxP : Equality.axiom (elemidx_eqb) :=
	eq_dec_Equality_axiom (elemidx) (elemidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elemidx) (eqelemidxP).
Hint Resolve elemidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:108.1-108.45 *)
Definition dataidx := idx.

Definition dataidx_eq_dec : forall (v1 v2 : dataidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition dataidx_eqb (v1 v2 : dataidx) : bool :=
	is_left(dataidx_eq_dec v1 v2).
Definition eqdataidxP : Equality.axiom (dataidx_eqb) :=
	eq_dec_Equality_axiom (dataidx) (dataidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (dataidx) (eqdataidxP).
Hint Resolve dataidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:109.1-109.47 *)
Definition labelidx := idx.

Definition labelidx_eq_dec : forall (v1 v2 : labelidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition labelidx_eqb (v1 v2 : labelidx) : bool :=
	is_left(labelidx_eq_dec v1 v2).
Definition eqlabelidxP : Equality.axiom (labelidx_eqb) :=
	eq_dec_Equality_axiom (labelidx) (labelidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (labelidx) (eqlabelidxP).
Hint Resolve labelidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:110.1-110.47 *)
Definition localidx := idx.

Definition localidx_eq_dec : forall (v1 v2 : localidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition localidx_eqb (v1 v2 : localidx) : bool :=
	is_left(localidx_eq_dec v1 v2).
Definition eqlocalidxP : Equality.axiom (localidx_eqb) :=
	eq_dec_Equality_axiom (localidx) (localidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (localidx) (eqlocalidxP).
Hint Resolve localidx_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:124.1-125.26 *)
Inductive numtype : Type :=
	| I32 : numtype
	| I64 : numtype
	| F32 : numtype
	| F64 : numtype.

Global Instance Inhabited__numtype : Inhabited (numtype) := { default_val := I32 }.

Definition numtype_eq_dec : forall (v1 v2 : numtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition numtype_eqb (v1 v2 : numtype) : bool :=
	is_left(numtype_eq_dec v1 v2).
Definition eqnumtypeP : Equality.axiom (numtype_eqb) :=
	eq_dec_Equality_axiom (numtype) (numtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (numtype) (eqnumtypeP).
Hint Resolve numtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:127.1-128.9 *)
Inductive vectype : Type :=
	| V128 : vectype.

Global Instance Inhabited__vectype : Inhabited (vectype) := { default_val := V128 }.

Definition vectype_eq_dec : forall (v1 v2 : vectype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vectype_eqb (v1 v2 : vectype) : bool :=
	is_left(vectype_eq_dec v1 v2).
Definition eqvectypeP : Equality.axiom (vectype_eqb) :=
	eq_dec_Equality_axiom (vectype) (vectype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vectype) (eqvectypeP).
Hint Resolve vectype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:130.1-131.22 *)
Inductive consttype : Type :=
	| const_I32 : consttype
	| const_I64 : consttype
	| const_F32 : consttype
	| const_F64 : consttype
	| const_V128 : consttype.

Global Instance Inhabited__consttype : Inhabited (consttype) := { default_val := const_I32 }.

Definition consttype_eq_dec : forall (v1 v2 : consttype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition consttype_eqb (v1 v2 : consttype) : bool :=
	is_left(consttype_eq_dec v1 v2).
Definition eqconsttypeP : Equality.axiom (consttype_eqb) :=
	eq_dec_Equality_axiom (consttype) (consttype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (consttype) (eqconsttypeP).
Hint Resolve consttype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:133.1-134.24 *)
Inductive reftype : Type :=
	| FUNCREF : reftype
	| EXTERNREF : reftype.

Global Instance Inhabited__reftype : Inhabited (reftype) := { default_val := FUNCREF }.

Definition reftype_eq_dec : forall (v1 v2 : reftype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition reftype_eqb (v1 v2 : reftype) : bool :=
	is_left(reftype_eq_dec v1 v2).
Definition eqreftypeP : Equality.axiom (reftype_eqb) :=
	eq_dec_Equality_axiom (reftype) (reftype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (reftype) (eqreftypeP).
Hint Resolve reftype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:136.1-137.38 *)
Inductive valtype : Type :=
	| VALTYPE_I32 : valtype
	| VALTYPE_I64 : valtype
	| VALTYPE_F32 : valtype
	| VALTYPE_F64 : valtype
	| VALTYPE_V128 : valtype
	| VALTYPE_FUNCREF : valtype
	| VALTYPE_EXTERNREF : valtype
	| VALTYPE_BOT : valtype.

Global Instance Inhabited__valtype : Inhabited (valtype) := { default_val := VALTYPE_I32 }.

Definition valtype_eq_dec : forall (v1 v2 : valtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition valtype_eqb (v1 v2 : valtype) : bool :=
	is_left(valtype_eq_dec v1 v2).
Definition eqvaltypeP : Equality.axiom (valtype_eqb) :=
	eq_dec_Equality_axiom (valtype) (valtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (valtype) (eqvaltypeP).
Hint Resolve valtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:139.1-139.58 *)
Inductive Inn : Type :=
	| INN_I32 : Inn
	| INN_I64 : Inn.

Global Instance Inhabited__Inn : Inhabited (Inn) := { default_val := INN_I32 }.

Definition Inn_eq_dec : forall (v1 v2 : Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Inn_eqb (v1 v2 : Inn) : bool :=
	is_left(Inn_eq_dec v1 v2).
Definition eqInnP : Equality.axiom (Inn_eqb) :=
	eq_dec_Equality_axiom (Inn) (Inn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Inn) (eqInnP).
Hint Resolve Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:140.1-140.58 *)
Inductive Fnn : Type :=
	| FNN_F32 : Fnn
	| FNN_F64 : Fnn.

Global Instance Inhabited__Fnn : Inhabited (Fnn) := { default_val := FNN_F32 }.

Definition Fnn_eq_dec : forall (v1 v2 : Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Fnn_eqb (v1 v2 : Fnn) : bool :=
	is_left(Fnn_eq_dec v1 v2).
Definition eqFnnP : Equality.axiom (Fnn_eqb) :=
	eq_dec_Equality_axiom (Fnn) (Fnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Fnn) (eqFnnP).
Hint Resolve Fnn_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:141.1-141.56 *)
Definition Vnn := vectype.

Definition Vnn_eq_dec : forall (v1 v2 : Vnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Vnn_eqb (v1 v2 : Vnn) : bool :=
	is_left(Vnn_eq_dec v1 v2).
Definition eqVnnP : Equality.axiom (Vnn_eqb) :=
	eq_dec_Equality_axiom (Vnn) (Vnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Vnn) (eqVnnP).
Hint Resolve Vnn_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:144.1-145.16 *)
Definition resulttype := (res_list valtype).

Definition resulttype_eq_dec : forall (v1 v2 : resulttype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition resulttype_eqb (v1 v2 : resulttype) : bool :=
	is_left(resulttype_eq_dec v1 v2).
Definition eqresulttypeP : Equality.axiom (resulttype_eqb) :=
	eq_dec_Equality_axiom (resulttype) (resulttype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (resulttype) (eqresulttypeP).
Hint Resolve resulttype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:150.1-150.52 *)
Inductive packtype : Type :=
	| I8 : packtype
	| I16 : packtype.

Global Instance Inhabited__packtype : Inhabited (packtype) := { default_val := I8 }.

Definition packtype_eq_dec : forall (v1 v2 : packtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition packtype_eqb (v1 v2 : packtype) : bool :=
	is_left(packtype_eq_dec v1 v2).
Definition eqpacktypeP : Equality.axiom (packtype_eqb) :=
	eq_dec_Equality_axiom (packtype) (packtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (packtype) (eqpacktypeP).
Hint Resolve packtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:151.1-151.85 *)
Inductive lanetype : Type :=
	| LANETYPE_I32 : lanetype
	| LANETYPE_I64 : lanetype
	| LANETYPE_F32 : lanetype
	| LANETYPE_F64 : lanetype
	| LANETYPE_I8 : lanetype
	| LANETYPE_I16 : lanetype.

Global Instance Inhabited__lanetype : Inhabited (lanetype) := { default_val := LANETYPE_I32 }.

Definition lanetype_eq_dec : forall (v1 v2 : lanetype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition lanetype_eqb (v1 v2 : lanetype) : bool :=
	is_left(lanetype_eq_dec v1 v2).
Definition eqlanetypeP : Equality.axiom (lanetype_eqb) :=
	eq_dec_Equality_axiom (lanetype) (lanetype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (lanetype) (eqlanetypeP).
Hint Resolve lanetype_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:153.1-153.57 *)
Definition Pnn := packtype.

Definition Pnn_eq_dec : forall (v1 v2 : Pnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Pnn_eqb (v1 v2 : Pnn) : bool :=
	is_left(Pnn_eq_dec v1 v2).
Definition eqPnnP : Equality.axiom (Pnn_eqb) :=
	eq_dec_Equality_axiom (Pnn) (Pnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Pnn) (eqPnnP).
Hint Resolve Pnn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:154.1-154.58 *)
Inductive Jnn : Type :=
	| JNN_I32 : Jnn
	| JNN_I64 : Jnn
	| JNN_I8 : Jnn
	| JNN_I16 : Jnn.

Global Instance Inhabited__Jnn : Inhabited (Jnn) := { default_val := JNN_I32 }.

Definition Jnn_eq_dec : forall (v1 v2 : Jnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Jnn_eqb (v1 v2 : Jnn) : bool :=
	is_left(Jnn_eq_dec v1 v2).
Definition eqJnnP : Equality.axiom (Jnn_eqb) :=
	eq_dec_Equality_axiom (Jnn) (Jnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Jnn) (eqJnnP).
Hint Resolve Jnn_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:155.1-155.57 *)
Definition Lnn := lanetype.

Definition Lnn_eq_dec : forall (v1 v2 : Lnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition Lnn_eqb (v1 v2 : Lnn) : bool :=
	is_left(Lnn_eq_dec v1 v2).
Definition eqLnnP : Equality.axiom (Lnn_eqb) :=
	eq_dec_Equality_axiom (Lnn) (Lnn_eq_dec).

HB.instance Definition _ := hasDecEq.Build (Lnn) (eqLnnP).
Hint Resolve Lnn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:160.1-160.22 *)
Inductive mutopt : Type :=
	| MUT : mutopt.

Global Instance Inhabited__mutopt : Inhabited (mutopt) := { default_val := MUT }.

Definition mutopt_eq_dec : forall (v1 v2 : mutopt),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition mutopt_eqb (v1 v2 : mutopt) : bool :=
	is_left(mutopt_eq_dec v1 v2).
Definition eqmutoptP : Equality.axiom (mutopt_eqb) :=
	eq_dec_Equality_axiom (mutopt) (mutopt_eq_dec).

HB.instance Definition _ := hasDecEq.Build (mutopt) (eqmutoptP).
Hint Resolve mutopt_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:161.1-161.21 *)
Definition mut := (option mutopt).

Definition mut_eq_dec : forall (v1 v2 : mut),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition mut_eqb (v1 v2 : mut) : bool :=
	is_left(mut_eq_dec v1 v2).
Definition eqmutP : Equality.axiom (mut_eqb) :=
	eq_dec_Equality_axiom (mut) (mut_eq_dec).

HB.instance Definition _ := hasDecEq.Build (mut) (eqmutP).
Hint Resolve mut_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:163.1-164.16 *)
Inductive limits : Type :=
	| mk_limits (v_u32 : u32) (v__ : u32) : limits.

Global Instance Inhabited__limits : Inhabited (limits) := { default_val := mk_limits default_val default_val }.

Definition limits_eq_dec : forall (v1 v2 : limits),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition limits_eqb (v1 v2 : limits) : bool :=
	is_left(limits_eq_dec v1 v2).
Definition eqlimitsP : Equality.axiom (limits_eqb) :=
	eq_dec_Equality_axiom (limits) (limits_eq_dec).

HB.instance Definition _ := hasDecEq.Build (limits) (eqlimitsP).
Hint Resolve limits_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:166.1-167.14 *)
Inductive globaltype : Type :=
	| mk_globaltype (v_mut : mut) (v_valtype : valtype) : globaltype.

Global Instance Inhabited__globaltype : Inhabited (globaltype) := { default_val := mk_globaltype default_val default_val }.

Definition globaltype_eq_dec : forall (v1 v2 : globaltype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globaltype_eqb (v1 v2 : globaltype) : bool :=
	is_left(globaltype_eq_dec v1 v2).
Definition eqglobaltypeP : Equality.axiom (globaltype_eqb) :=
	eq_dec_Equality_axiom (globaltype) (globaltype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globaltype) (eqglobaltypeP).
Hint Resolve globaltype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:168.1-169.27 *)
Inductive functype : Type :=
	| mk_functype (v_resulttype : resulttype) (v__ : resulttype) : functype.

Global Instance Inhabited__functype : Inhabited (functype) := { default_val := mk_functype default_val default_val }.

Definition functype_eq_dec : forall (v1 v2 : functype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition functype_eqb (v1 v2 : functype) : bool :=
	is_left(functype_eq_dec v1 v2).
Definition eqfunctypeP : Equality.axiom (functype_eqb) :=
	eq_dec_Equality_axiom (functype) (functype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (functype) (eqfunctypeP).
Hint Resolve functype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:170.1-171.17 *)
Inductive tabletype : Type :=
	| mk_tabletype (v_limits : limits) (v_reftype : reftype) : tabletype.

Global Instance Inhabited__tabletype : Inhabited (tabletype) := { default_val := mk_tabletype default_val default_val }.

Definition tabletype_eq_dec : forall (v1 v2 : tabletype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tabletype_eqb (v1 v2 : tabletype) : bool :=
	is_left(tabletype_eq_dec v1 v2).
Definition eqtabletypeP : Equality.axiom (tabletype_eqb) :=
	eq_dec_Equality_axiom (tabletype) (tabletype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tabletype) (eqtabletypeP).
Hint Resolve tabletype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:172.1-173.14 *)
Inductive memtype : Type :=
	| PAGE (v_limits : limits) : memtype.

Global Instance Inhabited__memtype : Inhabited (memtype) := { default_val := PAGE default_val }.

Definition memtype_eq_dec : forall (v1 v2 : memtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memtype_eqb (v1 v2 : memtype) : bool :=
	is_left(memtype_eq_dec v1 v2).
Definition eqmemtypeP : Equality.axiom (memtype_eqb) :=
	eq_dec_Equality_axiom (memtype) (memtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memtype) (eqmemtypeP).
Hint Resolve memtype_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:174.1-175.10 *)
Definition elemtype := reftype.

Definition elemtype_eq_dec : forall (v1 v2 : elemtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elemtype_eqb (v1 v2 : elemtype) : bool :=
	is_left(elemtype_eq_dec v1 v2).
Definition eqelemtypeP : Equality.axiom (elemtype_eqb) :=
	eq_dec_Equality_axiom (elemtype) (elemtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elemtype) (eqelemtypeP).
Hint Resolve elemtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:176.1-177.5 *)
Inductive datatype : Type :=
	| OK : datatype.

Global Instance Inhabited__datatype : Inhabited (datatype) := { default_val := OK }.

Definition datatype_eq_dec : forall (v1 v2 : datatype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition datatype_eqb (v1 v2 : datatype) : bool :=
	is_left(datatype_eq_dec v1 v2).
Definition eqdatatypeP : Equality.axiom (datatype_eqb) :=
	eq_dec_Equality_axiom (datatype) (datatype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (datatype) (eqdatatypeP).
Hint Resolve datatype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:178.1-179.70 *)
Inductive externtype : Type :=
	| EXT_FUNC (v_functype : functype) : externtype
	| EXT_GLOBAL (v_globaltype : globaltype) : externtype
	| EXT_TABLE (v_tabletype : tabletype) : externtype
	| EXT_MEM (v_memtype : memtype) : externtype.

Global Instance Inhabited__externtype : Inhabited (externtype) := { default_val := EXT_FUNC default_val }.

Definition externtype_eq_dec : forall (v1 v2 : externtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition externtype_eqb (v1 v2 : externtype) : bool :=
	is_left(externtype_eq_dec v1 v2).
Definition eqexterntypeP : Equality.axiom (externtype_eqb) :=
	eq_dec_Equality_axiom (externtype) (externtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (externtype) (eqexterntypeP).
Hint Resolve externtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:339.1-339.60 *)
Inductive dim : Type :=
	| mk_dim (v_i : nat) : dim.

Global Instance Inhabited__dim : Inhabited (dim) := { default_val := mk_dim default_val }.

Definition dim_eq_dec : forall (v1 v2 : dim),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition dim_eqb (v1 v2 : dim) : bool :=
	is_left(dim_eq_dec v1 v2).
Definition eqdimP : Equality.axiom (dim_eqb) :=
	eq_dec_Equality_axiom (dim) (dim_eq_dec).

HB.instance Definition _ := hasDecEq.Build (dim) (eqdimP).
Hint Resolve dim_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:339.1-339.60 *)
Definition wf_dim (v_x : dim) : Prop :=
	match v_x return Prop with
		| (mk_dim v_i) => (((((v_i = 1) \/ (v_i = 2)) \/ (v_i = 4)) \/ (v_i = 8)) \/ (v_i = 16))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:339.1-339.60 *)
Definition fun_proj_dim_0 (v_x : dim) : nat :=
	match v_x return nat with
		| (mk_dim v_v_num_0) => v_v_num_0
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:340.1-340.69 *)
Inductive shape : Type :=
	| X (v_lanetype : lanetype) (v_dim : dim) : shape.

Global Instance Inhabited__shape : Inhabited (shape) := { default_val := X default_val default_val }.

Definition shape_eq_dec : forall (v1 v2 : shape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition shape_eqb (v1 v2 : shape) : bool :=
	is_left(shape_eq_dec v1 v2).
Definition eqshapeP : Equality.axiom (shape_eqb) :=
	eq_dec_Equality_axiom (shape) (shape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (shape) (eqshapeP).
Hint Resolve shape_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:205.1-205.32 *)
Definition fun_lanetype (v_shape : shape) : lanetype :=
	match v_shape return lanetype with
		| (X v_Lnn (mk_dim v_N)) => v_Lnn
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:207.1-207.59 *)
Definition fun_size (v_valtype : valtype) : (option nat) :=
	match v_valtype return (option nat) with
		| (VALTYPE_I32) => (Some 32)
		| (VALTYPE_I64) => (Some 64)
		| (VALTYPE_F32) => (Some 32)
		| (VALTYPE_F64) => (Some 64)
		| (VALTYPE_V128) => (Some 128)
		| v_x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:208.1-208.45 *)
Definition fun_psize (v_packtype : packtype) : nat :=
	match v_packtype return nat with
		| (I8) => 8
		| (I16) => 16
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 *)
Definition fun_coec_numtype__valtype (v_numtype : numtype) : valtype :=
	match v_numtype return valtype with
		| (I32) => VALTYPE_I32
		| (I64) => VALTYPE_I64
		| (F32) => VALTYPE_F32
		| (F64) => VALTYPE_F64
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 *)
Coercion fun_coec_numtype__valtype : numtype >-> valtype.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 *)
Definition fun_lsize (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| (LANETYPE_I32) => (the (fun_size (I32 : valtype)))
		| (LANETYPE_I64) => (the (fun_size (I64 : valtype)))
		| (LANETYPE_F32) => (the (fun_size (F32 : valtype)))
		| (LANETYPE_F64) => (the (fun_size (F64 : valtype)))
		| (LANETYPE_I8) => (fun_psize I8)
		| (LANETYPE_I16) => (fun_psize I16)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.70 *)
Definition fun_coec_Inn__valtype (v_Inn : Inn) : valtype :=
	match v_Inn return valtype with
		| (INN_I32) => VALTYPE_I32
		| (INN_I64) => VALTYPE_I64
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.70 *)
Coercion fun_coec_Inn__valtype : Inn >-> valtype.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.70 *)
Definition fun_isize (v_Inn : Inn) : nat :=
	match v_Inn return nat with
		| (INN_I32) => (the (fun_size (INN_I32 : valtype)))
		| (INN_I64) => (the (fun_size (INN_I64 : valtype)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 *)
Definition fun_coec_Jnn__lanetype (v_Jnn : Jnn) : lanetype :=
	match v_Jnn return lanetype with
		| (JNN_I32) => LANETYPE_I32
		| (JNN_I64) => LANETYPE_I64
		| (JNN_I8) => LANETYPE_I8
		| (JNN_I16) => LANETYPE_I16
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 *)
Coercion fun_coec_Jnn__lanetype : Jnn >-> lanetype.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 *)
Definition fun_jsize (v_Jnn : Jnn) : nat :=
	match v_Jnn return nat with
		| (JNN_I32) => (fun_lsize (JNN_I32 : lanetype))
		| (JNN_I64) => (fun_lsize (JNN_I64 : lanetype))
		| (JNN_I8) => (fun_lsize (JNN_I8 : lanetype))
		| (JNN_I16) => (fun_lsize (JNN_I16 : lanetype))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 *)
Definition fun_coec_Fnn__valtype (v_Fnn : Fnn) : valtype :=
	match v_Fnn return valtype with
		| (FNN_F32) => VALTYPE_F32
		| (FNN_F64) => VALTYPE_F64
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 *)
Coercion fun_coec_Fnn__valtype : Fnn >-> valtype.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 *)
Definition fun_fsize (v_Fnn : Fnn) : nat :=
	match v_Fnn return nat with
		| (FNN_F32) => (the (fun_size (FNN_F32 : valtype)))
		| (FNN_F64) => (the (fun_size (FNN_F64 : valtype)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:230.1-230.63 *)
Definition fun_sizenn (v_numtype : numtype) : nat :=
	match v_numtype return nat with
		| (I32) => (the (fun_size (I32 : valtype)))
		| (I64) => (the (fun_size (I64 : valtype)))
		| (F32) => (the (fun_size (F32 : valtype)))
		| (F64) => (the (fun_size (F64 : valtype)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:231.1-231.63 *)
Definition fun_sizenn1 (v_numtype : numtype) : nat :=
	match v_numtype return nat with
		| (I32) => (the (fun_size (I32 : valtype)))
		| (I64) => (the (fun_size (I64 : valtype)))
		| (F32) => (the (fun_size (F32 : valtype)))
		| (F64) => (the (fun_size (F64 : valtype)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:232.1-232.63 *)
Definition fun_sizenn2 (v_numtype : numtype) : nat :=
	match v_numtype return nat with
		| (I32) => (the (fun_size (I32 : valtype)))
		| (I64) => (the (fun_size (I64 : valtype)))
		| (F32) => (the (fun_size (F32 : valtype)))
		| (F64) => (the (fun_size (F64 : valtype)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:237.1-237.63 *)
Definition fun_lsizenn (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| v_lt => (fun_lsize v_lt)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:238.1-238.63 *)
Definition fun_lsizenn1 (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| v_lt => (fun_lsize v_lt)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:239.1-239.63 *)
Definition fun_lsizenn2 (v_lanetype : lanetype) : nat :=
	match v_lanetype return nat with
		| v_lt => (fun_lsize v_lt)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:244.1-244.40 *)
Definition fun_inv_isize (v_nat : nat) : (option Inn) :=
	match v_nat return (option Inn) with
		| 32 => (Some INN_I32)
		| 64 => (Some INN_I64)
		| v_x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.26 *)
Definition fun_coec_Inn__Jnn (v_Inn : Inn) : Jnn :=
	match v_Inn return Jnn with
		| (INN_I32) => JNN_I32
		| (INN_I64) => JNN_I64
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.26 *)
Coercion fun_coec_Inn__Jnn : Inn >-> Jnn.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.26 *)
Definition fun_inv_jsize (v_nat : nat) : Jnn :=
	match v_nat return Jnn with
		| 8 => JNN_I8
		| 16 => JNN_I16
		| v_n => ((the (fun_inv_isize v_n)) : Jnn)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:246.1-246.40 *)
Definition fun_inv_fsize (v_nat : nat) : (option Fnn) :=
	match v_nat return (option Fnn) with
		| 32 => (Some FNN_F32)
		| 64 => (Some FNN_F64)
		| v_x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:257.1-257.21 *)
Definition fun_coec_Inn__numtype (v_Inn : Inn) : numtype :=
	match v_Inn return numtype with
		| (INN_I32) => I32
		| (INN_I64) => I64
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:257.1-257.21 *)
Coercion fun_coec_Inn__numtype : Inn >-> numtype.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:257.1-257.21 *)
Definition fun_coec_Fnn__numtype (v_Fnn : Fnn) : numtype :=
	match v_Fnn return numtype with
		| (FNN_F32) => F32
		| (FNN_F64) => F64
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:257.1-257.21 *)
Coercion fun_coec_Fnn__numtype : Fnn >-> numtype.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:257.1-257.21 *)
Definition num_ (v_numtype : numtype): Type :=
	match v_numtype with
		| (I32) => (iN (fun_sizenn (INN_I32 : numtype)))
		| (I64) => (iN (fun_sizenn (INN_I64 : numtype)))
		| (F32) => (fN (fun_sizenn (FNN_F32 : numtype)))
		| (F64) => (fN (fun_sizenn (FNN_F64 : numtype)))
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:261.1-261.36 *)
Definition pack_ (v_Pnn : Pnn) := (iN (fun_psize v_Pnn)).

Definition pack__eq_dec : forall (v_Pnn : Pnn) (v1 v2 : pack_ v_Pnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition pack__eqb (v_Pnn : Pnn) (v1 v2 : pack_ v_Pnn) : bool :=
	is_left(pack__eq_dec v_Pnn v1 v2).
Definition eqpack_P (v_Pnn : Pnn) : Equality.axiom (pack__eqb v_Pnn) :=
	eq_dec_Equality_axiom (pack_ v_Pnn) (pack__eq_dec v_Pnn).

HB.instance Definition _ (v_Pnn : Pnn) := hasDecEq.Build (pack_ v_Pnn) (eqpack_P v_Pnn).
Hint Resolve pack__eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:263.1-263.23 *)
Definition lane_ (v_lanetype : lanetype): Type :=
	match v_lanetype with
		| (LANETYPE_I32) => (uN 32)
		| (LANETYPE_I64) => (uN 64)
		| (LANETYPE_F32) => (fN 32)
		| (LANETYPE_F64) => (fN 64)
		| (LANETYPE_I8) => (pack_ I8)
		| (LANETYPE_I16) => (pack_ I16)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:268.1-268.34 *)
Definition fun_coec_vectype__valtype (v_vectype : vectype) : valtype :=
	match v_vectype return valtype with
		| (V128) => VALTYPE_V128
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:268.1-268.34 *)
Coercion fun_coec_vectype__valtype : vectype >-> valtype.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:268.1-268.34 *)
Definition vec_ (v_Vnn : Vnn) := (vN (the (fun_size (v_Vnn : valtype)))).

Definition vec__eq_dec : forall (v_Vnn : Vnn) (v1 v2 : vec_ v_Vnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vec__eqb (v_Vnn : Vnn) (v1 v2 : vec_ v_Vnn) : bool :=
	is_left(vec__eq_dec v_Vnn v1 v2).
Definition eqvec_P (v_Vnn : Vnn) : Equality.axiom (vec__eqb v_Vnn) :=
	eq_dec_Equality_axiom (vec_ v_Vnn) (vec__eq_dec v_Vnn).

HB.instance Definition _ (v_Vnn : Vnn) := hasDecEq.Build (vec_ v_Vnn) (eqvec_P v_Vnn).
Hint Resolve vec__eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:270.1-270.35 *)
Definition fun_zero (v_numtype : numtype) : (num_ v_numtype) :=
	match v_numtype return (num_ v_numtype) with
		| (I32) => (mk_uN _ 0)
		| (I64) => (mk_uN _ 0)
		| (F32) => (fun_fzero (the (fun_size (FNN_F32 : valtype))))
		| (F64) => (fun_fzero (the (fun_size (FNN_F64 : valtype))))
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:277.1-277.42 *)
Inductive sx : Type :=
	| U : sx
	| res_S : sx.

Global Instance Inhabited__sx : Inhabited (sx) := { default_val := U }.

Definition sx_eq_dec : forall (v1 v2 : sx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition sx_eqb (v1 v2 : sx) : bool :=
	is_left(sx_eq_dec v1 v2).
Definition eqsxP : Equality.axiom (sx_eqb) :=
	eq_dec_Equality_axiom (sx) (sx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (sx) (eqsxP).
Hint Resolve sx_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:278.1-278.56 *)
Inductive sz : Type :=
	| mk_sz (v_i : nat) : sz.

Global Instance Inhabited__sz : Inhabited (sz) := { default_val := mk_sz default_val }.

Definition sz_eq_dec : forall (v1 v2 : sz),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition sz_eqb (v1 v2 : sz) : bool :=
	is_left(sz_eq_dec v1 v2).
Definition eqszP : Equality.axiom (sz_eqb) :=
	eq_dec_Equality_axiom (sz) (sz_eq_dec).

HB.instance Definition _ := hasDecEq.Build (sz) (eqszP).
Hint Resolve sz_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:278.1-278.56 *)
Definition wf_sz (v_x : sz) : Prop :=
	match v_x return Prop with
		| (mk_sz v_i) => ((((v_i = 8) \/ (v_i = 16)) \/ (v_i = 32)) \/ (v_i = 64))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:278.1-278.56 *)
Definition fun_proj_sz_0 (v_x : sz) : nat :=
	match v_x return nat with
		| (mk_sz v_v_num_0) => v_v_num_0
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.22 *)
Inductive unop_Inn (v_Inn : Inn) : Type :=
	| INT_CLZ : unop_Inn v_Inn
	| INT_CTZ : unop_Inn v_Inn
	| INT_POPCNT : unop_Inn v_Inn
	| INT_EXTEND (v_n : n) : unop_Inn v_Inn.

Global Instance Inhabited__unop_Inn (v_Inn : Inn) : Inhabited (unop_Inn v_Inn) := { default_val := INT_CLZ v_Inn }.

Definition unop_Inn_eq_dec : forall (v_Inn : Inn) (v1 v2 : unop_Inn v_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition unop_Inn_eqb (v_Inn : Inn) (v1 v2 : unop_Inn v_Inn) : bool :=
	is_left(unop_Inn_eq_dec v_Inn v1 v2).
Definition equnop_InnP (v_Inn : Inn) : Equality.axiom (unop_Inn_eqb v_Inn) :=
	eq_dec_Equality_axiom (unop_Inn v_Inn) (unop_Inn_eq_dec v_Inn).

HB.instance Definition _ (v_Inn : Inn) := hasDecEq.Build (unop_Inn v_Inn) (equnop_InnP v_Inn).
Hint Resolve unop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.22 *)
Inductive unop_Fnn (v_Fnn : Fnn) : Type :=
	| FLOAT_ABS : unop_Fnn v_Fnn
	| FLOAT_NEG : unop_Fnn v_Fnn
	| FLOAT_SQRT : unop_Fnn v_Fnn
	| FLOAT_CEIL : unop_Fnn v_Fnn
	| FLOAT_FLOOR : unop_Fnn v_Fnn
	| FLOAT_TRUNC : unop_Fnn v_Fnn
	| FLOAT_NEAREST : unop_Fnn v_Fnn.

Global Instance Inhabited__unop_Fnn (v_Fnn : Fnn) : Inhabited (unop_Fnn v_Fnn) := { default_val := FLOAT_ABS v_Fnn }.

Definition unop_Fnn_eq_dec : forall (v_Fnn : Fnn) (v1 v2 : unop_Fnn v_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition unop_Fnn_eqb (v_Fnn : Fnn) (v1 v2 : unop_Fnn v_Fnn) : bool :=
	is_left(unop_Fnn_eq_dec v_Fnn v1 v2).
Definition equnop_FnnP (v_Fnn : Fnn) : Equality.axiom (unop_Fnn_eqb v_Fnn) :=
	eq_dec_Equality_axiom (unop_Fnn v_Fnn) (unop_Fnn_eq_dec v_Fnn).

HB.instance Definition _ (v_Fnn : Fnn) := hasDecEq.Build (unop_Fnn v_Fnn) (equnop_FnnP v_Fnn).
Hint Resolve unop_Fnn_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.22 *)
Definition unop_ (v_numtype : numtype): Type :=
	match v_numtype with
		| (I32) => (unop_Inn INN_I32)
		| (I64) => (unop_Inn INN_I64)
		| (F32) => (unop_Fnn FNN_F32)
		| (F64) => (unop_Fnn FNN_F64)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.23 *)
Inductive binop_Inn (v_Inn : Inn) : Type :=
	| INT_ADD : binop_Inn v_Inn
	| INT_SUB : binop_Inn v_Inn
	| INT_MUL : binop_Inn v_Inn
	| INT_DIV (v_sx : sx) : binop_Inn v_Inn
	| INT_REM (v_sx : sx) : binop_Inn v_Inn
	| INT_AND : binop_Inn v_Inn
	| INT_OR : binop_Inn v_Inn
	| INT_XOR : binop_Inn v_Inn
	| INT_SHL : binop_Inn v_Inn
	| INT_SHR (v_sx : sx) : binop_Inn v_Inn
	| INT_ROTL : binop_Inn v_Inn
	| INT_ROTR : binop_Inn v_Inn.

Global Instance Inhabited__binop_Inn (v_Inn : Inn) : Inhabited (binop_Inn v_Inn) := { default_val := INT_ADD v_Inn }.

Definition binop_Inn_eq_dec : forall (v_Inn : Inn) (v1 v2 : binop_Inn v_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition binop_Inn_eqb (v_Inn : Inn) (v1 v2 : binop_Inn v_Inn) : bool :=
	is_left(binop_Inn_eq_dec v_Inn v1 v2).
Definition eqbinop_InnP (v_Inn : Inn) : Equality.axiom (binop_Inn_eqb v_Inn) :=
	eq_dec_Equality_axiom (binop_Inn v_Inn) (binop_Inn_eq_dec v_Inn).

HB.instance Definition _ (v_Inn : Inn) := hasDecEq.Build (binop_Inn v_Inn) (eqbinop_InnP v_Inn).
Hint Resolve binop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.23 *)
Inductive binop_Fnn (v_Fnn : Fnn) : Type :=
	| FLOAT_ADD : binop_Fnn v_Fnn
	| FLOAT_SUB : binop_Fnn v_Fnn
	| FLOAT_MUL : binop_Fnn v_Fnn
	| FLOAT_DIV : binop_Fnn v_Fnn
	| FLOAT_MIN : binop_Fnn v_Fnn
	| FLOAT_MAX : binop_Fnn v_Fnn
	| FLOAT_COPYSIGN : binop_Fnn v_Fnn.

Global Instance Inhabited__binop_Fnn (v_Fnn : Fnn) : Inhabited (binop_Fnn v_Fnn) := { default_val := FLOAT_ADD v_Fnn }.

Definition binop_Fnn_eq_dec : forall (v_Fnn : Fnn) (v1 v2 : binop_Fnn v_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition binop_Fnn_eqb (v_Fnn : Fnn) (v1 v2 : binop_Fnn v_Fnn) : bool :=
	is_left(binop_Fnn_eq_dec v_Fnn v1 v2).
Definition eqbinop_FnnP (v_Fnn : Fnn) : Equality.axiom (binop_Fnn_eqb v_Fnn) :=
	eq_dec_Equality_axiom (binop_Fnn v_Fnn) (binop_Fnn_eq_dec v_Fnn).

HB.instance Definition _ (v_Fnn : Fnn) := hasDecEq.Build (binop_Fnn v_Fnn) (eqbinop_FnnP v_Fnn).
Hint Resolve binop_Fnn_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.23 *)
Definition binop_ (v_numtype : numtype): Type :=
	match v_numtype with
		| (I32) => (binop_Inn INN_I32)
		| (I64) => (binop_Inn INN_I64)
		| (F32) => (binop_Fnn FNN_F32)
		| (F64) => (binop_Fnn FNN_F64)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:309.1-309.38 *)
Inductive testop_Inn (v_Inn : Inn) : Type :=
	| EQZ : testop_Inn v_Inn.

Global Instance Inhabited__testop_Inn (v_Inn : Inn) : Inhabited (testop_Inn v_Inn) := { default_val := EQZ v_Inn }.

Definition testop_Inn_eq_dec : forall (v_Inn : Inn) (v1 v2 : testop_Inn v_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition testop_Inn_eqb (v_Inn : Inn) (v1 v2 : testop_Inn v_Inn) : bool :=
	is_left(testop_Inn_eq_dec v_Inn v1 v2).
Definition eqtestop_InnP (v_Inn : Inn) : Equality.axiom (testop_Inn_eqb v_Inn) :=
	eq_dec_Equality_axiom (testop_Inn v_Inn) (testop_Inn_eq_dec v_Inn).

HB.instance Definition _ (v_Inn : Inn) := hasDecEq.Build (testop_Inn v_Inn) (eqtestop_InnP v_Inn).
Hint Resolve testop_Inn_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:309.1-309.38 *)
Definition testop_ (v_numtype : numtype): Type :=
	match v_numtype with
		| (I32) => (testop_Inn INN_I32)
		| (I64) => (testop_Inn INN_I64)
		| _ => default_val
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:313.1-313.23 *)
Inductive relop_Inn (v_Inn : Inn) : Type :=
	| INT_EQ : relop_Inn v_Inn
	| INT_NE : relop_Inn v_Inn
	| INT_LT (v_sx : sx) : relop_Inn v_Inn
	| INT_GT (v_sx : sx) : relop_Inn v_Inn
	| INT_LE (v_sx : sx) : relop_Inn v_Inn
	| INT_GE (v_sx : sx) : relop_Inn v_Inn.

Global Instance Inhabited__relop_Inn (v_Inn : Inn) : Inhabited (relop_Inn v_Inn) := { default_val := INT_EQ v_Inn }.

Definition relop_Inn_eq_dec : forall (v_Inn : Inn) (v1 v2 : relop_Inn v_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition relop_Inn_eqb (v_Inn : Inn) (v1 v2 : relop_Inn v_Inn) : bool :=
	is_left(relop_Inn_eq_dec v_Inn v1 v2).
Definition eqrelop_InnP (v_Inn : Inn) : Equality.axiom (relop_Inn_eqb v_Inn) :=
	eq_dec_Equality_axiom (relop_Inn v_Inn) (relop_Inn_eq_dec v_Inn).

HB.instance Definition _ (v_Inn : Inn) := hasDecEq.Build (relop_Inn v_Inn) (eqrelop_InnP v_Inn).
Hint Resolve relop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:313.1-313.23 *)
Inductive relop_Fnn (v_Fnn : Fnn) : Type :=
	| FLOAT_EQ : relop_Fnn v_Fnn
	| FLOAT_NE : relop_Fnn v_Fnn
	| FLOAT_LT : relop_Fnn v_Fnn
	| FLOAT_GT : relop_Fnn v_Fnn
	| FLOAT_LE : relop_Fnn v_Fnn
	| FLOAT_GE : relop_Fnn v_Fnn.

Global Instance Inhabited__relop_Fnn (v_Fnn : Fnn) : Inhabited (relop_Fnn v_Fnn) := { default_val := FLOAT_EQ v_Fnn }.

Definition relop_Fnn_eq_dec : forall (v_Fnn : Fnn) (v1 v2 : relop_Fnn v_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition relop_Fnn_eqb (v_Fnn : Fnn) (v1 v2 : relop_Fnn v_Fnn) : bool :=
	is_left(relop_Fnn_eq_dec v_Fnn v1 v2).
Definition eqrelop_FnnP (v_Fnn : Fnn) : Equality.axiom (relop_Fnn_eqb v_Fnn) :=
	eq_dec_Equality_axiom (relop_Fnn v_Fnn) (relop_Fnn_eq_dec v_Fnn).

HB.instance Definition _ (v_Fnn : Fnn) := hasDecEq.Build (relop_Fnn v_Fnn) (eqrelop_FnnP v_Fnn).
Hint Resolve relop_Fnn_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:313.1-313.23 *)
Definition relop_ (v_numtype : numtype): Type :=
	match v_numtype with
		| (I32) => (relop_Inn INN_I32)
		| (I64) => (relop_Inn INN_I64)
		| (F32) => (relop_Fnn FNN_F32)
		| (F64) => (relop_Fnn FNN_F64)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:326.1-334.16 *)
Inductive cvtop : Type :=
	| EXTEND (v_sx : sx) : cvtop
	| WRAP : cvtop
	| CONVERT (v_sx : sx) : cvtop
	| TRUNC (v_sx : sx) : cvtop
	| TRUNC_SAT (v_sx : sx) : cvtop
	| PROMOTE : cvtop
	| DEMOTE : cvtop
	| REINTERPRET : cvtop.

Global Instance Inhabited__cvtop : Inhabited (cvtop) := { default_val := EXTEND default_val }.

Definition cvtop_eq_dec : forall (v1 v2 : cvtop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition cvtop_eqb (v1 v2 : cvtop) : bool :=
	is_left(cvtop_eq_dec v1 v2).
Definition eqcvtopP : Equality.axiom (cvtop_eqb) :=
	eq_dec_Equality_axiom (cvtop) (cvtop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (cvtop) (eqcvtopP).
Hint Resolve cvtop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:341.1-341.86 *)
Inductive ishape : Type :=
	| IX (v_Jnn : Jnn) (v_dim : dim) : ishape.

Global Instance Inhabited__ishape : Inhabited (ishape) := { default_val := IX default_val default_val }.

Definition ishape_eq_dec : forall (v1 v2 : ishape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition ishape_eqb (v1 v2 : ishape) : bool :=
	is_left(ishape_eq_dec v1 v2).
Definition eqishapeP : Equality.axiom (ishape_eqb) :=
	eq_dec_Equality_axiom (ishape) (ishape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (ishape) (eqishapeP).
Hint Resolve ishape_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.86 *)
Inductive fshape : Type :=
	| FX (v_Fnn : Fnn) (v_dim : dim) : fshape.

Global Instance Inhabited__fshape : Inhabited (fshape) := { default_val := FX default_val default_val }.

Definition fshape_eq_dec : forall (v1 v2 : fshape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition fshape_eqb (v1 v2 : fshape) : bool :=
	is_left(fshape_eq_dec v1 v2).
Definition eqfshapeP : Equality.axiom (fshape_eqb) :=
	eq_dec_Equality_axiom (fshape) (fshape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (fshape) (eqfshapeP).
Hint Resolve fshape_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:343.1-343.86 *)
Inductive pshape : Type :=
	| PX (v_Pnn : Pnn) (v_dim : dim) : pshape.

Global Instance Inhabited__pshape : Inhabited (pshape) := { default_val := PX default_val default_val }.

Definition pshape_eq_dec : forall (v1 v2 : pshape),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition pshape_eqb (v1 v2 : pshape) : bool :=
	is_left(pshape_eq_dec v1 v2).
Definition eqpshapeP : Equality.axiom (pshape_eqb) :=
	eq_dec_Equality_axiom (pshape) (pshape_eq_dec).

HB.instance Definition _ := hasDecEq.Build (pshape) (eqpshapeP).
Hint Resolve pshape_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:345.1-345.22 *)
Definition fun_dim (v_shape : shape) : dim :=
	match v_shape return dim with
		| (X v_Lnn (mk_dim v_N)) => (mk_dim v_N)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:346.1-346.41 *)
Definition fun_shsize (v_shape : shape) : nat :=
	match v_shape return nat with
		| (X v_Lnn (mk_dim v_N)) => ((fun_lsize v_Lnn) * v_N)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:348.1-348.20 *)
Inductive vvunop : Type :=
	| NOT : vvunop.

Global Instance Inhabited__vvunop : Inhabited (vvunop) := { default_val := NOT }.

Definition vvunop_eq_dec : forall (v1 v2 : vvunop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvunop_eqb (v1 v2 : vvunop) : bool :=
	is_left(vvunop_eq_dec v1 v2).
Definition eqvvunopP : Equality.axiom (vvunop_eqb) :=
	eq_dec_Equality_axiom (vvunop) (vvunop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvunop) (eqvvunopP).
Hint Resolve vvunop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:349.1-349.41 *)
Inductive vvbinop : Type :=
	| AND : vvbinop
	| ANDNOT : vvbinop
	| OR : vvbinop
	| XOR : vvbinop.

Global Instance Inhabited__vvbinop : Inhabited (vvbinop) := { default_val := AND }.

Definition vvbinop_eq_dec : forall (v1 v2 : vvbinop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvbinop_eqb (v1 v2 : vvbinop) : bool :=
	is_left(vvbinop_eq_dec v1 v2).
Definition eqvvbinopP : Equality.axiom (vvbinop_eqb) :=
	eq_dec_Equality_axiom (vvbinop) (vvbinop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvbinop) (eqvvbinopP).
Hint Resolve vvbinop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.28 *)
Inductive vvternop : Type :=
	| BITSELECT : vvternop.

Global Instance Inhabited__vvternop : Inhabited (vvternop) := { default_val := BITSELECT }.

Definition vvternop_eq_dec : forall (v1 v2 : vvternop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvternop_eqb (v1 v2 : vvternop) : bool :=
	is_left(vvternop_eq_dec v1 v2).
Definition eqvvternopP : Equality.axiom (vvternop_eqb) :=
	eq_dec_Equality_axiom (vvternop) (vvternop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvternop) (eqvvternopP).
Hint Resolve vvternop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:351.1-351.27 *)
Inductive vvtestop : Type :=
	| ANY_TRUE : vvtestop.

Global Instance Inhabited__vvtestop : Inhabited (vvtestop) := { default_val := ANY_TRUE }.

Definition vvtestop_eq_dec : forall (v1 v2 : vvtestop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vvtestop_eqb (v1 v2 : vvtestop) : bool :=
	is_left(vvtestop_eq_dec v1 v2).
Definition eqvvtestopP : Equality.axiom (vvtestop_eqb) :=
	eq_dec_Equality_axiom (vvtestop) (vvtestop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vvtestop) (eqvvtestopP).
Hint Resolve vvtestop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:353.1-353.21 *)
Inductive vunop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Type :=
	| VINT_ABS : vunop_Jnn_N v_Jnn v_N
	| VINT_NEG : vunop_Jnn_N v_Jnn v_N
	| VINT_POPCNT : vunop_Jnn_N v_Jnn v_N.

Global Instance Inhabited__vunop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Inhabited (vunop_Jnn_N v_Jnn v_N) := { default_val := VINT_ABS v_Jnn v_N }.

Definition vunop_Jnn_N_eq_dec : forall (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vunop_Jnn_N v_Jnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vunop_Jnn_N_eqb (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vunop_Jnn_N v_Jnn v_N) : bool :=
	is_left(vunop_Jnn_N_eq_dec v_Jnn v_N v1 v2).
Definition eqvunop_Jnn_NP (v_Jnn : Jnn) (v_N : res_N) : Equality.axiom (vunop_Jnn_N_eqb v_Jnn v_N) :=
	eq_dec_Equality_axiom (vunop_Jnn_N v_Jnn v_N) (vunop_Jnn_N_eq_dec v_Jnn v_N).

HB.instance Definition _ (v_Jnn : Jnn) (v_N : res_N) := hasDecEq.Build (vunop_Jnn_N v_Jnn v_N) (eqvunop_Jnn_NP v_Jnn v_N).
Hint Resolve vunop_Jnn_N_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:353.1-353.21 *)
Definition wf_vunop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) (v_x : (vunop_Jnn_N v_Jnn v_N)) : Prop :=
	match v_Jnn, v_N, v_x return Prop with
		| v_Jnn, v_N, (VINT_POPCNT) => (v_Jnn = JNN_I8)
		| _, _, _ => true
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:353.1-353.21 *)
Inductive vunop_Fnn_N (v_Fnn : Fnn) (v_N : res_N) : Type :=
	| VFLOAT_ABS : vunop_Fnn_N v_Fnn v_N
	| VFLOAT_NEG : vunop_Fnn_N v_Fnn v_N
	| VFLOAT_SQRT : vunop_Fnn_N v_Fnn v_N
	| VFLOAT_CEIL : vunop_Fnn_N v_Fnn v_N
	| VFLOAT_FLOOR : vunop_Fnn_N v_Fnn v_N
	| VFLOAT_TRUNC : vunop_Fnn_N v_Fnn v_N
	| VFLOAT_NEAREST : vunop_Fnn_N v_Fnn v_N.

Global Instance Inhabited__vunop_Fnn_N (v_Fnn : Fnn) (v_N : res_N) : Inhabited (vunop_Fnn_N v_Fnn v_N) := { default_val := VFLOAT_ABS v_Fnn v_N }.

Definition vunop_Fnn_N_eq_dec : forall (v_Fnn : Fnn) (v_N : res_N) (v1 v2 : vunop_Fnn_N v_Fnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vunop_Fnn_N_eqb (v_Fnn : Fnn) (v_N : res_N) (v1 v2 : vunop_Fnn_N v_Fnn v_N) : bool :=
	is_left(vunop_Fnn_N_eq_dec v_Fnn v_N v1 v2).
Definition eqvunop_Fnn_NP (v_Fnn : Fnn) (v_N : res_N) : Equality.axiom (vunop_Fnn_N_eqb v_Fnn v_N) :=
	eq_dec_Equality_axiom (vunop_Fnn_N v_Fnn v_N) (vunop_Fnn_N_eq_dec v_Fnn v_N).

HB.instance Definition _ (v_Fnn : Fnn) (v_N : res_N) := hasDecEq.Build (vunop_Fnn_N v_Fnn v_N) (eqvunop_Fnn_NP v_Fnn v_N).
Hint Resolve vunop_Fnn_N_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:353.1-353.21 *)
Definition vunop_ (v_shape : shape): Type :=
	match v_shape with
		| (X (LANETYPE_I32) (mk_dim v_N)) => (vunop_Jnn_N JNN_I32 v_N)
		| (X (LANETYPE_I64) (mk_dim v_N)) => (vunop_Jnn_N JNN_I64 v_N)
		| (X (LANETYPE_I8) (mk_dim v_N)) => (vunop_Jnn_N JNN_I8 v_N)
		| (X (LANETYPE_I16) (mk_dim v_N)) => (vunop_Jnn_N JNN_I16 v_N)
		| (X (LANETYPE_F32) (mk_dim v_N)) => (vunop_Fnn_N FNN_F32 v_N)
		| (X (LANETYPE_F64) (mk_dim v_N)) => (vunop_Fnn_N FNN_F64 v_N)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:360.1-360.22 *)
Inductive vbinop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Type :=
	| VINT_ADD : vbinop_Jnn_N v_Jnn v_N
	| VINT_SUB : vbinop_Jnn_N v_Jnn v_N
	| VINT_ADD_SAT (v_sx : sx) : vbinop_Jnn_N v_Jnn v_N
	| VINT_SUB_SAT (v_sx : sx) : vbinop_Jnn_N v_Jnn v_N
	| VINT_MUL : vbinop_Jnn_N v_Jnn v_N
	| VINT_AVGRU : vbinop_Jnn_N v_Jnn v_N
	| VINT_Q15MULR_SATres_S : vbinop_Jnn_N v_Jnn v_N
	| VINT_MIN (v_sx : sx) : vbinop_Jnn_N v_Jnn v_N
	| VINT_MAX (v_sx : sx) : vbinop_Jnn_N v_Jnn v_N.

Global Instance Inhabited__vbinop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Inhabited (vbinop_Jnn_N v_Jnn v_N) := { default_val := VINT_ADD v_Jnn v_N }.

Definition vbinop_Jnn_N_eq_dec : forall (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vbinop_Jnn_N v_Jnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vbinop_Jnn_N_eqb (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vbinop_Jnn_N v_Jnn v_N) : bool :=
	is_left(vbinop_Jnn_N_eq_dec v_Jnn v_N v1 v2).
Definition eqvbinop_Jnn_NP (v_Jnn : Jnn) (v_N : res_N) : Equality.axiom (vbinop_Jnn_N_eqb v_Jnn v_N) :=
	eq_dec_Equality_axiom (vbinop_Jnn_N v_Jnn v_N) (vbinop_Jnn_N_eq_dec v_Jnn v_N).

HB.instance Definition _ (v_Jnn : Jnn) (v_N : res_N) := hasDecEq.Build (vbinop_Jnn_N v_Jnn v_N) (eqvbinop_Jnn_NP v_Jnn v_N).
Hint Resolve vbinop_Jnn_N_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:360.1-360.22 *)
Definition wf_vbinop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) (v_x : (vbinop_Jnn_N v_Jnn v_N)) : Prop :=
	match v_Jnn, v_N, v_x return Prop with
		| v_Jnn, v_N, (VINT_ADD_SAT v_sx) => ((fun_lsizenn (v_Jnn : lanetype)) <= 16)
		| v_Jnn, v_N, (VINT_SUB_SAT v_sx) => ((fun_lsizenn (v_Jnn : lanetype)) <= 16)
		| v_Jnn, v_N, (VINT_MUL) => ((fun_lsizenn (v_Jnn : lanetype)) >= 16)
		| v_Jnn, v_N, (VINT_AVGRU) => ((fun_lsizenn (v_Jnn : lanetype)) <= 16)
		| v_Jnn, v_N, (VINT_Q15MULR_SATres_S) => ((fun_lsizenn (v_Jnn : lanetype)) = 16)
		| v_Jnn, v_N, (VINT_MIN v_sx) => ((fun_lsizenn (v_Jnn : lanetype)) <= 32)
		| v_Jnn, v_N, (VINT_MAX v_sx) => ((fun_lsizenn (v_Jnn : lanetype)) <= 32)
		| _, _, _ => true
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:360.1-360.22 *)
Inductive vbinop_Fnn_N (v_Fnn : Fnn) (v_N : res_N) : Type :=
	| VFLOAT_ADD : vbinop_Fnn_N v_Fnn v_N
	| VFLOAT_SUB : vbinop_Fnn_N v_Fnn v_N
	| VFLOAT_MUL : vbinop_Fnn_N v_Fnn v_N
	| VFLOAT_DIV : vbinop_Fnn_N v_Fnn v_N
	| VFLOAT_MIN : vbinop_Fnn_N v_Fnn v_N
	| VFLOAT_MAX : vbinop_Fnn_N v_Fnn v_N
	| VFLOAT_PMIN : vbinop_Fnn_N v_Fnn v_N
	| VFLOAT_PMAX : vbinop_Fnn_N v_Fnn v_N.

Global Instance Inhabited__vbinop_Fnn_N (v_Fnn : Fnn) (v_N : res_N) : Inhabited (vbinop_Fnn_N v_Fnn v_N) := { default_val := VFLOAT_ADD v_Fnn v_N }.

Definition vbinop_Fnn_N_eq_dec : forall (v_Fnn : Fnn) (v_N : res_N) (v1 v2 : vbinop_Fnn_N v_Fnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vbinop_Fnn_N_eqb (v_Fnn : Fnn) (v_N : res_N) (v1 v2 : vbinop_Fnn_N v_Fnn v_N) : bool :=
	is_left(vbinop_Fnn_N_eq_dec v_Fnn v_N v1 v2).
Definition eqvbinop_Fnn_NP (v_Fnn : Fnn) (v_N : res_N) : Equality.axiom (vbinop_Fnn_N_eqb v_Fnn v_N) :=
	eq_dec_Equality_axiom (vbinop_Fnn_N v_Fnn v_N) (vbinop_Fnn_N_eq_dec v_Fnn v_N).

HB.instance Definition _ (v_Fnn : Fnn) (v_N : res_N) := hasDecEq.Build (vbinop_Fnn_N v_Fnn v_N) (eqvbinop_Fnn_NP v_Fnn v_N).
Hint Resolve vbinop_Fnn_N_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:360.1-360.22 *)
Definition vbinop_ (v_shape : shape): Type :=
	match v_shape with
		| (X (LANETYPE_I32) (mk_dim v_N)) => (vbinop_Jnn_N JNN_I32 v_N)
		| (X (LANETYPE_I64) (mk_dim v_N)) => (vbinop_Jnn_N JNN_I64 v_N)
		| (X (LANETYPE_I8) (mk_dim v_N)) => (vbinop_Jnn_N JNN_I8 v_N)
		| (X (LANETYPE_I16) (mk_dim v_N)) => (vbinop_Jnn_N JNN_I16 v_N)
		| (X (LANETYPE_F32) (mk_dim v_N)) => (vbinop_Fnn_N FNN_F32 v_N)
		| (X (LANETYPE_F64) (mk_dim v_N)) => (vbinop_Fnn_N FNN_F64 v_N)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.1-381.37 *)
Inductive vtestop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Type :=
	| ALL_TRUE : vtestop_Jnn_N v_Jnn v_N.

Global Instance Inhabited__vtestop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Inhabited (vtestop_Jnn_N v_Jnn v_N) := { default_val := ALL_TRUE v_Jnn v_N }.

Definition vtestop_Jnn_N_eq_dec : forall (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vtestop_Jnn_N v_Jnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vtestop_Jnn_N_eqb (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vtestop_Jnn_N v_Jnn v_N) : bool :=
	is_left(vtestop_Jnn_N_eq_dec v_Jnn v_N v1 v2).
Definition eqvtestop_Jnn_NP (v_Jnn : Jnn) (v_N : res_N) : Equality.axiom (vtestop_Jnn_N_eqb v_Jnn v_N) :=
	eq_dec_Equality_axiom (vtestop_Jnn_N v_Jnn v_N) (vtestop_Jnn_N_eq_dec v_Jnn v_N).

HB.instance Definition _ (v_Jnn : Jnn) (v_N : res_N) := hasDecEq.Build (vtestop_Jnn_N v_Jnn v_N) (eqvtestop_Jnn_NP v_Jnn v_N).
Hint Resolve vtestop_Jnn_N_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.1-381.37 *)
Definition vtestop_ (v_shape : shape): Type :=
	match v_shape with
		| (X (LANETYPE_I32) (mk_dim v_N)) => (vtestop_Jnn_N JNN_I32 v_N)
		| (X (LANETYPE_I64) (mk_dim v_N)) => (vtestop_Jnn_N JNN_I64 v_N)
		| (X (LANETYPE_I8) (mk_dim v_N)) => (vtestop_Jnn_N JNN_I8 v_N)
		| (X (LANETYPE_I16) (mk_dim v_N)) => (vtestop_Jnn_N JNN_I16 v_N)
		| _ => default_val
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.22 *)
Inductive vrelop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Type :=
	| VINT_EQ : vrelop_Jnn_N v_Jnn v_N
	| VINT_NE : vrelop_Jnn_N v_Jnn v_N
	| VINT_LT (v_sx : sx) : vrelop_Jnn_N v_Jnn v_N
	| VINT_GT (v_sx : sx) : vrelop_Jnn_N v_Jnn v_N
	| VINT_LE (v_sx : sx) : vrelop_Jnn_N v_Jnn v_N
	| VINT_GE (v_sx : sx) : vrelop_Jnn_N v_Jnn v_N.

Global Instance Inhabited__vrelop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Inhabited (vrelop_Jnn_N v_Jnn v_N) := { default_val := VINT_EQ v_Jnn v_N }.

Definition vrelop_Jnn_N_eq_dec : forall (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vrelop_Jnn_N v_Jnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vrelop_Jnn_N_eqb (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vrelop_Jnn_N v_Jnn v_N) : bool :=
	is_left(vrelop_Jnn_N_eq_dec v_Jnn v_N v1 v2).
Definition eqvrelop_Jnn_NP (v_Jnn : Jnn) (v_N : res_N) : Equality.axiom (vrelop_Jnn_N_eqb v_Jnn v_N) :=
	eq_dec_Equality_axiom (vrelop_Jnn_N v_Jnn v_N) (vrelop_Jnn_N_eq_dec v_Jnn v_N).

HB.instance Definition _ (v_Jnn : Jnn) (v_N : res_N) := hasDecEq.Build (vrelop_Jnn_N v_Jnn v_N) (eqvrelop_Jnn_NP v_Jnn v_N).
Hint Resolve vrelop_Jnn_N_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.22 *)
Definition wf_vrelop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) (v_x : (vrelop_Jnn_N v_Jnn v_N)) : Prop :=
	match v_Jnn, v_N, v_x return Prop with
		| v_Jnn, v_N, (VINT_LT v_sx) => (((fun_lsizenn (v_Jnn : lanetype)) <> 64) \/ (v_sx = res_S))
		| v_Jnn, v_N, (VINT_GT v_sx) => (((fun_lsizenn (v_Jnn : lanetype)) <> 64) \/ (v_sx = res_S))
		| v_Jnn, v_N, (VINT_LE v_sx) => (((fun_lsizenn (v_Jnn : lanetype)) <> 64) \/ (v_sx = res_S))
		| v_Jnn, v_N, (VINT_GE v_sx) => (((fun_lsizenn (v_Jnn : lanetype)) <> 64) \/ (v_sx = res_S))
		| _, _, _ => true
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.22 *)
Inductive vrelop_Fnn_N (v_Fnn : Fnn) (v_N : res_N) : Type :=
	| VFLOAT_EQ : vrelop_Fnn_N v_Fnn v_N
	| VFLOAT_NE : vrelop_Fnn_N v_Fnn v_N
	| VFLOAT_LT : vrelop_Fnn_N v_Fnn v_N
	| VFLOAT_GT : vrelop_Fnn_N v_Fnn v_N
	| VFLOAT_LE : vrelop_Fnn_N v_Fnn v_N
	| VFLOAT_GE : vrelop_Fnn_N v_Fnn v_N.

Global Instance Inhabited__vrelop_Fnn_N (v_Fnn : Fnn) (v_N : res_N) : Inhabited (vrelop_Fnn_N v_Fnn v_N) := { default_val := VFLOAT_EQ v_Fnn v_N }.

Definition vrelop_Fnn_N_eq_dec : forall (v_Fnn : Fnn) (v_N : res_N) (v1 v2 : vrelop_Fnn_N v_Fnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vrelop_Fnn_N_eqb (v_Fnn : Fnn) (v_N : res_N) (v1 v2 : vrelop_Fnn_N v_Fnn v_N) : bool :=
	is_left(vrelop_Fnn_N_eq_dec v_Fnn v_N v1 v2).
Definition eqvrelop_Fnn_NP (v_Fnn : Fnn) (v_N : res_N) : Equality.axiom (vrelop_Fnn_N_eqb v_Fnn v_N) :=
	eq_dec_Equality_axiom (vrelop_Fnn_N v_Fnn v_N) (vrelop_Fnn_N_eq_dec v_Fnn v_N).

HB.instance Definition _ (v_Fnn : Fnn) (v_N : res_N) := hasDecEq.Build (vrelop_Fnn_N v_Fnn v_N) (eqvrelop_Fnn_NP v_Fnn v_N).
Hint Resolve vrelop_Fnn_N_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.22 *)
Definition vrelop_ (v_shape : shape): Type :=
	match v_shape with
		| (X (LANETYPE_I32) (mk_dim v_N)) => (vrelop_Jnn_N JNN_I32 v_N)
		| (X (LANETYPE_I64) (mk_dim v_N)) => (vrelop_Jnn_N JNN_I64 v_N)
		| (X (LANETYPE_I8) (mk_dim v_N)) => (vrelop_Jnn_N JNN_I8 v_N)
		| (X (LANETYPE_I16) (mk_dim v_N)) => (vrelop_Jnn_N JNN_I16 v_N)
		| (X (LANETYPE_F32) (mk_dim v_N)) => (vrelop_Fnn_N FNN_F32 v_N)
		| (X (LANETYPE_F64) (mk_dim v_N)) => (vrelop_Fnn_N FNN_F64 v_N)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:401.1-401.48 *)
Inductive half : Type :=
	| LOW : half
	| HIGH : half.

Global Instance Inhabited__half : Inhabited (half) := { default_val := LOW }.

Definition half_eq_dec : forall (v1 v2 : half),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition half_eqb (v1 v2 : half) : bool :=
	is_left(half_eq_dec v1 v2).
Definition eqhalfP : Equality.axiom (half_eqb) :=
	eq_dec_Equality_axiom (half) (half_eq_dec).

HB.instance Definition _ := hasDecEq.Build (half) (eqhalfP).
Hint Resolve half_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:402.1-402.19 *)
Inductive zero : Type :=
	| ZERO : zero.

Global Instance Inhabited__zero : Inhabited (zero) := { default_val := ZERO }.

Definition zero_eq_dec : forall (v1 v2 : zero),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition zero_eqb (v1 v2 : zero) : bool :=
	is_left(zero_eq_dec v1 v2).
Definition eqzeroP : Equality.axiom (zero_eqb) :=
	eq_dec_Equality_axiom (zero) (zero_eq_dec).

HB.instance Definition _ := hasDecEq.Build (zero) (eqzeroP).
Hint Resolve zero_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:404.1-409.16 *)
Inductive vcvtop : Type :=
	| V_EXTEND (v_half : half) (v_sx : sx) : vcvtop
	| V_TRUNC_SAT (v_sx : sx) (_ : (option zero)) : vcvtop
	| V_CONVERT (_ : (option half)) (v_sx : sx) : vcvtop
	| V_DEMOTE (v_zero : zero) : vcvtop
	| V_PROMOTELOW : vcvtop.

Global Instance Inhabited__vcvtop : Inhabited (vcvtop) := { default_val := V_EXTEND default_val default_val }.

Definition vcvtop_eq_dec : forall (v1 v2 : vcvtop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vcvtop_eqb (v1 v2 : vcvtop) : bool :=
	is_left(vcvtop_eq_dec v1 v2).
Definition eqvcvtopP : Equality.axiom (vcvtop_eqb) :=
	eq_dec_Equality_axiom (vcvtop) (vcvtop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vcvtop) (eqvcvtopP).
Hint Resolve vcvtop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:411.1-411.25 *)
Inductive vshiftop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Type :=
	| VSHIFT_SHL : vshiftop_Jnn_N v_Jnn v_N
	| VSHIFT_SHR (v_sx : sx) : vshiftop_Jnn_N v_Jnn v_N.

Global Instance Inhabited__vshiftop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Inhabited (vshiftop_Jnn_N v_Jnn v_N) := { default_val := VSHIFT_SHL v_Jnn v_N }.

Definition vshiftop_Jnn_N_eq_dec : forall (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vshiftop_Jnn_N v_Jnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vshiftop_Jnn_N_eqb (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vshiftop_Jnn_N v_Jnn v_N) : bool :=
	is_left(vshiftop_Jnn_N_eq_dec v_Jnn v_N v1 v2).
Definition eqvshiftop_Jnn_NP (v_Jnn : Jnn) (v_N : res_N) : Equality.axiom (vshiftop_Jnn_N_eqb v_Jnn v_N) :=
	eq_dec_Equality_axiom (vshiftop_Jnn_N v_Jnn v_N) (vshiftop_Jnn_N_eq_dec v_Jnn v_N).

HB.instance Definition _ (v_Jnn : Jnn) (v_N : res_N) := hasDecEq.Build (vshiftop_Jnn_N v_Jnn v_N) (eqvshiftop_Jnn_NP v_Jnn v_N).
Hint Resolve vshiftop_Jnn_N_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:411.1-411.25 *)
Definition vshiftop_ (v_ishape : ishape): Type :=
	match v_ishape with
		| (IX v_Jnn (mk_dim v_N)) => (vshiftop_Jnn_N v_Jnn v_N)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:414.1-414.25 *)
Inductive vextunop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Type :=
	| EXTADD_PAIRWISE (v_sx : sx) : vextunop_Jnn_N v_Jnn v_N.

Global Instance Inhabited__vextunop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Inhabited (vextunop_Jnn_N v_Jnn v_N) := { default_val := EXTADD_PAIRWISE v_Jnn v_N default_val }.

Definition vextunop_Jnn_N_eq_dec : forall (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vextunop_Jnn_N v_Jnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vextunop_Jnn_N_eqb (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vextunop_Jnn_N v_Jnn v_N) : bool :=
	is_left(vextunop_Jnn_N_eq_dec v_Jnn v_N v1 v2).
Definition eqvextunop_Jnn_NP (v_Jnn : Jnn) (v_N : res_N) : Equality.axiom (vextunop_Jnn_N_eqb v_Jnn v_N) :=
	eq_dec_Equality_axiom (vextunop_Jnn_N v_Jnn v_N) (vextunop_Jnn_N_eq_dec v_Jnn v_N).

HB.instance Definition _ (v_Jnn : Jnn) (v_N : res_N) := hasDecEq.Build (vextunop_Jnn_N v_Jnn v_N) (eqvextunop_Jnn_NP v_Jnn v_N).
Hint Resolve vextunop_Jnn_N_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:414.1-414.25 *)
Definition wf_vextunop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) (v_x : (vextunop_Jnn_N v_Jnn v_N)) : Prop :=
	match v_Jnn, v_N, v_x return Prop with
		| v_Jnn, v_N, (EXTADD_PAIRWISE v_sx) => ((16 <= (fun_lsizenn (v_Jnn : lanetype))) /\ ((fun_lsizenn (v_Jnn : lanetype)) <= 32))
	end.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:414.1-414.25 *)
Definition vextunop_ (v_ishape : ishape): Type :=
	match v_ishape with
		| (IX v_Jnn (mk_dim v_N)) => (vextunop_Jnn_N v_Jnn v_N)
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:417.1-417.26 *)
Inductive vextbinop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Type :=
	| EXTMUL (v_half : half) (v_sx : sx) : vextbinop_Jnn_N v_Jnn v_N
	| DOTres_S : vextbinop_Jnn_N v_Jnn v_N.

Global Instance Inhabited__vextbinop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) : Inhabited (vextbinop_Jnn_N v_Jnn v_N) := { default_val := EXTMUL v_Jnn v_N default_val default_val }.

Definition vextbinop_Jnn_N_eq_dec : forall (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vextbinop_Jnn_N v_Jnn v_N),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vextbinop_Jnn_N_eqb (v_Jnn : Jnn) (v_N : res_N) (v1 v2 : vextbinop_Jnn_N v_Jnn v_N) : bool :=
	is_left(vextbinop_Jnn_N_eq_dec v_Jnn v_N v1 v2).
Definition eqvextbinop_Jnn_NP (v_Jnn : Jnn) (v_N : res_N) : Equality.axiom (vextbinop_Jnn_N_eqb v_Jnn v_N) :=
	eq_dec_Equality_axiom (vextbinop_Jnn_N v_Jnn v_N) (vextbinop_Jnn_N_eq_dec v_Jnn v_N).

HB.instance Definition _ (v_Jnn : Jnn) (v_N : res_N) := hasDecEq.Build (vextbinop_Jnn_N v_Jnn v_N) (eqvextbinop_Jnn_NP v_Jnn v_N).
Hint Resolve vextbinop_Jnn_N_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:417.1-417.26 *)
Definition wf_vextbinop_Jnn_N (v_Jnn : Jnn) (v_N : res_N) (v_x : (vextbinop_Jnn_N v_Jnn v_N)) : Prop :=
	match v_Jnn, v_N, v_x return Prop with
		| v_Jnn, v_N, (DOTres_S) => ((fun_lsizenn (v_Jnn : lanetype)) = 32)
		| _, _, _ => true
	end.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:417.1-417.26 *)
Definition vextbinop_ (v_ishape : ishape): Type :=
	match v_ishape with
		| (IX v_Jnn (mk_dim v_N)) => (vextbinop_Jnn_N v_Jnn v_N)
	end.

(* Record Creation Definition at: ../specification/wasm-2.0/1-syntax.spectec:425.1-425.69 *)
Record memarg := MKmemarg
{	ALIGN : u32
;	OFFSET : u32
}.

Global Instance Inhabited_memarg : Inhabited memarg := 
{default_val := {|
	ALIGN := default_val;
	OFFSET := default_val|} }.

Definition _append_memarg (arg1 arg2 : memarg) :=
{|
	ALIGN := arg1.(ALIGN); (* FIXME - Non-trivial append *)
	OFFSET := arg1.(OFFSET); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_memarg : Append memarg := { _append arg1 arg2 := _append_memarg arg1 arg2 }.

#[export] Instance eta__memarg : Settable _ := settable! MKmemarg <ALIGN;OFFSET>.

Definition memarg_eq_dec : forall (v1 v2 : memarg),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memarg_eqb (v1 v2 : memarg) : bool :=
	is_left(memarg_eq_dec v1 v2).
Definition eqmemargP : Equality.axiom (memarg_eqb) :=
	eq_dec_Equality_axiom (memarg) (memarg_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memarg) (eqmemargP).
Hint Resolve memarg_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:429.1-429.38 *)
Inductive loadop_Inn (v_Inn : Inn) : Type :=
	| op_ (v_sz : sz) (v_sx : sx) : loadop_Inn v_Inn.

Global Instance Inhabited__loadop_Inn (v_Inn : Inn) : Inhabited (loadop_Inn v_Inn) := { default_val := op_ v_Inn default_val default_val }.

Definition loadop_Inn_eq_dec : forall (v_Inn : Inn) (v1 v2 : loadop_Inn v_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition loadop_Inn_eqb (v_Inn : Inn) (v1 v2 : loadop_Inn v_Inn) : bool :=
	is_left(loadop_Inn_eq_dec v_Inn v1 v2).
Definition eqloadop_InnP (v_Inn : Inn) : Equality.axiom (loadop_Inn_eqb v_Inn) :=
	eq_dec_Equality_axiom (loadop_Inn v_Inn) (loadop_Inn_eq_dec v_Inn).

HB.instance Definition _ (v_Inn : Inn) := hasDecEq.Build (loadop_Inn v_Inn) (eqloadop_InnP v_Inn).
Hint Resolve loadop_Inn_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:429.1-429.38 *)
Definition wf_loadop_Inn (v_Inn : Inn) (v_x : (loadop_Inn v_Inn)) : Prop :=
	match v_Inn, v_x return Prop with
		| v_Inn, (op_ v_sz v_sx) => ((fun_proj_sz_0 v_sz) < (fun_sizenn (v_Inn : numtype)))
	end.

(* Family Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:429.1-429.38 *)
Definition loadop_ (v_numtype : numtype): Type :=
	match v_numtype with
		| (I32) => (loadop_Inn INN_I32)
		| (I64) => (loadop_Inn INN_I64)
		| _ => default_val
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:432.1-435.46 *)
Inductive vloadop : Type :=
	| VLOAD_SHAPEX_ (v_nat : nat) (v__ : nat) (v_sx : sx) : vloadop
	| VLOAD_SPLAT (v_nat : nat) : vloadop
	| VLOAD_ZERO (v_nat : nat) : vloadop.

Global Instance Inhabited__vloadop : Inhabited (vloadop) := { default_val := VLOAD_SHAPEX_ default_val default_val default_val }.

Definition vloadop_eq_dec : forall (v1 v2 : vloadop),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition vloadop_eqb (v1 v2 : vloadop) : bool :=
	is_left(vloadop_eq_dec v1 v2).
Definition eqvloadopP : Equality.axiom (vloadop_eqb) :=
	eq_dec_Equality_axiom (vloadop) (vloadop_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vloadop) (eqvloadopP).
Hint Resolve vloadop_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:442.1-444.17 *)
Inductive blocktype : Type :=
	| _RESULT (_ : (option valtype)) : blocktype
	| _IDX (v_funcidx : funcidx) : blocktype.

Global Instance Inhabited__blocktype : Inhabited (blocktype) := { default_val := _RESULT default_val }.

Definition blocktype_eq_dec : forall (v1 v2 : blocktype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition blocktype_eqb (v1 v2 : blocktype) : bool :=
	is_left(blocktype_eq_dec v1 v2).
Definition eqblocktypeP : Equality.axiom (blocktype_eqb) :=
	eq_dec_Equality_axiom (blocktype) (blocktype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (blocktype) (eqblocktypeP).
Hint Resolve blocktype_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.22 *)
Definition fun_coec_numtype__lanetype (v_numtype : numtype) : lanetype :=
	match v_numtype return lanetype with
		| (I32) => LANETYPE_I32
		| (I64) => LANETYPE_I64
		| (F32) => LANETYPE_F32
		| (F64) => LANETYPE_F64
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.22 *)
Coercion fun_coec_numtype__lanetype : numtype >-> lanetype.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.22 *)
Definition fun_coec_ishape__shape (v_ishape : ishape) : shape :=
	match v_ishape return shape with
		| (IX v_0 v_1) => (X v_0 v_1)
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.22 *)
Coercion fun_coec_ishape__shape : ishape >-> shape.

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.22 *)
(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.22 *)
Inductive instr : Type :=
	| instr_NOP : instr
	| instr_UNREACHABLE : instr
	| instr_DROP : instr
	| instr_SELECT (_ : (option (list valtype))) : instr
	| instr_BLOCK (v_blocktype : blocktype) (_ : (list instr)) : instr
	| instr_LOOP (v_blocktype : blocktype) (_ : (list instr)) : instr
	| instr_IFELSE (v_blocktype : blocktype) (_ : (list instr)) (v__ : (list instr)) : instr
	| instr_BR (v_labelidx : labelidx) : instr
	| instr_BR_IF (v_labelidx : labelidx) : instr
	| instr_BR_TABLE (_ : (list labelidx)) (v__ : labelidx) : instr
	| instr_CALL (v_funcidx : funcidx) : instr
	| instr_CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : instr
	| instr_RETURN : instr
	| instr_CONST (v_numtype : numtype) (v_num_ : (num_ v_numtype)) : instr
	| instr_UNOP (v_numtype : numtype) (v_unop_ : (unop_ v_numtype)) : instr
	| instr_BINOP (v_numtype : numtype) (v_binop_ : (binop_ v_numtype)) : instr
	| instr_TESTOP (v_numtype : numtype) (v_testop_ : (testop_ v_numtype)) : instr
	| instr_RELOP (v_numtype : numtype) (v_relop_ : (relop_ v_numtype)) : instr
	| instr_CVTOP (v_numtype_1 : numtype) (v_numtype_2 : numtype) (v_cvtop : cvtop) : instr
	| instr_EXTEND (v_numtype : numtype) (v_n : n) : instr
	| instr_VCONST (v_vectype : vectype) (v_vec_ : (vec_ v_vectype)) : instr
	| instr_VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : instr
	| instr_VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : instr
	| instr_VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : instr
	| instr_VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : instr
	| instr_VUNOP (v_shape : shape) (v_vunop_ : (vunop_ v_shape)) : instr
	| instr_VBINOP (v_shape : shape) (v_vbinop_ : (vbinop_ v_shape)) : instr
	| instr_VTESTOP (v_shape : shape) (v_vtestop_ : (vtestop_ v_shape)) : instr
	| instr_VRELOP (v_shape : shape) (v_vrelop_ : (vrelop_ v_shape)) : instr
	| instr_VSHIFTOP (v_ishape : ishape) (v_vshiftop_ : (vshiftop_ v_ishape)) : instr
	| instr_VBITMASK (v_ishape : ishape) : instr
	| instr_VSWIZZLE (v_ishape : ishape) : instr
	| instr_VSHUFFLE (v_ishape : ishape) (_ : (list laneidx)) : instr
	| instr_VSPLAT (v_shape : shape) : instr
	| instr_VEXTRACT_LANE (v_shape : shape) (_ : (option sx)) (v_laneidx : laneidx) : instr
	| instr_VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : instr
	| instr_VEXTUNOP (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_vextunop_ : (vextunop_ v_ishape_1)) : instr
	| instr_VEXTBINOP (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_vextbinop_ : (vextbinop_ v_ishape_1)) : instr
	| instr_VNARROW (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_sx : sx) : instr
	| instr_VCVTOP (v_shape : shape) (v__ : shape) (v_vcvtop : vcvtop) : instr
	| instr_REF_NULL (v_reftype : reftype) : instr
	| instr_REF_FUNC (v_funcidx : funcidx) : instr
	| instr_REF_IS_NULL : instr
	| instr_LOCAL_GET (v_localidx : localidx) : instr
	| instr_LOCAL_SET (v_localidx : localidx) : instr
	| instr_LOCAL_TEE (v_localidx : localidx) : instr
	| instr_GLOBAL_GET (v_globalidx : globalidx) : instr
	| instr_GLOBAL_SET (v_globalidx : globalidx) : instr
	| instr_TABLE_GET (v_tableidx : tableidx) : instr
	| instr_TABLE_SET (v_tableidx : tableidx) : instr
	| instr_TABLE_SIZE (v_tableidx : tableidx) : instr
	| instr_TABLE_GROW (v_tableidx : tableidx) : instr
	| instr_TABLE_FILL (v_tableidx : tableidx) : instr
	| instr_TABLE_COPY (v_tableidx : tableidx) (v__ : tableidx) : instr
	| instr_TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : instr
	| instr_ELEM_DROP (v_elemidx : elemidx) : instr
	| instr_LOAD (v_numtype : numtype) (_ : (option (loadop_ v_numtype))) (v_memarg : memarg) : instr
	| instr_STORE (v_numtype : numtype) (_ : (option sz)) (v_memarg : memarg) : instr
	| instr_VLOAD (v_vectype : vectype) (_ : (option vloadop)) (v_memarg : memarg) : instr
	| instr_VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
	| instr_VSTORE (v_vectype : vectype) (v_memarg : memarg) : instr
	| instr_VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
	| instr_MEMORY_SIZE : instr
	| instr_MEMORY_GROW : instr
	| instr_MEMORY_FILL : instr
	| instr_MEMORY_COPY : instr
	| instr_MEMORY_INIT (v_dataidx : dataidx) : instr
	| instr_DATA_DROP (v_dataidx : dataidx) : instr.

Global Instance Inhabited__instr : Inhabited (instr) := { default_val := instr_NOP }.

(* FIXME - No clear way to do decidable equality *)
Fixpoint instr_eq_dec (v1 v2 : instr) {struct v1} :
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition instr_eqb (v1 v2 : instr) : bool :=
	is_left(instr_eq_dec v1 v2).
Definition eqinstrP : Equality.axiom (instr_eqb) :=
	eq_dec_Equality_axiom (instr) (instr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (instr) (eqinstrP).
Hint Resolve instr_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.22 *)
Fixpoint wf_instr (v_x : instr) : Prop :=
	match v_x return Prop with
		| (instr_CVTOP v_numtype_1 v_numtype_2 v_cvtop) => (v_numtype_1 <> v_numtype_2)
		| (instr_VSWIZZLE v_ishape) => (v_ishape = (IX JNN_I8 (mk_dim 16)))
		| (instr_VSHUFFLE v_ishape v_laneidx) => ((v_ishape = (IX JNN_I8 (mk_dim 16))) /\ ((List.length v_laneidx) = 16))
		| (instr_VEXTRACT_LANE v_shape v_sx v_laneidx) => forall (v_numtype : numtype), (((fun_lanetype v_shape) = (v_numtype : lanetype)) <-> (v_sx = None))
		| (instr_VEXTUNOP v_ishape_1 v_ishape_2 v_vextunop_) => ((fun_lsize (fun_lanetype (v_ishape_1 : shape))) = (2 * (fun_lsize (fun_lanetype (v_ishape_2 : shape)))))
		| (instr_VEXTBINOP v_ishape_1 v_ishape_2 v_vextbinop_) => ((fun_lsize (fun_lanetype (v_ishape_1 : shape))) = (2 * (fun_lsize (fun_lanetype (v_ishape_2 : shape)))))
		| (instr_VNARROW v_ishape_1 v_ishape_2 v_sx) => (((fun_lsize (fun_lanetype (v_ishape_2 : shape))) = (2 * (fun_lsize (fun_lanetype (v_ishape_1 : shape))))) /\ ((2 * (fun_lsize (fun_lanetype (v_ishape_1 : shape)))) <= 32))
		| (instr_STORE v_numtype v_sz v_memarg) => forall (v_Inn : (option Inn)), List.Forall2 (fun (v_Inn : Inn) (v_sz : sz) => ((v_numtype = (v_Inn : numtype)) /\ ((fun_proj_sz_0 v_sz) < (fun_sizenn (v_Inn : numtype))))) (option_to_list v_Inn) (option_to_list v_sz)
		| _ => true
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:567.1-568.9 *)
Definition expr := (list instr).

Definition expr_eq_dec : forall (v1 v2 : expr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition expr_eqb (v1 v2 : expr) : bool :=
	is_left(expr_eq_dec v1 v2).
Definition eqexprP : Equality.axiom (expr_eqb) :=
	eq_dec_Equality_axiom (expr) (expr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (expr) (eqexprP).
Hint Resolve expr_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:580.1-580.59 *)
Inductive elemmode : Type :=
	| ACTIVE (v_tableidx : tableidx) (v_expr : expr) : elemmode
	| PASSIVE : elemmode
	| DECLARE : elemmode.

Global Instance Inhabited__elemmode : Inhabited (elemmode) := { default_val := ACTIVE default_val default_val }.

Definition elemmode_eq_dec : forall (v1 v2 : elemmode),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elemmode_eqb (v1 v2 : elemmode) : bool :=
	is_left(elemmode_eq_dec v1 v2).
Definition eqelemmodeP : Equality.axiom (elemmode_eqb) :=
	eq_dec_Equality_axiom (elemmode) (elemmode_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elemmode) (eqelemmodeP).
Hint Resolve elemmode_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:581.1-581.69 *)
Inductive datamode : Type :=
	| DATAM_ACTIVE (v_memidx : memidx) (v_expr : expr) : datamode
	| DATAM_PASSIVE : datamode.

Global Instance Inhabited__datamode : Inhabited (datamode) := { default_val := DATAM_ACTIVE default_val default_val }.

Definition datamode_eq_dec : forall (v1 v2 : datamode),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition datamode_eqb (v1 v2 : datamode) : bool :=
	is_left(datamode_eq_dec v1 v2).
Definition eqdatamodeP : Equality.axiom (datamode_eqb) :=
	eq_dec_Equality_axiom (datamode) (datamode_eq_dec).

HB.instance Definition _ := hasDecEq.Build (datamode) (eqdatamodeP).
Hint Resolve datamode_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:583.1-584.16 *)
Inductive type : Type :=
	| TYPE (v_functype : functype) : type.

Global Instance Inhabited__type : Inhabited (type) := { default_val := TYPE default_val }.

Definition type_eq_dec : forall (v1 v2 : type),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition type_eqb (v1 v2 : type) : bool :=
	is_left(type_eq_dec v1 v2).
Definition eqtypeP : Equality.axiom (type_eqb) :=
	eq_dec_Equality_axiom (type) (type_eq_dec).

HB.instance Definition _ := hasDecEq.Build (type) (eqtypeP).
Hint Resolve type_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:585.1-586.16 *)
Inductive local : Type :=
	| LOCAL (v_valtype : valtype) : local.

Global Instance Inhabited__local : Inhabited (local) := { default_val := LOCAL default_val }.

Definition local_eq_dec : forall (v1 v2 : local),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition local_eqb (v1 v2 : local) : bool :=
	is_left(local_eq_dec v1 v2).
Definition eqlocalP : Equality.axiom (local_eqb) :=
	eq_dec_Equality_axiom (local) (local_eq_dec).

HB.instance Definition _ := hasDecEq.Build (local) (eqlocalP).
Hint Resolve local_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:587.1-588.27 *)
Inductive func : Type :=
	| FUNC (v_typeidx : typeidx) (_ : (list local)) (v_expr : expr) : func.

Global Instance Inhabited__func : Inhabited (func) := { default_val := FUNC default_val default_val default_val }.

Definition func_eq_dec : forall (v1 v2 : func),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition func_eqb (v1 v2 : func) : bool :=
	is_left(func_eq_dec v1 v2).
Definition eqfuncP : Equality.axiom (func_eqb) :=
	eq_dec_Equality_axiom (func) (func_eq_dec).

HB.instance Definition _ := hasDecEq.Build (func) (eqfuncP).
Hint Resolve func_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:589.1-590.25 *)
Inductive global : Type :=
	| GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global.

Global Instance Inhabited__global : Inhabited (global) := { default_val := GLOBAL default_val default_val }.

Definition global_eq_dec : forall (v1 v2 : global),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition global_eqb (v1 v2 : global) : bool :=
	is_left(global_eq_dec v1 v2).
Definition eqglobalP : Equality.axiom (global_eqb) :=
	eq_dec_Equality_axiom (global) (global_eq_dec).

HB.instance Definition _ := hasDecEq.Build (global) (eqglobalP).
Hint Resolve global_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:591.1-592.18 *)
Inductive table : Type :=
	| TABLE (v_tabletype : tabletype) : table.

Global Instance Inhabited__table : Inhabited (table) := { default_val := TABLE default_val }.

Definition table_eq_dec : forall (v1 v2 : table),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition table_eqb (v1 v2 : table) : bool :=
	is_left(table_eq_dec v1 v2).
Definition eqtableP : Equality.axiom (table_eqb) :=
	eq_dec_Equality_axiom (table) (table_eq_dec).

HB.instance Definition _ := hasDecEq.Build (table) (eqtableP).
Hint Resolve table_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:593.1-594.17 *)
Inductive mem : Type :=
	| MEMORY (v_memtype : memtype) : mem.

Global Instance Inhabited__mem : Inhabited (mem) := { default_val := MEMORY default_val }.

Definition mem_eq_dec : forall (v1 v2 : mem),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition mem_eqb (v1 v2 : mem) : bool :=
	is_left(mem_eq_dec v1 v2).
Definition eqmemP : Equality.axiom (mem_eqb) :=
	eq_dec_Equality_axiom (mem) (mem_eq_dec).

HB.instance Definition _ := hasDecEq.Build (mem) (eqmemP).
Hint Resolve mem_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:595.1-596.30 *)
Inductive elem : Type :=
	| ELEM (v_reftype : reftype) (_ : (list expr)) (v_elemmode : elemmode) : elem.

Global Instance Inhabited__elem : Inhabited (elem) := { default_val := ELEM default_val default_val default_val }.

Definition elem_eq_dec : forall (v1 v2 : elem),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elem_eqb (v1 v2 : elem) : bool :=
	is_left(elem_eq_dec v1 v2).
Definition eqelemP : Equality.axiom (elem_eqb) :=
	eq_dec_Equality_axiom (elem) (elem_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elem) (eqelemP).
Hint Resolve elem_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:597.1-598.22 *)
Inductive data : Type :=
	| DATA (_ : (list byte)) (v_datamode : datamode) : data.

Global Instance Inhabited__data : Inhabited (data) := { default_val := DATA default_val default_val }.

Definition data_eq_dec : forall (v1 v2 : data),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition data_eqb (v1 v2 : data) : bool :=
	is_left(data_eq_dec v1 v2).
Definition eqdataP : Equality.axiom (data_eqb) :=
	eq_dec_Equality_axiom (data) (data_eq_dec).

HB.instance Definition _ := hasDecEq.Build (data) (eqdataP).
Hint Resolve data_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:599.1-600.16 *)
Inductive start : Type :=
	| START (v_funcidx : funcidx) : start.

Global Instance Inhabited__start : Inhabited (start) := { default_val := START default_val }.

Definition start_eq_dec : forall (v1 v2 : start),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition start_eqb (v1 v2 : start) : bool :=
	is_left(start_eq_dec v1 v2).
Definition eqstartP : Equality.axiom (start_eqb) :=
	eq_dec_Equality_axiom (start) (start_eq_dec).

HB.instance Definition _ := hasDecEq.Build (start) (eqstartP).
Hint Resolve start_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:602.1-603.66 *)
Inductive externidx : Type :=
	| EXTIDX_FUNC (v_funcidx : funcidx) : externidx
	| EXTIDX_GLOBAL (v_globalidx : globalidx) : externidx
	| EXTIDX_TABLE (v_tableidx : tableidx) : externidx
	| EXTIDX_MEM (v_memidx : memidx) : externidx.

Global Instance Inhabited__externidx : Inhabited (externidx) := { default_val := EXTIDX_FUNC default_val }.

Definition externidx_eq_dec : forall (v1 v2 : externidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition externidx_eqb (v1 v2 : externidx) : bool :=
	is_left(externidx_eq_dec v1 v2).
Definition eqexternidxP : Equality.axiom (externidx_eqb) :=
	eq_dec_Equality_axiom (externidx) (externidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (externidx) (eqexternidxP).
Hint Resolve externidx_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:604.1-605.24 *)
Inductive export : Type :=
	| EXPORT (v_name : name) (v_externidx : externidx) : export.

Global Instance Inhabited__export : Inhabited (export) := { default_val := EXPORT default_val default_val }.

Definition export_eq_dec : forall (v1 v2 : export),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition export_eqb (v1 v2 : export) : bool :=
	is_left(export_eq_dec v1 v2).
Definition eqexportP : Equality.axiom (export_eqb) :=
	eq_dec_Equality_axiom (export) (export_eq_dec).

HB.instance Definition _ := hasDecEq.Build (export) (eqexportP).
Hint Resolve export_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:606.1-607.30 *)
Inductive import : Type :=
	| IMPORT (v_name : name) (v__ : name) (v_externtype : externtype) : import.

Global Instance Inhabited__import : Inhabited (import) := { default_val := IMPORT default_val default_val default_val }.

Definition import_eq_dec : forall (v1 v2 : import),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition import_eqb (v1 v2 : import) : bool :=
	is_left(import_eq_dec v1 v2).
Definition eqimportP : Equality.axiom (import_eqb) :=
	eq_dec_Equality_axiom (import) (import_eq_dec).

HB.instance Definition _ := hasDecEq.Build (import) (eqimportP).
Hint Resolve import_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:609.1-610.76 *)
Inductive module : Type :=
	| MODULE (_ : (list type)) (_ : (list import)) (_ : (list func)) (_ : (list global)) (_ : (list table)) (_ : (list mem)) (_ : (list elem)) (_ : (list data)) (_ : (option start)) (_ : (list export)) : module.

Global Instance Inhabited__module : Inhabited (module) := { default_val := MODULE default_val default_val default_val default_val default_val default_val default_val default_val default_val default_val }.

Definition module_eq_dec : forall (v1 v2 : module),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition module_eqb (v1 v2 : module) : bool :=
	is_left(module_eq_dec v1 v2).
Definition eqmoduleP : Equality.axiom (module_eqb) :=
	eq_dec_Equality_axiom (module) (module_eq_dec).

HB.instance Definition _ := hasDecEq.Build (module) (eqmoduleP).
Hint Resolve module_eq_dec : eq_dec_db.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
Fixpoint fun_concat_bytes (var_0 : (list (list byte))) : (list byte) :=
	match var_0 return (list byte) with
		| [] => []
		| (v_b :: v_b') => (v_b ++ (fun_concat_bytes v_b'))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32 *)
Definition fun_unpack (v_lanetype : lanetype) : numtype :=
	match v_lanetype return numtype with
		| (LANETYPE_I32) => I32
		| (LANETYPE_I64) => I64
		| (LANETYPE_F32) => F32
		| (LANETYPE_F64) => F64
		| (LANETYPE_I8) => I32
		| (LANETYPE_I16) => I32
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54 *)
Definition fun_shunpack (v_shape : shape) : numtype :=
	match v_shape return numtype with
		| (X v_Lnn (mk_dim v_N)) => (fun_unpack v_Lnn)
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64 *)
(* Axiom Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64 *)
Axiom fun_funcsxt : forall (var_0 : (list externtype)), (list functype).

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66 *)
(* Axiom Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66 *)
Axiom fun_globalsxt : forall (var_0 : (list externtype)), (list globaltype).

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
(* Axiom Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
Axiom fun_tablesxt : forall (var_0 : (list externtype)), (list tabletype).

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
(* Axiom Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
Axiom fun_memsxt : forall (var_0 : (list externtype)), (list memtype).

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 *)
Definition fun_dataidx_instr (v_instr : instr) : (list dataidx) :=
	match v_instr return (list dataidx) with
		| (instr_MEMORY_INIT v_x) => [v_x]
		| (instr_DATA_DROP v_x) => [v_x]
		| v_in => []
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
Fixpoint fun_dataidx_instrs (var_0 : (list instr)) : (list dataidx) :=
	match var_0 return (list dataidx) with
		| [] => []
		| (v_instr :: v_instr') => ((fun_dataidx_instr v_instr) ++ (fun_dataidx_instrs v_instr'))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.1-89.59 *)
Definition fun_dataidx_expr (v_expr : expr) : (list dataidx) :=
	match v_expr return (list dataidx) with
		| v_in => (fun_dataidx_instrs v_in)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.1-92.59 *)
Definition fun_dataidx_func (v_func : func) : (list dataidx) :=
	match v_func return (list dataidx) with
		| (FUNC v_x v_loc v_e) => (fun_dataidx_expr v_e)
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
Fixpoint fun_dataidx_funcs (var_0 : (list func)) : (list dataidx) :=
	match var_0 return (list dataidx) with
		| [] => []
		| (v_func :: v_func') => ((fun_dataidx_func v_func) ++ (fun_dataidx_funcs v_func'))
	end.

(* Global Declaration Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 *)
Definition fun_memarg0 : memarg := {| ALIGN := (mk_uN _ 0); OFFSET := (mk_uN _ 0) |}.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 *)
Axiom fun_s33_to_u32 : forall (v_s33 : s33), u32.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 *)
Definition fun_bool (v_bool : bool) : nat :=
	match v_bool return nat with
		| false => 0
		| true => 1
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 *)
Axiom fun_truncz : forall (v_rat : nat), nat.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.1-20.54 *)
Axiom fun_signed_ : forall (v_N : res_N) (v_nat : nat), nat.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.1-24.70 *)
Axiom fun_inv_signed_ : forall (v_N : res_N) (v_int : nat), nat.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 *)
Axiom fun_sat_u_ : forall (v_N : res_N) (v_int : nat), nat.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 *)
Axiom fun_sat_s_ : forall (v_N : res_N) (v_int : nat), nat.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 *)
Axiom fun_extend__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : (iN v_M)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 *)
Axiom fun_fabs_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 *)
Axiom fun_fceil_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 *)
Axiom fun_ffloor_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 *)
Axiom fun_fnearest_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 *)
Axiom fun_fneg_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 *)
Axiom fun_fsqrt_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 *)
Axiom fun_ftrunc_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 *)
Axiom fun_iclz_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 *)
Axiom fun_ictz_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 *)
Axiom fun_ipopcnt_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 *)
Axiom fun_wrap__ : forall (v_M : M) (v_N : res_N) (v_iN : (iN v_M)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
Definition fun_unop_ (v_numtype : numtype) (v_unop_ : (unop_ v_numtype)) (v_num_ : (num_ v_numtype)) : (list (num_ v_numtype)) :=
	match v_numtype, v_unop_, v_num_ return (list (num_ v_numtype)) with
		| (I32), (INT_CLZ), v_iN => [(fun_iclz_ (fun_sizenn (INN_I32 : numtype)) v_iN)]
		| (I64), (INT_CLZ), v_iN => [(fun_iclz_ (fun_sizenn (INN_I64 : numtype)) v_iN)]
		| (I32), (INT_CTZ), v_iN => [(fun_ictz_ (fun_sizenn (INN_I32 : numtype)) v_iN)]
		| (I64), (INT_CTZ), v_iN => [(fun_ictz_ (fun_sizenn (INN_I64 : numtype)) v_iN)]
		| (I32), (INT_POPCNT), v_iN => [(fun_ipopcnt_ (fun_sizenn (INN_I32 : numtype)) v_iN)]
		| (I64), (INT_POPCNT), v_iN => [(fun_ipopcnt_ (fun_sizenn (INN_I64 : numtype)) v_iN)]
		| (I32), (INT_EXTEND v_M), v_iN => [(fun_extend__ v_M (fun_sizenn (INN_I32 : numtype)) res_S (fun_wrap__ (fun_sizenn (INN_I32 : numtype)) v_M v_iN))]
		| (I64), (INT_EXTEND v_M), v_iN => [(fun_extend__ v_M (fun_sizenn (INN_I64 : numtype)) res_S (fun_wrap__ (fun_sizenn (INN_I64 : numtype)) v_M v_iN))]
		| (F32), (FLOAT_ABS), v_fN => (fun_fabs_ (fun_sizenn (FNN_F32 : numtype)) v_fN)
		| (F64), (FLOAT_ABS), v_fN => (fun_fabs_ (fun_sizenn (FNN_F64 : numtype)) v_fN)
		| (F32), (FLOAT_NEG), v_fN => (fun_fneg_ (fun_sizenn (FNN_F32 : numtype)) v_fN)
		| (F64), (FLOAT_NEG), v_fN => (fun_fneg_ (fun_sizenn (FNN_F64 : numtype)) v_fN)
		| (F32), (FLOAT_SQRT), v_fN => (fun_fsqrt_ (fun_sizenn (FNN_F32 : numtype)) v_fN)
		| (F64), (FLOAT_SQRT), v_fN => (fun_fsqrt_ (fun_sizenn (FNN_F64 : numtype)) v_fN)
		| (F32), (FLOAT_CEIL), v_fN => (fun_fceil_ (fun_sizenn (FNN_F32 : numtype)) v_fN)
		| (F64), (FLOAT_CEIL), v_fN => (fun_fceil_ (fun_sizenn (FNN_F64 : numtype)) v_fN)
		| (F32), (FLOAT_FLOOR), v_fN => (fun_ffloor_ (fun_sizenn (FNN_F32 : numtype)) v_fN)
		| (F64), (FLOAT_FLOOR), v_fN => (fun_ffloor_ (fun_sizenn (FNN_F64 : numtype)) v_fN)
		| (F32), (FLOAT_TRUNC), v_fN => (fun_ftrunc_ (fun_sizenn (FNN_F32 : numtype)) v_fN)
		| (F64), (FLOAT_TRUNC), v_fN => (fun_ftrunc_ (fun_sizenn (FNN_F64 : numtype)) v_fN)
		| (F32), (FLOAT_NEAREST), v_fN => (fun_fnearest_ (fun_sizenn (FNN_F32 : numtype)) v_fN)
		| (F64), (FLOAT_NEAREST), v_fN => (fun_fnearest_ (fun_sizenn (FNN_F64 : numtype)) v_fN)
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 *)
Axiom fun_fadd_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 *)
Axiom fun_fcopysign_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 *)
Axiom fun_fdiv_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 *)
Axiom fun_fmax_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 *)
Axiom fun_fmin_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 *)
Axiom fun_fmul_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 *)
Axiom fun_fsub_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 *)
Definition fun_iadd_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_iN, v_iN_0 return (iN v_N) with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (((fun_proj_uN_0 v_N v_i_1) + (fun_proj_uN_0 v_N v_i_2)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 *)
Axiom fun_iand_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.1-108.74 *)
Axiom fun_idiv_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (option (iN v_N)).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 *)
Definition fun_imul_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_iN, v_iN_0 return (iN v_N) with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (((fun_proj_uN_0 v_N v_i_1) * (fun_proj_uN_0 v_N v_i_2)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 *)
Axiom fun_ior_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.1-109.74 *)
Axiom fun_irem_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (option (iN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 *)
Axiom fun_irotl_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 *)
Axiom fun_irotr_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 *)
Axiom fun_ishl_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_u32 : u32), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 *)
Axiom fun_ishr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_u32 : u32), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 *)
Definition fun_isub_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_iN, v_iN_0 return (iN v_N) with
		| v_N, v_i_1, v_i_2 => (mk_uN _ ((((((2 ^ v_N) + (fun_proj_uN_0 v_N v_i_1)) : nat) - ((fun_proj_uN_0 v_N v_i_2) : nat)) mod ((2 ^ v_N) : nat)) : nat))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 *)
Axiom fun_ixor_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.1-47.34 *)
Definition fun_binop_ (v_numtype : numtype) (v_binop_ : (binop_ v_numtype)) (v_num_ : (num_ v_numtype)) (v_num__0 : (num_ v_numtype)) : (list (num_ v_numtype)) :=
	match v_numtype, v_binop_, v_num_, v_num__0 return (list (num_ v_numtype)) with
		| (I32), (INT_ADD), v_iN_1, v_iN_2 => [(fun_iadd_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_ADD), v_iN_1, v_iN_2 => [(fun_iadd_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (I32), (INT_SUB), v_iN_1, v_iN_2 => [(fun_isub_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_SUB), v_iN_1, v_iN_2 => [(fun_isub_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (I32), (INT_MUL), v_iN_1, v_iN_2 => [(fun_imul_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_MUL), v_iN_1, v_iN_2 => [(fun_imul_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (I32), (INT_DIV v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 32) (fun_idiv_ (fun_sizenn (INN_I32 : numtype)) v_sx v_iN_1 v_iN_2))
		| (I64), (INT_DIV v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 64) (fun_idiv_ (fun_sizenn (INN_I64 : numtype)) v_sx v_iN_1 v_iN_2))
		| (I32), (INT_REM v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 32) (fun_irem_ (fun_sizenn (INN_I32 : numtype)) v_sx v_iN_1 v_iN_2))
		| (I64), (INT_REM v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 64) (fun_irem_ (fun_sizenn (INN_I64 : numtype)) v_sx v_iN_1 v_iN_2))
		| (I32), (INT_AND), v_iN_1, v_iN_2 => [(fun_iand_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_AND), v_iN_1, v_iN_2 => [(fun_iand_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (I32), (INT_OR), v_iN_1, v_iN_2 => [(fun_ior_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_OR), v_iN_1, v_iN_2 => [(fun_ior_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (I32), (INT_XOR), v_iN_1, v_iN_2 => [(fun_ixor_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_XOR), v_iN_1, v_iN_2 => [(fun_ixor_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (I32), (INT_SHL), v_iN_1, v_iN_2 => [(fun_ishl_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 (mk_uN _ (fun_proj_uN_0 32 v_iN_2)))]
		| (I64), (INT_SHL), v_iN_1, v_iN_2 => [(fun_ishl_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 (mk_uN _ (fun_proj_uN_0 64 v_iN_2)))]
		| (I32), (INT_SHR v_sx), v_iN_1, v_iN_2 => [(fun_ishr_ (fun_sizenn (INN_I32 : numtype)) v_sx v_iN_1 (mk_uN _ (fun_proj_uN_0 32 v_iN_2)))]
		| (I64), (INT_SHR v_sx), v_iN_1, v_iN_2 => [(fun_ishr_ (fun_sizenn (INN_I64 : numtype)) v_sx v_iN_1 (mk_uN _ (fun_proj_uN_0 64 v_iN_2)))]
		| (I32), (INT_ROTL), v_iN_1, v_iN_2 => [(fun_irotl_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_ROTL), v_iN_1, v_iN_2 => [(fun_irotl_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (I32), (INT_ROTR), v_iN_1, v_iN_2 => [(fun_irotr_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)]
		| (I64), (INT_ROTR), v_iN_1, v_iN_2 => [(fun_irotr_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)]
		| (F32), (FLOAT_ADD), v_fN_1, v_fN_2 => (fun_fadd_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_ADD), v_fN_1, v_fN_2 => (fun_fadd_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_SUB), v_fN_1, v_fN_2 => (fun_fsub_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_SUB), v_fN_1, v_fN_2 => (fun_fsub_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_MUL), v_fN_1, v_fN_2 => (fun_fmul_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_MUL), v_fN_1, v_fN_2 => (fun_fmul_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_DIV), v_fN_1, v_fN_2 => (fun_fdiv_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_DIV), v_fN_1, v_fN_2 => (fun_fdiv_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_MIN), v_fN_1, v_fN_2 => (fun_fmin_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_MIN), v_fN_1, v_fN_2 => (fun_fmin_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_MAX), v_fN_1, v_fN_2 => (fun_fmax_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_MAX), v_fN_1, v_fN_2 => (fun_fmax_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_COPYSIGN), v_fN_1, v_fN_2 => (fun_fcopysign_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_COPYSIGN), v_fN_1, v_fN_2 => (fun_fcopysign_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 *)
Definition fun_ieqz_ (v_N : res_N) (v_iN : (iN v_N)) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, v_i_1 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) == 0)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.1-49.32 *)
Definition fun_testop_ (v_numtype : numtype) (v_testop_ : (testop_ v_numtype)) (v_num_ : (num_ v_numtype)) : (uN 32) :=
	match v_numtype, v_testop_, v_num_ return (uN 32) with
		| (I32), (EQZ), v_iN => (fun_ieqz_ (fun_sizenn (INN_I32 : numtype)) v_iN)
		| (I64), (EQZ), v_iN => (fun_ieqz_ (fun_sizenn (INN_I64 : numtype)) v_iN)
		| _, _, _ => default_val
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 *)
Axiom fun_feq_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 *)
Axiom fun_fge_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 *)
Axiom fun_fgt_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 *)
Axiom fun_fle_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 *)
Axiom fun_flt_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 *)
Axiom fun_fne_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 *)
Definition fun_ieq_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_iN, v_iN_0 return u32 with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (fun_bool (v_i_1 == v_i_2)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.1-130.73 *)
Definition fun_ige_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 return u32 with
		| v_N, (U), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) >= (fun_proj_uN_0 v_N v_i_2))))
		| v_N, (res_S), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) >= (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.1-128.73 *)
Definition fun_igt_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 return u32 with
		| v_N, (U), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) > (fun_proj_uN_0 v_N v_i_2))))
		| v_N, (res_S), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) > (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.1-129.73 *)
Definition fun_ile_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 return u32 with
		| v_N, (U), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) <= (fun_proj_uN_0 v_N v_i_2))))
		| v_N, (res_S), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) <= (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.1-127.73 *)
Definition fun_ilt_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 return u32 with
		| v_N, (U), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) < (fun_proj_uN_0 v_N v_i_2))))
		| v_N, (res_S), v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) < (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 *)
Definition fun_ine_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_iN, v_iN_0 return u32 with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (fun_bool (v_i_1 != v_i_2)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.1-51.34 *)
Definition fun_relop_ (v_numtype : numtype) (v_relop_ : (relop_ v_numtype)) (v_num_ : (num_ v_numtype)) (v_num__0 : (num_ v_numtype)) : (uN 32) :=
	match v_numtype, v_relop_, v_num_, v_num__0 return (uN 32) with
		| (I32), (INT_EQ), v_iN_1, v_iN_2 => (fun_ieq_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)
		| (I64), (INT_EQ), v_iN_1, v_iN_2 => (fun_ieq_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)
		| (I32), (INT_NE), v_iN_1, v_iN_2 => (fun_ine_ (fun_sizenn (INN_I32 : numtype)) v_iN_1 v_iN_2)
		| (I64), (INT_NE), v_iN_1, v_iN_2 => (fun_ine_ (fun_sizenn (INN_I64 : numtype)) v_iN_1 v_iN_2)
		| (I32), (INT_LT v_sx), v_iN_1, v_iN_2 => (fun_ilt_ (fun_sizenn (INN_I32 : numtype)) v_sx v_iN_1 v_iN_2)
		| (I64), (INT_LT v_sx), v_iN_1, v_iN_2 => (fun_ilt_ (fun_sizenn (INN_I64 : numtype)) v_sx v_iN_1 v_iN_2)
		| (I32), (INT_GT v_sx), v_iN_1, v_iN_2 => (fun_igt_ (fun_sizenn (INN_I32 : numtype)) v_sx v_iN_1 v_iN_2)
		| (I64), (INT_GT v_sx), v_iN_1, v_iN_2 => (fun_igt_ (fun_sizenn (INN_I64 : numtype)) v_sx v_iN_1 v_iN_2)
		| (I32), (INT_LE v_sx), v_iN_1, v_iN_2 => (fun_ile_ (fun_sizenn (INN_I32 : numtype)) v_sx v_iN_1 v_iN_2)
		| (I64), (INT_LE v_sx), v_iN_1, v_iN_2 => (fun_ile_ (fun_sizenn (INN_I64 : numtype)) v_sx v_iN_1 v_iN_2)
		| (I32), (INT_GE v_sx), v_iN_1, v_iN_2 => (fun_ige_ (fun_sizenn (INN_I32 : numtype)) v_sx v_iN_1 v_iN_2)
		| (I64), (INT_GE v_sx), v_iN_1, v_iN_2 => (fun_ige_ (fun_sizenn (INN_I64 : numtype)) v_sx v_iN_1 v_iN_2)
		| (F32), (FLOAT_EQ), v_fN_1, v_fN_2 => (fun_feq_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_EQ), v_fN_1, v_fN_2 => (fun_feq_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_NE), v_fN_1, v_fN_2 => (fun_fne_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_NE), v_fN_1, v_fN_2 => (fun_fne_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_LT), v_fN_1, v_fN_2 => (fun_flt_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_LT), v_fN_1, v_fN_2 => (fun_flt_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_GT), v_fN_1, v_fN_2 => (fun_fgt_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_GT), v_fN_1, v_fN_2 => (fun_fgt_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_LE), v_fN_1, v_fN_2 => (fun_fle_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_LE), v_fN_1, v_fN_2 => (fun_fle_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
		| (F32), (FLOAT_GE), v_fN_1, v_fN_2 => (fun_fge_ (fun_sizenn (FNN_F32 : numtype)) v_fN_1 v_fN_2)
		| (F64), (FLOAT_GE), v_fN_1, v_fN_2 => (fun_fge_ (fun_sizenn (FNN_F64 : numtype)) v_fN_1 v_fN_2)
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 *)
Axiom fun_convert__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : (iN v_M)), (fN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 *)
Axiom fun_demote__ : forall (v_M : M) (v_N : res_N) (v_fN : (fN v_M)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 *)
Axiom fun_promote__ : forall (v_M : M) (v_N : res_N) (v_fN : (fN v_M)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 *)
Axiom fun_reinterpret__ : forall (v_numtype_1 : numtype) (v_numtype_2 : numtype) (v_num_ : (num_ v_numtype_1)), (num_ v_numtype_2).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 *)
Axiom fun_trunc__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : (fN v_M)), (option (iN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 *)
Axiom fun_trunc_sat__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : (fN v_M)), (option (iN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.1-53.36 *)
Axiom fun_cvtop__ : forall (v_numtype_1 : numtype) (v_numtype_2 : numtype) (v_cvtop : cvtop) (v_num_ : (num_ v_numtype_1)), (list (num_ v_numtype_2)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 *)
Axiom fun_narrow__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : (iN v_M)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 *)
Axiom fun_ibits_ : forall (v_N : res_N) (v_iN : (iN v_N)), (list bit).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 *)
Axiom fun_fbits_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list bit).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 *)
Axiom fun_ibytes_ : forall (v_N : res_N) (v_iN : (iN v_N)), (list byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 *)
Axiom fun_fbytes_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 *)
Axiom fun_nbytes_ : forall (v_numtype : numtype) (v_num_ : (num_ v_numtype)), (list byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 *)
Axiom fun_vbytes_ : forall (v_vectype : vectype) (v_vec_ : (vec_ v_vectype)), (list byte).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 *)
Axiom fun_inv_ibits_ : forall (v_N : res_N) (var_0 : (list bit)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 *)
Axiom fun_inv_fbits_ : forall (v_N : res_N) (var_0 : (list bit)), (fN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 *)
Axiom fun_inv_ibytes_ : forall (v_N : res_N) (var_0 : (list byte)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 *)
Axiom fun_inv_fbytes_ : forall (v_N : res_N) (var_0 : (list byte)), (fN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 *)
Axiom fun_inv_nbytes_ : forall (v_numtype : numtype) (var_0 : (list byte)), (num_ v_numtype).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 *)
Axiom fun_inv_vbytes_ : forall (v_vectype : vectype) (var_0 : (list byte)), (vec_ v_vectype).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 *)
Axiom fun_inot_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 *)
Axiom fun_irev_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 *)
Axiom fun_iandnot_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 *)
Definition fun_inez_ (v_N : res_N) (v_iN : (iN v_N)) : u32 :=
	match v_N, v_iN return u32 with
		| v_N, v_i_1 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) != 0)))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 *)
Axiom fun_ibitselect_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) (v_iN_1 : (iN v_N)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 *)
Definition fun_ineg_ (v_N : res_N) (v_iN : (iN v_N)) : (iN v_N) :=
	match v_N, v_iN return (iN v_N) with
		| v_N, v_i_1 => (mk_uN _ (((((2 ^ v_N) : nat) - ((fun_proj_uN_0 v_N v_i_1) : nat)) mod ((2 ^ v_N) : nat)) : nat))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.1-132.29 *)
Axiom fun_iabs_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.1-134.81 *)
Axiom fun_imin_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.1-135.81 *)
Axiom fun_imax_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.1-136.86 *)
Definition fun_iadd_sat_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_sx, v_iN, v_iN_0 return (iN v_N) with
		| v_N, (U), v_i_1, v_i_2 => (mk_uN _ (fun_sat_u_ v_N (((fun_proj_uN_0 v_N v_i_1) + (fun_proj_uN_0 v_N v_i_2)) : nat)))
		| v_N, (res_S), v_i_1, v_i_2 => (mk_uN _ (fun_inv_signed_ v_N (fun_sat_s_ v_N ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) + (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2))))))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.1-137.86 *)
Definition fun_isub_sat_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_sx, v_iN, v_iN_0 return (iN v_N) with
		| v_N, (U), v_i_1, v_i_2 => (mk_uN _ (fun_sat_u_ v_N (((fun_proj_uN_0 v_N v_i_1) : nat) - ((fun_proj_uN_0 v_N v_i_2) : nat))))
		| v_N, (res_S), v_i_1, v_i_2 => (mk_uN _ (fun_inv_signed_ v_N (fun_sat_s_ v_N ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) - (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2))))))
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 *)
Axiom fun_iavgr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 *)
Axiom fun_iq15mulr_sat_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 *)
Axiom fun_fpmin_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 *)
Axiom fun_fpmax_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 *)
Definition fun_coec_packtype__lanetype (v_packtype : packtype) : lanetype :=
	match v_packtype return lanetype with
		| (I8) => LANETYPE_I8
		| (I16) => LANETYPE_I16
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 *)
Coercion fun_coec_packtype__lanetype : packtype >-> lanetype.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 *)
Definition fun_packnum_ (v_lanetype : lanetype) (v_num_ : (num_ (fun_unpack v_lanetype))) : (lane_ v_lanetype) :=
	match v_lanetype, v_num_ return (lane_ v_lanetype) with
		| (LANETYPE_I32), v_c => v_c
		| (LANETYPE_I64), v_c => v_c
		| (LANETYPE_F32), v_c => v_c
		| (LANETYPE_F64), v_c => v_c
		| (LANETYPE_I8), v_c => (fun_wrap__ (the (fun_size ((fun_unpack (I8 : lanetype)) : valtype))) (fun_psize I8) v_c)
		| (LANETYPE_I16), v_c => (fun_wrap__ (the (fun_size ((fun_unpack (I16 : lanetype)) : valtype))) (fun_psize I16) v_c)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.1-329.29 *)
Definition fun_unpacknum_ (v_lanetype : lanetype) (v_lane_ : (lane_ v_lanetype)) : (num_ (fun_unpack v_lanetype)) :=
	match v_lanetype, v_lane_ return (num_ (fun_unpack v_lanetype)) with
		| (LANETYPE_I32), v_c => v_c
		| (LANETYPE_I64), v_c => v_c
		| (LANETYPE_F32), v_c => v_c
		| (LANETYPE_F64), v_c => v_c
		| (LANETYPE_I8), v_c => (fun_extend__ (fun_psize I8) (the (fun_size ((fun_unpack (I8 : lanetype)) : valtype))) U v_c)
		| (LANETYPE_I16), v_c => (fun_extend__ (fun_psize I16) (the (fun_size ((fun_unpack (I16 : lanetype)) : valtype))) U v_c)
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 *)
Axiom fun_lanes_ : forall (v_shape : shape) (v_vec_ : (vec_ V128)), (list (lane_ (fun_lanetype v_shape))).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 *)
Axiom fun_inv_lanes_ : forall (v_shape : shape) (var_0 : (list (lane_ (fun_lanetype v_shape)))), (vec_ V128).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:343.1-343.28 *)
Definition fun_zeroop (v_vcvtop : vcvtop) : (option zero) :=
	match v_vcvtop return (option zero) with
		| (V_EXTEND v_half v_sx) => None
		| (V_CONVERT v_half v_sx) => None
		| (V_TRUNC_SAT v_sx v_zero) => v_zero
		| (V_DEMOTE v_zero) => (Some v_zero)
		| (V_PROMOTELOW) => None
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:350.1-350.28 *)
Definition fun_halfop (v_vcvtop : vcvtop) : (option half) :=
	match v_vcvtop return (option half) with
		| (V_EXTEND v_half v_sx) => (Some v_half)
		| (V_CONVERT v_half v_sx) => v_half
		| (V_TRUNC_SAT v_sx v_zero) => None
		| (V_DEMOTE v_zero) => None
		| (V_PROMOTELOW) => (Some LOW)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:357.1-357.32 *)
Definition fun_half (v_half : half) (v_nat : nat) (v_nat_0 : nat) : nat :=
	match v_half, v_nat, v_nat_0 return nat with
		| (LOW), v_i, v_j => v_i
		| (HIGH), v_i, v_j => v_j
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.1-363.28 *)
Definition fun_vvunop_ (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : (vec_ v_vectype)) : (vec_ v_vectype) :=
	match v_vectype, v_vvunop, v_vec_ return (vec_ v_vectype) with
		| (V128), (NOT), v_v128 => (fun_inot_ (the (fun_size VALTYPE_V128)) v_v128)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 *)
Definition fun_vvbinop_ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : (vec_ v_vectype)) (v_vec__0 : (vec_ v_vectype)) : (vec_ v_vectype) :=
	match v_vectype, v_vvbinop, v_vec_, v_vec__0 return (vec_ v_vectype) with
		| (V128), (AND), v_v128_1, v_v128_2 => (fun_iand_ (the (fun_size VALTYPE_V128)) v_v128_1 v_v128_2)
		| (V128), (ANDNOT), v_v128_1, v_v128_2 => (fun_iandnot_ (the (fun_size VALTYPE_V128)) v_v128_1 v_v128_2)
		| (V128), (OR), v_v128_1, v_v128_2 => (fun_ior_ (the (fun_size VALTYPE_V128)) v_v128_1 v_v128_2)
		| (V128), (XOR), v_v128_1, v_v128_2 => (fun_ixor_ (the (fun_size VALTYPE_V128)) v_v128_1 v_v128_2)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 *)
Definition fun_vvternop_ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : (vec_ v_vectype)) (v_vec__0 : (vec_ v_vectype)) (v_vec__1 : (vec_ v_vectype)) : (vec_ v_vectype) :=
	match v_vectype, v_vvternop, v_vec_, v_vec__0, v_vec__1 return (vec_ v_vectype) with
		| (V128), (BITSELECT), v_v128_1, v_v128_2, v_v128_3 => (fun_ibitselect_ (the (fun_size VALTYPE_V128)) v_v128_1 v_v128_2 v_v128_3)
	end.

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.1-378.32 *)
Axiom fun_vunop_ : forall (v_shape : shape) (v_vunop_ : (vunop_ v_shape)) (v_vec_ : (vec_ V128)), (list (vec_ V128)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.1-380.34 *)
Axiom fun_vbinop_ : forall (v_shape : shape) (v_vbinop_ : (vbinop_ v_shape)) (v_vec_ : (vec_ V128)) (v_vec__0 : (vec_ V128)), (list (vec_ V128)).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.1-382.34 *)
Axiom fun_vrelop_ : forall (v_shape : shape) (v_vrelop_ : (vrelop_ v_shape)) (v_vec_ : (vec_ V128)) (v_vec__0 : (vec_ V128)), (vec_ V128).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
Axiom fun_vcvtop__ : forall (v_shape_1 : shape) (v_shape_2 : shape) (v_vcvtop : vcvtop) (v_lane_ : (lane_ (fun_lanetype v_shape_1))), (list (lane_ (fun_lanetype v_shape_2))).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.1-584.42 *)
Axiom fun_vextunop__ : forall (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_vextunop_ : (vextunop_ v_ishape_1)) (v_vec_ : (vec_ V128)), (vec_ V128).

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.1-586.45 *)
Axiom fun_vextbinop__ : forall (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_vextbinop_ : (vextbinop_ v_ishape_1)) (v_vec_ : (vec_ V128)) (v_vec__0 : (vec_ V128)), (vec_ V128).

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.1-609.31 *)
Definition fun_vshiftop_ (v_ishape : ishape) (v_vshiftop_ : (vshiftop_ v_ishape)) (v_lane_ : (lane_ (fun_lanetype (v_ishape : shape)))) (v_u32 : u32) : (lane_ (fun_lanetype (v_ishape : shape))) :=
	match v_ishape, v_vshiftop_, v_lane_, v_u32 return (lane_ (fun_lanetype (v_ishape : shape))) with
		| (IX (JNN_I32) (mk_dim v_M)), (VSHIFT_SHL), v_lane, (mk_uN v_n) => (fun_ishl_ (fun_lsizenn (JNN_I32 : lanetype)) v_lane (mk_uN _ v_n))
		| (IX (JNN_I64) (mk_dim v_M)), (VSHIFT_SHL), v_lane, (mk_uN v_n) => (fun_ishl_ (fun_lsizenn (JNN_I64 : lanetype)) v_lane (mk_uN _ v_n))
		| (IX (JNN_I8) (mk_dim v_M)), (VSHIFT_SHL), v_lane, (mk_uN v_n) => (fun_ishl_ (fun_lsizenn (JNN_I8 : lanetype)) v_lane (mk_uN _ v_n))
		| (IX (JNN_I16) (mk_dim v_M)), (VSHIFT_SHL), v_lane, (mk_uN v_n) => (fun_ishl_ (fun_lsizenn (JNN_I16 : lanetype)) v_lane (mk_uN _ v_n))
		| (IX (JNN_I32) (mk_dim v_M)), (VSHIFT_SHR v_sx), v_lane, (mk_uN v_n) => (fun_ishr_ (fun_lsizenn (JNN_I32 : lanetype)) v_sx v_lane (mk_uN _ v_n))
		| (IX (JNN_I64) (mk_dim v_M)), (VSHIFT_SHR v_sx), v_lane, (mk_uN v_n) => (fun_ishr_ (fun_lsizenn (JNN_I64 : lanetype)) v_sx v_lane (mk_uN _ v_n))
		| (IX (JNN_I8) (mk_dim v_M)), (VSHIFT_SHR v_sx), v_lane, (mk_uN v_n) => (fun_ishr_ (fun_lsizenn (JNN_I8 : lanetype)) v_sx v_lane (mk_uN _ v_n))
		| (IX (JNN_I16) (mk_dim v_M)), (VSHIFT_SHR v_sx), v_lane, (mk_uN v_n) => (fun_ishr_ (fun_lsizenn (JNN_I16 : lanetype)) v_sx v_lane (mk_uN _ v_n))
	end.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:5.1-5.39 *)
Definition addr := nat.

Definition addr_eq_dec : forall (v1 v2 : addr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition addr_eqb (v1 v2 : addr) : bool :=
	is_left(addr_eq_dec v1 v2).
Definition eqaddrP : Equality.axiom (addr_eqb) :=
	eq_dec_Equality_axiom (addr) (addr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (addr) (eqaddrP).
Hint Resolve addr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:6.1-6.53 *)
Definition funcaddr := addr.

Definition funcaddr_eq_dec : forall (v1 v2 : funcaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition funcaddr_eqb (v1 v2 : funcaddr) : bool :=
	is_left(funcaddr_eq_dec v1 v2).
Definition eqfuncaddrP : Equality.axiom (funcaddr_eqb) :=
	eq_dec_Equality_axiom (funcaddr) (funcaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (funcaddr) (eqfuncaddrP).
Hint Resolve funcaddr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:7.1-7.53 *)
Definition globaladdr := addr.

Definition globaladdr_eq_dec : forall (v1 v2 : globaladdr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globaladdr_eqb (v1 v2 : globaladdr) : bool :=
	is_left(globaladdr_eq_dec v1 v2).
Definition eqglobaladdrP : Equality.axiom (globaladdr_eqb) :=
	eq_dec_Equality_axiom (globaladdr) (globaladdr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globaladdr) (eqglobaladdrP).
Hint Resolve globaladdr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:8.1-8.51 *)
Definition tableaddr := addr.

Definition tableaddr_eq_dec : forall (v1 v2 : tableaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tableaddr_eqb (v1 v2 : tableaddr) : bool :=
	is_left(tableaddr_eq_dec v1 v2).
Definition eqtableaddrP : Equality.axiom (tableaddr_eqb) :=
	eq_dec_Equality_axiom (tableaddr) (tableaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tableaddr) (eqtableaddrP).
Hint Resolve tableaddr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:9.1-9.50 *)
Definition memaddr := addr.

Definition memaddr_eq_dec : forall (v1 v2 : memaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memaddr_eqb (v1 v2 : memaddr) : bool :=
	is_left(memaddr_eq_dec v1 v2).
Definition eqmemaddrP : Equality.axiom (memaddr_eqb) :=
	eq_dec_Equality_axiom (memaddr) (memaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memaddr) (eqmemaddrP).
Hint Resolve memaddr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:10.1-10.49 *)
Definition elemaddr := addr.

Definition elemaddr_eq_dec : forall (v1 v2 : elemaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elemaddr_eqb (v1 v2 : elemaddr) : bool :=
	is_left(elemaddr_eq_dec v1 v2).
Definition eqelemaddrP : Equality.axiom (elemaddr_eqb) :=
	eq_dec_Equality_axiom (elemaddr) (elemaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elemaddr) (eqelemaddrP).
Hint Resolve elemaddr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:11.1-11.49 *)
Definition dataaddr := addr.

Definition dataaddr_eq_dec : forall (v1 v2 : dataaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition dataaddr_eqb (v1 v2 : dataaddr) : bool :=
	is_left(dataaddr_eq_dec v1 v2).
Definition eqdataaddrP : Equality.axiom (dataaddr_eqb) :=
	eq_dec_Equality_axiom (dataaddr) (dataaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (dataaddr) (eqdataaddrP).
Hint Resolve dataaddr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:12.1-12.49 *)
Definition hostaddr := addr.

Definition hostaddr_eq_dec : forall (v1 v2 : hostaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition hostaddr_eqb (v1 v2 : hostaddr) : bool :=
	is_left(hostaddr_eq_dec v1 v2).
Definition eqhostaddrP : Equality.axiom (hostaddr_eqb) :=
	eq_dec_Equality_axiom (hostaddr) (hostaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (hostaddr) (eqhostaddrP).
Hint Resolve hostaddr_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:25.1-26.70 *)
Inductive externaddr : Type :=
	| EXTADDR_FUNC (v_funcaddr : funcaddr) : externaddr
	| EXTADDR_GLOBAL (v_globaladdr : globaladdr) : externaddr
	| EXTADDR_TABLE (v_tableaddr : tableaddr) : externaddr
	| EXTADDR_MEM (v_memaddr : memaddr) : externaddr.

Global Instance Inhabited__externaddr : Inhabited (externaddr) := { default_val := EXTADDR_FUNC default_val }.

Definition externaddr_eq_dec : forall (v1 v2 : externaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition externaddr_eqb (v1 v2 : externaddr) : bool :=
	is_left(externaddr_eq_dec v1 v2).
Definition eqexternaddrP : Equality.axiom (externaddr_eqb) :=
	eq_dec_Equality_axiom (externaddr) (externaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (externaddr) (eqexternaddrP).
Hint Resolve externaddr_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.1-38.62 *)
Inductive num : Type :=
	| CONST (v_numtype : numtype) (v_num_ : (num_ v_numtype)) : num.

Global Instance Inhabited__num : Inhabited (num) := { default_val := CONST default_val default_val }.

(* FIXME - No clear way to do decidable equality *)
Definition num_eq_dec : forall (v1 v2 : num),
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition num_eqb (v1 v2 : num) : bool :=
	is_left(num_eq_dec v1 v2).
Definition eqnumP : Equality.axiom (num_eqb) :=
	eq_dec_Equality_axiom (num) (num_eq_dec).

HB.instance Definition _ := hasDecEq.Build (num) (eqnumP).
Hint Resolve num_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62 *)
Inductive vec : Type :=
	| VCONST (v_vectype : vectype) (v_vec_ : (vec_ v_vectype)) : vec.

Global Instance Inhabited__vec : Inhabited (vec) := { default_val := VCONST default_val default_val }.

(* FIXME - No clear way to do decidable equality *)
Definition vec_eq_dec : forall (v1 v2 : vec),
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition vec_eqb (v1 v2 : vec) : bool :=
	is_left(vec_eq_dec v1 v2).
Definition eqvecP : Equality.axiom (vec_eqb) :=
	eq_dec_Equality_axiom (vec) (vec_eq_dec).

HB.instance Definition _ := hasDecEq.Build (vec) (eqvecP).
Hint Resolve vec_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71 *)
Inductive ref : Type :=
	| REF_NULL (v_reftype : reftype) : ref
	| REF_FUNC_ADDR (v_funcaddr : funcaddr) : ref
	| REF_HOST_ADDR (v_hostaddr : hostaddr) : ref.

Global Instance Inhabited__ref : Inhabited (ref) := { default_val := REF_NULL default_val }.

Definition ref_eq_dec : forall (v1 v2 : ref),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition ref_eqb (v1 v2 : ref) : bool :=
	is_left(ref_eq_dec v1 v2).
Definition eqrefP : Equality.axiom (ref_eqb) :=
	eq_dec_Equality_axiom (ref) (ref_eq_dec).

HB.instance Definition _ := hasDecEq.Build (ref) (eqrefP).
Hint Resolve ref_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20 *)
Inductive val : Type :=
	| VAL_CONST (v_numtype : numtype) (v_num_ : (num_ v_numtype)) : val
	| VAL_VCONST (v_vectype : vectype) (v_vec_ : (vec_ v_vectype)) : val
	| VAL_REF_NULL (v_reftype : reftype) : val
	| VAL_REF_FUNC_ADDR (v_funcaddr : funcaddr) : val
	| VAL_REF_HOST_ADDR (v_hostaddr : hostaddr) : val.

Global Instance Inhabited__val : Inhabited (val) := { default_val := VAL_CONST default_val default_val }.

(* FIXME - No clear way to do decidable equality *)
Definition val_eq_dec : forall (v1 v2 : val),
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition val_eqb (v1 v2 : val) : bool :=
	is_left(val_eq_dec v1 v2).
Definition eqvalP : Equality.axiom (val_eqb) :=
	eq_dec_Equality_axiom (val) (val_eq_dec).

HB.instance Definition _ := hasDecEq.Build (val) (eqvalP).
Hint Resolve val_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22 *)
Inductive result : Type :=
	| _VALS (_ : (list val)) : result
	| TRAP : result.

Global Instance Inhabited__result : Inhabited (result) := { default_val := _VALS default_val }.

Definition result_eq_dec : forall (v1 v2 : result),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition result_eqb (v1 v2 : result) : bool :=
	is_left(result_eq_dec v1 v2).
Definition eqresultP : Equality.axiom (result_eqb) :=
	eq_dec_Equality_axiom (result) (result_eq_dec).

HB.instance Definition _ := hasDecEq.Build (result) (eqresultP).
Hint Resolve result_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22 *)
Record exportinst := MKexportinst
{	NAME : name
;	ADDR : externaddr
}.

Global Instance Inhabited_exportinst : Inhabited exportinst := 
{default_val := {|
	NAME := default_val;
	ADDR := default_val|} }.

Definition _append_exportinst (arg1 arg2 : exportinst) :=
{|
	NAME := arg1.(NAME); (* FIXME - Non-trivial append *)
	ADDR := arg1.(ADDR); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_exportinst : Append exportinst := { _append arg1 arg2 := _append_exportinst arg1 arg2 }.

#[export] Instance eta__exportinst : Settable _ := settable! MKexportinst <NAME;ADDR>.

Definition exportinst_eq_dec : forall (v1 v2 : exportinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition exportinst_eqb (v1 v2 : exportinst) : bool :=
	is_left(exportinst_eq_dec v1 v2).
Definition eqexportinstP : Equality.axiom (exportinst_eqb) :=
	eq_dec_Equality_axiom (exportinst) (exportinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (exportinst) (eqexportinstP).
Hint Resolve exportinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26 *)
Record moduleinst := MKmoduleinst
{	MODULE_TYPES : (list functype)
;	MODULE_FUNCS : (list funcaddr)
;	MODULE_GLOBALS : (list globaladdr)
;	MODULE_TABLES : (list tableaddr)
;	MODULE_MEMS : (list memaddr)
;	MODULE_ELEMS : (list elemaddr)
;	MODULE_DATAS : (list dataaddr)
;	MODULE_EXPORTS : (list exportinst)
}.

Global Instance Inhabited_moduleinst : Inhabited moduleinst := 
{default_val := {|
	MODULE_TYPES := default_val;
	MODULE_FUNCS := default_val;
	MODULE_GLOBALS := default_val;
	MODULE_TABLES := default_val;
	MODULE_MEMS := default_val;
	MODULE_ELEMS := default_val;
	MODULE_DATAS := default_val;
	MODULE_EXPORTS := default_val|} }.

Definition _append_moduleinst (arg1 arg2 : moduleinst) :=
{|
	MODULE_TYPES := arg1.(MODULE_TYPES) @@ arg2.(MODULE_TYPES);
	MODULE_FUNCS := arg1.(MODULE_FUNCS) @@ arg2.(MODULE_FUNCS);
	MODULE_GLOBALS := arg1.(MODULE_GLOBALS) @@ arg2.(MODULE_GLOBALS);
	MODULE_TABLES := arg1.(MODULE_TABLES) @@ arg2.(MODULE_TABLES);
	MODULE_MEMS := arg1.(MODULE_MEMS) @@ arg2.(MODULE_MEMS);
	MODULE_ELEMS := arg1.(MODULE_ELEMS) @@ arg2.(MODULE_ELEMS);
	MODULE_DATAS := arg1.(MODULE_DATAS) @@ arg2.(MODULE_DATAS);
	MODULE_EXPORTS := arg1.(MODULE_EXPORTS) @@ arg2.(MODULE_EXPORTS);
|}.

Global Instance Append_moduleinst : Append moduleinst := { _append arg1 arg2 := _append_moduleinst arg1 arg2 }.

#[export] Instance eta__moduleinst : Settable _ := settable! MKmoduleinst <MODULE_TYPES;MODULE_FUNCS;MODULE_GLOBALS;MODULE_TABLES;MODULE_MEMS;MODULE_ELEMS;MODULE_DATAS;MODULE_EXPORTS>.

Definition moduleinst_eq_dec : forall (v1 v2 : moduleinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition moduleinst_eqb (v1 v2 : moduleinst) : bool :=
	is_left(moduleinst_eq_dec v1 v2).
Definition eqmoduleinstP : Equality.axiom (moduleinst_eqb) :=
	eq_dec_Equality_axiom (moduleinst) (moduleinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (moduleinst) (eqmoduleinstP).
Hint Resolve moduleinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16 *)
Record funcinst := MKfuncinst
{	FUNC_TYPE : functype
;	FUNC_MODULE : moduleinst
;	FUNC_CODE : func
}.

Global Instance Inhabited_funcinst : Inhabited funcinst := 
{default_val := {|
	FUNC_TYPE := default_val;
	FUNC_MODULE := default_val;
	FUNC_CODE := default_val|} }.

Definition _append_funcinst (arg1 arg2 : funcinst) :=
{|
	FUNC_TYPE := arg1.(FUNC_TYPE); (* FIXME - Non-trivial append *)
	FUNC_MODULE := arg1.(FUNC_MODULE) @@ arg2.(FUNC_MODULE);
	FUNC_CODE := arg1.(FUNC_CODE); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_funcinst : Append funcinst := { _append arg1 arg2 := _append_funcinst arg1 arg2 }.

#[export] Instance eta__funcinst : Settable _ := settable! MKfuncinst <FUNC_TYPE;FUNC_MODULE;FUNC_CODE>.

Definition funcinst_eq_dec : forall (v1 v2 : funcinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition funcinst_eqb (v1 v2 : funcinst) : bool :=
	is_left(funcinst_eq_dec v1 v2).
Definition eqfuncinstP : Equality.axiom (funcinst_eqb) :=
	eq_dec_Equality_axiom (funcinst) (funcinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (funcinst) (eqfuncinstP).
Hint Resolve funcinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16 *)
Record globalinst := MKglobalinst
{	GLOB_TYPE : globaltype
;	GLOB_VALUE : val
}.

Global Instance Inhabited_globalinst : Inhabited globalinst := 
{default_val := {|
	GLOB_TYPE := default_val;
	GLOB_VALUE := default_val|} }.

Definition _append_globalinst (arg1 arg2 : globalinst) :=
{|
	GLOB_TYPE := arg1.(GLOB_TYPE); (* FIXME - Non-trivial append *)
	GLOB_VALUE := arg1.(GLOB_VALUE); (* FIXME - Non-trivial append *)
|}.

Global Instance Append_globalinst : Append globalinst := { _append arg1 arg2 := _append_globalinst arg1 arg2 }.

#[export] Instance eta__globalinst : Settable _ := settable! MKglobalinst <GLOB_TYPE;GLOB_VALUE>.

Definition globalinst_eq_dec : forall (v1 v2 : globalinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globalinst_eqb (v1 v2 : globalinst) : bool :=
	is_left(globalinst_eq_dec v1 v2).
Definition eqglobalinstP : Equality.axiom (globalinst_eqb) :=
	eq_dec_Equality_axiom (globalinst) (globalinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globalinst) (eqglobalinstP).
Hint Resolve globalinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16 *)
Record tableinst := MKtableinst
{	TAB_TYPE : tabletype
;	TAB_REFS : (list ref)
}.

Global Instance Inhabited_tableinst : Inhabited tableinst := 
{default_val := {|
	TAB_TYPE := default_val;
	TAB_REFS := default_val|} }.

Definition _append_tableinst (arg1 arg2 : tableinst) :=
{|
	TAB_TYPE := arg1.(TAB_TYPE); (* FIXME - Non-trivial append *)
	TAB_REFS := arg1.(TAB_REFS) @@ arg2.(TAB_REFS);
|}.

Global Instance Append_tableinst : Append tableinst := { _append arg1 arg2 := _append_tableinst arg1 arg2 }.

#[export] Instance eta__tableinst : Settable _ := settable! MKtableinst <TAB_TYPE;TAB_REFS>.

Definition tableinst_eq_dec : forall (v1 v2 : tableinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tableinst_eqb (v1 v2 : tableinst) : bool :=
	is_left(tableinst_eq_dec v1 v2).
Definition eqtableinstP : Equality.axiom (tableinst_eqb) :=
	eq_dec_Equality_axiom (tableinst) (tableinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tableinst) (eqtableinstP).
Hint Resolve tableinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18 *)
Record meminst := MKmeminst
{	MEM_TYPE : memtype
;	MEM_BYTES : (list byte)
}.

Global Instance Inhabited_meminst : Inhabited meminst := 
{default_val := {|
	MEM_TYPE := default_val;
	MEM_BYTES := default_val|} }.

Definition _append_meminst (arg1 arg2 : meminst) :=
{|
	MEM_TYPE := arg1.(MEM_TYPE); (* FIXME - Non-trivial append *)
	MEM_BYTES := arg1.(MEM_BYTES) @@ arg2.(MEM_BYTES);
|}.

Global Instance Append_meminst : Append meminst := { _append arg1 arg2 := _append_meminst arg1 arg2 }.

#[export] Instance eta__meminst : Settable _ := settable! MKmeminst <MEM_TYPE;MEM_BYTES>.

Definition meminst_eq_dec : forall (v1 v2 : meminst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition meminst_eqb (v1 v2 : meminst) : bool :=
	is_left(meminst_eq_dec v1 v2).
Definition eqmeminstP : Equality.axiom (meminst_eqb) :=
	eq_dec_Equality_axiom (meminst) (meminst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (meminst) (eqmeminstP).
Hint Resolve meminst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16 *)
Record eleminst := MKeleminst
{	ELEM_TYPE : elemtype
;	ELEM_REFS : (list ref)
}.

Global Instance Inhabited_eleminst : Inhabited eleminst := 
{default_val := {|
	ELEM_TYPE := default_val;
	ELEM_REFS := default_val|} }.

Definition _append_eleminst (arg1 arg2 : eleminst) :=
{|
	ELEM_TYPE := arg1.(ELEM_TYPE); (* FIXME - Non-trivial append *)
	ELEM_REFS := arg1.(ELEM_REFS) @@ arg2.(ELEM_REFS);
|}.

Global Instance Append_eleminst : Append eleminst := { _append arg1 arg2 := _append_eleminst arg1 arg2 }.

#[export] Instance eta__eleminst : Settable _ := settable! MKeleminst <ELEM_TYPE;ELEM_REFS>.

Definition eleminst_eq_dec : forall (v1 v2 : eleminst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition eleminst_eqb (v1 v2 : eleminst) : bool :=
	is_left(eleminst_eq_dec v1 v2).
Definition eqeleminstP : Equality.axiom (eleminst_eqb) :=
	eq_dec_Equality_axiom (eleminst) (eleminst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (eleminst) (eqeleminstP).
Hint Resolve eleminst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18 *)
Record datainst := MKdatainst
{	DATA_BYTES : (list byte)
}.

Global Instance Inhabited_datainst : Inhabited datainst := 
{default_val := {|
	DATA_BYTES := default_val|} }.

Definition _append_datainst (arg1 arg2 : datainst) :=
{|
	DATA_BYTES := arg1.(DATA_BYTES) @@ arg2.(DATA_BYTES);
|}.

Global Instance Append_datainst : Append datainst := { _append arg1 arg2 := _append_datainst arg1 arg2 }.

#[export] Instance eta__datainst : Settable _ := settable! MKdatainst <DATA_BYTES>.

Definition datainst_eq_dec : forall (v1 v2 : datainst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition datainst_eqb (v1 v2 : datainst) : bool :=
	is_left(datainst_eq_dec v1 v2).
Definition eqdatainstP : Equality.axiom (datainst_eqb) :=
	eq_dec_Equality_axiom (datainst) (datainst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (datainst) (eqdatainstP).
Hint Resolve datainst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22 *)
Record store := MKstore
{	FUNCS : (list funcinst)
;	GLOBALS : (list globalinst)
;	TABLES : (list tableinst)
;	MEMS : (list meminst)
;	ELEMS : (list eleminst)
;	DATAS : (list datainst)
}.

Global Instance Inhabited_store : Inhabited store := 
{default_val := {|
	FUNCS := default_val;
	GLOBALS := default_val;
	TABLES := default_val;
	MEMS := default_val;
	ELEMS := default_val;
	DATAS := default_val|} }.

Definition _append_store (arg1 arg2 : store) :=
{|
	FUNCS := arg1.(FUNCS) @@ arg2.(FUNCS);
	GLOBALS := arg1.(GLOBALS) @@ arg2.(GLOBALS);
	TABLES := arg1.(TABLES) @@ arg2.(TABLES);
	MEMS := arg1.(MEMS) @@ arg2.(MEMS);
	ELEMS := arg1.(ELEMS) @@ arg2.(ELEMS);
	DATAS := arg1.(DATAS) @@ arg2.(DATAS);
|}.

Global Instance Append_store : Append store := { _append arg1 arg2 := _append_store arg1 arg2 }.

#[export] Instance eta__store : Settable _ := settable! MKstore <FUNCS;GLOBALS;TABLES;MEMS;ELEMS;DATAS>.

Definition store_eq_dec : forall (v1 v2 : store),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition store_eqb (v1 v2 : store) : bool :=
	is_left(store_eq_dec v1 v2).
Definition eqstoreP : Equality.axiom (store_eqb) :=
	eq_dec_Equality_axiom (store) (store_eq_dec).

HB.instance Definition _ := hasDecEq.Build (store) (eqstoreP).
Hint Resolve store_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24 *)
Record frame := MKframe
{	F_LOCALS : (list val)
;	F_MODULE : moduleinst
}.

Global Instance Inhabited_frame : Inhabited frame := 
{default_val := {|
	F_LOCALS := default_val;
	F_MODULE := default_val|} }.

Definition _append_frame (arg1 arg2 : frame) :=
{|
	F_LOCALS := arg1.(F_LOCALS) @@ arg2.(F_LOCALS);
	F_MODULE := arg1.(F_MODULE) @@ arg2.(F_MODULE);
|}.

Global Instance Append_frame : Append frame := { _append arg1 arg2 := _append_frame arg1 arg2 }.

#[export] Instance eta__frame : Settable _ := settable! MKframe <F_LOCALS;F_MODULE>.

Definition frame_eq_dec : forall (v1 v2 : frame),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition frame_eqb (v1 v2 : frame) : bool :=
	is_left(frame_eq_dec v1 v2).
Definition eqframeP : Equality.axiom (frame_eqb) :=
	eq_dec_Equality_axiom (frame) (frame_eq_dec).

HB.instance Definition _ := hasDecEq.Build (frame) (eqframeP).
Hint Resolve frame_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47 *)
Inductive state : Type :=
	| mk_state (v_store : store) (v_frame : frame) : state.

Global Instance Inhabited__state : Inhabited (state) := { default_val := mk_state default_val default_val }.

Definition state_eq_dec : forall (v1 v2 : state),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition state_eqb (v1 v2 : state) : bool :=
	is_left(state_eq_dec v1 v2).
Definition eqstateP : Equality.axiom (state_eqb) :=
	eq_dec_Equality_axiom (state) (state_eq_dec).

HB.instance Definition _ := hasDecEq.Build (state) (eqstateP).
Hint Resolve state_eq_dec : eq_dec_db.

(* Mutual Recursion at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
Inductive admininstr : Type :=
	| AI_NOP : admininstr
	| AI_UNREACHABLE : admininstr
	| AI_DROP : admininstr
	| AI_SELECT (_ : (option (list valtype))) : admininstr
	| AI_BLOCK (v_blocktype : blocktype) (_ : (list instr)) : admininstr
	| AI_LOOP (v_blocktype : blocktype) (_ : (list instr)) : admininstr
	| AI_IFELSE (v_blocktype : blocktype) (_ : (list instr)) (v__ : (list instr)) : admininstr
	| AI_BR (v_labelidx : labelidx) : admininstr
	| AI_BR_IF (v_labelidx : labelidx) : admininstr
	| AI_BR_TABLE (_ : (list labelidx)) (v__ : labelidx) : admininstr
	| AI_CALL (v_funcidx : funcidx) : admininstr
	| AI_CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : admininstr
	| AI_RETURN : admininstr
	| AI_CONST (v_numtype : numtype) (v_num_ : (num_ v_numtype)) : admininstr
	| AI_UNOP (v_numtype : numtype) (v_unop_ : (unop_ v_numtype)) : admininstr
	| AI_BINOP (v_numtype : numtype) (v_binop_ : (binop_ v_numtype)) : admininstr
	| AI_TESTOP (v_numtype : numtype) (v_testop_ : (testop_ v_numtype)) : admininstr
	| AI_RELOP (v_numtype : numtype) (v_relop_ : (relop_ v_numtype)) : admininstr
	| AI_CVTOP (v_numtype_1 : numtype) (v_numtype_2 : numtype) (v_cvtop : cvtop) : admininstr
	| AI_EXTEND (v_numtype : numtype) (v_n : n) : admininstr
	| AI_VCONST (v_vectype : vectype) (v_vec_ : (vec_ v_vectype)) : admininstr
	| AI_VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : admininstr
	| AI_VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : admininstr
	| AI_VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : admininstr
	| AI_VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : admininstr
	| AI_VUNOP (v_shape : shape) (v_vunop_ : (vunop_ v_shape)) : admininstr
	| AI_VBINOP (v_shape : shape) (v_vbinop_ : (vbinop_ v_shape)) : admininstr
	| AI_VTESTOP (v_shape : shape) (v_vtestop_ : (vtestop_ v_shape)) : admininstr
	| AI_VRELOP (v_shape : shape) (v_vrelop_ : (vrelop_ v_shape)) : admininstr
	| AI_VSHIFTOP (v_ishape : ishape) (v_vshiftop_ : (vshiftop_ v_ishape)) : admininstr
	| AI_VBITMASK (v_ishape : ishape) : admininstr
	| AI_VSWIZZLE (v_ishape : ishape) : admininstr
	| AI_VSHUFFLE (v_ishape : ishape) (_ : (list laneidx)) : admininstr
	| AI_VSPLAT (v_shape : shape) : admininstr
	| AI_VEXTRACT_LANE (v_shape : shape) (_ : (option sx)) (v_laneidx : laneidx) : admininstr
	| AI_VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : admininstr
	| AI_VEXTUNOP (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_vextunop_ : (vextunop_ v_ishape_1)) : admininstr
	| AI_VEXTBINOP (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_vextbinop_ : (vextbinop_ v_ishape_1)) : admininstr
	| AI_VNARROW (v_ishape_1 : ishape) (v_ishape_2 : ishape) (v_sx : sx) : admininstr
	| AI_VCVTOP (v_shape : shape) (v__ : shape) (v_vcvtop : vcvtop) : admininstr
	| AI_REF_NULL (v_reftype : reftype) : admininstr
	| AI_REF_FUNC (v_funcidx : funcidx) : admininstr
	| AI_REF_IS_NULL : admininstr
	| AI_LOCAL_GET (v_localidx : localidx) : admininstr
	| AI_LOCAL_SET (v_localidx : localidx) : admininstr
	| AI_LOCAL_TEE (v_localidx : localidx) : admininstr
	| AI_GLOBAL_GET (v_globalidx : globalidx) : admininstr
	| AI_GLOBAL_SET (v_globalidx : globalidx) : admininstr
	| AI_TABLE_GET (v_tableidx : tableidx) : admininstr
	| AI_TABLE_SET (v_tableidx : tableidx) : admininstr
	| AI_TABLE_SIZE (v_tableidx : tableidx) : admininstr
	| AI_TABLE_GROW (v_tableidx : tableidx) : admininstr
	| AI_TABLE_FILL (v_tableidx : tableidx) : admininstr
	| AI_TABLE_COPY (v_tableidx : tableidx) (v__ : tableidx) : admininstr
	| AI_TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : admininstr
	| AI_ELEM_DROP (v_elemidx : elemidx) : admininstr
	| AI_LOAD (v_numtype : numtype) (_ : (option (loadop_ v_numtype))) (v_memarg : memarg) : admininstr
	| AI_STORE (v_numtype : numtype) (_ : (option sz)) (v_memarg : memarg) : admininstr
	| AI_VLOAD (v_vectype : vectype) (_ : (option vloadop)) (v_memarg : memarg) : admininstr
	| AI_VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : admininstr
	| AI_VSTORE (v_vectype : vectype) (v_memarg : memarg) : admininstr
	| AI_VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : admininstr
	| AI_MEMORY_SIZE : admininstr
	| AI_MEMORY_GROW : admininstr
	| AI_MEMORY_FILL : admininstr
	| AI_MEMORY_COPY : admininstr
	| AI_MEMORY_INIT (v_dataidx : dataidx) : admininstr
	| AI_DATA_DROP (v_dataidx : dataidx) : admininstr
	| AI_REF_FUNC_ADDR (v_funcaddr : funcaddr) : admininstr
	| AI_REF_HOST_ADDR (v_hostaddr : hostaddr) : admininstr
	| AI_CALL_ADDR (v_funcaddr : funcaddr) : admininstr
	| AI_LABEL_ (v_n : n) (_ : (list instr)) (_ : (list admininstr)) : admininstr
	| AI_FRAME_ (v_n : n) (v_frame : frame) (_ : (list admininstr)) : admininstr
	| AI_TRAP : admininstr.

Global Instance Inhabited__admininstr : Inhabited (admininstr) := { default_val := AI_NOP }.

(* FIXME - No clear way to do decidable equality *)
Fixpoint admininstr_eq_dec (v1 v2 : admininstr) {struct v1} :
  {v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition admininstr_eqb (v1 v2 : admininstr) : bool :=
	is_left(admininstr_eq_dec v1 v2).
Definition eqadmininstrP : Equality.axiom (admininstr_eqb) :=
	eq_dec_Equality_axiom (admininstr) (admininstr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (admininstr) (eqadmininstrP).
Hint Resolve admininstr_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
Fixpoint wf_admininstr (v_x : admininstr) : Prop :=
	match v_x return Prop with
		| (AI_CVTOP v_numtype_1 v_numtype_2 v_cvtop) => (v_numtype_1 <> v_numtype_2)
		| (AI_VSWIZZLE v_ishape) => (v_ishape = (IX JNN_I8 (mk_dim 16)))
		| (AI_VSHUFFLE v_ishape v_laneidx) => ((v_ishape = (IX JNN_I8 (mk_dim 16))) /\ ((List.length v_laneidx) = 16))
		| (AI_VEXTRACT_LANE v_shape v_sx v_laneidx) => forall (v_numtype : numtype), (((fun_lanetype v_shape) = (v_numtype : lanetype)) <-> (v_sx = None))
		| (AI_VEXTUNOP v_ishape_1 v_ishape_2 v_vextunop_) => ((fun_lsize (fun_lanetype (v_ishape_1 : shape))) = (2 * (fun_lsize (fun_lanetype (v_ishape_2 : shape)))))
		| (AI_VEXTBINOP v_ishape_1 v_ishape_2 v_vextbinop_) => ((fun_lsize (fun_lanetype (v_ishape_1 : shape))) = (2 * (fun_lsize (fun_lanetype (v_ishape_2 : shape)))))
		| (AI_VNARROW v_ishape_1 v_ishape_2 v_sx) => (((fun_lsize (fun_lanetype (v_ishape_2 : shape))) = (2 * (fun_lsize (fun_lanetype (v_ishape_1 : shape))))) /\ ((2 * (fun_lsize (fun_lanetype (v_ishape_1 : shape)))) <= 32))
		| (AI_STORE v_numtype v_sz v_memarg) => forall (v_Inn : (option Inn)), List.Forall2 (fun (v_Inn : Inn) (v_sz : sz) => ((v_numtype = (v_Inn : numtype)) /\ ((fun_proj_sz_0 v_sz) < (fun_sizenn (v_Inn : numtype))))) (option_to_list v_Inn) (option_to_list v_sz)
		| _ => true
	end.

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62 *)
Inductive config : Type :=
	| mk_config (v_state : state) (_ : (list admininstr)) : config.

Global Instance Inhabited__config : Inhabited (config) := { default_val := mk_config default_val default_val }.

Definition config_eq_dec : forall (v1 v2 : config),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition config_eqb (v1 v2 : config) : bool :=
	is_left(config_eq_dec v1 v2).
Definition eqconfigP : Equality.axiom (config_eqb) :=
	eq_dec_Equality_axiom (config) (config_eq_dec).

HB.instance Definition _ := hasDecEq.Build (config) (eqconfigP).
Hint Resolve config_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.43 *)
Definition fun_default_ (v_valtype : valtype) : (option val) :=
	match v_valtype return (option val) with
		| (VALTYPE_I32) => (Some (VAL_CONST I32 (mk_uN _ 0)))
		| (VALTYPE_I64) => (Some (VAL_CONST I64 (mk_uN _ 0)))
		| (VALTYPE_F32) => (Some (VAL_CONST F32 (fun_fzero 32)))
		| (VALTYPE_F64) => (Some (VAL_CONST F64 (fun_fzero 64)))
		| (VALTYPE_V128) => (Some (VAL_VCONST V128 (mk_uN _ 0)))
		| (VALTYPE_FUNCREF) => (Some (VAL_REF_NULL FUNCREF))
		| (VALTYPE_EXTERNREF) => (Some (VAL_REF_NULL EXTERNREF))
		| v_x0 => None
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63 *)
(* Axiom Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63 *)
Axiom fun_funcsxa : forall (var_0 : (list externaddr)), (list funcaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65 *)
(* Axiom Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65 *)
Axiom fun_globalsxa : forall (var_0 : (list externaddr)), (list globaladdr).

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64 *)
(* Axiom Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64 *)
Axiom fun_tablesxa : forall (var_0 : (list externaddr)), (list tableaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62 *)
(* Axiom Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62 *)
Axiom fun_memsxa : forall (var_0 : (list externaddr)), (list memaddr).

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57 *)
Definition fun_store (v_state : state) : store :=
	match v_state return store with
		| (mk_state v_s v_f) => v_s
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 *)
Definition fun_frame (v_state : state) : frame :=
	match v_state return frame with
		| (mk_state v_s v_f) => v_f
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64 *)
Definition fun_funcaddr (v_state : state) : (list funcaddr) :=
	match v_state return (list funcaddr) with
		| (mk_state v_s v_f) => (MODULE_FUNCS (F_MODULE v_f))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57 *)
Definition fun_funcinst (v_state : state) : (list funcinst) :=
	match v_state return (list funcinst) with
		| (mk_state v_s v_f) => (FUNCS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 *)
Definition fun_globalinst (v_state : state) : (list globalinst) :=
	match v_state return (list globalinst) with
		| (mk_state v_s v_f) => (GLOBALS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 *)
Definition fun_tableinst (v_state : state) : (list tableinst) :=
	match v_state return (list tableinst) with
		| (mk_state v_s v_f) => (TABLES v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 *)
Definition fun_meminst (v_state : state) : (list meminst) :=
	match v_state return (list meminst) with
		| (mk_state v_s v_f) => (MEMS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57 *)
Definition fun_eleminst (v_state : state) : (list eleminst) :=
	match v_state return (list eleminst) with
		| (mk_state v_s v_f) => (ELEMS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57 *)
Definition fun_datainst (v_state : state) : (list datainst) :=
	match v_state return (list datainst) with
		| (mk_state v_s v_f) => (DATAS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 *)
Definition fun_moduleinst (v_state : state) : moduleinst :=
	match v_state return moduleinst with
		| (mk_state v_s v_f) => (F_MODULE v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66 *)
Definition fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
	match v_state, v_typeidx return functype with
		| (mk_state v_s v_f), v_x => (lookup_total (MODULE_TYPES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66 *)
Definition fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
	match v_state, v_funcidx return funcinst with
		| (mk_state v_s v_f), v_x => (lookup_total (FUNCS v_s) (lookup_total (MODULE_FUNCS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 *)
Definition fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
	match v_state, v_globalidx return globalinst with
		| (mk_state v_s v_f), v_x => (lookup_total (GLOBALS v_s) (lookup_total (MODULE_GLOBALS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 *)
Definition fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
	match v_state, v_tableidx return tableinst with
		| (mk_state v_s v_f), v_x => (lookup_total (TABLES v_s) (lookup_total (MODULE_TABLES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 *)
Definition fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
	match v_state, v_memidx return meminst with
		| (mk_state v_s v_f), v_x => (lookup_total (MEMS v_s) (lookup_total (MODULE_MEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66 *)
Definition fun_elem (v_state : state) (v_tableidx : tableidx) : eleminst :=
	match v_state, v_tableidx return eleminst with
		| (mk_state v_s v_f), v_x => (lookup_total (ELEMS v_s) (lookup_total (MODULE_ELEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66 *)
Definition fun_data (v_state : state) (v_dataidx : dataidx) : datainst :=
	match v_state, v_dataidx return datainst with
		| (mk_state v_s v_f), v_x => (lookup_total (DATAS v_s) (lookup_total (MODULE_DATAS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 *)
Definition fun_local (v_state : state) (v_localidx : localidx) : val :=
	match v_state, v_localidx return val with
		| (mk_state v_s v_f), v_x => (lookup_total (F_LOCALS v_f) (fun_proj_uN_0 32 v_x))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 *)
Definition fun_with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
	match v_state, v_localidx, v_val return state with
		| (mk_state v_s v_f), v_x, v_v => (mk_state v_s (v_f <| F_LOCALS := (list_update_func (F_LOCALS v_f) (fun_proj_uN_0 32 v_x) (fun (_ : val) => v_v)) |>))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 *)
Definition fun_with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
	match v_state, v_globalidx, v_val return state with
		| (mk_state v_s v_f), v_x, v_v => (mk_state (v_s <| GLOBALS := (list_update_func (GLOBALS v_s) (lookup_total (MODULE_GLOBALS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : globalinst) => (v_1 <| GLOB_VALUE := v_v |>))) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 *)
Definition fun_with_table (v_state : state) (v_tableidx : tableidx) (v_nat : nat) (v_ref : ref) : state :=
	match v_state, v_tableidx, v_nat, v_ref return state with
		| (mk_state v_s v_f), v_x, v_i, v_r => (mk_state (v_s <| TABLES := (list_update_func (TABLES v_s) (lookup_total (MODULE_TABLES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : tableinst) => (v_1 <| TAB_REFS := (list_update_func (TAB_REFS v_1) v_i (fun (_ : ref) => v_r)) |>))) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 *)
Definition fun_with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
	match v_state, v_tableidx, v_tableinst return state with
		| (mk_state v_s v_f), v_x, v_ti => (mk_state (v_s <| TABLES := (list_update_func (TABLES v_s) (lookup_total (MODULE_TABLES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (_ : tableinst) => v_ti)) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 *)
Definition fun_with_mem (v_state : state) (v_memidx : memidx) (v_nat : nat) (v_nat_0 : nat) (var_0 : (list byte)) : state :=
	match v_state, v_memidx, v_nat, v_nat_0, var_0 return state with
		| (mk_state v_s v_f), v_x, v_i, v_j, v_b => (mk_state (v_s <| MEMS := (list_update_func (MEMS v_s) (lookup_total (MODULE_MEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : meminst) => (v_1 <| MEM_BYTES := (list_slice_update (MEM_BYTES v_1) v_i v_j v_b) |>))) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 *)
Definition fun_with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
	match v_state, v_memidx, v_meminst return state with
		| (mk_state v_s v_f), v_x, v_mi => (mk_state (v_s <| MEMS := (list_update_func (MEMS v_s) (lookup_total (MODULE_MEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (_ : meminst) => v_mi)) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 *)
Definition fun_with_elem (v_state : state) (v_elemidx : elemidx) (var_0 : (list ref)) : state :=
	match v_state, v_elemidx, var_0 return state with
		| (mk_state v_s v_f), v_x, v_r => (mk_state (v_s <| ELEMS := (list_update_func (ELEMS v_s) (lookup_total (MODULE_ELEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : eleminst) => (v_1 <| ELEM_REFS := v_r |>))) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 *)
Definition fun_with_data (v_state : state) (v_dataidx : dataidx) (var_0 : (list byte)) : state :=
	match v_state, v_dataidx, var_0 return state with
		| (mk_state v_s v_f), v_x, v_b => (mk_state (v_s <| DATAS := (list_update_func (DATAS v_s) (lookup_total (MODULE_DATAS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : datainst) => (v_1 <| DATA_BYTES := v_b |>))) |>) v_f)
	end.

(* Axiom Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.1-116.62 *)
Axiom fun_growtable : forall (v_tableinst : tableinst) (v_nat : nat) (v_ref : ref), (option tableinst).

(* Axiom Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.1-117.62 *)
Axiom fun_growmemory : forall (v_meminst : meminst) (v_nat : nat), (option meminst).

(* Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 *)
Record context := MKcontext
{	C_TYPES : (list functype)
;	C_FUNCS : (list functype)
;	C_GLOBALS : (list globaltype)
;	C_TABLES : (list tabletype)
;	C_MEMS : (list memtype)
;	C_ELEMS : (list elemtype)
;	C_DATAS : (list datatype)
;	C_LOCALS : (list valtype)
;	C_LABELS : (list resulttype)
;	C_RETURN : (option resulttype)
}.

Global Instance Inhabited_context : Inhabited context := 
{default_val := {|
	C_TYPES := default_val;
	C_FUNCS := default_val;
	C_GLOBALS := default_val;
	C_TABLES := default_val;
	C_MEMS := default_val;
	C_ELEMS := default_val;
	C_DATAS := default_val;
	C_LOCALS := default_val;
	C_LABELS := default_val;
	C_RETURN := default_val|} }.

Definition _append_context (arg1 arg2 : context) :=
{|
	C_TYPES := arg1.(C_TYPES) @@ arg2.(C_TYPES);
	C_FUNCS := arg1.(C_FUNCS) @@ arg2.(C_FUNCS);
	C_GLOBALS := arg1.(C_GLOBALS) @@ arg2.(C_GLOBALS);
	C_TABLES := arg1.(C_TABLES) @@ arg2.(C_TABLES);
	C_MEMS := arg1.(C_MEMS) @@ arg2.(C_MEMS);
	C_ELEMS := arg1.(C_ELEMS) @@ arg2.(C_ELEMS);
	C_DATAS := arg1.(C_DATAS) @@ arg2.(C_DATAS);
	C_LOCALS := arg1.(C_LOCALS) @@ arg2.(C_LOCALS);
	C_LABELS := arg1.(C_LABELS) @@ arg2.(C_LABELS);
	C_RETURN := arg1.(C_RETURN) @@ arg2.(C_RETURN);
|}.

Global Instance Append_context : Append context := { _append arg1 arg2 := _append_context arg1 arg2 }.

#[export] Instance eta__context : Settable _ := settable! MKcontext <C_TYPES;C_FUNCS;C_GLOBALS;C_TABLES;C_MEMS;C_ELEMS;C_DATAS;C_LOCALS;C_LABELS;C_RETURN>.

Definition context_eq_dec : forall (v1 v2 : context),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition context_eqb (v1 v2 : context) : bool :=
	is_left(context_eq_dec v1 v2).
Definition eqcontextP : Equality.axiom (context_eqb) :=
	eq_dec_Equality_axiom (context) (context_eq_dec).

HB.instance Definition _ := hasDecEq.Build (context) (eqcontextP).
Hint Resolve context_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 *)
Inductive Limits_ok: limits -> nat -> Prop :=
	| mk_Limits_ok : forall (v_n : n) (v_m : m) (v_k : nat), 
		((v_n <= v_m) /\ (v_m <= v_k)) ->
		Limits_ok (mk_limits (mk_uN _ v_n) (mk_uN _ v_m)) v_k.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 *)
Inductive Functype_ok: functype -> Prop :=
	| mk_Functype_ok : forall (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Functype_ok (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 *)
Inductive Globaltype_ok: globaltype -> Prop :=
	| mk_Globaltype_ok : forall (v_t : valtype), Globaltype_ok (mk_globaltype (Some MUT) v_t).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 *)
Inductive Tabletype_ok: tabletype -> Prop :=
	| mk_Tabletype_ok : forall (v_limits : limits) (v_reftype : reftype), 
		(Limits_ok v_limits ((((2 ^ 32) : nat) - (1 : nat)) : nat)) ->
		Tabletype_ok (mk_tabletype v_limits v_reftype).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 *)
Inductive Memtype_ok: memtype -> Prop :=
	| mk_Memtype_ok : forall (v_limits : limits), 
		(Limits_ok v_limits (2 ^ 16)) ->
		Memtype_ok (PAGE v_limits).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.89 *)
Inductive Externtype_ok: externtype -> Prop :=
	| ext_ok_func : forall (v_functype : functype), 
		(Functype_ok v_functype) ->
		Externtype_ok (EXT_FUNC v_functype)
	| ext_ok_global : forall (v_globaltype : globaltype), 
		(Globaltype_ok v_globaltype) ->
		Externtype_ok (EXT_GLOBAL v_globaltype)
	| ext_ok_table : forall (v_tabletype : tabletype), 
		(Tabletype_ok v_tabletype) ->
		Externtype_ok (EXT_TABLE v_tabletype)
	| ext_ok_mem : forall (v_memtype : memtype), 
		(Memtype_ok v_memtype) ->
		Externtype_ok (EXT_MEM v_memtype).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:70.1-70.69 *)
Inductive Valtype_sub: valtype -> valtype -> Prop :=
	| refl : forall (v_t : valtype), Valtype_sub v_t v_t
	| bot : forall (v_t : valtype), Valtype_sub VALTYPE_BOT v_t.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.76 *)
Inductive Resulttype_sub: resulttype -> resulttype -> Prop :=
	| mk_Resulttype_sub : forall (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		((List.length v_t_1) = (List.length v_t_2)) ->
		List.Forall2 (fun (v_t_1 : valtype) (v_t_2 : valtype) => (Valtype_sub v_t_1 v_t_2)) (v_t_1) (v_t_2) ->
		Resulttype_sub (mk_list _ v_t_1) (mk_list _ v_t_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:86.1-86.75 *)
Inductive Limits_sub: limits -> limits -> Prop :=
	| mk_Limits_sub : forall (v_n_11 : n) (v_n_12 : n) (v_n_21 : n) (v_n_22 : n), 
		(v_n_11 >= v_n_21) ->
		(v_n_12 <= v_n_22) ->
		Limits_sub (mk_limits (mk_uN _ v_n_11) (mk_uN _ v_n_12)) (mk_limits (mk_uN _ v_n_21) (mk_uN _ v_n_22)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:87.1-87.73 *)
Inductive Functype_sub: functype -> functype -> Prop :=
	| mk_Functype_sub : forall (v_ft : functype), Functype_sub v_ft v_ft.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:88.1-88.75 *)
Inductive Globaltype_sub: globaltype -> globaltype -> Prop :=
	| mk_Globaltype_sub : forall (v_gt : globaltype), Globaltype_sub v_gt v_gt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:89.1-89.74 *)
Inductive Tabletype_sub: tabletype -> tabletype -> Prop :=
	| mk_Tabletype_sub : forall (v_lim_1 : limits) (v_rt : reftype) (v_lim_2 : limits), 
		(Limits_sub v_lim_1 v_lim_2) ->
		Tabletype_sub (mk_tabletype v_lim_1 v_rt) (mk_tabletype v_lim_2 v_rt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:90.1-90.72 *)
Inductive Memtype_sub: memtype -> memtype -> Prop :=
	| mk_Memtype_sub : forall (v_lim_1 : limits) (v_lim_2 : limits), 
		(Limits_sub v_lim_1 v_lim_2) ->
		Memtype_sub (PAGE v_lim_1) (PAGE v_lim_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.99 *)
Inductive Externtype_sub: externtype -> externtype -> Prop :=
	| ext_sub_func : forall (v_ft_1 : functype) (v_ft_2 : functype), 
		(Functype_sub v_ft_1 v_ft_2) ->
		Externtype_sub (EXT_FUNC v_ft_1) (EXT_FUNC v_ft_2)
	| ext_sub_global : forall (v_gt_1 : globaltype) (v_gt_2 : globaltype), 
		(Globaltype_sub v_gt_1 v_gt_2) ->
		Externtype_sub (EXT_GLOBAL v_gt_1) (EXT_GLOBAL v_gt_2)
	| ext_sub_table : forall (v_tt_1 : tabletype) (v_tt_2 : tabletype), 
		(Tabletype_sub v_tt_1 v_tt_2) ->
		Externtype_sub (EXT_TABLE v_tt_1) (EXT_TABLE v_tt_2)
	| ext_sub_mem : forall (v_mt_1 : memtype) (v_mt_2 : memtype), 
		(Memtype_sub v_mt_1 v_mt_2) ->
		Externtype_sub (EXT_MEM v_mt_1) (EXT_MEM v_mt_2).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:193.1-193.101 *)
Inductive Blocktype_ok: context -> blocktype -> functype -> Prop :=
	| block_ok_valtype : forall (v_C : context) (v_valtype : (option valtype)), Blocktype_ok v_C (_RESULT v_valtype) (mk_functype (mk_list _ []) (mk_list _ (option_to_list v_valtype)))
	| block_ok_typeidx : forall (v_C : context) (v_typeidx : typeidx) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		((fun_proj_uN_0 32 v_typeidx) < (List.length (C_TYPES v_C))) ->
		((lookup_total (C_TYPES v_C) (fun_proj_uN_0 32 v_typeidx)) = (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Blocktype_ok v_C (_IDX v_typeidx) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2)).

(* Auxiliary Definition at: ../specification/wasm-2.0/6-typing.spectec:136.1-136.89 *)
Definition fun_coec_reftype__valtype (v_reftype : reftype) : valtype :=
	match v_reftype return valtype with
		| (FUNCREF) => VALTYPE_FUNCREF
		| (EXTERNREF) => VALTYPE_EXTERNREF
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/6-typing.spectec:136.1-136.89 *)
Coercion fun_coec_reftype__valtype : reftype >-> valtype.

(* Mutual Recursion at: ../specification/wasm-2.0/6-typing.spectec:136.1-137.91 *)
(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:136.1-136.89 *)
Inductive Instr_ok: context -> instr -> functype -> Prop :=
	| instr_ok_nop : forall (v_C : context), Instr_ok v_C instr_NOP (mk_functype (mk_list _ []) (mk_list _ []))
	| instr_ok_unreachable : forall (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Instr_ok v_C instr_UNREACHABLE (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))
	| instr_ok_drop : forall (v_C : context) (v_t : valtype), Instr_ok v_C instr_DROP (mk_functype (mk_list _ [v_t]) (mk_list _ []))
	| instr_ok_select_expl : forall (v_C : context) (v_t : valtype), Instr_ok v_C (instr_SELECT (Some [v_t])) (mk_functype (mk_list _ [v_t; v_t; VALTYPE_I32]) (mk_list _ [v_t]))
	| instr_ok_select_impl : forall (v_C : context) (v_t : valtype) (v_t' : valtype) (v_numtype : numtype) (v_vectype : vectype), 
		(Valtype_sub v_t v_t') ->
		((v_t' = (v_numtype : valtype)) \/ (v_t' = (v_vectype : valtype))) ->
		Instr_ok v_C (instr_SELECT None) (mk_functype (mk_list _ [v_t; v_t; VALTYPE_I32]) (mk_list _ [v_t]))
	| instr_ok_block : forall (v_C : context) (v_bt : blocktype) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Blocktype_ok v_C v_bt (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := [(mk_list _ v_t_2)]; C_RETURN := None |} @@ v_C) v_instr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Instr_ok v_C (instr_BLOCK v_bt v_instr) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))
	| instr_ok_loop : forall (v_C : context) (v_bt : blocktype) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Blocktype_ok v_C v_bt (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := [(mk_list _ v_t_1)]; C_RETURN := None |} @@ v_C) v_instr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Instr_ok v_C (instr_LOOP v_bt v_instr) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))
	| instr_ok_res_if : forall (v_C : context) (v_bt : blocktype) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Blocktype_ok v_C v_bt (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := [(mk_list _ v_t_2)]; C_RETURN := None |} @@ v_C) v_instr_1 (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := [(mk_list _ v_t_2)]; C_RETURN := None |} @@ v_C) v_instr_2 (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Instr_ok v_C (instr_IFELSE v_bt v_instr_1 v_instr_2) (mk_functype (mk_list _ (v_t_1 ++ [VALTYPE_I32])) (mk_list _ v_t_2))
	| instr_ok_br : forall (v_C : context) (v_l : labelidx) (v_t_1 : (list valtype)) (v_t : (list valtype)) (v_t_2 : (list valtype)), 
		((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C))) ->
		((fun_proj_list_0 valtype (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l))) = v_t) ->
		Instr_ok v_C (instr_BR v_l) (mk_functype (mk_list _ (v_t_1 ++ v_t)) (mk_list _ v_t_2))
	| instr_ok_br_if : forall (v_C : context) (v_l : labelidx) (v_t : (list valtype)), 
		((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C))) ->
		((fun_proj_list_0 valtype (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l))) = v_t) ->
		Instr_ok v_C (instr_BR_IF v_l) (mk_functype (mk_list _ (v_t ++ [VALTYPE_I32])) (mk_list _ v_t))
	| instr_ok_br_table : forall (v_C : context) (v_l : (list labelidx)) (v_l' : labelidx) (v_t_1 : (list valtype)) (v_t : (list valtype)) (v_t_2 : (list valtype)), 
		List.Forall (fun (v_l : labelidx) => ((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C)))) (v_l) ->
		List.Forall (fun (v_l : labelidx) => (Resulttype_sub (mk_list _ v_t) (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l)))) (v_l) ->
		((fun_proj_uN_0 32 v_l') < (List.length (C_LABELS v_C))) ->
		(Resulttype_sub (mk_list _ v_t) (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l'))) ->
		Instr_ok v_C (instr_BR_TABLE v_l v_l') (mk_functype (mk_list _ (v_t_1 ++ (v_t ++ [VALTYPE_I32]))) (mk_list _ v_t_2))
	| instr_ok_call : forall (v_C : context) (v_x : idx) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) ->
		((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Instr_ok v_C (instr_CALL v_x) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))
	| instr_ok_call_indirect : forall (v_C : context) (v_x : idx) (v_y : idx) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)) (v_lim : limits), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim FUNCREF)) ->
		((fun_proj_uN_0 32 v_y) < (List.length (C_TYPES v_C))) ->
		((lookup_total (C_TYPES v_C) (fun_proj_uN_0 32 v_y)) = (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Instr_ok v_C (instr_CALL_INDIRECT v_x v_y) (mk_functype (mk_list _ (v_t_1 ++ [VALTYPE_I32])) (mk_list _ v_t_2))
	| instr_ok_res_return : forall (v_C : context) (v_t_1 : (list valtype)) (v_t : (list valtype)) (v_t_2 : (list valtype)), 
		((C_RETURN v_C) = (Some (mk_list _ v_t))) ->
		Instr_ok v_C instr_RETURN (mk_functype (mk_list _ (v_t_1 ++ v_t)) (mk_list _ v_t_2))
	| instr_ok_const : forall (v_C : context) (v_nt : numtype) (v_c_nt : (num_ v_nt)), Instr_ok v_C (instr_CONST v_nt v_c_nt) (mk_functype (mk_list _ []) (mk_list _ [(v_nt : valtype)]))
	| instr_ok_unop : forall (v_C : context) (v_nt : numtype) (v_unop_nt : (unop_ v_nt)), Instr_ok v_C (instr_UNOP v_nt v_unop_nt) (mk_functype (mk_list _ [(v_nt : valtype)]) (mk_list _ [(v_nt : valtype)]))
	| instr_ok_binop : forall (v_C : context) (v_nt : numtype) (v_binop_nt : (binop_ v_nt)), Instr_ok v_C (instr_BINOP v_nt v_binop_nt) (mk_functype (mk_list _ [(v_nt : valtype); (v_nt : valtype)]) (mk_list _ [(v_nt : valtype)]))
	| instr_ok_testop : forall (v_C : context) (v_nt : numtype) (v_testop_nt : (testop_ v_nt)), Instr_ok v_C (instr_TESTOP v_nt v_testop_nt) (mk_functype (mk_list _ [(v_nt : valtype)]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_relop : forall (v_C : context) (v_nt : numtype) (v_relop_nt : (relop_ v_nt)), Instr_ok v_C (instr_RELOP v_nt v_relop_nt) (mk_functype (mk_list _ [(v_nt : valtype); (v_nt : valtype)]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_cvtop : forall (v_C : context) (v_nt_1 : numtype) (v_nt_2 : numtype) (v_cvtop : cvtop), Instr_ok v_C (instr_CVTOP v_nt_1 v_nt_2 v_cvtop) (mk_functype (mk_list _ [(v_nt_2 : valtype)]) (mk_list _ [(v_nt_1 : valtype)]))
	| instr_ok_ref_null : forall (v_C : context) (v_rt : reftype), Instr_ok v_C (instr_REF_NULL v_rt) (mk_functype (mk_list _ []) (mk_list _ [(v_rt : valtype)]))
	| instr_ok_ref_func : forall (v_C : context) (v_x : idx) (v_ft : functype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) ->
		((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = v_ft) ->
		Instr_ok v_C (instr_REF_FUNC v_x) (mk_functype (mk_list _ []) (mk_list _ [VALTYPE_FUNCREF]))
	| instr_ok_ref_is_null : forall (v_C : context) (v_rt : reftype), Instr_ok v_C instr_REF_IS_NULL (mk_functype (mk_list _ [(v_rt : valtype)]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_vconst : forall (v_C : context) (v_c : (vec_ V128)), Instr_ok v_C (instr_VCONST V128 v_c) (mk_functype (mk_list _ []) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vvunop : forall (v_C : context) (v_vvunop : vvunop), Instr_ok v_C (instr_VVUNOP V128 v_vvunop) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vvbinop : forall (v_C : context) (v_vvbinop : vvbinop), Instr_ok v_C (instr_VVBINOP V128 v_vvbinop) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vvternop : forall (v_C : context) (v_vvternop : vvternop), Instr_ok v_C (instr_VVTERNOP V128 v_vvternop) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vvtestop : forall (v_C : context) (v_vvtestop : vvtestop), Instr_ok v_C (instr_VVTESTOP V128 v_vvtestop) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_vunop : forall (v_C : context) (v_sh : shape) (v_vunop_sh : (vunop_ v_sh)), Instr_ok v_C (instr_VUNOP v_sh v_vunop_sh) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vbinop : forall (v_C : context) (v_sh : shape) (v_vbinop_sh : (vbinop_ v_sh)), Instr_ok v_C (instr_VBINOP v_sh v_vbinop_sh) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vtestop : forall (v_C : context) (v_sh : shape) (v_vtestop_sh : (vtestop_ v_sh)), Instr_ok v_C (instr_VTESTOP v_sh v_vtestop_sh) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_vrelop : forall (v_C : context) (v_sh : shape) (v_vrelop_sh : (vrelop_ v_sh)), Instr_ok v_C (instr_VRELOP v_sh v_vrelop_sh) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vshiftop : forall (v_C : context) (v_sh : ishape) (v_vshiftop_sh : (vshiftop_ v_sh)), Instr_ok v_C (instr_VSHIFTOP v_sh v_vshiftop_sh) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_I32]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vbitmask : forall (v_C : context) (v_sh : ishape), Instr_ok v_C (instr_VBITMASK v_sh) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_vswizzle : forall (v_C : context) (v_sh : ishape), Instr_ok v_C (instr_VSWIZZLE v_sh) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vshuffle : forall (v_C : context) (v_sh : ishape) (v_i : (list laneidx)), 
		List.Forall (fun (v_i : laneidx) => ((fun_proj_uN_0 8 v_i) < (2 * (fun_proj_dim_0 (fun_dim (v_sh : shape)))))) (v_i) ->
		Instr_ok v_C (instr_VSHUFFLE v_sh v_i) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vsplat : forall (v_C : context) (v_sh : shape), Instr_ok v_C (instr_VSPLAT v_sh) (mk_functype (mk_list _ [((fun_shunpack v_sh) : valtype)]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vextract_lane : forall (v_C : context) (v_sh : shape) (v_sx : (option sx)) (v_i : laneidx), 
		((fun_proj_uN_0 8 v_i) < (fun_proj_dim_0 (fun_dim v_sh))) ->
		Instr_ok v_C (instr_VEXTRACT_LANE v_sh v_sx v_i) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [((fun_shunpack v_sh) : valtype)]))
	| instr_ok_vreplace_lane : forall (v_C : context) (v_sh : shape) (v_i : laneidx), 
		((fun_proj_uN_0 8 v_i) < (fun_proj_dim_0 (fun_dim v_sh))) ->
		Instr_ok v_C (instr_VREPLACE_LANE v_sh v_i) (mk_functype (mk_list _ [VALTYPE_V128; ((fun_shunpack v_sh) : valtype)]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vextunop : forall (v_C : context) (v_sh_1 : ishape) (v_sh_2 : ishape) (v_vextunop : (vextunop_ v_sh_1)), Instr_ok v_C (instr_VEXTUNOP v_sh_1 v_sh_2 v_vextunop) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vextbinop : forall (v_C : context) (v_sh_1 : ishape) (v_sh_2 : ishape) (v_vextbinop : (vextbinop_ v_sh_1)), Instr_ok v_C (instr_VEXTBINOP v_sh_1 v_sh_2 v_vextbinop) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vnarrow : forall (v_C : context) (v_sh_1 : ishape) (v_sh_2 : ishape) (v_sx : sx), Instr_ok v_C (instr_VNARROW v_sh_1 v_sh_2 v_sx) (mk_functype (mk_list _ [VALTYPE_V128; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vcvtop : forall (v_C : context) (v_sh_1 : shape) (v_sh_2 : shape) (v_vcvtop : vcvtop), Instr_ok v_C (instr_VCVTOP v_sh_1 v_sh_2 v_vcvtop) (mk_functype (mk_list _ [VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_local_get : forall (v_C : context) (v_x : idx) (v_t : valtype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) ->
		((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t) ->
		Instr_ok v_C (instr_LOCAL_GET v_x) (mk_functype (mk_list _ []) (mk_list _ [v_t]))
	| instr_ok_local_set : forall (v_C : context) (v_x : idx) (v_t : valtype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) ->
		((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t) ->
		Instr_ok v_C (instr_LOCAL_SET v_x) (mk_functype (mk_list _ [v_t]) (mk_list _ []))
	| instr_ok_local_tee : forall (v_C : context) (v_x : idx) (v_t : valtype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) ->
		((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t) ->
		Instr_ok v_C (instr_LOCAL_TEE v_x) (mk_functype (mk_list _ [v_t]) (mk_list _ [v_t]))
	| instr_ok_global_get : forall (v_C : context) (v_x : idx) (v_t : valtype) (v_mut : mut), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) ->
		((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype v_mut v_t)) ->
		Instr_ok v_C (instr_GLOBAL_GET v_x) (mk_functype (mk_list _ []) (mk_list _ [v_t]))
	| instr_ok_global_set : forall (v_C : context) (v_x : idx) (v_t : valtype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) ->
		((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype (Some MUT) v_t)) ->
		Instr_ok v_C (instr_GLOBAL_SET v_x) (mk_functype (mk_list _ [v_t]) (mk_list _ []))
	| instr_ok_table_get : forall (v_C : context) (v_x : idx) (v_rt : reftype) (v_lim : limits), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt)) ->
		Instr_ok v_C (instr_TABLE_GET v_x) (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [(v_rt : valtype)]))
	| instr_ok_table_set : forall (v_C : context) (v_x : idx) (v_rt : reftype) (v_lim : limits), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt)) ->
		Instr_ok v_C (instr_TABLE_SET v_x) (mk_functype (mk_list _ [VALTYPE_I32; (v_rt : valtype)]) (mk_list _ []))
	| instr_ok_table_size : forall (v_C : context) (v_x : idx) (v_lim : limits) (v_rt : reftype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt)) ->
		Instr_ok v_C (instr_TABLE_SIZE v_x) (mk_functype (mk_list _ []) (mk_list _ [VALTYPE_I32]))
	| instr_ok_table_grow : forall (v_C : context) (v_x : idx) (v_rt : reftype) (v_lim : limits), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt)) ->
		Instr_ok v_C (instr_TABLE_GROW v_x) (mk_functype (mk_list _ [(v_rt : valtype); VALTYPE_I32]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_table_fill : forall (v_C : context) (v_x : idx) (v_rt : reftype) (v_lim : limits), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt)) ->
		Instr_ok v_C (instr_TABLE_FILL v_x) (mk_functype (mk_list _ [VALTYPE_I32; (v_rt : valtype); VALTYPE_I32]) (mk_list _ []))
	| instr_ok_table_copy : forall (v_C : context) (v_x_1 : idx) (v_x_2 : idx) (v_lim_1 : limits) (v_rt : reftype) (v_lim_2 : limits), 
		((fun_proj_uN_0 32 v_x_1) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x_1)) = (mk_tabletype v_lim_1 v_rt)) ->
		((fun_proj_uN_0 32 v_x_2) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x_2)) = (mk_tabletype v_lim_2 v_rt)) ->
		Instr_ok v_C (instr_TABLE_COPY v_x_1 v_x_2) (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]) (mk_list _ []))
	| instr_ok_table_init : forall (v_C : context) (v_x_1 : idx) (v_x_2 : idx) (v_lim : limits) (v_rt : reftype), 
		((fun_proj_uN_0 32 v_x_1) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x_1)) = (mk_tabletype v_lim v_rt)) ->
		((fun_proj_uN_0 32 v_x_2) < (List.length (C_ELEMS v_C))) ->
		((lookup_total (C_ELEMS v_C) (fun_proj_uN_0 32 v_x_2)) = v_rt) ->
		Instr_ok v_C (instr_TABLE_INIT v_x_1 v_x_2) (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]) (mk_list _ []))
	| instr_ok_elem_drop : forall (v_C : context) (v_x : idx) (v_rt : reftype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_ELEMS v_C))) ->
		((lookup_total (C_ELEMS v_C) (fun_proj_uN_0 32 v_x)) = v_rt) ->
		Instr_ok v_C (instr_ELEM_DROP v_x) (mk_functype (mk_list _ []) (mk_list _ []))
	| instr_ok_memory_size : forall (v_C : context) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		Instr_ok v_C instr_MEMORY_SIZE (mk_functype (mk_list _ []) (mk_list _ [VALTYPE_I32]))
	| instr_ok_memory_grow : forall (v_C : context) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		Instr_ok v_C instr_MEMORY_GROW (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [VALTYPE_I32]))
	| instr_ok_memory_fill : forall (v_C : context) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		Instr_ok v_C instr_MEMORY_FILL (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]) (mk_list _ []))
	| instr_ok_memory_copy : forall (v_C : context) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		Instr_ok v_C instr_MEMORY_COPY (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]) (mk_list _ []))
	| instr_ok_memory_init : forall (v_C : context) (v_x : idx) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		((fun_proj_uN_0 32 v_x) < (List.length (C_DATAS v_C))) ->
		((lookup_total (C_DATAS v_C) (fun_proj_uN_0 32 v_x)) = OK) ->
		Instr_ok v_C (instr_MEMORY_INIT v_x) (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]) (mk_list _ []))
	| instr_ok_data_drop : forall (v_C : context) (v_x : idx), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_DATAS v_C))) ->
		((lookup_total (C_DATAS v_C) (fun_proj_uN_0 32 v_x)) = OK) ->
		Instr_ok v_C (instr_DATA_DROP v_x) (mk_functype (mk_list _ []) (mk_list _ []))
	| instr_ok_load_val : forall (v_C : context) (v_nt : numtype) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		((fun_size (v_nt : valtype)) <> None) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((the (fun_size (v_nt : valtype))) : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_LOAD v_nt None v_memarg) (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [(v_nt : valtype)]))
	| instr_ok_load_pack_I32 : forall (v_C : context) (v_M : M) (v_sx : sx) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_LOAD (INN_I32 : numtype) (Some (op_ _ (mk_sz v_M) v_sx)) v_memarg) (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [(INN_I32 : valtype)]))
	| instr_ok_load_pack_I64 : forall (v_C : context) (v_M : M) (v_sx : sx) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_LOAD (INN_I64 : numtype) (Some (op_ _ (mk_sz v_M) v_sx)) v_memarg) (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [(INN_I64 : valtype)]))
	| instr_ok_store_val : forall (v_C : context) (v_nt : numtype) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		((fun_size (v_nt : valtype)) <> None) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((the (fun_size (v_nt : valtype))) : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_STORE v_nt None v_memarg) (mk_functype (mk_list _ [VALTYPE_I32; (v_nt : valtype)]) (mk_list _ []))
	| instr_ok_store_pack : forall (v_C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_STORE (v_Inn : numtype) (Some (mk_sz v_M)) v_memarg) (mk_functype (mk_list _ [VALTYPE_I32; (v_Inn : valtype)]) (mk_list _ []))
	| instr_ok_vload : forall (v_C : context) (v_M : M) (v_N : res_N) (v_sx : sx) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((v_M : nat) / (8 : nat)) * (v_N : nat))) ->
		Instr_ok v_C (instr_VLOAD V128 (Some (VLOAD_SHAPEX_ v_M v_N v_sx)) v_memarg) (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vload_splat : forall (v_C : context) (v_n : n) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_n : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_VLOAD V128 (Some (VLOAD_SPLAT v_n)) v_memarg) (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vload_zero : forall (v_C : context) (v_n : n) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_n : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_VLOAD V128 (Some (VLOAD_ZERO v_n)) v_memarg) (mk_functype (mk_list _ [VALTYPE_I32]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vload_lane : forall (v_C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_n : nat) / (8 : nat))) ->
		(((fun_proj_uN_0 8 v_laneidx) : nat) < ((128 : nat) / (v_n : nat))) ->
		Instr_ok v_C (instr_VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx) (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_V128]) (mk_list _ [VALTYPE_V128]))
	| instr_ok_vstore : forall (v_C : context) (v_memarg : memarg) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		((fun_size VALTYPE_V128) <> None) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((the (fun_size VALTYPE_V128)) : nat) / (8 : nat))) ->
		Instr_ok v_C (instr_VSTORE V128 v_memarg) (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_V128]) (mk_list _ []))
	| instr_ok_vstore_lane : forall (v_C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_n : nat) / (8 : nat))) ->
		(((fun_proj_uN_0 8 v_laneidx) : nat) < ((128 : nat) / (v_n : nat))) ->
		Instr_ok v_C (instr_VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx) (mk_functype (mk_list _ [VALTYPE_I32; VALTYPE_V128]) (mk_list _ []))

with

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:137.1-137.91 *)
Instrs_ok: context -> (list instr) -> functype -> Prop :=
	| instrs_ok_empty : forall (v_C : context), Instrs_ok v_C [] (mk_functype (mk_list _ []) (mk_list _ []))
	| instrs_ok_seq : forall (v_C : context) (v_instr_1 : (list instr)) (v_instr_2 : instr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), 
		(Instrs_ok v_C v_instr_1 (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Instr_ok v_C v_instr_2 (mk_functype (mk_list _ v_t_2) (mk_list _ v_t_3))) ->
		Instrs_ok v_C (v_instr_1 ++ [v_instr_2]) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_3))
	| instrs_ok_sub : forall (v_C : context) (v_instr : (list instr)) (v_t'_1 : (list valtype)) (v_t'_2 : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Instrs_ok v_C v_instr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Resulttype_sub (mk_list _ v_t'_1) (mk_list _ v_t_1)) ->
		(Resulttype_sub (mk_list _ v_t_2) (mk_list _ v_t'_2)) ->
		Instrs_ok v_C v_instr (mk_functype (mk_list _ v_t'_1) (mk_list _ v_t'_2))
	| instrs_ok_frame : forall (v_C : context) (v_instr : (list instr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Instrs_ok v_C v_instr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Instrs_ok v_C v_instr (mk_functype (mk_list _ (v_t ++ v_t_1)) (mk_list _ (v_t ++ v_t_2))).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:138.1-138.69 *)
Inductive Expr_ok: context -> expr -> resulttype -> Prop :=
	| mk_Expr_ok : forall (v_C : context) (v_instr : (list instr)) (v_t : (list valtype)), 
		(Instrs_ok v_C v_instr (mk_functype (mk_list _ []) (mk_list _ v_t))) ->
		Expr_ok v_C v_instr (mk_list _ v_t).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:517.1-517.78 *)
Inductive Instr_const: context -> instr -> Prop :=
	| const : forall (v_C : context) (v_nt : numtype) (v_c : (num_ v_nt)), Instr_const v_C (instr_CONST v_nt v_c)
	| vconst : forall (v_C : context) (v_vt : vectype) (v_vc : (vec_ v_vt)), Instr_const v_C (instr_VCONST v_vt v_vc)
	| ref_null : forall (v_C : context) (v_rt : reftype), Instr_const v_C (instr_REF_NULL v_rt)
	| ref_func : forall (v_C : context) (v_x : idx), Instr_const v_C (instr_REF_FUNC v_x)
	| global_get : forall (v_C : context) (v_x : idx) (v_t : valtype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) ->
		((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype None v_t)) ->
		Instr_const v_C (instr_GLOBAL_GET v_x).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:518.1-518.77 *)
Inductive Expr_const: context -> expr -> Prop :=
	| mk_Expr_const : forall (v_C : context) (v_instr : (list instr)), 
		List.Forall (fun (v_instr : instr) => (Instr_const v_C v_instr)) (v_instr) ->
		Expr_const v_C v_instr.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:519.1-519.78 *)
Inductive Expr_ok_const: context -> expr -> valtype -> Prop :=
	| mk_Expr_ok_const : forall (v_C : context) (v_expr : expr) (v_t : valtype), 
		(Expr_ok v_C v_expr (mk_list _ [v_t])) ->
		(Expr_const v_C v_expr) ->
		Expr_ok_const v_C v_expr v_t.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:552.1-552.73 *)
Inductive Type_ok: type -> functype -> Prop :=
	| mk_Type_ok : forall (v_ft : functype), 
		(Functype_ok v_ft) ->
		Type_ok (TYPE v_ft) v_ft.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:553.1-553.73 *)
Inductive Func_ok: context -> func -> functype -> Prop :=
	| mk_Func_ok : forall (v_C : context) (v_x : idx) (v_t : (list valtype)) (v_expr : expr) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TYPES v_C))) ->
		((lookup_total (C_TYPES v_C) (fun_proj_uN_0 32 v_x)) = (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Expr_ok (v_C @@ {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := (v_t_1 ++ v_t); C_LABELS := [(mk_list _ v_t_2)]; C_RETURN := (Some (mk_list _ v_t_2)) |}) v_expr (mk_list _ v_t_2)) ->
		Func_ok v_C (FUNC v_x (List.map (fun (v_t : valtype) => (LOCAL v_t)) v_t) v_expr) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:554.1-554.75 *)
Inductive Global_ok: context -> global -> globaltype -> Prop :=
	| mk_Global_ok : forall (v_C : context) (v_gt : globaltype) (v_expr : expr) (v_mut : mut) (v_t : valtype), 
		(Globaltype_ok v_gt) ->
		(v_gt = (mk_globaltype v_mut v_t)) ->
		(Expr_ok_const v_C v_expr v_t) ->
		Global_ok v_C (GLOBAL v_gt v_expr) v_gt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:555.1-555.74 *)
Inductive Table_ok: context -> table -> tabletype -> Prop :=
	| mk_Table_ok : forall (v_C : context) (v_tt : tabletype), 
		(Tabletype_ok v_tt) ->
		Table_ok v_C (TABLE v_tt) v_tt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:556.1-556.72 *)
Inductive Mem_ok: context -> mem -> memtype -> Prop :=
	| mk_Mem_ok : forall (v_C : context) (v_mt : memtype), 
		(Memtype_ok v_mt) ->
		Mem_ok v_C (MEMORY v_mt) v_mt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:559.1-559.77 *)
Inductive Elemmode_ok: context -> elemmode -> reftype -> Prop :=
	| active : forall (v_C : context) (v_x : idx) (v_expr : expr) (v_rt : reftype) (v_lim : limits), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = (mk_tabletype v_lim v_rt)) ->
		(Expr_ok_const v_C v_expr VALTYPE_I32) ->
		Elemmode_ok v_C (ACTIVE v_x v_expr) v_rt
	| passive : forall (v_C : context) (v_rt : reftype), Elemmode_ok v_C PASSIVE v_rt
	| declare : forall (v_C : context) (v_rt : reftype), Elemmode_ok v_C DECLARE v_rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:557.1-557.73 *)
Inductive Elem_ok: context -> elem -> reftype -> Prop :=
	| mk_Elem_ok : forall (v_C : context) (v_rt : reftype) (v_expr : (list expr)) (v_elemmode : elemmode), 
		List.Forall (fun (v_expr : expr) => (Expr_ok_const v_C v_expr (v_rt : valtype))) (v_expr) ->
		(Elemmode_ok v_C v_elemmode v_rt) ->
		Elem_ok v_C (ELEM v_rt v_expr v_elemmode) v_rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:560.1-560.105 *)
Inductive Datamode_ok: context -> datamode -> Prop :=
	| datamode_ok_active : forall (v_C : context) (v_expr : expr) (v_mt : memtype), 
		(0 < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) 0) = v_mt) ->
		(Expr_ok_const v_C v_expr VALTYPE_I32) ->
		Datamode_ok v_C (DATAM_ACTIVE (mk_uN _ 0) v_expr)
	| datamode_ok_passive : forall (v_C : context), Datamode_ok v_C DATAM_PASSIVE.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:558.1-558.73 *)
Inductive Data_ok: context -> data -> Prop :=
	| mk_Data_ok : forall (v_C : context) (v_b : (list byte)) (v_datamode : datamode), 
		(Datamode_ok v_C v_datamode) ->
		Data_ok v_C (DATA v_b v_datamode).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:561.1-561.74 *)
Inductive Start_ok: context -> start -> Prop :=
	| mk_Start_ok : forall (v_C : context) (v_x : idx), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) ->
		((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = (mk_functype (mk_list _ []) (mk_list _ []))) ->
		Start_ok v_C (START v_x).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:624.1-624.80 *)
Inductive Import_ok: context -> import -> externtype -> Prop :=
	| mk_Import_ok : forall (v_C : context) (v_name_1 : name) (v_name_2 : name) (v_xt : externtype), 
		(Externtype_ok v_xt) ->
		Import_ok v_C (IMPORT v_name_1 v_name_2 v_xt) v_xt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:626.1-626.109 *)
Inductive Externidx_ok: context -> externidx -> externtype -> Prop :=
	| extidx_ok_func : forall (v_C : context) (v_x : idx) (v_ft : functype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) ->
		((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = v_ft) ->
		Externidx_ok v_C (EXTIDX_FUNC v_x) (EXT_FUNC v_ft)
	| extidx_ok_global : forall (v_C : context) (v_x : idx) (v_gt : globaltype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) ->
		((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = v_gt) ->
		Externidx_ok v_C (EXTIDX_GLOBAL v_x) (EXT_GLOBAL v_gt)
	| extidx_ok_table : forall (v_C : context) (v_x : idx) (v_tt : tabletype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) ->
		((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = v_tt) ->
		Externidx_ok v_C (EXTIDX_TABLE v_x) (EXT_TABLE v_tt)
	| extidx_ok_mem : forall (v_C : context) (v_x : idx) (v_mt : memtype), 
		((fun_proj_uN_0 32 v_x) < (List.length (C_MEMS v_C))) ->
		((lookup_total (C_MEMS v_C) (fun_proj_uN_0 32 v_x)) = v_mt) ->
		Externidx_ok v_C (EXTIDX_MEM v_x) (EXT_MEM v_mt).

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:625.1-625.80 *)
Inductive Export_ok: context -> export -> externtype -> Prop :=
	| mk_Export_ok : forall (v_C : context) (v_name : name) (v_externidx : externidx) (v_xt : externtype), 
		(Externidx_ok v_C v_externidx v_xt) ->
		Export_ok v_C (EXPORT v_name v_externidx) v_xt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:656.1-656.62 *)
Inductive Module_ok: module -> Prop :=
	| mk_Module_ok : forall (v_type : (list type)) (v_import : (list import)) (v_func : (list func)) (v_global : (list global)) (v_table : (list table)) (v_mem : (list mem)) (v_elem : (list elem)) (v_data : (list data)) (v_n : n) (v_start : (option start)) (v_export : (list export)) (v_ft' : (list functype)) (v_ixt : (list externtype)) (v_C' : context) (v_gt : (list globaltype)) (v_tt : (list tabletype)) (v_mt : (list memtype)) (v_rt : (list reftype)) (v_C : context) (v_ft : (list functype)) (v_xt : (list externtype)) (v_ift : (list functype)) (v_igt : (list globaltype)) (v_itt : (list tabletype)) (v_imt : (list memtype)), 
		((List.length v_ft') = (List.length v_type)) ->
		List.Forall2 (fun (v_ft' : functype) (v_type : type) => (Type_ok v_type v_ft')) (v_ft') (v_type) ->
		((List.length v_import) = (List.length v_ixt)) ->
		List.Forall2 (fun (v_import : import) (v_ixt : externtype) => (Import_ok {| C_TYPES := v_ft'; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := None |} v_import v_ixt)) (v_import) (v_ixt) ->
		((List.length v_global) = (List.length v_gt)) ->
		List.Forall2 (fun (v_global : global) (v_gt : globaltype) => (Global_ok v_C' v_global v_gt)) (v_global) (v_gt) ->
		((List.length v_table) = (List.length v_tt)) ->
		List.Forall2 (fun (v_table : table) (v_tt : tabletype) => (Table_ok v_C' v_table v_tt)) (v_table) (v_tt) ->
		((List.length v_mem) = (List.length v_mt)) ->
		List.Forall2 (fun (v_mem : mem) (v_mt : memtype) => (Mem_ok v_C' v_mem v_mt)) (v_mem) (v_mt) ->
		((List.length v_elem) = (List.length v_rt)) ->
		List.Forall2 (fun (v_elem : elem) (v_rt : reftype) => (Elem_ok v_C' v_elem v_rt)) (v_elem) (v_rt) ->
		List.Forall (fun (v_data : data) => (Data_ok v_C' v_data)) (v_data) ->
		((List.length v_ft) = (List.length v_func)) ->
		List.Forall2 (fun (v_ft : functype) (v_func : func) => (Func_ok v_C v_func v_ft)) (v_ft) (v_func) ->
		List.Forall (fun (v_start : start) => (Start_ok v_C v_start)) (option_to_list v_start) ->
		((List.length v_export) = (List.length v_xt)) ->
		List.Forall2 (fun (v_export : export) (v_xt : externtype) => (Export_ok v_C v_export v_xt)) (v_export) (v_xt) ->
		((List.length v_mt) <= 1) ->
		(v_C = {| C_TYPES := v_ft'; C_FUNCS := (v_ift ++ v_ft); C_GLOBALS := (v_igt ++ v_gt); C_TABLES := (v_itt ++ v_tt); C_MEMS := (v_imt ++ v_mt); C_ELEMS := v_rt; C_DATAS := [OK]; C_LOCALS := []; C_LABELS := []; C_RETURN := None |}) ->
		(v_C' = {| C_TYPES := v_ft'; C_FUNCS := (v_ift ++ v_ft); C_GLOBALS := v_igt; C_TABLES := (v_itt ++ v_tt); C_MEMS := (v_imt ++ v_mt); C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := None |}) ->
		(v_ift = (fun_funcsxt v_ixt)) ->
		(v_igt = (fun_globalsxt v_ixt)) ->
		(v_itt = (fun_tablesxt v_ixt)) ->
		(v_imt = (fun_memsxt v_ixt)) ->
		Module_ok (MODULE v_type v_import v_func v_global v_table v_mem v_elem v_data v_start v_export).

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:232.1-234.15 *)
Definition fun_coec_ref__admininstr (v_ref : ref) : admininstr :=
	match v_ref return admininstr with
		| (REF_NULL v_0) => (AI_REF_NULL v_0)
		| (REF_FUNC_ADDR v_0) => (AI_REF_FUNC_ADDR v_0)
		| (REF_HOST_ADDR v_0) => (AI_REF_HOST_ADDR v_0)
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/8-reduction.spectec:232.1-234.15 *)
Coercion fun_coec_ref__admininstr : ref >-> admininstr.

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:232.1-234.15 *)
Inductive Step_pure_before_ref_is_null_false: (list admininstr) -> Prop :=
	| step_ref_is_null_true_0 : forall (v_ref : ref) (v_rt : reftype), 
		(v_ref = (REF_NULL v_rt)) ->
		Step_pure_before_ref_is_null_false [(v_ref : admininstr); AI_REF_IS_NULL].

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:284.1-286.15 *)
Inductive Step_pure_before_vtestop_false: (list admininstr) -> Prop :=
	| step_vtestop_true_0_I32 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 32))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 32)) => ((fun_proj_uN_0 32 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I32 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))]
	| step_vtestop_true_0_I64 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 64))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 64)) => ((fun_proj_uN_0 64 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I64 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))]
	| step_vtestop_true_0_I8 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 8))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 8)) => ((fun_proj_uN_0 8 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I8 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))]
	| step_vtestop_true_0_I16 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 16))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 16)) => ((fun_proj_uN_0 16 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I16 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))].

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.98 *)
Definition fun_coec_val__admininstr (v_val : val) : admininstr :=
	match v_val return admininstr with
		| (VAL_CONST v_0 v_1) => (AI_CONST v_0 v_1)
		| (VAL_VCONST v_0 v_1) => (AI_VCONST v_0 v_1)
		| (VAL_REF_NULL v_0) => (AI_REF_NULL v_0)
		| (VAL_REF_FUNC_ADDR v_0) => (AI_REF_FUNC_ADDR v_0)
		| (VAL_REF_HOST_ADDR v_0) => (AI_REF_HOST_ADDR v_0)
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.98 *)
Coercion fun_coec_val__admininstr : val >-> admininstr.

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.98 *)
Definition fun_coec_instr__admininstr (v_instr : instr) : admininstr :=
	match v_instr return admininstr with
		| (instr_NOP) => AI_NOP
		| (instr_UNREACHABLE) => AI_UNREACHABLE
		| (instr_DROP) => AI_DROP
		| (instr_SELECT v_0) => (AI_SELECT v_0)
		| (instr_BLOCK v_0 v_1) => (AI_BLOCK v_0 v_1)
		| (instr_LOOP v_0 v_1) => (AI_LOOP v_0 v_1)
		| (instr_IFELSE v_0 v_1 v_2) => (AI_IFELSE v_0 v_1 v_2)
		| (instr_BR v_0) => (AI_BR v_0)
		| (instr_BR_IF v_0) => (AI_BR_IF v_0)
		| (instr_BR_TABLE v_0 v_1) => (AI_BR_TABLE v_0 v_1)
		| (instr_CALL v_0) => (AI_CALL v_0)
		| (instr_CALL_INDIRECT v_0 v_1) => (AI_CALL_INDIRECT v_0 v_1)
		| (instr_RETURN) => AI_RETURN
		| (instr_CONST v_0 v_1) => (AI_CONST v_0 v_1)
		| (instr_UNOP v_0 v_1) => (AI_UNOP v_0 v_1)
		| (instr_BINOP v_0 v_1) => (AI_BINOP v_0 v_1)
		| (instr_TESTOP v_0 v_1) => (AI_TESTOP v_0 v_1)
		| (instr_RELOP v_0 v_1) => (AI_RELOP v_0 v_1)
		| (instr_CVTOP v_0 v_1 v_2) => (AI_CVTOP v_0 v_1 v_2)
		| (instr_EXTEND v_0 v_1) => (AI_EXTEND v_0 v_1)
		| (instr_VCONST v_0 v_1) => (AI_VCONST v_0 v_1)
		| (instr_VVUNOP v_0 v_1) => (AI_VVUNOP v_0 v_1)
		| (instr_VVBINOP v_0 v_1) => (AI_VVBINOP v_0 v_1)
		| (instr_VVTERNOP v_0 v_1) => (AI_VVTERNOP v_0 v_1)
		| (instr_VVTESTOP v_0 v_1) => (AI_VVTESTOP v_0 v_1)
		| (instr_VUNOP v_0 v_1) => (AI_VUNOP v_0 v_1)
		| (instr_VBINOP v_0 v_1) => (AI_VBINOP v_0 v_1)
		| (instr_VTESTOP v_0 v_1) => (AI_VTESTOP v_0 v_1)
		| (instr_VRELOP v_0 v_1) => (AI_VRELOP v_0 v_1)
		| (instr_VSHIFTOP v_0 v_1) => (AI_VSHIFTOP v_0 v_1)
		| (instr_VBITMASK v_0) => (AI_VBITMASK v_0)
		| (instr_VSWIZZLE v_0) => (AI_VSWIZZLE v_0)
		| (instr_VSHUFFLE v_0 v_1) => (AI_VSHUFFLE v_0 v_1)
		| (instr_VSPLAT v_0) => (AI_VSPLAT v_0)
		| (instr_VEXTRACT_LANE v_0 v_1 v_2) => (AI_VEXTRACT_LANE v_0 v_1 v_2)
		| (instr_VREPLACE_LANE v_0 v_1) => (AI_VREPLACE_LANE v_0 v_1)
		| (instr_VEXTUNOP v_0 v_1 v_2) => (AI_VEXTUNOP v_0 v_1 v_2)
		| (instr_VEXTBINOP v_0 v_1 v_2) => (AI_VEXTBINOP v_0 v_1 v_2)
		| (instr_VNARROW v_0 v_1 v_2) => (AI_VNARROW v_0 v_1 v_2)
		| (instr_VCVTOP v_0 v_1 v_2) => (AI_VCVTOP v_0 v_1 v_2)
		| (instr_REF_NULL v_0) => (AI_REF_NULL v_0)
		| (instr_REF_FUNC v_0) => (AI_REF_FUNC v_0)
		| (instr_REF_IS_NULL) => AI_REF_IS_NULL
		| (instr_LOCAL_GET v_0) => (AI_LOCAL_GET v_0)
		| (instr_LOCAL_SET v_0) => (AI_LOCAL_SET v_0)
		| (instr_LOCAL_TEE v_0) => (AI_LOCAL_TEE v_0)
		| (instr_GLOBAL_GET v_0) => (AI_GLOBAL_GET v_0)
		| (instr_GLOBAL_SET v_0) => (AI_GLOBAL_SET v_0)
		| (instr_TABLE_GET v_0) => (AI_TABLE_GET v_0)
		| (instr_TABLE_SET v_0) => (AI_TABLE_SET v_0)
		| (instr_TABLE_SIZE v_0) => (AI_TABLE_SIZE v_0)
		| (instr_TABLE_GROW v_0) => (AI_TABLE_GROW v_0)
		| (instr_TABLE_FILL v_0) => (AI_TABLE_FILL v_0)
		| (instr_TABLE_COPY v_0 v_1) => (AI_TABLE_COPY v_0 v_1)
		| (instr_TABLE_INIT v_0 v_1) => (AI_TABLE_INIT v_0 v_1)
		| (instr_ELEM_DROP v_0) => (AI_ELEM_DROP v_0)
		| (instr_LOAD v_0 v_1 v_2) => (AI_LOAD v_0 v_1 v_2)
		| (instr_STORE v_0 v_1 v_2) => (AI_STORE v_0 v_1 v_2)
		| (instr_VLOAD v_0 v_1 v_2) => (AI_VLOAD v_0 v_1 v_2)
		| (instr_VLOAD_LANE v_0 v_1 v_2 v_3) => (AI_VLOAD_LANE v_0 v_1 v_2 v_3)
		| (instr_VSTORE v_0 v_1) => (AI_VSTORE v_0 v_1)
		| (instr_VSTORE_LANE v_0 v_1 v_2 v_3) => (AI_VSTORE_LANE v_0 v_1 v_2 v_3)
		| (instr_MEMORY_SIZE) => AI_MEMORY_SIZE
		| (instr_MEMORY_GROW) => AI_MEMORY_GROW
		| (instr_MEMORY_FILL) => AI_MEMORY_FILL
		| (instr_MEMORY_COPY) => AI_MEMORY_COPY
		| (instr_MEMORY_INIT v_0) => (AI_MEMORY_INIT v_0)
		| (instr_DATA_DROP v_0) => (AI_DATA_DROP v_0)
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.98 *)
Coercion fun_coec_instr__admininstr : instr >-> admininstr.

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.98 *)
Definition fun_coec_packtype__Jnn (v_packtype : packtype) : Jnn :=
	match v_packtype return Jnn with
		| (I8) => JNN_I8
		| (I16) => JNN_I16
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.98 *)
Coercion fun_coec_packtype__Jnn : packtype >-> Jnn.

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.98 *)
Inductive Step_pure: (list admininstr) -> (list admininstr) -> Prop :=
	| step_unreachable : Step_pure [AI_UNREACHABLE] [AI_TRAP]
	| step_nop : Step_pure [AI_NOP] []
	| step_drop : forall (v_val : val), Step_pure [(v_val : admininstr); AI_DROP] []
	| step_select_true : forall (v_val_1 : val) (v_val_2 : val) (v_c : (uN 32)) (v_t : (option (list valtype))), 
		((fun_proj_uN_0 32 v_c) <> 0) ->
		Step_pure [(v_val_1 : admininstr); (v_val_2 : admininstr); (AI_CONST I32 v_c); (AI_SELECT v_t)] [(v_val_1 : admininstr)]
	| step_select_false : forall (v_val_1 : val) (v_val_2 : val) (v_c : (uN 32)) (v_t : (option (list valtype))), 
		((fun_proj_uN_0 32 v_c) = 0) ->
		Step_pure [(v_val_1 : admininstr); (v_val_2 : admininstr); (AI_CONST I32 v_c); (AI_SELECT v_t)] [(v_val_2 : admininstr)]
	| step_if_true : forall (v_c : (uN 32)) (v_bt : blocktype) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), 
		((fun_proj_uN_0 32 v_c) <> 0) ->
		Step_pure [(AI_CONST I32 v_c); (AI_IFELSE v_bt v_instr_1 v_instr_2)] [(AI_BLOCK v_bt v_instr_1)]
	| step_if_false : forall (v_c : (uN 32)) (v_bt : blocktype) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), 
		((fun_proj_uN_0 32 v_c) = 0) ->
		Step_pure [(AI_CONST I32 v_c); (AI_IFELSE v_bt v_instr_1 v_instr_2)] [(AI_BLOCK v_bt v_instr_2)]
	| step_label_vals : forall (v_n : n) (v_instr : (list instr)) (v_val : (list val)), Step_pure [(AI_LABEL_ v_n v_instr (List.map (fun (v_val : val) => (v_val : admininstr)) v_val))] (List.map (fun (v_val : val) => (v_val : admininstr)) v_val)
	| step_br_zero : forall (v_n : n) (v_instr' : (list instr)) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)), 
		((List.length v_val) = v_n) ->
		Step_pure [(AI_LABEL_ v_n v_instr' ((List.map (fun (v_val' : val) => (v_val' : admininstr)) v_val') ++ ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([(AI_BR (mk_uN _ 0))] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)))))] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))
	| step_br_succ : forall (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_l : labelidx) (v_instr : (list instr)), Step_pure [(AI_LABEL_ v_n v_instr' ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([(AI_BR (mk_uN _ ((fun_proj_uN_0 32 v_l) + 1)))] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))))] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [(AI_BR v_l)])
	| step_br_if_true : forall (v_c : (uN 32)) (v_l : labelidx), 
		((fun_proj_uN_0 32 v_c) <> 0) ->
		Step_pure [(AI_CONST I32 v_c); (AI_BR_IF v_l)] [(AI_BR v_l)]
	| step_br_if_false : forall (v_c : (uN 32)) (v_l : labelidx), 
		((fun_proj_uN_0 32 v_c) = 0) ->
		Step_pure [(AI_CONST I32 v_c); (AI_BR_IF v_l)] []
	| step_br_table_lt : forall (v_i : (uN 32)) (v_l : (list labelidx)) (v_l' : labelidx), 
		((fun_proj_uN_0 32 v_i) < (List.length v_l)) ->
		Step_pure [(AI_CONST I32 v_i); (AI_BR_TABLE v_l v_l')] [(AI_BR (lookup_total v_l (fun_proj_uN_0 32 v_i)))]
	| step_br_table_ge : forall (v_i : (uN 32)) (v_l : (list labelidx)) (v_l' : labelidx), 
		((fun_proj_uN_0 32 v_i) >= (List.length v_l)) ->
		Step_pure [(AI_CONST I32 v_i); (AI_BR_TABLE v_l v_l')] [(AI_BR v_l')]
	| step_frame_vals : forall (v_n : n) (v_f : frame) (v_val : (list val)), Step_pure [(AI_FRAME_ v_n v_f (List.map (fun (v_val : val) => (v_val : admininstr)) v_val))] (List.map (fun (v_val : val) => (v_val : admininstr)) v_val)
	| step_return_frame : forall (v_n : n) (v_f : frame) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)), 
		((List.length v_val) = v_n) ->
		Step_pure [(AI_FRAME_ v_n v_f ((List.map (fun (v_val' : val) => (v_val' : admininstr)) v_val') ++ ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([AI_RETURN] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)))))] (List.map (fun (v_val : val) => (v_val : admininstr)) v_val)
	| step_return_label : forall (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_instr : (list instr)), Step_pure [(AI_LABEL_ v_n v_instr' ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([AI_RETURN] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))))] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [AI_RETURN])
	| step_trap_vals : forall (v_val : (list val)) (v_instr : (list instr)), 
		((v_val <> []) \/ (v_instr <> [])) ->
		Step_pure ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([AI_TRAP] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))) [AI_TRAP]
	| step_trap_label : forall (v_n : n) (v_instr' : (list instr)), Step_pure [(AI_LABEL_ v_n v_instr' [AI_TRAP])] [AI_TRAP]
	| step_trap_frame : forall (v_n : n) (v_f : frame), Step_pure [(AI_FRAME_ v_n v_f [AI_TRAP])] [AI_TRAP]
	| step_unop_val : forall (v_nt : numtype) (v_c_1 : (num_ v_nt)) (v_unop : (unop_ v_nt)) (v_c : (num_ v_nt)), 
		((List.length (fun_unop_ v_nt v_unop v_c_1)) > 0) ->
		(List.In v_c (fun_unop_ v_nt v_unop v_c_1)) ->
		Step_pure [(AI_CONST v_nt v_c_1); (AI_UNOP v_nt v_unop)] [(AI_CONST v_nt v_c)]
	| step_unop_trap : forall (v_nt : numtype) (v_c_1 : (num_ v_nt)) (v_unop : (unop_ v_nt)), 
		((fun_unop_ v_nt v_unop v_c_1) = []) ->
		Step_pure [(AI_CONST v_nt v_c_1); (AI_UNOP v_nt v_unop)] [AI_TRAP]
	| step_binop_val : forall (v_nt : numtype) (v_c_1 : (num_ v_nt)) (v_c_2 : (num_ v_nt)) (v_binop : (binop_ v_nt)) (v_c : (num_ v_nt)), 
		((List.length (fun_binop_ v_nt v_binop v_c_1 v_c_2)) > 0) ->
		(List.In v_c (fun_binop_ v_nt v_binop v_c_1 v_c_2)) ->
		Step_pure [(AI_CONST v_nt v_c_1); (AI_CONST v_nt v_c_2); (AI_BINOP v_nt v_binop)] [(AI_CONST v_nt v_c)]
	| step_binop_trap : forall (v_nt : numtype) (v_c_1 : (num_ v_nt)) (v_c_2 : (num_ v_nt)) (v_binop : (binop_ v_nt)), 
		((fun_binop_ v_nt v_binop v_c_1 v_c_2) = []) ->
		Step_pure [(AI_CONST v_nt v_c_1); (AI_CONST v_nt v_c_2); (AI_BINOP v_nt v_binop)] [AI_TRAP]
	| step_testop : forall (v_nt : numtype) (v_c_1 : (num_ v_nt)) (v_testop : (testop_ v_nt)) (v_c : (uN 32)), 
		(v_c = (fun_testop_ v_nt v_testop v_c_1)) ->
		Step_pure [(AI_CONST v_nt v_c_1); (AI_TESTOP v_nt v_testop)] [(AI_CONST I32 v_c)]
	| step_relop : forall (v_nt : numtype) (v_c_1 : (num_ v_nt)) (v_c_2 : (num_ v_nt)) (v_relop : (relop_ v_nt)) (v_c : (uN 32)), 
		(v_c = (fun_relop_ v_nt v_relop v_c_1 v_c_2)) ->
		Step_pure [(AI_CONST v_nt v_c_1); (AI_CONST v_nt v_c_2); (AI_RELOP v_nt v_relop)] [(AI_CONST I32 v_c)]
	| step_cvtop_val : forall (v_nt_1 : numtype) (v_c_1 : (num_ v_nt_1)) (v_nt_2 : numtype) (v_cvtop : cvtop) (v_c : (num_ v_nt_2)), 
		((List.length (fun_cvtop__ v_nt_1 v_nt_2 v_cvtop v_c_1)) > 0) ->
		(List.In v_c (fun_cvtop__ v_nt_1 v_nt_2 v_cvtop v_c_1)) ->
		Step_pure [(AI_CONST v_nt_1 v_c_1); (AI_CVTOP v_nt_2 v_nt_1 v_cvtop)] [(AI_CONST v_nt_2 v_c)]
	| step_cvtop_trap : forall (v_nt_1 : numtype) (v_c_1 : (num_ v_nt_1)) (v_nt_2 : numtype) (v_cvtop : cvtop), 
		((fun_cvtop__ v_nt_1 v_nt_2 v_cvtop v_c_1) = []) ->
		Step_pure [(AI_CONST v_nt_1 v_c_1); (AI_CVTOP v_nt_2 v_nt_1 v_cvtop)] [AI_TRAP]
	| step_ref_is_null_true : forall (v_ref : ref) (v_rt : reftype), 
		(v_ref = (REF_NULL v_rt)) ->
		Step_pure [(v_ref : admininstr); AI_REF_IS_NULL] [(AI_CONST I32 (mk_uN _ 1))]
	| step_ref_is_null_false : forall (v_ref : ref), 
		(~(Step_pure_before_ref_is_null_false [(v_ref : admininstr); AI_REF_IS_NULL])) ->
		Step_pure [(v_ref : admininstr); AI_REF_IS_NULL] [(AI_CONST I32 (mk_uN _ 0))]
	| step_vvunop : forall (v_c_1 : (vec_ V128)) (v_vvunop : vvunop) (v_c : (vec_ V128)), 
		(v_c = (fun_vvunop_ V128 v_vvunop v_c_1)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VVUNOP V128 v_vvunop)] [(AI_VCONST V128 v_c)]
	| step_vvbinop : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_vvbinop : vvbinop) (v_c : (vec_ V128)), 
		(v_c = (fun_vvbinop_ V128 v_vvbinop v_c_1 v_c_2)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VVBINOP V128 v_vvbinop)] [(AI_VCONST V128 v_c)]
	| step_vvternop : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_c_3 : (vec_ V128)) (v_vvternop : vvternop) (v_c : (vec_ V128)), 
		(v_c = (fun_vvternop_ V128 v_vvternop v_c_1 v_c_2 v_c_3)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VCONST V128 v_c_3); (AI_VVTERNOP V128 v_vvternop)] [(AI_VCONST V128 v_c)]
	| step_vvtestop : forall (v_c_1 : (vec_ V128)) (v_c : (uN 32)), 
		((fun_size VALTYPE_V128) <> None) ->
		(v_c = (fun_ine_ (the (fun_size VALTYPE_V128)) v_c_1 (mk_uN _ 0))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VVTESTOP V128 ANY_TRUE)] [(AI_CONST I32 v_c)]
	| step_vunop : forall (v_c_1 : (vec_ V128)) (v_sh : shape) (v_vunop : (vunop_ v_sh)) (v_c : (vec_ V128)), 
		((List.length (fun_vunop_ v_sh v_vunop v_c_1)) > 0) ->
		(List.In v_c (fun_vunop_ v_sh v_vunop v_c_1)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VUNOP v_sh v_vunop)] [(AI_VCONST V128 v_c)]
	| step_vunop_trap : forall (v_c_1 : (vec_ V128)) (v_sh : shape) (v_vunop : (vunop_ v_sh)), 
		((fun_vunop_ v_sh v_vunop v_c_1) = []) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VUNOP v_sh v_vunop)] [AI_TRAP]
	| step_vbinop_val : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_sh : shape) (v_vbinop : (vbinop_ v_sh)) (v_c : (vec_ V128)), 
		((List.length (fun_vbinop_ v_sh v_vbinop v_c_1 v_c_2)) > 0) ->
		(List.In v_c (fun_vbinop_ v_sh v_vbinop v_c_1 v_c_2)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VBINOP v_sh v_vbinop)] [(AI_VCONST V128 v_c)]
	| step_vbinop_trap : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_sh : shape) (v_vbinop : (vbinop_ v_sh)), 
		((fun_vbinop_ v_sh v_vbinop v_c_1 v_c_2) = []) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VBINOP v_sh v_vbinop)] [AI_TRAP]
	| step_vtestop_true_I32 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 32))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 32)) => ((fun_proj_uN_0 32 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I32 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 1))]
	| step_vtestop_true_I64 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 64))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 64)) => ((fun_proj_uN_0 64 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I64 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 1))]
	| step_vtestop_true_I8 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 8))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 8)) => ((fun_proj_uN_0 8 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I8 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 1))]
	| step_vtestop_true_I16 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci_1 : (list (uN 16))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N)) v_c)) ->
		List.Forall (fun (v_ci_1 : (uN 16)) => ((fun_proj_uN_0 16 v_ci_1) <> 0)) (v_ci_1) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I16 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 1))]
	| step_vtestop_false_I32 : forall (v_c : (vec_ V128)) (v_N : res_N), 
		(~(Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I32 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I32 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 0))]
	| step_vtestop_false_I64 : forall (v_c : (vec_ V128)) (v_N : res_N), 
		(~(Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I64 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I64 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 0))]
	| step_vtestop_false_I8 : forall (v_c : (vec_ V128)) (v_N : res_N), 
		(~(Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I8 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I8 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 0))]
	| step_vtestop_false_I16 : forall (v_c : (vec_ V128)) (v_N : res_N), 
		(~(Step_pure_before_vtestop_false [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I16 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VTESTOP (X (JNN_I16 : lanetype) (mk_dim v_N)) (ALL_TRUE _ _))] [(AI_CONST I32 (mk_uN _ 0))]
	| step_vrelop : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_sh : shape) (v_vrelop : (vrelop_ v_sh)) (v_c : (vec_ V128)), 
		((fun_vrelop_ v_sh v_vrelop v_c_1 v_c_2) = v_c) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VRELOP v_sh v_vrelop)] [(AI_VCONST V128 v_c)]
	| step_vshiftop_I32 : forall (v_c_1 : (vec_ V128)) (v_n : n) (v_N : res_N) (v_vshiftop : (vshiftop_Jnn_N JNN_I32 v_N)) (v_c : (vec_ V128)) (v_c' : (list (uN 32))), 
		(v_c' = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N)) v_c_1)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N)) (List.map (fun (v_c' : (uN 32)) => (fun_vshiftop_ (IX JNN_I32 (mk_dim v_N)) v_vshiftop v_c' (mk_uN _ v_n))) v_c'))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_CONST I32 (mk_uN _ v_n)); (AI_VSHIFTOP (IX JNN_I32 (mk_dim v_N)) v_vshiftop)] [(AI_VCONST V128 v_c)]
	| step_vshiftop_I64 : forall (v_c_1 : (vec_ V128)) (v_n : n) (v_N : res_N) (v_vshiftop : (vshiftop_Jnn_N JNN_I64 v_N)) (v_c : (vec_ V128)) (v_c' : (list (uN 64))), 
		(v_c' = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N)) v_c_1)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N)) (List.map (fun (v_c' : (uN 64)) => (fun_vshiftop_ (IX JNN_I64 (mk_dim v_N)) v_vshiftop v_c' (mk_uN _ v_n))) v_c'))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_CONST I32 (mk_uN _ v_n)); (AI_VSHIFTOP (IX JNN_I64 (mk_dim v_N)) v_vshiftop)] [(AI_VCONST V128 v_c)]
	| step_vshiftop_I8 : forall (v_c_1 : (vec_ V128)) (v_n : n) (v_N : res_N) (v_vshiftop : (vshiftop_Jnn_N JNN_I8 v_N)) (v_c : (vec_ V128)) (v_c' : (list (uN 8))), 
		(v_c' = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N)) v_c_1)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N)) (List.map (fun (v_c' : (uN 8)) => (fun_vshiftop_ (IX JNN_I8 (mk_dim v_N)) v_vshiftop v_c' (mk_uN _ v_n))) v_c'))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_CONST I32 (mk_uN _ v_n)); (AI_VSHIFTOP (IX JNN_I8 (mk_dim v_N)) v_vshiftop)] [(AI_VCONST V128 v_c)]
	| step_vshiftop_I16 : forall (v_c_1 : (vec_ V128)) (v_n : n) (v_N : res_N) (v_vshiftop : (vshiftop_Jnn_N JNN_I16 v_N)) (v_c : (vec_ V128)) (v_c' : (list (uN 16))), 
		(v_c' = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N)) v_c_1)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N)) (List.map (fun (v_c' : (uN 16)) => (fun_vshiftop_ (IX JNN_I16 (mk_dim v_N)) v_vshiftop v_c' (mk_uN _ v_n))) v_c'))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_CONST I32 (mk_uN _ v_n)); (AI_VSHIFTOP (IX JNN_I16 (mk_dim v_N)) v_vshiftop)] [(AI_VCONST V128 v_c)]
	| step_vbitmask_I32 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci : (iN 32)) (v_ci_1 : (list (uN 32))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N)) v_c)) ->
		((fun_ibits_ 32 v_ci) = ((List.map (fun (v_ci_1 : (iN (fun_lsize (I32 : lanetype)))) => (mk_bit (fun_proj_uN_0 32 (fun_ilt_ (fun_lsize (JNN_I32 : lanetype)) res_S v_ci_1 (mk_uN _ 0))))) v_ci_1) ++ [(mk_bit 0)])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VBITMASK (IX JNN_I32 (mk_dim v_N)))] [(AI_CONST I32 (fun_irev_ 32 v_ci))]
	| step_vbitmask_I64 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci : (iN 32)) (v_ci_1 : (list (uN 64))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N)) v_c)) ->
		((fun_ibits_ 32 v_ci) = ((List.map (fun (v_ci_1 : (iN (fun_lsize (I64 : lanetype)))) => (mk_bit (fun_proj_uN_0 32 (fun_ilt_ (fun_lsize (JNN_I64 : lanetype)) res_S v_ci_1 (mk_uN _ 0))))) v_ci_1) ++ [(mk_bit 0)])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VBITMASK (IX JNN_I64 (mk_dim v_N)))] [(AI_CONST I32 (fun_irev_ 32 v_ci))]
	| step_vbitmask_I8 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci : (iN 32)) (v_ci_1 : (list (uN 8))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N)) v_c)) ->
		((fun_ibits_ 32 v_ci) = ((List.map (fun (v_ci_1 : (iN (fun_lsize (I8 : lanetype)))) => (mk_bit (fun_proj_uN_0 32 (fun_ilt_ (fun_lsize (JNN_I8 : lanetype)) res_S v_ci_1 (mk_uN _ 0))))) v_ci_1) ++ [(mk_bit 0)])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VBITMASK (IX JNN_I8 (mk_dim v_N)))] [(AI_CONST I32 (fun_irev_ 32 v_ci))]
	| step_vbitmask_I16 : forall (v_c : (vec_ V128)) (v_N : res_N) (v_ci : (iN 32)) (v_ci_1 : (list (uN 16))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N)) v_c)) ->
		((fun_ibits_ 32 v_ci) = ((List.map (fun (v_ci_1 : (iN (fun_lsize (I16 : lanetype)))) => (mk_bit (fun_proj_uN_0 32 (fun_ilt_ (fun_lsize (JNN_I16 : lanetype)) res_S v_ci_1 (mk_uN _ 0))))) v_ci_1) ++ [(mk_bit 0)])) ->
		Step_pure [(AI_VCONST V128 v_c); (AI_VBITMASK (IX JNN_I16 (mk_dim v_N)))] [(AI_CONST I32 (fun_irev_ 32 v_ci))]
	| step_vswizzle_I8 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_M : M) (v_c : (vec_ V128)) (v_c' : (list (iN (fun_lsize (I8 : lanetype))))) (v_ci : (list (uN 8))) (v_k : (list nat)), 
		(v_ci = (fun_lanes_ (X (I8 : lanetype) (mk_dim v_M)) v_c_2)) ->
		(v_c' = ((fun_lanes_ (X (I8 : lanetype) (mk_dim v_M)) v_c_1) ++ [(mk_uN _ 0)])) ->
		List.Forall (fun (v_k : nat) => ((fun_proj_uN_0 8 (lookup_total v_ci v_k)) < (List.length v_c'))) (v_k) ->
		List.Forall (fun (v_k : nat) => (v_k < (List.length v_ci))) (v_k) ->
		(v_c = (fun_inv_lanes_ (X (I8 : lanetype) (mk_dim v_M)) (List.map (fun (v_k : nat) => (lookup_total v_c' (fun_proj_uN_0 8 (lookup_total v_ci v_k)))) v_k))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VSWIZZLE (IX (I8 : Jnn) (mk_dim v_M)))] [(AI_VCONST V128 v_c)]
	| step_vswizzle_I16 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_M : M) (v_c : (vec_ V128)) (v_c' : (list (iN (fun_lsize (I16 : lanetype))))) (v_ci : (list (uN 16))) (v_k : (list nat)), 
		(v_ci = (fun_lanes_ (X (I16 : lanetype) (mk_dim v_M)) v_c_2)) ->
		(v_c' = ((fun_lanes_ (X (I16 : lanetype) (mk_dim v_M)) v_c_1) ++ [(mk_uN _ 0)])) ->
		List.Forall (fun (v_k : nat) => ((fun_proj_uN_0 16 (lookup_total v_ci v_k)) < (List.length v_c'))) (v_k) ->
		List.Forall (fun (v_k : nat) => (v_k < (List.length v_ci))) (v_k) ->
		(v_c = (fun_inv_lanes_ (X (I16 : lanetype) (mk_dim v_M)) (List.map (fun (v_k : nat) => (lookup_total v_c' (fun_proj_uN_0 16 (lookup_total v_ci v_k)))) v_k))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VSWIZZLE (IX (I16 : Jnn) (mk_dim v_M)))] [(AI_VCONST V128 v_c)]
	| step_vshuffle_I8 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N : res_N) (v_i : (list laneidx)) (v_c : (vec_ V128)) (v_c' : (list (iN (fun_lsize (I8 : lanetype))))) (v_k : (list nat)), 
		(v_c' = ((fun_lanes_ (X (I8 : lanetype) (mk_dim v_N)) v_c_1) ++ (fun_lanes_ (X (I8 : lanetype) (mk_dim v_N)) v_c_2))) ->
		List.Forall (fun (v_k : nat) => ((fun_proj_uN_0 8 (lookup_total v_i v_k)) < (List.length v_c'))) (v_k) ->
		List.Forall (fun (v_k : nat) => (v_k < (List.length v_i))) (v_k) ->
		(v_c = (fun_inv_lanes_ (X (I8 : lanetype) (mk_dim v_N)) (List.map (fun (v_k : nat) => (lookup_total v_c' (fun_proj_uN_0 8 (lookup_total v_i v_k)))) v_k))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VSHUFFLE (IX (I8 : Jnn) (mk_dim v_N)) v_i)] [(AI_VCONST V128 v_c)]
	| step_vshuffle_I16 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N : res_N) (v_i : (list laneidx)) (v_c : (vec_ V128)) (v_c' : (list (iN (fun_lsize (I16 : lanetype))))) (v_k : (list nat)), 
		(v_c' = ((fun_lanes_ (X (I16 : lanetype) (mk_dim v_N)) v_c_1) ++ (fun_lanes_ (X (I16 : lanetype) (mk_dim v_N)) v_c_2))) ->
		List.Forall (fun (v_k : nat) => ((fun_proj_uN_0 8 (lookup_total v_i v_k)) < (List.length v_c'))) (v_k) ->
		List.Forall (fun (v_k : nat) => (v_k < (List.length v_i))) (v_k) ->
		(v_c = (fun_inv_lanes_ (X (I16 : lanetype) (mk_dim v_N)) (List.map (fun (v_k : nat) => (lookup_total v_c' (fun_proj_uN_0 8 (lookup_total v_i v_k)))) v_k))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VSHUFFLE (IX (I16 : Jnn) (mk_dim v_N)) v_i)] [(AI_VCONST V128 v_c)]
	| step_vsplat : forall (v_Lnn : Lnn) (v_c_1 : (num_ (fun_unpack v_Lnn))) (v_N : res_N) (v_c : (vec_ V128)), 
		(v_c = (fun_inv_lanes_ (X v_Lnn (mk_dim v_N)) [(fun_packnum_ v_Lnn v_c_1)])) ->
		Step_pure [(AI_CONST (fun_unpack v_Lnn) v_c_1); (AI_VSPLAT (X v_Lnn (mk_dim v_N)))] [(AI_VCONST V128 v_c)]
	| step_vextract_lane_num_I32 : forall (v_c_1 : (vec_ V128)) (v_N : res_N) (v_i : laneidx) (v_c_2 : (uN 32)), 
		((fun_proj_uN_0 8 v_i) < (List.length (fun_lanes_ (X (I32 : lanetype) (mk_dim v_N)) v_c_1))) ->
		(v_c_2 = (lookup_total (fun_lanes_ (X (I32 : lanetype) (mk_dim v_N)) v_c_1) (fun_proj_uN_0 8 v_i))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VEXTRACT_LANE (X (I32 : lanetype) (mk_dim v_N)) None v_i)] [(AI_CONST I32 v_c_2)]
	| step_vextract_lane_num_I64 : forall (v_c_1 : (vec_ V128)) (v_N : res_N) (v_i : laneidx) (v_c_2 : (uN 64)), 
		((fun_proj_uN_0 8 v_i) < (List.length (fun_lanes_ (X (I64 : lanetype) (mk_dim v_N)) v_c_1))) ->
		(v_c_2 = (lookup_total (fun_lanes_ (X (I64 : lanetype) (mk_dim v_N)) v_c_1) (fun_proj_uN_0 8 v_i))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VEXTRACT_LANE (X (I64 : lanetype) (mk_dim v_N)) None v_i)] [(AI_CONST I64 v_c_2)]
	| step_vextract_lane_num_F32 : forall (v_c_1 : (vec_ V128)) (v_N : res_N) (v_i : laneidx) (v_c_2 : (fN 32)), 
		((fun_proj_uN_0 8 v_i) < (List.length (fun_lanes_ (X (F32 : lanetype) (mk_dim v_N)) v_c_1))) ->
		(v_c_2 = (lookup_total (fun_lanes_ (X (F32 : lanetype) (mk_dim v_N)) v_c_1) (fun_proj_uN_0 8 v_i))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VEXTRACT_LANE (X (F32 : lanetype) (mk_dim v_N)) None v_i)] [(AI_CONST F32 v_c_2)]
	| step_vextract_lane_num_F64 : forall (v_c_1 : (vec_ V128)) (v_N : res_N) (v_i : laneidx) (v_c_2 : (fN 64)), 
		((fun_proj_uN_0 8 v_i) < (List.length (fun_lanes_ (X (F64 : lanetype) (mk_dim v_N)) v_c_1))) ->
		(v_c_2 = (lookup_total (fun_lanes_ (X (F64 : lanetype) (mk_dim v_N)) v_c_1) (fun_proj_uN_0 8 v_i))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VEXTRACT_LANE (X (F64 : lanetype) (mk_dim v_N)) None v_i)] [(AI_CONST F64 v_c_2)]
	| step_vextract_lane_pack_I8 : forall (v_c_1 : (vec_ V128)) (v_N : res_N) (v_sx : sx) (v_i : laneidx) (v_c_2 : (uN 32)), 
		((fun_proj_uN_0 8 v_i) < (List.length (fun_lanes_ (X (I8 : lanetype) (mk_dim v_N)) v_c_1))) ->
		(v_c_2 = (fun_extend__ (fun_psize I8) 32 v_sx (lookup_total (fun_lanes_ (X (I8 : lanetype) (mk_dim v_N)) v_c_1) (fun_proj_uN_0 8 v_i)))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VEXTRACT_LANE (X (I8 : lanetype) (mk_dim v_N)) (Some v_sx) v_i)] [(AI_CONST I32 v_c_2)]
	| step_vextract_lane_pack_I16 : forall (v_c_1 : (vec_ V128)) (v_N : res_N) (v_sx : sx) (v_i : laneidx) (v_c_2 : (uN 32)), 
		((fun_proj_uN_0 8 v_i) < (List.length (fun_lanes_ (X (I16 : lanetype) (mk_dim v_N)) v_c_1))) ->
		(v_c_2 = (fun_extend__ (fun_psize I16) 32 v_sx (lookup_total (fun_lanes_ (X (I16 : lanetype) (mk_dim v_N)) v_c_1) (fun_proj_uN_0 8 v_i)))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VEXTRACT_LANE (X (I16 : lanetype) (mk_dim v_N)) (Some v_sx) v_i)] [(AI_CONST I32 v_c_2)]
	| step_vreplace_lane : forall (v_c_1 : (vec_ V128)) (v_Lnn : Lnn) (v_c_2 : (num_ (fun_unpack v_Lnn))) (v_N : res_N) (v_i : laneidx) (v_c : (vec_ V128)), 
		(v_c = (fun_inv_lanes_ (X v_Lnn (mk_dim v_N)) (list_update_func (fun_lanes_ (X v_Lnn (mk_dim v_N)) v_c_1) (fun_proj_uN_0 8 v_i) (fun (_ : (lane_ v_Lnn)) => (fun_packnum_ v_Lnn v_c_2))))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_CONST (fun_unpack v_Lnn) v_c_2); (AI_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) v_i)] [(AI_VCONST V128 v_c)]
	| step_vextunop : forall (v_c_1 : (vec_ V128)) (v_sh_1 : ishape) (v_sh_2 : ishape) (v_vextunop : (vextunop_ v_sh_1)) (v_c : (vec_ V128)), 
		((fun_vextunop__ v_sh_1 v_sh_2 v_vextunop v_c_1) = v_c) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VEXTUNOP v_sh_1 v_sh_2 v_vextunop)] [(AI_VCONST V128 v_c)]
	| step_vextbinop : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_sh_1 : ishape) (v_sh_2 : ishape) (v_vextbinop : (vextbinop_ v_sh_1)) (v_c : (vec_ V128)), 
		((fun_vextbinop__ v_sh_1 v_sh_2 v_vextbinop v_c_1 v_c_2) = v_c) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VEXTBINOP v_sh_1 v_sh_2 v_vextbinop)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I32_I32 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 32))) (v_ci_2 : (list (uN 32))) (v_cj_1 : (list (iN (fun_lsize (JNN_I32 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I32 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I32 (mk_dim v_N_2)) (IX JNN_I32 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I64_I32 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 64))) (v_ci_2 : (list (uN 64))) (v_cj_1 : (list (iN (fun_lsize (JNN_I32 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I32 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I32 (mk_dim v_N_2)) (IX JNN_I64 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I8_I32 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 8))) (v_ci_2 : (list (uN 8))) (v_cj_1 : (list (iN (fun_lsize (JNN_I32 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I32 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I32 (mk_dim v_N_2)) (IX JNN_I8 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I16_I32 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 16))) (v_ci_2 : (list (uN 16))) (v_cj_1 : (list (iN (fun_lsize (JNN_I32 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I32 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I32 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I32 (mk_dim v_N_2)) (IX JNN_I16 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I32_I64 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 32))) (v_ci_2 : (list (uN 32))) (v_cj_1 : (list (iN (fun_lsize (JNN_I64 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I64 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I64 (mk_dim v_N_2)) (IX JNN_I32 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I64_I64 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 64))) (v_ci_2 : (list (uN 64))) (v_cj_1 : (list (iN (fun_lsize (JNN_I64 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I64 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I64 (mk_dim v_N_2)) (IX JNN_I64 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I8_I64 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 8))) (v_ci_2 : (list (uN 8))) (v_cj_1 : (list (iN (fun_lsize (JNN_I64 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I64 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I64 (mk_dim v_N_2)) (IX JNN_I8 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I16_I64 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 16))) (v_ci_2 : (list (uN 16))) (v_cj_1 : (list (iN (fun_lsize (JNN_I64 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I64 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I64 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I64 (mk_dim v_N_2)) (IX JNN_I16 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I32_I8 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 32))) (v_ci_2 : (list (uN 32))) (v_cj_1 : (list (iN (fun_lsize (JNN_I8 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I8 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I8 (mk_dim v_N_2)) (IX JNN_I32 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I64_I8 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 64))) (v_ci_2 : (list (uN 64))) (v_cj_1 : (list (iN (fun_lsize (JNN_I8 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I8 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I8 (mk_dim v_N_2)) (IX JNN_I64 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I8_I8 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 8))) (v_ci_2 : (list (uN 8))) (v_cj_1 : (list (iN (fun_lsize (JNN_I8 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I8 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I8 (mk_dim v_N_2)) (IX JNN_I8 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I16_I8 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 16))) (v_ci_2 : (list (uN 16))) (v_cj_1 : (list (iN (fun_lsize (JNN_I8 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I8 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I8 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I8 (mk_dim v_N_2)) (IX JNN_I16 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I32_I16 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 32))) (v_ci_2 : (list (uN 32))) (v_cj_1 : (list (iN (fun_lsize (JNN_I16 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I16 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I32 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I32 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I16 (mk_dim v_N_2)) (IX JNN_I32 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I64_I16 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 64))) (v_ci_2 : (list (uN 64))) (v_cj_1 : (list (iN (fun_lsize (JNN_I16 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I16 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I64 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I64 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I16 (mk_dim v_N_2)) (IX JNN_I64 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I8_I16 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 8))) (v_ci_2 : (list (uN 8))) (v_cj_1 : (list (iN (fun_lsize (JNN_I16 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I16 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I8 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I8 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I16 (mk_dim v_N_2)) (IX JNN_I8 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vnarrow_I16_I16 : forall (v_c_1 : (vec_ V128)) (v_c_2 : (vec_ V128)) (v_N_2 : res_N) (v_N_1 : res_N) (v_sx : sx) (v_c : (vec_ V128)) (v_ci_1 : (list (uN 16))) (v_ci_2 : (list (uN 16))) (v_cj_1 : (list (iN (fun_lsize (JNN_I16 : lanetype))))) (v_cj_2 : (list (iN (fun_lsize (JNN_I16 : lanetype))))), 
		(v_ci_1 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_1)) ->
		(v_ci_2 = (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_1)) v_c_2)) ->
		(v_cj_1 = (List.map (fun (v_ci_1 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_1)) v_ci_1)) ->
		(v_cj_2 = (List.map (fun (v_ci_2 : (iN (fun_lsize (I16 : lanetype)))) => (fun_narrow__ (fun_lsize (JNN_I16 : lanetype)) (fun_lsize (JNN_I16 : lanetype)) v_sx v_ci_2)) v_ci_2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N_2)) (v_cj_1 ++ v_cj_2))) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCONST V128 v_c_2); (AI_VNARROW (IX JNN_I16 (mk_dim v_N_2)) (IX JNN_I16 (mk_dim v_N_1)) v_sx)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_full : forall (v_c_1 : (vec_ V128)) (v_Lnn_2 : Lnn) (v_M : M) (v_Lnn_1 : Lnn) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (lane_ v_Lnn_1))) (v_cj : (list (list (lane_ v_Lnn_2)))), 
		(((fun_halfop v_vcvtop) = None) /\ ((fun_zeroop v_vcvtop) = None)) ->
		(v_ci = (fun_lanes_ (X v_Lnn_1 (mk_dim v_M)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (lane_ v_Lnn_2) (List.map (fun (v_ci : (lane_ v_Lnn_1)) => (fun_vcvtop__ (X v_Lnn_1 (mk_dim v_M)) (X v_Lnn_2 (mk_dim v_M)) v_vcvtop v_ci)) v_ci))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X v_Lnn_2 (mk_dim v_M)))))) => (fun_inv_lanes_ (X v_Lnn_2 (mk_dim v_M)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (lane_ v_Lnn_2))) => (fun_inv_lanes_ (X v_Lnn_2 (mk_dim v_M)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X v_Lnn_2 (mk_dim v_M)) (X v_Lnn_1 (mk_dim v_M)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_half : forall (v_c_1 : (vec_ V128)) (v_Lnn_2 : Lnn) (v_M_2 : M) (v_Lnn_1 : Lnn) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_half : half) (v_ci : (list (lane_ v_Lnn_1))) (v_cj : (list (list (lane_ v_Lnn_2)))), 
		((fun_halfop v_vcvtop) = (Some v_half)) ->
		(v_ci = (list_slice (fun_lanes_ (X v_Lnn_1 (mk_dim v_M_1)) v_c_1) (fun_half v_half 0 v_M_2) v_M_2)) ->
		(v_cj = (fun_setproduct_ (lane_ v_Lnn_2) (List.map (fun (v_ci : (lane_ v_Lnn_1)) => (fun_vcvtop__ (X v_Lnn_1 (mk_dim v_M_1)) (X v_Lnn_2 (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X v_Lnn_2 (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X v_Lnn_2 (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (lane_ v_Lnn_2))) => (fun_inv_lanes_ (X v_Lnn_2 (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X v_Lnn_2 (mk_dim v_M_2)) (X v_Lnn_1 (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I32_I32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 32))) (v_cj : (list (list (uN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 32) ((List.map (fun (v_ci : (uN 32)) => (fun_vcvtop__ (X (I32 : lanetype) (mk_dim v_M_1)) (X (I32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 32))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I32 : lanetype) (mk_dim v_M_2)) (X (I32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I64_I32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 64))) (v_cj : (list (list (uN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 32) ((List.map (fun (v_ci : (uN 64)) => (fun_vcvtop__ (X (I64 : lanetype) (mk_dim v_M_1)) (X (I32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 32))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I32 : lanetype) (mk_dim v_M_2)) (X (I64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F32_I32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 32))) (v_cj : (list (list (uN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 32) ((List.map (fun (v_ci : (fN 32)) => (fun_vcvtop__ (X (F32 : lanetype) (mk_dim v_M_1)) (X (I32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 32))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I32 : lanetype) (mk_dim v_M_2)) (X (F32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F64_I32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 64))) (v_cj : (list (list (uN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 32) ((List.map (fun (v_ci : (fN 64)) => (fun_vcvtop__ (X (F64 : lanetype) (mk_dim v_M_1)) (X (I32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 32))) => (fun_inv_lanes_ (X (I32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I32 : lanetype) (mk_dim v_M_2)) (X (F64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I32_I64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 32))) (v_cj : (list (list (uN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 64) ((List.map (fun (v_ci : (uN 32)) => (fun_vcvtop__ (X (I32 : lanetype) (mk_dim v_M_1)) (X (I64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 64))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I64 : lanetype) (mk_dim v_M_2)) (X (I32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I64_I64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 64))) (v_cj : (list (list (uN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 64) ((List.map (fun (v_ci : (uN 64)) => (fun_vcvtop__ (X (I64 : lanetype) (mk_dim v_M_1)) (X (I64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 64))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I64 : lanetype) (mk_dim v_M_2)) (X (I64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F32_I64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 32))) (v_cj : (list (list (uN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 64) ((List.map (fun (v_ci : (fN 32)) => (fun_vcvtop__ (X (F32 : lanetype) (mk_dim v_M_1)) (X (I64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 64))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I64 : lanetype) (mk_dim v_M_2)) (X (F32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F64_I64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 64))) (v_cj : (list (list (uN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (uN 64) ((List.map (fun (v_ci : (fN 64)) => (fun_vcvtop__ (X (F64 : lanetype) (mk_dim v_M_1)) (X (I64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero I64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (I64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (uN 64))) => (fun_inv_lanes_ (X (I64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (I64 : lanetype) (mk_dim v_M_2)) (X (F64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I32_F32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 32))) (v_cj : (list (list (fN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 32) ((List.map (fun (v_ci : (uN 32)) => (fun_vcvtop__ (X (I32 : lanetype) (mk_dim v_M_1)) (X (F32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 32))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F32 : lanetype) (mk_dim v_M_2)) (X (I32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I64_F32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 64))) (v_cj : (list (list (fN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 32) ((List.map (fun (v_ci : (uN 64)) => (fun_vcvtop__ (X (I64 : lanetype) (mk_dim v_M_1)) (X (F32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 32))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F32 : lanetype) (mk_dim v_M_2)) (X (I64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F32_F32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 32))) (v_cj : (list (list (fN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 32) ((List.map (fun (v_ci : (fN 32)) => (fun_vcvtop__ (X (F32 : lanetype) (mk_dim v_M_1)) (X (F32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 32))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F32 : lanetype) (mk_dim v_M_2)) (X (F32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F64_F32 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 64))) (v_cj : (list (list (fN 32)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 32) ((List.map (fun (v_ci : (fN 64)) => (fun_vcvtop__ (X (F64 : lanetype) (mk_dim v_M_1)) (X (F32 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F32)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F32 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 32))) => (fun_inv_lanes_ (X (F32 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F32 : lanetype) (mk_dim v_M_2)) (X (F64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I32_F64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 32))) (v_cj : (list (list (fN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 64) ((List.map (fun (v_ci : (uN 32)) => (fun_vcvtop__ (X (I32 : lanetype) (mk_dim v_M_1)) (X (F64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 64))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F64 : lanetype) (mk_dim v_M_2)) (X (I32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_I64_F64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (uN 64))) (v_cj : (list (list (fN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (I64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 64) ((List.map (fun (v_ci : (uN 64)) => (fun_vcvtop__ (X (I64 : lanetype) (mk_dim v_M_1)) (X (F64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 64))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F64 : lanetype) (mk_dim v_M_2)) (X (I64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F32_F64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 32))) (v_cj : (list (list (fN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F32 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 64) ((List.map (fun (v_ci : (fN 32)) => (fun_vcvtop__ (X (F32 : lanetype) (mk_dim v_M_1)) (X (F64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 64))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F64 : lanetype) (mk_dim v_M_2)) (X (F32 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_vcvtop_zero_F64_F64 : forall (v_c_1 : (vec_ V128)) (v_M_2 : M) (v_M_1 : M) (v_vcvtop : vcvtop) (v_c : (vec_ V128)) (v_ci : (list (fN 64))) (v_cj : (list (list (fN 64)))), 
		((fun_zeroop v_vcvtop) = (Some ZERO)) ->
		(v_ci = (fun_lanes_ (X (F64 : lanetype) (mk_dim v_M_1)) v_c_1)) ->
		(v_cj = (fun_setproduct_ (fN 64) ((List.map (fun (v_ci : (fN 64)) => (fun_vcvtop__ (X (F64 : lanetype) (mk_dim v_M_1)) (X (F64 : lanetype) (mk_dim v_M_2)) v_vcvtop v_ci)) v_ci) ++ [[(fun_zero F64)]]))) ->
		((List.length (List.map (fun (v_cj : (list (lane_ (fun_lanetype (X (F64 : lanetype) (mk_dim v_M_2)))))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) > 0) ->
		(List.In v_c (List.map (fun (v_cj : (list (fN 64))) => (fun_inv_lanes_ (X (F64 : lanetype) (mk_dim v_M_2)) v_cj)) v_cj)) ->
		Step_pure [(AI_VCONST V128 v_c_1); (AI_VCVTOP (X (F64 : lanetype) (mk_dim v_M_2)) (X (F64 : lanetype) (mk_dim v_M_1)) v_vcvtop)] [(AI_VCONST V128 v_c)]
	| step_local_tee : forall (v_val : val) (v_x : idx), Step_pure [(v_val : admininstr); (AI_LOCAL_TEE v_x)] [(v_val : admininstr); (v_val : admininstr); (AI_LOCAL_SET v_x)].

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 *)
Definition fun_blocktype (v_state : state) (v_blocktype : blocktype) : functype :=
	match v_state, v_blocktype return functype with
		| v_z, (_RESULT None) => (mk_functype (mk_list _ []) (mk_list _ []))
		| v_z, (_RESULT (Some v_t)) => (mk_functype (mk_list _ []) (mk_list _ [v_t]))
		| v_z, (_IDX v_x) => (fun_type v_z v_x)
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:132.1-134.15 *)
Inductive Step_read_before_call_indirect_trap: config -> Prop :=
	| step_call_indirect_call_0 : forall (v_z : state) (v_i : (uN 32)) (v_x : idx) (v_y : idx) (v_a : addr), 
		((fun_proj_uN_0 32 v_i) < (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		((lookup_total (TAB_REFS (fun_table v_z v_x)) (fun_proj_uN_0 32 v_i)) = (REF_FUNC_ADDR v_a)) ->
		(v_a < (List.length (fun_funcinst v_z))) ->
		((fun_type v_z v_y) = (FUNC_TYPE (lookup_total (fun_funcinst v_z) v_a))) ->
		Step_read_before_call_indirect_trap (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x v_y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:444.1-447.14 *)
Inductive Step_read_before_table_fill_zero: config -> Prop :=
	| step_table_fill_trap_0 : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n) (v_x : idx), 
		(((fun_proj_uN_0 32 v_i) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		Step_read_before_table_fill_zero (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:449.1-453.15 *)
Inductive Step_read_before_table_fill_succ: config -> Prop :=
	| step_table_fill_zero_0 : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n) (v_x : idx), 
		(~(Step_read_before_table_fill_zero (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]))) ->
		(v_n = 0) ->
		Step_read_before_table_fill_succ (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)])
	| step_table_fill_trap_1 : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n) (v_x : idx), 
		(((fun_proj_uN_0 32 v_i) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		Step_read_before_table_fill_succ (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:460.1-463.14 *)
Inductive Step_read_before_table_copy_zero: config -> Prop :=
	| step_table_copy_trap_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (TAB_REFS (fun_table v_z v_y)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x))))) ->
		Step_read_before_table_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:465.1-470.15 *)
Inductive Step_read_before_table_copy_le: config -> Prop :=
	| step_table_copy_zero_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]))) ->
		(v_n = 0) ->
		Step_read_before_table_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)])
	| step_table_copy_trap_1 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (TAB_REFS (fun_table v_z v_y)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x))))) ->
		Step_read_before_table_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:472.1-476.15 *)
Inductive Step_read_before_table_copy_gt: config -> Prop :=
	| step_table_copy_le_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]))) ->
		((fun_proj_uN_0 32 v_j) <= (fun_proj_uN_0 32 v_i)) ->
		Step_read_before_table_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)])
	| step_table_copy_zero_1 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]))) ->
		(v_n = 0) ->
		Step_read_before_table_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)])
	| step_table_copy_trap_2 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (TAB_REFS (fun_table v_z v_y)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x))))) ->
		Step_read_before_table_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:483.1-486.14 *)
Inductive Step_read_before_table_init_zero: config -> Prop :=
	| step_table_init_trap_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (ELEM_REFS (fun_elem v_z v_y)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x))))) ->
		Step_read_before_table_init_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:488.1-492.15 *)
Inductive Step_read_before_table_init_succ: config -> Prop :=
	| step_table_init_zero_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_init_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]))) ->
		(v_n = 0) ->
		Step_read_before_table_init_succ (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)])
	| step_table_init_trap_1 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (ELEM_REFS (fun_elem v_z v_y)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x))))) ->
		Step_read_before_table_init_succ (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:624.1-627.14 *)
Inductive Step_read_before_memory_fill_zero: config -> Prop :=
	| step_memory_fill_trap_0 : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n), 
		(((fun_proj_uN_0 32 v_i) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read_before_memory_fill_zero (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:629.1-633.15 *)
Inductive Step_read_before_memory_fill_succ: config -> Prop :=
	| step_memory_fill_zero_0 : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n), 
		(~(Step_read_before_memory_fill_zero (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]))) ->
		(v_n = 0) ->
		Step_read_before_memory_fill_succ (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL])
	| step_memory_fill_trap_1 : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n), 
		(((fun_proj_uN_0 32 v_i) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read_before_memory_fill_succ (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:640.1-643.14 *)
Inductive Step_read_before_memory_copy_zero: config -> Prop :=
	| step_memory_copy_trap_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))))) ->
		Step_read_before_memory_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:645.1-650.15 *)
Inductive Step_read_before_memory_copy_le: config -> Prop :=
	| step_memory_copy_zero_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		(~(Step_read_before_memory_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]))) ->
		(v_n = 0) ->
		Step_read_before_memory_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY])
	| step_memory_copy_trap_1 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))))) ->
		Step_read_before_memory_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:652.1-656.15 *)
Inductive Step_read_before_memory_copy_gt: config -> Prop :=
	| step_memory_copy_le_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		(~(Step_read_before_memory_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]))) ->
		((fun_proj_uN_0 32 v_j) <= (fun_proj_uN_0 32 v_i)) ->
		Step_read_before_memory_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY])
	| step_memory_copy_zero_1 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		(~(Step_read_before_memory_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]))) ->
		(v_n = 0) ->
		Step_read_before_memory_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY])
	| step_memory_copy_trap_2 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))))) ->
		Step_read_before_memory_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:663.1-666.14 *)
Inductive Step_read_before_memory_init_zero: config -> Prop :=
	| step_memory_init_trap_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (DATA_BYTES (fun_data v_z v_x)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))))) ->
		Step_read_before_memory_init_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:668.1-672.15 *)
Inductive Step_read_before_memory_init_succ: config -> Prop :=
	| step_memory_init_zero_0 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx), 
		(~(Step_read_before_memory_init_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]))) ->
		(v_n = 0) ->
		Step_read_before_memory_init_succ (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)])
	| step_memory_init_trap_1 : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (DATA_BYTES (fun_data v_z v_x)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))))) ->
		Step_read_before_memory_init_succ (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]).

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.98 *)
Inductive Step_read: config -> (list admininstr) -> Prop :=
	| step_block : forall (v_z : state) (v_val : (list val)) (v_k : nat) (v_bt : blocktype) (v_instr : (list instr)) (v_n : n) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		((fun_blocktype v_z v_bt) = (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		((List.length v_t_1) = (List.length v_val)) ->
		((List.length v_t_2) = v_n) ->
		Step_read (mk_config v_z ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [(AI_BLOCK v_bt v_instr)])) [(AI_LABEL_ v_n [] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)))]
	| step_loop : forall (v_z : state) (v_val : (list val)) (v_k : nat) (v_bt : blocktype) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)) (v_n : n), 
		((fun_blocktype v_z v_bt) = (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		((List.length v_t_1) = (List.length v_val)) ->
		((List.length v_val) = v_k) ->
		Step_read (mk_config v_z ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [(AI_LOOP v_bt v_instr)])) [(AI_LABEL_ v_k [(instr_LOOP v_bt v_instr)] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)))]
	| step_call : forall (v_z : state) (v_x : idx), 
		((fun_proj_uN_0 32 v_x) < (List.length (fun_funcaddr v_z))) ->
		Step_read (mk_config v_z [(AI_CALL v_x)]) [(AI_CALL_ADDR (lookup_total (fun_funcaddr v_z) (fun_proj_uN_0 32 v_x)))]
	| step_call_indirect_call : forall (v_z : state) (v_i : (uN 32)) (v_x : idx) (v_y : idx) (v_a : addr), 
		((fun_proj_uN_0 32 v_i) < (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		((lookup_total (TAB_REFS (fun_table v_z v_x)) (fun_proj_uN_0 32 v_i)) = (REF_FUNC_ADDR v_a)) ->
		(v_a < (List.length (fun_funcinst v_z))) ->
		((fun_type v_z v_y) = (FUNC_TYPE (lookup_total (fun_funcinst v_z) v_a))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x v_y)]) [(AI_CALL_ADDR v_a)]
	| step_call_indirect_trap : forall (v_z : state) (v_i : (uN 32)) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_call_indirect_trap (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x v_y)]))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x v_y)]) [AI_TRAP]
	| step_call_addr : forall (v_z : state) (v_val : (list val)) (v_k : nat) (v_a : addr) (v_n : n) (v_f : frame) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)) (v_mm : moduleinst) (v_func : func) (v_x : idx) (v_t : (list valtype)), 
		(v_a < (List.length (fun_funcinst v_z))) ->
		((lookup_total (fun_funcinst v_z) v_a) = {| FUNC_TYPE := (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2)); FUNC_MODULE := v_mm; FUNC_CODE := v_func |}) ->
		(v_func = (FUNC v_x (List.map (fun (v_t : valtype) => (LOCAL v_t)) v_t) v_instr)) ->
		List.Forall (fun (v_t : valtype) => ((fun_default_ v_t) <> None)) (v_t) ->
		(v_f = {| F_LOCALS := (v_val ++ (List.map (fun (v_t : valtype) => (the (fun_default_ v_t))) v_t)); F_MODULE := v_mm |}) ->
		((List.length v_t_2) = v_n) ->
		((List.length v_val) = (List.length v_t_1)) ->
		Step_read (mk_config v_z ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [(AI_CALL_ADDR v_a)])) [(AI_FRAME_ v_n v_f [(AI_LABEL_ v_n [] (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))])]
	| step_ref_func : forall (v_z : state) (v_x : idx), 
		((fun_proj_uN_0 32 v_x) < (List.length (fun_funcaddr v_z))) ->
		Step_read (mk_config v_z [(AI_REF_FUNC v_x)]) [(AI_REF_FUNC_ADDR (lookup_total (fun_funcaddr v_z) (fun_proj_uN_0 32 v_x)))]
	| step_local_get : forall (v_z : state) (v_x : idx), Step_read (mk_config v_z [(AI_LOCAL_GET v_x)]) [((fun_local v_z v_x) : admininstr)]
	| step_global_get : forall (v_z : state) (v_x : idx), Step_read (mk_config v_z [(AI_GLOBAL_GET v_x)]) [((GLOB_VALUE (fun_global v_z v_x)) : admininstr)]
	| step_table_get_trap : forall (v_z : state) (v_i : (uN 32)) (v_x : idx), 
		((fun_proj_uN_0 32 v_i) >= (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_TABLE_GET v_x)]) [AI_TRAP]
	| step_table_get_val : forall (v_z : state) (v_i : (uN 32)) (v_x : idx), 
		((fun_proj_uN_0 32 v_i) < (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_TABLE_GET v_x)]) [((lookup_total (TAB_REFS (fun_table v_z v_x)) (fun_proj_uN_0 32 v_i)) : admininstr)]
	| step_table_size : forall (v_z : state) (v_x : idx) (v_n : n), 
		((List.length (TAB_REFS (fun_table v_z v_x))) = v_n) ->
		Step_read (mk_config v_z [(AI_TABLE_SIZE v_x)]) [(AI_CONST I32 (mk_uN _ v_n))]
	| step_table_fill_trap : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n) (v_x : idx), 
		(((fun_proj_uN_0 32 v_i) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]) [AI_TRAP]
	| step_table_fill_zero : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n) (v_x : idx), 
		(~(Step_read_before_table_fill_zero (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]))) ->
		(v_n = 0) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]) []
	| step_table_fill_succ : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n) (v_x : idx), 
		(~(Step_read_before_table_fill_succ (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_FILL v_x)]) [(AI_CONST I32 v_i); (v_val : admininstr); (AI_TABLE_SET v_x); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_i) + 1))); (v_val : admininstr); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); (AI_TABLE_FILL v_x)]
	| step_table_copy_trap : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (TAB_REFS (fun_table v_z v_y)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]) [AI_TRAP]
	| step_table_copy_zero : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]))) ->
		(v_n = 0) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]) []
	| step_table_copy_le : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]))) ->
		((fun_proj_uN_0 32 v_j) <= (fun_proj_uN_0 32 v_i)) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]) [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_TABLE_GET v_y); (AI_TABLE_SET v_x); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_j) + 1))); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_i) + 1))); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); (AI_TABLE_COPY v_x v_y)]
	| step_table_copy_gt : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_COPY v_x v_y)]) [(AI_CONST I32 (mk_uN _ (((((fun_proj_uN_0 32 v_j) + v_n) : nat) - (1 : nat)) : nat))); (AI_CONST I32 (mk_uN _ (((((fun_proj_uN_0 32 v_i) + v_n) : nat) - (1 : nat)) : nat))); (AI_TABLE_GET v_y); (AI_TABLE_SET v_x); (AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); (AI_TABLE_COPY v_x v_y)]
	| step_table_init_trap : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (ELEM_REFS (fun_elem v_z v_y)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (TAB_REFS (fun_table v_z v_x))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]) [AI_TRAP]
	| step_table_init_zero : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		(~(Step_read_before_table_init_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]))) ->
		(v_n = 0) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]) []
	| step_table_init_succ : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx) (v_y : idx), 
		((fun_proj_uN_0 32 v_i) < (List.length (ELEM_REFS (fun_elem v_z v_y)))) ->
		(~(Step_read_before_table_init_succ (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_INIT v_x v_y)]) [(AI_CONST I32 v_j); ((lookup_total (ELEM_REFS (fun_elem v_z v_y)) (fun_proj_uN_0 32 v_i)) : admininstr); (AI_TABLE_SET v_x); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_j) + 1))); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_i) + 1))); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); (AI_TABLE_INIT v_x v_y)]
	| step_load_num_trap : forall (v_z : state) (v_i : (uN 32)) (v_nt : numtype) (v_ao : memarg), 
		((fun_size (v_nt : valtype)) <> None) ->
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((the (fun_size (v_nt : valtype))) : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD v_nt None v_ao)]) [AI_TRAP]
	| step_load_num_val : forall (v_z : state) (v_i : (uN 32)) (v_nt : numtype) (v_ao : memarg) (v_c : (num_ v_nt)), 
		((fun_size (v_nt : valtype)) <> None) ->
		((fun_nbytes_ v_nt v_c) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) ((((the (fun_size (v_nt : valtype))) : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD v_nt None v_ao)]) [(AI_CONST v_nt v_c)]
	| step_load_pack_trap_I32 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I32 : numtype) (Some (op_ _ (mk_sz v_n) v_sx)) v_ao)]) [AI_TRAP]
	| step_load_pack_trap_I64 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I64 : numtype) (Some (op_ _ (mk_sz v_n) v_sx)) v_ao)]) [AI_TRAP]
	| step_load_pack_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg) (v_c : (iN v_n)), 
		((fun_size (INN_I32 : valtype)) <> None) ->
		((fun_ibytes_ v_n v_c) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I32 : numtype) (Some (op_ _ (mk_sz v_n) v_sx)) v_ao)]) [(AI_CONST (INN_I32 : numtype) (fun_extend__ v_n (the (fun_size (INN_I32 : valtype))) v_sx v_c))]
	| step_load_pack_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg) (v_c : (iN v_n)), 
		((fun_size (INN_I64 : valtype)) <> None) ->
		((fun_ibytes_ v_n v_c) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I64 : numtype) (Some (op_ _ (mk_sz v_n) v_sx)) v_ao)]) [(AI_CONST (INN_I64 : numtype) (fun_extend__ v_n (the (fun_size (INN_I64 : valtype))) v_sx v_c))]
	| step_vload_oob : forall (v_z : state) (v_i : (uN 32)) (v_ao : memarg), 
		((fun_size VALTYPE_V128) <> None) ->
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((the (fun_size VALTYPE_V128)) : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 None v_ao)]) [AI_TRAP]
	| step_vload_val : forall (v_z : state) (v_i : (uN 32)) (v_ao : memarg) (v_c : (vec_ V128)), 
		((fun_size VALTYPE_V128) <> None) ->
		((fun_vbytes_ V128 v_c) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) ((((the (fun_size VALTYPE_V128)) : nat) / (8 : nat)) : nat))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 None v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_shape_oob : forall (v_z : state) (v_i : (uN 32)) (v_M : M) (v_N : res_N) (v_sx : sx) (v_ao : memarg), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((v_M * v_N) : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SHAPEX_ v_M v_N v_sx)) v_ao)]) [AI_TRAP]
	| step_vload_shape_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_M : M) (v_N : res_N) (v_sx : sx) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (list (iN v_M))) (v_k : (list nat)), 
		List.Forall2 (fun (v_j : (iN v_M)) (v_k : nat) => ((fun_ibytes_ v_M v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) (((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((v_k * v_M) : nat) / (8 : nat)) : nat)) (((v_M : nat) / (8 : nat)) : nat)))) (v_j) (v_k) ->
		((fun_jsize JNN_I32) = (v_M * 2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_N)) (List.map (fun (v_j : (iN v_M)) => (fun_extend__ v_M (fun_jsize JNN_I32) v_sx v_j)) v_j))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SHAPEX_ v_M v_N v_sx)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_shape_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_M : M) (v_N : res_N) (v_sx : sx) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (list (iN v_M))) (v_k : (list nat)), 
		List.Forall2 (fun (v_j : (iN v_M)) (v_k : nat) => ((fun_ibytes_ v_M v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) (((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((v_k * v_M) : nat) / (8 : nat)) : nat)) (((v_M : nat) / (8 : nat)) : nat)))) (v_j) (v_k) ->
		((fun_jsize JNN_I64) = (v_M * 2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_N)) (List.map (fun (v_j : (iN v_M)) => (fun_extend__ v_M (fun_jsize JNN_I64) v_sx v_j)) v_j))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SHAPEX_ v_M v_N v_sx)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_shape_val_I8 : forall (v_z : state) (v_i : (uN 32)) (v_M : M) (v_N : res_N) (v_sx : sx) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (list (iN v_M))) (v_k : (list nat)), 
		List.Forall2 (fun (v_j : (iN v_M)) (v_k : nat) => ((fun_ibytes_ v_M v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) (((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((v_k * v_M) : nat) / (8 : nat)) : nat)) (((v_M : nat) / (8 : nat)) : nat)))) (v_j) (v_k) ->
		((fun_jsize JNN_I8) = (v_M * 2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_N)) (List.map (fun (v_j : (iN v_M)) => (fun_extend__ v_M (fun_jsize JNN_I8) v_sx v_j)) v_j))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SHAPEX_ v_M v_N v_sx)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_shape_val_I16 : forall (v_z : state) (v_i : (uN 32)) (v_M : M) (v_N : res_N) (v_sx : sx) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (list (iN v_M))) (v_k : (list nat)), 
		List.Forall2 (fun (v_j : (iN v_M)) (v_k : nat) => ((fun_ibytes_ v_M v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) (((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((v_k * v_M) : nat) / (8 : nat)) : nat)) (((v_M : nat) / (8 : nat)) : nat)))) (v_j) (v_k) ->
		((fun_jsize JNN_I16) = (v_M * 2)) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_N)) (List.map (fun (v_j : (iN v_M)) => (fun_extend__ v_M (fun_jsize JNN_I16) v_sx v_j)) v_j))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SHAPEX_ v_M v_N v_sx)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_splat_oob : forall (v_z : state) (v_i : (uN 32)) (v_N : res_N) (v_ao : memarg), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_N : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SPLAT v_N)) v_ao)]) [AI_TRAP]
	| step_vload_splat_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_N : res_N) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I32)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_M)) [(mk_uN _ (fun_proj_uN_0 v_N v_j))])) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SPLAT v_N)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_splat_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_N : res_N) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I64)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_M)) [(mk_uN _ (fun_proj_uN_0 v_N v_j))])) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SPLAT v_N)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_splat_val_I8 : forall (v_z : state) (v_i : (uN 32)) (v_N : res_N) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I8)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_M)) [(mk_uN _ (fun_proj_uN_0 v_N v_j))])) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SPLAT v_N)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_splat_val_I16 : forall (v_z : state) (v_i : (uN 32)) (v_N : res_N) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I16)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_M)) [(mk_uN _ (fun_proj_uN_0 v_N v_j))])) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_SPLAT v_N)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_zero_oob : forall (v_z : state) (v_i : (uN 32)) (v_N : res_N) (v_ao : memarg), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_N : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_ZERO v_N)) v_ao)]) [AI_TRAP]
	| step_vload_zero_val : forall (v_z : state) (v_i : (uN 32)) (v_N : res_N) (v_ao : memarg) (v_c : (vec_ V128)) (v_j : (iN v_N)), 
		((fun_ibytes_ v_N v_j) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_c = (fun_extend__ v_N 128 U v_j)) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VLOAD V128 (Some (VLOAD_ZERO v_N)) v_ao)]) [(AI_VCONST V128 v_c)]
	| step_vload_lane_oob : forall (v_z : state) (v_i : (uN 32)) (v_c_1 : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_N : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c_1); (AI_VLOAD_LANE V128 (mk_sz v_N) v_ao v_j)]) [AI_TRAP]
	| step_vload_lane_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_c_1 : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_c : (vec_ V128)) (v_k : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_k) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I32)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_M)) (list_update_func (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_M)) v_c_1) (fun_proj_uN_0 8 v_j) (fun (_ : (uN 32)) => (mk_uN _ (fun_proj_uN_0 v_N v_k)))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c_1); (AI_VLOAD_LANE V128 (mk_sz v_N) v_ao v_j)]) [(AI_VCONST V128 v_c)]
	| step_vload_lane_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_c_1 : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_c : (vec_ V128)) (v_k : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_k) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I64)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_M)) (list_update_func (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_M)) v_c_1) (fun_proj_uN_0 8 v_j) (fun (_ : (uN 64)) => (mk_uN _ (fun_proj_uN_0 v_N v_k)))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c_1); (AI_VLOAD_LANE V128 (mk_sz v_N) v_ao v_j)]) [(AI_VCONST V128 v_c)]
	| step_vload_lane_val_I8 : forall (v_z : state) (v_i : (uN 32)) (v_c_1 : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_c : (vec_ V128)) (v_k : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_k) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I8)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_M)) (list_update_func (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_M)) v_c_1) (fun_proj_uN_0 8 v_j) (fun (_ : (uN 8)) => (mk_uN _ (fun_proj_uN_0 v_N v_k)))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c_1); (AI_VLOAD_LANE V128 (mk_sz v_N) v_ao v_j)]) [(AI_VCONST V128 v_c)]
	| step_vload_lane_val_I16 : forall (v_z : state) (v_i : (uN 32)) (v_c_1 : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_c : (vec_ V128)) (v_k : (iN v_N)) (v_M : M), 
		((fun_ibytes_ v_N v_k) = (list_slice (MEM_BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat))) ->
		(v_N = (fun_jsize JNN_I16)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		(v_c = (fun_inv_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_M)) (list_update_func (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_M)) v_c_1) (fun_proj_uN_0 8 v_j) (fun (_ : (uN 16)) => (mk_uN _ (fun_proj_uN_0 v_N v_k)))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c_1); (AI_VLOAD_LANE V128 (mk_sz v_N) v_ao v_j)]) [(AI_VCONST V128 v_c)]
	| step_memory_size : forall (v_z : state) (v_n : n), 
		(((v_n * 64) * fun_Ki) = (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [AI_MEMORY_SIZE]) [(AI_CONST I32 (mk_uN _ v_n))]
	| step_memory_fill_trap : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n), 
		(((fun_proj_uN_0 32 v_i) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]) [AI_TRAP]
	| step_memory_fill_zero : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n), 
		(~(Step_read_before_memory_fill_zero (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]))) ->
		(v_n = 0) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]) []
	| step_memory_fill_succ : forall (v_z : state) (v_i : (uN 32)) (v_val : val) (v_n : n), 
		(~(Step_read_before_memory_fill_succ (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_i); (v_val : admininstr); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_FILL]) [(AI_CONST I32 v_i); (v_val : admininstr); (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_i) + 1))); (v_val : admininstr); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); AI_MEMORY_FILL]
	| step_memory_copy_trap : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]) [AI_TRAP]
	| step_memory_copy_zero : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		(~(Step_read_before_memory_copy_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]))) ->
		(v_n = 0) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]) []
	| step_memory_copy_le : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		(~(Step_read_before_memory_copy_le (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]))) ->
		((fun_proj_uN_0 32 v_j) <= (fun_proj_uN_0 32 v_i)) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]) [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_LOAD I32 (Some (op_ _ (mk_sz 8) U)) fun_memarg0); (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_j) + 1))); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_i) + 1))); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); AI_MEMORY_COPY]
	| step_memory_copy_gt : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n), 
		(~(Step_read_before_memory_copy_gt (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_COPY]) [(AI_CONST I32 (mk_uN _ (((((fun_proj_uN_0 32 v_j) + v_n) : nat) - (1 : nat)) : nat))); (AI_CONST I32 (mk_uN _ (((((fun_proj_uN_0 32 v_i) + v_n) : nat) - (1 : nat)) : nat))); (AI_LOAD I32 (Some (op_ _ (mk_sz 8) U)) fun_memarg0); (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0); (AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); AI_MEMORY_COPY]
	| step_memory_init_trap : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx), 
		((((fun_proj_uN_0 32 v_i) + v_n) > (List.length (DATA_BYTES (fun_data v_z v_x)))) \/ (((fun_proj_uN_0 32 v_j) + v_n) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]) [AI_TRAP]
	| step_memory_init_zero : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx), 
		(~(Step_read_before_memory_init_zero (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]))) ->
		(v_n = 0) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]) []
	| step_memory_init_succ : forall (v_z : state) (v_j : (uN 32)) (v_i : (uN 32)) (v_n : n) (v_x : idx), 
		((fun_proj_uN_0 32 v_i) < (List.length (DATA_BYTES (fun_data v_z v_x)))) ->
		(~(Step_read_before_memory_init_succ (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]))) ->
		Step_read (mk_config v_z [(AI_CONST I32 v_j); (AI_CONST I32 v_i); (AI_CONST I32 (mk_uN _ v_n)); (AI_MEMORY_INIT v_x)]) [(AI_CONST I32 v_j); (AI_CONST I32 (mk_uN _ (fun_proj_byte_0 (lookup_total (DATA_BYTES (fun_data v_z v_x)) (fun_proj_uN_0 32 v_i))))); (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_j) + 1))); (AI_CONST I32 (mk_uN _ ((fun_proj_uN_0 32 v_i) + 1))); (AI_CONST I32 (mk_uN _ (((v_n : nat) - (1 : nat)) : nat))); (AI_MEMORY_INIT v_x)].

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.98 *)
(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.98 *)
Inductive Step: config -> config -> Prop :=
	| step_pure : forall (v_z : state) (v_admininstr : (list admininstr)) (v_admininstr' : (list admininstr)), 
		(Step_pure v_admininstr v_admininstr') ->
		Step (mk_config v_z v_admininstr) (mk_config v_z v_admininstr')
	| step_read : forall (v_z : state) (v_admininstr : (list admininstr)) (v_admininstr' : (list admininstr)), 
		(Step_read (mk_config v_z v_admininstr) v_admininstr') ->
		Step (mk_config v_z v_admininstr) (mk_config v_z v_admininstr')
	| step_ctxt_seq : forall (v_z : state) (v_val : (list val)) (v_admininstr : (list admininstr)) (v_admininstr'' : (list admininstr)) (v_z' : state) (v_admininstr' : (list admininstr)), 
		(Step (mk_config v_z v_admininstr) (mk_config v_z' v_admininstr')) ->
		Step (mk_config v_z ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ (v_admininstr ++ v_admininstr''))) (mk_config v_z' ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ (v_admininstr' ++ v_admininstr'')))
	| step_ctxt_label : forall (v_z : state) (v_n : n) (v_instr : (list instr)) (v_admininstr : (list admininstr)) (v_z' : state) (v_admininstr' : (list admininstr)), 
		(Step (mk_config v_z v_admininstr) (mk_config v_z' v_admininstr')) ->
		Step (mk_config v_z [(AI_LABEL_ v_n v_instr v_admininstr)]) (mk_config v_z' [(AI_LABEL_ v_n v_instr v_admininstr')])
	| step_ctxt_frame : forall (v_s : store) (v_f : frame) (v_n : n) (v_f' : frame) (v_admininstr : (list admininstr)) (v_s' : store) (v_admininstr' : (list admininstr)), 
		(Step (mk_config (mk_state v_s v_f') v_admininstr) (mk_config (mk_state v_s' v_f') v_admininstr')) ->
		Step (mk_config (mk_state v_s v_f) [(AI_FRAME_ v_n v_f' v_admininstr)]) (mk_config (mk_state v_s' v_f) [(AI_FRAME_ v_n v_f' v_admininstr')])
	| step_local_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (mk_config v_z [(v_val : admininstr); (AI_LOCAL_SET v_x)]) (mk_config (fun_with_local v_z v_x v_val) [])
	| step_global_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (mk_config v_z [(v_val : admininstr); (AI_GLOBAL_SET v_x)]) (mk_config (fun_with_global v_z v_x v_val) [])
	| step_table_set_trap : forall (v_z : state) (v_i : (uN 32)) (v_ref : ref) (v_x : idx), 
		((fun_proj_uN_0 32 v_i) >= (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (v_ref : admininstr); (AI_TABLE_SET v_x)]) (mk_config v_z [AI_TRAP])
	| step_table_set_val : forall (v_z : state) (v_i : (uN 32)) (v_ref : ref) (v_x : idx), 
		((fun_proj_uN_0 32 v_i) < (List.length (TAB_REFS (fun_table v_z v_x)))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (v_ref : admininstr); (AI_TABLE_SET v_x)]) (mk_config (fun_with_table v_z v_x (fun_proj_uN_0 32 v_i) v_ref) [])
	| step_table_grow_succeed : forall (v_z : state) (v_ref : ref) (v_n : n) (v_x : idx) (v_ti : tableinst), 
		((fun_growtable (fun_table v_z v_x) v_n v_ref) <> None) ->
		((the (fun_growtable (fun_table v_z v_x) v_n v_ref)) = v_ti) ->
		Step (mk_config v_z [(v_ref : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_GROW v_x)]) (mk_config (fun_with_tableinst v_z v_x v_ti) [(AI_CONST I32 (mk_uN _ (List.length (TAB_REFS (fun_table v_z v_x)))))])
	| step_table_grow_fail : forall (v_z : state) (v_ref : ref) (v_n : n) (v_x : idx), Step (mk_config v_z [(v_ref : admininstr); (AI_CONST I32 (mk_uN _ v_n)); (AI_TABLE_GROW v_x)]) (mk_config v_z [(AI_CONST I32 (mk_uN _ (fun_inv_signed_ 32 (0 - (1 : nat)))))])
	| step_elem_drop : forall (v_z : state) (v_x : idx), Step (mk_config v_z [(AI_ELEM_DROP v_x)]) (mk_config (fun_with_elem v_z v_x []) [])
	| step_store_num_trap : forall (v_z : state) (v_i : (uN 32)) (v_nt : numtype) (v_c : (num_ v_nt)) (v_ao : memarg), 
		((fun_size (v_nt : valtype)) <> None) ->
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((the (fun_size (v_nt : valtype))) : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST v_nt v_c); (AI_STORE v_nt None v_ao)]) (mk_config v_z [AI_TRAP])
	| step_store_num_val : forall (v_z : state) (v_i : (uN 32)) (v_nt : numtype) (v_c : (num_ v_nt)) (v_ao : memarg) (v_b : (list byte)), 
		((fun_size (v_nt : valtype)) <> None) ->
		(v_b = (fun_nbytes_ v_nt v_c)) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST v_nt v_c); (AI_STORE v_nt None v_ao)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) ((((the (fun_size (v_nt : valtype))) : nat) / (8 : nat)) : nat) v_b) [])
	| step_store_pack_trap_I32 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 32)) (v_n : n) (v_ao : memarg), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I32 : numtype) v_c); (AI_STORE (INN_I32 : numtype) (Some (mk_sz v_n)) v_ao)]) (mk_config v_z [AI_TRAP])
	| step_store_pack_trap_I64 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 64)) (v_n : n) (v_ao : memarg), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I64 : numtype) v_c); (AI_STORE (INN_I64 : numtype) (Some (mk_sz v_n)) v_ao)]) (mk_config v_z [AI_TRAP])
	| step_store_pack_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 32)) (v_n : n) (v_ao : memarg) (v_b : (list byte)), 
		((fun_size (INN_I32 : valtype)) <> None) ->
		(v_b = (fun_ibytes_ v_n (fun_wrap__ (the (fun_size (INN_I32 : valtype))) v_n v_c))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I32 : numtype) v_c); (AI_STORE (INN_I32 : numtype) (Some (mk_sz v_n)) v_ao)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat) v_b) [])
	| step_store_pack_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 64)) (v_n : n) (v_ao : memarg) (v_b : (list byte)), 
		((fun_size (INN_I64 : valtype)) <> None) ->
		(v_b = (fun_ibytes_ v_n (fun_wrap__ (the (fun_size (INN_I64 : valtype))) v_n v_c))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I64 : numtype) v_c); (AI_STORE (INN_I64 : numtype) (Some (mk_sz v_n)) v_ao)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat) v_b) [])
	| step_vstore_oob : forall (v_z : state) (v_i : (uN 32)) (v_c : (vec_ V128)) (v_ao : memarg), 
		((fun_size VALTYPE_V128) <> None) ->
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((the (fun_size VALTYPE_V128)) : nat) / (8 : nat)) : nat)) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c); (AI_VSTORE V128 v_ao)]) (mk_config v_z [AI_TRAP])
	| step_vstore_val : forall (v_z : state) (v_i : (uN 32)) (v_c : (vec_ V128)) (v_ao : memarg) (v_b : (list byte)), 
		((fun_size VALTYPE_V128) <> None) ->
		(v_b = (fun_vbytes_ V128 v_c)) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c); (AI_VSTORE V128 v_ao)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) ((((the (fun_size VALTYPE_V128)) : nat) / (8 : nat)) : nat) v_b) [])
	| step_vstore_lane_oob : forall (v_z : state) (v_i : (uN 32)) (v_c : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx), 
		((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + v_N) > (List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c); (AI_VSTORE_LANE V128 (mk_sz v_N) v_ao v_j)]) (mk_config v_z [AI_TRAP])
	| step_vstore_lane_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_c : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_b : (list byte)) (v_M : M), 
		(v_N = (fun_jsize JNN_I32)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		((fun_proj_uN_0 8 v_j) < (List.length (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_M)) v_c))) ->
		(v_b = (fun_ibytes_ v_N (mk_uN _ (fun_proj_uN_0 32 (lookup_total (fun_lanes_ (X (JNN_I32 : lanetype) (mk_dim v_M)) v_c) (fun_proj_uN_0 8 v_j)))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c); (AI_VSTORE_LANE V128 (mk_sz v_N) v_ao v_j)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat) v_b) [])
	| step_vstore_lane_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_c : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_b : (list byte)) (v_M : M), 
		(v_N = (fun_jsize JNN_I64)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		((fun_proj_uN_0 8 v_j) < (List.length (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_M)) v_c))) ->
		(v_b = (fun_ibytes_ v_N (mk_uN _ (fun_proj_uN_0 64 (lookup_total (fun_lanes_ (X (JNN_I64 : lanetype) (mk_dim v_M)) v_c) (fun_proj_uN_0 8 v_j)))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c); (AI_VSTORE_LANE V128 (mk_sz v_N) v_ao v_j)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat) v_b) [])
	| step_vstore_lane_val_I8 : forall (v_z : state) (v_i : (uN 32)) (v_c : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_b : (list byte)) (v_M : M), 
		(v_N = (fun_jsize JNN_I8)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		((fun_proj_uN_0 8 v_j) < (List.length (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_M)) v_c))) ->
		(v_b = (fun_ibytes_ v_N (mk_uN _ (fun_proj_uN_0 8 (lookup_total (fun_lanes_ (X (JNN_I8 : lanetype) (mk_dim v_M)) v_c) (fun_proj_uN_0 8 v_j)))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c); (AI_VSTORE_LANE V128 (mk_sz v_N) v_ao v_j)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat) v_b) [])
	| step_vstore_lane_val_I16 : forall (v_z : state) (v_i : (uN 32)) (v_c : (vec_ V128)) (v_N : res_N) (v_ao : memarg) (v_j : laneidx) (v_b : (list byte)) (v_M : M), 
		(v_N = (fun_jsize JNN_I16)) ->
		((v_M : nat) = ((128 : nat) / (v_N : nat))) ->
		((fun_proj_uN_0 8 v_j) < (List.length (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_M)) v_c))) ->
		(v_b = (fun_ibytes_ v_N (mk_uN _ (fun_proj_uN_0 16 (lookup_total (fun_lanes_ (X (JNN_I16 : lanetype) (mk_dim v_M)) v_c) (fun_proj_uN_0 8 v_j)))))) ->
		Step (mk_config v_z [(AI_CONST I32 v_i); (AI_VCONST V128 v_c); (AI_VSTORE_LANE V128 (mk_sz v_N) v_ao v_j)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_N : nat) / (8 : nat)) : nat) v_b) [])
	| step_memory_grow_succeed : forall (v_z : state) (v_n : n) (v_mi : meminst), 
		((fun_growmemory (fun_mem v_z (mk_uN _ 0)) v_n) <> None) ->
		((the (fun_growmemory (fun_mem v_z (mk_uN _ 0)) v_n)) = v_mi) ->
		Step (mk_config v_z [(AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_GROW]) (mk_config (fun_with_meminst v_z (mk_uN _ 0) v_mi) [(AI_CONST I32 (mk_uN _ ((((List.length (MEM_BYTES (fun_mem v_z (mk_uN _ 0)))) : nat) / ((64 * fun_Ki) : nat)) : nat)))])
	| step_memory_grow_fail : forall (v_z : state) (v_n : n), Step (mk_config v_z [(AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_GROW]) (mk_config v_z [(AI_CONST I32 (mk_uN _ (fun_inv_signed_ 32 (0 - (1 : nat)))))])
	| step_data_drop : forall (v_z : state) (v_x : idx), Step (mk_config v_z [(AI_DATA_DROP v_x)]) (mk_config (fun_with_data v_z v_x []) []).

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.99 *)
(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.99 *)
Inductive Steps: config -> config -> Prop :=
	| steps_refl : forall (v_z : state) (v_admininstr : (list admininstr)), Steps (mk_config v_z v_admininstr) (mk_config v_z v_admininstr)
	| steps_trans : forall (v_z : state) (v_admininstr : (list admininstr)) (v_z'' : state) (v_admininstr'' : (list admininstr)) (v_z' : state) (v_admininstr' : (list admininstr)), 
		(Step (mk_config v_z v_admininstr) (mk_config v_z' v_admininstr')) ->
		(Steps (mk_config v_z' v_admininstr') (mk_config v_z'' v_admininstr'')) ->
		Steps (mk_config v_z v_admininstr) (mk_config v_z'' v_admininstr'').

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 *)
Inductive Eval_expr: state -> expr -> state -> (list val) -> Prop :=
	| mk_Eval_expr : forall (v_z : state) (v_instr : (list instr)) (v_z' : state) (v_val : (list val)), 
		(Steps (mk_config v_z (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)) (mk_config v_z' (List.map (fun (v_val : val) => (v_val : admininstr)) v_val))) ->
		Eval_expr v_z v_instr v_z' v_val.

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:5.1-5.36 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:5.1-5.36 *)
Axiom fun_funcs : forall (var_0 : (list externaddr)), (list funcaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:11.1-11.40 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:11.1-11.40 *)
Axiom fun_globals : forall (var_0 : (list externaddr)), (list globaladdr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:17.1-17.38 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:17.1-17.38 *)
Axiom fun_tables : forall (var_0 : (list externaddr)), (list tableaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:23.1-23.34 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:23.1-23.34 *)
Axiom fun_mems : forall (var_0 : (list externaddr)), (list memaddr).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:36.1-36.60 *)
Axiom fun_allocfunc : forall (v_store : store) (v_moduleinst : moduleinst) (v_func : func), (prod store funcaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
Axiom fun_allocfuncs : forall (v_store : store) (v_moduleinst : moduleinst) (var_0 : (list func)), (prod store (list funcaddr)).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:47.1-47.63 *)
Axiom fun_allocglobal : forall (v_store : store) (v_globaltype : globaltype) (v_val : val), (prod store globaladdr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
Axiom fun_allocglobals : forall (v_store : store) (var_0 : (list globaltype)) (var_1 : (list val)), (prod store (list globaladdr)).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:57.1-57.55 *)
Axiom fun_alloctable : forall (v_store : store) (v_tabletype : tabletype), (prod store tableaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
Axiom fun_alloctables : forall (v_store : store) (var_0 : (list tabletype)), (prod store (list tableaddr)).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:67.1-67.49 *)
Axiom fun_allocmem : forall (v_store : store) (v_memtype : memtype), (prod store memaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
Axiom fun_allocmems : forall (v_store : store) (var_0 : (list memtype)), (prod store (list memaddr)).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:77.1-77.57 *)
Axiom fun_allocelem : forall (v_store : store) (v_reftype : reftype) (var_0 : (list ref)), (prod store elemaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
Axiom fun_allocelems : forall (v_store : store) (var_0 : (list reftype)) (var_1 : (list (list ref))), (prod store (list elemaddr)).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:87.1-87.49 *)
Axiom fun_allocdata : forall (v_store : store) (var_0 : (list byte)), (prod store dataaddr).

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
Axiom fun_allocdatas : forall (v_store : store) (var_0 : (list (list byte))), (prod store (list dataaddr)).

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 *)
Definition fun_instexport (var_0 : (list funcaddr)) (var_1 : (list globaladdr)) (var_2 : (list tableaddr)) (var_3 : (list memaddr)) (v_export : export) : exportinst :=
	match var_0, var_1, var_2, var_3, v_export return exportinst with
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_FUNC v_x)) => {| NAME := v_name; ADDR := (EXTADDR_FUNC (lookup_total v_fa (fun_proj_uN_0 32 v_x))) |}
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_GLOBAL v_x)) => {| NAME := v_name; ADDR := (EXTADDR_GLOBAL (lookup_total v_ga (fun_proj_uN_0 32 v_x))) |}
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_TABLE v_x)) => {| NAME := v_name; ADDR := (EXTADDR_TABLE (lookup_total v_ta (fun_proj_uN_0 32 v_x))) |}
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_MEM v_x)) => {| NAME := v_name; ADDR := (EXTADDR_MEM (lookup_total v_ma (fun_proj_uN_0 32 v_x))) |}
	end.

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:107.1-107.82 *)
Axiom fun_allocmodule : forall (v_store : store) (v_module : module) (var_0 : (list externaddr)) (var_1 : (list val)) (var_2 : (list (list ref))), (prod store moduleinst).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:154.1-154.33 *)
Axiom fun_runelem : forall (v_elem : elem) (v_idx : idx), (list instr).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:161.1-161.33 *)
Axiom fun_rundata : forall (v_data : data) (v_idx : idx), (list instr).

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:167.1-167.54 *)
Axiom fun_instantiate : forall (v_store : store) (v_module : module) (var_0 : (list externaddr)), config.

(* Axiom Definition at: ../specification/wasm-2.0/9-module.spectec:196.1-196.44 *)
Axiom fun_invoke : forall (v_store : store) (v_funcaddr : funcaddr) (var_0 : (list val)), config.

(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:20.1-22.82 *)
(* Mutual Recursion at: ../specification/wasm-2.0/A-binary.spectec:738.1-748.59 *)
(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:845.1-845.43 *)
Definition startopt := (list start).

Definition startopt_eq_dec : forall (v1 v2 : startopt),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition startopt_eqb (v1 v2 : startopt) : bool :=
	is_left(startopt_eq_dec v1 v2).
Definition eqstartoptP : Equality.axiom (startopt_eqb) :=
	eq_dec_Equality_axiom (startopt) (startopt_eq_dec).

HB.instance Definition _ := hasDecEq.Build (startopt) (eqstartoptP).
Hint Resolve startopt_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:880.1-880.29 *)
Definition code := (prod (list local) expr).

Definition code_eq_dec : forall (v1 v2 : code),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition code_eqb (v1 v2 : code) : bool :=
	is_left(code_eq_dec v1 v2).
Definition eqcodeP : Equality.axiom (code_eqb) :=
	eq_dec_Equality_axiom (code) (code_eq_dec).

HB.instance Definition _ := hasDecEq.Build (code) (eqcodeP).
Hint Resolve code_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:911.1-911.33 *)
Definition nopt := (list u32).

Definition nopt_eq_dec : forall (v1 v2 : nopt),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition nopt_eqb (v1 v2 : nopt) : bool :=
	is_left(nopt_eq_dec v1 v2).
Definition eqnoptP : Equality.axiom (nopt_eqb) :=
	eq_dec_Equality_axiom (nopt) (nopt_eq_dec).

HB.instance Definition _ := hasDecEq.Build (nopt) (eqnoptP).
Hint Resolve nopt_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:7.1-7.85 *)
Inductive Externaddrs_ok: store -> externaddr -> externtype -> Prop :=
	| extaddr_ok_func : forall (v_S : store) (v_a : addr) (v_ext : functype) (v_minst : moduleinst) (v_func : func), 
		(v_a < (List.length (FUNCS v_S))) ->
		((lookup_total (FUNCS v_S) v_a) = {| FUNC_TYPE := v_ext; FUNC_MODULE := v_minst; FUNC_CODE := v_func |}) ->
		Externaddrs_ok v_S (EXTADDR_FUNC v_a) (EXT_FUNC v_ext)
	| extaddr_ok_table : forall (v_S : store) (v_a : addr) (v_tt : tabletype) (v_tt' : tabletype) (v_ref : (list ref)), 
		(v_a < (List.length (TABLES v_S))) ->
		((lookup_total (TABLES v_S) v_a) = {| TAB_TYPE := v_tt'; TAB_REFS := v_ref |}) ->
		(Tabletype_sub v_tt' v_tt) ->
		Externaddrs_ok v_S (EXTADDR_TABLE v_a) (EXT_TABLE v_tt)
	| extaddr_ok_mem : forall (v_S : store) (v_a : addr) (v_mt : memtype) (v_mt' : memtype) (v_b : (list byte)), 
		(v_a < (List.length (MEMS v_S))) ->
		((lookup_total (MEMS v_S) v_a) = {| MEM_TYPE := v_mt'; MEM_BYTES := v_b |}) ->
		(Memtype_sub v_mt' v_mt) ->
		Externaddrs_ok v_S (EXTADDR_MEM v_a) (EXT_MEM v_mt)
	| extaddr_ok_global : forall (v_S : store) (v_a : addr) (v_mut : mut) (v_valtype : valtype) (v_val : val), 
		(v_a < (List.length (GLOBALS v_S))) ->
		((lookup_total (GLOBALS v_S) v_a) = {| GLOB_TYPE := (mk_globaltype v_mut v_valtype); GLOB_VALUE := v_val |}) ->
		Externaddrs_ok v_S (EXTADDR_GLOBAL v_a) (EXT_GLOBAL (mk_globaltype v_mut v_valtype)).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:29.1-29.59 *)
Inductive Ref_ok: store -> ref -> reftype -> Prop :=
	| ok_null : forall (v_S : store) (v_rt : reftype), Ref_ok v_S (REF_NULL v_rt) v_rt
	| ok_func : forall (v_S : store) (v_a : addr) (v_ext : functype), 
		(Externaddrs_ok v_S (EXTADDR_FUNC v_a) (EXT_FUNC v_ext)) ->
		Ref_ok v_S (REF_FUNC_ADDR v_a) FUNCREF
	| ok_extern : forall (v_S : store) (v_a : addr), Ref_ok v_S (REF_HOST_ADDR v_a) EXTERNREF.

(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:43.1-43.59 *)
Definition fun_coec_ref__val (v_ref : ref) : val :=
	match v_ref return val with
		| (REF_NULL v_0) => (VAL_REF_NULL v_0)
		| (REF_FUNC_ADDR v_0) => (VAL_REF_FUNC_ADDR v_0)
		| (REF_HOST_ADDR v_0) => (VAL_REF_HOST_ADDR v_0)
	end.

(* Type Coercion Definition at: ../specification/wasm-2.0/B-soundness.spectec:43.1-43.59 *)
Coercion fun_coec_ref__val : ref >-> val.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:43.1-43.59 *)
Inductive Val_ok: store -> val -> valtype -> Prop :=
	| ok_numtype : forall (v_S : store) (v_nt : numtype) (v_c_t : (num_ v_nt)), Val_ok v_S (VAL_CONST v_nt v_c_t) (v_nt : valtype)
	| ok_vectype : forall (v_S : store) (v_vt : vectype) (v_c_t : (vec_ v_vt)), Val_ok v_S (VAL_VCONST v_vt v_c_t) (v_vt : valtype)
	| ok_reftype : forall (v_S : store) (v_r : ref) (v_rt : reftype), 
		(Ref_ok v_S v_r v_rt) ->
		Val_ok v_S (v_r : val) (v_rt : valtype).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:57.1-57.66 *)
Inductive Result_ok: store -> result -> (list valtype) -> Prop :=
	| ok_result : forall (v_S : store) (v_v : (list val)) (v_t : (list valtype)), 
		((List.length v_t) = (List.length v_v)) ->
		List.Forall2 (fun (v_t : valtype) (v_v : val) => (Val_ok v_S v_v v_t)) (v_t) (v_v) ->
		Result_ok v_S (_VALS v_v) v_t
	| ok_trap : forall (v_S : store) (v_t : (list valtype)), Result_ok v_S TRAP v_t.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:69.1-69.56 *)
Inductive Memory_instance_ok: store -> meminst -> memtype -> Prop :=
	| mk_Memory_instance_ok : forall (v_S : store) (v_mt : memtype) (v_b : (list byte)) (v_n : n) (v_m : m), 
		(v_mt = (PAGE (mk_limits (mk_uN _ v_n) (mk_uN _ v_m)))) ->
		((List.length v_b) = ((v_n * 64) * fun_Ki)) ->
		(Memtype_ok v_mt) ->
		Memory_instance_ok v_S {| MEM_TYPE := v_mt; MEM_BYTES := v_b |} v_mt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:79.1-79.59 *)
Inductive Table_instance_ok: store -> tableinst -> tabletype -> Prop :=
	| mk_Table_instance_ok : forall (v_S : store) (v_tt : tabletype) (v_ref : (list ref)) (v_n : n) (v_m : m) (v_rt : reftype) (v_fa : (list (option funcaddr))) (v_functype : (list (option functype))), 
		(v_tt = (mk_tabletype (mk_limits (mk_uN _ v_n) (mk_uN _ v_m)) v_rt)) ->
		((List.length v_fa) = (List.length v_functype)) ->
		List.Forall2 (fun (v_fa : (option funcaddr)) (v_functype : (option functype)) => ((v_fa = None) <-> (v_functype = None))) (v_fa) (v_functype) ->
		List.Forall2 (fun (v_fa : (option funcaddr)) (v_functype : (option functype)) => List.Forall2 (fun (v_fa : funcaddr) (v_functype : functype) => (Externaddrs_ok v_S (EXTADDR_FUNC v_fa) (EXT_FUNC v_functype))) (option_to_list v_fa) (option_to_list v_functype)) (v_fa) (v_functype) ->
		(Tabletype_ok v_tt) ->
		Table_instance_ok v_S {| TAB_TYPE := v_tt; TAB_REFS := v_ref |} v_tt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:89.1-89.62 *)
Inductive Global_instance_ok: store -> globalinst -> globaltype -> Prop :=
	| mk_Global_instance_ok : forall (v_S : store) (v_gt : globaltype) (v_v : val) (v_mut : mut) (v_vt : vectype), 
		(v_gt = (mk_globaltype v_mut (v_vt : valtype))) ->
		(Globaltype_ok v_gt) ->
		(Val_ok v_S v_v (v_vt : valtype)) ->
		Global_instance_ok v_S {| GLOB_TYPE := v_gt; GLOB_VALUE := v_v |} v_gt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:99.1-99.54 *)
Inductive Export_instance_ok: store -> exportinst -> Prop :=
	| mk_Export_instance_ok : forall (v_S : store) (v_name : name) (v_eaddr : externaddr) (v_ext : externtype), 
		(Externaddrs_ok v_S v_eaddr v_ext) ->
		Export_instance_ok v_S {| NAME := v_name; ADDR := v_eaddr |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:107.1-107.58 *)
Inductive Element_instance_ok: store -> eleminst -> reftype -> Prop :=
	| mk_Element_instance_ok : forall (v_S : store) (v_rt : reftype) (v_ref : (list ref)), 
		List.Forall (fun (v_ref : ref) => (Ref_ok v_S v_ref v_rt)) (v_ref) ->
		Element_instance_ok v_S {| ELEM_TYPE := v_rt; ELEM_REFS := v_ref |} v_rt.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:115.1-115.50 *)
Inductive Data_instance_ok: store -> datainst -> Prop :=
	| mk_Data_instance_ok : forall (v_S : store) (v_b : (list byte)), Data_instance_ok v_S {| DATA_BYTES := v_b |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:122.1-122.59 *)
Inductive Module_instance_ok: store -> moduleinst -> context -> Prop :=
	| mk_Module_instance_ok : forall (v_S : store) (v_functype : (list functype)) (v_funcaddr : (list funcaddr)) (v_globaladdr : (list globaladdr)) (v_tableaddr : (list tableaddr)) (v_memaddr : (list memaddr)) (v_elemaddr : (list elemaddr)) (v_dataaddr : (list dataaddr)) (v_exportinst : (list exportinst)) (v_functype' : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)) (v_reftype : (list reftype)), 
		List.Forall (fun (v_functype : functype) => (Functype_ok v_functype)) (v_functype) ->
		((List.length v_funcaddr) = (List.length v_functype')) ->
		List.Forall2 (fun (v_funcaddr : funcaddr) (v_functype' : functype) => (Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_functype'))) (v_funcaddr) (v_functype') ->
		((List.length v_tableaddr) = (List.length v_tabletype)) ->
		List.Forall2 (fun (v_tableaddr : tableaddr) (v_tabletype : tabletype) => (Externaddrs_ok v_S (EXTADDR_TABLE v_tableaddr) (EXT_TABLE v_tabletype))) (v_tableaddr) (v_tabletype) ->
		((List.length v_memaddr) = (List.length v_memtype)) ->
		List.Forall2 (fun (v_memaddr : memaddr) (v_memtype : memtype) => (Externaddrs_ok v_S (EXTADDR_MEM v_memaddr) (EXT_MEM v_memtype))) (v_memaddr) (v_memtype) ->
		((List.length v_globaladdr) = (List.length v_globaltype)) ->
		List.Forall2 (fun (v_globaladdr : globaladdr) (v_globaltype : globaltype) => (Externaddrs_ok v_S (EXTADDR_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype))) (v_globaladdr) (v_globaltype) ->
		((List.length v_elemaddr) = (List.length v_reftype)) ->
		List.Forall (fun (v_elemaddr : nat) => (v_elemaddr < (List.length (ELEMS v_S)))) (v_elemaddr) ->
		List.Forall2 (fun (v_elemaddr : nat) (v_reftype : reftype) => (Element_instance_ok v_S (lookup_total (ELEMS v_S) v_elemaddr) v_reftype)) (v_elemaddr) (v_reftype) ->
		List.Forall (fun (v_dataaddr : nat) => (v_dataaddr < (List.length (DATAS v_S)))) (v_dataaddr) ->
		List.Forall (fun (v_dataaddr : nat) => (Data_instance_ok v_S (lookup_total (DATAS v_S) v_dataaddr))) (v_dataaddr) ->
		List.Forall (fun (v_exportinst : exportinst) => (Export_instance_ok v_S v_exportinst)) (v_exportinst) ->
		Module_instance_ok v_S {| MODULE_TYPES := v_functype; MODULE_FUNCS := v_funcaddr; MODULE_GLOBALS := v_globaladdr; MODULE_TABLES := v_tableaddr; MODULE_MEMS := v_memaddr; MODULE_ELEMS := v_elemaddr; MODULE_DATAS := v_dataaddr; MODULE_EXPORTS := v_exportinst |} {| C_TYPES := v_functype; C_FUNCS := v_functype'; C_GLOBALS := v_globaltype; C_TABLES := v_tabletype; C_MEMS := v_memtype; C_ELEMS := v_reftype; C_DATAS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := None |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:139.1-139.60 *)
Inductive Function_instance_ok: store -> funcinst -> functype -> Prop :=
	| mk_Function_instance_ok : forall (v_S : store) (v_functype : functype) (v_moduleinst : moduleinst) (v_func : func) (v_C : context), 
		(Functype_ok v_functype) ->
		(Module_instance_ok v_S v_moduleinst v_C) ->
		(Func_ok v_C v_func v_functype) ->
		Function_instance_ok v_S {| FUNC_TYPE := v_functype; FUNC_MODULE := v_moduleinst; FUNC_CODE := v_func |} v_functype.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:149.1-149.33 *)
Inductive Store_ok: store -> Prop :=
	| mk_Store_ok : forall (v_S : store) (v_funcinst : (list funcinst)) (v_globalinst : (list globalinst)) (v_tableinst : (list tableinst)) (v_meminst : (list meminst)) (v_eleminst : (list eleminst)) (v_datainst : (list datainst)) (v_functype : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)) (v_reftype : (list reftype)), 
		(v_S = {| FUNCS := v_funcinst; GLOBALS := v_globalinst; TABLES := v_tableinst; MEMS := v_meminst; ELEMS := v_eleminst; DATAS := v_datainst |}) ->
		((List.length v_funcinst) = (List.length v_functype)) ->
		List.Forall2 (fun (v_funcinst : funcinst) (v_functype : functype) => (Function_instance_ok v_S v_funcinst v_functype)) (v_funcinst) (v_functype) ->
		((List.length v_globalinst) = (List.length v_globaltype)) ->
		List.Forall2 (fun (v_globalinst : globalinst) (v_globaltype : globaltype) => (Global_instance_ok v_S v_globalinst v_globaltype)) (v_globalinst) (v_globaltype) ->
		((List.length v_tableinst) = (List.length v_tabletype)) ->
		List.Forall2 (fun (v_tableinst : tableinst) (v_tabletype : tabletype) => (Table_instance_ok v_S v_tableinst v_tabletype)) (v_tableinst) (v_tabletype) ->
		((List.length v_meminst) = (List.length v_memtype)) ->
		List.Forall2 (fun (v_meminst : meminst) (v_memtype : memtype) => (Memory_instance_ok v_S v_meminst v_memtype)) (v_meminst) (v_memtype) ->
		((List.length v_eleminst) = (List.length v_reftype)) ->
		List.Forall2 (fun (v_eleminst : eleminst) (v_reftype : reftype) => (Element_instance_ok v_S v_eleminst v_reftype)) (v_eleminst) (v_reftype) ->
		List.Forall (fun (v_datainst : datainst) => (Data_instance_ok v_S v_datainst)) (v_datainst) ->
		Store_ok v_S.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:240.1-240.44 *)
Inductive Frame_ok: store -> frame -> context -> Prop :=
	| mk_Frame_ok : forall (v_S : store) (v_val : (list val)) (v_moduleinst : moduleinst) (v_C : context) (v_t : (list valtype)), 
		(Module_instance_ok v_S v_moduleinst v_C) ->
		((List.length v_t) = (List.length v_val)) ->
		List.Forall2 (fun (v_t : valtype) (v_val : val) => (Val_ok v_S v_val v_t)) (v_t) (v_val) ->
		Frame_ok v_S {| F_LOCALS := v_val; F_MODULE := v_moduleinst |} ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := v_t; C_LABELS := []; C_RETURN := None |} @@ v_C).

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:164.1-166.75 *)
(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:164.1-164.87 *)
Inductive Admin_instr_ok: store -> context -> admininstr -> functype -> Prop :=
	| AI_ok_instr : forall (v_S : store) (v_C : context) (v_instr : instr) (v_functype : functype), 
		(Instr_ok v_C v_instr v_functype) ->
		Admin_instr_ok v_S v_C (v_instr : admininstr) v_functype
	| AI_ok_trap : forall (v_S : store) (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Admin_instr_ok v_S v_C AI_TRAP (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))
	| AI_ok_ref_extern : forall (v_S : store) (v_C : context) (v_hostaddr : hostaddr), Admin_instr_ok v_S v_C (AI_REF_HOST_ADDR v_hostaddr) (mk_functype (mk_list _ []) (mk_list _ [VALTYPE_EXTERNREF]))
	| AI_ok_ref : forall (v_S : store) (v_C : context) (v_funcaddr : funcaddr) (v_functype : functype), 
		(Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_functype)) ->
		Admin_instr_ok v_S v_C (AI_REF_FUNC_ADDR v_funcaddr) (mk_functype (mk_list _ []) (mk_list _ [VALTYPE_FUNCREF]))
	| AI_ok_call_addr : forall (v_S : store) (v_C : context) (v_funcaddr : funcaddr) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2)))) ->
		Admin_instr_ok v_S v_C (AI_CALL_ADDR v_funcaddr) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))
	| AI_ok_label : forall (v_S : store) (v_C : context) (v_n : n) (v_instr : (list instr)) (v_admininstr : (list admininstr)) (v_t_2 : (list valtype)) (v_t_1 : (list valtype)), 
		(Instrs_ok v_C v_instr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Admin_instrs_ok v_S ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := [(mk_list _ v_t_1)]; C_RETURN := None |} @@ v_C) v_admininstr (mk_functype (mk_list _ []) (mk_list _ v_t_2))) ->
		(v_n = (List.length v_t_1)) ->
		Admin_instr_ok v_S v_C (AI_LABEL_ v_n v_instr v_admininstr) (mk_functype (mk_list _ []) (mk_list _ v_t_2))
	| AI_ok_frame : forall (v_S : store) (v_C : context) (v_n : n) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (list valtype)), 
		(Thread_ok v_S (Some (mk_list _ v_t)) v_F v_admininstr (mk_list _ v_t)) ->
		(v_n = (List.length v_t)) ->
		Admin_instr_ok v_S v_C (AI_FRAME_ v_n v_F v_admininstr) (mk_functype (mk_list _ []) (mk_list _ v_t))
	| AI_ok_weakening : forall (v_S : store) (v_C : context) (v_admininstr : admininstr) (v_t' : (list valtype)) (v_t'_1 : (list valtype)) (v_t : (list valtype)) (v_t'_2 : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Admin_instr_ok v_S v_C v_admininstr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Resulttype_sub (mk_list _ v_t') (mk_list _ v_t)) ->
		(Resulttype_sub (mk_list _ v_t'_1) (mk_list _ v_t_1)) ->
		(Resulttype_sub (mk_list _ v_t_2) (mk_list _ v_t'_2)) ->
		Admin_instr_ok v_S v_C v_admininstr (mk_functype (mk_list _ (v_t' ++ v_t'_1)) (mk_list _ (v_t ++ v_t'_2)))

with

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:165.1-165.90 *)
Admin_instrs_ok: store -> context -> (list admininstr) -> functype -> Prop :=
	| AIs_ok_empty : forall (v_S : store) (v_C : context), Admin_instrs_ok v_S v_C [] (mk_functype (mk_list _ []) (mk_list _ []))
	| AIs_ok_seq : forall (v_S : store) (v_C : context) (v_admininstr_1 : (list admininstr)) (v_admininstr_2 : admininstr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), 
		(Admin_instrs_ok v_S v_C v_admininstr_1 (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Admin_instr_ok v_S v_C v_admininstr_2 (mk_functype (mk_list _ v_t_2) (mk_list _ v_t_3))) ->
		Admin_instrs_ok v_S v_C (v_admininstr_1 ++ [v_admininstr_2]) (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_3))
	| AIs_ok_sub : forall (v_S : store) (v_C : context) (v_admininstr : (list admininstr)) (v_t'_1 : (list valtype)) (v_t'_2 : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Admin_instrs_ok v_S v_C v_admininstr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		(Resulttype_sub (mk_list _ v_t'_1) (mk_list _ v_t_1)) ->
		(Resulttype_sub (mk_list _ v_t_2) (mk_list _ v_t'_2)) ->
		Admin_instrs_ok v_S v_C v_admininstr (mk_functype (mk_list _ v_t'_1) (mk_list _ v_t'_2))
	| AIs_ok_frame : forall (v_S : store) (v_C : context) (v_admininstr : (list admininstr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), 
		(Admin_instrs_ok v_S v_C v_admininstr (mk_functype (mk_list _ v_t_1) (mk_list _ v_t_2))) ->
		Admin_instrs_ok v_S v_C v_admininstr (mk_functype (mk_list _ (v_t ++ v_t_1)) (mk_list _ (v_t ++ v_t_2)))
	| AIs_ok_instrs : forall (v_S : store) (v_C : context) (v_instr : (list instr)) (v_functype : functype), 
		(Instrs_ok v_C v_instr v_functype) ->
		Admin_instrs_ok v_S v_C (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr) v_functype

with

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:166.1-166.75 *)
Thread_ok: store -> (option resulttype) -> frame -> (list admininstr) -> resulttype -> Prop :=
	| mk_Thread_ok : forall (v_S : store) (v_resulttype : (option resulttype)) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (list valtype)) (v_C : context), 
		(Frame_ok v_S v_F v_C) ->
		(Admin_instrs_ok v_S ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := v_resulttype |} @@ v_C) v_admininstr (mk_functype (mk_list _ []) (mk_list _ v_t))) ->
		Thread_ok v_S v_resulttype v_F v_admininstr (mk_list _ v_t).

(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:195.1-195.32 *)
Definition fun_optionSize (var_0 : (option valtype)) : nat :=
	match var_0 return nat with
		| (Some v_valtype) => 1
		| None => 0
	end.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:252.1-252.43 *)
Inductive Config_ok: config -> resulttype -> Prop :=
	| mk_Config_ok : forall (v_S : store) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (list valtype)), 
		(Store_ok v_S) ->
		(Thread_ok v_S None v_F v_admininstr (mk_list _ v_t)) ->
		Config_ok (mk_config (mk_state v_S v_F) v_admininstr) (mk_list _ v_t).

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:263.1-263.48 *)
Inductive Func_extension: funcinst -> funcinst -> Prop :=
	| mk_Func_extension : forall (v_funcinst : funcinst), Func_extension v_funcinst v_funcinst.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:264.1-264.51 *)
Inductive Table_extension: tableinst -> tableinst -> Prop :=
	| mk_Table_extension : forall (v_n1 : u32) (v_m : m) (v_rt : reftype) (v_ref_1 : (list ref)) (v_n2 : u32) (v_ref_2 : (list ref)), 
		((fun_proj_uN_0 32 v_n1) <= (fun_proj_uN_0 32 v_n2)) ->
		Table_extension {| TAB_TYPE := (mk_tabletype (mk_limits v_n1 (mk_uN _ v_m)) v_rt); TAB_REFS := v_ref_1 |} {| TAB_TYPE := (mk_tabletype (mk_limits v_n2 (mk_uN _ v_m)) v_rt); TAB_REFS := v_ref_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:265.1-265.45 *)
Inductive Mem_extension: meminst -> meminst -> Prop :=
	| mk_Mem_extension : forall (v_n1 : u32) (v_m : m) (v_b_1 : (list byte)) (v_n2 : u32) (v_b_2 : (list byte)), 
		((fun_proj_uN_0 32 v_n1) <= (fun_proj_uN_0 32 v_n2)) ->
		Mem_extension {| MEM_TYPE := (PAGE (mk_limits v_n1 (mk_uN _ v_m))); MEM_BYTES := v_b_1 |} {| MEM_TYPE := (PAGE (mk_limits v_n2 (mk_uN _ v_m))); MEM_BYTES := v_b_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:266.1-266.54 *)
Inductive Global_extension: globalinst -> globalinst -> Prop :=
	| mk_Global_extension : forall (v_mut : mut) (v_t : valtype) (v_val_1 : val) (v_val_2 : val), 
		((v_mut = (Some MUT)) \/ (v_val_1 = v_val_2)) ->
		Global_extension {| GLOB_TYPE := (mk_globaltype v_mut v_t); GLOB_VALUE := v_val_1 |} {| GLOB_TYPE := (mk_globaltype v_mut v_t); GLOB_VALUE := v_val_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:267.1-267.48 *)
Inductive Elem_extension: eleminst -> eleminst -> Prop :=
	| mk_Elem_extension : forall (v_elemtype : elemtype) (v_ref_1 : (list ref)) (v_ref_2 : (list ref)), 
		((v_ref_1 = v_ref_2) \/ (v_ref_2 = [])) ->
		Elem_extension {| ELEM_TYPE := v_elemtype; ELEM_REFS := v_ref_1 |} {| ELEM_TYPE := v_elemtype; ELEM_REFS := v_ref_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:268.1-268.48 *)
Inductive Data_extension: datainst -> datainst -> Prop :=
	| mk_Data_extension : forall (v_byte_1 : (list byte)) (v_byte_2 : (list byte)), 
		((v_byte_1 = v_byte_2) \/ (v_byte_2 = [])) ->
		Data_extension {| DATA_BYTES := v_byte_1 |} {| DATA_BYTES := v_byte_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:269.1-269.43 *)
Inductive Store_extension: store -> store -> Prop :=
	| mk_Store_extension : forall (v_store_1 : store) (v_store_2 : store) (v_funcinst_1 : (list funcinst)) (v_tableinst_1 : (list tableinst)) (v_meminst_1 : (list meminst)) (v_globalinst_1 : (list globalinst)) (v_eleminst_1 : (list eleminst)) (v_datainst_1 : (list datainst)) (v_funcinst_1' : (list funcinst)) (v_funcinst_2 : (list funcinst)) (v_tableinst_1' : (list tableinst)) (v_tableinst_2 : (list tableinst)) (v_meminst_1' : (list meminst)) (v_meminst_2 : (list meminst)) (v_globalinst_1' : (list globalinst)) (v_globalinst_2 : (list globalinst)) (v_eleminst_1' : (list eleminst)) (v_eleminst_2 : (list eleminst)) (v_datainst_1' : (list datainst)) (v_datainst_2 : (list datainst)), 
		((FUNCS v_store_1) = v_funcinst_1) ->
		((TABLES v_store_1) = v_tableinst_1) ->
		((MEMS v_store_1) = v_meminst_1) ->
		((GLOBALS v_store_1) = v_globalinst_1) ->
		((ELEMS v_store_1) = v_eleminst_1) ->
		((DATAS v_store_1) = v_datainst_1) ->
		([(FUNCS v_store_2)] = [v_funcinst_1'; v_funcinst_2]) ->
		([(TABLES v_store_2)] = [v_tableinst_1'; v_tableinst_2]) ->
		([(MEMS v_store_2)] = [v_meminst_1'; v_meminst_2]) ->
		([(GLOBALS v_store_2)] = [v_globalinst_1'; v_globalinst_2]) ->
		([(ELEMS v_store_2)] = [v_eleminst_1'; v_eleminst_2]) ->
		([(DATAS v_store_2)] = [v_datainst_1'; v_datainst_2]) ->
		((List.length v_funcinst_1) = (List.length v_funcinst_1')) ->
		List.Forall2 (fun (v_funcinst_1 : funcinst) (v_funcinst_1' : funcinst) => (Func_extension v_funcinst_1 v_funcinst_1')) (v_funcinst_1) (v_funcinst_1') ->
		((List.length v_tableinst_1) = (List.length v_tableinst_1')) ->
		List.Forall2 (fun (v_tableinst_1 : tableinst) (v_tableinst_1' : tableinst) => (Table_extension v_tableinst_1 v_tableinst_1')) (v_tableinst_1) (v_tableinst_1') ->
		((List.length v_meminst_1) = (List.length v_meminst_1')) ->
		List.Forall2 (fun (v_meminst_1 : meminst) (v_meminst_1' : meminst) => (Mem_extension v_meminst_1 v_meminst_1')) (v_meminst_1) (v_meminst_1') ->
		((List.length v_globalinst_1) = (List.length v_globalinst_1')) ->
		List.Forall2 (fun (v_globalinst_1 : globalinst) (v_globalinst_1' : globalinst) => (Global_extension v_globalinst_1 v_globalinst_1')) (v_globalinst_1) (v_globalinst_1') ->
		((List.length v_eleminst_1) = (List.length v_eleminst_1')) ->
		List.Forall2 (fun (v_eleminst_1 : eleminst) (v_eleminst_1' : eleminst) => (Elem_extension v_eleminst_1 v_eleminst_1')) (v_eleminst_1) (v_eleminst_1') ->
		((List.length v_datainst_1) = (List.length v_datainst_1')) ->
		List.Forall2 (fun (v_datainst_1 : datainst) (v_datainst_1' : datainst) => (Data_extension v_datainst_1 v_datainst_1')) (v_datainst_1) (v_datainst_1') ->
		Store_extension v_store_1 v_store_2.

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:315.1-315.32 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:315.1-315.32 *)
Fixpoint fun_types__of (var_0 : (list val)) : (list valtype) :=
	match var_0 return (list valtype) with
		| [] => []
		| ((VAL_CONST (I32) v_val_) :: v_val') => ([(I32 : valtype)] ++ (fun_types__of v_val'))
		| ((VAL_CONST (I64) v_val_) :: v_val') => ([(I64 : valtype)] ++ (fun_types__of v_val'))
		| ((VAL_CONST (F32) v_val_) :: v_val') => ([(F32 : valtype)] ++ (fun_types__of v_val'))
		| ((VAL_CONST (F64) v_val_) :: v_val') => ([(F64 : valtype)] ++ (fun_types__of v_val'))
		| ((VAL_VCONST (V128) v_val_) :: v_val') => ([(V128 : valtype)] ++ (fun_types__of v_val'))
		| ((VAL_REF_NULL (FUNCREF)) :: v_val') => ([(FUNCREF : valtype)] ++ (fun_types__of v_val'))
		| ((VAL_REF_NULL (EXTERNREF)) :: v_val') => ([(EXTERNREF : valtype)] ++ (fun_types__of v_val'))
		| ((VAL_REF_FUNC_ADDR v_a) :: v_val') => ([VALTYPE_FUNCREF] ++ (fun_types__of v_val'))
		| ((VAL_REF_HOST_ADDR v_a) :: v_val') => ([VALTYPE_EXTERNREF] ++ (fun_types__of v_val'))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:323.1-324.32 *)
Definition fun_is__const (v_admininstr : admininstr) : bool :=
	match v_admininstr return bool with
		| (AI_CONST v_numtype v_val_) => true
		| (AI_VCONST v_vectype v_val_) => true
		| v_admininstr => false
	end.

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:329.1-330.41 *)
(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:329.1-330.41 *)
Fixpoint fun_const__list (var_0 : (list admininstr)) : bool :=
	match var_0 return bool with
		| [] => true
		| (v_admininstr :: v_admininstr') => ((fun_is__const v_admininstr) && (fun_const__list v_admininstr'))
	end.

(* Auxiliary Definition at: ../specification/wasm-2.0/B-soundness.spectec:335.1-336.38 *)
Definition fun_terminal__form (var_0 : (list admininstr)) : bool :=
	match var_0 return bool with
		| v_admininstr => ((fun_const__list v_admininstr) || (v_admininstr == [AI_TRAP]))
	end.

