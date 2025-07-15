(* Imported Code *)
From Coq Require Import String List Unicode.Utf8 Reals.
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
(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:7.1-7.27 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:8.1-8.27 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:9.1-9.27 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:10.1-10.27 *)
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

(* Global Declaration Definition at: ../specification/wasm-1.0/0-aux.spectec:15.1-15.14 *)
Definition fun_Ki : nat := 1024.

(* Axiom Definition at: ../specification/wasm-1.0/0-aux.spectec:21.1-21.25 *)
Axiom fun_min : forall (v_nat : nat) (v_nat_0 : nat), nat.

(* Mutual Recursion at: ../specification/wasm-1.0/0-aux.spectec:25.1-25.21 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:25.1-25.21 *)
Fixpoint fun_sum (var_0 : (list nat)) : nat :=
	match var_0 with
		| [] => 0
		| (v_n :: v_n') => (v_n + (fun_sum v_n'))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:32.1-32.44 *)
Definition fun_opt_ (v_X : Type) (var_0 : (list v_X)) : (option v_X) :=
	match v_X, var_0 with
		| _, [] => None
		| _, [v_w] => (Some v_w)
		| _, (v_w :: v_w') => (Some v_w)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:37.1-37.45 *)
Definition fun_list_ (v_X : Type) (var_0 : (option v_X)) : (list v_X) :=
	match v_X, var_0 with
		| _, None => []
		| _, (Some v_w) => [v_w]
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/0-aux.spectec:41.1-41.59 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:41.1-41.59 *)
Fixpoint fun_concat_ (v_X : Type) (var_0 : (list (list v_X))) : (list v_X) :=
	match v_X, var_0 with
		| _, [] => []
		| _, (v_w :: v_w') => (v_w ++ (fun_concat_ v_X v_w'))
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:6.1-6.49 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:6.1-6.49 *)
Definition wf_list (v_X : Type) (v_x : (res_list v_X)) : Prop :=
	match v_X, v_x with
		| _, (mk_list v_X) => ((List.length v_X) < (2 ^ 32))
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:14.1-14.50 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:14.1-14.50 *)
Definition wf_byte (v_x : byte) : Prop :=
	match v_x with
		| (mk_byte v_i) => ((v_i >= 0) /\ (v_i <= 255))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:14.1-14.50 *)
Definition fun_proj_byte_0 (v_x : byte) : nat :=
	match v_x with
		| (mk_byte v_v_num_0) => v_v_num_0
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:16.1-17.25 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:16.1-17.25 *)
Definition wf_uN (v_N : res_N) (v_x : (uN v_N)) : Prop :=
	match v_N, v_x with
		| v_N, (mk_uN v_i) => ((v_i >= 0) /\ (v_i <= ((((2 ^ v_N) : nat) - (1 : nat)) : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:16.1-17.25 *)
Definition fun_proj_uN_0 (v_N : res_N) (v_x : (uN v_N)) : nat :=
	match v_N, v_x with
		| v_N, (mk_uN v_v_num_0) => v_v_num_0
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:18.1-19.49 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:18.1-19.49 *)
Definition wf_sN (v_N : res_N) (v_x : (sN v_N)) : Prop :=
	match v_N, v_x with
		| v_N, (mk_sN v_i) => ((((v_i >= (0 - ((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat))) /\ (v_i <= (0 - (1 : nat)))) \/ (v_i = (0 : nat))) \/ ((v_i >= (0 + (1 : nat))) /\ (v_i <= (((2 ^ (((v_N : nat) - (1 : nat)) : nat)) : nat) - (1 : nat)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:18.1-19.49 *)
Definition fun_proj_sN_0 (v_N : res_N) (v_x : (sN v_N)) : nat :=
	match v_N, v_x with
		| v_N, (mk_sN v_v_num_0) => v_v_num_0
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:20.1-21.8 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:23.1-23.20 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:24.1-24.20 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:25.1-25.20 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:32.1-32.35 *)
Definition fun_signif (v_N : res_N) : (option nat) :=
	match v_N with
		| 32 => (Some 23)
		| 64 => (Some 52)
		| v_x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:36.1-36.34 *)
Definition fun_expon (v_N : res_N) : (option nat) :=
	match v_N with
		| 32 => (Some 8)
		| 64 => (Some 11)
		| v_x0 => None
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:40.1-40.30 *)
Definition fun_M (v_N : res_N) : nat :=
	match v_N with
		| v_N => (the (fun_signif v_N))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:43.1-43.30 *)
Definition fun_E (v_N : res_N) : nat :=
	match v_N with
		| v_N => (the (fun_expon v_N))
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.1-50.30 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:51.1-55.84 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:51.1-55.84 *)
Definition wf_fNmag (v_N : res_N) (v_x : (fNmag v_N)) : Prop :=
	match v_N, v_x with
		| v_N, (NORM v_m v_exp) => ((v_m < (2 ^ (fun_M v_N))) /\ ((((2 : nat) - ((2 ^ ((((fun_E v_N) : nat) - (1 : nat)) : nat)) : nat)) <= v_exp) /\ (v_exp <= (((2 ^ ((((fun_E v_N) : nat) - (1 : nat)) : nat)) : nat) - (1 : nat)))))
		| v_N, (SUBNORM v_m) => forall (v_exp : exp), ((v_m < (2 ^ (fun_M v_N))) /\ (((2 : nat) - ((2 ^ ((((fun_E v_N) : nat) - (1 : nat)) : nat)) : nat)) = v_exp))
		| v_N, INF => True
		| v_N, (NAN v_m) => ((1 <= v_m) /\ (v_m < (2 ^ (fun_M v_N))))
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:46.1-48.35 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:57.1-57.20 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:58.1-58.20 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:60.1-60.39 *)
Definition fun_fzero (v_N : res_N) : (fN v_N) :=
	match v_N with
		| v_N => (POS _ (SUBNORM _ 0))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:63.1-63.39 *)
Definition fun_fone (v_N : res_N) : (fN v_N) :=
	match v_N with
		| v_N => (POS _ (NORM _ 1 (0 : nat)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:66.1-66.21 *)
Definition fun_canon_ (v_N : res_N) : nat :=
	match v_N with
		| v_N => (2 ^ ((((the (fun_signif v_N)) : nat) - (1 : nat)) : nat))
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:74.1-74.85 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:74.1-74.85 *)
Definition wf_char (v_x : char) : Prop :=
	match v_x with
		| (mk_char v_i) => (((v_i >= 0) /\ (v_i <= 55295)) \/ ((v_i >= 57344) /\ (v_i <= 1114111)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:74.1-74.85 *)
Definition fun_proj_char_0 (v_x : char) : nat :=
	match v_x with
		| (mk_char v_v_num_0) => v_v_num_0
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:76.1-76.25 *)
(* Axiom Definition at: ../specification/wasm-1.0/1-syntax.spectec:76.1-76.25 *)
Axiom fun_utf8 : forall (var_0 : (list char)), (list byte).

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.70 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.70 *)
Definition wf_name (v_x : name) : Prop :=
	match v_x with
		| (mk_name v_char) => ((List.length (fun_utf8 v_char)) < (2 ^ 32))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.70 *)
Definition fun_proj_name_0 (v_x : name) : (list char) :=
	match v_x with
		| (mk_name v_v_char_list_0) => v_v_char_list_0
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:87.1-87.36 *)
Definition idx := (uN 32).

Definition idx_eq_dec : forall (v1 v2 : idx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition idx_eqb (v1 v2 : idx) : bool :=
	is_left(idx_eq_dec v1 v2).
Definition eqidxP : Equality.axiom (idx_eqb) :=
	eq_dec_Equality_axiom (idx) (idx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (idx) (eqidxP).
Hint Resolve idx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:89.1-89.45 *)
Definition typeidx := (uN 32).

Definition typeidx_eq_dec : forall (v1 v2 : typeidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition typeidx_eqb (v1 v2 : typeidx) : bool :=
	is_left(typeidx_eq_dec v1 v2).
Definition eqtypeidxP : Equality.axiom (typeidx_eqb) :=
	eq_dec_Equality_axiom (typeidx) (typeidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (typeidx) (eqtypeidxP).
Hint Resolve typeidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:90.1-90.49 *)
Definition funcidx := (uN 32).

Definition funcidx_eq_dec : forall (v1 v2 : funcidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition funcidx_eqb (v1 v2 : funcidx) : bool :=
	is_left(funcidx_eq_dec v1 v2).
Definition eqfuncidxP : Equality.axiom (funcidx_eqb) :=
	eq_dec_Equality_axiom (funcidx) (funcidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (funcidx) (eqfuncidxP).
Hint Resolve funcidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:91.1-91.49 *)
Definition globalidx := (uN 32).

Definition globalidx_eq_dec : forall (v1 v2 : globalidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globalidx_eqb (v1 v2 : globalidx) : bool :=
	is_left(globalidx_eq_dec v1 v2).
Definition eqglobalidxP : Equality.axiom (globalidx_eqb) :=
	eq_dec_Equality_axiom (globalidx) (globalidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globalidx) (eqglobalidxP).
Hint Resolve globalidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:92.1-92.47 *)
Definition tableidx := (uN 32).

Definition tableidx_eq_dec : forall (v1 v2 : tableidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tableidx_eqb (v1 v2 : tableidx) : bool :=
	is_left(tableidx_eq_dec v1 v2).
Definition eqtableidxP : Equality.axiom (tableidx_eqb) :=
	eq_dec_Equality_axiom (tableidx) (tableidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tableidx) (eqtableidxP).
Hint Resolve tableidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:93.1-93.46 *)
Definition memidx := (uN 32).

Definition memidx_eq_dec : forall (v1 v2 : memidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memidx_eqb (v1 v2 : memidx) : bool :=
	is_left(memidx_eq_dec v1 v2).
Definition eqmemidxP : Equality.axiom (memidx_eqb) :=
	eq_dec_Equality_axiom (memidx) (memidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memidx) (eqmemidxP).
Hint Resolve memidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:94.1-94.47 *)
Definition labelidx := (uN 32).

Definition labelidx_eq_dec : forall (v1 v2 : labelidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition labelidx_eqb (v1 v2 : labelidx) : bool :=
	is_left(labelidx_eq_dec v1 v2).
Definition eqlabelidxP : Equality.axiom (labelidx_eqb) :=
	eq_dec_Equality_axiom (labelidx) (labelidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (labelidx) (eqlabelidxP).
Hint Resolve labelidx_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:95.1-95.47 *)
Definition localidx := (uN 32).

Definition localidx_eq_dec : forall (v1 v2 : localidx),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition localidx_eqb (v1 v2 : localidx) : bool :=
	is_left(localidx_eq_dec v1 v2).
Definition eqlocalidxP : Equality.axiom (localidx_eqb) :=
	eq_dec_Equality_axiom (localidx) (localidx_eq_dec).

HB.instance Definition _ := hasDecEq.Build (localidx) (eqlocalidxP).
Hint Resolve localidx_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:104.1-105.26 *)
Inductive valtype : Type :=
	| I32 : valtype
	| I64 : valtype
	| F32 : valtype
	| F64 : valtype.

Global Instance Inhabited__valtype : Inhabited (valtype) := { default_val := I32 }.

Definition valtype_eq_dec : forall (v1 v2 : valtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition valtype_eqb (v1 v2 : valtype) : bool :=
	is_left(valtype_eq_dec v1 v2).
Definition eqvaltypeP : Equality.axiom (valtype_eqb) :=
	eq_dec_Equality_axiom (valtype) (valtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (valtype) (eqvaltypeP).
Hint Resolve valtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:107.1-107.58 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:108.1-108.58 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:110.1-110.32 *)
Definition fun_optionSize (var_0 : (option valtype)) : nat :=
	match var_0 with
		| (Some v_valtype) => 1
		| None => 0
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:116.1-117.11 *)
Definition resulttype := (option valtype).

Definition resulttype_eq_dec : forall (v1 v2 : resulttype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition resulttype_eqb (v1 v2 : resulttype) : bool :=
	is_left(resulttype_eq_dec v1 v2).
Definition eqresulttypeP : Equality.axiom (resulttype_eqb) :=
	eq_dec_Equality_axiom (resulttype) (resulttype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (resulttype) (eqresulttypeP).
Hint Resolve resulttype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.1-119.22 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:120.1-120.21 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:122.1-123.16 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:124.1-125.14 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:126.1-127.23 *)
Inductive functype : Type :=
	| mk_functype (_ : (list valtype)) (v__ : (list valtype)) : functype.

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

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:128.1-129.9 *)
Definition tabletype := limits.

Definition tabletype_eq_dec : forall (v1 v2 : tabletype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tabletype_eqb (v1 v2 : tabletype) : bool :=
	is_left(tabletype_eq_dec v1 v2).
Definition eqtabletypeP : Equality.axiom (tabletype_eqb) :=
	eq_dec_Equality_axiom (tabletype) (tabletype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tabletype) (eqtabletypeP).
Hint Resolve tabletype_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:130.1-131.9 *)
Definition memtype := limits.

Definition memtype_eq_dec : forall (v1 v2 : memtype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memtype_eqb (v1 v2 : memtype) : bool :=
	is_left(memtype_eq_dec v1 v2).
Definition eqmemtypeP : Equality.axiom (memtype_eqb) :=
	eq_dec_Equality_axiom (memtype) (memtype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memtype) (eqmemtypeP).
Hint Resolve memtype_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:132.1-133.70 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:145.1-145.40 *)
Definition fun_size (v_valtype : valtype) : nat :=
	match v_valtype with
		| I32 => 32
		| I64 => 64
		| F32 => 32
		| F64 => 64
	end.

(* Family Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:147.1-147.21 *)
Definition val_ (v_valtype : valtype): Type :=
	match v_valtype with
		| I32 => (uN 32)
		| I64 => (uN 64)
		| F32 => (fN 32)
		| F64 => (fN 64)
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.42 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:155.1-155.56 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:155.1-155.56 *)
Definition wf_sz (v_x : sz) : Prop :=
	match v_x with
		| (mk_sz v_i) => ((((v_i = 8) \/ (v_i = 16)) \/ (v_i = 32)) \/ (v_i = 64))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:155.1-155.56 *)
Definition fun_proj_sz_0 (v_x : sz) : nat :=
	match v_x with
		| (mk_sz v_v_num_0) => v_v_num_0
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:157.1-157.22 *)
Inductive unop_Inn (v_Inn : Inn) : Type :=
	| CLZ : unop_Inn v_Inn
	| CTZ : unop_Inn v_Inn
	| POPCNT : unop_Inn v_Inn.

Global Instance Inhabited__unop_Inn (v_Inn : Inn) : Inhabited (unop_Inn v_Inn) := { default_val := CLZ v_Inn }.

Definition unop_Inn_eq_dec : forall (v_Inn : Inn) (v1 v2 : unop_Inn v_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition unop_Inn_eqb (v_Inn : Inn) (v1 v2 : unop_Inn v_Inn) : bool :=
	is_left(unop_Inn_eq_dec v_Inn v1 v2).
Definition equnop_InnP (v_Inn : Inn) : Equality.axiom (unop_Inn_eqb v_Inn) :=
	eq_dec_Equality_axiom (unop_Inn v_Inn) (unop_Inn_eq_dec v_Inn).

HB.instance Definition _ (v_Inn : Inn) := hasDecEq.Build (unop_Inn v_Inn) (equnop_InnP v_Inn).
Hint Resolve unop_Inn_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:157.1-157.22 *)
Inductive unop_Fnn (v_Fnn : Fnn) : Type :=
	| ABS : unop_Fnn v_Fnn
	| UNOP_NEG : unop_Fnn v_Fnn
	| SQRT : unop_Fnn v_Fnn
	| CEIL : unop_Fnn v_Fnn
	| FLOOR : unop_Fnn v_Fnn
	| UNOP_TRUNC : unop_Fnn v_Fnn
	| NEAREST : unop_Fnn v_Fnn.

Global Instance Inhabited__unop_Fnn (v_Fnn : Fnn) : Inhabited (unop_Fnn v_Fnn) := { default_val := ABS v_Fnn }.

Definition unop_Fnn_eq_dec : forall (v_Fnn : Fnn) (v1 v2 : unop_Fnn v_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition unop_Fnn_eqb (v_Fnn : Fnn) (v1 v2 : unop_Fnn v_Fnn) : bool :=
	is_left(unop_Fnn_eq_dec v_Fnn v1 v2).
Definition equnop_FnnP (v_Fnn : Fnn) : Equality.axiom (unop_Fnn_eqb v_Fnn) :=
	eq_dec_Equality_axiom (unop_Fnn v_Fnn) (unop_Fnn_eq_dec v_Fnn).

HB.instance Definition _ (v_Fnn : Fnn) := hasDecEq.Build (unop_Fnn v_Fnn) (equnop_FnnP v_Fnn).
Hint Resolve unop_Fnn_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:157.1-157.22 *)
Definition unop_ (v_valtype : valtype): Type :=
	match v_valtype with
		| I32 => (unop_Inn INN_I32)
		| I64 => (unop_Inn INN_I64)
		| F32 => (unop_Fnn FNN_F32)
		| F64 => (unop_Fnn FNN_F64)
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:161.1-161.23 *)
Inductive binop_Inn (v_Inn : Inn) : Type :=
	| INT_ADD : binop_Inn v_Inn
	| INT_SUB : binop_Inn v_Inn
	| INT_MUL : binop_Inn v_Inn
	| INT_DIV (v_sx : sx) : binop_Inn v_Inn
	| REM (v_sx : sx) : binop_Inn v_Inn
	| AND : binop_Inn v_Inn
	| OR : binop_Inn v_Inn
	| XOR : binop_Inn v_Inn
	| SHL : binop_Inn v_Inn
	| SHR (v_sx : sx) : binop_Inn v_Inn
	| ROTL : binop_Inn v_Inn
	| ROTR : binop_Inn v_Inn.

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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:161.1-161.23 *)
Inductive binop_Fnn (v_Fnn : Fnn) : Type :=
	| ADD : binop_Fnn v_Fnn
	| SUB : binop_Fnn v_Fnn
	| MUL : binop_Fnn v_Fnn
	| DIV : binop_Fnn v_Fnn
	| MIN : binop_Fnn v_Fnn
	| MAX : binop_Fnn v_Fnn
	| COPYSIGN : binop_Fnn v_Fnn.

Global Instance Inhabited__binop_Fnn (v_Fnn : Fnn) : Inhabited (binop_Fnn v_Fnn) := { default_val := ADD v_Fnn }.

Definition binop_Fnn_eq_dec : forall (v_Fnn : Fnn) (v1 v2 : binop_Fnn v_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition binop_Fnn_eqb (v_Fnn : Fnn) (v1 v2 : binop_Fnn v_Fnn) : bool :=
	is_left(binop_Fnn_eq_dec v_Fnn v1 v2).
Definition eqbinop_FnnP (v_Fnn : Fnn) : Equality.axiom (binop_Fnn_eqb v_Fnn) :=
	eq_dec_Equality_axiom (binop_Fnn v_Fnn) (binop_Fnn_eq_dec v_Fnn).

HB.instance Definition _ (v_Fnn : Fnn) := hasDecEq.Build (binop_Fnn v_Fnn) (eqbinop_FnnP v_Fnn).
Hint Resolve binop_Fnn_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:161.1-161.23 *)
Definition binop_ (v_valtype : valtype): Type :=
	match v_valtype with
		| I32 => (binop_Inn INN_I32)
		| I64 => (binop_Inn INN_I64)
		| F32 => (binop_Fnn FNN_F32)
		| F64 => (binop_Fnn FNN_F64)
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:168.1-168.42 *)
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

(* Family Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:168.1-168.42 *)
Definition testop_ (v_valtype : valtype): Type :=
	match v_valtype with
		| I32 => (testop_Inn INN_I32)
		| I64 => (testop_Inn INN_I64)
		| _ => default_val
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:172.1-172.23 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:172.1-172.23 *)
Inductive relop_Fnn (v_Fnn : Fnn) : Type :=
	| EQ : relop_Fnn v_Fnn
	| NE : relop_Fnn v_Fnn
	| LT : relop_Fnn v_Fnn
	| GT : relop_Fnn v_Fnn
	| LE : relop_Fnn v_Fnn
	| GE : relop_Fnn v_Fnn.

Global Instance Inhabited__relop_Fnn (v_Fnn : Fnn) : Inhabited (relop_Fnn v_Fnn) := { default_val := EQ v_Fnn }.

Definition relop_Fnn_eq_dec : forall (v_Fnn : Fnn) (v1 v2 : relop_Fnn v_Fnn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition relop_Fnn_eqb (v_Fnn : Fnn) (v1 v2 : relop_Fnn v_Fnn) : bool :=
	is_left(relop_Fnn_eq_dec v_Fnn v1 v2).
Definition eqrelop_FnnP (v_Fnn : Fnn) : Equality.axiom (relop_Fnn_eqb v_Fnn) :=
	eq_dec_Equality_axiom (relop_Fnn v_Fnn) (relop_Fnn_eq_dec v_Fnn).

HB.instance Definition _ (v_Fnn : Fnn) := hasDecEq.Build (relop_Fnn v_Fnn) (eqrelop_FnnP v_Fnn).
Hint Resolve relop_Fnn_eq_dec : eq_dec_db.

(* Family Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:172.1-172.23 *)
Definition relop_ (v_valtype : valtype): Type :=
	match v_valtype with
		| I32 => (relop_Inn INN_I32)
		| I64 => (relop_Inn INN_I64)
		| F32 => (relop_Fnn FNN_F32)
		| F64 => (relop_Fnn FNN_F64)
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:180.1-181.78 *)
Inductive cvtop : Type :=
	| EXTEND (v_sx : sx) : cvtop
	| WRAP : cvtop
	| CONVERT (v_sx : sx) : cvtop
	| TRUNC (v_sx : sx) : cvtop
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

(* Record Creation Definition at: ../specification/wasm-1.0/1-syntax.spectec:186.1-186.69 *)
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
	ALIGN := arg1.(ALIGN); (* FIXME - Non-trivial append*)
	OFFSET := arg1.(OFFSET); (* FIXME - Non-trivial append*)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:190.1-190.42 *)
Inductive loadop_Inn (v_Inn : Inn) : Type :=
	| op__ (v_sz : sz) (v_sx : sx) : loadop_Inn v_Inn.

Global Instance Inhabited__loadop_Inn (v_Inn : Inn) : Inhabited (loadop_Inn v_Inn) := { default_val := op__ v_Inn default_val default_val }.

Definition loadop_Inn_eq_dec : forall (v_Inn : Inn) (v1 v2 : loadop_Inn v_Inn),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition loadop_Inn_eqb (v_Inn : Inn) (v1 v2 : loadop_Inn v_Inn) : bool :=
	is_left(loadop_Inn_eq_dec v_Inn v1 v2).
Definition eqloadop_InnP (v_Inn : Inn) : Equality.axiom (loadop_Inn_eqb v_Inn) :=
	eq_dec_Equality_axiom (loadop_Inn v_Inn) (loadop_Inn_eq_dec v_Inn).

HB.instance Definition _ (v_Inn : Inn) := hasDecEq.Build (loadop_Inn v_Inn) (eqloadop_InnP v_Inn).
Hint Resolve loadop_Inn_eq_dec : eq_dec_db.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:190.1-190.42 *)
Definition fun_coec_Inn__valtype (v_Inn : Inn) : valtype :=
	match v_Inn with
		| INN_I32 => I32
		| INN_I64 => I64
	end.

(* Type Coercion Definition at: ../specification/wasm-1.0/1-syntax.spectec:190.1-190.42 *)
Coercion fun_coec_Inn__valtype : Inn >-> valtype.

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:190.1-190.42 *)
Definition wf_loadop_Inn (v_Inn : Inn) (v_x : (loadop_Inn v_Inn)) : Prop :=
	match v_Inn, v_x with
		| v_Inn, (op__ v_sz v_sx) => ((fun_proj_sz_0 v_sz) < (fun_size (v_Inn : valtype)))
	end.

(* Family Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:190.1-190.42 *)
Definition loadop_ (v_valtype : valtype): Type :=
	match v_valtype with
		| I32 => (loadop_Inn INN_I32)
		| I64 => (loadop_Inn INN_I64)
		| _ => default_val
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:196.1-196.52 *)
Definition blocktype := (option valtype).

Definition blocktype_eq_dec : forall (v1 v2 : blocktype),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition blocktype_eqb (v1 v2 : blocktype) : bool :=
	is_left(blocktype_eq_dec v1 v2).
Definition eqblocktypeP : Equality.axiom (blocktype_eqb) :=
	eq_dec_Equality_axiom (blocktype) (blocktype_eq_dec).

HB.instance Definition _ := hasDecEq.Build (blocktype) (eqblocktypeP).
Hint Resolve blocktype_eq_dec : eq_dec_db.

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:246.1-251.16 *)
(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:246.1-251.16 *)
Inductive instr : Type :=
	| NOP : instr
	| UNREACHABLE : instr
	| DROP : instr
	| SELECT : instr
	| BLOCK (v_blocktype : blocktype) (_ : (list instr)) : instr
	| LOOP (v_blocktype : blocktype) (_ : (list instr)) : instr
	| IFELSE (v_blocktype : blocktype) (_ : (list instr)) (v__ : (list instr)) : instr
	| BR (v_labelidx : labelidx) : instr
	| BR_IF (v_labelidx : labelidx) : instr
	| BR_TABLE (_ : (list labelidx)) (v__ : labelidx) : instr
	| CALL (v_funcidx : funcidx) : instr
	| CALL_INDIRECT (v_typeidx : typeidx) : instr
	| RETURN : instr
	| CONST (v_valtype : valtype) (v_val_ : (val_ v_valtype)) : instr
	| UNOP (v_valtype : valtype) (v_unop_ : (unop_ v_valtype)) : instr
	| BINOP (v_valtype : valtype) (v_binop_ : (binop_ v_valtype)) : instr
	| TESTOP (v_valtype : valtype) (v_testop_ : (testop_ v_valtype)) : instr
	| RELOP (v_valtype : valtype) (v_relop_ : (relop_ v_valtype)) : instr
	| CVTOP (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_cvtop : cvtop) : instr
	| LOCAL_GET (v_localidx : localidx) : instr
	| LOCAL_SET (v_localidx : localidx) : instr
	| LOCAL_TEE (v_localidx : localidx) : instr
	| GLOBAL_GET (v_globalidx : globalidx) : instr
	| GLOBAL_SET (v_globalidx : globalidx) : instr
	| LOAD (v_valtype : valtype) (_ : (option (loadop_ v_valtype))) (v_memarg : memarg) : instr
	| STORE (v_valtype : valtype) (_ : (option sz)) (v_memarg : memarg) : instr
	| MEMORY_SIZE : instr
	| MEMORY_GROW : instr.

Global Instance Inhabited__instr : Inhabited (instr) := { default_val := NOP }.

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

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:246.1-251.16 *)
Fixpoint wf_instr (v_x : instr) : Prop :=
	match v_x with
		| NOP => True
		| UNREACHABLE => True
		| DROP => True
		| SELECT => True
		| (BLOCK v_blocktype v_instr) => True
		| (LOOP v_blocktype v_instr) => True
		| (IFELSE v_blocktype v_instr v__) => True
		| (BR v_labelidx) => True
		| (BR_IF v_labelidx) => True
		| (BR_TABLE v_labelidx v__) => True
		| (CALL v_funcidx) => True
		| (CALL_INDIRECT v_typeidx) => True
		| RETURN => True
		| (CONST v_valtype v_val_) => True
		| (UNOP v_valtype v_unop_) => True
		| (BINOP v_valtype v_binop_) => True
		| (TESTOP v_valtype v_testop_) => True
		| (RELOP v_valtype v_relop_) => True
		| (CVTOP v_valtype_1 v_valtype_2 v_cvtop) => (v_valtype_1 <> v_valtype_2)
		| (LOCAL_GET v_localidx) => True
		| (LOCAL_SET v_localidx) => True
		| (LOCAL_TEE v_localidx) => True
		| (GLOBAL_GET v_globalidx) => True
		| (GLOBAL_SET v_globalidx) => True
		| (LOAD v_valtype v_loadop_ v_memarg) => True
		| (STORE v_valtype v_sz v_memarg) => forall (v_Inn : (option Inn)), List.Forall2 (fun (v_Inn : Inn) (v_sz : sz) => ((v_valtype = (v_Inn : valtype)) /\ ((fun_proj_sz_0 v_sz) < (fun_size (v_Inn : valtype))))) (option_to_list v_Inn) (option_to_list v_sz)
		| MEMORY_SIZE => True
		| MEMORY_GROW => True
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:253.1-254.9 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:264.1-265.16 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:266.1-267.16 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:268.1-269.27 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:270.1-271.25 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:272.1-273.18 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:274.1-275.17 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:276.1-277.21 *)
Inductive elem : Type :=
	| ELEM (v_expr : expr) (_ : (list funcidx)) : elem.

Global Instance Inhabited__elem : Inhabited (elem) := { default_val := ELEM default_val default_val }.

Definition elem_eq_dec : forall (v1 v2 : elem),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition elem_eqb (v1 v2 : elem) : bool :=
	is_left(elem_eq_dec v1 v2).
Definition eqelemP : Equality.axiom (elem_eqb) :=
	eq_dec_Equality_axiom (elem) (elem_eq_dec).

HB.instance Definition _ := hasDecEq.Build (elem) (eqelemP).
Hint Resolve elem_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:278.1-279.18 *)
Inductive data : Type :=
	| DATA (v_expr : expr) (_ : (list byte)) : data.

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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:280.1-281.16 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:283.1-284.66 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:285.1-286.24 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:287.1-288.30 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:290.1-291.76 *)
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

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:20.1-20.64 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:20.1-20.64 *)
Fixpoint fun_funcsxt (var_0 : (list externtype)) : (list functype) :=
	match var_0 with
		| [] => []
		| ((EXT_FUNC v_ft) :: v_xt) => ([v_ft] ++ (fun_funcsxt v_xt))
		| (v_externtype :: v_xt) => (fun_funcsxt v_xt)
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:21.1-21.66 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:21.1-21.66 *)
Fixpoint fun_globalsxt (var_0 : (list externtype)) : (list globaltype) :=
	match var_0 with
		| [] => []
		| ((EXT_GLOBAL v_gt) :: v_xt) => ([v_gt] ++ (fun_globalsxt v_xt))
		| (v_externtype :: v_xt) => (fun_globalsxt v_xt)
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65 *)
Fixpoint fun_tablesxt (var_0 : (list externtype)) : (list tabletype) :=
	match var_0 with
		| [] => []
		| ((EXT_TABLE v_tt) :: v_xt) => ([v_tt] ++ (fun_tablesxt v_xt))
		| (v_externtype :: v_xt) => (fun_tablesxt v_xt)
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63 *)
Fixpoint fun_memsxt (var_0 : (list externtype)) : (list memtype) :=
	match var_0 with
		| [] => []
		| ((EXT_MEM v_mt) :: v_xt) => ([v_mt] ++ (fun_memsxt v_xt))
		| (v_externtype :: v_xt) => (fun_memsxt v_xt)
	end.

(* Global Declaration Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:49.1-49.35 *)
Definition fun_memarg0 : memarg := {| ALIGN := (mk_uN _ 0); OFFSET := (mk_uN _ 0) |}.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:7.1-7.22 *)
Definition fun_bool (v_bool : bool) : nat :=
	match v_bool with
		| false => 0
		| true => 1
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:14.1-14.27 *)
Axiom fun_signed_ : forall (v_N : res_N) (v_nat : nat), nat.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:18.1-18.67 *)
Axiom fun_invsigned_ : forall (v_N : res_N) (v_int : nat), nat.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:102.1-102.30 *)
Axiom fun_fabs_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:105.1-105.31 *)
Axiom fun_fceil_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:106.1-106.32 *)
Axiom fun_ffloor_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:108.1-108.34 *)
Axiom fun_fnearest_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:103.1-103.30 *)
Axiom fun_fneg_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:104.1-104.31 *)
Axiom fun_fsqrt_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:107.1-107.32 *)
Axiom fun_ftrunc_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:66.1-66.29 *)
Axiom fun_iclz_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:67.1-67.29 *)
Axiom fun_ictz_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:68.1-68.32 *)
Axiom fun_ipopcnt_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:24.1-25.32 *)
Definition fun_coec_Fnn__valtype (v_Fnn : Fnn) : valtype :=
	match v_Fnn with
		| FNN_F32 => F32
		| FNN_F64 => F64
	end.

(* Type Coercion Definition at: ../specification/wasm-1.0/3-numerics.spectec:24.1-25.32 *)
Coercion fun_coec_Fnn__valtype : Fnn >-> valtype.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:24.1-25.32 *)
Definition fun_unop_ (v_valtype : valtype) (v_unop_ : (unop_ v_valtype)) (v_val_ : (val_ v_valtype)) : (list (val_ v_valtype)) :=
	match v_valtype, v_unop_, v_val_ with
		| I32, CLZ, v_iN => [(fun_iclz_ (fun_size (INN_I32 : valtype)) v_iN)]
		| I64, CLZ, v_iN => [(fun_iclz_ (fun_size (INN_I64 : valtype)) v_iN)]
		| I32, CTZ, v_iN => [(fun_ictz_ (fun_size (INN_I32 : valtype)) v_iN)]
		| I64, CTZ, v_iN => [(fun_ictz_ (fun_size (INN_I64 : valtype)) v_iN)]
		| I32, POPCNT, v_iN => [(fun_ipopcnt_ (fun_size (INN_I32 : valtype)) v_iN)]
		| I64, POPCNT, v_iN => [(fun_ipopcnt_ (fun_size (INN_I64 : valtype)) v_iN)]
		| F32, ABS, v_fN => (fun_fabs_ (fun_size (FNN_F32 : valtype)) v_fN)
		| F64, ABS, v_fN => (fun_fabs_ (fun_size (FNN_F64 : valtype)) v_fN)
		| F32, UNOP_NEG, v_fN => (fun_fneg_ (fun_size (FNN_F32 : valtype)) v_fN)
		| F64, UNOP_NEG, v_fN => (fun_fneg_ (fun_size (FNN_F64 : valtype)) v_fN)
		| F32, SQRT, v_fN => (fun_fsqrt_ (fun_size (FNN_F32 : valtype)) v_fN)
		| F64, SQRT, v_fN => (fun_fsqrt_ (fun_size (FNN_F64 : valtype)) v_fN)
		| F32, CEIL, v_fN => (fun_fceil_ (fun_size (FNN_F32 : valtype)) v_fN)
		| F64, CEIL, v_fN => (fun_fceil_ (fun_size (FNN_F64 : valtype)) v_fN)
		| F32, FLOOR, v_fN => (fun_ffloor_ (fun_size (FNN_F32 : valtype)) v_fN)
		| F64, FLOOR, v_fN => (fun_ffloor_ (fun_size (FNN_F64 : valtype)) v_fN)
		| F32, UNOP_TRUNC, v_fN => (fun_ftrunc_ (fun_size (FNN_F32 : valtype)) v_fN)
		| F64, UNOP_TRUNC, v_fN => (fun_ftrunc_ (fun_size (FNN_F64 : valtype)) v_fN)
		| F32, NEAREST, v_fN => (fun_fnearest_ (fun_size (FNN_F32 : valtype)) v_fN)
		| F64, NEAREST, v_fN => (fun_fnearest_ (fun_size (FNN_F64 : valtype)) v_fN)
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:95.1-95.37 *)
Axiom fun_fadd_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:101.1-101.42 *)
Axiom fun_fcopysign_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:98.1-98.37 *)
Axiom fun_fdiv_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:100.1-100.37 *)
Axiom fun_fmax_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:99.1-99.37 *)
Axiom fun_fmin_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:97.1-97.37 *)
Axiom fun_fmul_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:96.1-96.37 *)
Axiom fun_fsub_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), (list (fN v_N)).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:53.1-53.36 *)
Definition fun_iadd_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_iN, v_iN_0 with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (((fun_proj_uN_0 v_N v_i_1) + (fun_proj_uN_0 v_N v_i_2)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:59.1-59.36 *)
Axiom fun_iand_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:56.1-56.74 *)
Axiom fun_idiv_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (option (iN v_N)).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:55.1-55.36 *)
Definition fun_imul_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_iN, v_iN_0 with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (((fun_proj_uN_0 v_N v_i_1) * (fun_proj_uN_0 v_N v_i_2)) mod (2 ^ v_N)))
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:60.1-60.35 *)
Axiom fun_ior_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:57.1-57.74 *)
Axiom fun_irem_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (option (iN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:64.1-64.37 *)
Axiom fun_irotl_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:65.1-65.37 *)
Axiom fun_irotr_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:62.1-62.34 *)
Axiom fun_ishl_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_u32 : u32), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:63.1-63.74 *)
Axiom fun_ishr_ : forall (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_u32 : u32), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:54.1-54.36 *)
Definition fun_isub_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : (iN v_N) :=
	match v_N, v_iN, v_iN_0 with
		| v_N, v_i_1, v_i_2 => (mk_uN _ ((((((2 ^ v_N) + (fun_proj_uN_0 v_N v_i_1)) : nat) - ((fun_proj_uN_0 v_N v_i_2) : nat)) mod ((2 ^ v_N) : nat)) : nat))
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:61.1-61.36 *)
Axiom fun_ixor_ : forall (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:26.1-27.34 *)
Definition fun_binop_ (v_valtype : valtype) (v_binop_ : (binop_ v_valtype)) (v_val_ : (val_ v_valtype)) (v_val__0 : (val_ v_valtype)) : (list (val_ v_valtype)) :=
	match v_valtype, v_binop_, v_val_, v_val__0 with
		| I32, INT_ADD, v_iN_1, v_iN_2 => [(fun_iadd_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, INT_ADD, v_iN_1, v_iN_2 => [(fun_iadd_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| I32, INT_SUB, v_iN_1, v_iN_2 => [(fun_isub_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, INT_SUB, v_iN_1, v_iN_2 => [(fun_isub_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| I32, INT_MUL, v_iN_1, v_iN_2 => [(fun_imul_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, INT_MUL, v_iN_1, v_iN_2 => [(fun_imul_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| I32, (INT_DIV v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 32) (fun_idiv_ (fun_size (INN_I32 : valtype)) v_sx v_iN_1 v_iN_2))
		| I64, (INT_DIV v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 64) (fun_idiv_ (fun_size (INN_I64 : valtype)) v_sx v_iN_1 v_iN_2))
		| I32, (REM v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 32) (fun_irem_ (fun_size (INN_I32 : valtype)) v_sx v_iN_1 v_iN_2))
		| I64, (REM v_sx), v_iN_1, v_iN_2 => (fun_list_ (uN 64) (fun_irem_ (fun_size (INN_I64 : valtype)) v_sx v_iN_1 v_iN_2))
		| I32, AND, v_iN_1, v_iN_2 => [(fun_iand_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, AND, v_iN_1, v_iN_2 => [(fun_iand_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| I32, OR, v_iN_1, v_iN_2 => [(fun_ior_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, OR, v_iN_1, v_iN_2 => [(fun_ior_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| I32, XOR, v_iN_1, v_iN_2 => [(fun_ixor_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, XOR, v_iN_1, v_iN_2 => [(fun_ixor_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| I32, SHL, v_iN_1, v_iN_2 => [(fun_ishl_ (fun_size (INN_I32 : valtype)) v_iN_1 (mk_uN _ (fun_proj_uN_0 32 v_iN_2)))]
		| I64, SHL, v_iN_1, v_iN_2 => [(fun_ishl_ (fun_size (INN_I64 : valtype)) v_iN_1 (mk_uN _ (fun_proj_uN_0 64 v_iN_2)))]
		| I32, (SHR v_sx), v_iN_1, v_iN_2 => [(fun_ishr_ (fun_size (INN_I32 : valtype)) v_sx v_iN_1 (mk_uN _ (fun_proj_uN_0 32 v_iN_2)))]
		| I64, (SHR v_sx), v_iN_1, v_iN_2 => [(fun_ishr_ (fun_size (INN_I64 : valtype)) v_sx v_iN_1 (mk_uN _ (fun_proj_uN_0 64 v_iN_2)))]
		| I32, ROTL, v_iN_1, v_iN_2 => [(fun_irotl_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, ROTL, v_iN_1, v_iN_2 => [(fun_irotl_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| I32, ROTR, v_iN_1, v_iN_2 => [(fun_irotr_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)]
		| I64, ROTR, v_iN_1, v_iN_2 => [(fun_irotr_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)]
		| F32, ADD, v_fN_1, v_fN_2 => (fun_fadd_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, ADD, v_fN_1, v_fN_2 => (fun_fadd_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, SUB, v_fN_1, v_fN_2 => (fun_fsub_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, SUB, v_fN_1, v_fN_2 => (fun_fsub_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, MUL, v_fN_1, v_fN_2 => (fun_fmul_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, MUL, v_fN_1, v_fN_2 => (fun_fmul_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, DIV, v_fN_1, v_fN_2 => (fun_fdiv_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, DIV, v_fN_1, v_fN_2 => (fun_fdiv_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, MIN, v_fN_1, v_fN_2 => (fun_fmin_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, MIN, v_fN_1, v_fN_2 => (fun_fmin_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, MAX, v_fN_1, v_fN_2 => (fun_fmax_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, MAX, v_fN_1, v_fN_2 => (fun_fmax_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, COPYSIGN, v_fN_1, v_fN_2 => (fun_fcopysign_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, COPYSIGN, v_fN_1, v_fN_2 => (fun_fcopysign_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:69.1-69.27 *)
Definition fun_ieqz_ (v_N : res_N) (v_iN : (iN v_N)) : u32 :=
	match v_N, v_iN with
		| v_N, v_i_1 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) == 0)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.1-29.32 *)
Definition fun_testop_ (v_valtype : valtype) (v_testop_ : (testop_ v_valtype)) (v_val_ : (val_ v_valtype)) : (uN 32) :=
	match v_valtype, v_testop_, v_val_ with
		| I32, EQZ, v_iN => (fun_ieqz_ (fun_size (INN_I32 : valtype)) v_iN)
		| I64, EQZ, v_iN => (fun_ieqz_ (fun_size (INN_I64 : valtype)) v_iN)
		| _, _, _ => default_val
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:109.1-109.33 *)
Axiom fun_feq_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:114.1-114.33 *)
Axiom fun_fge_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:112.1-112.33 *)
Axiom fun_fgt_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:113.1-113.33 *)
Axiom fun_fle_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:111.1-111.33 *)
Axiom fun_flt_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:110.1-110.33 *)
Axiom fun_fne_ : forall (v_N : res_N) (v_fN : (fN v_N)) (v_fN_0 : (fN v_N)), u32.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:71.1-71.33 *)
Definition fun_ieq_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_iN, v_iN_0 with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (fun_bool (v_i_1 == v_i_2)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:76.1-76.73 *)
Definition fun_ige_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 with
		| v_N, U, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) >= (fun_proj_uN_0 v_N v_i_2))))
		| v_N, res_S, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) >= (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:74.1-74.73 *)
Definition fun_igt_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 with
		| v_N, U, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) > (fun_proj_uN_0 v_N v_i_2))))
		| v_N, res_S, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) > (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:75.1-75.73 *)
Definition fun_ile_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 with
		| v_N, U, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) <= (fun_proj_uN_0 v_N v_i_2))))
		| v_N, res_S, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) <= (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:73.1-73.73 *)
Definition fun_ilt_ (v_N : res_N) (v_sx : sx) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_sx, v_iN, v_iN_0 with
		| v_N, U, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) < (fun_proj_uN_0 v_N v_i_2))))
		| v_N, res_S, v_i_1, v_i_2 => (mk_uN _ (fun_bool ((fun_signed_ v_N (fun_proj_uN_0 v_N v_i_1)) < (fun_signed_ v_N (fun_proj_uN_0 v_N v_i_2)))))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:72.1-72.33 *)
Definition fun_ine_ (v_N : res_N) (v_iN : (iN v_N)) (v_iN_0 : (iN v_N)) : u32 :=
	match v_N, v_iN, v_iN_0 with
		| v_N, v_i_1, v_i_2 => (mk_uN _ (fun_bool (v_i_1 != v_i_2)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:30.1-31.34 *)
Definition fun_relop_ (v_valtype : valtype) (v_relop_ : (relop_ v_valtype)) (v_val_ : (val_ v_valtype)) (v_val__0 : (val_ v_valtype)) : (uN 32) :=
	match v_valtype, v_relop_, v_val_, v_val__0 with
		| I32, INT_EQ, v_iN_1, v_iN_2 => (fun_ieq_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)
		| I64, INT_EQ, v_iN_1, v_iN_2 => (fun_ieq_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)
		| I32, INT_NE, v_iN_1, v_iN_2 => (fun_ine_ (fun_size (INN_I32 : valtype)) v_iN_1 v_iN_2)
		| I64, INT_NE, v_iN_1, v_iN_2 => (fun_ine_ (fun_size (INN_I64 : valtype)) v_iN_1 v_iN_2)
		| I32, (INT_LT v_sx), v_iN_1, v_iN_2 => (fun_ilt_ (fun_size (INN_I32 : valtype)) v_sx v_iN_1 v_iN_2)
		| I64, (INT_LT v_sx), v_iN_1, v_iN_2 => (fun_ilt_ (fun_size (INN_I64 : valtype)) v_sx v_iN_1 v_iN_2)
		| I32, (INT_GT v_sx), v_iN_1, v_iN_2 => (fun_igt_ (fun_size (INN_I32 : valtype)) v_sx v_iN_1 v_iN_2)
		| I64, (INT_GT v_sx), v_iN_1, v_iN_2 => (fun_igt_ (fun_size (INN_I64 : valtype)) v_sx v_iN_1 v_iN_2)
		| I32, (INT_LE v_sx), v_iN_1, v_iN_2 => (fun_ile_ (fun_size (INN_I32 : valtype)) v_sx v_iN_1 v_iN_2)
		| I64, (INT_LE v_sx), v_iN_1, v_iN_2 => (fun_ile_ (fun_size (INN_I64 : valtype)) v_sx v_iN_1 v_iN_2)
		| I32, (INT_GE v_sx), v_iN_1, v_iN_2 => (fun_ige_ (fun_size (INN_I32 : valtype)) v_sx v_iN_1 v_iN_2)
		| I64, (INT_GE v_sx), v_iN_1, v_iN_2 => (fun_ige_ (fun_size (INN_I64 : valtype)) v_sx v_iN_1 v_iN_2)
		| F32, EQ, v_fN_1, v_fN_2 => (fun_feq_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, EQ, v_fN_1, v_fN_2 => (fun_feq_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, NE, v_fN_1, v_fN_2 => (fun_fne_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, NE, v_fN_1, v_fN_2 => (fun_fne_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, LT, v_fN_1, v_fN_2 => (fun_flt_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, LT, v_fN_1, v_fN_2 => (fun_flt_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, GT, v_fN_1, v_fN_2 => (fun_fgt_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, GT, v_fN_1, v_fN_2 => (fun_fgt_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, LE, v_fN_1, v_fN_2 => (fun_fle_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, LE, v_fN_1, v_fN_2 => (fun_fle_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
		| F32, GE, v_fN_1, v_fN_2 => (fun_fge_ (fun_size (FNN_F32 : valtype)) v_fN_1 v_fN_2)
		| F64, GE, v_fN_1, v_fN_2 => (fun_fge_ (fun_size (FNN_F64 : valtype)) v_fN_1 v_fN_2)
	end.

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:40.1-40.90 *)
Axiom fun_convert__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : (iN v_M)), (fN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:38.1-38.36 *)
Axiom fun_demote__ : forall (v_M : M) (v_N : res_N) (v_fN : (fN v_M)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:36.1-36.89 *)
Axiom fun_extend__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_iN : (iN v_M)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:39.1-39.37 *)
Axiom fun_promote__ : forall (v_M : M) (v_N : res_N) (v_fN : (fN v_M)), (list (fN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:41.1-41.76 *)
Axiom fun_reinterpret__ : forall (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_val_ : (val_ v_valtype_1)), (val_ v_valtype_2).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:37.1-37.88 *)
Axiom fun_trunc__ : forall (v_M : M) (v_N : res_N) (v_sx : sx) (v_fN : (fN v_M)), (option (iN v_N)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:35.1-35.33 *)
Axiom fun_wrap__ : forall (v_M : M) (v_N : res_N) (v_iN : (iN v_M)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:32.1-33.36 *)
Axiom fun_cvtop__ : forall (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_cvtop : cvtop) (v_val_ : (val_ v_valtype_1)), (list (val_ v_valtype_2)).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:43.1-43.79 *)
Axiom fun_ibytes_ : forall (v_N : res_N) (v_iN : (iN v_N)), (list byte).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:44.1-44.79 *)
Axiom fun_fbytes_ : forall (v_N : res_N) (v_fN : (fN v_N)), (list byte).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:45.1-45.44 *)
Axiom fun_bytes_ : forall (v_valtype : valtype) (v_val_ : (val_ v_valtype)), (list byte).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:47.1-47.34 *)
Axiom fun_invibytes_ : forall (v_N : res_N) (var_0 : (list byte)), (iN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:48.1-48.34 *)
Axiom fun_invfbytes_ : forall (v_N : res_N) (var_0 : (list byte)), (fN v_N).

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:58.1-58.29 *)
Axiom fun_inot_ : forall (v_N : res_N) (v_iN : (iN v_N)), (iN v_N).

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:70.1-70.27 *)
Definition fun_inez_ (v_N : res_N) (v_iN : (iN v_N)) : u32 :=
	match v_N, v_iN with
		| v_N, v_i_1 => (mk_uN _ (fun_bool ((fun_proj_uN_0 v_N v_i_1) != 0)))
	end.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:5.1-5.39 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:6.1-6.53 *)
Definition funcaddr := nat.

Definition funcaddr_eq_dec : forall (v1 v2 : funcaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition funcaddr_eqb (v1 v2 : funcaddr) : bool :=
	is_left(funcaddr_eq_dec v1 v2).
Definition eqfuncaddrP : Equality.axiom (funcaddr_eqb) :=
	eq_dec_Equality_axiom (funcaddr) (funcaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (funcaddr) (eqfuncaddrP).
Hint Resolve funcaddr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:7.1-7.53 *)
Definition globaladdr := nat.

Definition globaladdr_eq_dec : forall (v1 v2 : globaladdr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globaladdr_eqb (v1 v2 : globaladdr) : bool :=
	is_left(globaladdr_eq_dec v1 v2).
Definition eqglobaladdrP : Equality.axiom (globaladdr_eqb) :=
	eq_dec_Equality_axiom (globaladdr) (globaladdr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globaladdr) (eqglobaladdrP).
Hint Resolve globaladdr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:8.1-8.51 *)
Definition tableaddr := nat.

Definition tableaddr_eq_dec : forall (v1 v2 : tableaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tableaddr_eqb (v1 v2 : tableaddr) : bool :=
	is_left(tableaddr_eq_dec v1 v2).
Definition eqtableaddrP : Equality.axiom (tableaddr_eqb) :=
	eq_dec_Equality_axiom (tableaddr) (tableaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tableaddr) (eqtableaddrP).
Hint Resolve tableaddr_eq_dec : eq_dec_db.

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:9.1-9.50 *)
Definition memaddr := nat.

Definition memaddr_eq_dec : forall (v1 v2 : memaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition memaddr_eqb (v1 v2 : memaddr) : bool :=
	is_left(memaddr_eq_dec v1 v2).
Definition eqmemaddrP : Equality.axiom (memaddr_eqb) :=
	eq_dec_Equality_axiom (memaddr) (memaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (memaddr) (eqmemaddrP).
Hint Resolve memaddr_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:20.1-21.70 *)
Inductive externaddr : Type :=
	| EXTVAL_FUNC (v_funcaddr : funcaddr) : externaddr
	| EXTVAL_GLOBAL (v_globaladdr : globaladdr) : externaddr
	| EXTVAL_TABLE (v_tableaddr : tableaddr) : externaddr
	| EXTVAL_MEM (v_memaddr : memaddr) : externaddr.

Global Instance Inhabited__externaddr : Inhabited (externaddr) := { default_val := EXTVAL_FUNC default_val }.

Definition externaddr_eq_dec : forall (v1 v2 : externaddr),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition externaddr_eqb (v1 v2 : externaddr) : bool :=
	is_left(externaddr_eq_dec v1 v2).
Definition eqexternaddrP : Equality.axiom (externaddr_eqb) :=
	eq_dec_Equality_axiom (externaddr) (externaddr_eq_dec).

HB.instance Definition _ := hasDecEq.Build (externaddr) (eqexternaddrP).
Hint Resolve externaddr_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.1-33.55 *)
Inductive val : Type :=
	| VAL_CONST (v_valtype : valtype) (v_val_ : (val_ v_valtype)) : val.

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

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.1-36.22 *)
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

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.1-63.22 *)
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
	NAME := arg1.(NAME); (* FIXME - Non-trivial append*)
	ADDR := arg1.(ADDR); (* FIXME - Non-trivial append*)
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

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.1-71.26 *)
Record moduleinst := MKmoduleinst
{	MODULE_TYPES : (list functype)
;	MODULE_FUNCS : (list funcaddr)
;	MODULE_GLOBALS : (list globaladdr)
;	MODULE_TABLES : (list tableaddr)
;	MODULE_MEMS : (list memaddr)
;	MODULE_EXPORTS : (list exportinst)
}.

Global Instance Inhabited_moduleinst : Inhabited moduleinst := 
{default_val := {|
	MODULE_TYPES := default_val;
	MODULE_FUNCS := default_val;
	MODULE_GLOBALS := default_val;
	MODULE_TABLES := default_val;
	MODULE_MEMS := default_val;
	MODULE_EXPORTS := default_val|} }.

Definition _append_moduleinst (arg1 arg2 : moduleinst) :=
{|
	MODULE_TYPES := arg1.(MODULE_TYPES) @@ arg2.(MODULE_TYPES);
	MODULE_FUNCS := arg1.(MODULE_FUNCS) @@ arg2.(MODULE_FUNCS);
	MODULE_GLOBALS := arg1.(MODULE_GLOBALS) @@ arg2.(MODULE_GLOBALS);
	MODULE_TABLES := arg1.(MODULE_TABLES) @@ arg2.(MODULE_TABLES);
	MODULE_MEMS := arg1.(MODULE_MEMS) @@ arg2.(MODULE_MEMS);
	MODULE_EXPORTS := arg1.(MODULE_EXPORTS) @@ arg2.(MODULE_EXPORTS);
|}.

Global Instance Append_moduleinst : Append moduleinst := { _append arg1 arg2 := _append_moduleinst arg1 arg2 }.

#[export] Instance eta__moduleinst : Settable _ := settable! MKmoduleinst <MODULE_TYPES;MODULE_FUNCS;MODULE_GLOBALS;MODULE_TABLES;MODULE_MEMS;MODULE_EXPORTS>.

Definition moduleinst_eq_dec : forall (v1 v2 : moduleinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition moduleinst_eqb (v1 v2 : moduleinst) : bool :=
	is_left(moduleinst_eq_dec v1 v2).
Definition eqmoduleinstP : Equality.axiom (moduleinst_eqb) :=
	eq_dec_Equality_axiom (moduleinst) (moduleinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (moduleinst) (eqmoduleinstP).
Hint Resolve moduleinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.1-51.16 *)
Record funcinst := MKfuncinst
{	FUNC_TYPE : functype
;	FUNC_MODULE : moduleinst
;	CODE : func
}.

Global Instance Inhabited_funcinst : Inhabited funcinst := 
{default_val := {|
	FUNC_TYPE := default_val;
	FUNC_MODULE := default_val;
	CODE := default_val|} }.

Definition _append_funcinst (arg1 arg2 : funcinst) :=
{|
	FUNC_TYPE := arg1.(FUNC_TYPE); (* FIXME - Non-trivial append*)
	FUNC_MODULE := arg1.(FUNC_MODULE); (* FIXME - Non-trivial append*)
	CODE := arg1.(CODE); (* FIXME - Non-trivial append*)
|}.

Global Instance Append_funcinst : Append funcinst := { _append arg1 arg2 := _append_funcinst arg1 arg2 }.

#[export] Instance eta__funcinst : Settable _ := settable! MKfuncinst <FUNC_TYPE;FUNC_MODULE;CODE>.

Definition funcinst_eq_dec : forall (v1 v2 : funcinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition funcinst_eqb (v1 v2 : funcinst) : bool :=
	is_left(funcinst_eq_dec v1 v2).
Definition eqfuncinstP : Equality.axiom (funcinst_eqb) :=
	eq_dec_Equality_axiom (funcinst) (funcinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (funcinst) (eqfuncinstP).
Hint Resolve funcinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.1-54.16 *)
Record globalinst := MKglobalinst
{	GLOB_TYPE : globaltype
;	VALUE : val
}.

Global Instance Inhabited_globalinst : Inhabited globalinst := 
{default_val := {|
	GLOB_TYPE := default_val;
	VALUE := default_val|} }.

Definition _append_globalinst (arg1 arg2 : globalinst) :=
{|
	GLOB_TYPE := arg1.(GLOB_TYPE); (* FIXME - Non-trivial append*)
	VALUE := arg1.(VALUE); (* FIXME - Non-trivial append*)
|}.

Global Instance Append_globalinst : Append globalinst := { _append arg1 arg2 := _append_globalinst arg1 arg2 }.

#[export] Instance eta__globalinst : Settable _ := settable! MKglobalinst <GLOB_TYPE;VALUE>.

Definition globalinst_eq_dec : forall (v1 v2 : globalinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition globalinst_eqb (v1 v2 : globalinst) : bool :=
	is_left(globalinst_eq_dec v1 v2).
Definition eqglobalinstP : Equality.axiom (globalinst_eqb) :=
	eq_dec_Equality_axiom (globalinst) (globalinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (globalinst) (eqglobalinstP).
Hint Resolve globalinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.1-57.24 *)
Record tableinst := MKtableinst
{	TAB_TYPE : tabletype
;	REFS : (list (option funcaddr))
}.

Global Instance Inhabited_tableinst : Inhabited tableinst := 
{default_val := {|
	TAB_TYPE := default_val;
	REFS := default_val|} }.

Definition _append_tableinst (arg1 arg2 : tableinst) :=
{|
	TAB_TYPE := arg1.(TAB_TYPE); (* FIXME - Non-trivial append*)
	REFS := arg1.(REFS) @@ arg2.(REFS);
|}.

Global Instance Append_tableinst : Append tableinst := { _append arg1 arg2 := _append_tableinst arg1 arg2 }.

#[export] Instance eta__tableinst : Settable _ := settable! MKtableinst <TAB_TYPE;REFS>.

Definition tableinst_eq_dec : forall (v1 v2 : tableinst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition tableinst_eqb (v1 v2 : tableinst) : bool :=
	is_left(tableinst_eq_dec v1 v2).
Definition eqtableinstP : Equality.axiom (tableinst_eqb) :=
	eq_dec_Equality_axiom (tableinst) (tableinst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (tableinst) (eqtableinstP).
Hint Resolve tableinst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.1-60.18 *)
Record meminst := MKmeminst
{	MEM_TYPE : memtype
;	BYTES : (list byte)
}.

Global Instance Inhabited_meminst : Inhabited meminst := 
{default_val := {|
	MEM_TYPE := default_val;
	BYTES := default_val|} }.

Definition _append_meminst (arg1 arg2 : meminst) :=
{|
	MEM_TYPE := arg1.(MEM_TYPE); (* FIXME - Non-trivial append*)
	BYTES := arg1.(BYTES) @@ arg2.(BYTES);
|}.

Global Instance Append_meminst : Append meminst := { _append arg1 arg2 := _append_meminst arg1 arg2 }.

#[export] Instance eta__meminst : Settable _ := settable! MKmeminst <MEM_TYPE;BYTES>.

Definition meminst_eq_dec : forall (v1 v2 : meminst),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition meminst_eqb (v1 v2 : meminst) : bool :=
	is_left(meminst_eq_dec v1 v2).
Definition eqmeminstP : Equality.axiom (meminst_eqb) :=
	eq_dec_Equality_axiom (meminst) (meminst_eq_dec).

HB.instance Definition _ := hasDecEq.Build (meminst) (eqmeminstP).
Hint Resolve meminst_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.1-87.20 *)
Record store := MKstore
{	FUNCS : (list funcinst)
;	GLOBALS : (list globalinst)
;	TABLES : (list tableinst)
;	MEMS : (list meminst)
}.

Global Instance Inhabited_store : Inhabited store := 
{default_val := {|
	FUNCS := default_val;
	GLOBALS := default_val;
	TABLES := default_val;
	MEMS := default_val|} }.

Definition _append_store (arg1 arg2 : store) :=
{|
	FUNCS := arg1.(FUNCS) @@ arg2.(FUNCS);
	GLOBALS := arg1.(GLOBALS) @@ arg2.(GLOBALS);
	TABLES := arg1.(TABLES) @@ arg2.(TABLES);
	MEMS := arg1.(MEMS) @@ arg2.(MEMS);
|}.

Global Instance Append_store : Append store := { _append arg1 arg2 := _append_store arg1 arg2 }.

#[export] Instance eta__store : Settable _ := settable! MKstore <FUNCS;GLOBALS;TABLES;MEMS>.

Definition store_eq_dec : forall (v1 v2 : store),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition store_eqb (v1 v2 : store) : bool :=
	is_left(store_eq_dec v1 v2).
Definition eqstoreP : Equality.axiom (store_eqb) :=
	eq_dec_Equality_axiom (store) (store_eq_dec).

HB.instance Definition _ := hasDecEq.Build (store) (eqstoreP).
Hint Resolve store_eq_dec : eq_dec_db.

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.1-91.41 *)
Record frame := MKframe
{	LOCALS : (list val)
;	F_MODULE : moduleinst
}.

Global Instance Inhabited_frame : Inhabited frame := 
{default_val := {|
	LOCALS := default_val;
	F_MODULE := default_val|} }.

Definition _append_frame (arg1 arg2 : frame) :=
{|
	LOCALS := arg1.(LOCALS) @@ arg2.(LOCALS);
	F_MODULE := arg1.(F_MODULE); (* FIXME - Non-trivial append*)
|}.

Global Instance Append_frame : Append frame := { _append arg1 arg2 := _append_frame arg1 arg2 }.

#[export] Instance eta__frame : Settable _ := settable! MKframe <LOCALS;F_MODULE>.

Definition frame_eq_dec : forall (v1 v2 : frame),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition frame_eqb (v1 v2 : frame) : bool :=
	is_left(frame_eq_dec v1 v2).
Definition eqframeP : Equality.axiom (frame_eqb) :=
	eq_dec_Equality_axiom (frame) (frame_eq_dec).

HB.instance Definition _ := hasDecEq.Build (frame) (eqframeP).
Hint Resolve frame_eq_dec : eq_dec_db.

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.1-93.47 *)
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

(* Mutual Recursion at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 *)
(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 *)
Inductive admininstr : Type :=
	| AI_NOP : admininstr
	| AI_UNREACHABLE : admininstr
	| AI_DROP : admininstr
	| AI_SELECT : admininstr
	| AI_BLOCK (v_blocktype : blocktype) (_ : (list instr)) : admininstr
	| AI_LOOP (v_blocktype : blocktype) (_ : (list instr)) : admininstr
	| AI_IFELSE (v_blocktype : blocktype) (_ : (list instr)) (v__ : (list instr)) : admininstr
	| AI_BR (v_labelidx : labelidx) : admininstr
	| AI_BR_IF (v_labelidx : labelidx) : admininstr
	| AI_BR_TABLE (_ : (list labelidx)) (v__ : labelidx) : admininstr
	| AI_CALL (v_funcidx : funcidx) : admininstr
	| AI_CALL_INDIRECT (v_typeidx : typeidx) : admininstr
	| AI_RETURN : admininstr
	| AI_CONST (v_valtype : valtype) (v_val_ : (val_ v_valtype)) : admininstr
	| AI_UNOP (v_valtype : valtype) (v_unop_ : (unop_ v_valtype)) : admininstr
	| AI_BINOP (v_valtype : valtype) (v_binop_ : (binop_ v_valtype)) : admininstr
	| AI_TESTOP (v_valtype : valtype) (v_testop_ : (testop_ v_valtype)) : admininstr
	| AI_RELOP (v_valtype : valtype) (v_relop_ : (relop_ v_valtype)) : admininstr
	| AI_CVTOP (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_cvtop : cvtop) : admininstr
	| AI_LOCAL_GET (v_localidx : localidx) : admininstr
	| AI_LOCAL_SET (v_localidx : localidx) : admininstr
	| AI_LOCAL_TEE (v_localidx : localidx) : admininstr
	| AI_GLOBAL_GET (v_globalidx : globalidx) : admininstr
	| AI_GLOBAL_SET (v_globalidx : globalidx) : admininstr
	| AI_LOAD (v_valtype : valtype) (_ : (option (loadop_ v_valtype))) (v_memarg : memarg) : admininstr
	| AI_STORE (v_valtype : valtype) (_ : (option sz)) (v_memarg : memarg) : admininstr
	| AI_MEMORY_SIZE : admininstr
	| AI_MEMORY_GROW : admininstr
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

(* Auxiliary Definition at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 *)
Fixpoint wf_admininstr (v_x : admininstr) : Prop :=
	match v_x with
		| AI_NOP => True
		| AI_UNREACHABLE => True
		| AI_DROP => True
		| AI_SELECT => True
		| (AI_BLOCK v_blocktype v_instr) => True
		| (AI_LOOP v_blocktype v_instr) => True
		| (AI_IFELSE v_blocktype v_instr v__) => True
		| (AI_BR v_labelidx) => True
		| (AI_BR_IF v_labelidx) => True
		| (AI_BR_TABLE v_labelidx v__) => True
		| (AI_CALL v_funcidx) => True
		| (AI_CALL_INDIRECT v_typeidx) => True
		| AI_RETURN => True
		| (AI_CONST v_valtype v_val_) => True
		| (AI_UNOP v_valtype v_unop_) => True
		| (AI_BINOP v_valtype v_binop_) => True
		| (AI_TESTOP v_valtype v_testop_) => True
		| (AI_RELOP v_valtype v_relop_) => True
		| (AI_CVTOP v_valtype_1 v_valtype_2 v_cvtop) => (v_valtype_1 <> v_valtype_2)
		| (AI_LOCAL_GET v_localidx) => True
		| (AI_LOCAL_SET v_localidx) => True
		| (AI_LOCAL_TEE v_localidx) => True
		| (AI_GLOBAL_GET v_globalidx) => True
		| (AI_GLOBAL_SET v_globalidx) => True
		| (AI_LOAD v_valtype v_loadop_ v_memarg) => True
		| (AI_STORE v_valtype v_sz v_memarg) => forall (v_Inn : (option Inn)), List.Forall2 (fun (v_Inn : Inn) (v_sz : sz) => ((v_valtype = (v_Inn : valtype)) /\ ((fun_proj_sz_0 v_sz) < (fun_size (v_Inn : valtype))))) (option_to_list v_Inn) (option_to_list v_sz)
		| AI_MEMORY_SIZE => True
		| AI_MEMORY_GROW => True
		| (AI_CALL_ADDR v_funcaddr) => True
		| (AI_LABEL_ v_n v_instr v_admininstr) => True
		| (AI_FRAME_ v_n v_frame v_admininstr) => True
		| AI_TRAP => True
	end.

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.1-94.62 *)
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

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:7.1-7.29 *)
Definition fun_default_ (v_valtype : valtype) : val :=
	match v_valtype with
		| I32 => (VAL_CONST I32 (mk_uN _ 0))
		| I64 => (VAL_CONST I64 (mk_uN _ 0))
		| F32 => (VAL_CONST F32 (fun_fzero 32))
		| F64 => (VAL_CONST F64 (fun_fzero 64))
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:17.1-17.63 *)
(* Axiom Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:17.1-17.63 *)
Axiom fun_funcsxa : forall (var_0 : (list externaddr)), (list funcaddr).

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:18.1-18.65 *)
(* Axiom Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:18.1-18.65 *)
Axiom fun_globalsxa : forall (var_0 : (list externaddr)), (list globaladdr).

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:19.1-19.64 *)
(* Axiom Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:19.1-19.64 *)
Axiom fun_tablesxa : forall (var_0 : (list externaddr)), (list tableaddr).

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:20.1-20.62 *)
(* Axiom Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:20.1-20.62 *)
Axiom fun_memsxa : forall (var_0 : (list externaddr)), (list memaddr).

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:46.1-46.57 *)
Definition fun_store (v_state : state) : store :=
	match v_state with
		| (mk_state v_s v_f) => v_s
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:47.1-47.57 *)
Definition fun_frame (v_state : state) : frame :=
	match v_state with
		| (mk_state v_s v_f) => v_f
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:53.1-53.64 *)
Definition fun_funcaddr (v_state : state) : (list funcaddr) :=
	match v_state with
		| (mk_state v_s v_f) => (MODULE_FUNCS (F_MODULE v_f))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:56.1-56.57 *)
Definition fun_funcinst (v_state : state) : (list funcinst) :=
	match v_state with
		| (mk_state v_s v_f) => (FUNCS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:57.1-57.59 *)
Definition fun_globalinst (v_state : state) : (list globalinst) :=
	match v_state with
		| (mk_state v_s v_f) => (GLOBALS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:58.1-58.58 *)
Definition fun_tableinst (v_state : state) : (list tableinst) :=
	match v_state with
		| (mk_state v_s v_f) => (TABLES v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:59.1-59.56 *)
Definition fun_meminst (v_state : state) : (list meminst) :=
	match v_state with
		| (mk_state v_s v_f) => (MEMS v_s)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:60.1-60.58 *)
Definition fun_moduleinst (v_state : state) : moduleinst :=
	match v_state with
		| (mk_state v_s v_f) => (F_MODULE v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:68.1-68.66 *)
Definition fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
	match v_state, v_typeidx with
		| (mk_state v_s v_f), v_x => (lookup_total (MODULE_TYPES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:69.1-69.66 *)
Definition fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
	match v_state, v_funcidx with
		| (mk_state v_s v_f), v_x => (lookup_total (FUNCS v_s) (lookup_total (MODULE_FUNCS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:70.1-70.68 *)
Definition fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
	match v_state, v_globalidx with
		| (mk_state v_s v_f), v_x => (lookup_total (GLOBALS v_s) (lookup_total (MODULE_GLOBALS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:71.1-71.67 *)
Definition fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
	match v_state, v_tableidx with
		| (mk_state v_s v_f), v_x => (lookup_total (TABLES v_s) (lookup_total (MODULE_TABLES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:72.1-72.65 *)
Definition fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
	match v_state, v_memidx with
		| (mk_state v_s v_f), v_x => (lookup_total (MEMS v_s) (lookup_total (MODULE_MEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:73.1-73.67 *)
Definition fun_local (v_state : state) (v_localidx : localidx) : val :=
	match v_state, v_localidx with
		| (mk_state v_s v_f), v_x => (lookup_total (LOCALS v_f) (fun_proj_uN_0 32 v_x))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:85.1-85.89 *)
Definition fun_with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
	match v_state, v_localidx, v_val with
		| (mk_state v_s v_f), v_x, v_v => (mk_state v_s (v_f <| LOCALS := (list_update_func (LOCALS v_f) (fun_proj_uN_0 32 v_x) (fun (_ : val) => v_v)) |>))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:86.1-86.96 *)
Definition fun_with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
	match v_state, v_globalidx, v_val with
		| (mk_state v_s v_f), v_x, v_v => (mk_state (v_s <| GLOBALS := (list_update_func (GLOBALS v_s) (lookup_total (MODULE_GLOBALS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : globalinst) => (v_1 <| VALUE := v_v |>))) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:87.1-87.97 *)
Definition fun_with_table (v_state : state) (v_tableidx : tableidx) (v_nat : nat) (v_funcaddr : funcaddr) : state :=
	match v_state, v_tableidx, v_nat, v_funcaddr with
		| (mk_state v_s v_f), v_x, v_i, v_a => (mk_state (v_s <| TABLES := (list_update_func (TABLES v_s) (lookup_total (MODULE_TABLES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : tableinst) => (v_1 <| REFS := (list_update_func (REFS v_1) v_i (fun (_ : (option funcaddr)) => (Some v_a))) |>))) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:88.1-88.89 *)
Definition fun_with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
	match v_state, v_tableidx, v_tableinst with
		| (mk_state v_s v_f), v_x, v_ti => (mk_state (v_s <| TABLES := (list_update_func (TABLES v_s) (lookup_total (MODULE_TABLES (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (_ : tableinst) => v_ti)) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:89.1-89.100 *)
Definition fun_with_mem (v_state : state) (v_memidx : memidx) (v_nat : nat) (v_nat_0 : nat) (var_0 : (list byte)) : state :=
	match v_state, v_memidx, v_nat, v_nat_0, var_0 with
		| (mk_state v_s v_f), v_x, v_i, v_j, v_b => (mk_state (v_s <| MEMS := (list_update_func (MEMS v_s) (lookup_total (MODULE_MEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (v_1 : meminst) => (v_1 <| BYTES := (list_slice_update (BYTES v_1) v_i v_j v_b) |>))) |>) v_f)
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:90.1-90.87 *)
Definition fun_with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
	match v_state, v_memidx, v_meminst with
		| (mk_state v_s v_f), v_x, v_mi => (mk_state (v_s <| MEMS := (list_update_func (MEMS v_s) (lookup_total (MODULE_MEMS (F_MODULE v_f)) (fun_proj_uN_0 32 v_x)) (fun (_ : meminst) => v_mi)) |>) v_f)
	end.

(* Axiom Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:102.1-102.58 *)
Axiom fun_growtable : forall (v_tableinst : tableinst) (v_nat : nat), (option tableinst).

(* Axiom Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:103.1-103.58 *)
Axiom fun_growmemory : forall (v_meminst : meminst) (v_nat : nat), (option meminst).

(* Record Creation Definition at: ../specification/wasm-1.0/6-typing.spectec:5.1-8.62 *)
Record context := MKcontext
{	C_TYPES : (list functype)
;	C_FUNCS : (list functype)
;	C_GLOBALS : (list globaltype)
;	C_TABLES : (list tabletype)
;	C_MEMS : (list memtype)
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
	C_LOCALS := arg1.(C_LOCALS) @@ arg2.(C_LOCALS);
	C_LABELS := arg1.(C_LABELS) @@ arg2.(C_LABELS);
	C_RETURN := arg1.(C_RETURN) @@ arg2.(C_RETURN); (* FIXME - Non-trivial append*)
|}.

Global Instance Append_context : Append context := { _append arg1 arg2 := _append_context arg1 arg2 }.

#[export] Instance eta__context : Settable _ := settable! MKcontext <C_TYPES;C_FUNCS;C_GLOBALS;C_TABLES;C_MEMS;C_LOCALS;C_LABELS;C_RETURN>.

Definition context_eq_dec : forall (v1 v2 : context),
  {v1 = v2} + {v1 <> v2}.
Proof. do ? decidable_equality_step. Defined.

Definition context_eqb (v1 v2 : context) : bool :=
	is_left(context_eq_dec v1 v2).
Definition eqcontextP : Equality.axiom (context_eqb) :=
	eq_dec_Equality_axiom (context) (context_eq_dec).

HB.instance Definition _ := hasDecEq.Build (context) (eqcontextP).
Hint Resolve context_eq_dec : eq_dec_db.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:18.1-18.66 *)
Inductive Limits_ok: limits -> nat -> Prop :=
	| mk_Limits_ok : forall (v_n : n) (v_m : m) (v_k : nat), ((v_n <= v_m) /\ (v_m <= v_k)) -> Limits_ok (mk_limits (mk_uN _ v_n) (mk_uN _ v_m)) v_k.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:19.1-19.64 *)
Inductive Functype_ok: functype -> Prop :=
	| mk_Functype_ok : forall (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), Functype_ok (mk_functype v_t_1 (option_to_list v_t_2)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:20.1-20.66 *)
Inductive Globaltype_ok: globaltype -> Prop :=
	| mk_Globaltype_ok : forall (v_t : valtype), Globaltype_ok (mk_globaltype (Some MUT) v_t).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:21.1-21.65 *)
Inductive Tabletype_ok: tabletype -> Prop :=
	| mk_Tabletype_ok : forall (v_limits : limits), (Limits_ok v_limits ((((2 ^ 32) : nat) - (1 : nat)) : nat)) -> Tabletype_ok v_limits.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:22.1-22.63 *)
Inductive Memtype_ok: memtype -> Prop :=
	| mk_Memtype_ok : forall (v_limits : limits), (Limits_ok v_limits (2 ^ 16)) -> Memtype_ok v_limits.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:23.1-23.86 *)
Inductive Externtype_ok: externtype -> Prop :=
	| ext_func : forall (v_functype : functype), (Functype_ok v_functype) -> Externtype_ok (EXT_FUNC v_functype)
	| ext_global : forall (v_globaltype : globaltype), (Globaltype_ok v_globaltype) -> Externtype_ok (EXT_GLOBAL v_globaltype)
	| ext_table : forall (v_tabletype : tabletype), (Tabletype_ok v_tabletype) -> Externtype_ok (EXT_TABLE v_tabletype)
	| ext_mem : forall (v_memtype : memtype), (Memtype_ok v_memtype) -> Externtype_ok (EXT_MEM v_memtype).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:69.1-69.75 *)
Inductive Limits_sub: limits -> limits -> Prop :=
	| mk_Limits_sub : forall (v_n_11 : n) (v_n_12 : n) (v_n_21 : n) (v_n_22 : n), (v_n_11 >= v_n_21) -> (v_n_12 <= v_n_22) -> Limits_sub (mk_limits (mk_uN _ v_n_11) (mk_uN _ v_n_12)) (mk_limits (mk_uN _ v_n_21) (mk_uN _ v_n_22)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:70.1-70.73 *)
Inductive Functype_sub: functype -> functype -> Prop :=
	| mk_Functype_sub : forall (v_ft : functype), Functype_sub v_ft v_ft.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:71.1-71.75 *)
Inductive Globaltype_sub: globaltype -> globaltype -> Prop :=
	| mk_Globaltype_sub : forall (v_gt : globaltype), Globaltype_sub v_gt v_gt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:72.1-72.74 *)
Inductive Tabletype_sub: tabletype -> tabletype -> Prop :=
	| mk_Tabletype_sub : forall (v_lim_1 : limits) (v_lim_2 : limits), (Limits_sub v_lim_1 v_lim_2) -> Tabletype_sub v_lim_1 v_lim_2.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:73.1-73.72 *)
Inductive Memtype_sub: memtype -> memtype -> Prop :=
	| mk_Memtype_sub : forall (v_lim_1 : limits) (v_lim_2 : limits), (Limits_sub v_lim_1 v_lim_2) -> Memtype_sub v_lim_1 v_lim_2.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:74.1-74.98 *)
Inductive Externtype_sub: externtype -> externtype -> Prop :=
	| extsub_func : forall (v_ft_1 : functype) (v_ft_2 : functype), (Functype_sub v_ft_1 v_ft_2) -> Externtype_sub (EXT_FUNC v_ft_1) (EXT_FUNC v_ft_2)
	| extsub_global : forall (v_gt_1 : globaltype) (v_gt_2 : globaltype), (Globaltype_sub v_gt_1 v_gt_2) -> Externtype_sub (EXT_GLOBAL v_gt_1) (EXT_GLOBAL v_gt_2)
	| extsub_table : forall (v_tt_1 : tabletype) (v_tt_2 : tabletype), (Tabletype_sub v_tt_1 v_tt_2) -> Externtype_sub (EXT_TABLE v_tt_1) (EXT_TABLE v_tt_2)
	| extsub_mem : forall (v_mt_1 : memtype) (v_mt_2 : memtype), (Memtype_sub v_mt_1 v_mt_2) -> Externtype_sub (EXT_MEM v_mt_1) (EXT_MEM v_mt_2).

(* Mutual Recursion at: ../specification/wasm-1.0/6-typing.spectec:119.1-120.88 *)
(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:119.1-119.64 *)
Inductive Instr_ok: context -> instr -> functype -> Prop :=
	| nop : forall (v_C : context), Instr_ok v_C NOP (mk_functype [] [])
	| unreachable : forall (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Instr_ok v_C UNREACHABLE (mk_functype v_t_1 v_t_2)
	| drop : forall (v_C : context) (v_t : valtype), Instr_ok v_C DROP (mk_functype [v_t] [])
	| select : forall (v_C : context) (v_t : valtype), Instr_ok v_C SELECT (mk_functype [v_t; v_t; I32] [v_t])
	| block : forall (v_C : context) (v_t : (option valtype)) (v_instr : (list instr)), (Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := [v_t]; C_RETURN := None |} @@ v_C) v_instr (mk_functype [] (option_to_list v_t))) -> Instr_ok v_C (BLOCK v_t v_instr) (mk_functype [] (option_to_list v_t))
	| loop : forall (v_C : context) (v_t : (option valtype)) (v_instr : (list instr)), (Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := None |} @@ v_C) v_instr (mk_functype [] [])) -> Instr_ok v_C (LOOP v_t v_instr) (mk_functype [] (option_to_list v_t))
	| res_if : forall (v_C : context) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), (Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := [v_t]; C_RETURN := None |} @@ v_C) v_instr_1 (mk_functype [] (option_to_list v_t))) -> (Instrs_ok ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := [v_t]; C_RETURN := None |} @@ v_C) v_instr_2 (mk_functype [] (option_to_list v_t))) -> Instr_ok v_C (IFELSE v_t v_instr_1 v_instr_2) (mk_functype [I32] (option_to_list v_t))
	| br : forall (v_C : context) (v_l : labelidx) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), ((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C))) -> ((lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l)) = v_t) -> Instr_ok v_C (BR v_l) (mk_functype (v_t_1 ++ (option_to_list v_t)) v_t_2)
	| br_if : forall (v_C : context) (v_l : labelidx) (v_t : (option valtype)), ((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C))) -> ((lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l)) = v_t) -> Instr_ok v_C (BR_IF v_l) (mk_functype ((option_to_list v_t) ++ [I32]) (option_to_list v_t))
	| br_table : forall (v_C : context) (v_l : (list labelidx)) (v_l' : labelidx) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), ((fun_proj_uN_0 32 v_l') < (List.length (C_LABELS v_C))) -> (v_t = (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l'))) -> List.Forall (fun (v_l : labelidx) => ((fun_proj_uN_0 32 v_l) < (List.length (C_LABELS v_C)))) (v_l) -> List.Forall (fun (v_l : labelidx) => (v_t = (lookup_total (C_LABELS v_C) (fun_proj_uN_0 32 v_l)))) (v_l) -> Instr_ok v_C (BR_TABLE v_l v_l') (mk_functype (v_t_1 ++ ((option_to_list v_t) ++ [I32])) v_t_2)
	| call : forall (v_C : context) (v_x : idx) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), ((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) -> ((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = (mk_functype v_t_1 (option_to_list v_t_2))) -> Instr_ok v_C (CALL v_x) (mk_functype v_t_1 (option_to_list v_t_2))
	| call_indirect : forall (v_C : context) (v_x : idx) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), ((fun_proj_uN_0 32 v_x) < (List.length (C_TYPES v_C))) -> ((lookup_total (C_TYPES v_C) (fun_proj_uN_0 32 v_x)) = (mk_functype v_t_1 (option_to_list v_t_2))) -> Instr_ok v_C (CALL_INDIRECT v_x) (mk_functype (v_t_1 ++ [I32]) (option_to_list v_t_2))
	| res_return : forall (v_C : context) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), ((C_RETURN v_C) = (Some v_t)) -> Instr_ok v_C RETURN (mk_functype (v_t_1 ++ (option_to_list v_t)) v_t_2)
	| const : forall (v_C : context) (v_t : valtype) (v_c_t : (val_ v_t)), Instr_ok v_C (CONST v_t v_c_t) (mk_functype [] [v_t])
	| unop : forall (v_C : context) (v_t : valtype) (v_unop_t : (unop_ v_t)), Instr_ok v_C (UNOP v_t v_unop_t) (mk_functype [v_t] [v_t])
	| binop : forall (v_C : context) (v_t : valtype) (v_binop_t : (binop_ v_t)), Instr_ok v_C (BINOP v_t v_binop_t) (mk_functype [v_t; v_t] [v_t])
	| testop : forall (v_C : context) (v_t : valtype) (v_testop_t : (testop_ v_t)), Instr_ok v_C (TESTOP v_t v_testop_t) (mk_functype [v_t] [I32])
	| relop : forall (v_C : context) (v_t : valtype) (v_relop_t : (relop_ v_t)), Instr_ok v_C (RELOP v_t v_relop_t) (mk_functype [v_t; v_t] [I32])
	| cvtop_reinterpret : forall (v_C : context) (v_nt_1 : valtype) (v_nt_2 : valtype), ((fun_size v_nt_1) = (fun_size v_nt_2)) -> Instr_ok v_C (CVTOP v_nt_1 v_nt_2 REINTERPRET) (mk_functype [v_nt_2] [v_nt_1])
	| cvtop_convert : forall (v_C : context) (v_nt_1 : valtype) (v_nt_2 : valtype) (v_cvtop : cvtop), Instr_ok v_C (CVTOP v_nt_1 v_nt_2 v_cvtop) (mk_functype [v_nt_2] [v_nt_1])
	| local_get : forall (v_C : context) (v_x : idx) (v_t : valtype), ((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) -> ((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t) -> Instr_ok v_C (LOCAL_GET v_x) (mk_functype [] [v_t])
	| local_set : forall (v_C : context) (v_x : idx) (v_t : valtype), ((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) -> ((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t) -> Instr_ok v_C (LOCAL_SET v_x) (mk_functype [v_t] [])
	| local_tee : forall (v_C : context) (v_x : idx) (v_t : valtype), ((fun_proj_uN_0 32 v_x) < (List.length (C_LOCALS v_C))) -> ((lookup_total (C_LOCALS v_C) (fun_proj_uN_0 32 v_x)) = v_t) -> Instr_ok v_C (LOCAL_TEE v_x) (mk_functype [v_t] [v_t])
	| global_get : forall (v_C : context) (v_x : idx) (v_t : valtype) (v_mut : mut), ((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) -> ((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype v_mut v_t)) -> Instr_ok v_C (GLOBAL_GET v_x) (mk_functype [] [v_t])
	| global_set : forall (v_C : context) (v_x : idx) (v_t : valtype), ((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) -> ((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype (Some MUT) v_t)) -> Instr_ok v_C (GLOBAL_SET v_x) (mk_functype [v_t] [])
	| memory_size : forall (v_C : context) (v_mt : memtype), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_mt) -> Instr_ok v_C MEMORY_SIZE (mk_functype [] [I32])
	| memory_grow : forall (v_C : context) (v_mt : memtype), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_mt) -> Instr_ok v_C MEMORY_GROW (mk_functype [I32] [I32])
	| load_val : forall (v_C : context) (v_t : valtype) (v_memarg : memarg) (v_mt : memtype), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_mt) -> (((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((fun_size v_t) : nat) / (8 : nat))) -> Instr_ok v_C (LOAD v_t None v_memarg) (mk_functype [I32] [v_t])
	| load_pack_I32 : forall (v_C : context) (v_M : M) (v_sx : sx) (v_memarg : memarg) (v_mt : memtype), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_mt) -> (((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat))) -> Instr_ok v_C (LOAD (INN_I32 : valtype) (Some (op__ _ (mk_sz v_M) v_sx)) v_memarg) (mk_functype [I32] [(INN_I32 : valtype)])
	| load_pack_I64 : forall (v_C : context) (v_M : M) (v_sx : sx) (v_memarg : memarg) (v_mt : memtype), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_mt) -> (((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat))) -> Instr_ok v_C (LOAD (INN_I64 : valtype) (Some (op__ _ (mk_sz v_M) v_sx)) v_memarg) (mk_functype [I32] [(INN_I64 : valtype)])
	| store_val : forall (v_C : context) (v_t : valtype) (v_memarg : memarg) (v_mt : memtype), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_mt) -> (((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= (((fun_size v_t) : nat) / (8 : nat))) -> Instr_ok v_C (STORE v_t None v_memarg) (mk_functype [I32; v_t] [])
	| store_pack : forall (v_C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (v_mt : memtype), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_mt) -> (((2 ^ (fun_proj_uN_0 32 (ALIGN v_memarg))) : nat) <= ((v_M : nat) / (8 : nat))) -> Instr_ok v_C (STORE (v_Inn : valtype) (Some (mk_sz v_M)) v_memarg) (mk_functype [I32; (v_Inn : valtype)] [])

with

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:120.1-120.88 *)
Instrs_ok: context -> (list instr) -> functype -> Prop :=
	| instrs_empty : forall (v_C : context), Instrs_ok v_C [] (mk_functype [] [])
	| instrs_seq : forall (v_C : context) (v_instr_1 : (list instr)) (v_instr_2 : instr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), (Instrs_ok v_C v_instr_1 (mk_functype v_t_1 v_t_2)) -> (Instr_ok v_C v_instr_2 (mk_functype v_t_2 v_t_3)) -> Instrs_ok v_C (v_instr_1 ++ [v_instr_2]) (mk_functype v_t_1 v_t_3)
	| instrs_frame : forall (v_C : context) (v_instr : (list instr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Instrs_ok v_C v_instr (mk_functype v_t_1 v_t_2)) -> Instrs_ok v_C v_instr (mk_functype (v_t ++ v_t_1) (v_t ++ v_t_2)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:121.1-121.69 *)
Inductive Expr_ok: context -> expr -> resulttype -> Prop :=
	| mk_Expr_ok : forall (v_C : context) (v_instr : (list instr)) (v_t : (option valtype)), (Instrs_ok v_C v_instr (mk_functype [] (option_to_list v_t))) -> Expr_ok v_C v_instr v_t.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:314.1-314.103 *)
Inductive Instr_const: context -> instr -> Prop :=
	| C_instr_const : forall (v_C : context) (v_t : valtype) (v_c : (val_ v_t)), Instr_const v_C (CONST v_t v_c)
	| C_instr_global_get : forall (v_C : context) (v_x : idx) (v_t : valtype), ((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) -> ((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = (mk_globaltype None v_t)) -> Instr_const v_C (GLOBAL_GET v_x).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:315.1-315.78 *)
Inductive Expr_const: context -> expr -> Prop :=
	| mk_Expr_const : forall (v_C : context) (v_instr : (list instr)), List.Forall (fun (v_instr : instr) => (Instr_const v_C v_instr)) (v_instr) -> Expr_const v_C v_instr.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:316.1-316.79 *)
Inductive Expr_ok_const: context -> expr -> (option valtype) -> Prop :=
	| mk_Expr_ok_const : forall (v_C : context) (v_expr : expr) (v_t : (option valtype)), (Expr_ok v_C v_expr v_t) -> (Expr_const v_C v_expr) -> Expr_ok_const v_C v_expr v_t.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:340.1-340.73 *)
Inductive Type_ok: type -> functype -> Prop :=
	| mk_Type_ok : forall (v_ft : functype), (Functype_ok v_ft) -> Type_ok (TYPE v_ft) v_ft.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:341.1-341.73 *)
Inductive Func_ok: context -> func -> functype -> Prop :=
	| mk_Func_ok : forall (v_C : context) (v_x : idx) (v_t : (list valtype)) (v_expr : expr) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), ((fun_proj_uN_0 32 v_x) < (List.length (C_TYPES v_C))) -> ((lookup_total (C_TYPES v_C) (fun_proj_uN_0 32 v_x)) = (mk_functype v_t_1 (option_to_list v_t_2))) -> (Expr_ok (v_C @@ {| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := (v_t_1 ++ v_t); C_LABELS := [v_t_2]; C_RETURN := (Some v_t_2) |}) v_expr v_t_2) -> Func_ok v_C (FUNC v_x (List.map (fun (v_t : valtype) => (LOCAL v_t)) v_t) v_expr) (mk_functype v_t_1 (option_to_list v_t_2)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:342.1-342.75 *)
Inductive Global_ok: context -> global -> globaltype -> Prop :=
	| mk_Global_ok : forall (v_C : context) (v_gt : globaltype) (v_expr : expr) (v_mut : mut) (v_t : valtype), (Globaltype_ok v_gt) -> (v_gt = (mk_globaltype v_mut v_t)) -> (Expr_ok_const v_C v_expr (Some v_t)) -> Global_ok v_C (GLOBAL v_gt v_expr) v_gt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:343.1-343.74 *)
Inductive Table_ok: context -> table -> tabletype -> Prop :=
	| mk_Table_ok : forall (v_C : context) (v_tt : tabletype), (Tabletype_ok v_tt) -> Table_ok v_C (TABLE v_tt) v_tt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:344.1-344.72 *)
Inductive Mem_ok: context -> mem -> memtype -> Prop :=
	| mk_Mem_ok : forall (v_C : context) (v_mt : memtype), (Memtype_ok v_mt) -> Mem_ok v_C (MEMORY v_mt) v_mt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:345.1-345.73 *)
Inductive Elem_ok: context -> elem -> Prop :=
	| mk_Elem_ok : forall (v_C : context) (v_expr : expr) (v_x : (list idx)) (v_lim : limits) (v_ft : (list functype)), (0 < (List.length (C_TABLES v_C))) -> ((lookup_total (C_TABLES v_C) 0) = v_lim) -> (Expr_ok_const v_C v_expr (Some I32)) -> ((List.length v_ft) = (List.length v_x)) -> List.Forall (fun (v_x : idx) => ((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C)))) (v_x) -> List.Forall2 (fun (v_ft : functype) (v_x : idx) => ((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = v_ft)) (v_ft) (v_x) -> Elem_ok v_C (ELEM v_expr v_x).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:346.1-346.73 *)
Inductive Data_ok: context -> data -> Prop :=
	| mk_Data_ok : forall (v_C : context) (v_expr : expr) (v_b : (list byte)) (v_lim : limits), (0 < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) 0) = v_lim) -> (Expr_ok_const v_C v_expr (Some I32)) -> Data_ok v_C (DATA v_expr v_b).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:347.1-347.74 *)
Inductive Start_ok: context -> start -> Prop :=
	| mk_Start_ok : forall (v_C : context) (v_x : idx), ((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) -> ((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = (mk_functype [] [])) -> Start_ok v_C (START v_x).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:395.1-395.80 *)
Inductive Import_ok: context -> import -> externtype -> Prop :=
	| mk_Import_ok : forall (v_C : context) (v_name_1 : name) (v_name_2 : name) (v_xt : externtype), (Externtype_ok v_xt) -> Import_ok v_C (IMPORT v_name_1 v_name_2 v_xt) v_xt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:397.1-397.102 *)
Inductive Externidx_ok: context -> externidx -> externtype -> Prop :=
	| OK_func : forall (v_C : context) (v_x : idx) (v_ft : functype), ((fun_proj_uN_0 32 v_x) < (List.length (C_FUNCS v_C))) -> ((lookup_total (C_FUNCS v_C) (fun_proj_uN_0 32 v_x)) = v_ft) -> Externidx_ok v_C (EXTIDX_FUNC v_x) (EXT_FUNC v_ft)
	| OK_global : forall (v_C : context) (v_x : idx) (v_gt : globaltype), ((fun_proj_uN_0 32 v_x) < (List.length (C_GLOBALS v_C))) -> ((lookup_total (C_GLOBALS v_C) (fun_proj_uN_0 32 v_x)) = v_gt) -> Externidx_ok v_C (EXTIDX_GLOBAL v_x) (EXT_GLOBAL v_gt)
	| OK_table : forall (v_C : context) (v_x : idx) (v_tt : tabletype), ((fun_proj_uN_0 32 v_x) < (List.length (C_TABLES v_C))) -> ((lookup_total (C_TABLES v_C) (fun_proj_uN_0 32 v_x)) = v_tt) -> Externidx_ok v_C (EXTIDX_TABLE v_x) (EXT_TABLE v_tt)
	| OK_mem : forall (v_C : context) (v_x : idx) (v_mt : memtype), ((fun_proj_uN_0 32 v_x) < (List.length (C_MEMS v_C))) -> ((lookup_total (C_MEMS v_C) (fun_proj_uN_0 32 v_x)) = v_mt) -> Externidx_ok v_C (EXTIDX_MEM v_x) (EXT_MEM v_mt).

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:396.1-396.80 *)
Inductive Export_ok: context -> export -> externtype -> Prop :=
	| mk_Export_ok : forall (v_C : context) (v_name : name) (v_externidx : externidx) (v_xt : externtype), (Externidx_ok v_C v_externidx v_xt) -> Export_ok v_C (EXPORT v_name v_externidx) v_xt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:427.1-427.62 *)
Inductive Module_ok: module -> Prop :=
	| mk_Module_ok : forall (v_type : (list type)) (v_import : (list import)) (v_func : (list func)) (v_global : (list global)) (v_table : (list table)) (v_mem : (list mem)) (v_elem : (list elem)) (v_data : (list data)) (v_start : (option start)) (v_export : (list export)) (v_ft' : (list functype)) (v_ixt : (list externtype)) (v_C' : context) (v_gt : (list globaltype)) (v_C : context) (v_ft : (list functype)) (v_tt : (list tabletype)) (v_mt : (list memtype)) (v_xt : (list externtype)) (v_ift : (list functype)) (v_igt : (list globaltype)) (v_itt : (list tabletype)) (v_imt : (list memtype)), ((List.length v_ft') = (List.length v_type)) -> List.Forall2 (fun (v_ft' : functype) (v_type : type) => (Type_ok v_type v_ft')) (v_ft') (v_type) -> ((List.length v_import) = (List.length v_ixt)) -> List.Forall2 (fun (v_import : import) (v_ixt : externtype) => (Import_ok {| C_TYPES := v_ft'; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := None |} v_import v_ixt)) (v_import) (v_ixt) -> ((List.length v_global) = (List.length v_gt)) -> List.Forall2 (fun (v_global : global) (v_gt : globaltype) => (Global_ok v_C' v_global v_gt)) (v_global) (v_gt) -> ((List.length v_ft) = (List.length v_func)) -> List.Forall2 (fun (v_ft : functype) (v_func : func) => (Func_ok v_C v_func v_ft)) (v_ft) (v_func) -> ((List.length v_table) = (List.length v_tt)) -> List.Forall2 (fun (v_table : table) (v_tt : tabletype) => (Table_ok v_C v_table v_tt)) (v_table) (v_tt) -> ((List.length v_mem) = (List.length v_mt)) -> List.Forall2 (fun (v_mem : mem) (v_mt : memtype) => (Mem_ok v_C v_mem v_mt)) (v_mem) (v_mt) -> List.Forall (fun (v_elem : elem) => (Elem_ok v_C v_elem)) (v_elem) -> List.Forall (fun (v_data : data) => (Data_ok v_C v_data)) (v_data) -> List.Forall (fun (v_start : start) => (Start_ok v_C v_start)) (option_to_list v_start) -> ((List.length v_export) = (List.length v_xt)) -> List.Forall2 (fun (v_export : export) (v_xt : externtype) => (Export_ok v_C v_export v_xt)) (v_export) (v_xt) -> ((List.length v_tt) <= 1) -> ((List.length v_mt) <= 1) -> (v_C = {| C_TYPES := v_ft'; C_FUNCS := (v_ift ++ v_ft); C_GLOBALS := (v_igt ++ v_gt); C_TABLES := (v_itt ++ v_tt); C_MEMS := (v_imt ++ v_mt); C_LOCALS := []; C_LABELS := []; C_RETURN := None |}) -> (v_C' = {| C_TYPES := v_ft'; C_FUNCS := (v_ift ++ v_ft); C_GLOBALS := v_igt; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := None |}) -> (v_ift = (fun_funcsxt v_ixt)) -> (v_igt = (fun_globalsxt v_ixt)) -> (v_itt = (fun_tablesxt v_ixt)) -> (v_imt = (fun_memsxt v_ixt)) -> Module_ok (MODULE v_type v_import v_func v_global v_table v_mem v_elem v_data v_start v_export).

(* Auxiliary Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.98 *)
Definition fun_coec_val__admininstr (v_val : val) : admininstr :=
	match v_val with
		| (VAL_CONST v_0 v_1) => (AI_CONST v_0 v_1)
	end.

(* Type Coercion Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.98 *)
Coercion fun_coec_val__admininstr : val >-> admininstr.

(* Auxiliary Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.98 *)
Definition fun_coec_instr__admininstr (v_instr : instr) : admininstr :=
	match v_instr with
		| NOP => AI_NOP
		| UNREACHABLE => AI_UNREACHABLE
		| DROP => AI_DROP
		| SELECT => AI_SELECT
		| (BLOCK v_0 v_1) => (AI_BLOCK v_0 v_1)
		| (LOOP v_0 v_1) => (AI_LOOP v_0 v_1)
		| (IFELSE v_0 v_1 v_2) => (AI_IFELSE v_0 v_1 v_2)
		| (BR v_0) => (AI_BR v_0)
		| (BR_IF v_0) => (AI_BR_IF v_0)
		| (BR_TABLE v_0 v_1) => (AI_BR_TABLE v_0 v_1)
		| (CALL v_0) => (AI_CALL v_0)
		| (CALL_INDIRECT v_0) => (AI_CALL_INDIRECT v_0)
		| RETURN => AI_RETURN
		| (CONST v_0 v_1) => (AI_CONST v_0 v_1)
		| (UNOP v_0 v_1) => (AI_UNOP v_0 v_1)
		| (BINOP v_0 v_1) => (AI_BINOP v_0 v_1)
		| (TESTOP v_0 v_1) => (AI_TESTOP v_0 v_1)
		| (RELOP v_0 v_1) => (AI_RELOP v_0 v_1)
		| (CVTOP v_0 v_1 v_2) => (AI_CVTOP v_0 v_1 v_2)
		| (LOCAL_GET v_0) => (AI_LOCAL_GET v_0)
		| (LOCAL_SET v_0) => (AI_LOCAL_SET v_0)
		| (LOCAL_TEE v_0) => (AI_LOCAL_TEE v_0)
		| (GLOBAL_GET v_0) => (AI_GLOBAL_GET v_0)
		| (GLOBAL_SET v_0) => (AI_GLOBAL_SET v_0)
		| (LOAD v_0 v_1 v_2) => (AI_LOAD v_0 v_1 v_2)
		| (STORE v_0 v_1 v_2) => (AI_STORE v_0 v_1 v_2)
		| MEMORY_SIZE => AI_MEMORY_SIZE
		| MEMORY_GROW => AI_MEMORY_GROW
	end.

(* Type Coercion Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.98 *)
Coercion fun_coec_instr__admininstr : instr >-> admininstr.

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.98 *)
Inductive Step_pure: (list admininstr) -> (list admininstr) -> Prop :=
	| step_unreachable : Step_pure [AI_UNREACHABLE] [AI_TRAP]
	| step_nop : Step_pure [AI_NOP] []
	| step_drop : forall (v_val : val), Step_pure [(v_val : admininstr); AI_DROP] []
	| step_select_true : forall (v_val_1 : val) (v_val_2 : val) (v_c : (uN 32)), ((fun_proj_uN_0 32 v_c) <> 0) -> Step_pure [(v_val_1 : admininstr); (v_val_2 : admininstr); (AI_CONST I32 v_c); AI_SELECT] [(v_val_1 : admininstr)]
	| step_select_false : forall (v_val_1 : val) (v_val_2 : val) (v_c : (uN 32)), ((fun_proj_uN_0 32 v_c) = 0) -> Step_pure [(v_val_1 : admininstr); (v_val_2 : admininstr); (AI_CONST I32 v_c); AI_SELECT] [(v_val_2 : admininstr)]
	| step_if_true : forall (v_c : (uN 32)) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), ((fun_proj_uN_0 32 v_c) <> 0) -> Step_pure [(AI_CONST I32 v_c); (AI_IFELSE v_t v_instr_1 v_instr_2)] [(AI_BLOCK v_t v_instr_1)]
	| step_if_false : forall (v_c : (uN 32)) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), ((fun_proj_uN_0 32 v_c) = 0) -> Step_pure [(AI_CONST I32 v_c); (AI_IFELSE v_t v_instr_1 v_instr_2)] [(AI_BLOCK v_t v_instr_2)]
	| step_label_vals : forall (v_n : n) (v_instr : (list instr)) (v_val : (list val)), Step_pure [(AI_LABEL_ v_n v_instr (List.map (fun (v_val : val) => (v_val : admininstr)) v_val))] (List.map (fun (v_val : val) => (v_val : admininstr)) v_val)
	| step_br_zero : forall (v_n : n) (v_instr' : (list instr)) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)), Step_pure [(AI_LABEL_ v_n v_instr' ((List.map (fun (v_val' : val) => (v_val' : admininstr)) v_val') ++ ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([(AI_BR (mk_uN _ 0))] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)))))] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))
	| step_br_succ : forall (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_l : labelidx) (v_instr : (list instr)), Step_pure [(AI_LABEL_ v_n v_instr' ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([(AI_BR (mk_uN _ ((fun_proj_uN_0 32 v_l) + 1)))] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))))] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [(AI_BR v_l)])
	| step_br_if_true : forall (v_c : (uN 32)) (v_l : labelidx), ((fun_proj_uN_0 32 v_c) <> 0) -> Step_pure [(AI_CONST I32 v_c); (AI_BR_IF v_l)] [(AI_BR v_l)]
	| step_br_if_false : forall (v_c : (uN 32)) (v_l : labelidx), ((fun_proj_uN_0 32 v_c) = 0) -> Step_pure [(AI_CONST I32 v_c); (AI_BR_IF v_l)] []
	| step_br_table_lt : forall (v_i : (uN 32)) (v_l : (list labelidx)) (v_l' : labelidx), ((fun_proj_uN_0 32 v_i) < (List.length v_l)) -> Step_pure [(AI_CONST I32 v_i); (AI_BR_TABLE v_l v_l')] [(AI_BR (lookup_total v_l (fun_proj_uN_0 32 v_i)))]
	| step_br_table_ge : forall (v_i : (uN 32)) (v_l : (list labelidx)) (v_l' : labelidx), ((fun_proj_uN_0 32 v_i) >= (List.length v_l)) -> Step_pure [(AI_CONST I32 v_i); (AI_BR_TABLE v_l v_l')] [(AI_BR v_l')]
	| step_frame_vals : forall (v_n : n) (v_f : frame) (v_val : (list val)), Step_pure [(AI_FRAME_ v_n v_f (List.map (fun (v_val : val) => (v_val : admininstr)) v_val))] (List.map (fun (v_val : val) => (v_val : admininstr)) v_val)
	| step_return_frame : forall (v_n : n) (v_f : frame) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)), Step_pure [(AI_FRAME_ v_n v_f ((List.map (fun (v_val' : val) => (v_val' : admininstr)) v_val') ++ ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([AI_RETURN] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)))))] (List.map (fun (v_val : val) => (v_val : admininstr)) v_val)
	| step_return_label : forall (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_instr : (list instr)), Step_pure [(AI_LABEL_ v_n v_instr' ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([AI_RETURN] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))))] ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [AI_RETURN])
	| step_trap_vals : forall (v_val : (list val)) (v_instr : (list instr)), ((v_val <> []) \/ (v_instr <> [])) -> Step_pure ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ ([AI_TRAP] ++ (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))) [AI_TRAP]
	| step_trap_label : forall (v_n : n) (v_instr' : (list instr)), Step_pure [(AI_LABEL_ v_n v_instr' [AI_TRAP])] [AI_TRAP]
	| step_trap_frame : forall (v_n : n) (v_f : frame), Step_pure [(AI_FRAME_ v_n v_f [AI_TRAP])] [AI_TRAP]
	| step_unop_val : forall (v_t : valtype) (v_c_1 : (val_ v_t)) (v_unop : (unop_ v_t)) (v_c : (val_ v_t)), ((List.length (fun_unop_ v_t v_unop v_c_1)) > 0) -> (List.In v_c (fun_unop_ v_t v_unop v_c_1)) -> Step_pure [(AI_CONST v_t v_c_1); (AI_UNOP v_t v_unop)] [(AI_CONST v_t v_c)]
	| step_unop_trap : forall (v_t : valtype) (v_c_1 : (val_ v_t)) (v_unop : (unop_ v_t)), ((fun_unop_ v_t v_unop v_c_1) = []) -> Step_pure [(AI_CONST v_t v_c_1); (AI_UNOP v_t v_unop)] [AI_TRAP]
	| step_binop_val : forall (v_t : valtype) (v_c_1 : (val_ v_t)) (v_c_2 : (val_ v_t)) (v_binop : (binop_ v_t)) (v_c : (val_ v_t)), ((List.length (fun_binop_ v_t v_binop v_c_1 v_c_2)) > 0) -> (List.In v_c (fun_binop_ v_t v_binop v_c_1 v_c_2)) -> Step_pure [(AI_CONST v_t v_c_1); (AI_CONST v_t v_c_2); (AI_BINOP v_t v_binop)] [(AI_CONST v_t v_c)]
	| step_binop_trap : forall (v_t : valtype) (v_c_1 : (val_ v_t)) (v_c_2 : (val_ v_t)) (v_binop : (binop_ v_t)), ((fun_binop_ v_t v_binop v_c_1 v_c_2) = []) -> Step_pure [(AI_CONST v_t v_c_1); (AI_CONST v_t v_c_2); (AI_BINOP v_t v_binop)] [AI_TRAP]
	| step_testop : forall (v_t : valtype) (v_c_1 : (val_ v_t)) (v_testop : (testop_ v_t)) (v_c : (uN 32)), (v_c = (fun_testop_ v_t v_testop v_c_1)) -> Step_pure [(AI_CONST v_t v_c_1); (AI_TESTOP v_t v_testop)] [(AI_CONST I32 v_c)]
	| step_relop : forall (v_t : valtype) (v_c_1 : (val_ v_t)) (v_c_2 : (val_ v_t)) (v_relop : (relop_ v_t)) (v_c : (uN 32)), (v_c = (fun_relop_ v_t v_relop v_c_1 v_c_2)) -> Step_pure [(AI_CONST v_t v_c_1); (AI_CONST v_t v_c_2); (AI_RELOP v_t v_relop)] [(AI_CONST I32 v_c)]
	| step_cvtop_val : forall (v_t_1 : valtype) (v_c_1 : (val_ v_t_1)) (v_t_2 : valtype) (v_cvtop : cvtop) (v_c : (val_ v_t_2)), ((List.length (fun_cvtop__ v_t_1 v_t_2 v_cvtop v_c_1)) > 0) -> (List.In v_c (fun_cvtop__ v_t_1 v_t_2 v_cvtop v_c_1)) -> Step_pure [(AI_CONST v_t_1 v_c_1); (AI_CVTOP v_t_2 v_t_1 v_cvtop)] [(AI_CONST v_t_2 v_c)]
	| step_cvtop_trap : forall (v_t_1 : valtype) (v_c_1 : (val_ v_t_1)) (v_t_2 : valtype) (v_cvtop : cvtop), ((fun_cvtop__ v_t_1 v_t_2 v_cvtop v_c_1) = []) -> Step_pure [(AI_CONST v_t_1 v_c_1); (AI_CVTOP v_t_2 v_t_1 v_cvtop)] [AI_TRAP]
	| step_local_tee : forall (v_val : val) (v_x : idx), Step_pure [(v_val : admininstr); (AI_LOCAL_TEE v_x)] [(v_val : admininstr); (v_val : admininstr); (AI_LOCAL_SET v_x)].

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:7.1-7.98 *)
Inductive Step_read_before_call_indirect_trap: config -> Prop :=
	| call_indirect_call_neg : forall (v_z : state) (v_i : (uN 32)) (v_x : idx) (v_a : addr), ((fun_proj_uN_0 32 v_i) < (List.length (REFS (fun_table v_z (mk_uN _ 0))))) -> ((lookup_total (REFS (fun_table v_z (mk_uN _ 0))) (fun_proj_uN_0 32 v_i)) = (Some v_a)) -> (v_a < (List.length (fun_funcinst v_z))) -> ((fun_type v_z v_x) = (FUNC_TYPE (lookup_total (fun_funcinst v_z) v_a))) -> Step_read_before_call_indirect_trap (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x)]).

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:7.1-7.98 *)
Inductive Step_read: config -> (list admininstr) -> Prop :=
	| step_block : forall (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) (v_n : n), (((v_t = None) /\ (v_n = 0)) \/ ((v_t <> None) /\ (v_n = 1))) -> Step_read (mk_config v_z [(AI_BLOCK v_t v_instr)]) [(AI_LABEL_ v_n [] (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))]
	| step_loop : forall (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)), Step_read (mk_config v_z [(AI_LOOP v_t v_instr)]) [(AI_LABEL_ 0 [(LOOP v_t v_instr)] (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))]
	| step_call : forall (v_z : state) (v_x : idx), ((fun_proj_uN_0 32 v_x) < (List.length (fun_funcaddr v_z))) -> Step_read (mk_config v_z [(AI_CALL v_x)]) [(AI_CALL_ADDR (lookup_total (fun_funcaddr v_z) (fun_proj_uN_0 32 v_x)))]
	| step_call_indirect_call : forall (v_z : state) (v_i : (uN 32)) (v_x : idx) (v_a : addr), ((fun_proj_uN_0 32 v_i) < (List.length (REFS (fun_table v_z (mk_uN _ 0))))) -> ((lookup_total (REFS (fun_table v_z (mk_uN _ 0))) (fun_proj_uN_0 32 v_i)) = (Some v_a)) -> (v_a < (List.length (fun_funcinst v_z))) -> ((fun_type v_z v_x) = (FUNC_TYPE (lookup_total (fun_funcinst v_z) v_a))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x)]) [(AI_CALL_ADDR v_a)]
	| step_call_indirect_trap : forall (v_z : state) (v_i : (uN 32)) (v_x : idx), (~(Step_read_before_call_indirect_trap (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x)]))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_CALL_INDIRECT v_x)]) [AI_TRAP]
	| step_call_addr : forall (v_z : state) (v_val : (list val)) (v_k : nat) (v_a : addr) (v_n : n) (v_f : frame) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)) (v_mm : moduleinst) (v_func : func) (v_x : idx) (v_t : (list valtype)), (v_a < (List.length (fun_funcinst v_z))) -> ((lookup_total (fun_funcinst v_z) v_a) = {| FUNC_TYPE := (mk_functype v_t_1 v_t_2); FUNC_MODULE := v_mm; CODE := v_func |}) -> (v_func = (FUNC v_x (List.map (fun (v_t : valtype) => (LOCAL v_t)) v_t) v_instr)) -> (v_f = {| LOCALS := (v_val ++ (List.map (fun (v_t : valtype) => (fun_default_ v_t)) v_t)); F_MODULE := v_mm |}) -> Step_read (mk_config v_z ((List.map (fun (v_val : val) => (v_val : admininstr)) v_val) ++ [(AI_CALL_ADDR v_a)])) [(AI_FRAME_ v_n v_f [(AI_LABEL_ v_n [] (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))])]
	| step_local_get : forall (v_z : state) (v_x : idx), Step_read (mk_config v_z [(AI_LOCAL_GET v_x)]) [((fun_local v_z v_x) : admininstr)]
	| step_global_get : forall (v_z : state) (v_x : idx), Step_read (mk_config v_z [(AI_GLOBAL_GET v_x)]) [((VALUE (fun_global v_z v_x)) : admininstr)]
	| step_load_num_trap : forall (v_z : state) (v_i : (uN 32)) (v_t : valtype) (v_ao : memarg), ((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((fun_size v_t) : nat) / (8 : nat)) : nat)) > (List.length (BYTES (fun_mem v_z (mk_uN _ 0))))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD v_t None v_ao)]) [AI_TRAP]
	| step_load_num_val : forall (v_z : state) (v_i : (uN 32)) (v_t : valtype) (v_ao : memarg) (v_c : (val_ v_t)), ((fun_bytes_ v_t v_c) = (list_slice (BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) ((((fun_size v_t) : nat) / (8 : nat)) : nat))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD v_t None v_ao)]) [(AI_CONST v_t v_c)]
	| step_load_pack_trap_I32 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg), ((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (BYTES (fun_mem v_z (mk_uN _ 0))))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I32 : valtype) (Some (op__ _ (mk_sz v_n) v_sx)) v_ao)]) [AI_TRAP]
	| step_load_pack_trap_I64 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg), ((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (BYTES (fun_mem v_z (mk_uN _ 0))))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I64 : valtype) (Some (op__ _ (mk_sz v_n) v_sx)) v_ao)]) [AI_TRAP]
	| step_load_pack_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg) (v_c : (iN v_n)), ((fun_ibytes_ v_n v_c) = (list_slice (BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I32 : valtype) (Some (op__ _ (mk_sz v_n) v_sx)) v_ao)]) [(AI_CONST (INN_I32 : valtype) (fun_extend__ v_n (fun_size (INN_I32 : valtype)) v_sx v_c))]
	| step_load_pack_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_n : n) (v_sx : sx) (v_ao : memarg) (v_c : (iN v_n)), ((fun_ibytes_ v_n v_c) = (list_slice (BYTES (fun_mem v_z (mk_uN _ 0))) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat))) -> Step_read (mk_config v_z [(AI_CONST I32 v_i); (AI_LOAD (INN_I64 : valtype) (Some (op__ _ (mk_sz v_n) v_sx)) v_ao)]) [(AI_CONST (INN_I64 : valtype) (fun_extend__ v_n (fun_size (INN_I64 : valtype)) v_sx v_c))]
	| step_memory_size : forall (v_z : state) (v_n : n), (((v_n * 64) * fun_Ki) = (List.length (BYTES (fun_mem v_z (mk_uN _ 0))))) -> Step_read (mk_config v_z [AI_MEMORY_SIZE]) [(AI_CONST I32 (mk_uN _ v_n))].

(* Mutual Recursion at: ../specification/wasm-1.0/8-reduction.spectec:5.1-5.98 *)
(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:5.1-5.98 *)
Inductive Step: config -> config -> Prop :=
	| step_pure : forall (v_z : state) (v_instr : (list instr)) (v_instr' : (list instr)), (Step_pure (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr) (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr')) -> Step (mk_config v_z (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)) (mk_config v_z (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))
	| step_read : forall (v_z : state) (v_instr : (list instr)) (v_instr' : (list instr)), (Step_read (mk_config v_z (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)) (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr')) -> Step (mk_config v_z (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)) (mk_config v_z (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))
	| step_ctxt_label : forall (v_z : state) (v_n : n) (v_instr_0 : (list instr)) (v_instr : (list instr)) (v_z' : state) (v_instr' : (list instr)), (Step (mk_config v_z (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)) (mk_config v_z' (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))) -> Step (mk_config v_z [(AI_LABEL_ v_n v_instr_0 (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))]) (mk_config v_z' [(AI_LABEL_ v_n v_instr_0 (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))])
	| step_ctxt_frame : forall (v_s : store) (v_f : frame) (v_n : n) (v_f' : frame) (v_instr : (list instr)) (v_s' : store) (v_instr' : (list instr)), (Step (mk_config (mk_state v_s v_f') (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)) (mk_config (mk_state v_s' v_f') (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))) -> Step (mk_config (mk_state v_s v_f) [(AI_FRAME_ v_n v_f' (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr))]) (mk_config (mk_state v_s' v_f) [(AI_FRAME_ v_n v_f' (List.map (fun (v_instr' : instr) => (v_instr' : admininstr)) v_instr'))])
	| step_local_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (mk_config v_z [(v_val : admininstr); (AI_LOCAL_SET v_x)]) (mk_config (fun_with_local v_z v_x v_val) [])
	| step_global_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (mk_config v_z [(v_val : admininstr); (AI_GLOBAL_SET v_x)]) (mk_config (fun_with_global v_z v_x v_val) [])
	| step_store_num_trap : forall (v_z : state) (v_i : (uN 32)) (v_t : valtype) (v_c : (val_ v_t)) (v_ao : memarg), ((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + ((((fun_size v_t) : nat) / (8 : nat)) : nat)) > (List.length (BYTES (fun_mem v_z (mk_uN _ 0))))) -> Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST v_t v_c); (AI_STORE v_t None v_ao)]) (mk_config v_z [AI_TRAP])
	| step_store_num_val : forall (v_z : state) (v_i : (uN 32)) (v_t : valtype) (v_c : (val_ v_t)) (v_ao : memarg) (v_b : (list byte)), (v_b = (fun_bytes_ v_t v_c)) -> Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST v_t v_c); (AI_STORE v_t None v_ao)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) ((((fun_size v_t) : nat) / (8 : nat)) : nat) v_b) [])
	| step_store_pack_trap_I32 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 32)) (v_n : n) (v_ao : memarg), ((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (BYTES (fun_mem v_z (mk_uN _ 0))))) -> Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I32 : valtype) v_c); (AI_STORE (INN_I32 : valtype) (Some (mk_sz v_n)) v_ao)]) (mk_config v_z [AI_TRAP])
	| step_store_pack_trap_I64 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 64)) (v_n : n) (v_ao : memarg), ((((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) + (((v_n : nat) / (8 : nat)) : nat)) > (List.length (BYTES (fun_mem v_z (mk_uN _ 0))))) -> Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I64 : valtype) v_c); (AI_STORE (INN_I64 : valtype) (Some (mk_sz v_n)) v_ao)]) (mk_config v_z [AI_TRAP])
	| step_store_pack_val_I32 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 32)) (v_n : n) (v_ao : memarg) (v_b : (list byte)), (v_b = (fun_ibytes_ v_n (fun_wrap__ (fun_size (INN_I32 : valtype)) v_n v_c))) -> Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I32 : valtype) v_c); (AI_STORE (INN_I32 : valtype) (Some (mk_sz v_n)) v_ao)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat) v_b) [])
	| step_store_pack_val_I64 : forall (v_z : state) (v_i : (uN 32)) (v_c : (uN 64)) (v_n : n) (v_ao : memarg) (v_b : (list byte)), (v_b = (fun_ibytes_ v_n (fun_wrap__ (fun_size (INN_I64 : valtype)) v_n v_c))) -> Step (mk_config v_z [(AI_CONST I32 v_i); (AI_CONST (INN_I64 : valtype) v_c); (AI_STORE (INN_I64 : valtype) (Some (mk_sz v_n)) v_ao)]) (mk_config (fun_with_mem v_z (mk_uN _ 0) ((fun_proj_uN_0 32 v_i) + (fun_proj_uN_0 32 (OFFSET v_ao))) (((v_n : nat) / (8 : nat)) : nat) v_b) [])
	| step_memory_grow_succeed : forall (v_z : state) (v_n : n) (v_mi : meminst), ((fun_growmemory (fun_mem v_z (mk_uN _ 0)) v_n) <> None) -> ((the (fun_growmemory (fun_mem v_z (mk_uN _ 0)) v_n)) = v_mi) -> Step (mk_config v_z [(AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_GROW]) (mk_config (fun_with_meminst v_z (mk_uN _ 0) v_mi) [(AI_CONST I32 (mk_uN _ ((((List.length (BYTES (fun_mem v_z (mk_uN _ 0)))) : nat) / ((64 * fun_Ki) : nat)) : nat)))])
	| step_memory_grow_fail : forall (v_z : state) (v_n : n), Step (mk_config v_z [(AI_CONST I32 (mk_uN _ v_n)); AI_MEMORY_GROW]) (mk_config v_z [(AI_CONST I32 (mk_uN _ (fun_invsigned_ 32 (0 - (1 : nat)))))]).

(* Mutual Recursion at: ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77 *)
(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77 *)
Inductive Steps: config -> config -> Prop :=
	| refl : forall (v_z : state) (v_admininstr : (list admininstr)), Steps (mk_config v_z v_admininstr) (mk_config v_z v_admininstr)
	| trans : forall (v_z : state) (v_admininstr : (list admininstr)) (v_z'' : state) (v_admininstr'' : (list admininstr)) (v_z' : state) (v_admininstr' : (list admininstr)), (Step (mk_config v_z v_admininstr) (mk_config v_z' v_admininstr')) -> (Steps (mk_config v_z' v_admininstr') (mk_config v_z'' v_admininstr'')) -> Steps (mk_config v_z v_admininstr) (mk_config v_z'' v_admininstr'').

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:29.1-29.83 *)
Inductive Eval_expr: state -> expr -> state -> (list val) -> Prop :=
	| mk_Eval_expr : forall (v_z : state) (v_instr : (list instr)) (v_z' : state) (v_val : (list val)), (Steps (mk_config v_z (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr)) (mk_config v_z' (List.map (fun (v_val : val) => (v_val : admininstr)) v_val))) -> Eval_expr v_z v_instr v_z' v_val.

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:5.1-5.36 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:5.1-5.36 *)
Axiom fun_funcs : forall (var_0 : (list externaddr)), (list funcaddr).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:11.1-11.40 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:11.1-11.40 *)
Axiom fun_globals : forall (var_0 : (list externaddr)), (list globaladdr).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:17.1-17.38 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:17.1-17.38 *)
Axiom fun_tables : forall (var_0 : (list externaddr)), (list tableaddr).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:23.1-23.34 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:23.1-23.34 *)
Axiom fun_mems : forall (var_0 : (list externaddr)), (list memaddr).

(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:36.1-36.60 *)
Axiom fun_allocfunc : forall (v_store : store) (v_moduleinst : moduleinst) (v_func : func), (prod store funcaddr).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:41.1-41.63 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:41.1-41.63 *)
Axiom fun_allocfuncs : forall (v_store : store) (v_moduleinst : moduleinst) (var_0 : (list func)), (prod store (list funcaddr)).

(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:47.1-47.63 *)
Axiom fun_allocglobal : forall (v_store : store) (v_globaltype : globaltype) (v_val : val), (prod store globaladdr).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:51.1-51.67 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:51.1-51.67 *)
Axiom fun_allocglobals : forall (v_store : store) (var_0 : (list globaltype)) (var_1 : (list val)), (prod store (list globaladdr)).

(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:57.1-57.55 *)
Axiom fun_alloctable : forall (v_store : store) (v_tabletype : tabletype), (prod store tableaddr).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:61.1-61.58 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:61.1-61.58 *)
Axiom fun_alloctables : forall (v_store : store) (var_0 : (list tabletype)), (prod store (list tableaddr)).

(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:67.1-67.49 *)
Axiom fun_allocmem : forall (v_store : store) (v_memtype : memtype), (prod store memaddr).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:71.1-71.52 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:71.1-71.52 *)
Axiom fun_allocmems : forall (v_store : store) (var_0 : (list memtype)), (prod store (list memaddr)).

(* Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:80.1-80.83 *)
Definition fun_instexport (var_0 : (list funcaddr)) (var_1 : (list globaladdr)) (var_2 : (list tableaddr)) (var_3 : (list memaddr)) (v_export : export) : exportinst :=
	match var_0, var_1, var_2, var_3, v_export with
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_FUNC v_x)) => {| NAME := v_name; ADDR := (EXTVAL_FUNC (lookup_total v_fa (fun_proj_uN_0 32 v_x))) |}
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_GLOBAL v_x)) => {| NAME := v_name; ADDR := (EXTVAL_GLOBAL (lookup_total v_ga (fun_proj_uN_0 32 v_x))) |}
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_TABLE v_x)) => {| NAME := v_name; ADDR := (EXTVAL_TABLE (lookup_total v_ta (fun_proj_uN_0 32 v_x))) |}
		| v_fa, v_ga, v_ta, v_ma, (EXPORT v_name (EXTIDX_MEM v_x)) => {| NAME := v_name; ADDR := (EXTVAL_MEM (lookup_total v_ma (fun_proj_uN_0 32 v_x))) |}
	end.

(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:87.1-87.73 *)
Axiom fun_allocmodule : forall (v_store : store) (v_module : module) (var_0 : (list externaddr)) (var_1 : (list val)), (prod store moduleinst).

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:128.1-128.61 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:128.1-128.61 *)
Axiom fun_initelem : forall (v_store : store) (v_moduleinst : moduleinst) (var_0 : (list u32)) (var_1 : (list (list funcaddr))), store.

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:134.1-134.57 *)
(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:134.1-134.57 *)
Axiom fun_initdata : forall (v_store : store) (v_moduleinst : moduleinst) (var_0 : (list u32)) (var_1 : (list (list byte))), store.

(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:140.1-140.54 *)
Axiom fun_instantiate : forall (v_store : store) (v_module : module) (var_0 : (list externaddr)), config.

(* Axiom Definition at: ../specification/wasm-1.0/9-module.spectec:169.1-169.44 *)
Axiom fun_invoke : forall (v_store : store) (v_funcaddr : funcaddr) (var_0 : (list val)), config.

(* Mutual Recursion at: ../specification/wasm-1.0/A-binary.spectec:20.1-22.82 *)
(* Mutual Recursion at: ../specification/wasm-1.0/A-binary.spectec:358.1-383.38 *)
(* Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:480.1-480.43 *)
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

(* Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:497.1-497.29 *)
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

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:8.1-8.34 *)
Inductive Val_ok: val -> valtype -> Prop :=
	| mk_Val_ok : forall (v_t : valtype) (v_c_t : (val_ v_t)), Val_ok (VAL_CONST v_t v_c_t) v_t.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:16.1-16.60 *)
Inductive Result_ok: result -> (list valtype) -> Prop :=
	| ok_result : forall (v_v : (list val)) (v_t : (list valtype)), ((List.length v_t) = (List.length v_v)) -> List.Forall2 (fun (v_t : valtype) (v_v : val) => (Val_ok v_v v_t)) (v_t) (v_v) -> Result_ok (_VALS v_v) v_t
	| ok_trap : forall (v_t : (list valtype)), Result_ok TRAP v_t.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:27.1-27.85 *)
Inductive Externaddrs_ok: store -> externaddr -> externtype -> Prop :=
	| extaddr_ok_func : forall (v_S : store) (v_a : addr) (v_ext : functype) (v_minst : moduleinst) (v_func : func), (v_a < (List.length (FUNCS v_S))) -> ((lookup_total (FUNCS v_S) v_a) = {| FUNC_TYPE := v_ext; FUNC_MODULE := v_minst; CODE := v_func |}) -> Externaddrs_ok v_S (EXTVAL_FUNC v_a) (EXT_FUNC v_ext)
	| extaddr_ok_table : forall (v_S : store) (v_a : addr) (v_tt : tabletype) (v_tt' : tabletype) (v_fa : (list (option funcaddr))), (v_a < (List.length (TABLES v_S))) -> ((lookup_total (TABLES v_S) v_a) = {| TAB_TYPE := v_tt'; REFS := v_fa |}) -> (Tabletype_sub v_tt' v_tt) -> Externaddrs_ok v_S (EXTVAL_TABLE v_a) (EXT_TABLE v_tt)
	| extaddr_ok_mem : forall (v_S : store) (v_a : addr) (v_mt : memtype) (v_mt' : memtype) (v_b : (list byte)), (v_a < (List.length (MEMS v_S))) -> ((lookup_total (MEMS v_S) v_a) = {| MEM_TYPE := v_mt'; BYTES := v_b |}) -> (Memtype_sub v_mt' v_mt) -> Externaddrs_ok v_S (EXTVAL_MEM v_a) (EXT_MEM v_mt)
	| extaddr_ok_global : forall (v_S : store) (v_a : addr) (v_mut : mut) (v_valtype : valtype) (v_val_ : (val_ v_valtype)), (v_a < (List.length (GLOBALS v_S))) -> ((lookup_total (GLOBALS v_S) v_a) = {| GLOB_TYPE := (mk_globaltype v_mut v_valtype); VALUE := (VAL_CONST v_valtype v_val_) |}) -> Externaddrs_ok v_S (EXTVAL_GLOBAL v_a) (EXT_GLOBAL (mk_globaltype v_mut v_valtype)).

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:49.1-49.56 *)
Inductive Memory_instance_ok: store -> meminst -> memtype -> Prop :=
	| mk_Memory_instance_ok : forall (v_S : store) (v_mt : memtype) (v_b : (list byte)) (v_n : n) (v_m : m), (v_mt = (mk_limits (mk_uN _ v_n) (mk_uN _ v_m))) -> ((List.length v_b) = ((v_n * 64) * fun_Ki)) -> (Memtype_ok v_mt) -> Memory_instance_ok v_S {| MEM_TYPE := v_mt; BYTES := v_b |} v_mt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:59.1-59.59 *)
Inductive Table_instance_ok: store -> tableinst -> tabletype -> Prop :=
	| mk_Table_instance_ok : forall (v_S : store) (v_tt : tabletype) (v_fa : (list (option funcaddr))) (v_n : n) (v_m : m) (v_functype : (list (option functype))), (v_tt = (mk_limits (mk_uN _ v_n) (mk_uN _ v_m))) -> ((List.length v_fa) = (List.length v_functype)) -> List.Forall2 (fun (v_fa : (option funcaddr)) (v_functype : (option functype)) => ((v_fa = None) <-> (v_functype = None))) (v_fa) (v_functype) -> List.Forall2 (fun (v_fa : (option funcaddr)) (v_functype : (option functype)) => List.Forall2 (fun (v_fa : funcaddr) (v_functype : functype) => (Externaddrs_ok v_S (EXTVAL_FUNC v_fa) (EXT_FUNC v_functype))) (option_to_list v_fa) (option_to_list v_functype)) (v_fa) (v_functype) -> (Tabletype_ok v_tt) -> Table_instance_ok v_S {| TAB_TYPE := v_tt; REFS := v_fa |} v_tt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:69.1-69.62 *)
Inductive Global_instance_ok: store -> globalinst -> globaltype -> Prop :=
	| mk_Global_instance_ok : forall (v_S : store) (v_gt : globaltype) (v_v : val) (v_mut : mut) (v_vt : valtype), (v_gt = (mk_globaltype v_mut v_vt)) -> (Globaltype_ok v_gt) -> (Val_ok v_v v_vt) -> Global_instance_ok v_S {| GLOB_TYPE := v_gt; VALUE := v_v |} v_gt.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:79.1-79.54 *)
Inductive Export_instance_ok: store -> exportinst -> Prop :=
	| mk_Export_instance_ok : forall (v_S : store) (v_name : name) (v_eaddr : externaddr) (v_ext : externtype), (Externaddrs_ok v_S v_eaddr v_ext) -> Export_instance_ok v_S {| NAME := v_name; ADDR := v_eaddr |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:87.1-87.59 *)
Inductive Module_instance_ok: store -> moduleinst -> context -> Prop :=
	| mk_Module_instance_ok : forall (v_S : store) (v_functype : (list functype)) (v_funcaddr : (list funcaddr)) (v_globaladdr : (list globaladdr)) (v_tableaddr : (list tableaddr)) (v_memaddr : (list memaddr)) (v_exportinst : (list exportinst)) (v_functype' : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)), List.Forall (fun (v_functype : functype) => (Functype_ok v_functype)) (v_functype) -> ((List.length v_funcaddr) = (List.length v_functype')) -> List.Forall2 (fun (v_funcaddr : funcaddr) (v_functype' : functype) => (Externaddrs_ok v_S (EXTVAL_FUNC v_funcaddr) (EXT_FUNC v_functype'))) (v_funcaddr) (v_functype') -> ((List.length v_tableaddr) = (List.length v_tabletype)) -> List.Forall2 (fun (v_tableaddr : tableaddr) (v_tabletype : tabletype) => (Externaddrs_ok v_S (EXTVAL_TABLE v_tableaddr) (EXT_TABLE v_tabletype))) (v_tableaddr) (v_tabletype) -> ((List.length v_globaladdr) = (List.length v_globaltype)) -> List.Forall2 (fun (v_globaladdr : globaladdr) (v_globaltype : globaltype) => (Externaddrs_ok v_S (EXTVAL_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype))) (v_globaladdr) (v_globaltype) -> ((List.length v_memaddr) = (List.length v_memtype)) -> List.Forall2 (fun (v_memaddr : memaddr) (v_memtype : memtype) => (Externaddrs_ok v_S (EXTVAL_MEM v_memaddr) (EXT_MEM v_memtype))) (v_memaddr) (v_memtype) -> List.Forall (fun (v_exportinst : exportinst) => (Export_instance_ok v_S v_exportinst)) (v_exportinst) -> Module_instance_ok v_S {| MODULE_TYPES := v_functype; MODULE_FUNCS := v_funcaddr; MODULE_GLOBALS := v_globaladdr; MODULE_TABLES := v_tableaddr; MODULE_MEMS := v_memaddr; MODULE_EXPORTS := v_exportinst |} {| C_TYPES := v_functype; C_FUNCS := v_functype'; C_GLOBALS := v_globaltype; C_TABLES := v_tabletype; C_MEMS := v_memtype; C_LOCALS := []; C_LABELS := []; C_RETURN := None |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:101.1-101.60 *)
Inductive Function_instance_ok: store -> funcinst -> functype -> Prop :=
	| mk_Function_instance_ok : forall (v_S : store) (v_functype : functype) (v_moduleinst : moduleinst) (v_func : func) (v_C : context), (Functype_ok v_functype) -> (Module_instance_ok v_S v_moduleinst v_C) -> (Func_ok v_C v_func v_functype) -> Function_instance_ok v_S {| FUNC_TYPE := v_functype; FUNC_MODULE := v_moduleinst; CODE := v_func |} v_functype.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:111.1-111.33 *)
Inductive Store_ok: store -> Prop :=
	| mk_Store_ok : forall (v_S : store) (v_funcinst : (list funcinst)) (v_globalinst : (list globalinst)) (v_tableinst : (list tableinst)) (v_meminst : (list meminst)) (v_functype : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)), (v_S = {| FUNCS := v_funcinst; GLOBALS := v_globalinst; TABLES := v_tableinst; MEMS := v_meminst |}) -> ((List.length v_funcinst) = (List.length v_functype)) -> List.Forall2 (fun (v_funcinst : funcinst) (v_functype : functype) => (Function_instance_ok v_S v_funcinst v_functype)) (v_funcinst) (v_functype) -> ((List.length v_globalinst) = (List.length v_globaltype)) -> List.Forall2 (fun (v_globalinst : globalinst) (v_globaltype : globaltype) => (Global_instance_ok v_S v_globalinst v_globaltype)) (v_globalinst) (v_globaltype) -> ((List.length v_tableinst) = (List.length v_tabletype)) -> List.Forall2 (fun (v_tableinst : tableinst) (v_tabletype : tabletype) => (Table_instance_ok v_S v_tableinst v_tabletype)) (v_tableinst) (v_tabletype) -> ((List.length v_meminst) = (List.length v_memtype)) -> List.Forall2 (fun (v_meminst : meminst) (v_memtype : memtype) => (Memory_instance_ok v_S v_meminst v_memtype)) (v_meminst) (v_memtype) -> Store_ok v_S.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:176.1-176.44 *)
Inductive Frame_ok: store -> frame -> context -> Prop :=
	| mk_Frame_ok : forall (v_S : store) (v_val : (list val)) (v_moduleinst : moduleinst) (v_C : context) (v_t : (list valtype)), (Module_instance_ok v_S v_moduleinst v_C) -> ((List.length v_t) = (List.length v_val)) -> List.Forall2 (fun (v_t : valtype) (v_val : val) => (Val_ok v_val v_t)) (v_t) (v_val) -> Frame_ok v_S {| LOCALS := v_val; F_MODULE := v_moduleinst |} ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := v_t; C_LABELS := []; C_RETURN := None |} @@ v_C).

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:123.1-125.75 *)
(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:123.1-123.87 *)
Inductive Admin_instr_ok: store -> context -> admininstr -> functype -> Prop :=
	| AI_ok_instr : forall (v_S : store) (v_C : context) (v_instr : instr) (v_functype : functype), (Instr_ok v_C v_instr v_functype) -> Admin_instr_ok v_S v_C (v_instr : admininstr) v_functype
	| AI_ok_trap : forall (v_S : store) (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Admin_instr_ok v_S v_C AI_TRAP (mk_functype v_t_1 v_t_2)
	| AI_ok_call_addr : forall (v_S : store) (v_C : context) (v_funcaddr : funcaddr) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (Externaddrs_ok v_S (EXTVAL_FUNC v_funcaddr) (EXT_FUNC (mk_functype v_t_1 (option_to_list v_t_2)))) -> Admin_instr_ok v_S v_C (AI_CALL_ADDR v_funcaddr) (mk_functype v_t_1 (option_to_list v_t_2))
	| AI_ok_label : forall (v_S : store) (v_C : context) (v_n : n) (v_instr : (list instr)) (v_admininstr : (list admininstr)) (v_t_2 : (option valtype)) (v_t_1 : (option valtype)), (Instrs_ok v_C v_instr (mk_functype (option_to_list v_t_1) (option_to_list v_t_2))) -> (Admin_instrs_ok v_S ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := [v_t_1]; C_RETURN := None |} @@ v_C) v_admininstr (mk_functype [] (option_to_list v_t_2))) -> (v_n = (fun_optionSize v_t_1)) -> Admin_instr_ok v_S v_C (AI_LABEL_ v_n v_instr v_admininstr) (mk_functype [] (option_to_list v_t_2))
	| AI_ok_frame : forall (v_S : store) (v_C : context) (v_n : n) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), (Thread_ok v_S (Some v_t) v_F v_admininstr v_t) -> (v_n = (fun_optionSize v_t)) -> Admin_instr_ok v_S v_C (AI_FRAME_ v_n v_F v_admininstr) (mk_functype [] (option_to_list v_t))
	| AI_ok_weakening : forall (v_S : store) (v_C : context) (v_admininstr : admininstr) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instr_ok v_S v_C v_admininstr (mk_functype v_t_1 v_t_2)) -> Admin_instr_ok v_S v_C v_admininstr (mk_functype (v_t ++ v_t_1) (v_t ++ v_t_2))

with

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:124.1-124.90 *)
Admin_instrs_ok: store -> context -> (list admininstr) -> functype -> Prop :=
	| AIs_ok_empty : forall (v_S : store) (v_C : context), Admin_instrs_ok v_S v_C [] (mk_functype [] [])
	| AIs_ok_seq : forall (v_S : store) (v_C : context) (v_admininstr_1 : (list admininstr)) (v_admininstr_2 : admininstr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instrs_ok v_S v_C v_admininstr_1 (mk_functype v_t_1 v_t_2)) -> (Admin_instr_ok v_S v_C v_admininstr_2 (mk_functype v_t_2 v_t_3)) -> Admin_instrs_ok v_S v_C (v_admininstr_1 ++ [v_admininstr_2]) (mk_functype v_t_1 v_t_3)
	| AIs_ok_frame : forall (v_S : store) (v_C : context) (v_admininstr : (list admininstr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instrs_ok v_S v_C v_admininstr (mk_functype v_t_1 v_t_2)) -> Admin_instrs_ok v_S v_C v_admininstr (mk_functype (v_t ++ v_t_1) (v_t ++ v_t_2))
	| AIs_ok_instrs : forall (v_S : store) (v_C : context) (v_instr : (list instr)) (v_functype : functype), (Instrs_ok v_C v_instr v_functype) -> Admin_instrs_ok v_S v_C (List.map (fun (v_instr : instr) => (v_instr : admininstr)) v_instr) v_functype

with

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:125.1-125.75 *)
Thread_ok: store -> (option resulttype) -> frame -> (list admininstr) -> resulttype -> Prop :=
	| mk_Thread_ok : forall (v_S : store) (v_rt : (option resulttype)) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)) (v_C : context), (Frame_ok v_S v_F v_C) -> (Admin_instrs_ok v_S ({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_LOCALS := []; C_LABELS := []; C_RETURN := v_rt |} @@ v_C) v_admininstr (mk_functype [] (option_to_list v_t))) -> Thread_ok v_S v_rt v_F v_admininstr v_t.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:188.1-188.43 *)
Inductive Config_ok: config -> resulttype -> Prop :=
	| mk_Config_ok : forall (v_S : store) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), (Store_ok v_S) -> (Thread_ok v_S None v_F v_admininstr v_t) -> Config_ok (mk_config (mk_state v_S v_F) v_admininstr) v_t.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:199.1-199.48 *)
Inductive Func_extension: funcinst -> funcinst -> Prop :=
	| mk_Func_extension : forall (v_funcinst : funcinst), Func_extension v_funcinst v_funcinst.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:200.1-200.51 *)
Inductive Table_extension: tableinst -> tableinst -> Prop :=
	| mk_Table_extension : forall (v_n1 : u32) (v_m : m) (v_fa_1 : (list (option funcaddr))) (v_n2 : u32) (v_fa_2 : (list (option funcaddr))), ((fun_proj_uN_0 32 v_n1) <= (fun_proj_uN_0 32 v_n2)) -> Table_extension {| TAB_TYPE := (mk_limits v_n1 (mk_uN _ v_m)); REFS := v_fa_1 |} {| TAB_TYPE := (mk_limits v_n2 (mk_uN _ v_m)); REFS := v_fa_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:201.1-201.45 *)
Inductive Mem_extension: meminst -> meminst -> Prop :=
	| mk_Mem_extension : forall (v_n1 : u32) (v_m : m) (v_b_1 : (list byte)) (v_n2 : u32) (v_b_2 : (list byte)), ((fun_proj_uN_0 32 v_n1) <= (fun_proj_uN_0 32 v_n2)) -> Mem_extension {| MEM_TYPE := (mk_limits v_n1 (mk_uN _ v_m)); BYTES := v_b_1 |} {| MEM_TYPE := (mk_limits v_n2 (mk_uN _ v_m)); BYTES := v_b_2 |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:202.1-202.54 *)
Inductive Global_extension: globalinst -> globalinst -> Prop :=
	| mk_Global_extension : forall (v_mut : mut) (v_t2 : valtype) (v_c1 : (val_ v_t2)) (v_c2 : (val_ v_t2)), ((v_mut = (Some MUT)) \/ (v_c1 = v_c2)) -> Global_extension {| GLOB_TYPE := (mk_globaltype v_mut v_t2); VALUE := (VAL_CONST v_t2 v_c1) |} {| GLOB_TYPE := (mk_globaltype v_mut v_t2); VALUE := (VAL_CONST v_t2 v_c2) |}.

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:203.1-203.43 *)
Inductive Store_extension: store -> store -> Prop :=
	| mk_Store_extension : forall (v_store_1 : store) (v_store_2 : store) (v_funcinst_1 : (list funcinst)) (v_tableinst_1 : (list tableinst)) (v_meminst_1 : (list meminst)) (v_globalinst_1 : (list globalinst)) (v_funcinst_1' : (list funcinst)) (v_funcinst_2 : (list funcinst)) (v_tableinst_1' : (list tableinst)) (v_tableinst_2 : (list tableinst)) (v_meminst_1' : (list meminst)) (v_meminst_2 : (list meminst)) (v_globalinst_1' : (list globalinst)) (v_globalinst_2 : (list globalinst)), ((FUNCS v_store_1) = v_funcinst_1) -> ((TABLES v_store_1) = v_tableinst_1) -> ((MEMS v_store_1) = v_meminst_1) -> ((GLOBALS v_store_1) = v_globalinst_1) -> ([(FUNCS v_store_2)] = [v_funcinst_1'; v_funcinst_2]) -> ([(TABLES v_store_2)] = [v_tableinst_1'; v_tableinst_2]) -> ([(MEMS v_store_2)] = [v_meminst_1'; v_meminst_2]) -> ([(GLOBALS v_store_2)] = [v_globalinst_1'; v_globalinst_2]) -> ((List.length v_funcinst_1) = (List.length v_funcinst_1')) -> List.Forall2 (fun (v_funcinst_1 : funcinst) (v_funcinst_1' : funcinst) => (Func_extension v_funcinst_1 v_funcinst_1')) (v_funcinst_1) (v_funcinst_1') -> ((List.length v_tableinst_1) = (List.length v_tableinst_1')) -> List.Forall2 (fun (v_tableinst_1 : tableinst) (v_tableinst_1' : tableinst) => (Table_extension v_tableinst_1 v_tableinst_1')) (v_tableinst_1) (v_tableinst_1') -> ((List.length v_meminst_1) = (List.length v_meminst_1')) -> List.Forall2 (fun (v_meminst_1 : meminst) (v_meminst_1' : meminst) => (Mem_extension v_meminst_1 v_meminst_1')) (v_meminst_1) (v_meminst_1') -> ((List.length v_globalinst_1) = (List.length v_globalinst_1')) -> List.Forall2 (fun (v_globalinst_1 : globalinst) (v_globalinst_1' : globalinst) => (Global_extension v_globalinst_1 v_globalinst_1')) (v_globalinst_1) (v_globalinst_1') -> Store_extension v_store_1 v_store_2.

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:235.1-235.32 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/B-soundness.spectec:235.1-235.32 *)
Fixpoint fun_types__of (var_0 : (list val)) : (list valtype) :=
	match var_0 with
		| [] => []
		| ((VAL_CONST v_valtype v_val_) :: v_val') => ([v_valtype] ++ (fun_types__of v_val'))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/B-soundness.spectec:239.1-240.32 *)
Definition fun_is__const (v_admininstr : admininstr) : bool :=
	match v_admininstr with
		| (AI_CONST v_valtype v_val_) => true
		| v_admininstr => false
	end.

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:244.1-245.41 *)
(* Auxiliary Definition at: ../specification/wasm-1.0/B-soundness.spectec:244.1-245.41 *)
Fixpoint fun_const__list (var_0 : (list admininstr)) : bool :=
	match var_0 with
		| [] => true
		| (v_admininstr :: v_admininstr') => ((fun_is__const v_admininstr) && (fun_const__list v_admininstr'))
	end.

(* Auxiliary Definition at: ../specification/wasm-1.0/B-soundness.spectec:250.1-251.38 *)
Definition fun_terminal__form (var_0 : (list admininstr)) : bool :=
	match var_0 with
		| v_admininstr => ((fun_const__list v_admininstr) || (v_admininstr == [AI_TRAP]))
	end.

