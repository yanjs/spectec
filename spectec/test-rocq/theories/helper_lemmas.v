From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

(*** 

The following lemmas are simply simple facts that are needed for lists and predicates such as
Forall and Forall2. 

***)


Lemma leadd: forall (i n : nat),
	(i <= (i + n))%coq_nat.
Proof.
	move => i.
	induction i; move => n.
	- apply Nat.le_0_l.
	- simpl. rewrite addSn.	 apply le_n_S. apply IHi.
Qed.

Lemma list_update_func_split : forall {A : Type} (x x' : list A) (idx : nat) (f : A -> A),
	x' = list_update_func x idx f ->
	(exists y, In (f y) x') \/ x = x'.
Proof. 
	move => A x x' idx f H.
	generalize dependent idx.
	generalize dependent x'.
	induction x.
	- right. rewrite H => //.
	- move => x' idx H. destruct idx. 
		- left. exists a. rewrite H. apply in_eq.
		- destruct x'.
			- discriminate.
			- injection H as H2. apply IHx in H.
				destruct H.
				- destruct H. left. exists x0. apply List.in_cons => //.
				- right. by f_equal.
Qed.

Lemma list_update_func_split_strong : forall {A : Type} (x x' : list A) (idx : nat) (f : A -> A),
	x' = list_update_func x idx f -> 
	(idx < length x)%coq_nat ->
	(exists y, In (f y) x').
Proof. 
	move => A x x' idx f H H2.
	generalize dependent idx.
	generalize dependent x'.
	induction x; move => x' idx H H2. 
	- apply Nat.nlt_0_r in H2. exfalso. apply H2.
	- destruct idx. 
		- simpl in H. destruct x' => //=.
			injection H as ?; subst. exists a. by left.
		- destruct x' => //=.
			simpl in H. injection H as ?.
			apply IHx in H0; destruct H0.
			- exists x0. by right. 
			- by apply Nat.succ_lt_mono.
Qed.

Lemma length_app_lt: forall {A : Type} (l l' l1' l2': list A),
	length l = length l1' ->
	l' = l1' ++ l2' -> 
	(length l <= length l')%coq_nat.
Proof.
	move => A l l' l1' l2' HLength HApp.

	apply f_equal with (f := fun t => length t) in HApp.
	rewrite List.length_app in HApp.
	rewrite <- HLength in HApp.
	symmetry in HApp.
	generalize dependent l2'.
	generalize dependent l'.
	clear HLength.
	induction l; move => l' l2' HApp.
	- simpl. apply Nat.le_0_l.
	- destruct l' => //. simpl in HApp. 
		injection HApp as H.
		apply IHl in H.
		simpl. apply le_n_S. apply H.
Qed.  

Lemma length_same_split_zero: forall {A : Type} (l l2' : list A),
	length l = length l + length l2' ->
	length l2' = 0.
Proof.
	move => A l l2' H.
	generalize dependent l2'.
	induction l; move => l2' H.
	- simpl in H. symmetry in H. apply H.
	- simpl in H. injection H as ?. apply IHl. apply H.
Qed.
	

Lemma length_app_both_nil: forall {A : Type} (l l' l1' l2': list A),
	length l = length l' ->
	length l = length l1' -> 
	l' = l1' ++ l2' -> 
	l2' = [].
Proof.
	move => A l l' l1' l2' HLength HLength2 HApp.

	apply f_equal with (f := fun t => List.length t) in HApp.
	rewrite List.length_app in HApp.
	rewrite <- HLength in HApp.
	rewrite <- HLength2 in HApp.
	apply length_same_split_zero in HApp.
	rewrite <- List.length_zero_iff_nil => //=.
Qed.  

Lemma length_app_nil: forall {A : Type} (l' l1' l2': list A),
	length l' = length l1' -> 
	l' = l1' ++ l2' -> 
	l2' = [].
Proof.
	move => A l' l1' l2' HLength HApp.
	apply f_equal with (f := fun t => List.length t) in HApp.
	rewrite List.length_app in HApp.
	rewrite <- HLength in HApp.
	apply length_same_split_zero in HApp.
	rewrite <- List.length_zero_iff_nil => //=.
Qed.  

Lemma Forall2_nth {A : Type} {B : Type} {_ : Inhabited A} {_ : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i, (i < length l) -> R (List.nth i l default_val) (List.nth i l' default_val)).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i H'.
	move/ltP in H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.

Lemma Forall2_nth2 {A : Type} {B : Type} {_ : Inhabited A} {_ : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i, (i < length l') -> R (List.nth i l default_val) (List.nth i l' default_val)).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i H'.
	move/ltP in H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.

Lemma Forall2_lookup {A : Type} {X : Inhabited A} {B : Type} {Y : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i, (i < length l)%coq_nat -> R (lookup_total l i) (lookup_total l' i)).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.

Lemma Forall2_lookup2 {A : Type} {X : Inhabited A} {B : Type} {Y : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i, (i < length l')%coq_nat -> R (lookup_total l i) (lookup_total l' i)).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.


Fixpoint In2 {A B : Type} (x : A) (y : B) (l : list A) (l' : list B) : Prop :=
    match l, l' with
      | [], [] => False
	  | [], b :: ms => False
	  | a :: ns, [] => False
      | a :: ns, b :: ms => (a = x /\ b = y) \/ In2 x y ns ms
    end.

Lemma lookup_list_update_func: forall {A : Type} {B : Inhabited A} (x : A) (f : A -> A) (l : list A) (idx : nat),
	(idx < length l)%coq_nat ->
	x = lookup_total (list_update_func l idx f) idx -> 
	exists y, x = f y.
Proof.
	move => A B x f l idx.
	move: x idx f.
	induction l; move => x idx f HLength HLookup.
	- apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
	- destruct idx.
		- simpl in *. unfold lookup_total in HLookup. simpl in HLookup. by exists a.
		- simpl in HLength. apply Nat.succ_lt_mono in HLength. eapply IHl; eauto.
Qed.

Lemma In2_split: forall {A B : Type} (x : A) (y : B) (l : list A) (l' : list B),
	In2 x y l l' -> In x l /\ In y l'.
Proof.
	move => A B x y l l' HIn.
	generalize dependent x.
	generalize dependent y.
	generalize dependent l'.
	induction l; move => l0' y0 x0 HIn => //=.
	- destruct l0' => //=.
	- destruct l0' => //=.
		simpl in HIn.
		destruct HIn. 
		- destruct H. split; by left.
		- apply IHl in H. destruct H. split; by right.
Qed.	

Lemma Forall2_forall2 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	Forall2 R l l' <-> length l = length l' /\ (forall x y, In2 x y l l' -> R x y).
Proof.
	split.
	- (* -> *)
		move => H.
		split. eapply Forall2_length; eauto.	
		move => x y HIn.
		generalize dependent x.
		generalize dependent y.
		induction H => //=; move => y0 x0 HIn; subst; simpl in *.
		destruct HIn. 
		- destruct H1. subst => //=.
		- by eapply IHForall2.
	- (* <- *)
		move => H.
		destruct H.
		generalize dependent l'.
		induction l => //=; move => l' H H1.
		- destruct l' => //=.
		- destruct l' => //=.
			apply Forall2_cons_iff. split.
			- apply H1. left; split => //=.
			- apply IHl. simpl in H. injection H as ?. apply H.
			- move => x y HIn. apply H1. right. apply HIn.
Qed.

Lemma Forall2_forall2weak {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	Forall2 R l l' -> (forall x , In x l -> exists y, R x y).
Proof.
	
	move => H x.
	generalize dependent x.
	induction H => //=; move => x0 HIn; subst; simpl in *.
	destruct HIn. 
	- subst. exists y. subst => //=.
	- by apply IHForall2.
Qed.

Lemma Forall2_forall2weak2 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	Forall2 R l l' -> (forall y, In y l' -> exists x, R x y).
Proof.
	move => H y.
	generalize dependent y.
	induction H => //=; move => y0 HIn; subst; simpl in *.
	destruct HIn. 
	- subst. exists x. subst => //=.
	- by apply IHForall2.
Qed.

Lemma Forall2_forall2weak3 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	(forall x y, In x l -> R x y) /\ length l = length l' -> Forall2 R l l'.
Proof.
	move => H.
	destruct H.
	generalize dependent l'.
	induction l; move => l0' HLength; subst; simpl in * => //=.
	- destruct l0' => //=.
	- destruct l0' => //=.
		apply Forall2_cons_iff. split.
		- apply H. left => //=.
		- apply IHl. move => x y HIn. apply H. by right.
		- simpl in HLength. injection HLength as ?. apply H0.
Qed.

Lemma Forall2_forall2weak4 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	(forall x y, In y l' -> R x y) /\ length l = length l' -> Forall2 R l l'.
Proof.
	move => H.
	destruct H.
	generalize dependent l.
	induction l'; move => l0 HLength; subst; simpl in * => //=.
	- destruct l0 => //=.
	- destruct l0 => //=.
		apply Forall2_cons_iff. split.
		- apply H. left => //=.
		- apply IHl'. move => x y HIn. apply H. by right.
		- simpl in HLength. injection HLength as ?. apply H0.
Qed.

Lemma Forall2_list_update_func {A B : Type} {C : Inhabited A} {D : Inhabited B}
	(l : list A) (l' : list B) (R : A -> B -> Prop) (i : nat) (f : A -> A) (x : A) (y : B):
	Forall2 R l l' ->
	lookup_total l i = x -> 
	lookup_total l' i = y -> 
	R (f x) y -> Forall2 R (list_update_func l i f) l'.
Proof.
	generalize dependent l'.
	generalize dependent i.
	generalize dependent x.
	generalize dependent y.
	generalize dependent f.
	induction l; move => f0 y0 x0 i0 l0' HForall HLx HLy HR.
	- inversion HForall. destruct i0 => //=.
	- destruct l0' => //=; inversion HForall => //=; subst.
		destruct i0 => //=.
		- apply Forall2_cons_iff; split.
			- by unfold lookup_total in HR.
			- apply H4.
		- apply Forall2_cons_iff; split.
			- apply H2.
			- eapply IHl; eauto.
Qed.

Lemma Forall2_list_update_func2 {A B : Type} {C : Inhabited A} {D : Inhabited B}
	(l : list A) (l' : list B) (R : A -> B -> Prop) (i : nat) (f : B -> B) (x : A) (y : B):
	Forall2 R l l' ->
	lookup_total l i = x -> 
	lookup_total l' i = y -> 
	R x (f y) -> Forall2 R l (list_update_func l' i f).
Proof.
	generalize dependent l'.
	generalize dependent i.
	generalize dependent x.
	generalize dependent y.
	generalize dependent f.
	induction l; move => f0 y0 x0 i0 l0' HForall HLx HLy HR.
	- inversion HForall. destruct i0 => //=.
	- destruct l0' => //=; inversion HForall => //=; subst.
		destruct i0 => //=.
		- apply Forall2_cons_iff; split.
			- by unfold lookup_total in HR.
			- apply H4.
		- apply Forall2_cons_iff; split.
			- apply H2.
			- eapply IHl; eauto.
Qed.

Lemma Forall2_list_update {A B : Type} {C : Inhabited A} {D : Inhabited B}
	(l : list A) (l' : list B) (R : A -> B -> Prop) (i : nat) (x : A) (y : B):
	Forall2 R l l' ->
	lookup_total l' i = y -> 
	R x y -> Forall2 R (list_update l i x) l'.
Proof.
	generalize dependent l'.
	generalize dependent i.
	generalize dependent x.
	generalize dependent y.
	induction l; move => y0 x0 i0 l0' HForall HLx HR.
	- inversion HForall. destruct i0 => //=.
	- destruct l0' => //=; inversion HForall => //=; subst.
		destruct i0 => //=.
		- apply Forall2_cons_iff; split.
			- by unfold lookup_total in HR.
			- apply H4.
		- apply Forall2_cons_iff; split.
			- apply H2.
			- eapply IHl; eauto.
Qed.

Lemma Forall2_list_update2 {A B : Type} {C : Inhabited A} {D : Inhabited B}
	(l : list A) (l' : list B) (R : A -> B -> Prop) (i : nat) (x : A) (y : B):
	Forall2 R l l' ->
	lookup_total l i = x -> 
	R x y -> Forall2 R l (list_update l' i y).
Proof.
	generalize dependent l'.
	generalize dependent i.
	generalize dependent x.
	generalize dependent y.
	induction l; move => y0 x0 i0 l0' HForall HLx HR.
	- inversion HForall. destruct i0 => //=.
	- destruct l0' => //=; inversion HForall => //=; subst.
		destruct i0 => //=.
		- apply Forall2_cons_iff; split.
			- by unfold lookup_total in HR.
			- apply H4.
		- apply Forall2_cons_iff; split.
			- apply H2.
			- eapply IHl; eauto.
Qed.

Lemma Forall2_list_update_both {A B : Type} {C : Inhabited A} {D : Inhabited B}
	(l : list A) (l' : list B) (R : A -> B -> Prop) (i : nat) (x : A) (y : B):
	Forall2 R l l' ->
	R x y -> Forall2 R (list_update l i x) (list_update l' i y).
Proof.
	generalize dependent l'.
	generalize dependent i.
	generalize dependent x.
	generalize dependent y.
	induction l; move => y0 x0 i0 l0' HForall HR.
	- inversion HForall. destruct i0 => //=.
	- destruct l0' => //=; inversion HForall => //=; subst.
		destruct i0 => //=.
		- apply Forall2_cons_iff; split.
			- by unfold lookup_total in HR.
			- apply H4.
		- apply Forall2_cons_iff; split.
			- apply H2.
			- eapply IHl; eauto.
Qed.

Lemma list_update_length: forall {A : Type} (l : list A) (i : nat) (x : A),
	length (list_update l i x) = length l.
Proof.
	move => A l i x.
	generalize dependent l.
	generalize dependent x.
	induction i; move => x l.
	- destruct l => //=.
	- destruct l => //=.
		f_equal. apply IHi.
Qed.


Lemma list_update_length_func: forall {A : Type} (l : list A) (f : A -> A) (i : nat),
	length (list_update_func l i f) = length l.
Proof.
	move => A l f i.
	generalize dependent l.
	generalize dependent f.
	induction i; move => f l.
	- destruct l => //=.
	- destruct l => //=.
		f_equal. apply IHi.
Qed.

Lemma split_append_last : forall {A : Type} (z : list A) (y : list A) (i : A) (j : A),
	@app _ z [i] = @app _ y [j] ->
	z = y /\ i = j.
Proof.
	move => A z y i j H.
	apply app_inj_tail.
	apply H.
Qed.

Lemma split_cons : forall {A : Type} (j : A) (k : A),
	[j; k] = @app _ [j] [k].
Proof.
	move => A j k.
	done.
Qed.

Lemma split_append_1 : forall {A : Type} (z : list A) (i : A) (j : A),
	@app _ z [i] = [j] ->
	z = [] /\ i = j.
Proof.
	move => A z i j H.
	apply app_eq_unit in H.
	destruct H as [[H1 H2] | [H1 H2]].
		- split. apply H1. injection H2 as H3. apply H3.
		- discriminate.
Qed.

Lemma split_append_2 : forall {A : Type} (z : list A) (i : A) (j : A) (k : A),
	@app _ z [i] = [j; k] ->
	z = [j] /\ i = k.
Proof.
	move => A z i j k H.
	apply split_append_last.
	apply H.
Qed.

Lemma split_append_left_1 : forall {A : Type} (z : list A) (i : A) (j : A),
	@app _ [i] z = [j] ->
	z = [] /\ i = j.
Proof.
	move => A z i j H.
	apply app_eq_unit in H.
	destruct H as [[H1 H2] | [H1 H2]].
		- discriminate. 
		- split. apply H2. injection H1 as H3. apply H3.
Qed.


Lemma empty_append {A : Type}: forall (i : list A) (j : list A),
	[] = @app _ i j ->
	i = [] /\ j = [].
Proof.
	move => i j H.
	simpl.
	induction i.
		- rewrite -> app_nil_l in H. split. reflexivity. symmetry in H. apply H.
		- discriminate.
Qed. 

Lemma lookup_app: forall {A : Type} {B : Inhabited A} (l l' : list A) (n : nat),
	(n < List.length l) ->
	lookup_total l n = lookup_total (l ++ l') n.
Proof.
	move => A B l l' n.
	move: l l'.
	induction n; move => l l' H.
	- destruct l => //=.
	- destruct l => //=. 
	  unfold lookup_total. simpl.
	  apply IHn. apply H.
Qed.


(* These lemmas are simply just issues with it recognizing the ssreflect lemmas. I'll probably remove them later *)
Lemma app_left_single_nil: forall {A : Type} (x : A), [x] = @app _ [] [x].
Proof. done. Qed.

Lemma app_right_nil: forall {A : Type} (x : list A), x = @app _ x [].
Proof. move => A x. rewrite app_nil_r. done. Qed.

Lemma app_left_nil: forall {A : Type} (x : list A), x = @app _ [] x.
Proof. move => A x. rewrite app_nil_l. done. Qed.

Lemma _append_option_none: forall {A : Type} (c : option A) ,
	_append c None = c.
Proof.
	move => A c.
	unfold _append. unfold Append_Option. unfold option_append.
	induction c => //.
Qed.

Lemma _append_option_none_left: forall {A : Type} (c : option A) ,
	_append None c = c.
Proof.
	move => A c.
	unfold _append. unfold Append_Option. unfold option_append.
	destruct c => //.
Qed.

Lemma _append_some_left: forall {A : Type} (b : A) (c : option A) ,
	_append (Some b) c = (Some b).
Proof. reflexivity. Qed.

Lemma add_false: forall (n m : nat),
	~ (n + (S m) = n).
Proof.
	move => n m H.
	induction n. simpl in H.
	- rewrite add0n in H. discriminate.
	- apply IHn.
		rewrite addSn in H.
		by injection H.
Qed.

Lemma concat_cancel_last_n: forall (l1 l2 l3 l4: list valtype),
    l1 ++ l2 = l3 ++ l4 ->
    length l2 = length l4 ->
    (l1 = l3) /\  (l2 = l4).
Proof.
	move => l1.
	induction l1; move => l2 l3 l4 HApp HLength.
	- destruct l3; destruct l2; destruct l4 => //=.
		simpl in HApp. injection HApp as ?.
		simpl in HLength. injection HLength as ?.
		apply f_equal with (f := fun t => List.length t) in H0 as ?.
		rewrite length_app in H2. simpl in H2.
		rewrite H2 in H1.
		rewrite <- addnC in H1.
		rewrite addSn in H1.
		rewrite <- addnS in H1.
		apply add_false in H1. exfalso. apply H1.
	- destruct l3; destruct l2; destruct l4 => //=.
		simpl in HApp. 
		apply f_equal with (f := fun t => List.length t) in HApp as ?.
		simpl in H.
		injection H as H.
		rewrite length_app in H. simpl in H.
		simpl in HLength. injection HLength as ?.
		rewrite H0 in H.
		rewrite <- addnC in H.
		rewrite addSn in H.
		rewrite <- addnS in H.
		apply add_false in H. exfalso. apply H.
	-
		split => //=.
		simpl in HApp.
		repeat rewrite <- app_right_nil in HApp => //=.
	-
		repeat rewrite <- app_comm_cons in HApp.
		injection HApp as ?; subst. 
		assert (l1 = l3 /\ v0 :: l2 = v1 :: l4 -> v :: l1 = v :: l3 /\ v0 :: l2 = v1 :: l4).
		{
			move => H2.
			destruct H2.
			split.
			- f_equal. apply H.
			- apply H1.	
		}
		apply H.
		eapply IHl1; eauto.
Qed.

Lemma list_update_same_unchanged: forall {X : Type} {Y : Inhabited X} (l: list X) e i,
    (lookup_total l i) = e ->
	(i < length l)%coq_nat ->
    list_update l i e = l.
Proof.
	move => X Y l e i.
	generalize dependent l. generalize dependent e.
	induction i; move => e l HLookup HLT.
	- destruct l => //=. by f_equal.
	- destruct l => //=.
		f_equal. apply IHi. unfold lookup_total. unfold lookup_total in HLookup. simpl in HLookup. apply HLookup.
		by apply Nat.succ_lt_mono.
Qed.

Lemma list_update_map: forall {X Y:Type} (l:list X) i val {f: X -> Y},
    (i < length l)%coq_nat ->
    List.map f (list_update l i val) = list_update (List.map f l) i (f val).
Proof.
	move => X Y l i val.
	generalize dependent l. generalize dependent val.
	induction i; move => val l f HSize => //=.
  	- by destruct l => //=.
  	- destruct l => //=.
    	f_equal.
    	apply IHi.
		simpl in HSize. by apply Nat.succ_lt_mono.
Qed.


Lemma app_cat : forall {A : Type} (xs ys: seq A),
  (xs ++ ys)%list = xs ++ ys.
Proof. auto. Qed.

Definition prepend_label (v_C: context) (v_t: resulttype) :=
({| C_TYPES := []; C_FUNCS := []; C_GLOBALS := []; C_TABLES := []; C_MEMS := []; C_ELEMS := []; C_DATAS := []; C_LOCALS := []; C_LABELS := [v_t]; C_RETURN := None |} @@ v_C).

Lemma lookup_label_0: forall v_C (t: resulttype),
lookup_total (C_LABELS (prepend_label v_C t)) 0 = t.
Proof.
	move=> v_C t.
	unfold lookup_total.
	unfold C_LABELS, prepend_label, _append, Append_context, _append_context.
	unfold _append, Append_List_.
	unfold C_LABELS.
	rewrite app_cat.
	rewrite cat1s.
	unfold ListDef.nth.
	eauto.
Qed.

Lemma lookup_label_1: forall v_C (t: resulttype) n,
lookup_total (C_LABELS (prepend_label v_C t)) (n + 1) =
lookup_total (C_LABELS v_C) (n).
Proof.
	move=> v_C t n.
	unfold lookup_total.
	unfold C_LABELS, prepend_label, _append, Append_context, _append_context.
	unfold _append, Append_List_.
	unfold C_LABELS.
	rewrite app_cat.
	rewrite cat1s.
	rewrite addn1.
	reflexivity.
Qed.
