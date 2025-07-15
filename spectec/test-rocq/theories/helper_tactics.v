From Coq Require Import String List Unicode.Utf8.
From RecordUpdate Require Import RecordSet.
Require Import NArith.
Require Import Arith.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

(***

These are some tactics that are very useful when doing type soundness.

You should be able to notice that some of these tactics are directly taken from
WasmCert, as they work essentially the same. 

***)

Ltac decomp :=
repeat lazymatch goal with
	| H: _ /\ _ |- _ => 
		destruct H
end.

(** Similar to [set (name := term)], but introduce an equality instead of a local definition. **)
Ltac set_eq name term :=
  set (name := term);
  have: name = term; [
      reflexivity
    | clearbody name ].

Ltac is_variable x cont1 cont2 :=
	match tt with
	| _ =>
		(* Sorry for the hack.
		Only a variable be cleared.
		Local definitions are not considered variables by this tactic. *)
		(exfalso; clear - x; assert_fails clearbody x; fail 1) || cont2
	| _ => cont1
	end.

(** The first step is to name each parameter of the predicate. **)
Ltac gen_ind_pre H :=
  let rec aux v :=
    lazymatch v with
    | ?f ?x =>
      let only_do_if_ok_direct t cont :=
        lazymatch t with
        | Type => idtac

        | _ => cont tt
        end in
      let t := type of x in
      only_do_if_ok_direct t ltac:(fun _ =>
        let t :=
          match t with
          | _ _ => t
          | ?t => eval unfold t in t
          | _ => t
          end in
        only_do_if_ok_direct t ltac:(fun _ =>
          let x' :=
            let rec get_name x :=
              match x with
              | ?f _ => get_name f
              | _ => fresh x
              | _ => fresh "x"
              end in
            get_name x in
          move: H;
          set_eq x' x;
          let E := fresh "E" x' in
          move=> E H));
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** Then, each of the associated parameters can be generalised. **)
Ltac gen_ind_gen H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize dependent x) ltac:(idtac)
    | _ => fail "unable to generalize" t
    end in
  let rec aux v :=
    lazymatch v with
    | ?f ?x => 
    lazymatch goal with
      | _ : x = ?y |- _ => try_generalize y
      | _ => fail "unexpected term" v
      end;
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** After the induction, one can inverse them again (and do some cleaning). **)
Ltac gen_ind_post :=
  repeat lazymatch goal with
  | |- _ = _ -> _ => inversion 1
  | |- _ -> _ => intro
  end;
  repeat lazymatch goal with
  | H: True |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  end.

(** Wrapping every part of the generalised induction together. **)
Ltac gen_ind H :=
  gen_ind_pre H;
  gen_ind_gen H;
  induction H;
  gen_ind_post.

(** Similar to [gen_ind H; subst], but cleaning just a little bit more. **)
Ltac gen_ind_subst H :=
  gen_ind H;
  subst;
  gen_ind_post.


Ltac admin_instrs_ok_dependent_ind H :=
let Ht := type of H in
lazymatch Ht with
| Admin_instrs_ok ?s ?C ?es ?tf =>
	let s2 := fresh "s2" in
	let C2 := fresh "C2" in
	let es2 := fresh "es2" in
	let tf2 := fresh "tf2" in
	remember s as s2 eqn:Hrems;
	remember C as C2 eqn:HremC;
	remember es as es2 eqn:Hremes;
	remember tf as tf2 eqn:Hremtf;
	generalize dependent Hrems;
	generalize dependent HremC;
	generalize dependent Hremtf;
	generalize dependent s; generalize dependent C;
	generalize dependent tf;
	induction H
end.

Ltac removeinst2 H :=
    let H1 := fresh "HLength" in
    eapply length_app_both_nil in H as H1; eauto;
    rewrite H1 in H; rewrite <- app_right_nil in H.

Ltac removeinstSimpler H :=
	let H1 := fresh "HLength" in
	eapply length_app_nil in H as H1; eauto;
	rewrite H1 in H; rewrite <- app_right_nil in H.