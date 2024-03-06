Require Import Asm.
Require Import Maps.
Require Import Values.
Require Import Memory.
Require Import Integers.

(* Augment the above by instructions that are not generated as part of
CompCert, i.e. machine-state operations like CSR reads and writes. *)



Inductive csreg: Type :=
  | CSRmscratch: csreg.

Lemma csreg_eq: forall (x y: csreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Inductive mreg: Type :=
  | PR: preg -> mreg                    (**regular registers *)
  | CSR: csreg -> mreg.                 (**RISC-V CSRs *)

Coercion PR: preg >-> mreg.
Coercion CSR: csreg >-> mreg.

Lemma mreg_eq: forall (x y: mreg), {x=y} + {x<>y}.
Proof. decide equality. apply preg_eq. apply csreg_eq. Defined.

Module MregEq.
  Definition t  := mreg.
  Definition eq := mreg_eq.
End MregEq.

Module Mregmap := EMap(MregEq).

Definition mregset := Mregmap.t val.

Inductive minstruction : Type :=
| Mins     (ins: instruction)                    (**regular instruction *)
| Mcsrrw   (rd: ireg) (csr: csreg) (rs: ireg)
| Mcsrw    (csr: csreg) (rs: ireg)
| Mcsrr    (rd: ireg) (csr: csreg).

Variable mge: genv.            (* Why can't we use `ge`? *)

Notation "a ^# b <- c" := (Mregmap.set b c a) (at level 1, b at next level) : asm.

Definition exec_minstr (f: function) (i: minstruction) (rs: mregset) (m: mem) : outcome :=
  match i with
  | Mins ins => exec_instr mge f ins rs m
  | Mcsrrw d csr s =>
      Next (nextinstr (
        rs ^# (PR d) <- (rs csr)
           ^# csr <- (rs ## s)
      )) m
  | Mcsrr d csr =>
      Next (nextinstr (rs ^# (PR d) <- (rs csr))) m
  | Mcsrw csr s =>
      Next (nextinstr (rs ^# csr <- (rs ## s))) m
  end.

Search outcome.
Print val.

Search Int.zero.

Search Val.add.

Print val.

Search Mregmap.set.

(* Theorem nop_is_nop : forall (f: function) (rs: mregset) (m: mem), (exists i, (rs # X1) = Vint i) -> (exec_minstr f (Mins (Paddiw X1 X1 Int.zero)) rs m) = (Next (nextinstr rs) m). *)
(* Proof. *)
(*   intros. destruct H. *)
(*   simpl. unfold Val.add. rewrite H. rewrite Int.add_zero. unfold Pregmap.set. unfold nextinstr. unfold Pregmap.set. *)
(*   -  *)
(*   exists (rs ## X1). intros _. unfold exec_minstr. unfold exec_instr. auto. *)
(*   unfold Val.add. unfold "##".  *)
(* Qed. *)
