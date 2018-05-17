From mathcomp Require Import all_ssreflect.
From fcsl Require Import axioms pred prelude domain.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma nat_leq_refl : forall x : nat, x <= x.
Proof.
exact: leqnn.
Qed.

Lemma nat_leq_antisymmetric : forall x y, x <= y -> y <= x -> x = y.
Proof.
  move => x' y'.  
  rewrite leq_eqVlt.
  move/orP.
  case.
  - by move/eqP.
  - move => Hlt.
    rewrite leq_eqVlt.
    move/orP.
    case.
    * by move/eqP.
    * move => Ht'.
      rewrite ltnNge in Ht'.
      rewrite ltnNge in Hlt.
      have Ht := leq_total x' y'.
      move/orP: Ht.
      case.
      + move => Hlt'.
        by move/negP in Ht'.
      + move => Hlt'.
        by move/negP in Hlt.
Qed.

Lemma nat_leq_trans : forall x y z, x <= y -> y <= z -> x <= z.
Proof.
move => x y z.
apply: leq_trans.
Qed.

Definition nat_leq_PosetMixin := 
  PosetMixin nat_leq_refl nat_leq_antisymmetric nat_leq_trans.
Canonical nat_leq_Poset := Eval hnf in Poset nat nat_leq_PosetMixin.

Inductive nat_top :=
| nat_top_nat (n : nat)
| nat_top_top.

Inductive nat_top_leq : nat_top -> nat_top -> Prop :=
| nat_top_leq_nat_nat : forall m n, m <= n -> nat_top_leq (nat_top_nat m) (nat_top_nat n)
| nat_top_leq_nat_top : forall n, nat_top_leq (nat_top_nat n) nat_top_top
| nat_top_leq_top_top : nat_top_leq nat_top_top nat_top_top.

Notation "x <=T y" := (nat_top_leq x y) (at level 40).

Lemma nat_top_leq_refl : forall x, x <=T x.
Proof.
case.
- move => n.
  apply nat_top_leq_nat_nat.
  exact: leqnn.
- apply nat_top_leq_top_top.
Qed.

Lemma nat_top_leq_antisymmetric : forall x y, x <=T y -> y <=T x -> x = y.
Proof.
case.
- move => m.
  case.
  * move => n Hle Hle'.
    inversion Hle; subst.
    inversion Hle'; subst.
    by rewrite (nat_leq_antisymmetric H1 H2).
  * move => Hle Hle'.
    by inversion Hle'.
- case => //=.
  move => n Hle.
  by inversion Hle.
Qed.

Lemma nat_top_leq_trans : forall x y z, x <=T y -> y <=T z -> x <=T z.
Proof.
case.
- move => x.
  case.
  * move => y.
    case.
    + move => z.
      move => Hle Hle'.
      inversion Hle; subst.
      inversion Hle'; subst.
      apply nat_top_leq_nat_nat.
      by eapply nat_leq_trans; eauto.
    + move => Hle Hle'.
      exact: nat_top_leq_nat_top.
  * case.
    + move => n.
      move => Hle Hle'.
      by inversion Hle'.
    + move => Hle Hle'.
      exact: nat_top_leq_nat_top.
- case.
  * move => m.
    case.
    + move => n.
      move => Hle Hle'.
      by inversion Hle.
    + move => Hle.
      by inversion Hle.
  * case.
    + move => n Hle Hle'.
      by inversion Hle'.
    + move => Hle Hle'.
      exact: nat_top_leq_top_top.
Qed.

Definition nat_top_leq_PosetMixin := 
  PosetMixin nat_top_leq_refl nat_top_leq_antisymmetric nat_top_leq_trans.
Canonical nat_top_leq_Poset := Eval hnf in Poset nat_top nat_top_leq_PosetMixin.

Section LatticeFacts.

Variable L : lattice.

Variable S T : Pred L.

Local Notation "⋁ S" := (sup S) (at level 40).
Local Notation "⋀ S" := (inf S) (at level 40).
Local Notation "s ⋞ t" := (Poset.leq s t) (at level 70).
Local Notation "s ∈ S" := (s \In S) (at level 70).

(* Mini-exercises from p. 44 in Ordered Sets and Complete Lattices *)
(* http://profs.sci.univr.it/~giaco/paperi/lattices-for-CS.pdf *)

Lemma mini_i_1 : forall s, s ∈ S -> s ⋞ ⋁ S.
Proof.
exact: supP.
Qed.

Lemma mini_i_2 : forall s, s ∈ S -> ⋀ S ⋞ s.
Proof.
exact: infP.
Qed.

Lemma mini_iv_1 :
  ⋁ S ⋞ ⋀ T ->
  (forall s t, s ∈ S -> t ∈ T -> s ⋞ t).
Proof.
move => HST s t Hs Ht.
have HsupP := supP Hs.
have HinfP := infP Ht.
have Hle: s ⋞ inf T.
  move: HsupP HST.
  exact: poset_trans.
move: Hle HinfP.
exact: poset_trans.
Qed.

Lemma mini_iv_2 :
  (forall s t, s ∈ S -> t ∈ T -> s ⋞ t) ->
  ⋁ S ⋞ ⋀ T.
Proof.
move => Hst.
have HsupM := @supM _ S (inf T).
apply HsupM.
move => y Hy.
have HinfM := @infM _ T y.
apply HinfM.
move => x Hx.
exact: Hst.
Qed.

Hypothesis S_subset_T : forall s, s ∈ S -> s ∈ T.

Lemma mini_v_1 : ⋁ S ⋞ ⋁ T.
Proof.
apply supM.
move => y H.
apply supP.
exact: S_subset_T.
Qed.

Lemma mini_v_2 : ⋀ T ⋞ ⋀ S.
Proof.
apply infM.
move => y H.
apply infP.
exact: S_subset_T.
Qed.

End LatticeFacts.
