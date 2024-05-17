import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Control.Bifunctor
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Logic.Equiv.Functor
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

import «Catalean».FullBinaryTrees

open Nat
open Finset
open BigOperators
open Finset.antidiagonal (fst_le snd_le)

open FullBinaryTree

def catalan_number : Nat → Nat
| 0 => 1
| succ n => ∑ i : Fin (succ n), (catalan_number i) * (catalan_number (n - i))

lemma sigmaOptionEquivSum {α : Type u} {β : Option α → Type v} :
  (a : Option α) × β a ≃ β none ⊕ (a : α) × β (some a) where
  toFun := λ
  | ⟨none, b⟩ => Sum.inl b
  | ⟨some a, b⟩ => Sum.inr ⟨a, b⟩
  invFun := λ
  | Sum.inl b => ⟨none, b⟩
  | Sum.inr ⟨a, b⟩ => ⟨a, b⟩
  left_inv := λ
  | ⟨none, _⟩ => by rfl
  | ⟨some _, _⟩ => by rfl
  right_inv := λ
  | Sum.inl _ => by rfl
  | Sum.inr _ => by rfl

lemma dist_fin_sigma {k : Nat} {n : Fin k → Nat} :
  (i : Fin k) × Fin (n i) ≃ Fin (∑ i : Fin k, n i) := by
  induction k with
  | zero => dsimp; apply Equiv.equivOfIsEmpty
  | succ k H =>
    apply Equiv.trans
    apply Equiv.sigmaCongr (β₂ := ?mot) ?base ?fiber
    case mot =>
      exact λ o => Fin (n (match o with | none => k | some i => Fin.castSucc i))
    case base => exact finSuccEquivLast
    case fiber =>
      apply Fin.lastCases
      . simp; apply Equiv.refl
      . intro i; simp; apply Equiv.refl
    apply Equiv.trans
    refine sigmaOptionEquivSum
    simp
    apply Equiv.trans
    apply Equiv.sumComm
    apply Equiv.trans
    exact
      (Bifunctor.mapEquiv Sum
        ( @H (n ·.castSucc))
        ( Equiv.refl (Fin (n (Fin.last k)))))
    apply Equiv.trans
    apply finSumFinEquiv
    apply finCongr
    symm
    apply Fin.sum_univ_castSucc

def full_binary_tree_of_node_count (n : Nat) : Type :=
  { T : FullBinaryTree // T.nodes = n}

def catalan_structure (n : Nat) : Type :=
  (i : Fin (n + 1)) × Fin (catalan_number i) × Fin (catalan_number (n - i))

def equiv_root_binary_tree :
  full_binary_tree_of_node_count 0 ≃ Fin (catalan_number 0) := Equiv.mk
    ( λ _ => Fin.ofNat 0)
    ( λ _ => ⟨ FullBinaryTree.leaf , by rfl ⟩)
    ( λ ⟨ T , n ⟩ => by
      simp
      induction T with
      | leaf => rfl
      | node T1 T2 _ _ =>
        unfold nodes at n
        exfalso
        linarith
      done)
    ( λ u => by
      simp
      induction u with
      | mk val is_lt =>
        unfold catalan_number at is_lt
        apply Fin.eq_of_val_eq
        simp at *
        rw [is_lt]
      done)

def tree_node_initiality (n : Nat) :
  full_binary_tree_of_node_count (n + 1) ≃
  { X : FullBinaryTree × FullBinaryTree // X.1.nodes + X.2.nodes = n } := Equiv.mk
  ( λ ⟨ T , p ⟩ => match T with
    | leaf => by contradiction
    | node T₁ T₂ => by
      use ⟨ T₁, T₂ ⟩
      unfold nodes at p
      dsimp
      rw [add_assoc, add_comm] at p
      apply Nat.succ_inj.mp
      assumption)
  ( λ ⟨ ⟨ T₁, T₂ ⟩, p ⟩ => by
    use (node T₁ T₂)
    dsimp at p
    unfold nodes
    rw [add_assoc, p, add_comm])
  ( λ ⟨ T, p ⟩ => by
    match T with
    | leaf => contradiction
    | node T₁ T₂ => rfl)
  ( λ ⟨ ⟨ T₁, T₂ ⟩, p ⟩ => by rfl)

def peasants_contractibility_of_singletons (n : Nat) :
  { X : FullBinaryTree × FullBinaryTree // X.1.nodes + X.2.nodes = n } ≃
  { X : (Fin (n + 1) × FullBinaryTree × FullBinaryTree) //
    X.2.1.nodes = ↑X.1 ∧ X.2.2.nodes = n - ↑X.1 } := Equiv.mk
  ( λ ⟨ ⟨ T₁, T₂⟩, p ⟩ => by
    use ⟨T₁.nodes, T₁, T₂⟩
    dsimp at *
    have e : T₁.nodes % (n + 1) = T₁.nodes := by
      apply Nat.mod_eq_of_lt
      apply Nat.lt_of_succ_le
      apply Nat.succ_le_succ
      rw [← p]
      apply Nat.le_add_right
    constructor
    . symm; exact e
    . rw [e]
      symm; apply Nat.sub_eq_of_eq_add; symm
      rw [add_comm, p])
  ( λ ⟨ ⟨ ⟨i, h⟩, T₁, T₂⟩, p, q⟩ => by
    use ⟨T₁, T₂⟩
    dsimp at *
    rw [p, q]
    rw [Nat.add_comm, Nat.sub_add_cancel]
    apply Nat.lt_add_one_iff.1
    apply h)
  ( λ ⟨ ⟨ T₁, T₂⟩, p ⟩ => by dsimp)
  (λ ⟨ ⟨ ⟨i, h⟩, T₁, T₂⟩, p, q⟩ => by
    repeat simp at *
    rw [p]
    apply Fin.eq_of_val_eq
    apply Nat.mod_eq_of_lt h)

def sigma_arith (n : Nat) :
  { X : (Fin (n + 1) × FullBinaryTree × FullBinaryTree) //
    X.2.1.nodes = ↑X.1 ∧ X.2.2.nodes = n - ↑X.1 } ≃
  ( (i : Fin (n + 1)) ×
    full_binary_tree_of_node_count i ×
    full_binary_tree_of_node_count (n - i)) := Equiv.mk
  ( λ ⟨ ⟨ i, T₁, T₂ ⟩, p, q ⟩ => ⟨ i , ⟨ T₁, p⟩, ⟨T₂, q⟩⟩)
  ( λ ⟨ i, ⟨ T₁, p⟩, ⟨ T₂, q⟩⟩ => ⟨ ⟨ i, T₁, T₂⟩, p, q⟩)
  ( λ ⟨ _, _, _ ⟩ => by rfl)
  ( λ ⟨ _, _, _ ⟩ => by rfl)

noncomputable def equiv_catalan_structure (n : Nat) :
  catalan_structure n ≃ Fin (catalan_number (n + 1)) := by
  unfold catalan_number
  unfold catalan_structure
  apply Equiv.trans
  . apply Equiv.sigmaCongrRight;
    . intro i; exact finProdFinEquiv
  . exact dist_fin_sigma

noncomputable def compute_support_full_binary_tree : (n : Nat) ->
  full_binary_tree_of_node_count n ≃ Fin (catalan_number n)
| 0 => equiv_root_binary_tree
| succ n' => by
  apply Equiv.trans
  apply tree_node_initiality
  apply Equiv.trans
  apply peasants_contractibility_of_singletons
  apply Equiv.trans
  apply sigma_arith
  apply Equiv.trans
  apply Equiv.sigmaCongrRight
  . intro i
    apply Equiv.prodCongr
    . apply compute_support_full_binary_tree
    . apply compute_support_full_binary_tree
  apply equiv_catalan_structure
