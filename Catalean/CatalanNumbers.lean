import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring

import «Catalean».FullBinaryTrees

open Nat
open Finset
open BigOperators
open Finset.antidiagonal (fst_le snd_le)

open FullBinaryTree

def catalan_number : Nat → Nat
| 0 => 1
| succ n => ∑ i : Fin (succ n), (catalan_number i) * (catalan_number (n - i))

lemma dist_fin_sigma {k : Nat} {n : Fin k → Nat} :
  (i : Fin k) × Fin (n i) ≃ Fin (∑ i : Fin k, n i) := by
  sorry

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
        rw [Nat.add_assoc, ← Nat.succ_eq_one_add] at n
        apply (Nat.not_eq_zero_of_lt (Nat.lt_succ_self _)) at n
        assumption
      done)
    ( λ u => by
      simp
      induction u with
      | mk val is_lt =>
        apply Fin.eq_of_val_eq
        unfold catalan_number at is_lt
        simp at is_lt
        simp
        rw [is_lt]
      done)

def equiv_full_binary_tree_catalan_structure : (n : Nat) ->
  full_binary_tree_of_node_count (n + 1) ≃ catalan_structure n := by sorry

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
| succ n => Equiv.trans
  (equiv_full_binary_tree_catalan_structure n)
  (equiv_catalan_structure n)
