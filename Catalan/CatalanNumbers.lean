import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Defs

import «Catalan».FullBinaryTrees

open Nat
open Finset
open BigOperators
open Finset.antidiagonal (fst_le snd_le)

open FullBinaryTree

def catalan_number : Nat → Nat
| 0 => 1
| succ n => ∑ i : Fin (succ n), (catalan_number i) * (catalan_number (n - i))

def full_binary_tree_of_node_count (n : Nat) : Type :=
  { T : FullBinaryTree // T.nodes = n}

def catalan_structure (n : Nat) : Type :=
  (i : Fin (n + 1)) × Fin (catalan_number i) × Fin (catalan_number (n - i))

def equiv_full_binary_tree_catalan_structure : (n : Nat) ->
  full_binary_tree_of_node_count (n + 1) ≃ catalan_structure n := by sorry

def equiv_catalan_structure : (n : Nat) ->
  catalan_structure n ≃ Fin (catalan_number (n + 1)) := by sorry

def compute_support_full_binary_tree : (n : Nat) ->
  full_binary_tree_of_node_count n ≃ Fin (catalan_number n)
| 0 => by sorry
| succ n => Equiv.trans
  (equiv_full_binary_tree_catalan_structure n)
  (equiv_catalan_structure n)
