import Mathlib.Logic.Equiv.Defs

inductive PlaneTree : Type
| branches : List PlaneTree → PlaneTree

-- Algebra for X ↦ 1 + X²
@[inline]
def PlaneTree.leaf : PlaneTree := branches []

@[simp]
def PlaneTree.join : PlaneTree → PlaneTree → PlaneTree
| left, branches rights =>
  branches (List.cons left rights)

def least_fixed_point_list_plane_tree : List PlaneTree ≃ PlaneTree := Equiv.mk
  ( PlaneTree.branches)
  ( λ (PlaneTree.branches l) => l)
  ( λ _ => rfl)
  ( λ (PlaneTree.branches _) => rfl)
