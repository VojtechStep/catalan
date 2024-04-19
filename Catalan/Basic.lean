import Mathlib.Logic.Equiv.Defs
import «Catalan».FullBinaryTrees
import «Catalan».PlaneTrees

section PTofFBT
open FullBinaryTree

def plane_tree_of_full_binary_tree : FullBinaryTree → PlaneTree
| leaf =>
  PlaneTree.leaf
| node T1 T2 =>
  PlaneTree.join
    ( plane_tree_of_full_binary_tree T1)
    ( plane_tree_of_full_binary_tree T2)

theorem plane_tree_of_leaf : plane_tree_of_full_binary_tree leaf = PlaneTree.leaf :=
  rfl

theorem plane_tree_of_node (left : FullBinaryTree) (right : FullBinaryTree) :
  plane_tree_of_full_binary_tree (node left right) =
  PlaneTree.join
    ( plane_tree_of_full_binary_tree left)
    ( plane_tree_of_full_binary_tree right) :=
  rfl

end PTofFBT

section FBTofPT
open PlaneTree
open List

def full_binary_tree_of_plane_tree : PlaneTree → FullBinaryTree
| branches b => match b with
  | nil => FullBinaryTree.leaf
  | cons left rights =>
    FullBinaryTree.node
      ( full_binary_tree_of_plane_tree left)
      ( full_binary_tree_of_plane_tree (branches rights))

theorem full_binary_tree_of_leaf : full_binary_tree_of_plane_tree leaf = FullBinaryTree.leaf :=
  rfl

theorem full_binary_tree_of_cons (left : PlaneTree) (rights : List PlaneTree) :
  full_binary_tree_of_plane_tree (branches (cons left rights)) =
  FullBinaryTree.node
    ( full_binary_tree_of_plane_tree left)
    ( full_binary_tree_of_plane_tree (branches rights)) := by
  dsimp [full_binary_tree_of_plane_tree]
  rw [WellFounded.fix_eq]

end FBTofPT

example : FullBinaryTree ≃ PlaneTree where
  toFun := plane_tree_of_full_binary_tree
  invFun := full_binary_tree_of_plane_tree
  left_inv := by
    intro f
    induction f with
    | leaf => apply full_binary_tree_of_leaf
    | node T1 T2 H1 H2 =>
      rw [plane_tree_of_node]
      cases e : plane_tree_of_full_binary_tree T2
      simp; rw [full_binary_tree_of_cons, H1, ← e, H2]
  right_inv := @PlaneTree.rec
    ( λ p =>
      plane_tree_of_full_binary_tree
        ( full_binary_tree_of_plane_tree p) =
      p)
    ( λ branches =>
      plane_tree_of_full_binary_tree
        ( full_binary_tree_of_plane_tree
          ( PlaneTree.branches branches)) =
      PlaneTree.branches branches)
    ( λ branches H => H)
    ( plane_tree_of_leaf)
    ( λ left rights HL HR => by
      unfold full_binary_tree_of_plane_tree
      simp
      rw [plane_tree_of_node, HL, HR]
      rfl)

section examples

def e1 : PlaneTree :=
  PlaneTree.branches
  [ PlaneTree.branches
    [ PlaneTree.branches
      [ PlaneTree.leaf
      , PlaneTree.leaf] ]
  , PlaneTree.branches
    [ PlaneTree.leaf
    , PlaneTree.branches
      [ PlaneTree.leaf ]
    , PlaneTree.leaf]
  , PlaneTree.leaf ]

#reduce full_binary_tree_of_plane_tree e1

#reduce full_binary_tree_of_plane_tree $ PlaneTree.branches [ PlaneTree.leaf, PlaneTree.leaf ]
#reduce PlaneTree.join PlaneTree.leaf PlaneTree.leaf

end examples
