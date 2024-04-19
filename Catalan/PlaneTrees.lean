inductive PlaneTree : Type
| branches : List PlaneTree → PlaneTree

-- Algebra for X ↦ 1 + X²
@[inline]
def PlaneTree.leaf : PlaneTree := branches []

@[simp]
def PlaneTree.join : PlaneTree → PlaneTree → PlaneTree
| left, branches rights =>
  branches (List.cons left rights)
