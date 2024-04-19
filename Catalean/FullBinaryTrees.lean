inductive FullBinaryTree : Type
| leaf
| node (T1 T2 : FullBinaryTree)

def FullBinaryTree.nodes : FullBinaryTree → Nat
| leaf => 0
| node left right => 1 + left.nodes + right.nodes
