def BallotSequence : Type := { pos_neg : Nat × Nat // pos_neg.1 - pos_neg.2 >= 0 }

def BallotSequence.pos : BallotSequence → Nat
| b => b.val.1
def BallotSequence.neg : BallotSequence → Nat
| b => b.val.2

def ballot_sequence_of_length (n : Nat) : Type :=
  { seq : BallotSequence // seq.pos + seq.neg = n }
