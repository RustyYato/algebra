namespace Int

def induction {motive : Int → Prop} (i : Int)
  (zero : motive 0) (succ : ∀i, motive i → motive (i + 1)) (pred : ∀i, motive i → motive (i - 1)) : motive i := by
induction i with
| ofNat i =>
  induction i with
  | zero => exact zero
  | succ i ih => exact succ _ ih
| negSucc i =>
  induction i with
  | zero =>
    suffices motive (0 - 1) from this
    apply pred
    assumption
  | succ n ih =>
    suffices motive (-[n+1] - 1) from this
    apply pred
    assumption

end Int
