import Mathlib

namespace KStar.TotallyRealRoots

private def sieveOK (n : ℕ) : Bool :=
  decide (2 ≤ n) && [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31].all (fun d => n == d || n % d != 0)

private def headF (n : ℕ) : ℕ :=
  if sieveOK n then (Nat.log2 (n ^ 256) + 1) * 1000000 / n ^ 2 + 1 else 0



end KStar.TotallyRealRoots
