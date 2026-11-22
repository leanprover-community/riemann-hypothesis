module

public import Mathlib

@[expose] public section

noncomputable section

namespace PI.FglPhSplit

open Classical

def expMv {K : Type*} [Field K] {σ : Type*} (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : K)

namespace Dat

variable {K : Type*} [Field K] (g : Dat K) {σ : Type*}

end Dat

end PI.FglPhSplit

end
