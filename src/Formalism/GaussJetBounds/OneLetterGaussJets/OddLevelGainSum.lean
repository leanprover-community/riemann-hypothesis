module

public import Formalism.GaussJetBounds.Statement

@[expose] public section

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

section TopData

variable (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)

def WcapOneLetter (s : ZMod d) : ℕ :=
  sSup ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) ''
    {i : ℕ | Odd i ∧ l ^ i ≤ Dl d TT nu1 size (s - (i : ZMod d))})

open Classical in
def oddLevelGainSum (s : ZMod d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ ¬ (∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e) then
      max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else 0

end TopData

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
