module

public import Formalism.HermitianCurvature.LevelRecursionCondNeeded

@[expose] public section

namespace Formalism.FourierDecayAlt.PairingProductCorollary

open Finset
open scoped ComplexOrder

noncomputable section

def PairingGramInequality (Ntt : ℂ) (Nt Nt' : ℝ) : Prop := ‖Ntt‖ ^ 2 ≤ Nt * Nt'

def minFac (L o : ℝ) (K : ℕ) : ℝ := if L < o then (L / o) ^ K else 1

def oAbs {ι : Type} (t t' : ι → ℂ) (v : ι) : ℝ := ‖1 / t v - 1 / t' v‖

def LeadingBlockSeveralPlacesBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ : ι → ℝ) (t t' : ι → ℂ) (Ntt : ℂ)
    (Nt Nt' S1 S2 : ℝ),
    (∀ v, t v ≠ 0 ∧ t' v ≠ 0) → (∀ v, 0 ≤ abelian₂ v) → 0 ≤ Nt → 0 ≤ Nt' → 0 ≤ S1 → 0 ≤ S2 →
    PairingGramInequality Ntt Nt Nt' →
    Nt ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1 →
    Nt' ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2 →
    ‖Ntt‖ ≤ (∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K) * ((S1 + S2) / 2)

end

end Formalism.FourierDecayAlt.PairingProductCorollary
