module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmul
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem kum_smul (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) (h : Kum X l n x χ) :
    Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  apply GlobalTheory.KZ.BettiB.kum_smul <;> assumption

end GlobalTheory.KZ.H3
