module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ

@[expose] public section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) → IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  first | exact @GlobalTheory.K5.PDiv.pdiv
