module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationEqZpow

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem val_unif' {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem sqrt_pow (q : ℝ) (hq : 0 < q) (v : ℤ) (N : ℕ) :
    (q ^ (-v)) ^ ((N : ℝ) / 2) = (Real.sqrt q) ^ (-v * N) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

end GlobalTheory.TwBridge.PsiRat

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

end GlobalTheory.TwBridge.PsiRat

namespace GlobalTheory.TwBridge

end GlobalTheory.TwBridge
