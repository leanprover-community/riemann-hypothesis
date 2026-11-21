import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv

open MeasureTheory GlobalTheory.Orb GlobalTheory.AdelicU Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.Published

def PseudoCoefficientUpq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : GlobalTheory.Dec.IsSqIntIrr ε σ)
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f

theorem PseudoCoefficientUpq.of_isDS (hP : PseudoCoefficientUpq) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}
    (h : IsDS ε lam σ) (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure] :
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f :=
  hP n ε X σ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩ μ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult NumberField in

theorem PseudoCoefficientUpq.exists_isTestArchG (hP : PseudoCoefficientUpq) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    [∀ w, (μa w).IsHaarMeasure] : ∃ fa, IsTestArchG M μa fa :=
  GlobalTheory.Orb.exists_isTestArchG M (fun ρ =>
    have ⟨f, hf⟩ := hP.of_isDS (M.ds ρ) (Formalism.REAL.muG _)
    ⟨Formalism.REAL.muG _, inferInstance, f, hf.2⟩) μa


end GlobalTheory.Published
