import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SumSquaresNeThreeThreeAdic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.SplitUnitary.Model

open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)




section Form

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)


end Form

section Edge

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def Concl (hc : ∀ z, c (c z) = z) (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (χ : Eˣ →* Circle) : Prop :=
  ∃ ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E)),
      IsSmoothRep ω ∧
      (∀ μ : @Measure (Matrix α ν E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)),
          ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ) ∧
      (∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E),
        Heisenberg₂ c hψ Q w * ω g =
          ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) ∧
      ∀ (a : GL ν E) (φ : SB (Matrix α ν E)) (x : Matrix α ν E),
        (ω (levi c hc a) φ : Matrix α ν E → ℂ) x =
          (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
            ((nabs F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) ^
              ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
            (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E))




end Edge

end GlobalTheory.SplitUnitary.Model

end
