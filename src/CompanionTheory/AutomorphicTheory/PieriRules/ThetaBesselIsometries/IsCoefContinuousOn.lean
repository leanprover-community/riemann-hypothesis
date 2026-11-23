module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCoefContinuousOn
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.AemeasurableBesselNormIntegrandBigCellImports
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupMeas

theorem isDS_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDG ε μ) (v : R.H) : ContinuousOn (fun g => R.σ g v) (GG k r) :=
  _root_.GlobalTheory.SupMeas.isDS_continuousOn (GlobalTheory.isDS_of_isDG h) v

theorem isCoef_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {l : R.H → Wp} {l' : R.H → Wq} {F : Mx k r → (Wq →L[ℂ] Wp)} {s : ℂ}
    (h : R.IsDG ε μ) (hF : IsCoef R l l' F s) : ContinuousOn F (GG k r) :=
  _root_.GlobalTheory.SupMeas.isCoef_continuousOn (GlobalTheory.isDS_of_isDG h) hF

end GlobalTheory.SupMeas
