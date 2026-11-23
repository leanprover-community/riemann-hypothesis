module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCapelliIntertwine
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementKT
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAt
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DualEmb

open PI.UpqRep _root_.Gp91.GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem hasDerivAt_inv_exp_entry (X : Mx k r) (j c : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) (-X j c) 0 :=
  _root_.GlobalTheory.DualEmb.hasDerivAt_inv_exp_entry X j c

theorem lie_part₁ (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) :=
  _root_.GlobalTheory.DualEmb.lie_part₁ Y

theorem lie_part₂ (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) :=
  _root_.GlobalTheory.DualEmb.lie_part₂ Y

theorem io_dsig (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDG ε mu) {RI : Fin (2 * r + k + 1) → Rep k r}
    {muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ}
    {io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H} {pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H}
    (hI : ∀ s, (RI s).IsDG ε (muI s)) (hT : TensRaw dualM R RI io pr) (s : Fin (2 * r + k + 1))
    {X : Mx k r} (hX : InLieHpk k r X) {y : (RI s).H} (hy : y ∈ (RI s).sm) (c : Fin (2 * r + k + 1)) :
    io s c (dsig (k := k) (r := r) (RI s).σ X y) =
      dsig (k := k) (r := r) R.σ X (io s c y) - ∑ j, X j c • io s j y :=
  _root_.GlobalTheory.DualEmb.io_dsig hK (GlobalTheory.isDS_of_isDG hR) (fun s => GlobalTheory.isDS_of_isDG (hI s)) hT s hX hy c

end GlobalTheory.DualEmb

namespace GlobalTheory

open DualEmb

theorem dualTens_io_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H), (∀ s, (RI s).IsDG ε (muI s)) → TensRaw dualM R RI io pr → ∀ s Y, ∀ y ∈ (RI s).sm, ∀ c, io s c ((RI s).dC Y y) = R.dC Y (io s c y) - ∑ j, Y j c • io s j y :=
  fun h1 k r ε mu R h2 RI muI io pr h3 =>
    _root_.GlobalTheory.dualTens_io_dC h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2) RI muI io pr (fun s => GlobalTheory.isDS_of_isDG (h3 s))

end GlobalTheory

end
