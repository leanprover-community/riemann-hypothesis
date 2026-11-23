module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselLieTriangularVanishing
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementKT
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacterStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAtStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNilp

variable {k r : ℕ}

theorem H_ne {i j : Fin (2 * r + k + 1)} (h : Formalism.QuantumDeterminants.Hpk k r i j ≠ 0) :
    (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
      (r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = j.val) :=
  _root_.GlobalTheory.BesselNilp.H_ne h

theorem H_herm : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r :=
  _root_.GlobalTheory.BesselNilp.H_herm

theorem H_sq : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 :=
  _root_.GlobalTheory.BesselNilp.H_sq

def Pat (Y : Mx k r) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0

theorem pat_theta {Y : Mx k r} (hY : Pat Y) : Pat (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r) :=
  _root_.GlobalTheory.BesselNilp.pat_theta hY

theorem ell_add (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (A + B) = Formalism.QuantumDeterminants.ell k r z A + Formalism.QuantumDeterminants.ell k r z B :=
  _root_.GlobalTheory.BesselNilp.ell_add z A B

theorem ell_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (A : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (c • A) = c * Formalism.QuantumDeterminants.ell k r z A :=
  _root_.GlobalTheory.BesselNilp.ell_smul z c A

theorem ell_sub (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (A - B) = Formalism.QuantumDeterminants.ell k r z A - Formalism.QuantumDeterminants.ell k r z B :=
  _root_.GlobalTheory.BesselNilp.ell_sub z A B

theorem theta_key (Y : Mx k r) :
    (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * Y ∧
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r) = Yᴴ * Formalism.QuantumDeterminants.Hpk k r :=
  _root_.GlobalTheory.BesselNilp.theta_key Y

theorem lie_re (Y : Mx k r) : PI.UpqRep.InLieHpk k r
    ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) :=
  _root_.GlobalTheory.BesselNilp.lie_re Y

theorem lie_im (Y : Mx k r) : PI.UpqRep.InLieHpk k r
    ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) :=
  _root_.GlobalTheory.BesselNilp.lie_im Y

theorem on_real (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {l : R.H → Wp}
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hπ : ∀ x, π 1 x = x) (hl : IsBes R z π l) {X : Mx k r}
    (hX : PI.UpqRep.InLieHpk k r X) (hP : Pat X) {v : R.H} (hv : v ∈ R.sm) :
    l (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) =
      (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) • l v :=
  _root_.GlobalTheory.BesselNilp.on_real hK (GlobalTheory.isDS_of_isDG hR) hz hπ hl hX hP hv

theorem bessel_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), Formalism.QuantumDeterminants.inWb k r z → (∀ x, π 1 x = x) → IsBes R z π l → ∀ Y : Mx k r, (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0) → ∀ v ∈ R.sm, l (R.dC Y v) = (Formalism.QuantumDeterminants.ell k r z Y - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r))))) • l v :=
  fun h1 k r ε mu R h2 =>
    _root_.GlobalTheory.BesselNilp.bessel_dC h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory.BesselNilp
