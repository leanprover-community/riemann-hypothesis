module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatrixCoefficientSmoothDerivatives
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoeffDeriv

open _root_.Gp91.GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def coefL (R : Rep k r) (x : R.H) (X : V) : R.H →L[ℝ] V :=
  ((innerSL ℂ x).smulRight X).restrictScalars ℝ

theorem coefL_apply (x w : R.H) (X : V) : coefL R x X w = ⟪x, w⟫_ℂ • X :=
  _root_.GlobalTheory.CoeffDeriv.coefL_apply x w X

theorem dsigW_smooth (hR : R.IsDG ε mu) {y : R.H} (hy : y ∈ R.sm) (b : List (Mx k r))
    (hb : ∀ Y ∈ b, B.inLie k r Y) : PI.UpqRep.dsigW (k := k) (r := r) R.σ b y ∈ R.sm :=
  _root_.GlobalTheory.CoeffDeriv.dsigW_smooth (GlobalTheory.isDS_of_isDG hR) hy b hb

theorem right_step (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (X : V) (F : Mx k r → V) (x : R.H) {y : R.H}
    (hy : y ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      ⟪x, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ Y y)⟫_ℂ • X :=
  _root_.GlobalTheory.CoeffDeriv.right_step hK (GlobalTheory.isDS_of_isDG hR) X F x hy hF hY g hg

theorem left_step (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (X : V) (F : Mx k r → V) {x : R.H} (y : R.H)
    (hx : x ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    B.LdV Y F g = ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ Y x, R.σ g y⟫_ℂ • X :=
  _root_.GlobalTheory.CoeffDeriv.left_step hK (GlobalTheory.isDS_of_isDG hR) X F y hx hF hY g hg

theorem coeff_dLR : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDG ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X :=
  fun h1 k r ε mu R V [NormedAddCommGroup V] [NormedSpace ℂ V] X F h2 =>
    _root_.GlobalTheory.CoeffDeriv.coeff_dLR h1 k r ε mu R V X F (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory.CoeffDeriv
