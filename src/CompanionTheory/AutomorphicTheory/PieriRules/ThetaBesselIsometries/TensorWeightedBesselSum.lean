module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrepDiscreteSeriesSum
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorRawOfFrep
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s :=
  fun h1 k r ι κ [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] ρ Γ d R RI io pr ep ε mu muI Wp [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] Wq [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] om om' l l' lI lI' F s h2 h3 =>
    _root_.GlobalTheory.coef_mul_split h1 k r ι κ ρ Γ d R RI io pr ep ε mu muI Wp Wq om om' l l' lI lI' F s (GlobalTheory.isDS_of_isDG h2) (fun s => GlobalTheory.isDS_of_isDG (h3 s))

end GlobalTheory
