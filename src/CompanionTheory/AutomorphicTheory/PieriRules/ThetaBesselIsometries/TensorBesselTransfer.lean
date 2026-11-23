module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransfer
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_sum_of_add_on_sm {k r : ℕ} (R : Rep k r) {Wp : Type} [AddCommGroup Wp] [Module ℂ Wp] (l : R.H → Wp)
    (hadd : ∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) (hsmul : ∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v)
    {α : Type} (s : Finset α) (f : α → R.H) (hf : ∀ i, f i ∈ R.sm) : l (∑ i ∈ s, f i) = ∑ i ∈ s, l (f i) :=
  _root_.GlobalTheory.map_sum_of_add_on_sm R l hadd hsmul s f hf

theorem herm_smul_eq_sum_of_tensRaw : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) :=
  fun h1 k r ι κ [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] ρ Γ d R RI io pr ε mu muI Wp [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] om l lI β h2 h3 =>
    _root_.GlobalTheory.herm_smul_eq_sum_of_tensRaw h1 k r ι κ ρ Γ d R RI io pr ε mu muI Wp om l lI β (GlobalTheory.isDS_of_isDG h2) (fun s => GlobalTheory.isDS_of_isDG (h3 s))

end GlobalTheory
