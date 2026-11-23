module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSumDecomposition
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosureStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KapBes

variable {k r : ℕ}

theorem dsigW_zero (R : Rep k r) (W : List (Mx k r)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 :=
  _root_.GlobalTheory.KapBes.dsigW_zero R W

theorem smMap_zero (R R' : Rep k r) : SmMap R R' (fun _ => 0) :=
  _root_.GlobalTheory.KapBes.smMap_zero R R'

theorem smMap_congr {R R' : Rep k r} {T T' : R.H → R'.H} (h : SmMap R R' T)
    (e : ∀ v ∈ R.sm, T' v = T v) : SmMap R R' T' :=
  _root_.GlobalTheory.KapBes.smMap_congr h e

theorem smMap_sum {R R' : Rep k r}
    (hl : ∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v))
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (T : ι → R.H → R'.H) (hT : ∀ i, SmMap R R' (T i)) :
    SmMap R R' (fun v => ∑ i ∈ s, a i • T i v) :=
  _root_.GlobalTheory.KapBes.smMap_sum hl s a T hT

theorem mem_GG_of_mem_Sset {z : Fin (2 * r + k + 1) → ℂ} {s : Mx k r} (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) :
    s ∈ GG k r :=
  _root_.GlobalTheory.KapBes.mem_GG_of_mem_Sset hs

theorem ev_eq {ι : Type} [Fintype ι] (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) :
    ev Γ R a x = ∑ j, (star a ᵥ* Γ) j • x j :=
  _root_.GlobalTheory.KapBes.ev_eq Γ R a x

theorem vecMul_inv {ι : Type} [Fintype ι] (Γ A : Matrix ι ι ℂ) (a : ι → ℂ) (hA : Aᴴ * Γ * A = Γ)
    (ha : A *ᵥ a = a) : (star a ᵥ* Γ) ᵥ* A = star a ᵥ* Γ :=
  _root_.GlobalTheory.KapBes.vecMul_inv Γ A a hA ha

theorem main : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) :=
  fun h1 k r ι κ [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] ρ Γ d R RI io pr ε mu muI Wp [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] z π om h2 h3 =>
    _root_.GlobalTheory.KapBes.main h1 k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π om (GlobalTheory.isDS_of_isDG h2) (fun s => GlobalTheory.isDS_of_isDG (h3 s))

end GlobalTheory.KapBes
