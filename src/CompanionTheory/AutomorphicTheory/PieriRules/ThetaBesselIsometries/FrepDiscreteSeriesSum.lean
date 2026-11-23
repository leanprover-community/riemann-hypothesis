module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensAdj

section
variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_left (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (y : ι → R.H) :
    hh Γ R (fun c => ∑ I, f I c) y = ∑ I, hh Γ R (f I) y :=
  _root_.GlobalTheory.TensAdj.hh_sum_left Γ R f y

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (x : ι → R.H) :
    hh Γ R x (fun c => ∑ I, f I c) = ∑ I, hh Γ R x (f I) :=
  _root_.GlobalTheory.TensAdj.hh_sum_right Γ R f x

omit [DecidableEq ι] in
theorem sum_sm (R : Rep k r) (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) : ∑ c, x c ∈ R.sm :=
  _root_.GlobalTheory.TensAdj.sum_sm R x hx

omit [DecidableEq ι] in
theorem hh_tm (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) (v : R.H) :
    hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ :=
  _root_.GlobalTheory.TensAdj.hh_tm Γ R a x v

theorem norm_sq_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Γ : Matrix ι ι ℂ}
    (h : Γᴴ * Γ = 1) (x : ι → H) : ∑ i, ‖∑ j, Γ i j • x j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  _root_.GlobalTheory.TensAdj.norm_sq_mul h x

theorem norm_hh_le {Γ : Matrix ι ι ℂ} (h : Γᴴ * Γ = 1) (R : Rep k r) (x : ι → R.H) :
    ‖hh Γ R x x‖ ≤ ∑ c, ‖x c‖ ^ 2 :=
  _root_.GlobalTheory.TensAdj.norm_hh_le h R x

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
  {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} {ep : κ → ℝ}

theorem proj_sm (hT : TensH ρ Γ R RI io pr ep) (I : κ) {x : ι → R.H} (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, pr I c (x c) ∈ (RI I).sm :=
  _root_.GlobalTheory.TensAdj.proj_sm hT I hx

theorem adj (hT : TensH ρ Γ R RI io pr ep) (I : κ) (y : (RI I).H) (hy : y ∈ (RI I).sm) (x : ι → R.H)
    (hx : ∀ c, x c ∈ R.sm) :
    hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ :=
  _root_.GlobalTheory.TensAdj.adj hT I y hy x hx

theorem parseval (hT : TensH ρ Γ R RI io pr ep) (x x' : ι → R.H) (hx : ∀ c, x c ∈ R.sm)
    (hx' : ∀ c, x' c ∈ R.sm) :
    hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ :=
  _root_.GlobalTheory.TensAdj.parseval hT x x' hx hx'

end

theorem tens_adj : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ :=
  fun h1 k r ι κ [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] ρ Γ d R RI io pr ep ε mu muI h2 h3 =>
    _root_.GlobalTheory.TensAdj.tens_adj h1 k r ι κ ρ Γ d R RI io pr ep ε mu muI (GlobalTheory.isDS_of_isDG h2) (fun s => GlobalTheory.isDS_of_isDG (h3 s))

end GlobalTheory.TensAdj
