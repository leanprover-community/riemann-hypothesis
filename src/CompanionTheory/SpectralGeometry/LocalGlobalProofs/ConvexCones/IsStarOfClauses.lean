module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStarOfOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPointStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan GlobalTheory.PolFan.StarCells

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses

theorem isStarOf_of_clauses : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf bar q ψ w ψ' := by
  intro O _ _ _ _ bar _ q ψ w ψ' hψ hw h1 h2
  refine ⟨h1, h2, ?_⟩

  intro X _ _ _ _ hX n γ' hγ'
  set B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ j, (1 : ℝ) • toReal (γ' j) with hBdef
  have hB : B ∈ psdCone (bar := bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone O bar X n γ' _ hγ'.mem hγ'.nonneg fun _ => zero_le_one
  obtain ⟨S, -, hfin⟩ := (hψ X hX).finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hfin B hB
  set δ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hδdef
  have hδ : IsCell bar ψ δ := CarDim.isCell_pull_equiv hγ e.symm
  have hBδ : B = ∑ i, c i • toReal (δ i) := by
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hδdef, pull_apply,
      LinearEquiv.coe_coe]
    exact this
  have key : ∀ (k : ℕ) (σ : Fin k → LinearMap.BilinForm ℤ X), IsCell bar ψ' σ → B ∈ rcone σ →
      ∀ j, InRCone σ (γ' j) := by
    rintro k σ hσ ⟨t, ht, hBt⟩ j
    obtain ⟨kk, d, hk, hkd⟩ := inCone_of_strict hσ.strict hσ.linear hγ'.mem hγ'.nonneg (a := fun _ => 1) (b := t)
      (fun _ => zero_le_one) ht ((linearOn_iff ψ' γ').1 hγ'.linear _ fun _ => zero_le_one) hBt j one_ne_zero
    exact inRCone_of_nsmul hk hkd
  by_cases hc0 : ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ InRCone δ β ∧ w.evalZ β = 1
  · obtain ⟨β₀, hβ₀, hβ₀p, hin, hw1⟩ := hc0
    have hne : β₀ ≠ 0 := by
      intro h0
      have := (hw X hX).2.1 β₀ hβ₀ hβ₀p hw1 2 0 (by simp [h0])
      omega
    obtain ⟨m', s, h, hfc, hpos, hBc⟩ :=
      GlobalTheory.T.realCone_covered_by_star_at_point X m δ β₀ B (fun i => (hδ.mem i).1) hδ.nonneg hne hin ⟨c, hc, hBδ⟩
    exact Or.inr ⟨m, δ, β₀, m', s, h, hδ, hβ₀, hβ₀p, hw1, hin, hfc, hpos,
      key _ _ (h2 X hX m δ hδ β₀ hβ₀ hβ₀p hw1 hin m' s h hfc hpos) hBc⟩
  · push_neg at hc0
    have h0 : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β = 0 := fun β hβ hp hi =>
      ((hw X hX).1 β hβ hp).resolve_right (hc0 β hβ hp hi)
    exact Or.inl ⟨m, δ, hδ, h0, key _ _ (h1 X hX m δ hδ h0) ⟨c, hc, hBδ⟩⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses
