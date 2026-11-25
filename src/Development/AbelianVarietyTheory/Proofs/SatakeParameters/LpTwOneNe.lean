module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp

noncomputable section

namespace GlobalTheory

theorem WeilDeligne.WD.lpTw_one_ne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (x : WD h) : 0 < x.lpDim → x.lpTw 1 ≠ x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  intro hn heq
  rw [WD.lpTw_mk, WD.mk_eq_mk] at heq
  obtain ⟨e, he, -⟩ := heq
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
  set σ := frob h
  set T := (a.tw 1).ρ σ
  set B := a.ρ σ
  have hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B := by
    refine LinearMap.ext fun v => ?_
    show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v
    rw [he, LinearEquiv.apply_symm_apply]
  have hdet : LinearMap.det T = LinearMap.det B := by
    rw [← hconj, LinearMap.det_conj]
  have hT : T = ((normV w : ℕ) : ℂ) • B := by
    show (a.tw 1).ρ σ = _
    rw [WDRep.tw_ρ, deg_frob]
    simp only [Complex.ofReal_one, Complex.cpow_one, zpow_one]
    rfl
  rw [hT, LinearMap.det_smul, Module.finrank_fin_fun] at hdet
  have hB : LinearMap.det B ≠ 0 := by
    intro h0
    have h1 : B * a.ρ σ⁻¹ = 1 := by
      show a.ρ σ * a.ρ σ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg LinearMap.det h1
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hq : ((normV w : ℕ) : ℂ) ^ n = 1 := by
    have := mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)
    exact this
  have hq' : (normV w : ℕ) ^ n = 1 := by exact_mod_cast hq
  have h1q := one_lt_normV w
  have : 1 < (normV w : ℕ) ^ n := Nat.one_lt_pow hn.ne' h1q
  omega

end GlobalTheory
