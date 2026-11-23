module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

noncomputable section

namespace Formalism.IndefR.Rat

open Matrix

theorem coord_rat {K : Type} [Field K] (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {κ : Type} [Fintype κ]
    [DecidableEq κ] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : κ → Module.Dual ℂ E) (hψ : ∀ e, (∀ i, ψ i e = 0) → e = 0)
    (f : (ι → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f)
    (hfr : ∀ i l, ψ i (f (Pi.single l 1)) ∈ Set.range σ)
    (c : ι → ℂ) (hc : ∀ i, ψ i (f c) ∈ Set.range σ) : ∀ l, c l ∈ Set.range σ := by
  classical
  intro l

  choose A'' hA' using hfr
  choose b' hb' using hc
  set A' : Matrix κ ι K := Matrix.of A''
  have hfc : ∀ y : ι → ℂ, f y = ∑ m, y m • f (Pi.single m 1) := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]

    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by
      rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hmul : ∀ y : ι → ℂ, ((A'.map σ) *ᵥ y) = fun i => ψ i (f y) := by
    intro y; funext i

    rw [hfc y, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, A', Matrix.of_apply, hA', map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  have hinj : Function.Injective (Matrix.toLin' A') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (A'.map σ) *ᵥ (σ ∘ x) = 0 := by
      funext i
      rw [← RingHom.map_mulVec σ A' x i]
      have hx' : (A' *ᵥ x) i = 0 := by
        have := congrFun hx i; simpa using this
      simp [hx']
    rw [hmul] at h1
    have h2 : f (σ ∘ x) = 0 := hψ _ (fun i => congrFun h1 i)
    have h3 : (σ ∘ x) = 0 := hf (by rw [h2, map_zero])
    funext m
    have := congrFun h3 m
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A')
    (LinearMap.ker_eq_bot.mpr hinj)
  set L' : Matrix ι κ K := LinearMap.toMatrix' g
  have hLA : L' * A' = 1 := by
    have : LinearMap.toMatrix' (g.comp (Matrix.toLin' A')) = L' * A' := by
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
    rw [← this, hg, LinearMap.toMatrix'_id]
  have hLA' : (L'.map σ) * (A'.map σ) = 1 := by
    rw [← Matrix.map_mul, hLA, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hb : (A'.map σ) *ᵥ c = σ ∘ b' := by
    rw [hmul]; funext i; simp [hb']
  have hcL : c = (L'.map σ) *ᵥ (σ ∘ b') := by
    rw [← hb, Matrix.mulVec_mulVec, hLA', Matrix.one_mulVec]
  rw [hcL]
  exact ⟨(L' *ᵥ b') l, RingHom.map_mulVec σ L' b' l⟩

end Formalism.IndefR.Rat
