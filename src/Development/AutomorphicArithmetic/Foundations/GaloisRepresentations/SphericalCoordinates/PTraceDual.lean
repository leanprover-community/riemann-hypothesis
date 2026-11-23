module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.traceDual_of :
    UpperTheory.Gal.W2.TraceDual := by
  intro F _ _ s hs
  classical
  let e := NumberField.RingOfIntegers.basis F
  choose m hm using fun k => hs (e k)
  let L : F →ₗ[ℚ] ℚ := (NumberField.integralBasis F).constr ℚ (fun k => (m k : ℚ))
  let D := (Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)
  let b : F := D.symm L
  have hb : ∀ x : F, Algebra.trace ℚ F (b * x) = L x := by
    intro x
    have h := LinearMap.congr_fun (D.apply_symm_apply L) x
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h
    exact h
  have htr : ∀ x : F, algebraMap ℚ ℂ (Algebra.trace ℚ F x) = ∑ τ : F →+* ℂ, τ x := by
    intro x
    rw [trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ (fun σ => rfl)
  have hk : ∀ k, ∑ τ : F →+* ℂ, τ (e k : F) * (τ b - s τ) = 0 := by
    intro k
    simp only [mul_sub, Finset.sum_sub_distrib, ← map_mul]
    rw [hm k, ← htr, mul_comm (e k : F) b, hb, sub_eq_zero]
    have he : (e k : F) = NumberField.integralBasis F k := by
      rw [NumberField.integralBasis_apply]
    rw [he, Module.Basis.constr_basis]
    simp
  let P : ((F →+* ℂ) → ℂ) →ₗ[ℂ] ℂ := ∑ τ, (τ b - s τ) • LinearMap.proj τ
  have hP : P = 0 := by
    apply (NumberField.canonicalEmbedding.latticeBasis F).ext
    intro k
    simp only [P, NumberField.canonicalEmbedding.latticeBasis_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply,
      NumberField.canonicalEmbedding.apply_at, smul_eq_mul, LinearMap.zero_apply]
    rw [← hk k]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_comm, NumberField.integralBasis_apply]
  refine ⟨b, fun τ => ?_⟩
  have h := LinearMap.congr_fun hP (Pi.single τ 1)
  simp [P, Pi.single_apply] at h
  rw [sub_eq_zero] at h
  exact h.symm
