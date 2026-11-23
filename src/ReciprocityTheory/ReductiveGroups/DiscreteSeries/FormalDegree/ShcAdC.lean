module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbB

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) (w : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => shcAd y (pmat w) ab.1.1 ab.1.2

theorem detPb {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      (LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
        (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))) ^ 4 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have hU' : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  have hY : U * dpbD (pev y) * Uᴴ = pmat y := (pmat_isHermitian y).spectral_theorem.symm
  have e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc) := rfl
  have e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε) := by
    funext w ab
    refine (dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm
    rw [dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]
  rw [e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)

end ReciprocityTheory.ChartRestriction.DS
