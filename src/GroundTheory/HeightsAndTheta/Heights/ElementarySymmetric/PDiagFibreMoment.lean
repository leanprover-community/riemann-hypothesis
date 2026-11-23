module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StDiagFibreFubini
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagFibreMoment

theorem coeff_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (m : Fin 3 →₀ ℕ) :
    AddMonoidAlgebra.coeff (momentPoly μ w Q) m = ∫ p, w p * AddMonoidAlgebra.coeff Q m p ∂μ := by
  rw [momentPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h]
    simp

theorem momentPoly_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) (s : Finset ι)
    (Q : ι → MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ i ∈ s, ∀ m, Integrable (fun p => w p * AddMonoidAlgebra.coeff (Q i) m p) μ) :
    momentPoly μ w (∑ i ∈ s, Q i) = ∑ i ∈ s, momentPoly μ w (Q i) := by
  ext m
  rw [coeff_momentPoly, coeff_sum, coeff_sum]
  simp only [coeff_momentPoly, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => hQ i hi m

theorem continuous_coeff_aeval (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (AddMonoidAlgebra.coeff (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q) m) := by
  set φ : C(S2 × S2, ℝ) →ₐ[ℝ] (S2 × S2 → ℝ) := ContinuousMap.coeFnAlgHom (α := S2 × S2) (A := ℝ) ℝ
  set v : Fin 2 → MvPolynomial (Fin 3) C(S2 × S2, ℝ) :=
    ![∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.fst),
      ∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.snd)]
  have hv : ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] = fun r => mapAlgHom φ (v r) := by
    funext r
    fin_cases r

    · simp only [Fin.zero_eta, Matrix.cons_val_zero, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]
      apply Finset.sum_congr rfl
      intro i hi
      congr 2

    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, v, dotPoly, mapAlgHom_apply, map_sum,
      map_mul, map_X, map_C]
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
  rw [hv, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (AddMonoidAlgebra.coeff (aeval v Q) m).continuous

theorem sum_words (k : ℕ) :
    ∑ i ∈ Finset.range k, ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ) =
      gPoly k := by
  rw [FibreLocal.gPoly_eq, FlagBundles.gKernel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  rw [show 2 * k - 2 * i = (2 * k - 1 - 2 * i) + 1 by omega, pow_succ, pow_succ]
  ring

theorem sum_diagWordMomentPoly (k : ℕ) :
    ∑ i ∈ Finset.range k, diagWordMomentPoly k i = fibreMomentPoly k := by
  simp only [diagWordMomentPoly]
  rw [← momentPoly_sum _ _ _ _ fun i _ m =>
    FibreLocal.integrable_mul _ (continuous_coeff_aeval _ m)]

  rw [← map_sum, ← map_sum, ← map_sum, sum_words]
  rfl

end DiagFibreMoment

end

end GroundTheory.Heights₂.Heights.Inter
