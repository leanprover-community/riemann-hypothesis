module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Determinant
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace GlobalTheory.AnalyticMatrixEntries

universe u_1 u_2

theorem analyticAt_entry {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} (b : Module.Basis ι ℂ E) {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) (i j : ι) :
    AnalyticAt ℂ (fun z : X ↦ b.repr (A z (b j)) i) a := by
  let L : (E →L[ℂ] E) →L[ℂ] ℂ :=
    (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℂ E (b j))
  have h := (L.analyticAt (A a)).comp hA
  convert h using 1
  funext z
  simp [L, Module.Basis.coord_apply]

theorem analyticAt_det {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : X → E →L[ℂ] E} {a : X} (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z : X ↦ LinearMap.det (A z : E →ₗ[ℂ] E)) a := by
  let b := Module.finBasis ℂ E
  have hfun : (fun z : X => LinearMap.det (A z : E →ₗ[ℂ] E)) =
      fun z => ∑ σ : Equiv.Perm (Fin (Module.finrank ℂ E)),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, b.repr (A z (b i)) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [LinearMap.toMatrix_apply]
  rw [hfun]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
  exact analyticAt_entry b hA (σ i) i

end GlobalTheory.AnalyticMatrixEntries
