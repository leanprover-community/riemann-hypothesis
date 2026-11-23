module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMu
public import Mathlib.RingTheory.TotallySplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuP
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def BetaSym : Prop := ∀ {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)), betaI X x y = betaI X y x


open Classical in
def MatND : Prop := ∀ {D : D7} (X : HidaSetting D), (matI X).det ≠ 0

section
variable {D : D7} (X : HidaSetting D)


def Alin : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm : (KapI X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) ∘ₗ
    Matrix.toLin' (matI X) ∘ₗ
    ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm.symm : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] (KapI X → ℝ))

theorem det_Alin : LinearMap.det (Alin X) = (matI X).det := by
  rw [Alin, LinearMap.det_conj, LinearMap.det_toLin']

theorem inner_Alin (x y : EuclideanSpace ℝ (KapI X)) : ⟪x, Alin X y⟫ = betaI X x y := by
  classical
  rw [betaI_expand]
  simp only [Alin, PiLp.inner_apply, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe]
  simp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  have hy : ∀ j, (EuclideanSpace.equiv (KapI X) ℝ) y j = y j := fun j => rfl
  simp only [hy]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end


end PI.AprimeInfW
