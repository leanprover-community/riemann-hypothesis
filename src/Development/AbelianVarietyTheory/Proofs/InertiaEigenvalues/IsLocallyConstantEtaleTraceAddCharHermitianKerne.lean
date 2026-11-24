module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isLocallyConstant_of_isStdChar {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) : IsLocallyConstant (fun t : F => ψ t) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have hs : ‖y - x‖ ≤ 1 := by simpa [dist_eq_norm] using hy
  have : y = x + (y - x) := by abel
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hs, mul_one]

def kerLinF {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : Et F E) (x : A.K) (y' : A.L) : A.L →ₗ[F] F where
  toFun y := Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y * y'))
  map_add' a b := by simp [star_add, add_mul, mul_add, map_add (f := _)]
  map_smul' c a := by
    have hc : star (algebraMap F A.L c) = algebraMap F A.L c := by
      rw [IsScalarTower.algebraMap_apply F A.K A.L]; exact A.star_K _
    have h1 : star (c • a) * y' = (algebraMap F A.K c) • (star a * y') := by
      rw [Algebra.smul_def, star_mul, hc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]; ring
    rw [h1, map_smul, smul_eq_mul, ← mul_assoc, mul_comm x, mul_assoc, ← Algebra.smul_def, map_smul]
    rfl

theorem isLocallyConstant_psiK_kerL (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  have hl := isLocallyConstant_of_isStdChar ψ hψ
  refine ⟨?_, fun x y' => ?_⟩
  · have hc : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hl.comp_continuous hc
  · have hc : Continuous (kerLinF A x y') := IsModuleTopology.continuous_of_linearMap _
    exact hl.comp_continuous hc

end GlobalTheory.JR.Hyp
