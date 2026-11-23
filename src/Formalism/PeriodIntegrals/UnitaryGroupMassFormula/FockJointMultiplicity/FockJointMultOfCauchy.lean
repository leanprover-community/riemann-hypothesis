module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.IsBlockHighestWeight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.IsDiagonalBlockIndexRightOfPositiveRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.MinDeg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ShapeFromFacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ShapeProdVarMatNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.VarsZeroOfSupported
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory

@[expose] public section

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJM

theorem minHyp_of_mem {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hP : P ∈ JH p q r s μ μ') (h0 : P ≠ 0) : MinHyp p q r s μ μ' P := by
  obtain ⟨⟨d1, hd1, hP1⟩, ⟨d2, hd2, hP2⟩⟩ := PI.FJMF.minimal_degree_joint p q r s μ μ' P hP h0
  have h12 : d1 = d2 :=
    ((mem_homogeneousSubmodule _ _).1 hP1).inj_right ((mem_homogeneousSubmodule _ _).1 hP2) h0
  subst h12
  exact ⟨hP, h0, d1, hd1, hd2, hP1⟩

theorem shapeOf_of_cauchy (hC : CauchyHW) : ShapeOf := by
  intro p q r s μ μ' P hP h0
  have hM := minHyp_of_mem hP h0
  exact shape_from_facts p q r s μ μ'
    (PI.FJMA.line_of hC PI.FJMS.hypothesis_first_cover PI.FJMS.hypothesis_second_cover PI.FJMS.hypothesis_third_cover PI.FJMS.hypothesis_fourth_cover
      PI.FJMS.cover_by_blocks p q r s μ μ' P hM).1
    (PI.FJMS.segs_of hM) (PI.FJMS.intFacts_of hM)

theorem rankLe_of_cauchy (hC : CauchyHW) : RankLe := by
  intro p q r s μ μ' _
  refine ⟨vLine p q r s μ μ', fun P hP => ?_⟩
  by_cases h0 : P = 0
  · rw [h0]; exact Submodule.zero_mem _
  · obtain ⟨c, hc⟩ := (PI.FJMA.line_of hC PI.FJMS.hypothesis_first_cover PI.FJMS.hypothesis_second_cover PI.FJMS.hypothesis_third_cover
      PI.FJMS.hypothesis_fourth_cover PI.FJMS.cover_by_blocks p q r s μ μ' P (minHyp_of_mem hP h0)).2
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by rw [hc, C_mul']⟩

theorem fockJointMult_of_cauchy (hC : CauchyHW) : PI.FockDegreeTwoParts.JointMult := jointMult_of
    (exist_of PI.FJMD.shapeVector_ne_zero (PI.FJMD.vecJ_of jointHarmonicsIffLaplacians) (PI.FJMX.vecHW1_of leftDiagonalActionFormula leftOffDiagonalActionFormula)
      (PI.FJMX.vecHW2_of rightDiagonalActionFormula rightOffDiagonalActionFormula))
    (shapeOf_of_cauchy hC) (rankLe_of_cauchy hC)

end PI.FJM
