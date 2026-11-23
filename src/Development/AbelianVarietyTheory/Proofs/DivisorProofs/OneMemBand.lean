module

public import GroundTheory.AutomorphicForms.ReductionCore
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def absDetA (g : GA E a) : ℝ :=
  GroundTheory.Automorphic.Reduction.adeleAbs ((Matrix.GeneralLinearGroup.det g : (Ad E)ˣ) : Ad E)

theorem absDetA_pos (g : GA E a) : 0 < absDetA g := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det g)]
  exact ((GroundTheory.Global.IdeleGroup.ideleModule E) (Matrix.GeneralLinearGroup.det g)).2

theorem absDetA_one : absDetA (1 : GA E a) = 1 := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det (1 : GA E a)), map_one, map_one]
  rfl


variable (E a) in
def band : Set (GA E a) := {g | 1 ≤ absDetA g ∧ absDetA g ≤ 2}

theorem one_mem_band : (1 : GA E a) ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_one]; norm_num

end GlobalTheory.HCF

end
