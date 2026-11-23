module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def cOmega (N : ℕ) : ℝ := 1 / (2 ^ (N * (N - 1) / 2) * volU N)

theorem cOmega_pos (N : ℕ) : 0 < cOmega N := by
  have hv : 0 < volU N := by
    unfold volU
    apply Finset.prod_pos
    intro i _
    have hf : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hp : (0 : ℝ) < Real.pi ^ (i + 1) := pow_pos Real.pi_pos _
    exact div_pos (mul_pos two_pos hp) hf
  unfold cOmega
  exact div_pos one_pos (mul_pos (pow_pos two_pos _) hv)

theorem omegaDensity_haarProb (μ : Measure (Formalism.BasicNotions.UpqT N 0)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    Formalism.BasicNotions.OmegaDensity μ (ENNReal.ofReal (cOmega N)) :=
  PolarCoordinateComparison.omegaDensity_main μ

theorem omegaDensity_cd (cd : Formalism.BasicNotions.CDHaar) (N : ℕ) :
    Formalism.BasicNotions.OmegaDensity (cd.cd N 0) (ENNReal.ofReal (cOmega N)) := by
  haveI := cd.haar N 0
  haveI := cd.prob N
  exact omegaDensity_haarProb (cd.cd N 0)

end ReciprocityTheory.ChartRestriction.DS
