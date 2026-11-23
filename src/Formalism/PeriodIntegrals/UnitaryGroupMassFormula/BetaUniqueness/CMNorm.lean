module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions

namespace PI.UnitaryGroupMassFormula.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cm_norm_eq_one (D : D7) (μ : D.host.E) (h : star μ * μ = 1) (φ : D.host.E →+* ℂ) :
    ‖φ μ‖ = 1 := by
  have hφ := D.sp.cm.cmUnram.2.1 φ μ
  have h1 : φ (star μ) * φ μ = 1 := by rw [← map_mul, h, map_one]
  rw [hφ, Complex.conj_mul'] at h1
  have h2 : ‖φ μ‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : 0 ≤ ‖φ μ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖φ μ‖ - 1), sq_nonneg (‖φ μ‖ + 1)]

end PI.UnitaryGroupMassFormula.BetaLUniq
