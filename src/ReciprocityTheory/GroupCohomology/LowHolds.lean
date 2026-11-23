module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot

@[expose] public section

namespace ReciprocityTheory.Coh

universe u

theorem low_holds : LowStatement.{u} := by
  intro R _ G _ _ _ M
  refine ⟨fun n => ⟨LowDeg.hEquiv M n, fun x hx => ⟨_, LowDeg.hEquiv_cls M n x hx⟩⟩,
    ⟨LowDeg.cohomZeroEquivContinuous M, fun x hx => LowDeg.cohomZeroEquivContinuous_cls_apply M x hx⟩,
    ⟨LowDeg.h1EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩, ⟨LowDeg.h2EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩⟩

end ReciprocityTheory.Coh
