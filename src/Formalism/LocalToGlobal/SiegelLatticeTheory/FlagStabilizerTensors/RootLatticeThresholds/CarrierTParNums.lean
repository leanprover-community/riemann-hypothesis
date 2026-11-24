module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BuiltPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierParts
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

theorem half_lt_int {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : a < b) : a + 1 / 2 ≤ b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : z < n := by
    have : (z : ℚ) < n := by linarith
    exact_mod_cast this
  have : (z : ℚ) + 1 ≤ n := by exact_mod_cast this
  linarith

theorem int_lt_half {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : b < a) : b + 1 / 2 ≤ a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : n ≤ z := by
    have : (n : ℚ) < z + 1 := by linarith
    have : n < z + 1 := by exact_mod_cast this
    omega
  have : (n : ℚ) ≤ z := by exact_mod_cast this
  linarith

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
