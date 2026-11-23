module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IKDiscrete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.WhatContinuous

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

theorem zm_norm {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    |(Col.ob (IR I)).toBasis.det (ZM.Ib hI)| * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) *
      (Col.YB hI hP 1).l2 1 (ZM.zmB hI s) ≤ X.l2 1 s :=
  le_of_eq (ZM.zm_norm_eq hI hP hs).symm

end ReciprocityTheory.ChartRestriction.G.I2
