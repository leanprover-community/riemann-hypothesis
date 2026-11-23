module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.L2.Pj IsDedekindDomain

theorem vV_alg_nonneg (T : CDVR) (r : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
  unfold vV valV
  have h := HeightOneSpectrum.valuation_le_one (K := T.Fr) (IsDiscreteValuationRing.maximalIdeal T.V) r
  generalize (HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
    ((algebraMap T.V T.Fr) r) = x at h ⊢
  induction x using WithZero.recZeroCoe with
  | zero => simp
  | coe a =>
    have ha : a ≤ 1 := WithZero.coe_le_one.mp h
    have hl : (↑a : WithZero (Multiplicative ℤ)).log = Multiplicative.toAdd a := by
      simp [WithZero.log]
    rw [hl]
    have h2 : Multiplicative.toAdd a ≤ 0 := ha
    omega

variable {T T' : CDVR} (iT : T.Fr →+* T'.Fr) {e' : ℕ}
  (hv : ∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a)


end ReciprocityTheory.ChartRestriction.G.PullbackSections
