module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.NumberTheory.NumberField.ClassNumber
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

structure HostSz {R : Ranks} (H : Formalism.BasicNotions.Host R) (L : ℝ) : Prop where
  rank : 62 ≤ R.r
  len : 4 ≤ L
  deg : Real.log R.f ≤ L
  g : ∀ i, Real.log (H.g i) ≤ 9 * L + 1
  p : Real.log H.pde ≤ L ∧ Real.log H.pde' ≤ L
  rd : Real.log |((discr H.E : ℤ) : ℝ)| / (2 * R.f) ≤ 2 * L

def poR (R : Ranks) (L : ℝ) : ℝ := 19 * (R.f : ℝ) * (R.r : ℝ) ^ 2 * L + 198 * (R.f : ℝ) ^ 2 * L

def xiOrd {R : Ranks} (H : Formalism.BasicNotions.Host R) (N : ℕ) : ℕ :=
  2 * classNumber H.E * Nat.card (𝓞 H.E ⧸ Ideal.span {(N : 𝓞 H.E)})ˣ

def JointQ (D : D7) : Prop :=
  FieldOK0 D D.host.pde ∧ FieldOK0 D D.host.pde' ∧ (∃ xi, XiOK D D.host.pde xi) ∧ (∃ xi, XiOK D D.host.pde' xi) ∧
    ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

end GlobalTheory.FieldSize
