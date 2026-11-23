module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
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
open scoped BigOperators

namespace Formalism.L2.Th1.C

def IsogenyReduce : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (c : ι → K) (al : K), al ≠ 0 →
    (IsogenyFormula e s2 c al ↔
      mvExp ((2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • PowerSeries.rescale al (lam e s2))
        = ∏ P, wpShift e (c P))

def IsogenyIff : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (c : ι → K) (w : ι → PowerSeries K) (al : K), al ≠ 0 →
    IsEndoZ e neg c w al →
    (IsogenyFormula e s2 c al ↔ (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2 = ∑ P, c P)

def IsogenyIffBar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (c0 : K) (w : ι → PowerSeries K) (al albar : K), al ≠ 0 →
    al * albar = (Fintype.card ι : K) + 1 →
    IsEndoZ e neg (fun P => xP P + c0) w al →
    (IsogenyFormula e s2 (fun P => xP P + c0) al ↔
      al * (al - albar) * s2 = ∑ P, (xP P + c0))

end Formalism.L2.Th1.C
