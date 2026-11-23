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

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def veluXs {K : Type} [Field K] {ι : Type} [Fintype ι] (A : PowerSeries K) (xs : ι → PowerSeries K)
    (xP : ι → K) (r : K) : PowerSeries K :=
  A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) - PowerSeries.C r)

def VeluXFromZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l linv A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al : K),
    IsLogPair l linv → XIsWp e l A c0 → IsEndoZ e neg (fun P => xP P + c0) w al →
    (∀ P, PowerSeries.subst l (w P) = xs P + PowerSeries.C c0) →
    PowerSeries.C (al ^ 2) * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 =
      (mulBy l linv al) ^ 2 * veluXs A xs xP ((al ^ 2 - 1) * c0)

def IsogenyU : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (l linv ph A : PowerSeries K)
    (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    (mulBy l linv al) ^ 2 * mvExp (-((2 : K) • PowerSeries.subst (mulBy l linv al) ph))
        * PowerSeries.X ^ (2 * Fintype.card ι) =
      PowerSeries.C (al ^ 2) * PowerSeries.X ^ (2 * (Fintype.card ι + 1))
        * mvExp (-((2 * ((Fintype.card ι : K) + 1)) • ph))
        * ∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)

def PhNormUnit : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e : PowerSeries K) (s2 : K)
    (l linv ph A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    IsOneUnit R A → (∀ P, xP P ∈ R) → al ∈ R → al⁻¹ ∈ R → al ≠ 0 → (2 : K)⁻¹ ∈ R →
    IntPS R (mulBy l linv al) →
    Cong R (PowerSeries.subst (mulBy l linv al) ph) (((Fintype.card ι : K) + 1) • ph)

end Formalism.L2.Th1.C
