module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.Published

open NumberField GlobalTheory.FieldSize

def WeberRayFieldSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra K ℂ], Module.finrank ℚ K = 2 → discr K < -4 →
    ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) → ∀ n : ℕ, 0 < n →
      ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n)))
        (_ : IsAbelianGalois K (IntermediateField.adjoin K (weberSet L n))),
        IsRay (IntermediateField.adjoin K (weberSet L n)) (Ideal.span {(n : 𝓞 K)})

end GlobalTheory.Published
