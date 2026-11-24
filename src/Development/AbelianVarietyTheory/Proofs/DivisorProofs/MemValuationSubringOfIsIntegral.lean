module

public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

namespace GlobalTheory.IntegralInValuationSubring

theorem mem_valuationSubring_of_isIntegral {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    [Algebra R Ω] (A : ValuationSubring Ω) (h : ∀ r : R, algebraMap R Ω r ∈ A) {b : Ω}
    (hb : IsIntegral R b) : b ∈ A := by
  let f : R →+* A := (algebraMap R Ω).codRestrict A h
  letI : Algebra R A := f.toAlgebra
  haveI : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hA : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hA
  rw [← hy]
  exact y.2

end GlobalTheory.IntegralInValuationSubring
