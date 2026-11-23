module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
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
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

set_option autoImplicit false
noncomputable section
open IsLocalRing

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms

variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R]

theorem isLocalHom_algebraMap [Module.Finite O R] : IsLocalHom (algebraMap O R) := by
  constructor
  intro a ha
  by_contra hna
  have hmax : (Ideal.comap (algebraMap O R) (maximalIdeal R)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R)
  have heq : Ideal.comap (algebraMap O R) (maximalIdeal R) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  have h1 : a ∈ Ideal.comap (algebraMap O R) (maximalIdeal R) := by
    rw [heq]
    exact hna
  exact ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h1)) ha

end ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
