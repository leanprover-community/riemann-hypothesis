module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.EtC

namespace GlobalTheory

theorem field_finiteType_algClosed_SH : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B], IsField B → SH B := by
  intro k B _ _ _ _ _ hB
  letI : Field B := hB.toField
  haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  have hbk : Function.Bijective (algebraMap k B) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv k B
    (RingEquiv.ofBijective (algebraMap k B) hbk)
  refine ⟨Field.henselian B, ?_⟩
  have hbij : Function.Bijective (IsLocalRing.residue B) :=
    ⟨(IsLocalRing.residue B).injective, Ideal.Quotient.mk_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField B) :=
    IsAlgClosed.of_ringEquiv B _ (RingEquiv.ofBijective _ hbij)
  exact IsSepClosed.of_isAlgClosed _

end GlobalTheory
