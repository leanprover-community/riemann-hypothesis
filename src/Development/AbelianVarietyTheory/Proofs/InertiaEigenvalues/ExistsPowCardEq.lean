module

public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.RingTheory.Algebraic.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

@[expose] public section

namespace GlobalTheory.CardinalPower

open IntermediateField

theorem exists_pow_card_eq {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : Gal(L/K)) (X : Finset L) :
    ∃ i : ℕ, ∀ x ∈ X, (σ : L → L) x = x ^ Fintype.card K ^ i := by
  classical
  let M : IntermediateField K L := adjoin K (X : Set L)
  haveI : FiniteDimensional K M :=
    finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : Finite M := Module.finite_of_finite K
  haveI : Normal K M := inferInstance
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K M).2 (σ.restrictNormal M)
  refine ⟨n.1, fun x hx => ?_⟩
  have hxM : x ∈ M := subset_adjoin K _ hx
  have h1 := AlgEquiv.restrictNormal_commutes σ M ⟨x, hxM⟩
  rw [← hn] at h1
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate] at h1
  simpa using h1.symm

end GlobalTheory.CardinalPower
