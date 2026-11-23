module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem isWeightedHomogeneous_of_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {σ M : Type*} [AddCommMonoid M] {w : σ → M}
    {m : M} {f : MvPolynomial σ R} (hf : IsWeightedHomogeneous w (map φ f) m) :
    IsWeightedHomogeneous w f m := by
  intro d hd
  apply hf
  rw [MvPolynomial.coeff_map]
  intro h0
  exact hd (hφ (h0.trans (map_zero φ).symm))

theorem dualWeylModuleIntRat : DualWeylIntRat := by
  intro r n ν f
  have hφ : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  constructor
  · exact dualWeylModuleMap ℤ ℚ (Int.castRingHom ℚ) r n ν f
  · intro h
    rw [lsat_mem_dualWeyl] at h ⊢
    obtain ⟨hw, hc⟩ := h
    refine ⟨isWeightedHomogeneous_of_map_of_injective hφ hw, ?_⟩
    intro l j hlj
    apply MvPolynomial.map_injective (f := Int.castRingHom ℚ) hφ
    rw [lsat_map_colAddGen, MvPolynomial.map_rename]
    exact hc l j hlj

end Formalism.GradedWeylDivisibility
