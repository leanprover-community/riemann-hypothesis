module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain Rat.HeightOneSpectrum

theorem exists_finset_forall_prime_awayP_padic :
    ∀ (p : ℕ) [Fact p.Prime] (P : AwayP p → Prop), (∀ᶠ w in Filter.cofinite, P w) →
    ∃ S : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ w : AwayP p, P w ∧ Nonempty (w.1.adicCompletion ℚ ≃+* ℚ_[ℓ]) := by
  intro p _ P hP
  have hfin : {w : AwayP p | ¬ P w}.Finite := hP
  refine ⟨insert p (hfin.toFinset.image fun w => ((primesEquiv (R := ℤ) w.1 : Nat.Primes) : ℕ)), ?_⟩
  intro ℓ hℓ hS
  have hℓp : ℓ ≠ p := fun h => hS (by simp [h])
  let q : Nat.Primes := ⟨ℓ, hℓ.out⟩
  let v : HeightOneSpectrum ℤ := (primesEquiv (R := ℤ)).symm q
  have hv : ((primesEquiv (R := ℤ) v : Nat.Primes) : ℕ) = ℓ := by
    show ((primesEquiv (R := ℤ) ((primesEquiv (R := ℤ)).symm q) : Nat.Primes) : ℕ) = ℓ
    rw [Equiv.apply_symm_apply]
  have hne : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have h1 := span_natGenerator (R := ℤ) v
    have h2 : natGenerator v = ℓ := hv
    rw [h, h2, Ideal.map_span] at h1
    simp only [Set.image_singleton, map_natCast] at h1
    have h3 : (ℓ : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (p : ℤ) ∣ (ℓ : ℤ) := Ideal.mem_span_singleton.1 (h1.symm ▸ Ideal.mem_span_singleton_self _)
    exact hℓp (Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h3) (Int.natCast_dvd_natCast.1 h4))
  refine ⟨⟨v, hne⟩, ?_, ?_⟩
  · by_contra hw
    apply hS
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨v, hne⟩, hfin.mem_toFinset.2 hw, hv⟩)
  · exact ⟨((Padic.adicCompletionEquiv ℤ q).symm : _ ≃+* ℚ_[(q : ℕ)])⟩

end GlobalTheory.FinClsLoc
