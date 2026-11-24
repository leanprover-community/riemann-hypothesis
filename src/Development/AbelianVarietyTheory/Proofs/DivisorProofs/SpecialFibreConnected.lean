module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

namespace GlobalTheory.SpecialConn

theorem range_spec_map_eq {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] [Nontrivial S] (φ : O →+* S)
    (hφ : ∀ Q : Ideal S, Q.IsPrime → IsLocalRing.maximalIdeal O ≤ Q.comap φ) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) = {IsLocalRing.closedPoint O} := by
  have key : ∀ Q : PrimeSpectrum S, Spec.map (CommRingCat.ofHom φ) Q = IsLocalRing.closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap φ = IsLocalRing.maximalIdeal O
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap φ).ne_top) (hφ _ Q.2)
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal S
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem range_thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (Spec.map (CommRingCat.ofHom (thickQ O n))) = {IsLocalRing.closedPoint O} := by
  haveI : Nontrivial (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  refine range_spec_map_eq _ fun Q hQ => ?_
  have h : IsLocalRing.maximalIdeal O ^ (n + 1) ≤ Q.comap (thickQ O n) := fun a ha => by
    change Ideal.Quotient.mk _ a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.zero_mem
  exact (Ideal.IsPrime.comap (thickQ O n)).le_of_pow_le h

theorem range_residue (O : Type) [CommRing O] [IsLocalRing O] :
    Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = {IsLocalRing.closedPoint O} := by
  refine range_spec_map_eq _ fun Q hQ a ha => ?_
  change IsLocalRing.residue O a ∈ Q
  rw [(IsLocalRing.residue_eq_zero_iff a).2 ha]
  exact Q.zero_mem

end GlobalTheory.SpecialConn
