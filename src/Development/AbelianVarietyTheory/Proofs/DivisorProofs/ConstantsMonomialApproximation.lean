module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEquivLocPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical

namespace GlobalTheory.FinTrace

noncomputable def dcToOrbit (G : Type) [Group G] (H K : Subgroup G) :
    DoubleCoset.Quotient (H : Set G) (K : Set G) → MulAction.orbitRel.Quotient H (G ⧸ K) :=
  Quotient.lift (fun g : G => (Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) : MulAction.orbitRel.Quotient H (G ⧸ K)))
    (by
      intro a b hab
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
      apply Quotient.sound
      show _ ∈ MulAction.orbit H _
      refine ⟨⟨h⁻¹, H.inv_mem hh⟩, ?_⟩
      show ((h⁻¹ : G) • (QuotientGroup.mk (h * a * k) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using hk)

theorem dcToOrbit_mk (G : Type) [Group G] (H K : Subgroup G) (g : G) :
    dcToOrbit G H K (Quotient.mk _ g) = Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) := rfl

theorem dcToOrbit_bijective (G : Type) [Group G] (H K : Subgroup G) :
    Function.Bijective (dcToOrbit G H K) := by
  constructor
  · intro q₁ q₂ he
    induction q₁ using Quotient.inductionOn with | h a => ?_
    induction q₂ using Quotient.inductionOn with | h b => ?_
    rw [dcToOrbit_mk, dcToOrbit_mk] at he
    obtain ⟨h, hh⟩ := Quotient.exact he
    change ((h : G) • (QuotientGroup.mk b : G ⧸ K)) = _ at hh
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hh
    apply Quotient.sound
    apply DoubleCoset.rel_iff.2
    refine ⟨(h : G)⁻¹, H.inv_mem h.2, ((h * b)⁻¹ * a)⁻¹, K.inv_mem hh, ?_⟩
    group
  · intro o
    induction o using Quotient.inductionOn with | h x => ?_
    induction x using QuotientGroup.induction_on with | H g => ?_
    exact ⟨Quotient.mk _ g, rfl⟩

theorem sum_doubleCoset_eq_sum_orbit : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  intro G _ H K F hF
  let e := Equiv.ofBijective _ (dcToOrbit_bijective G H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have heq : e q = Quotient.mk _ (QuotientGroup.mk (Quotient.out q) : G ⧸ K) := by
    show dcToOrbit G H K q = _
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hrel : MulAction.orbitRel H (G ⧸ K) (Quotient.out (e q)) (QuotientGroup.mk (Quotient.out q)) := by
    apply Quotient.exact
    rw [Quotient.out_eq, heq]
  obtain ⟨h, hh⟩ := hrel
  rw [← hh, hF]
  congr 2
  have h1 := Nat.card_congr (Classical.choice (stabilizer_equiv_locPart G H K (Quotient.out q)))
  rw [← h1]
  exact_mod_cast (Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel (G := H) (a := h • (QuotientGroup.mk (Quotient.out q) : G ⧸ K))
    (b := (QuotientGroup.mk (Quotient.out q) : G ⧸ K)) (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)).toEquiv).symm
end GlobalTheory.FinTrace
