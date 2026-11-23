module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ramCard :
    ∀ (R D M : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M) (I : Subgroup D) (m0 : M), (∀ g, ρ g = 1) → m0 ≠ 0 → Finite (H1 ρ) →
      ∀ φ₁ ∈ Z1 (Representation.trivial R D R), ∀ φ₂ ∈ Z1 (Representation.trivial R D R), (∀ g ∈ I, φ₁ g = 0) → (∃ g, φ₁ g = 1) → (∃ g ∈ I, φ₂ g = 1) →
      2 * Nat.card M ≤ Nat.card (ramLine ρ I m0) := by
  rintro R D M _ _ _ _ _ _ _ _ _ _ ρ I m0 hρ hm0 _ φ₁ hφ₁ φ₂ hφ₂ hI1 ⟨g1, hg1⟩ ⟨g2, hg2I, hg2⟩
  obtain ⟨c1, a1⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₁
  obtain ⟨c2, a2⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₂
  let fn : R → M → D → M := fun t m g => φ₁ g • m + (t * φ₂ g) • m0
  have hz : ∀ t m, fn t m ∈ Z1 ρ := by
    intro t m
    rw [mem_Z1_iff_cocycle]
    refine ⟨(continuous_of_discreteTopology (f := fun p : R × R => p.1 • m + (t * p.2) • m0)).comp
      (c1.prodMk c2), ?_⟩
    intro g h
    simp [fn, hρ g, a1 g h, a2 g h, add_smul, mul_add] <;> abel
  let F : Bool × M → ramLine ρ I m0 := fun p =>
    ⟨Submodule.Quotient.mk ⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩,
      (mem_ramLine ρ I m0 _).2 ⟨⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩, fun g hg => by
        show fn _ _ g ∈ _
        simp only [fn, hI1 g hg, zero_smul, zero_add]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m0), rfl⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨b, m⟩ ⟨b', m'⟩ h
    have h1 := congrArg Subtype.val h
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at h1
    obtain ⟨x, hx⟩ := h1
    have hpt : ∀ g, fn (if b then 1 else 0) m g = fn (if b' then 1 else 0) m' g := by
      intro g
      have h2 := hx g
      rw [hρ g, Module.End.one_apply, sub_self] at h2
      exact sub_eq_zero.1 h2
    have hb : b = b' := by
      have h3 := hpt g2
      simp only [fn, hI1 g2 hg2I, hg2, zero_smul, zero_add, mul_one] at h3
      cases b <;> cases b' <;> simp_all
    subst hb
    have h4 := hpt g1
    simp only [fn, hg1, one_smul] at h4
    rw [add_right_cancel h4]
  have hc := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hc
  exact hc
