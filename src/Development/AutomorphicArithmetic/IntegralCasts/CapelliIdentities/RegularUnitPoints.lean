module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

namespace UpperTheory.Reformulated.B.RegularUnitPoints

theorem aux1 : ∀ {Ω : Type} [inst : Field Ω], IsLocalRing Ω := by
  intro Ω inst
  infer_instance

noncomputable def genPt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec ↧Ω ⟶ X) → ↥X :=
  fun {X} {Ω} [Field Ω] ξ => ξ (IsLocalRing.closedPoint Ω)

noncomputable def Cpt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec ↧Ω ⟶ X) → Type :=
  fun {X} {Ω} [Field Ω] ξ => { p // genPt ξ ⤳ p }

theorem aux4 : ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
  (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) (p : Cpt ξ),
  genPt ξ ⤳ p.val := by
  intro X Ω inst ξ p
  exact p.2

theorem aux5 : ∀ {Ω : Type} [inst : Field Ω], IsLocalRing (CommRingCat.of Ω) := by
  intro Ω inst
  show IsLocalRing Ω
  infer_instance

noncomputable def genMap : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) →
        (p : Cpt ξ) → ↑(X.presheaf.stalk p.val) →+* Ω :=
  fun {X} {Ω} [Field Ω] ξ p =>
    CommRingCat.Hom.hom
      (CategoryTheory.CategoryStruct.comp
        (X.presheaf.stalkSpecializes (aux4 ξ p))
        (AlgebraicGeometry.Scheme.stalkClosedPointTo ξ))

noncomputable def regAt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → Cpt ξ → Subring Ω :=
  fun {X} {Ω} [Field Ω] ξ p => (genMap ξ p).range

noncomputable def unitAt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → Cpt ξ → Ω → Prop :=
  fun {X} {Ω} [Field Ω] ξ p a =>
    a ≠ 0 ∧
      a ∈ regAt ξ p ∧
        a⁻¹ ∈ regAt ξ p

noncomputable def InFibre : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → ℕ → Cpt ξ → Prop :=
  fun {X} {Ω} [Field Ω] ξ p q => ¬unitAt ξ q ↑p

theorem main : ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
  {ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X} {q : Cpt ξ},
  (∀ (r : ℕ), Nat.Prime r → ¬InFibre ξ r q) →
    ∀ (n : ℕ), n ≠ 0 → unitAt ξ q ↑n := by
  intro X Ω inst ξ q hq n hn
  have key : ∀ m : ℕ, m ≠ 0 → unitAt ξ q (m : Ω) := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _
      refine ⟨by simp, ?_, ?_⟩
      · simp [(regAt ξ q).one_mem]
      · simp [(regAt ξ q).one_mem]
    | prime p hp =>
      intro _
      have := hq p hp
      unfold InFibre at this
      exact not_not.mp this
    | mul a b ha hb =>
      intro hab
      have ha0 : a ≠ 0 := by rintro rfl; simp at hab
      have hb0 : b ≠ 0 := by rintro rfl; simp at hab
      obtain ⟨a1, a2, a3⟩ := ha ha0
      obtain ⟨b1, b2, b3⟩ := hb hb0
      refine ⟨?_, ?_, ?_⟩
      · push_cast; exact mul_ne_zero a1 b1
      · push_cast; exact Subring.mul_mem _ a2 b2
      · push_cast; rw [mul_inv]; exact Subring.mul_mem _ a3 b3
  exact key n hn

end UpperTheory.Reformulated.B.RegularUnitPoints
