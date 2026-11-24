module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionsTwoComponents
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  show IsLocalRing (genMap ξ p).range
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have e : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have ha : (a : Ω) ≠ 0 := fun h0 => by simp [h0] at e
    refine ⟨ha, a.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right e]
    exact b.2
  · rintro ⟨h0, -, h2⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem unitAt_iff_of_dominated {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'} {q : Cpt ξ}
    (h : (∀ a ∈ regAt ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ q, unitAt ξ' p' (i a) → unitAt ξ q a)
    {a : Ω} (ha : a ∈ regAt ξ q) : unitAt ξ q a ↔ unitAt ξ' p' (i a) := by
  refine ⟨fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 a hu.2.1, ?_⟩, h.2 a ha⟩
  rw [← map_inv₀]
  exact h.1 _ hu.2.2

theorem eq_of_dominated_of_inChart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {i : Ω →+* Ω'} {p' : Cpt ξ'} {c : κ} {q r : Cpt M.ξ} (hq : InChart M.ξ x c q) (hr : InChart M.ξ x c r)
    (dq : (∀ a ∈ regAt M.ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q, unitAt ξ' p' (i a) → unitAt M.ξ q a)
    (dr : (∀ a ∈ regAt M.ξ r, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ r, unitAt ξ' p' (i a) → unitAt M.ξ r a) :
    q = r := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.CompanionTheory.Ar.Centre.Sep.eq_of_dominated_of_inChart <;> assumption

theorem eq_of_dominated : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' q₁ q₂ d₁ d₂
  obtain ⟨c₁, hc₁⟩ := M.tie.cover q₁
  obtain ⟨c₂, hc₂⟩ := M.tie.cover q₂
  have hctr : p' ∈ ctrSet o x i ξ' :=
    ⟨c₁, hc₁.1, fun a ha => d₁.1 a ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ q₁ hc₁).1 a ha)⟩
  obtain ⟨p₀, d₀, -, hp₀⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have e₁ : q₁ = p₀ := eq_of_dominated_of_inChart M hc₁ (hp₀ c₁ hc₁.1 fun j => d₁.1 _ (hc₁.2 j)) d₁ d₀
  have e₂ : q₂ = p₀ := eq_of_dominated_of_inChart M hc₂ (hp₀ c₂ hc₂.1 fun j => d₂.1 _ (hc₂.2 j)) d₂ d₀
  exact e₁.trans e₂.symm

end PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.centre_unique : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ :=
  @PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep.eq_of_dominated
