module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasType_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap f)) (ρ : R) (p q : ℕ), (Function.Injective f → HasType H t.act ρ p q → HasType H t'.act (f ρ) p q) ∧ ((∀ (k : Type) [Field k] (β : R →+* k), Function.Injective β → ∃ β' : R' →+* k, β'.comp f = β ∧ Function.Injective β') → HasType H t'.act (f ρ) p q → HasType H t.act ρ p q) := by
  intro E _ _ _ H R R' _ _ f t t' m ρ p q
  have key : ∀ (k : Type) [Field k] (β' : R' →+* k) (τ : 𝓞 E →+* k) (n : ℕ),
      LieMult t'.act (spMap β') τ n ↔ LieMult t.act (spMap (β'.comp f)) τ n := fun k _ β' τ n => by
    have e : spMap β' ≫ spMap f = spMap (β'.comp f) := (Spec.map_comp _ _).symm
    rw [← e]
    exact LiePull.lieMult_pull _ _ _ t.G t'.G (spMap f) m.cm.F t.act t'.act m.cart m.act k _ τ n
  refine ⟨fun hf h k _ _ β' hβ' τ => ?_, fun hext h k _ _ β hβ τ => ?_⟩
  · rw [key, key]
    exact h k (β'.comp f) (hβ'.comp hf) τ
  · obtain ⟨β', rfl, hβ'⟩ := hext k β hβ
    rw [← key, ← key]
    exact h k β' hβ' τ

end GlobalTheory.CM
