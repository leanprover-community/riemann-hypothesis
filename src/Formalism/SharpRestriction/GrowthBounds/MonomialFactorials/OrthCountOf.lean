module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

def OrthBasisLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∃ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) ∧ LinearIndependent ℤ_[p] f ∧
      Submodule.span ℤ_[p] (Set.range f) = L ∧ ∀ a b, a ≠ b → B (f a) (f b) = 0

def OrthCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∀ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) → LinearIndependent ℤ_[p] f →
      Submodule.span ℤ_[p] (Set.range f) = L → (∀ a b, a ≠ b → B (f a) (f b) = 0) →
      ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial σ ℚ_[p]), (∀ a, e a ∈ L) ∧ LinearIndependent ℤ_[p] e ∧
        (∀ a b, a ≠ b → B (e a) (e b) = 0) ∧ (∀ a, B (e a) (e a) ≠ 0 ∧ (B (e a) (e a)).valuation ≤ D) ∧
        n₁ ≤ Module.finrank ℤ_[p] L ∧ Module.finrank ℤ_[p] L ≤ n₁ + Formalism.GM.M.bad p B L D


open Classical in
def GoodLeSmall : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∀ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) → LinearIndependent ℤ_[p] f →
      Submodule.span ℤ_[p] (Set.range f) = L → (∀ a b, a ≠ b → B (f a) (f b) = 0) →
      Formalism.GM.M.goodCount p B L D ≤
        (Finset.univ.filter (fun a : Fin m => B (f a) (f a) ≠ 0 ∧ (B (f a) (f a)).valuation ≤ D)).card

open Classical in
theorem orthCount_of (h : GoodLeSmall) : OrthCount := by
  intro p _ σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth
  have hgood := h p σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth
  have hrank : Module.finrank ℤ_[p] L = m := by
    rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]
  set S := Finset.univ.filter
    (fun a : Fin m => B (f a) (f a) ≠ 0 ∧ (B (f a) (f a)).valuation ≤ D) with hS
  refine ⟨S.card, fun a => f (S.orderEmbOfFin rfl a), fun a => hfL _,
    hli.comp _ (S.orderEmbOfFin rfl).injective, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact horth _ _ (fun h' => hab ((S.orderEmbOfFin rfl).injective h'))
  · intro a
    have hmem := S.orderEmbOfFin_mem rfl a
    exact (Finset.mem_filter.mp hmem).2
  · rw [hrank]
    exact (Finset.card_le_univ S).trans (le_of_eq (Fintype.card_fin m))
  · unfold Formalism.GM.M.bad
    rw [hrank]
    omega

theorem orthLat_of (h1 : OrthBasisLat) (h2 : OrthCount) : OrthLat := by
  intro p _ σ B L W D hp2 hW hLW hfg hsm hadd hsym
  obtain ⟨m, f, hfL, hli, hspan, horth⟩ := h1 p σ B L W hp2 hW hLW hfg hsm hadd hsym
  exact h2 p σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth

end Formalism.MainNotions.G.SymmetricFormBlocks

end

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem orthLat_of' (h1 : OrthBasisLat) (h2 : GoodLeSmall) : OrthLat := orthLat_of h1 (orthCount_of h2)

end Formalism.MainNotions.G.SymmetricFormBlocks
