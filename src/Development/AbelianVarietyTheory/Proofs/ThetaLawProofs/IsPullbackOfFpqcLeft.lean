module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.CategoryTheory.MorphismProperty.Descent

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isGrpPullback_of_fpqc (S S' S'' : Scheme.{0}) (a : S' ⟶ S) (π : S'' ⟶ S') (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (G'' : Over S'') [GrpObj G''] (φ : G''.left ⟶ G'.left) (ψ : G'.left ⟶ G.left)
    (hf : Flat π) (hs : Surjective π) (hq : QuasiCompact π) (h₁ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' π φ)
    (h₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G (π ≫ a) (φ ≫ ψ)) (w : ψ ≫ G.hom = G'.hom ≫ a) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G a ψ := by
  refine ⟨?_, ?_⟩
  · let c : G'.left ⟶ pullback G.hom a := pullback.lift ψ G'.hom w
    have hc₁ : c ≫ pullback.fst G.hom a = ψ := pullback.lift_fst _ _ _
    have hc₂ : c ≫ pullback.snd G.hom a = G'.hom := pullback.lift_snd _ _ _
    have hlow : IsPullback (φ ≫ c) G''.hom (pullback.snd G.hom a) π :=
      (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback G.hom a)
        (by rw [Category.assoc, hc₂, h₁.1.w])).1 (by rw [Category.assoc, hc₁]; exact h₂.1)
    have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (φ ≫ c) :=
      ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hlow.flip hs,
        MorphismProperty.of_isPullback (P := @Flat) hlow.flip hf⟩,
        MorphismProperty.of_isPullback (P := @QuasiCompact) hlow.flip hq⟩
    have hsq : IsPullback (𝟙 G''.left) φ (φ ≫ c) c :=
      ((IsPullback.paste_vert_iff (h₁₁ := φ) (v₁₁ := 𝟙 _) (v₁₂ := c) hlow (by simp)).1
        (by rw [Category.id_comp, hc₂]; exact h₁.1)).flip
    have hc : IsIso c :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms _)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq hcov (inferInstanceAs (IsIso (𝟙 G''.left)))
    exact IsPullback.of_iso (IsPullback.of_hasPullback G.hom a) (asIso c).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [IsIso.eq_inv_comp, hc₁]) (by simp [IsIso.eq_inv_comp, hc₂])
      (by simp) (by simp)
  · intro T x y x₀ y₀ hx hy
    haveI := hf
    haveI := hs
    let p : pullback T.hom π ⟶ T.left := pullback.fst T.hom π
    haveI : Epi p := Flat.epi_of_flat_of_surjective _
    let T'' : Over S'' := Over.mk (pullback.snd T.hom π)
    let q : Over.mk (T''.hom ≫ π) ⟶ T := Over.homMk p (by simp [p, T'', pullback.condition])
    let q₀ : Over.mk (T''.hom ≫ π ≫ a) ⟶ Over.mk (T.hom ≫ a) :=
      Over.homMk p (by simp [p, T'', pullback.condition_assoc])
    let x'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ x.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    let y'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ y.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    have hx'' : x''.left ≫ φ = p ≫ x.left := by simp [x'']
    have hy'' : y''.left ≫ φ = p ≫ y.left := by simp [y'']
    have k₁ := h₁.2 T'' x'' y'' (q ≫ x) (q ≫ y) (by simp [q, hx'']) (by simp [q, hy''])
    have k₂ := h₂.2 T'' x'' y'' (q₀ ≫ x₀) (q₀ ≫ y₀)
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hx, reassoc_of% hx''])
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hy, reassoc_of% hy''])
    rw [← cancel_epi p]
    calc p ≫ (x₀ * y₀).left = (q₀ ≫ (x₀ * y₀)).left := by simp [q₀]
      _ = ((q₀ ≫ x₀) * (q₀ ≫ y₀)).left := by rw [comp_mul]
      _ = (x'' * y'').left ≫ φ ≫ ψ := k₂
      _ = ((q ≫ x) * (q ≫ y)).left ≫ ψ := by rw [k₁, Category.assoc]
      _ = (q ≫ (x * y)).left ≫ ψ := by rw [comp_mul]
      _ = p ≫ (x * y).left ≫ ψ := by simp [q]

end GlobalTheory
