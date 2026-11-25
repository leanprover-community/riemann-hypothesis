module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_bijective : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  intro R k _ _ σ hσ X s X₀ s₀ ψ w
  let e : R ≃+* k := RingEquiv.ofBijective σ hσ
  let τ : k →+* R := e.symm.toRingHom
  have hστ : ∀ r, σ (τ r) = r := fun r => e.apply_symm_apply r
  have hτσ : ∀ r, τ (σ r) = r := fun r => e.symm_apply_apply r
  have c1 : spMap τ ≫ spMap σ = 𝟙 (Sp R) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    have : τ.comp σ = RingHom.id R := RingHom.ext hτσ
    rw [this]; simp
  have c2 : spMap σ ≫ spMap τ = 𝟙 (Sp k) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    rw [this]; simp
  let l : X ⟶ X₀ := w.lift (𝟙 X) (s ≫ spMap τ) (by rw [Category.id_comp, Category.assoc, c1, Category.comp_id])
  have hl1 : l ≫ ψ = 𝟙 X := w.lift_fst _ _ _
  have hl2 : l ≫ s₀ = s ≫ spMap τ := w.lift_snd _ _ _
  have hl3 : ψ ≫ l = 𝟙 X₀ := by
    apply w.hom_ext
    · rw [Category.assoc, hl1, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hl2, ← Category.assoc, w.w, Category.assoc, c2, Category.comp_id, Category.id_comp]
  obtain ⟨hcomp, -, hid⟩ := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  intro b
  refine ⟨pullHO1 hl2 b, ?_⟩
  have := (hcomp k R X₀ X s₀ s τ l hl2 k X₀ s₀ σ ψ w.w (RingHom.id k) (𝟙 (Over.mk s₀) : Over.mk s₀ ⟶ Over.mk s₀).left
    (ovw (𝟙 (Over.mk s₀))) (by simp [hl3]) (fun r => (hστ r).symm)).1 b
  rw [this]
  exact (hid k (Over.mk s₀)).1 b

end GlobalTheory.AbCoh
