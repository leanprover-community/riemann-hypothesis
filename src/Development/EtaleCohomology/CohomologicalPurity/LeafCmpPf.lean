module

public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
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

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

def LeafCmpNb : Prop := ∀ (X : Scheme.{0}) (B B₀ : Type) [CommRing B] [CommRing B₀] (w : Spec (CommRingCat.of B) ⟶ X)
  (w₀ : Spec (CommRingCat.of B₀) ⟶ X), IsOpenImmersion w₀ → ∀ y, w y ∈ Set.range w₀ →
  ∃ (C : Type) (_ : CommRing C) (φ : B →+* C) (ψ : B₀ →+* C),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ y ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) ∧
    Spec.map (CommRingCat.ofHom φ) ≫ w = Spec.map (CommRingCat.ofHom ψ) ≫ w₀

def LeafCmpId : Prop := ∀ (d : ℕ) (P : SP d) (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C),
  Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w → F.I.map φ = F₀.I.map ψ

theorem spec_comp_ofHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

theorem LeafCmp_of (hMat : LeafMat) (hNb : LeafCmpNb) (hId : LeafCmpId) : LeafCmp := by
  intro d P F F₀ h₀ y hy
  obtain ⟨C, _, φ, ψ, ho, ⟨z, rfl⟩, e⟩ := hNb P.X F.B F₀.B F.w F₀.w h₀ y hy
  have hI := hId d P F F₀ C φ ψ e
  obtain ⟨M, hdet, hM⟩ := hMat d C (ψ ∘ F₀.x) (φ ∘ F.x)
    (by rw [span_comp, span_comp, F.hx, F₀.hx, hI]) z
  let g : C := M.det
  let l : C →+* Localization.Away g := algebraMap C (Localization.Away g)
  have hl : IsOpenImmersion (Spec.map (CommRingCat.ofHom l)) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of C) g
  refine ⟨Localization.Away g, inferInstance, l.comp φ, l.comp ψ, M.map l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec_comp_ofHom φ l]; infer_instance
  · have hr : z ∈ Set.range (PrimeSpectrum.comap l) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact hdet
    obtain ⟨z', hz'⟩ := hr
    refine ⟨show Spec (CommRingCat.of (Localization.Away g)) from z', ?_⟩
    rw [spec_comp_ofHom φ l]
    show (Spec.map (CommRingCat.ofHom φ)) ((Spec.map (CommRingCat.ofHom l)) z') = _
    exact congrArg (Spec.map (CommRingCat.ofHom φ)) hz'
  · rw [spec_comp_ofHom φ l, spec_comp_ofHom ψ l, Category.assoc, Category.assoc, e]
  · rw [← Ideal.map_map, ← Ideal.map_map, hI]
  · change IsUnit (l.mapMatrix M).det
    rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit g
  · funext j
    change l (φ (F.x j)) = _
    rw [show φ (F.x j) = (φ ∘ F.x) j from rfl, hM, RingHom.map_mulVec]
    rfl

end LateralTheory.CohomologicalPurity.Cl
