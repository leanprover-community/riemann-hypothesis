module

public import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_bij_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_of_iso (R : Type) [CommRing R] {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (g : E₁' ⟶ E₂')
    (e₁ : E₁ ≅ E₁') (e₂ : E₂ ≅ E₂') (w : f ≫ e₂.hom = e₁.hom ≫ g) (F : Shv R) (h : Eqv R g F) : Eqv R f F := by
  have hf : f = e₁.hom ≫ g ≫ e₂.inv := by rw [← Category.assoc, ← w, Category.assoc, e₂.hom_inv_id, Category.comp_id]
  have hE : ∀ {E E' : Spc} (u : E ⟶ E'), Eqv R u F ↔ ∀ n, Function.Bijective (pull R u F n) := fun _ => Iff.rfl
  rw [hE] at h ⊢
  intro n
  have key : pull R f F n = (pull R e₁.hom F n).comp ((pull R g F n).comp (pull R e₂.inv F n)) := by
    ext x; simp only [hf, pull_comp, AddMonoidHom.comp_apply]
  rw [key]
  exact (pull_bij_of_iso R e₁ F n).comp ((h n).comp (pull_bij_of_iso R e₂.symm F n))

def LeafTailRep : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (φ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : disc.obj ((PR (d + 1) 1 R).obj n) ≅ sch.obj (off (Polynomial A) (I.map Polynomial.C)))
      (e₂ : disc.obj ((PR d 0 R).obj n) ≅ sch.obj (off A I)),
      disc.map ((prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n) ≫ e₂.hom =
        e₁.hom ≫ sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTail_of (hRep : LeafTailRep) (hH : LeafHtpy) : LeafTail := by
  intro hyp q _ d R _ hq i
  obtain ⟨hA1, -, hA3, hA4, -, -, -, -, -, hC4, -, -⟩ := hyp
  apply hA3
  intro n
  obtain ⟨A, _, I, φ, hI, h, e₁, e₂, w⟩ := hRep d R n
  have hqA : IsUnit (q : A) := by simpa using hq.map φ
  exact eqv_of_iso _ _ _ e₁ e₂ w _ (hH hA1 hA4 hC4 q A I hI hqA h i)

end LateralTheory.CohomologicalPurity.Thom
