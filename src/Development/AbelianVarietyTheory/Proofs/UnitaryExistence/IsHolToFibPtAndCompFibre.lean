module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolFibre

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isHolTo_comp {W : Set E} {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ X)} (hc : IsHolTo W c) (ψ : X ⟶ Y) :
    IsHolTo W (fun w => c w ≫ ψ) := GlobalTheory.HolTorsion.isHolTo_comp hc ψ

theorem isHolTo_const {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) :
    IsHolTo W (fun _ => x) := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [h, and_true]
    exact hW
  · simp only [h, and_false, Set.setOf_false, isOpen_empty]

theorem isHolTo_of_isPullback {W : Set E} {S X Y Z : Scheme.{0}}
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)}
    (ha : IsHolTo W (fun w => c w ≫ p)) (hb : IsHolTo W (fun w => c w ≫ q)) : IsHolTo W c := by
  apply GlobalTheory.HolTorsion.isHolTo_of_isPullback <;> assumption

theorem isHolTo_fibPt {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (G : Over X) (y : Sp ℂ ⟶ X)
    (e : E → (Over.mk y ⟶ G)) (he : IsHolTo W (fun z => (e z).left)) :
    IsHolTo W (fun z => fibPt G (e z)) := by
  refine isHolTo_of_isPullback (IsPullback.of_hasPullback G.hom y) ?_ ?_
  · simp only [fibPt, pullback.lift_fst]
    exact he
  · simp only [fibPt, pullback.lift_snd]
    exact isHolTo_const hW _

theorem isHolTo_fibPt_and_comp :
    ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) :=
  fun _ G y _ e he =>
    ⟨isHolTo_fibPt isOpen_univ G y e he, fun _ ψ => isHolTo_comp (isHolTo_fibPt isOpen_univ G y e he) ψ⟩

end GlobalTheory.HolFibre
