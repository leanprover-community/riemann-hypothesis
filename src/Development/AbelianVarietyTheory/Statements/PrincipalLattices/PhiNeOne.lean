import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.CM.ExStModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => rfl, fun f => ⟨0, by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := by
    have hs : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) := inferInstance
    refine ⟨0, fun x => Subsingleton.elim _ _, fun x y => by simp, fun x hx => absurd (Subsingleton.elim _ _) hx, ?_⟩
    intro a A t _ ht
    rw [Subsingleton.elim A 0, ht]
    simp

theorem unit_comp {S S' T : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (s : T ⟶ S')
    (s₀ : T ⟶ S) (h : s ≫ f = s₀) :
    (1 : Over.mk s ⟶ t'.G).left ≫ m.φ = (1 : Over.mk s₀ ⟶ t.G).left := by
  subst h
  have e1 : (1 : Over.mk s ⟶ t'.G).left = s ≫ eSec t'.G := by
    rw [Hom.one_def]; simp [eSec]
  have e2 : (1 : Over.mk (s ≫ f) ⟶ t.G).left = (s ≫ f) ≫ eSec t.G := by
    rw [Hom.one_def]; simp [eSec]
  have e3 := m.cm.e_comm
  rw [m.base] at e3
  rw [e1, e2]
  simp only [Category.assoc]
  exact congrArg (s ≫ ·) e3




end GlobalTheory.CM.ExStModel
end
