module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCechDelta

theorem app_res_nat {X : TopCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (a : Q ⟶ Q₂)
    {A B : Opens X} (h : A ≤ B) (x : Q.obj (op B)) :
    a.app (op A) (res Q h x) = res Q₂ h (a.app (op B) x) := by
  exact NatTrans.naturality_apply a (homOfLE h).op x

theorem push_pullCoch {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {P P₂ : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (a : P ⟶ P₂) (a' : Q ⟶ Q₂) (φ : P ⟶ (Opens.map f).op ⋙ Q) (φ₂ : P₂ ⟶ (Opens.map f).op ⋙ Q₂)
    (h : ∀ W x, φ₂.app W (a.app W x) = a'.app _ (φ.app W x)) (n : ℕ) (σ : Cochain P V n) :
    push U a' n (pullCoch f φ V U τ hτ n σ) = pullCoch f φ₂ V U τ hτ n (push V a n σ) := by
  funext t
  exact (app_res_nat a' _ _).trans (congrArg (res Q₂ _) (h _ _).symm)

end GlobalTheory.CompanionTheory.OmCechDelta
