import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

theorem bc_self (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    ∃ l : BC F F, ∀ T b, l.α T b = b :=
  ⟨⟨fun _ => RingHom.id _, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ => ⟨TensorProduct.lid R _, fun b => by simp [TensorProduct.lid_tmul]⟩⟩, fun _ _ => rfl⟩

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_identity : ∀ (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∃ l : BC F F, ∀ T b, l.α T b = b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.bc_self
