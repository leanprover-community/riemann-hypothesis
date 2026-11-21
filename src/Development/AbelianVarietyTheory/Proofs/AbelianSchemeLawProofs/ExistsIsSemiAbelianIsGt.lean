import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GeneratorSchemeProperties
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGrpObjSplitExtensionOfGenerators
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_grpObj_splitExtension_of_generators : GlobalFnsSt → ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Scheme.{0}) (q : G ⟶ E.B.left), letI := E.free; letI := E.finite; let B := E.B.left; let N := fun k => (E.O (E.basis k)).L; ∀ (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), ((∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val) → IsAffineHom q → Flat q → Surjective q → ∃ (_ : GrpObj (Over.mk (q ≫ E.B.hom))), IsCommMonObj (Over.mk (q ≫ E.B.hom)) ∧ ∃ d : E.GtDatum (Over.mk (q ≫ E.B.hom)), d.q.left = q := by
  first | exact @GlobalTheory.exists_grpObj_gtDatum_of_generators | exact GlobalTheory.exists_grpObj_gtDatum_of_generators | (intros; apply GlobalTheory.exists_grpObj_gtDatum_of_generators <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isSemiAbelian_isGt :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (E : SplitExt S),
      ∃ (G : Over S) (_ : GrpObj G), IsSemiAbelian G ∧ E.IsGt G := by
  intro hG S E
  letI := E.free
  letI := E.finite
  have hN : ∀ k, (E.O (E.basis k)).L.IsLB := fun k => (E.O (E.basis k)).isLB
  obtain ⟨G, q, u, hu⟩ := exists_generatorScheme E.B.left _ (fun k => (E.O (E.basis k)).L) hN
  obtain ⟨h₁, h₂, h₃, -, -⟩ :=
    generatorScheme_properties E.B.left _ (fun k => (E.O (E.basis k)).L) hN G q u hu
  obtain ⟨inst, hc, d, -⟩ := GlobalTheory.T.exists_grpObj_splitExtension_of_generators hG S E G q u hu h₁ inferInstance h₃
  exact ⟨Over.mk (q ≫ E.B.hom), inst, isSemiAbelian_of_isGt S E _ ⟨d⟩, ⟨d⟩⟩

end GlobalTheory
end
