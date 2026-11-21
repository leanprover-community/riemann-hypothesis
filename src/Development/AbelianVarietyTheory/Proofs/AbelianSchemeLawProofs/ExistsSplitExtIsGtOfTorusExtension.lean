import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B], IsAbelianScheme B → ∀ (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∃ (O : X → RigLB B) (h₁ : _) (h₂ : _) (h₃ : _), ∀ hB : IsAbelianScheme B, ∃ d : (SplitExt.mk B hB X O h₁ h₂ h₃).GtDatum G, d.q = q ∧ d.i = i := by
  first | exact @GlobalTheory.exists_gtDatum_of_splitTorus_extension | exact GlobalTheory.exists_gtDatum_of_splitTorus_extension | (intros; apply GlobalTheory.exists_gtDatum_of_splitTorus_extension <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_splitExt_isGt_of_torusExtension :
    ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → ∃ E : SplitExt (Spec (CommRingCat.of K)), E.IsGt G := by
  intro K _ G _ _ ⟨T⟩
  let _ := T.addCommGroup
  let _ := T.free
  let _ := T.finite
  let _ := T.grpB
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension (Spec (CommRingCat.of K)) T.X G T.B T.isAbelian T.q T.i
    T.q_hom T.i_hom T.q_flat T.q_surjective T.q_quasiCompact T.isKernel
  obtain ⟨d, -, -⟩ := h T.isAbelian
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory
end
