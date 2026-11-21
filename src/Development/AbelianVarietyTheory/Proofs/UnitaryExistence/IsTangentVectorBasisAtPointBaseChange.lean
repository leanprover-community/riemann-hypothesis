import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  first | exact @GlobalTheory.Frames.lieBasis_iff_tanBasis | exact GlobalTheory.Frames.lieBasis_iff_tanBasis | (intros; apply GlobalTheory.Frames.lieBasis_iff_tanBasis <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open scoped CategoryTheory.Obj

namespace GlobalTheory.Frames

theorem tanBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), TanBasis x v → TanBasis (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x n v hv
  have := Xo.univ.t.semi.comm
  have := Xo.univ.t.semi.smooth
  have h₁ := isGrpPullback_pullback Xo.univ.t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj Xo.univ.t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj Xo.univ.t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo S x _ _ h₁
  obtain ⟨-, b₃⟩ := GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo T _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv.1 i)
  have hb : IsLieBasis u := (b₁ n u).2 (by rw [funext hu]; exact hv)
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd Xo.univ.t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  convert key using 2 with i
  rw [← Category.assoc, hu', e, Category.assoc, hu]

end GlobalTheory.Frames
end
end
