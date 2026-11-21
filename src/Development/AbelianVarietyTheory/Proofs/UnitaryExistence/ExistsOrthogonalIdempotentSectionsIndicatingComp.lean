import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBiject

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) → (∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((U.un k x).u τ i)) → Function.Bijective ik := by
  first | exact @GlobalTheory.CompBij.ik_bijective | exact GlobalTheory.CompBij.ik_bijective | (intros; apply GlobalTheory.CompBij.ik_bijective <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRead

theorem exists_idempotents_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → FnAlgClosed Xo c → ∃ χ : U.Comp → Rul Xo c, (∀ k, χ k ∈ sec Xo c 0 0) ∧ (∀ k, χ k * χ k = χ k) ∧ (∀ k k', k ≠ k' → χ k * χ k' = 0) ∧ ∑ k, χ k = 1 ∧ ∀ k k' x, x ∈ (U.X k').dom → (k' = k → rdU U (χ k) k' x = 1) ∧ (k' ≠ k → rdU U (χ k) k' x = 0) := by
  intro E _ _ _ H Dw l Xo c σ r U hr hσ hU hF
  obtain ⟨g, e, F, ik, φ, hφ, hP⟩ := hU.2.2.2.2.2
  have hb : Function.Bijective ik := by
    refine GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective E H Dw l Xo c σ r U hr hσ hU g e F ik φ hφ (fun k x => ?_)
    obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hP k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  obtain ⟨χ, h0, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces E H Dw l Xo c σ g _ F hF
  refine ⟨fun k => χ (ik k), fun k => h0 _, fun k => h1 _, fun k k' h => h2 _ _ (fun h' => h (hb.1 h')), ?_, ?_⟩
  · rw [← h3]
    exact hb.sum_comp χ
  · intro k k' x hx
    obtain ⟨Pm, -, hp, hu, -⟩ := hP k' ⟨x, hx⟩
    have hv := h4 (U.un k' ⟨x, hx⟩) (ik k) (ik k') Pm hp hu
    have hr : rdU U (χ (ik k)) k' x = toC (evR Xo c (χ (ik k)) (U.un k' ⟨x, hx⟩)) := dif_pos hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hr, hv, if_pos (congrArg ik h)]
    · rw [hr, hv, if_neg (fun h' => h (hb.1 h'))]

end GlobalTheory.CompRead
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotent_sections_indicating_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → FnAlgClosed Xo c → ∃ χ : U.Comp → Rul Xo c, (∀ k, χ k ∈ sec Xo c 0 0) ∧ (∀ k, χ k * χ k = χ k) ∧ (∀ k k', k ≠ k' → χ k * χ k' = 0) ∧ ∑ k, χ k = 1 ∧ ∀ k k' x, x ∈ (U.X k').dom → (k' = k → rdU U (χ k) k' x = 1) ∧ (k' ≠ k → rdU U (χ k) k' x = 0) := by
  atlas_forward_decl GlobalTheory.CompRead.exists_idempotents_rdU
end
