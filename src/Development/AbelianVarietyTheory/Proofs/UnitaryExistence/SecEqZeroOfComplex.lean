import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_periodSpaces_complexAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  first | exact @GlobalTheory.ConjPermutes.exists_perm | exact GlobalTheory.ConjPermutes.exists_perm | (intros; apply GlobalTheory.ConjPermutes.exists_perm <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autConj_translates_detCharacter_markings : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → (Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → FixesCurve H τ 1 → ∀ π : Fin C.F.n → Fin C.F.n, ConjugationPermutesPeriods C.F τ π → ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, (∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1) → (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) → ∃ κ : ℂˣ, (∃ u : GA D V, κ = xi (Matrix.GeneralLinearGroup.det (finHom V (u)))) ∧ ∀ h γ k h' γ', C.Mark h k γ → C.Mark h' (π k) γ' → xi (Matrix.GeneralLinearGroup.det (finHom V (γ' * h'))) = κ * xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) := by
  first | exact @GlobalTheory.DetTranslate.conj_translates_det | exact GlobalTheory.DetTranslate.conj_translates_det | (intros; apply GlobalTheory.DetTranslate.conj_translates_det <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZeroSection_value_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ), ∀ f ∈ sec Xo c 0 0, ∀ (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((τ : ℂ →+* ℂ).comp σ))), y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x → Formalism.L2.PjFree.toC (evR Xo c f y') = τ (Formalism.L2.PjFree.toC (evR Xo c f y)) := by
  first | exact @GlobalTheory.WeightZeroValue.evR_conj | exact GlobalTheory.WeightZeroValue.evR_conj | (intros; apply GlobalTheory.WeightZeroValue.evR_conj <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.GalTw.CharSec

section General

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sec_eq_zero_of_complex (σ : c.F →+* ℂ) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c}
    (hg : g ∈ sec Xo c a n) (h : ∀ y : FrPt Xo c (CAt σ), evR Xo c g y = 0) : g = 0 := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW := (GlobalTheory.Frames.algebraic_laws hS E H Dw l Xo c).2.2.1
  funext p y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  letI : Algebra c.F ℂ := σ.toAlgebra
  refine GlobalTheory.FiniteOrderRule.eq_zero_of_forall_algHom (K := c.F) (Ω := ℂ) (g p y) ?_
  intro φ
  let φ' : p.R →ₐ[c.F] CAt σ := φ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R (CAt σ) φ' y
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ', y, hz⟩
  have h0 := h z
  unfold evR evalAt at h0
  rw [dif_pos hT, ← hW g hg.1 (CAt σ) p _ φ' _ y _ z hz hT.choose_spec.choose_spec.choose_spec] at h0
  exact h0

theorem conj_value (σ σ' : c.F →+* ℂ) (τ : ℂ ≃+* ℂ) (hσ : σ' = (τ : ℂ →+* ℂ).comp σ) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt σ'))
    (h : y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x) : toC (evR Xo c f y') = τ (toC (evR Xo c f y)) := by
  subst hσ
  exact GlobalTheory.T.weightZeroSection_value_conj_point E H Dw l Xo c σ τ f hf y y' h

theorem exists_conj_point (σ : c.F →+* ℂ) {ta : c.F ≃+* c.F} (hta : Fixes c ta) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a, τ (σ a) = σ (ta a)) (y : FrPt Xo c (CAt σ)) :
    ∃ y₀ : FrPt Xo c (CAt σ), y.x = spMap (τ : ℂ →+* ℂ) ≫ y₀.x ∧
      ∀ f ∈ sec Xo c 0 0, toC (evR Xo c (galRul hta f) y) = τ (toC (evR Xo c f y₀)) := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  let φ : CAt (σ.comp ta.toRingHom) →ₐ[c.F] CAt σ :=
    { toRingHom := (τ.symm : ℂ →+* ℂ)
      commutes' := fun a => by
        show τ.symm (σ (ta a)) = σ a
        rw [← hτ, RingEquiv.symm_apply_apply] }
  let y' : FrPt Xo c (CAt (σ.comp ta.toRingHom)) := twPt hta y
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ φ y'
  have hx : y.x = spMap (τ : ℂ →+* ℂ) ≫ z.x := by
    have h1 : z.x = spMap (τ.symm : ℂ →+* ℂ) ≫ y.x := hz.1
    have h2 : spMap (τ : ℂ →+* ℂ) ≫ spMap (τ.symm : ℂ →+* ℂ) = 𝟙 _ := by
      unfold spMap
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      simp
    rw [h1]
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) h2).trans (Category.id_comp _))).symm
  refine ⟨z, hx, fun f hf => ?_⟩
  have e1 := (((GlobalTheory.T.conjugateSection_values_semilinear E H Dw l Xo c ta hta).1 0 0 f hf).2 (CAt σ) y)
  have e2 := conj_value σ (σ.comp ta.toRingHom) τ (RingHom.ext fun a => (hτ a).symm) hf z y' hx
  rw [e1]
  exact e2

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat GlobalTheory.GalTw

end GlobalTheory.GalTw.CharSec
end
end
