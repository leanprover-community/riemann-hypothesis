import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsHaarZetaValueAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

noncomputable section

open scoped NNReal ComplexConjugate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.DblModel

variable {D : D7} {V : HSp D}

theorem const_one_mem_cuspForms_of_anisotropic (h : IsAniso V) (θ : InfF D) (A : CptF V) : (1 : GA D V → ℂ) ∈ Cusp.A0 θ V A :=
  Cusp.mem_cuspForms.2 ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

theorem hypotheses_inhabited (D : D7) (n b : ℕ) :
    ∃ (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (θ : InfF D) (A : CptF V) (m : Measure (GA D V)),
      V.rank = n ∧ IsMaj V a ∧ IsHeckeChar D μ ∧ ResEta D μ b ∧ IsInfFam θ ∧ V.SigOK ∧ Cusp.IsCartanFrame V A ∧
        m.IsHaarMeasure ∧ (1 : GA D V → ℂ) ∈ Cusp.A0 θ V A := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  let V : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  have h1 : IsHeckeChar D (η ^ b) := ⟨by
    have : ((η ^ b : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ b := by funext x; simp
    rw [this]; exact hη.1.1.pow b, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hr := hη.2.2.1
  have h2 : ResEta D (η ^ b) b := ⟨hr.1, fun e he a => by rw [MonoidHom.pow_apply, hr.2 e he a, pow_one]⟩
  obtain ⟨a, ha⟩ := exists_isMaj V
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hV : V.SigOK := Examples₂.posSpace_sigOK _ _
  obtain ⟨A, hA⟩ := Cusp.exists_isCartanFrame V hV
  exact ⟨V, a, _, θ, A, Measure.haar, rfl, ha, h1, h2, hθ, hV, hA, inferInstance,
    const_one_mem_cuspForms_of_anisotropic (ThetaMean.Model.isAniso_posSpace n) θ A⟩

theorem resEta_one (D : D7) (b : ℕ) : ResEta D 1 (2 * b) := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  exact resEta_parity (n := 0) ⟨hη.2.2.1.1, fun _ _ _ => rfl⟩ (by omega)







end GlobalTheory.Eis.DblModel

end
