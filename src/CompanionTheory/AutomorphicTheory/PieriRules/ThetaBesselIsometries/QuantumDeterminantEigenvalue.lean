import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperatorStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionExpandMatrixUnits
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransportStatement

section
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  have key : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * (X * Y) * Q := by
    intro X Y
    calc (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * X * (Q * Q⁻¹) * Y * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (X * Y) * Q := by
          rw [hQQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [key, key, ← Matrix.sub_mul, ← Matrix.mul_sub]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp [Matrix.single_mul_single_same, Matrix.mul_sub, Matrix.sub_mul]
  · subst hbc
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hda, Matrix.mul_sub, Matrix.sub_mul]
  · subst hda
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, Matrix.mul_sub, Matrix.sub_mul]
  · simp [Matrix.single_mul_single_of_ne, hbc, hda]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hR Q hQ
  obtain ⟨hsm, hlinv, hlinY, -, hcomm, -⟩ := Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hzero : ∀ Y : Mx k r, R.dC Y 0 = 0 := by
    intro Y
    have h := hlinv Y 1 0 R.smSub.zero_mem 0 R.smSub.zero_mem
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := by
    intro v hv
    have h := hlinY 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z : Mx k r, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := by
    intro Y Z v hv
    have h := hlinY Z Y (-1) v hv
    rw [neg_one_smul, neg_add_eq_sub, neg_one_smul, neg_add_eq_sub] at h
    exact h
  let Em : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hsm _ v v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) 1 v v.2 w w.2
        simpa using h
      map_smul' := fun c v => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) c v v.2 0 R.smSub.zero_mem
        simpa [hzero] using h }
  have hE : ∀ a b (v : R.smSub), ((Em a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v :=
    fun _ _ _ => rfl
  refine ⟨Em, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have hv : (v : R.H) ∈ R.sm := v.2
  have key := hcomm (Q⁻¹ * Matrix.single a b 1 * Q) (Q⁻¹ * Matrix.single c d 1 * Q) v hv
  rw [conj_single_comm Q hQ a b c d, hsub _ _ _ hv] at key
  split_ifs at key ⊢ <;>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE, LinearMap.zero_apply,
      Submodule.coe_zero, sub_zero, zero_sub, hY0 _ hv] at key ⊢ <;>
    exact key

end GlobalTheory
end Gp91
end

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.smoothVectors_discreteSeries_glModule : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  atlas_forward_decl GlobalTheory.smooth_gl_module
end Gp91
end

section
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliSmooth

lemma entry_conj {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * P') c d = P c a * P' b d := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]
  · simp

theorem qdet_smooth : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  intro hyp k r ε mu R hR Q E hQ hE Y w
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hC := hyp.2.2.1
  obtain ⟨hmu, ⟨Q0, hQ0, hDS⟩, hgp⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC k r ε mu R.H _ ⟨Q0, hQ0⟩ hgp hmu hDS w (hsm w w.2) Y]
  rfl

end GlobalTheory.CapelliSmooth
end Gp91
end

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.quantum_determinant_eigenvalue : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  atlas_forward_decl GlobalTheory.CapelliSmooth.qdet_smooth
end Gp91
end
