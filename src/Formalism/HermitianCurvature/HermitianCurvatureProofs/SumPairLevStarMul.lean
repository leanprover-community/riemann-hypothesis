import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelIntegrandAestronglyMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving

section
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Split

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_split (μ : Measure (Mt k r)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (hint : Integrable (fun c' : Cf r l.castSucc =>
      ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c'))) :
    form μ l.castSucc x y c =
      ∫ t : ℂ, ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ x y (Function.update c l t) := by
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hform : form μ l.castSucc x y c = ∫ c', f c' := rfl
  have h1 : ∫ c', f c' = ∫ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) := by
    rw [← hmp.integral_comp' (fun p => f ((coordinateSplit (r := r) l).symm p))]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (x a) (y a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) := by
    have := (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
    exact this
  rw [hform, h1, show (volume : Measure (ℂ × Cf r l.succ)) = volume.prod volume from rfl,
    integral_prod _ hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hval]
  rw [integral_const_mul]
  rfl

end Split

end Formalism.FourierDecayAlt.P5.HerA
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

def pairLev (μ : Measure (Mt k r)) (i : Fin (r + 1)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c')

variable {μ : Measure (Mt k r)} {i : Fin (r + 1)} {U : Submodule ℂ (RadSp k r z z' π π')}

theorem pairLev_swap (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairLev μ i Ψ Φ c = conj (pairLev μ i Φ Ψ c) := by
  unfold pairLev
  rw [← integral_conj]
  congr 1
  funext c'
  rw [pairAt_swap, map_mul, Complex.conj_ofReal]

theorem pairLev_smul_left (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairLev μ i (a • Φ) Ψ c = a * pairLev μ i Φ Ψ c := by
  unfold pairLev
  rw [← integral_const_mul]
  congr 1
  funext c'
  rw [pairAt_smul_left]
  ring

theorem pairLev_smul_right (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairLev μ i Φ (a • Ψ) c = conj a * pairLev μ i Φ Ψ c := by
  unfold pairLev
  rw [← integral_const_mul]
  congr 1
  funext c'
  rw [pairAt_smul_right]
  ring

theorem pairLev_add_left (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Φ' Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΦ' : Φ' ∈ U) (hΨ : Ψ ∈ U) :
    pairLev μ i (Φ + Φ') Ψ c = pairLev μ i Φ Ψ c + pairLev μ i Φ' Ψ c := by
  unfold pairLev
  rw [← integral_add (hI c hc Φ hΦ Ψ hΨ).2 (hI c hc Φ' hΦ' Ψ hΨ).2]
  congr 1
  funext c'
  have := pairAt_add_smul_left μ Φ Φ' Ψ (glue i c c') 1 ((hI c hc Φ hΦ Ψ hΨ).1 c') ((hI c hc Φ' hΦ' Ψ hΨ).1 c')
  rw [one_smul, one_mul] at this
  rw [this, mul_add]

theorem pairLev_add_right (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Ψ Ψ' : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) (hΨ' : Ψ' ∈ U) :
    pairLev μ i Φ (Ψ + Ψ') c = pairLev μ i Φ Ψ c + pairLev μ i Φ Ψ' c := by
  rw [pairLev_swap, pairLev_add_left hI hc hΨ hΨ' hΦ, map_add, ← pairLev_swap, ← pairLev_swap]

theorem pairLev_zero_left (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairLev μ i 0 Ψ c = 0 := by
  unfold pairLev
  have h0 : ∀ c', pairAt μ (0 : RadSp k r z z' π π') Ψ c' = 0 := fun c' => by
    have := pairAt_smul_left μ (0 : RadSp k r z z' π π') Ψ c' 0
    rwa [zero_smul, zero_mul] at this
  simp [h0]



def adjLev (μ : Measure (Mt k r)) (i : Fin (r + 1)) (U : Submodule ℂ (RadSp k r z z' π π')) (hI : IntLevOn μ i U)
    (c : Fin r → ℂ) (hc : c ∈ OmX r) : StarSubalgebra ℂ (Pr (RadSp k r z z' π π')) where
  carrier := {a | (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ (∀ Φ ∈ U, a.2.unop Φ ∈ U) ∧
    ∀ Φ ∈ U, ∀ Ψ ∈ U, pairLev μ i (a.1 Φ) Ψ c = pairLev μ i Φ (a.2.unop Ψ) c}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ), fun Φ hΦ Ψ hΨ => ?_⟩
    change pairLev μ i (a.1 (b.1 Φ)) Ψ c = pairLev μ i Φ (b.2.unop (a.2.unop Ψ)) c
    rw [ha _ (hb1 Φ hΦ) Ψ hΨ, hb Φ hΦ _ (ha2 Ψ hΨ)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ),
      fun Φ hΦ Ψ hΨ => ?_⟩
    change pairLev μ i (a.1 Φ + b.1 Φ) Ψ c = pairLev μ i Φ (a.2.unop Ψ + b.2.unop Ψ) c
    rw [pairLev_add_left hI hc (ha1 Φ hΦ) (hb1 Φ hΦ) hΨ, pairLev_add_right hI hc hΦ (ha2 Ψ hΨ) (hb2 Ψ hΨ),
      ha Φ hΦ Ψ hΨ, hb Φ hΦ Ψ hΨ]
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun Φ _ Ψ _ => ?_⟩
    · rw [pr_alg_fst, Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · rw [pr_alg_snd, Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
    · rw [pr_alg_fst, pr_alg_snd, Module.algebraMap_end_apply, Module.algebraMap_end_apply, pairLev_smul_left,
        pairLev_smul_right, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun Φ hΦ Ψ hΨ => ?_⟩
    change pairLev μ i (a.2.unop Φ) Ψ c = pairLev μ i Φ (a.1 Ψ) c
    rw [pairLev_swap (Φ := Ψ), ← ha Ψ hΨ Φ hΦ, ← pairLev_swap]


theorem act_mem_pres (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ presAlg U)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := U.sum_mem fun b _ => (hM a b).1 _ (hx b)



theorem form_eq_sum (hI : IntLevOn μ i U) {c : Fin r → ℂ} (hc : c ∈ OmX r) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ U) (hv : ∀ a, v a ∈ U) : form μ i u v c = ∑ a, pairLev μ i (u a) (v a) c := by
  unfold form pairLev
  simp only [Finset.mul_sum]
  exact integral_finsetSum _ fun a _ => (hI c hc _ (hu a) _ (hv a)).2



end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]


end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end
