import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem asm_contOn_of_ckOn {r : ℕ} {m : ℕ∞} {F : B.Mat k r → E} (hF : B.CkOn m (B.GV k r) F) :
    ContinuousOn F (B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := (hF'.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := B.GV k r)).congr_of_eventuallyEq ?_ (hag g₀ hgU hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgG
  exact hag g hgU' hgG

theorem asm_star_cpt (j ρ : ℕ) (F : B.Mat k (j + ρ) → E) (hFc : B.CkOn ⊤ (B.GV k (j + ρ)) F)
    (R : ℝ) (hR : ∀ g ∈ B.GV k (j + ρ), F g ≠ 0 → B.gN g ≤ R) (χD : ℂ → ℂ) (hχ : U.IsCutC χD) (A₁ : ℝ)
    (hA₁ : 0 ≤ A₁) :
    ∃ B₁, U.Star k j ρ (fun g => χD (U.DjU k j ρ g) • F g) A₁ 0 B₁ ((fun w : ℂ => ‖w‖) '' tsupport χD) := by
  have hχc : Continuous χD := hχ.1.continuous
  have hDc := Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k j ρ
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hχ.2.1
  have hKc : IsCompact (B.GV k (j + ρ) ∩ {g : B.Mat k (j + ρ) | B.gN g ≤ R}) :=
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (j + ρ) R).inter_left (Formalism.FourierDecayAlt.P.unitary_group_closed k (j + ρ)).closed
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn ((asm_contOn_of_ckOn hFc).mono Set.inter_subset_left)
  refine ⟨(max R 0) ^ A₁ * (max Cχ 0 * max CF 0), ⟨?_, ?_, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hFc g₀ hg₀
    refine ⟨W0, fun g => χD (U.DjU k j ρ g) • F' g, hU, hgU, ?_, fun g hg hgG => by simp only [hag g hg hgG]⟩
    exact contDiffOn_zero.2 ((hχc.comp hDc).continuousOn.smul (hF'.continuousOn))
  · intro g _ hne
    refine ⟨U.DjU k j ρ g, subset_tsupport _ (fun h0 => hne ?_), rfl⟩
    simp only [h0, zero_smul]
  · intro u v hu hv hl g hg
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0 hv0
    show B.gN g ^ A₁ * ‖χD (U.DjU k j ρ g) • F g‖ ≤ _
    by_cases h0 : F g = 0
    · rw [h0, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · have hgR := hR g hg h0
      have hg0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
      refine mul_le_mul (Real.rpow_le_rpow hg0 (hgR.trans (le_max_left _ _)) hA₁) ?_ (norm_nonneg _)
        (Real.rpow_nonneg (le_max_right _ _) _)
      rw [norm_smul]
      exact mul_le_mul ((hCχ _).trans (le_max_left _ _)) ((hCF g ⟨hg, hgR⟩).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)

theorem asm_gInt_int (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ) (hd : ∀ i, d i ≠ 0) (ht : t ≠ 0)
    (z z' : Fin (2 * (ph + (0 + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (0 + 1) + ρ) → E)
    (hFc : B.CkOn ⊤ (B.GV k (ph + (0 + 1) + ρ)) F) (R : ℝ)
    (hR : ∀ g ∈ B.GV k (ph + (0 + 1) + ρ), F g ≠ 0 → B.gN g ≤ R) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) := by
  have hw : (G.wMat (0 + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (0 + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (0 + 1) * (G.wMat (0 + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc₀
  have hR0 : (0 : ℝ) ≤ ((ph + (0 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA₁ : (0 : ℝ) ≤ 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
      (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) := by positivity
  obtain ⟨B₁, hStar⟩ := asm_star_cpt (ph + (0 + 1)) ρ F hFc R hR χD hχD _ hA₁
  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    have := norm_pos_iff.mpr hc₀
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
        (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) /
        (8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1)) := by
    rw [mul_div_cancel_left₀ _ (by positivity)]
    linarith
  have h1 := Formalism.FourierDecayAlt.P.JCTx6.Int.intG k ph 0 ρ σ d t hd ht _ hK hK0 0 _ hthr z z' E _ B₁ hStar γ hγ
  have e : Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ =
      Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' (fun g => χD (U.DjU k (ph + (0 + 1)) ρ g) • F g) γ := by
    funext y
    have hdet : G.detM (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) = t ^ (0 + 1) * (G.wMat (0 + 1)).det :=
      Formalism.FourierDecayAlt.P.JCTx6.Pos.detM_Zv 0 t y.2.2
    have hD : U.DjU k (ph + (0 + 1)) ρ (U.gaXi (p := ph) (s := 0 + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) γ) = c₀ := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hdet]
    simp only [Formalism.FourierDecayAlt.P.JCTx6.gInt]
    rw [hD, hχD1 c₀ (by rw [dist_self]; positivity), one_smul]
  rw [e]; exact h1

theorem integrable_unipotent_rank_one (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (c : ℂ)
    (z z' : Fin (2 * (ph + 1 + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + 1 + ρ) → E) (γ : B.Mat k ρ)
    (h : Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d c z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ)) :
    Integrable (fun ξ : U.Xi k ph 1 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ))
      (U.muXi k ph 1 ρ σ) := by
  have hE : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  let v₀ : G.UT (0 + 1) → ℂ := fun q => isEmptyElim q
  have hvol : (volume : Measure (G.UT (0 + 1) → ℂ)) = Measure.dirac v₀ := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  have a1 : SigmaFinite (volume : Measure (Fin (0 + 1) → Fin ph → ℂ)) := inferInstance
  have a2 : SigmaFinite (volume : Measure (Fin ph → Fin (0 + 1) → ℂ)) := inferInstance
  have a3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
  have b1 : SigmaFinite (volume : Measure ((Fin (0 + 1) → Fin ph → ℂ) × (Fin ph → Fin (0 + 1) → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b2 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : SigmaFinite (volume : Measure (U.XiH ph (0 + 1) σ)) := by
    haveI := b1; haveI := b2
    rw [Measure.volume_eq_prod]; infer_instance
  have b4 : SigmaFinite (U.muXiH ph (0 + 1) σ) := by unfold U.muXiH; exact b3
  have hg : MeasurePreserving (fun b : U.XiH ph (0 + 1) σ => (b, v₀)) volume
      ((volume : Measure (U.XiH ph (0 + 1) σ)).prod (volume : Measure (G.UT (0 + 1) → ℂ))) := by
    rw [hvol]
    exact ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SL.sigma_RC k (ph + (0 + 1)) ρ
  have hφ : MeasurePreserving (Prod.map (id : U.RC k (ph + (0 + 1)) ρ × U.RC k (ph + (0 + 1)) ρ → _)
      (fun b : U.XiH ph (0 + 1) σ => (b, v₀))) (U.muXi k ph 1 ρ σ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) :=
    (MeasurePreserving.id _).prod hg
  have h2 := (hφ.integrable_comp h.aestronglyMeasurable).2 h
  refine h2.congr (ae_of_all _ fun ξ => ?_)
  have hs : G.superSum (G.upper v₀) = 0 := by simp [G.superSum]
  have hZ : (Matrix.of.symm (c • G.wMat (0 + 1) * G.upper v₀) : G.Mat (0 + 1)) = fun _ _ => c := by
    funext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  simp only [Function.comp_apply, Prod.map, id, Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]
  simp [G.psi]

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem point_size_append_single (h : C.LPt) (c : ℂ) : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := by
  rw [Dx2.SL.ptSize_append]

theorem integrable_slice_append_single {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h : C.LPt) (c : ℂ)
    (hle : D.ptSize (h ++ [(1, c)]) ≤ r) (hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])))
    (γ' : B.Mat k (r - D.ptSize (h ++ [(1, c)])))
    (hI : Integrable (JCTx6.gInt k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
        (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
        (D.castF (by have := point_size_append_single h c; omega) F) γ')
      (JCTx6.muG k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h))) :
    Integrable (fun ξ : U.Xi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) =>
        U.psiStar k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) (D.castV (by omega) z)
            (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))
            (D.ptDiag (h ++ [(1, c)])) ξ (fun a => a.elim0) γ'))
      (U.muXi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))) := by
  have hP : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := point_size_append_single h c
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ (Dx2.SL.isLocPt_head hloc)).1
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(1, c)]) a).val := by
    intro a
    rw [hspec a, Dx2.SL.partner_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      Dx2.SL.dP (n := 0) (D.ptDiag h) c (Fin.cast hP a) = D.ptDiag (h ++ [(1, c)]) a := by
    intro a
    simp only [D.ptDiag]
    rw [Dx2.SL.scal_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.dP, Fin.addCases_right]

  have hσ' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      (D.ptPerm (h ++ [(1, c)]) (Fin.cast hP.symm b)).val = ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) b).val := by
    intro b
    have := hσ (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have hd' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      D.ptDiag (h ++ [(1, c)]) (Fin.cast hP.symm b) = Dx2.SL.dP (n := 0) (D.ptDiag h) c b := by
    intro b
    have := hd (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have h1 := JCTx6.Int.orbit_slice_integrable k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z') E
    (D.castF (by have := point_size_append_single h c; omega) F) γ' hI
  have h2 := (Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(1, c)])) hP.symm _ _ hσ' _ _ hd'
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
    (D.castF (by have := point_size_append_single h c; omega) F) γ').1 h1
  simpa only [Dx2.SL.castV_castV, Dx2.SL.castF_castF] using h2

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem asm_omLong_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (β : ℂ) (Φ : G.Mat 1 → V) (z : ℂ) :
    G.OmLong β 0 Φ z = Φ (fun _ _ => z) := by
  unfold G.OmLong
  have : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  have hμ : G.muPi β (G.UT (0 + 1)) = Measure.dirac (fun q => isEmptyElim q) := Measure.pi_of_empty _ _
  rw [hμ, integral_dirac]
  have h1 : G.superSum (G.upper (fun q : G.UT (0 + 1) => isEmptyElim q)) = 0 := by
    simp [G.superSum]
  have h2 : (G.ptLong (0 + 1) z * G.upper (fun q : G.UT (0 + 1) => isEmptyElim q) : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.of fun _ _ => z := by
    ext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.ptLong, G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  rw [h1, h2]
  simp [G.psi]
  rfl

theorem asm_psi_cast {a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) (cc : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h z) cc (D.castM h g) = psi k a z cc g := by
  subst h; rw [P.JCTx5.castV_rfl, P.JCTx5.castM_rfl]

theorem asm_castM_mul {a b : ℕ} (h : a = b) (g g' : B.Mat k a) : D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_inv {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_castM {a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem asm_castM_symm {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h.symm (D.castM h g) = g := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_lowV_lift (a ρ m r : ℕ) (hm : 1 + ρ = m) (h1 : a + m = r) (h5 : a + 1 + ρ = a + (1 + ρ))
    (er : r = a + 1 + ρ) (zj : Fin (2 * m + k + 1) → ℂ) :
    U.lowV k a (1 + ρ) (D.castV h5 (D.castV er (D.castV h1 (liftVec k a m zj)))) = D.castV hm.symm zj := by
  subst hm; subst h1
  funext i
  simp only [U.lowV, D.castV, liftVec, Fin.val_cast]
  rw [dif_pos (by omega)]
  congr 1; ext; simp

theorem asm_phiFun_lev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {a r ρa ρb : ℕ} (e : ρa = ρb)
    (ha : r = a + 0 + ρa) (hb : r = a + 0 + ρb) (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (z0 z0' : Fin (2 * r + k + 1) → ℂ) (F0 : B.Mat k r → E) (g : B.Mat k ρa) :
    U.PhiFun (s := 0) k ρa σ d (D.castV ha z0) (D.castV ha z0') (D.castF ha.symm F0) (fun q => q.elim0) g =
      U.PhiFun (s := 0) k ρb σ d (D.castV hb z0) (D.castV hb z0') (D.castF hb.symm F0) (fun q => q.elim0)
        (D.castM e g) := by
  subst e; rw [P.JCTx5.castM_rfl]

theorem asm_bridge {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a ρ1 ρ2 m r : ℕ) (e12 : ρ1 = ρ2) (e : ρ2 + 1 = m) (er : r = a + 1 + ρ1)
    (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (zb zb' : Fin (2 * r + k + 1) → ℂ) (zj zj' : Fin (2 * m + k + 1) → ℂ)
    (hzj : D.castV (show a + m = r by omega) (liftVec k a m zj) = zb)
    (hzj' : D.castV (show a + m = r by omega) (liftVec k a m zj') = zb')
    (Fb : B.Mat k r → E) (c : ℂ) (γ : B.Mat k ρ2)
    (zA zA' : Fin (2 * (a + 1 + ρ1) + k + 1) → ℂ) (hzA : zA = D.castV er zb) (hzA' : zA' = D.castV er zb')
    (FA : B.Mat k (a + 1 + ρ1) → E) (hFA : FA = D.castF er.symm Fb) (γ1 : B.Mat k ρ1)
    (hγ1 : γ1 = D.castM e12.symm γ) :
    ∫ yy : U.RC k 1 ρ1 × U.RC k 1 ρ1,
        (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)) cStd
            (U.Rn k 1 ρ1 yy.1) *
          star (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA')) cStd
            (U.Rn k 1 ρ1 yy.2))) •
        U.PhiFun (p := a) (s := 0) k (1 + ρ1) σ d (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)
          (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA') (D.castF (by omega : a + (1 + ρ1) = a + 1 + ρ1) FA)
          (fun q => q.elim0)
          ((U.Rn k 1 ρ1 yy.1)⁻¹ * U.mMap k 1 ρ1 (Matrix.of fun _ _ => c) γ1 * U.Rn k 1 ρ1 yy.2)
        ∂((U.muRC k 1 ρ1).prod (U.muRC k 1 ρ1)) =
      ∫ xx : U.RC k 1 ρ2 × U.RC k 1 ρ2,
        (psi k m zj cStd (rn1 e xx.1) * star (psi k m zj' cStd (rn1 e xx.2))) •
          U.PhiFun (p := a) (s := 0) k (r - a) σ d (D.castV (by omega : r = a + 0 + (r - a)) zb)
            (D.castV (by omega : r = a + 0 + (r - a)) zb') (D.castF (by omega : a + 0 + (r - a) = r) Fb)
            (fun q => q.elim0)
            (D.castM (by omega : m = r - a) ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2))
        ∂((U.muRC k 1 ρ2).prod (U.muRC k 1 ρ2)) := by
  subst e12; subst e; subst hzA; subst hzA'; subst hFA; subst hγ1; subst er
  rw [P.JCTx5.castM_rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  simp only [rn1, mc, P.JCTx5.castM_rfl]
  have hl := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj
  have hl' := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj'
  subst hzj; subst hzj'
  rw [hl, hl', ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.1),
    ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.2)]
  congr 1
  rw [← asm_castM_inv, ← asm_castM_mul, ← asm_castM_mul, asm_castM_castM]
  exact asm_phiFun_lev (by omega) _ _ σ d _ _ _ _

theorem asm_pointStepT (hPS : PointStep) : PointStepT := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ
  obtain ⟨hhb, rfl⟩ := hh
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hP' : D.ptSize (h ++ [(1, c)]) = D.ptSize h + 1 := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h 1 c
  have hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])) := ⟨hc.1, rfl⟩
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨hhb, rfl⟩
  have hle : D.ptSize (h ++ [(1, c)]) ≤ P.r := by omega
  have e2 : D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])) = P.r := by omega
  have hFs : B.CkOn ⊤ (B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])))) (D.castF e2 F) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hF.1
  obtain ⟨R, hR⟩ := hF.2.1
  have hRs : ∀ g ∈ B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)]))), D.castF e2 F g ≠ 0 →
      B.gN g ≤ R := fun g hg hne => by
    have := hR _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne
    rwa [Formalism.FourierDecayAlt.P.PBE.gN_castM] at this
  have hγ' : D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ ∈
      B.GV P.k (P.r - D.ptSize (h ++ [(1, c)])) := Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  have hI := asm_gInt_int (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c hd0 hc0
    (D.castV e2.symm p.T.base.z) (D.castV e2.symm p.T.base.z') (D.castF e2 F) hFs R hRs _ hγ'
  have hS := Formalism.FourierDecayAlt.P.slice_measure_identity P.k P.r (Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' F h (h ++ [(1, c)]) 0 c rfl hle
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) hloc
    (integrable_slice_append_single p.T.base.z p.T.base.z' F h c hle hloc _ hI)
  rw [asm_omLong_zero] at hS
  have hPS' := hPS P.k (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) hd0 c hc0
    (D.castV (by omega) p.T.base.z) (D.castV (by omega) p.T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z'_mem)
    (Wq →L[ℂ] Wp) (D.castF (by omega) F)
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ)
    (integrable_unipotent_rank_one (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c _ _ _ _ hI)
  have hB := asm_bridge (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (P.r - (D.ptSize h + 1))
    (P.r - D.ptSize h) P.r (by omega) (by omega) (by omega) (D.ptPerm h) (D.ptDiag h) p.T.base.z p.T.base.z'
    (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' (p.T.z_lev _ (by omega)) (p.T.z'_lev _ (by omega)) F c γ
    _ _ rfl rfl _ rfl _ rfl
  have hπ : ((Real.pi ^ ((0 + 1) * 0 / 2) : ℝ) : ℂ) = 1 := by norm_num
  rw [hπ, one_smul] at hS
  refine ((show KB.slv p.T F (D.ptSize h + 1) hj [] (h ++ [(1, c)]) hc.2 (fun a => a.elim0) γ =
      D.sliceAt P.k P.r p.T.base.z p.T.base.z' F (h ++ [(1, c)])
        (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) from rfl).trans
    (hS.trans (hPS'.trans (hB.trans ?_))))
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  dsimp only
  congr 1
  show _ = D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h (D.castM _ _)
  unfold D.sliceAt
  rw [dif_pos (by omega)]

end Formalism.FourierDecayAlt.P.PBH
end
end
