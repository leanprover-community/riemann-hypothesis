import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdCons

section
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS

theorem degPsi : DegPsi := by
  intro n ε V _ _ _ Ψ H _ _ σ j C d m hC hj hΨ hd
  set b := stdOrthonormalBasis ℂ V with hb
  obtain ⟨hd0, hS⟩ := hd
  have hb1 : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
  have key : ∀ i l, Integrable (fun g : Formalism.REAL.UJ ε => ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2) m ∧
      ∫ g, ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 ∂m = 1 / d := by
    intro i l
    obtain ⟨hi, he⟩ := hS (j (b i)) (j (b l)) (j (b i)) (j (b l))
    have hpt : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.coefOn σ (j (b i)) (j (b l)) g * star (Formalism.MainNotions.S.coefOn σ (j (b i)) (j (b l)) g) =
        ((C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [Formalism.MainNotions.S.coefOn]
      rw [hΨ g (b i) (b l), norm_mul, Complex.norm_real, Real.norm_of_nonneg hC.le]
      push_cast; ring
    simp_rw [hpt] at hi he
    rw [integral_complex_ofReal, hj, hj, hb1, hb1] at he
    have he' : ∫ g, C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 ∂m = C * C / d := by
      apply Complex.ofReal_injective
      rw [he]; push_cast; ring
    have hi' : Integrable (fun g : Formalism.REAL.UJ ε => C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2) m := by
      refine hi.re.congr (ae_of_all _ fun g => ?_)
      simp only
      exact RCLike.ofReal_re _
    have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hC.ne'
    refine ⟨?_, ?_⟩
    · refine (hi'.const_mul (C ^ 2)⁻¹).congr (ae_of_all _ fun g => ?_)
      simp only
      field_simp
    · rw [integral_const_mul] at he'
      have hd' : d ≠ 0 := hd0.ne'
      field_simp at he' ⊢
      nlinarith [he']
  have hexp : ∀ g : Formalism.REAL.UJ ε, hsOp (Ψ (Formalism.MainNotions.S.umat g)) =
      ∑ i, ∑ l, ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 := by
    intro g
    unfold hsOp
    exact sum_congr rfl fun i _ => (b.sum_sq_norm_inner_right _).symm
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => hsOp (Ψ (Formalism.MainNotions.S.umat g))) m := by
    simp_rw [hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (key i l).1
  have hval : ∫ g, hsOp (Ψ (Formalism.MainNotions.S.umat g)) ∂m = (Module.finrank ℂ V : ℝ) ^ 2 / d := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun l _ => (key i l).1)]
    rw [sum_congr rfl fun i _ => integral_finsetSum _ fun l _ => (key i l).1]
    rw [sum_congr rfl fun i _ => sum_congr rfl fun l _ => (key i l).2]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun g => by unfold hsOp; positivity), hval]

end CompanionTheory.RgFd
end
end

section
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem gapNorm_of (hD : DegPsi) : GapNorm := by
  intro n ε hp hq
  refine ⟨G2.thrS ε + 2, fun lam hlam hgap T μ hμ => ?_⟩
  have hh : G2.thrS ε + 1 < G2.thrS ε + 2 := by linarith
  have hq0 := G2.one_le_q0_of_p_q_pos hp hq
  have h8 := G2.fdc_eight hh
  have hP : IsPsiFor ε lam T (PsiM T μ) := (S7.isPsiFor_psiM ε lam _ T μ hlam hμ hgap hq0 h8).1
  have hgap' := G2.fdc_stdGap hlam hgap hh
  have hw := G2.fdc_w_ne T
  have hDS := G2.isDS_sigLam hgap' hP hw
  have : CompleteSpace (Hlam ε (PsiM T μ) T.w) := hDS.1
  have : Nontrivial (Hlam ε (PsiM T μ) T.w) := hDS.2.1
  obtain ⟨d, hd⟩ := G2.fdcGood_of_isDS hDS
  obtain ⟨x, hx⟩ := exists_ne (0 : Hlam ε (PsiM T μ) T.w)
  have hΨ : ∀ μ' : Fin n → ℝ, IsHCParam μ' → GapAtLeast ε μ' (G2.thrS ε + 2) →
      ∃ (T' : KType ε (lowK ε μ')) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)), IsPsiFor ε μ' T' Ψ := by
    intro μ' hμ' hg'
    obtain ⟨T'⟩ := HW.kType_exists ε μ' hμ'
    obtain ⟨m', -, hP'⟩ := G2.fdc_model hp hq hμ' hg' hh T'
    exact ⟨T', _, hP'⟩
  have hdeg := G2.fdCons_cd hp hq hlam hgap hh hΨ hDS hx
  rw [fdegOf_of_isFdeg' hd hx] at hdeg
  subst hdeg
  set C : ℝ := ‖uniformisationL2 ε (PsiM T μ) T.w T.w‖ ^ 2 with hC
  have hC0 : 0 < C := by
    have := G2.datumEmbedding_highest_ne_zero hgap' hP hw
    positivity
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := umat_mem_UJset ε 1
  refine hD n ε T.V (PsiM T μ) (Hlam ε (PsiM T μ) T.w) (sigLam ε (PsiM T μ) T.w)
    (fun v => ⟨uniformisationL2 ε (PsiM T μ) T.w v, datumEmbedding_mem_Hlam hP v⟩) C (dimVlam lam) (muCD ε) hC0 (fun v v' => ?_) (fun g v v' => ?_) hd
  · have e := G2.formulaF_sigLam hgap' hP hw h1 v v'
    rw [hP.2.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    rw [← e, (G2.sigLam_isURepOn hgap' hP hw).1.1]
    rfl
  · exact G2.formulaF_sigLam hgap' hP hw (umat_mem_UJset ε g) v v'

end CompanionTheory.RgFd
end
end
