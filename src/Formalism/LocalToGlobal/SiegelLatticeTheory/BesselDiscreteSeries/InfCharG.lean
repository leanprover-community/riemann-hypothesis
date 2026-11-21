import Formalism.LocalToGlobal.SiegelLatticeTheory.InfCharDSGOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyCap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopCap

section
noncomputable section

open Matrix

namespace Formalism.MainNotions.BesselDiscreteSeries

open ReciprocityTheory.ChartRestriction.DS

theorem freeAlg_hom_eq_sum {X A : Type} [Ring A] [Algebra ℂ A] (φ : FreeAlgebra ℂ X →ₐ[ℂ] A)
    (p : FreeAlgebra ℂ X) :
    φ p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff
      (fun w c => c • (w.toList.map fun x => φ (FreeAlgebra.ι ℂ x)).prod) := by
  have key : φ = (MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift fun x => φ (FreeAlgebra.ι ℂ x))).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := X)).toAlgHom := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  refine (DFunLike.congr_fun key p).trans ?_
  simp only [AlgHom.comp_apply, MonoidAlgebra.lift_apply, FreeMonoid.lift_apply]
  rfl

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem thetaJ_cpart1 (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (Y + Formalism.L2.SG.LitS.thetaJ ε Y) = S7.cpart1 ε Y := by
  simp only [Formalism.L2.SG.LitS.thetaJ, S7.cpart1, sub_eq_add_neg]
  rfl

theorem thetaJ_cpart2 (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (1 / (2 * Complex.I)) • (Y - Formalism.L2.SG.LitS.thetaJ ε Y) = S7.cpart2 ε Y := by
  simp only [Formalism.L2.SG.LitS.thetaJ, S7.cpart2, sub_neg_eq_add]
  rfl

theorem dsigC_eq (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    Formalism.L2.SG.LitS.dsigC ε σ Y v = dS σ (S7.cpart1 ε Y) v + Complex.I • dS σ (S7.cpart2 ε Y) v := by
  unfold Formalism.L2.SG.LitS.dsigC
  rw [thetaJ_cpart1, thetaJ_cpart2]
  rfl

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dsigCW_word (hσ : IsURepOn (UJset ε) σ) (w : List (Fin n × Fin n)) (x : smD ε σ) :
    Formalism.L2.SG.LitS.dsigCW ε σ (w.map Formalism.L2.SG.LitS.unitM) x =
      (((w.map fun p => smE ε σ p.1 p.2).prod x : smD ε σ) : H) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, smE_apply hσ]
    show Formalism.L2.SG.LitS.dsigC ε σ (Formalism.L2.SG.LitS.unitM p)
      (Formalism.L2.SG.LitS.dsigCW ε σ (w.map Formalism.L2.SG.LitS.unitM) x) = _
    rw [ih, dsigC_eq]
    rfl

def smAlg (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (smD ε σ) :=
  FreeAlgebra.lift ℂ fun p => smE ε σ p.1 p.2

theorem actU_eq (hσ : IsURepOn (UJset ε) σ) (p : FreeAlgebra ℂ (Fin n × Fin n)) (x : smD ε σ) :
    Formalism.L2.SG.LitS.actU ε σ p x = ((smAlg ε σ p x : smD ε σ) : H) := by
  rw [freeAlg_hom_eq_sum (smAlg ε σ) p]
  simp only [Formalism.L2.SG.LitS.actU, Finsupp.sum, dsigCW_word hσ, smAlg, FreeAlgebra.lift_ι_apply]
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [LinearMap.smul_apply, Submodule.coe_smul]

theorem actU_qdet (hσ : IsURepOn (UJset ε) σ) (u : ℂ) (v : H) (hv : v ∈ smD ε σ) :
    Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) u) v =
      ((Formalism.REAL.qdet (smE ε σ) u ⟨v, hv⟩ : smD ε σ) : H) := by
  refine (actU_eq hσ _ ⟨v, hv⟩).trans ?_
  simp only [smAlg, ReciprocityTheory.ChartRestriction.DS.ICD.qdet_map, Formalism.L2.SG.LitS.Egl, FreeAlgebra.lift_ι_apply]

theorem mem_smD_of_smoothVecs {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ) :
    v ∈ smD ε σ := by
  exact (ReciprocityTheory.ChartRestriction.DS.mem_smD_iff ε σ v).mpr hv

end Formalism.MainNotions.BesselDiscreteSeries
end
end

section
noncomputable section

open Matrix MeasureTheory

namespace Formalism.MainNotions.BesselDiscreteSeries

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem infChar_of_model {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hDS : Formalism.MainNotions.S.IsDS ε lam σ)
    (hgap : StdGap ε lam) {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hP : IsPsiFor ε lam T Ψ)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g) :
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v := by
  haveI : CompleteSpace H := hDS.1
  intro v hv Y
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hm : v ∈ smD ε σ := mem_smD_of_smoothVecs hv
  have hc := anyCap hDS hgap hP hcap Y ⟨v, hm⟩
  rw [actU_qdet hσ _ v hm, hc]
  rfl

theorem isPsiFor_compact {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : S7.IsMu lam μ) :
    IsPsiFor ε lam T (S7.PsiM T μ) := by
  refine ⟨fun k₁ k₂ g hg => S7.psiM_equiv T μ k₁ k₂ hg, S7.psiM_one T μ, S7.psiM_smooth T μ hμ,
    fun g hg => S7.psiM_casimir T μ hμ hg, fun ν hν => ?_⟩
  haveI : CompactSpace (S7.UJ ε) := cmpt_compact (cmpt_eps_eq hpq)
  haveI := hν
  haveI : IsFiniteMeasure ν := inferInstance
  have hc : Continuous (fun g : S7.UJ ε => S7.PsiM T μ (S7.toM g)) :=
    (S7.psiM_continuousOn T μ hμ).comp_continuous (Units.continuous_val.comp continuous_subtype_val)
      (fun g => g.2)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun g => hC g (Set.mem_univ _))

theorem infinitesimal_character_discrete_series_gap : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
    Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrX ε < h →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v := by
  intro n ε lam H _ _ σ hlam hDS h hh hthr
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
  have hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) (S7.PsiM T μ) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • S7.PsiM T μ g :=
    fun Y g hg => S7.psiCapelli ε lam T μ hμ Y g hg
  rcases Nat.eq_zero_or_pos (S7.q0 ε) with h0 | hq
  ·
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := Nat.min_eq_zero_iff.1 h0
    exact infChar_of_model hDS (cf_stdGap_of_pq hpq hlam.1) (isPsiFor_compact hpq T μ hμ) hcap
  ·
    have hX : Formalism.MainNotions.GapDS.thrDS ε ≤ Formalism.MainNotions.GapDS.thrX ε ∧
        120 * (n : ℝ) * ((S7.q0 ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ Formalism.MainNotions.GapDS.thrX ε :=
      ⟨le_max_left _ _, le_max_right _ _⟩
    have hq1 : (1 : ℝ) ≤ (S7.q0 ε : ℝ) := by exact_mod_cast hq
    have e1 : (S7.q0 ε : ℝ) ≤ (S7.q0 ε : ℝ) ^ ((3 : ℝ) / 2) := by
      have := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
      simpa using this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
      have e2 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) ≤ 120 * (n : ℝ) * ((S7.q0 ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
        have : 8 * (n : ℝ) * (S7.q0 ε : ℝ) ≤ 120 * (n : ℝ) * (S7.q0 ε : ℝ) := by nlinarith
        have e3 : 120 * (n : ℝ) * (S7.q0 ε : ℝ) ≤ 120 * (n : ℝ) * ((S7.q0 ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
        linarith
      linarith [hX.2]
    have hstd : StdGap ε lam := ⟨hlam.1, h, hh, lt_of_le_of_lt hX.1 hthr⟩
    exact infChar_of_model hDS hstd (S7.isPsiFor_psiM ε lam h T μ hlam hμ hh hq h8).1 hcap

theorem gapped_infinitesimal_character : Formalism.MainNotions.GapDS.InfCharDSG := infinitesimal_character_discrete_series_gap

end Formalism.MainNotions.BesselDiscreteSeries
end
end
