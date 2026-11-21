import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.FormBSelfLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FormCc
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Sandwich
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SumFlatMapMap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTopA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefIntCpt

section
set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem poles_injective {lam : Fin n → ℝ} (hlam : StrictAnti lam) : Function.Injective (poleF false lam) := by
  intro s t h
  have h' : lam s + (1 - (n : ℝ)) / 2 = lam t + (1 - (n : ℝ)) / 2 := by
    have := h
    simp only [poleF, cond_false, poleV] at this
    exact_mod_cast this
  exact hlam.injective (by linarith)

theorem projection_square_integrable {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    ∃ P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)),
      (∀ s, IsGKEndo false ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (P s)) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) (P s f) = poleF false lam s • P s f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) f = poleF false lam s • f → P s f = f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF false lam s →
        eeF false (smE ε (rreg ε)) f = z' • f → P s f = 0) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), f = ∑ s, P s f) ∧
      ∀ s (j : ℕ), ∃ C : ℝ, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        NT (smE ε (rreg ε)) j (P s f) ≤ C * NT (smE ε (rreg ε)) (j + (n - 1)) f := by
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  have hc := datumV_casimir hP v₀
  have hVK := datumV_kStable hP v₀
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : L2 ε) := fun v =>
    (mem_smD_iff ε (rreg ε) (v : L2 ε)).1 v.2
  obtain ⟨B, hdec, -⟩ := ee_decomp false hσ hD hgap hV hc hVK hW
  obtain ⟨hpole, -⟩ := pole_match false hσ hD hsm hgap hV hc hVK hW hG
  have hinj : Set.InjOn (poleF false lam) (Finset.univ : Finset (Fin n)) :=
    (poles_injective hgap.1).injOn
  set a := poleF false lam with ha
  set EE := eeF false (smE ε (rreg ε)) with hEE
  set S := tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) with hS
  let P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)) := fun s =>
    Polynomial.aeval EE (Lagrange.basis Finset.univ a s)
  have hPe : ∀ s (e : Fin n → smD ε (rreg ε)) (z : ℂ), EE e = z • e →
      P s e = (Lagrange.basis Finset.univ a s).eval z • e := fun s e z he => dc_aeval_eigen he _
  have hLval : ∀ s t, (Lagrange.basis Finset.univ a s).eval (a t) = if s = t then 1 else 0 := by
    intro s t
    split_ifs with hst
    · subst hst; exact Lagrange.eval_basis_self hinj (Finset.mem_univ _)
    · exact Lagrange.eval_basis_of_ne hst (Finset.mem_univ _)

  have hterm : ∀ s, ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → EE (P s e) = a s • P s e := by
    intro s e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    rw [hPe s e _ hz, hLval s t]
    split_ifs with hst
    · subst hst; rw [one_smul, hz]
    · simp
  have hsum1 : ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → ∑ s, P s e = e := by
    intro e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨t, Finset.mem_univ _⟩
    have h1 : ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) = 1 := by
      rw [← Polynomial.eval_finsetSum, Lagrange.sum_basis hinj hne, Polynomial.eval_one]
    calc ∑ s, P s e = ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) • e :=
          Finset.sum_congr rfl fun s _ => hPe s e _ hz
      _ = e := by rw [← Finset.sum_smul, h1, one_smul]
  refine ⟨P, fun s => dc_isGKEndo_aeval (isGKEndo_eeF hσ hD _ false) _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    rw [hfe, map_sum, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => hterm s _ (hfb b).1 _ (hfb b).2
  · intro s f _ hf
    rw [hPe s f _ hf, Lagrange.eval_basis_self hinj (Finset.mem_univ _), one_smul]
  · intro s f hf z' hz' hfz
    by_cases h0 : f = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z' f hf h0 hfz
    have hts : s ≠ t := fun h => hz' (by rw [h])
    rw [hPe s f _ hfz, hLval s t, if_neg hts, zero_smul]
  · intro f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    conv_lhs => rw [hfe]
    rw [hfe]
    simp only [map_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_congr rfl fun b _ => hsum1 _ (hfb b).1 _ (hfb b).2).symm
  · intro s j
    obtain ⟨C, hC⟩ := NT_poly_le false (smE ε (rreg ε)) (Lagrange.basis Finset.univ a s) j
    have hdeg : (Lagrange.basis Finset.univ a s).natDegree = n - 1 := by
      rw [Lagrange.natDegree_basis hinj (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    refine ⟨C, fun f _ => ?_⟩
    have := hC f
    rw [hdeg] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem opPow_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hA : ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → A a b f g = A a b f' g) :
    ∀ (k : ℕ) (a b : Fin n) (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.opPow A k a b f g = S7.opPow A k a b f' g
  | 0, a, b, f, f', h, g, hg => by
      simp only [S7.opPow]
      split_ifs
      · exact h g hg
      · rfl
  | k + 1, a, b, f, f', h, g, hg => by
      simp only [S7.opPow, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact hA a c _ _ (fun g' hg' => opPow_congr A hA k c b f f' h g' hg') g hg

theorem opGelfand_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hA : ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → A a b f g = A a b f' g)
    (k : ℕ) {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    S7.opGelfand A k f g = S7.opGelfand A k f' g := by
  simp only [S7.opGelfand, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => opPow_congr A hA k a a f f' h g hg

theorem rightE_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.rightE ε a b f g = S7.rightE ε a b f' g :=
  fun a b _ _ h _ hg => icx_eabV_congr h a b hg

theorem rightEanti_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.rightEanti ε a b f g = S7.rightEanti ε a b f' g := by
  intro a b f f' h g hg
  simp only [S7.rightEanti, Pi.neg_apply]
  rw [icx_eabV_congr h (Fin.rev b) (Fin.rev a) hg]

theorem psiFor_pos_gelfand {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ) :
    (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        S7.opGelfand (S7.rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
          S7.opGelfand (S7.rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g := by
  obtain ⟨Ψ', h1, h2, h3, h4, -, h6, h7, h8⟩ := S7.psiAll (n := n) ε lam h T hlam hgap hq
  have hT1 : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 ≤ thrStar ε := le_max_left _ _
  have hT2 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
    le_max_right _ _
  have h8' : 8 * (n : ℝ) * S7.q0 ε < h := by
    have : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, by linarith⟩
  have hP' : IsPsiFor ε lam T Ψ' := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 h8'⟩
  have heq : ∀ g ∈ UJset ε, Ψ' g = Ψ g := puniq_psi_eq hstd hP hP' (HW.KType.w_ne_zero T)
  have heq' : ∀ g, inUJ ε g → Ψ g = Ψ' g := fun g hg => (heq g hg).symm
  refine ⟨fun X hX => ?_, fun k g hg => ?_⟩
  · obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
    have hX1 : inUJ ε (NormedSpace.exp X) := by
      have := S7.inUJ_kexp (1 : S7.KG ε) hX
      have hk1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
      rwa [hk1, one_mul] at this
    rw [heq' _ hX1]
    exact psi_exp_isPositive T Ψ' μ hμ (h8 μ hμ) X hX
  · obtain ⟨e1, e2⟩ := h7 k g hg
    refine ⟨?_, ?_⟩
    · rw [opGelfand_congr _ rightE_congr k heq' hg, e1, heq' g hg]
    · rw [opGelfand_congr _ rightEanti_congr k heq' hg, e2, heq' g hg]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

def PmProp (ε : Fin n → Bool) (m : ℕ) {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) : Prop :=
  ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ idx : Fin m → Fin n × Fin n,
        ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
            ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
          C * NE (smE ε (rreg ε)) (m * (n - 1)) x * NE (smE ε (rreg ε)) (m * (n - 1)) y

theorem one_le_q_zero {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) : 1 ≤ S7.q0 ε := by
  unfold S7.q0; exact le_min hp hq

theorem square_integrable_generated_vectors {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ)
    (hv₀ : v₀ ≠ 0) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
        (Formalism.REAL.muG ε) := by
  obtain ⟨Ψ', h1, h2, h3, h4, -, h6, -, -⟩ := S7.psiAll (n := n) ε lam h T hlam hgap hq
  have hmax := hth
  unfold thrStar at hmax
  rw [max_lt_iff] at hmax
  have hsq : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ (n : ℝ) * S7.q0 ε := by positivity
  have hL2 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith [hmax.2]
  have hw2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith [hmax.2]
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, hmax.1⟩
  have hP' : IsPsiFor ε lam T Ψ' := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 hL2⟩
  have heq : ∀ g ∈ UJset ε, Ψ' g = Ψ g := puniq_psi_eq hstd hP hP' hv₀
  refine weighted_datum hstd hP hv₀ (fun μ hμ => ?_)
  refine ((h6 μ hμ).2.2 2 (by norm_num) hw2).congr (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [heq _ g.2]

theorem standard_gap_data {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ)
    (hv₀ : v₀ ≠ 0) :
    StdGap ε lam ∧ (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  have hT1 : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 ≤ thrStar ε := le_max_left _ _
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, by linarith⟩
  obtain ⟨hpos, hGel⟩ := psiFor_pos_gelfand hlam hgap hth hq hP
  exact ⟨hstd, hpos, square_integrable_generated_vectors hlam hgap hth hq hP hv₀, hasGelfandChar_sigLam hstd hP hv₀ hGel⟩

theorem tensor_inner_single_coef {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (a b : Fin n) (x y : D) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((((Pi.single a y : Fin n → D) c) : D) : H)
        (tensGrp false σ g (fun d => ((((Pi.single b x : Fin n → D) d) : D) : H)) c) =
      (if ε a then (1 : ℂ) else -1) * (g a b * inner ℂ (y : H) (σ g (x : H))) := by
  rw [Finset.sum_eq_single a (fun c _ hc => by simp [Pi.single_eq_of_ne hc]) (by simp)]
  congr 1
  simp only [Pi.single_eq_same, tensGrp, cond_false, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single b (fun d _ hd => by simp [Pi.single_eq_of_ne hd]) (by simp)]
  simp

theorem tensor_inner_sum_eq {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (η : Fin n → H) {β : Type*} (B : Finset β) (F : β → Fin n → D) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (η c) (tensGrp false σ g (fun d => (((∑ b ∈ B, F b) d : D) : H)) c) =
      ∑ b ∈ B, ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (η c) (tensGrp false σ g (fun d => ((F b d : D) : H)) c) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [tensGrp, Finset.sum_apply, Submodule.coe_sum, map_sum, Finset.smul_sum, inner_sum]
  rw [Finset.sum_comm]

theorem pmProp_zero {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) : PmProp ε 0 T Ψ v₀ := by
  refine ⟨1, fun x _ y _ g hg idx => ?_⟩
  rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one, zero_mul, NE_zero_eq, NE_zero_eq, one_mul]
  calc ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖
      ≤ ‖((y : smD ε (rreg ε)) : L2 ε)‖ * ‖rreg ε g ((x : smD ε (rreg ε)) : L2 ε)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [(rreg_isURepOn ε).2.1 g hg, mul_comm]

theorem regular_term_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (hstd : StdGap ε lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hth : thrStar ε < h) (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (s : Fin n) {P : Module.End ℂ (Fin n → smD ε (rreg ε))}
    (hPG : IsGKEndo false ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) P)
    (hPz : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF false (smE ε (rreg ε)) (P f) = poleF false lam s • P f)
    (hP1 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF false (smE ε (rreg ε)) f = poleF false lam s • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF false lam s →
      eeF false (smE ε (rreg ε)) f = z' • f → P f = 0)
    (hPN : ∀ j : ℕ, ∃ C : ℝ, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      NT (smE ε (rreg ε)) j (P f) ≤ C * NT (smE ε (rreg ε)) (j + (n - 1)) f)
    {T' : S7.KType ε (lowK ε (shiftF false lam s))}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hok : ReciprocityTheory.ChartRestriction.DS.cns_Ok ε (shiftF false lam s) T' Ψ') (m : ℕ) (IH : PmProp ε m T' Ψ' T'.w) :
    ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ a b : Fin n, ∀ idx : Fin m → Fin n × Fin n,
        ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single a y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g (fun d => ((P (Pi.single b x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
        C * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
  obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hok
  have := Hlam_nontrivial hstd hP hv₀
  have := Hlam_nontrivial hgap' hP' hv'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ v₀)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  obtain ⟨⟨ι, hι, hιe, hιs⟩, -⟩ := cc_gk false hstd hP hv₀ hgap' hP' hv' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s rfl hw hw'
  obtain ⟨ka, q, hka, -, hqm, hT2, hT3, hT1⟩ :=
    form_cc false hstd hP hv₀ hgap' hP' hv' hW s hι hιe hιs hPG hPz hP1 hP0
  obtain ⟨K, hK⟩ := NE_q_le ε (smE ε (rreg ε)) (smE ε (rreg ε)) (tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (fun a b f hf => tensSub_stable false a b f hf) q P (n - 1) hPN ka hka (fun a b f hf => hT2 a b f hf) hT3
    (m * (n - 1))
  obtain ⟨C', hC'⟩ := IH
  refine ⟨|ka| * max C' 0 * max K 0 * max K 0, fun x hx y hy g hg a b idx => ?_⟩
  have hfx : (Pi.single b x : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
    rw [tset_mem]; intro c; by_cases hc : c = b
    · subst hc; simpa using hx
    · simp [Pi.single_eq_of_ne hc]
  have hfy : (Pi.single a y : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
    rw [tset_mem]; intro c; by_cases hc : c = a
    · subst hc; simpa using hy
    · simp [Pi.single_eq_of_ne hc]
  rw [hT1 _ hfx _ hfy g hg]
  have hidx : m * (n - 1) + (n - 1) = (m + 1) * (n - 1) := by ring
  have hX := (hqm _ hfx).1
  have hY := (hqm _ hfy).1
  have h1 := hC' _ hX _ hY g hg idx
  have h2 : NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) ≤
      max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x := by
    refine (hK _ hfx).trans ?_
    rw [NT_single, hidx]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NE_nonneg _ _ _)
  have h3 : NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) ≤
      max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
    refine (hK _ hfy).trans ?_
    rw [NT_single, hidx]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NE_nonneg _ _ _)
  have hA := NE_nonneg (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x))
  have hB := NE_nonneg (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y))
  have hC0 : (0 : ℝ) ≤ max C' 0 := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ max K 0 := le_max_right _ _
  have h4 : C' * NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) *
      NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) ≤
      max C' 0 * (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x) *
        (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y) := by
    calc _ ≤ max C' 0 * NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) *
          NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hA) hB
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 hC0) h3 hB (mul_nonneg hC0 (mul_nonneg hK0 (NE_nonneg _ _ _)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  calc |ka| * (‖inner ℂ ((q (Pi.single a y) : smD ε (rreg ε)) : L2 ε)
          (rreg ε g ((q (Pi.single b x) : smD ε (rreg ε)) : L2 ε))‖ * ∏ t, ‖g (idx t).1 (idx t).2‖)
      ≤ |ka| * (max C' 0 * (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x) *
        (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y)) :=
        mul_le_mul_of_nonneg_left (h1.trans h4) (abs_nonneg _)
    _ = _ := by ring

theorem single_mem_tensSub {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (b : Fin n) {x : smD ε (rreg ε)}
    (hx : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :
    (Pi.single b x : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  rw [tset_mem]; intro c; by_cases hc : c = b
  · subst hc; simpa using hx
  · simp [Pi.single_eq_of_ne hc]

theorem pmProp_succ_of_gap {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ)
    (IH : ∀ {lam : Fin n → ℝ}, S7.IsHCParam lam → ∀ {h : ℝ}, GapAtLeast ε lam h → thrStar ε + m < h →
      ∀ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V),
        IsPsiFor ε lam T Ψ → v₀ ≠ 0 → PmProp ε m T Ψ v₀)
    {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hm : thrStar ε + ((m + 1 : ℕ) : ℝ) < h) {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    PmProp ε (m + 1) T Ψ v₀ := by
  have hq0 := one_le_q_zero hp hq
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast at hm
  have hth : thrStar ε < h := by linarith
  obtain ⟨hstd, hpos, hW, hG⟩ := standard_gap_data hlam hgap hth hq0 hP hv₀
  obtain ⟨P, hPG, hPz, hP1, hP0, hsum, hPN⟩ := projection_square_integrable hlam hstd hP hv₀ hW hG
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : _) := fun v => (mem_smD_iff ε (rreg ε) _).1 v.2
  have hterm : ∀ s, ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ g ∈ UJset ε, ∀ a b : Fin n,
      ∀ idx : Fin m → Fin n × Fin n,
        ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single a y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g (fun d => ((P s (Pi.single b x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
        C * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF false lam s)
    · have hg' := ReciprocityTheory.ChartRestriction.DS.cns_shift_gap false hgap s
      obtain ⟨T', Ψ', hok⟩ := ReciprocityTheory.ChartRestriction.DS.cns_data' hq0 hs hg' (by linarith)
      exact regular_term_bound hP hv₀ hstd hgap hth hpos hW hG s (hPG s) (hPz s) (hP1 s) (hP0 s) (hPN s) hok m
        (IH hs hg' (by linarith) T' Ψ' T'.w hok.2.2.1 hok.2.2.2.1)
    · refine ⟨0, fun x hx y hy g hg a b idx => ?_⟩
      have hfx := single_mem_tensSub b hx
      have h0 : P s (Pi.single b x) = 0 :=
        cc_gk_singular false hσ hD hsm hstd (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
          (datumV_kStable hP v₀) hW hG s (ReciprocityTheory.ChartRestriction.DS.cns_sing false hlam hs) _ ((hPG s).1 _ hfx)
          (hPz s _ hfx)
      rw [h0]
      simp [tensGrp]
  choose Cs hCs using hterm
  refine ⟨∑ s, Cs s, fun x hx y hy g hg idx => ?_⟩
  have hfx := single_mem_tensSub (idx 0).2 hx
  have key := tensor_inner_single_coef (ε := ε) (rreg ε) g (idx 0).1 (idx 0).2 x y
  rw [hsum _ hfx, tensor_inner_sum_eq] at key
  have hsgn : ‖(if ε (idx 0).1 then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  rw [Fin.prod_univ_succ]
  calc ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
        (‖g (idx 0).1 (idx 0).2‖ * ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖)
      = ‖(if ε (idx 0).1 then (1 : ℂ) else -1) * (g (idx 0).1 (idx 0).2 *
          inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε)))‖ *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := by
        rw [norm_mul, norm_mul, hsgn]; ring
    _ ≤ (∑ s, ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single (idx 0).1 y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g
              (fun d => ((P s (Pi.single (idx 0).2 x) d : smD ε (rreg ε)) : L2 ε)) c)‖) *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := by
        rw [← key]
        exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (prod_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ s, ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single (idx 0).1 y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g
              (fun d => ((P s (Pi.single (idx 0).2 x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := Finset.sum_mul _ _ _
    _ ≤ ∑ s, Cs s * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y :=
        Finset.sum_le_sum fun s _ => hCs s x hx y hy g hg (idx 0).1 (idx 0).2 (fun t => idx t.succ)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

theorem pmProp_of_gap {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ) :
    ∀ {lam : Fin n → ℝ}, S7.IsHCParam lam → ∀ {h : ℝ}, GapAtLeast ε lam h → thrStar ε + m < h →
      ∀ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V),
        IsPsiFor ε lam T Ψ → v₀ ≠ 0 → PmProp ε m T Ψ v₀ := by
  induction m with
  | zero => intro lam _ h _ _ T Ψ v₀ _ _; exact pmProp_zero T Ψ v₀
  | succ m ih => intro lam hlam h hgap hm T Ψ v₀ hP hv₀; exact pmProp_succ_of_gap hp hq m ih hlam hgap hm hP hv₀

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem pm_induction {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ) {lam : Fin n → ℝ}
    (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hm : thrStar ε + m < h)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ idx : Fin m → Fin n × Fin n,
        ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
            ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
          C * NE (smE ε (rreg ε)) (m * (n - 1)) x * NE (smE ε (rreg ε)) (m * (n - 1)) y :=
  pmProp_of_gap hp hq m hlam hgap hm T Ψ v₀ hP hv₀

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem hs_pow_mul_le (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) {c A : ℝ} (hc : 0 ≤ c)
    (h : ∀ idx : Fin m → Fin n × Fin n, c * ∏ t, ‖g (idx t).1 (idx t).2‖ ≤ A) :
    Real.sqrt (S7.hs g) ^ m * c ≤ (n : ℝ) ^ (2 * m) * A := by
  have hsq : Real.sqrt (S7.hs g) ≤ ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ := by
    have h1 : S7.hs g = ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ ^ 2 := by
      rw [S7.hs, ← Finset.univ_product_univ, Finset.sum_product]
    have h2 : ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ ^ 2 ≤ (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ 2 := by
      rw [sq (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖), Finset.sum_mul]
      refine Finset.sum_le_sum fun ab _ => ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun ab : Fin n × Fin n => ‖g ab.1 ab.2‖)
        (fun (i : Fin n × Fin n) _ => norm_nonneg (g i.1 i.2)) (Finset.mem_univ ab)) (norm_nonneg (g ab.1 ab.2))
    rw [h1, Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact h2
  have hpow : (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ m =
      ∑ idx : Fin m → Fin n × Fin n, ∏ t, ‖g (idx t).1 (idx t).2‖ := by
    rw [← Fin.prod_const, Finset.prod_univ_sum]
    rfl
  calc Real.sqrt (S7.hs g) ^ m * c ≤ (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ m * c :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq m) hc
    _ = ∑ idx : Fin m → Fin n × Fin n, c * ∏ t, ‖g (idx t).1 (idx t).2‖ := by
        rw [hpow, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ ∑ _idx : Fin m → Fin n × Fin n, A := Finset.sum_le_sum fun idx _ => h idx
    _ = (n : ℝ) ^ (2 * m) * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        simp only [Fintype.card_fin]; push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Equiv

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem dSW_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x)) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ x : H₁, dSW σ₂ w (U x) = U (dSW σ₁ w x)
  | [], _, _ => rfl
  | X :: w, hw, x => by
    simp only [dSW]
    rw [dSW_map_isometry U hU w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) x,
      dS_map_isometry U hU (hw X List.mem_cons_self)]

theorem nuJ_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (x : H₁) :
    nuJ σ₂ Ws (U x) = nuJ σ₁ Ws x := by
  unfold nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [dSW_map_isometry U hU w (hWs w hw) x, U.norm_map]

end Equiv

theorem decBoundJ_of_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) (m N : ℕ) (hL : DecBoundJ ε (sigLam ε Ψ v₀) m N) :
    DecBoundJ ε σ m N := by
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hσ hstd hP hv₀
  obtain ⟨C, Ws, hWs, hB⟩ := hL
  have hWs' : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  refine ⟨C, Ws, hWs, fun u v hu hv g hg => ?_⟩
  obtain ⟨x, rfl⟩ := U.surjective u
  obtain ⟨y, rfl⟩ := U.surjective v
  have hx := smooth_symm_of_isometry U hU hu
  have hy := smooth_symm_of_isometry U hU hv
  rw [U.symm_apply_apply] at hx hy
  have hb := hB x y hx hy g hg
  rw [← hU g hg x, U.inner_map_map, nuJ_map_isometry U hU hWs' x, nuJ_map_isometry U hU hWs' y]
  exact hb

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem br_facts {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) :
    P⁻¹ = Pᴴ ∧ P * Pᴴ = 1 ∧ Pᴴ * P = 1 ∧ Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
  obtain ⟨⟨_, hJ⟩, hU⟩ := hP
  have h1 : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨Matrix.inv_eq_left_inv h2, h1, h2, ?_⟩
  have hJe : Jm ε = Formalism.REAL.Jm ε := rfl
  rw [hJe, ← hJ]
  calc Formalism.REAL.Jm ε = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by simp only [Matrix.mul_assoc]

theorem bridge_group {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ↔ P * g * P⁻¹ ∈ UJset ε := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hJ' : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = P * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * Pᴴ := by
    rw [hinv, ← hJ']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  show gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r ↔ inUJ ε (P * g * P⁻¹)
  unfold inUJ
  rw [e, hJ]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key] at this
    exact this

theorem bridge_lie {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.S.InLieHpk k r X ↔ inG ε (P * X * P⁻¹) := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have h2' : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * X * P⁻¹)ᴴ * Jm ε + Jm ε * (P * X * P⁻¹) =
      P * (Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X) * Pᴴ := by
    rw [hinv, hJ]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc, h2']
  show Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 ↔ inG ε (P * X * P⁻¹)
  unfold inG
  rw [e]
  constructor
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this

theorem bridge_gN {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g = Real.sqrt (S7.hs (P * g * P⁻¹)) := by
  obtain ⟨hi, h2, h1, -⟩ := br_facts hP
  have key : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Matrix.trace (Mᴴ * M)).re := by
    intro M
    rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  have e1 : ∑ i, ∑ j, Complex.normSq (g i j) = ∑ i, ∑ j, ‖g i j‖ ^ 2 := by
    simp [Complex.normSq_eq_norm_sq]
  have e2 : (P * g * Pᴴ)ᴴ * (P * g * Pᴴ) = P * ((gᴴ * g) * Pᴴ) := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul]
  have L : ∑ i, ∑ j, ‖g i j‖ ^ 2 = (gᴴ * g).trace.re := key g
  have R : ∑ i, ∑ j, ‖(P * g * Pᴴ) i j‖ ^ 2 = ((P * g * Pᴴ)ᴴ * (P * g * Pᴴ)).trace.re := key _
  rw [e1, hi, L, R, e2, Matrix.trace_mul_comm P, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bridge_smooth {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ ↔ IsSmoothVecU ε (fun g => σ (P⁻¹ * g * P)) v := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  let cA : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P⁻¹).comp (LinearMap.mulRight ℝ P))
  let cB : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P).comp (LinearMap.mulRight ℝ P⁻¹))
  have hcA : ∀ g, cA g = P⁻¹ * g * P := fun g => by simp [cA, Matrix.mul_assoc]
  have hcB : ∀ g, cB g = P * g * P⁻¹ := fun g => by simp [cB, Matrix.mul_assoc]
  have hAB : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hBA : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hPd, Matrix.mul_one]
  have hmem : ∀ g, Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) g ↔ inUJ ε (P * g * P⁻¹) := fun g => bridge_group hP g
  simp only [Formalism.MainNotions.S.smoothVecs, Set.mem_setOf_eq, Formalism.MainNotions.S.IsSmoothVec, IsSmoothVecU]
  constructor
  · intro hv g₀ hg₀
    have hg₁ : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g₀ * P) := (hmem _).2 (by rw [hBA]; exact hg₀)
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cA ⁻¹' U, F ∘ cA, hU.preimage cA.continuous, by simp [hcA, hxU],
      hF.comp cA.contDiff.contDiffOn (fun x hx => hx), fun g hg hgJ => ?_⟩
    have hgH : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g * P) := (hmem _).2 (by rw [hBA]; exact hgJ)
    have h3 := hfF _ (by simpa [hcA] using hg) hgH
    simp only at h3
    simp only [Function.comp_apply, hcA]
    exact h3
  · intro hv g₀ hg₀
    have hg₁ : inUJ ε (P * g₀ * P⁻¹) := (hmem g₀).1 hg₀
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cB ⁻¹' U, F ∘ cB, hU.preimage cB.continuous, by simp [hcB, hxU],
      hF.comp cB.contDiff.contDiffOn (fun x hx => hx), fun g hg hgH => ?_⟩
    have h3 := hfF _ (by simpa [hcB] using hg) ((hmem g).1 hgH)
    simp only at h3
    simp only [Function.comp_apply, hcB]
    rw [← h3, hAB]

theorem bridge_dsigW {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v =
      dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v := by
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hE : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (t : ℝ),
      P⁻¹ * NormedSpace.exp ((t : ℂ) • (P * X * P⁻¹)) * P = NormedSpace.exp ((t : ℂ) • X) := by
    intro X t
    have e1 : ((t : ℂ) • (P * X * P⁻¹)) = P * ((t : ℂ) • X) * P⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.exp_conj P ((t : ℂ) • X) hPu]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hconj : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (u : H),
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X u = dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) u := by
    intro X u
    unfold Formalism.MainNotions.S.dsig dS
    simp only [hE]
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) =
      dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) (dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v)
    rw [ih, hconj]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem decSm_of_decBoundJ {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (m N : ℕ)
    (hJ : DecBoundJ ε (fun g => σ (P⁻¹ * g * P)) m N) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ N ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨hinv, -, -, -⟩ := br_facts hP
  have hPPi : P * P⁻¹ = 1 := by
    rw [hinv]; exact (br_facts hP).2.1
  have hPiP : P⁻¹ * P = 1 := by
    rw [hinv]; exact (br_facts hP).2.2.1
  have hconj : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P * (P⁻¹ * X * P) * P⁻¹ = X := by
    intro X
    calc P * (P⁻¹ * X * P) * P⁻¹ = (P * P⁻¹) * X * (P * P⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
  have hconj' : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
  have hmapid : ∀ w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      ((w.map fun X => P⁻¹ * X * P).map fun X => P * X * P⁻¹) = w := by
    intro w
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left (fun X _ => hconj X)
  obtain ⟨C, Ws, hWs, hb⟩ := hJ
  refine ⟨C, Ws.map fun w => w.map fun X => P⁻¹ * X * P, ?_, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    refine ⟨by rw [List.length_map]; exact (hWs w hw).1, ?_⟩
    intro X' hX'
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hX'
    rw [bridge_lie hP, hconj]
    exact (hWs w hw).2 X hX
  · intro u hu v hv g hg
    have hsum : ∀ x : H,
        ((Ws.map fun w => w.map fun X => P⁻¹ * X * P).map
            fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w x‖).sum = nuJ (fun g => σ (P⁻¹ * g * P)) Ws x := by
      intro x
      unfold nuJ
      rw [List.map_map]
      congr 1
      refine List.map_congr_left (fun w _ => ?_)
      simp only [Function.comp_apply]
      rw [bridge_dsigW hP, hmapid]
    have key := hb u v ((bridge_smooth hP σ u).1 hu) ((bridge_smooth hP σ v).1 hv)
      (P * g * P⁻¹) ((bridge_group hP g).1 hg)
    simp only [] at key
    rw [hconj'] at key
    rw [hsum, hsum, bridge_gN hP]
    exact key

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

theorem hs_eq_of_compact {n : ℕ} {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : S7.hs g = n := by
  have h2 : inUJ ε g := hg
  delta inUJ Jm at h2
  delta pOf qOf at hpq
  have hU : g.conjTranspose * g = 1 := by
    rcases hpq with hp | hq
    · have hall : ∀ a, ε a = false := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hp) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = -1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
    · have hall : ∀ a, ε a = true := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hq) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = 1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
  delta S7.hs
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, ‖g i j‖ ^ 2 = (1 : ℝ) := by
    intro j
    have hjj := congrFun (congrFun hU j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
    have hc : ∀ i, g.conjTranspose j i * g i j = ((‖g i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
      norm_cast
    simp only [hc] at hjj
    exact_mod_cast hjj
  simp [key]

theorem decBound_of_compact {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0) (m N : ℕ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m N := by
  obtain ⟨_, _, hU, _⟩ := hσ
  refine ⟨Real.sqrt (n : ℝ) ^ m, [[]], ?_, ?_⟩
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    simp
  · intro u v _ _ g hg
    have hn : S7.hs g = n := hs_eq_of_compact hpq hg
    have hnorm : ‖σ g u‖ = ‖u‖ := hU.2.1 g hg u
    simp only [nuJ, dSW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hn, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) _)
    calc ‖inner ℂ v (σ g u)‖ ≤ ‖v‖ * ‖σ g u‖ := norm_inner_le_norm v (σ g u)
      _ = ‖u‖ * ‖v‖ := by rw [hnorm, mul_comm]

theorem decSmJ {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (m : ℕ) (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m (m * (n - 1)) := by
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · exact decBound_of_compact hpq m _ hσ
  have hp : 1 ≤ pOf ε := by omega
  have hq : 1 ≤ qOf ε := by omega
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have hth : thrStar ε < h := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε := le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hlam hgap hq0 h8
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨C, hC⟩ := pm_induction hp hq m hlam hgap hm hP hv₀
  refine decBoundJ_of_sigLam hlam hgap hth hP hv₀ hσ m _ ?_
  refine decBoundJ_sigLam hlam hstd hP hv₀ m _ ⟨(n : ℝ) ^ (2 * m) * C, fun x hx y hy g hg => ?_⟩
  have := hs_pow_mul_le m g (norm_nonneg _) fun idx => hC x hx y hy g hg idx
  calc _ ≤ _ := this
    _ = _ := by ring

theorem decSm {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m : ℕ)
    (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ m * (2 * r + k) ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hJ := decSmJ ((mir_isHCParam_iff lam).1 hlam) ((mir_gapAtLeast_iff ε lam h).1 hgap) m hm hDS
  have hN : m * (2 * r + k + 1 - 1) = m * (2 * r + k) := by rw [Nat.add_sub_cancel]
  rw [hN] at hJ
  exact decSm_of_decBoundJ hP m _ hJ

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
