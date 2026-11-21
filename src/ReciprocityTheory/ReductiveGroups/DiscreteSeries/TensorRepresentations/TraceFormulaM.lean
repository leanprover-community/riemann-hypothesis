import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer

section
noncomputable section

open MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_rep_closure {n : ℕ} {G : Type*} [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hρ : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (S : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hS : ∀ v ∈ S, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v)) :
    ∀ v ∈ S.topologicalClosure, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v) := by
  intro v hv c
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hv
  have huc : Tendsto (fun k => u k c) atTop (𝓝 (v c)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => PiLp.dist_apply_le _ _ c) (tendsto_iff_dist_tendsto_zero.1 hu))
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp huc).exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ k, ((u k c : Lp ℂ 2 μ) : G → ℂ) g = inner ℂ (w c) (ρ g (u k)) :=
    ae_all_iff.2 (fun k => hS (u k) (huS k) c)
  filter_upwards [hns, hall] with g hg hgall
  have h2 : Tendsto (fun i => inner ℂ (w c) (ρ g (u (ns i)))) atTop (𝓝 (inner ℂ (w c) (ρ g v))) := by
    have h3 : Tendsto (fun i => u (ns i)) atTop (𝓝 v) :=
      hu.comp (hmono.tendsto_atTop)
    exact ((continuous_const.inner continuous_id).tendsto _).comp ((ρ g).continuous.tendsto v |>.comp h3)
  simp only [hgall] at hg
  exact tendsto_nhds_unique hg h2

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem coe_toL2_ae_eq_of_memLp {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ((toL2 ε F : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun g => F (Formalism.MainNotions.S.umat g) := by
  unfold toL2
  rw [dif_pos h]
  exact h.coeFn_toLp

theorem tfd_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool) (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) (ζ : Fin n → H) (c : Fin n)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ g =
      tfSgn ε c * ∑ d, tfCoef dual g c d * inner ℂ y (σ g (ζ d)) := by
  unfold coefMap
  rw [sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same, inner_smul_left,
    tf_tensGrp_apply, inner_sum]
  simp only [inner_smul_right]
  congr 1
  exact tf_star_sgn ε c

theorem tensor_functor_separation (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : H} (hy : y ∈ closGen E V) {ζ ζ' : Fin n → H} (hζ : ∀ c, ζ c ∈ closGen E V)
    (hζ' : ∀ c, ζ' c ∈ closGen E V)
    (hm : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hm' : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ' (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    inner ℂ (tfPh dual ε σ y ζ) (tfJ ε (tfPh dual ε σ y ζ')) = tfFormBH ε ζ ζ' * inner ℂ y y / (d : ℂ) := by
  set F : (Fin n → H) → Fin n → Formalism.REAL.UJ ε → ℂ := fun ζ c g =>
    coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g) with hF
  have h1 : ∀ c, inner ℂ (tfPh dual ε σ y ζ c) (tfJ ε (tfPh dual ε σ y ζ') c) =
      ∫ g, tfSgn ε c * (star (F ζ c g) * F ζ' c g) ∂(Formalism.REAL.muG ε) := fun c => by
    rw [tfJ_apply, inner_smul_right, integral_const_mul, tfPh_apply, tfPh_apply, L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [coe_toL2_ae_eq_of_memLp (hm c), coe_toL2_ae_eq_of_memLp (hm' c)] with g e1 e2
    rw [e1, e2, RCLike.inner_apply, mul_comm]
    rfl
  have hi : ∀ c, Integrable (fun g => tfSgn ε c * (star (F ζ c g) * F ζ' c g)) (Formalism.REAL.muG ε) :=
    fun c => ((hm c).star.integrable_mul (hm' c)).const_mul _
  have hs := fun c => tfClRep_schur hgap hσ hD hV hc hVK hd hy (hζ' c) hy (hζ c)
  rw [PiLp.inner_apply, sum_congr rfl fun c _ => h1 c, ← integral_finsetSum _ fun c _ => hi c]
  have h2 : ∀ g : Formalism.REAL.UJ ε, ∑ c, tfSgn ε c * (star (F ζ c g) * F ζ' c g) =
      ∑ c, tfSgn ε c * (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)) *
        star (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c)))) := fun g => by
    have h3 := tf_jquad (tfCoef dual (Formalism.MainNotions.S.umat g)) (tfSgn ε) (tfCoef_orth dual (umat_mem_UJset ε g))
      (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c))) (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)))
    refine Eq.trans (sum_congr rfl fun c _ => ?_) (h3.trans (sum_congr rfl fun c _ => by ring))
    simp only [hF, tfd_coef, star_mul', tf_star_sgn]
    linear_combination (tfSgn ε c * star (∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
      inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ d))) * ∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
        inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' d))) * tfSgn_mul_self ε c
  simp only [h2]
  rw [integral_finsetSum _ fun c _ => (hs c).1.const_mul _, tfFormBH, sum_mul, sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [integral_const_mul, (hs c).2]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  set ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (Formalism.MainNotions.S.umat g) with hρ
  have hone : ρ 1 = 1 := by
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
    rw [e]; exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
    rw [e]; exact hU.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 _ (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy0, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy0
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hcoe : ∀ (g : Formalism.REAL.UJ ε) (x w : closGen E V),
      inner ℂ w (ρ g x) = inner ℂ (w : H) (σ (Formalism.MainNotions.S.umat g) (x : H)) := by
    intro g x w
    rw [Submodule.coe_inner, tfClRep_coe σ _ (hst _ (umat_mem_UJset ε g))]
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ ((y : D) : H) (σ (Formalism.MainNotions.S.umat g) ((y : D) : H))) :=
    continuous_const.inner ((hσ.2.2 _).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    simp only [hcoe]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : Subsingleton (Formalism.REAL.UJ ε) :=
        ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
      have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
      refine MemLp.of_bound hcont.aestronglyMeasurable (‖((y : D) : H)‖ * ‖((y : D) : H)‖)
        (Filter.Eventually.of_forall fun g => ?_)
      calc ‖inner ℂ ((y : D) : H) (σ (Formalism.MainNotions.S.umat g) ((y : D) : H))‖
          ≤ ‖((y : D) : H)‖ * ‖σ (Formalism.MainNotions.S.umat g) ((y : D) : H)‖ := norm_inner_le_norm _ _
        _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
    · refine (hW y hyG y hyG).of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
      have h1 : 1 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) :=
        Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact le_mul_of_one_le_left (norm_nonneg _) h1
  have hall : ∀ x, MemLp (fun g => inner ℂ y0 (ρ g x)) 2 (Formalism.REAL.muG ε) := fun x =>
    GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := ρ) (measurePreserving_mul_right ε) hone hmul hiso hirr
      y0 y0 hy0 h0 x
  intro v w
  show MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ w (ρ g v)) 2 (Formalism.REAL.muG ε)
  by_cases hw : w = 0
  · have e : (fun g : Formalism.REAL.UJ ε => inner ℂ w (ρ g v)) = 0 := by
      funext g
      rw [hw, inner_zero_left]
      rfl
    rw [e]
    exact (Lp.memLp (0 : Lp ℂ 2 (Formalism.REAL.muG ε))).ae_eq (Lp.coeFn_zero ℂ 2 _)
  have hinv := ((hall w).comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e2 : star ((fun g : Formalism.REAL.UJ ε => inner ℂ y0 (ρ g w)) ∘ Inv.inv) =
      fun g : Formalism.REAL.UJ ε => inner ℂ w (ρ g y0) := by
    funext g
    have hs : star (ρ g⁻¹) = ρ g⁻¹⁻¹ := GraphTrick.star_eq hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e2] at hinv
  exact GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := ρ) (measurePreserving_mul_right ε) hone hmul hiso hirr
    w y0 hy0 hinv v

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem tfg_gen {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (S : Submodule ℂ (Fin n → M))
    (hV : tensSub V ≤ S) (hS : ∀ a b, ∀ f ∈ S, tensF dual E a b f ∈ S) : tensSub (genSub E V) ≤ S := by
  let T : Submodule ℂ M := ⨅ c, S.comap (LinearMap.single ℂ (fun _ : Fin n => M) c)
  have hT : ∀ m, m ∈ T ↔ ∀ c, (Pi.single c m : Fin n → M) ∈ S := fun m => by simp [T, Submodule.mem_iInf]
  have hle : genSub E V ≤ T := sInf_le ⟨fun v hv => (hT v).2 fun c => hV (tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using hv
      · simp [h]),
    fun a b m hm => (hT _).2 fun c => by
      have hm' := (hT m).1 hm
      cases dual
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF false E a b (Pi.single c m) - if b = c then Pi.single a m else 0 := by
          funext d
          simp only [tensF, cond_false, Pi.sub_apply, tensV_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = a <;> by_cases h3 : b = c <;>
            simp_all
        rw [e]
        refine S.sub_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' a
        · exact S.zero_mem
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF true E a b (Pi.single c m) + if a = c then Pi.single b m else 0 := by
          funext d
          simp only [tensF, cond_true, Pi.add_apply, tensVd_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = b <;> by_cases h3 : a = c <;>
            simp_all
        rw [e]
        refine S.add_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' b
        · exact S.zero_mem⟩
  intro f hf
  rw [← Finset.univ_sum_single f]
  exact S.sum_mem fun c _ => (hT _).1 (hle (tset_mem.mp hf c)) c

theorem tfg_real {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ X} (hU : IsInfUnitary ε E) {c : ℂ} {v : X}
    (h : casimir E v = c • v) : casimir E v = ((c.re : ℝ) : ℂ) • v := by
  by_cases hv : v = 0
  · simp [hv]
  have h1 : inner ℂ (casimir E v) v = inner ℂ v (casimir E v) := by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have e1 := hU b a v (E b a v)
    have e2 := hU a b (E b a v) v
    have e3 : inner ℂ v (E a b (E b a v)) = starRingEnd ℂ (inner ℂ (E a b (E b a v)) v) :=
      (inner_conj_symm _ _).symm
    rw [e3, e2, map_mul, inner_conj_symm]
    congr 1
    unfold adjSign; split_ifs <;> simp
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h2 := mul_right_cancel₀ (inner_self_ne_zero.mpr hv) h1
  rw [h, Complex.conj_eq_iff_re.mp h2]

theorem tf_closure_stable (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {y : D} (hy : y ∈ genSub E V) :
    ∀ g ∈ UJset ε, ∀ v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure,
      tfRdiag ε g v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure := by
  have hη : ∀ c, (Pi.single c (tfSgn ε c • y) : Fin n → D) ∈ tensSub (genSub E V) := fun c =>
    tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using Submodule.smul_mem _ _ hy
      · simp [h]
  have hco : ∀ c, (fun d => (((Pi.single c (tfSgn ε c • y) : Fin n → D) d : D) : H)) =
      Pi.single c (tfSgn ε c • (y : H)) := fun c => funext fun d => by
    by_cases h : d = c
    · subst h; simp
    · simp [h]
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (hη c) f hf
  simp only [hco] at hce
  have hR := tfRdiag_isURepOn ε
  have hDR := isDerivedOn_smE hR
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, mul_sum, mul_left_comm]) }
  have hΦE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
      Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f =>
    Subtype.ext (vectorL2_ext fun c => by
      refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
      refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
      exact (hce c f.1 f.2).2.1 a b g hg)
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let Ξ := Φ ∘ₗ P'
  have hΞE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Ξ f) =
      Ξ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f => by
    refine (hΦE a b (P' f)).trans (congrArg Φ (Subtype.ext ?_))
    exact (hP.2.1 a b f.1 f.2).symm
  let W : Submodule ℂ (tensSub (n := n) (genSub E V)) := (tensSub V).comap (tensSub (genSub E V)).subtype
  have := hV.1
  have hVle : tensSub (n := n) V ≤ tensSub (genSub E V) := fun f hf =>
    tset_mem.mpr fun c => Submodule.mem_sInf.mpr fun _ hT => hT.1 (tset_mem.mp hf c)
  have hfd : FiniteDimensional ℂ (tensSub (n := n) V) :=
    Module.Finite.of_injective (LinearMap.pi fun c => LinearMap.codRestrict V
      ((LinearMap.proj c : (Fin n → D) →ₗ[ℂ] D) ∘ₗ (tensSub V).subtype) fun f => tset_mem.mp f.2 c)
      (fun f f' h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hW' : FiniteDimensional ℂ W := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hVle).symm
  have hkst : IsKStableSub ε (smE ε (tfRdiag ε)) (W.map Ξ) := by
    rintro a b hab _ ⟨f, hf, rfl⟩
    refine ⟨_, ?_, (hΞE a b f).symm⟩
    have hf' := tset_mem.mp (show f.1 ∈ tensSub V from hf)
    refine tset_mem.mpr fun c => ?_
    show tensF dual E a b f.1 c ∈ V
    cases dual
    · simp only [tensF, cond_false, tensV_coord]
      exact V.add_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' b, V.zero_mem])
    · simp only [tensF, cond_true, tensVd_coord]
      exact V.sub_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' a, V.zero_mem])
  have hcas : ∀ v ∈ W.map Ξ, casimir (smE ε (tfRdiag ε)) v =
      (((((casVal lam : ℝ) : ℂ) + n + 2 * z).re : ℝ) : ℂ) • v := by
    rintro _ ⟨f, -, rfl⟩
    refine tfg_real (isInfUnitary_of_isDerivedOn hR hDR) ?_
    have h3 : diagOp (casimir E) (P f.1) = ((casVal lam : ℝ) : ℂ) • P f.1 := funext fun c => by
      rw [diagOp_coord, casimir_genSub hD.glRep hc _ (tset_mem.mp (hP.1 _ f.2) c)]; rfl
    have h2 : casimir (tensF dual E) (P f.1) = (((casVal lam : ℝ) : ℂ) + n + 2 * z) • P f.1 := by
      rw [add_smul, add_smul, mul_smul, ← hEP f.1 f.2, ← h3]
      cases dual
      · exact LinearMap.congr_fun (casimir_tensV hD.glRep) _
      · exact LinearMap.congr_fun (casimir_tensVd hD.glRep) _
    show casimir _ (Φ (P' f)) = _ • Φ (P' f)
    rw [← map_smul]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hΦE, ← map_sum]
    refine congrArg Φ (Subtype.ext ?_)
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [show ((P' f : tensSub (n := n) (genSub E V)) : Fin n → D) = P f.1 from rfl, ← h2]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply]
  have hgen : genSub (smE ε (tfRdiag ε)) (W.map Ξ) = LinearMap.range Ξ := by
    refine le_antisymm (sInf_le ⟨LinearMap.map_le_range, ?_⟩) ?_
    · rintro a b _ ⟨f, rfl⟩
      exact ⟨_, (hΞE a b f).symm⟩
    · rintro _ ⟨f, rfl⟩
      have h1 := tfg_gen dual E V (((genSub (smE ε (tfRdiag ε)) (W.map Ξ)).comap Ξ).map
        (tensSub (genSub E V)).subtype)
        (fun f hf => ⟨⟨f, hVle hf⟩, Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨_, hf, rfl⟩, rfl⟩)
        (by
          rintro a b _ ⟨f, hf, rfl⟩
          refine ⟨⟨_, tensSub_stable dual a b f.1 f.2⟩, ?_, rfl⟩
          show Ξ _ ∈ genSub _ _
          rw [← hΞE]
          exact tset_genSub_E _ _ a b hf) f.2
      obtain ⟨f', hf', e⟩ := h1
      rwa [← Subtype.ext e]
  have hspan : Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
      v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))} =
      (genSub (smE ε (tfRdiag ε)) (W.map Ξ)).map (smD ε (tfRdiag ε)).subtype := by
    rw [hgen, ← Submodule.span_eq (Submodule.map _ _)]
    congr 1
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨f.1, f.2, rfl⟩
  rw [hspan]
  exact closure_genSub_stable hR hDR inferInstance hkst hcas

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

section TR

variable {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G] {μ : Measure G} [μ.IsInvInvariant]

theorem tf_inner_conj_conj (a b : ℂ) :
    inner ℂ (starRingEnd ℂ a) (starRingEnd ℂ b) = starRingEnd ℂ (inner ℂ a b) := by
  simp only [RCLike.inner_apply, map_mul, Complex.conj_conj]

theorem tf_tr_swap (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hadj : ∀ g x y, inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y))
    (J : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)) (s : Fin n → ℝ)
    (hJ : ∀ x c, J x c = (s c : ℂ) • x c) (hρJ : ∀ g x, ρ g (J x) = J (ρ g x))
    (HP : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) [HP.HasOrthogonalProjection]
    (hst : ∀ g, ∀ v ∈ HP, ρ g v ∈ HP) (d : ℝ) (u w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hu : ∀ c, u c ∈ HP) (hw : ∀ c, w c = (d : ℂ) • HP.starProjection (J (u c)))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    (c c' : Fin n) :
    inner ℂ (u c c') (w c c') = starRingEnd ℂ (inner ℂ (u c' c) (w c' c)) := by
  have hJs : ∀ x y, inner ℂ (J x) y = inner ℂ x (J y) := by
    intro x y
    simp only [PiLp.inner_apply, hJ, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have hP : ∀ v ∈ HP, HP.starProjection v = v := fun v hv => Submodule.starProjection_eq_self_iff.2 hv
  have hwm : ∀ c, w c ∈ HP := fun c => by
    rw [hw c]; exact HP.smul_mem _ (Submodule.starProjection_apply_mem HP _)
  have k1 : ∀ g a b, inner ℂ (w a) (ρ g⁻¹ (u b)) = starRingEnd ℂ (inner ℂ (w b) (ρ g (u a))) := by
    intro g a b
    rw [inner_conj_symm, hw a, hw b, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    calc inner ℂ (HP.starProjection (J (u a))) (ρ g⁻¹ (u b))
        = inner ℂ (J (u a)) (HP.starProjection (ρ g⁻¹ (u b))) :=
          Submodule.inner_starProjection_left_eq_right HP _ _
      _ = inner ℂ (J (u a)) (ρ g⁻¹ (u b)) := by rw [hP _ (hst _ _ (hu b))]
      _ = inner ℂ (u a) (ρ g⁻¹ (J (u b))) := by rw [hJs, hρJ]
      _ = inner ℂ (ρ g (u a)) (J (u b)) := (hadj _ _ _).symm
      _ = inner ℂ (HP.starProjection (ρ g (u a))) (J (u b)) := by rw [hP _ (hst _ _ (hu a))]
      _ = inner ℂ (ρ g (u a)) (HP.starProjection (J (u b))) :=
          Submodule.inner_starProjection_left_eq_right HP _ _
  have k2 : ∀ g a b, inner ℂ (w a) (ρ g⁻¹ (w b)) = starRingEnd ℂ (inner ℂ (w b) (ρ g (w a))) := by
    intro g a b
    rw [inner_conj_symm, hadj]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  have e1 : ∫ g, inner ℂ ((u c c' : Lp ℂ 2 μ) g) ((w c c' : Lp ℂ 2 μ) g) ∂μ =
      ∫ g, inner ℂ (inner ℂ (w c') (ρ g (u c))) (inner ℂ (w c') (ρ g (w c))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hrep _ (hu c) c', hrep _ (hwm c) c'] with g h1 h2
    rw [h1, h2]
  have e2 : ∫ g, starRingEnd ℂ (inner ℂ ((u c' c : Lp ℂ 2 μ) g) ((w c' c : Lp ℂ 2 μ) g)) ∂μ =
      ∫ g, starRingEnd ℂ (inner ℂ (inner ℂ (w c) (ρ g (u c'))) (inner ℂ (w c) (ρ g (w c')))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hrep _ (hu c') c, hrep _ (hwm c') c] with g h1 h2
    rw [h1, h2]
  rw [e1, e2, ← integral_inv_eq_self _ μ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [k1, k2, tf_inner_conj_conj]

end TR

section Core

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_single_smul_mem {D : Submodule ℂ H} {S : Submodule ℂ D} (c : Fin n) (a : ℂ) {y : D} (hy : y ∈ S) :
    (Pi.single c (a • y) : Fin n → D) ∈ tensSub S := by
  rw [tset_mem]
  intro i
  by_cases h : i = c
  · subst h; simpa using S.smul_mem a hy
  · simp [h]

theorem tf_coe_single {D : Submodule ℂ H} (c : Fin n) (a : ℂ) (y : D) :
    (fun i => (((Pi.single c (a • y) : Fin n → D) i : D) : H)) = Pi.single c (a • (y : H)) := by
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem tf_coe_single' {D : Submodule ℂ H} (c : Fin n) (y : D) :
    (fun i => (((Pi.single c y : Fin n → D) i : D) : H)) = Pi.single c (y : H) := by
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem tf_ph_memLp (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {y : D} (hy : y ∈ genSub E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) (c : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
      (fun d => ((f d : D) : H)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have h := ((coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (tf_single_smul_mem c (tfSgn ε c) hy) f hf).1).2 []
  rw [tf_coe_single] at h
  exact h

theorem tfRdiag_tfPh (dual : Bool) {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε) (y : H) (ζ : Fin n → H) :
    tfRdiag ε h (tfPh dual ε σ y ζ) = tfPh dual ε σ y (tensGrp dual σ h ζ) := by
  refine vectorL2_ext fun c => ?_
  rw [tfRdiag_apply, tfPh_apply, tfPh_apply, rightRegular_toL2 ε _ hh]
  refine toL2_congr_of_eq_on_UJset fun x hx => ?_
  simp only [coefMap]
  rw [tf_tensGrp_mul dual hσ hx hh]

theorem tfJ_inner (ε : Fin n → Bool) (x x' : tfL2n ε) : inner ℂ (tfJ ε x) x' = inner ℂ x (tfJ ε x') := by
  simp only [PiLp.inner_apply, tfJ_apply, inner_smul_left, inner_smul_right]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  exact tf_star_sgn ε i

theorem tfFormBH_sub_left (ε : Fin n → Bool) (f f' g : Fin n → H) :
    tfFormBH ε (f - f') g = tfFormBH ε f g - tfFormBH ε f' g := by
  simp only [tfFormBH, Pi.sub_apply, inner_sub_left, mul_sub, sum_sub_distrib]

end Core

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_trace_data (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) :
    ∃ (HP : Submodule ℂ (tfL2n ε)) (w : Fin n → tfL2n ε), IsClosed (HP : Set (tfL2n ε)) ∧
      HP = (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure ∧
      (∀ g ∈ UJset ε, ∀ v ∈ HP, tfRdiag ε g v ∈ HP) ∧
      (∀ v ∈ HP, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v)) ∧
      c0 = (((∑ c, ‖w c‖ ^ 2) / d : ℝ) : ℂ) := by
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  have hdpos : 0 < d := hd.1
  have hst0 := closGen_stable hgap hσ hD hV hc hVK

  set S : Submodule ℂ (tfL2n ε) := Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
    v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))} with hS
  set HP : Submodule ℂ (tfL2n ε) := S.topologicalClosure with hHP
  have hHPc : IsClosed (HP : Set (tfL2n ε)) := S.isClosed_topologicalClosure
  have : CompleteSpace HP := hHPc.completeSpace_coe
  have hst : ∀ g ∈ UJset ε, ∀ v ∈ HP, tfRdiag ε g v ∈ HP :=
    tf_closure_stable dual hσ hD hsm hgap hV hc hVK hW hP hEP hyG
  have hSHP : S ≤ HP := S.le_topologicalClosure
  have hPm : ∀ f ∈ tensSub (genSub E V), P f ∈ tensSub (genSub E V) := hP.1
  have hcoeC : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c : Fin n, ((f c : D) : H) ∈ closGen E V := fun f hf c =>
    Submodule.le_topologicalClosure _ ⟨f c, (tset_mem.1 hf) c, rfl⟩
  have hmem := fun {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) =>
    tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf

  have hT2 := fun {ζ ζ' : Fin n → H} (hζ : ∀ c, ζ c ∈ closGen E V) (hζ' : ∀ c, ζ' c ∈ closGen E V)
    (hm : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hm' : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ' (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) =>
    tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC hζ hζ' hm hm'

  set Nr : ℝ := ‖(y : H)‖ ^ 2 with hNr
  have hNpos : 0 < Nr := pow_pos (norm_pos_iff.2 hy0) 2
  have hNc : inner ℂ (y : H) (y : H) = (Nr : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hNr, Complex.ofReal_pow]
    rfl
  set κ : ℝ := d / Nr with hκ
  have hκpos : 0 < κ := div_pos hdpos hNpos
  have hsing : ∀ b, (Pi.single b y : Fin n → D) ∈ tensSub (genSub E V) := fun b => by
    simpa using tf_single_smul_mem b (1 : ℂ) hyG
  set u : Fin n → tfL2n ε := fun b => tfPh dual ε σ (y : H) (fun c => ((P (Pi.single b y) c : D) : H)) with hu
  have huHP : ∀ b, u b ∈ HP := fun b => hSHP (Submodule.subset_span ⟨_, hsing b, rfl⟩)
  set a : Fin n → tfL2n ε := fun b => HP.starProjection (tfJ ε (u b)) with ha
  set w : Fin n → tfL2n ε := fun b => (κ : ℂ) • a b with hw
  have haHP : ∀ b, a b ∈ HP := fun b => Submodule.starProjection_apply_mem HP _
  have hwHP : ∀ b, w b ∈ HP := fun b => HP.smul_mem _ (haHP b)
  have hPself : ∀ v ∈ HP, HP.starProjection v = v := fun v hv => Submodule.starProjection_eq_self_iff.2 hv
  have hproj : ∀ x v, v ∈ HP → inner ℂ (HP.starProjection x) v = inner ℂ x v := by
    intro x v hv
    rw [Submodule.inner_starProjection_left_eq_right HP, hPself v hv]
  have hsubι : ∀ f g : Fin n → D, (fun c => (((f - g) c : D) : H)) =
      (fun c => ((f c : D) : H)) - (fun c => ((g c : D) : H)) := by
    intro f g; funext c; simp

  have hA : ∀ η ∈ tensSub (genSub E V), ∀ v ∈ HP,
      inner ℂ (tfJ ε (tfPh dual ε σ (y : H) (fun c => (((η - P η) c : D) : H)))) v = 0 := by
    intro η hη
    have hη' : η - P η ∈ tensSub (genSub E V) := Submodule.sub_mem _ hη (hPm η hη)
    set q := tfJ ε (tfPh dual ε σ (y : H) (fun c => (((η - P η) c : D) : H))) with hq
    have hle : S ≤ (ℂ ∙ q)ᗮ := by
      rw [hS, Submodule.span_le]
      rintro v ⟨f, hf, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, hq, tfJ_inner,
        hT2 (hcoeC _ hη') (hcoeC _ (hPm f hf)) (hmem hη') (hmem (hPm f hf)), hsubι, tfFormBH_sub_left,
        ← hPB η hη f hf, hPB η hη (P f) (hPm f hf), hPP f hf, ← hPB η hη f hf, sub_self, zero_mul, zero_div]
    intro v hv
    have h2 : v ∈ (ℂ ∙ q)ᗮ := Submodule.topologicalClosure_minimal S hle (Submodule.isClosed_orthogonal _) hv
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h2)

  have hcoefS : ∀ (c : Fin n) (ζ : Fin n → H) (g : Matrix (Fin n) (Fin n) ℂ),
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ g = tfSgn ε c * inner ℂ (y : H) (tensGrp dual σ g ζ c) := by
    intro c ζ g
    unfold coefMap
    rw [sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same, inner_smul_left]
    congr 1
    exact tf_star_sgn ε c
  have hformS : ∀ (c : Fin n) (ζ : Fin n → H),
      tfFormBH ε (fun i => (((Pi.single c y : Fin n → D) i : D) : H)) ζ = tfSgn ε c * inner ℂ (y : H) (ζ c) := by
    intro c ζ
    rw [tf_coe_single', tfFormBH_single_left]

  have htr : ∀ f ∈ tensSub (genSub E V), ∀ g : Formalism.REAL.UJ ε,
      (∀ c, tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H)) c ∈ closGen E V) ∧
      ∀ c, MemLp (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
        (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) (Formalism.MainNotions.S.umat x)) 2 (Formalism.REAL.muG ε) := by
    intro f hf g
    refine ⟨fun c => ?_, fun c => ?_⟩
    · rw [tf_tensGrp_apply]
      exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
        (hst0 _ (umat_mem_UJset ε g) _ (hcoeC _ (hPm f hf) d))
    · have h1 := (hmem (hPm f hf) c).comp_measurePreserving (measurePreserving_mul_right ε g)
      have e : (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
          (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) (Formalism.MainNotions.S.umat x)) =
          (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
            (fun i => ((P f i : D) : H)) (Formalism.MainNotions.S.umat x)) ∘ (fun x => x * g) := by
        funext x
        simp only [Function.comp_apply, coefMap]
        rw [show Formalism.MainNotions.S.umat (x * g) = Formalism.MainNotions.S.umat x * Formalism.MainNotions.S.umat g from rfl,
          tf_tensGrp_mul dual hσ (umat_mem_UJset ε x) (umat_mem_UJset ε g)]
      rw [e]
      exact h1

  have hrepGen : ∀ f ∈ tensSub (genSub E V), ∀ c,
      ((tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H)) c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) (tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H)))) := by
    intro f hf c
    filter_upwards [coe_toL2_ae_eq_of_memLp (hmem (hPm f hf) c)] with g hg
    rw [tfPh_apply, hg]
    obtain ⟨hζC, hζm⟩ := htr f hf g
    have hRv : tfRdiag ε (Formalism.MainNotions.S.umat g) (tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H))) ∈ HP :=
      hst _ (umat_mem_UJset ε g) _ (hSHP (Submodule.subset_span ⟨f, hf, rfl⟩))
    have hs' : Pi.single c y - P (Pi.single c y) ∈ tensSub (genSub E V) :=
      Submodule.sub_mem _ (hsing c) (hPm _ (hsing c))
    have hA1 := hA _ (hsing c) _ hRv
    rw [tfRdiag_tfPh dual hσ (umat_mem_UJset ε g), tfJ_inner,
      hT2 (hcoeC _ hs') hζC (hmem hs') hζm, hsubι, tfFormBH_sub_left] at hA1
    have hA2 : tfFormBH ε (fun i => (((Pi.single c y : Fin n → D) i : D) : H))
        (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) =
        tfFormBH ε (fun i => ((P (Pi.single c y) i : D) : H))
          (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) := by
      have hne : (inner ℂ (y : H) (y : H)) / (d : ℂ) ≠ 0 := by
        rw [hNc]
        exact div_ne_zero (Complex.ofReal_ne_zero.2 hNpos.ne') (Complex.ofReal_ne_zero.2 hdpos.ne')
      rw [mul_div_assoc] at hA1
      exact sub_eq_zero.1 ((mul_eq_zero.1 hA1).resolve_right hne)
    rw [hcoefS, ← hformS, hA2, hw]
    simp only
    rw [inner_smul_left, Complex.conj_ofReal, ha]
    simp only
    rw [hproj _ _ hRv, tfJ_inner, tfRdiag_tfPh dual hσ (umat_mem_UJset ε g), hu]
    simp only
    rw [hT2 (hcoeC _ (hPm _ (hsing c))) hζC (hmem (hPm _ (hsing c))) hζm, hNc]
    have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdpos.ne'
    have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
    rw [hκ, Complex.ofReal_div]
    field_simp

  have hrepS : ∀ v ∈ S, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact hrepGen f hf
    | zero =>
      intro c
      filter_upwards [Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε)] with g hg
      rw [map_zero, inner_zero_right]
      exact hg
    | add x x' _ _ hx hx' =>
      intro c
      filter_upwards [Lp.coeFn_add (x c) (x' c), hx c, hx' c] with g h1 h2 h3
      rw [map_add, inner_add_right, ← h2, ← h3, ← Pi.add_apply, ← h1]
      rfl
    | smul r x _ hx =>
      intro c
      filter_upwards [Lp.coeFn_smul r (x c), hx c] with g h1 h2
      rw [map_smul, inner_smul_right, ← h2, ← smul_eq_mul, ← Pi.smul_apply, ← h1]
      rfl
  have hrep : ∀ v ∈ HP, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v) :=
    tf_rep_closure (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g))
      (fun g x => le_of_eq ((tfRdiag_isURepOn ε).2.1 _ (umat_mem_UJset ε g) x)) w S hrepS

  have hT1 : c0 * (Nr : ℂ) = ∑ b, tfSgn ε b *
      tfFormBH ε (fun i => ((P (Pi.single b y) i : D) : H)) (fun i => ((P (Pi.single b y) i : D) : H)) := by
    have h1 : inner ℂ (y : H) ((ptr P y : D) : H) = c0 * (Nr : ℂ) := by
      rw [hc0 y hyG, Submodule.coe_smul, inner_smul_right, hNc]
    rw [← h1, ptr_apply, Submodule.coe_sum, inner_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [hPB _ (hsing b) _ (hPm _ (hsing b)), hPP _ (hsing b), hformS, ← mul_assoc, tfSgn_mul_self, one_mul]
  have hub : ∀ b, inner ℂ (u b) (w b) =
      tfFormBH ε (fun i => ((P (Pi.single b y) i : D) : H)) (fun i => ((P (Pi.single b y) i : D) : H)) := by
    intro b
    rw [hw]
    simp only
    rw [inner_smul_right, ha]
    simp only
    rw [← Submodule.inner_starProjection_left_eq_right HP, hPself _ (huHP b), hu]
    simp only
    rw [hT2 (hcoeC _ (hPm _ (hsing b))) (hcoeC _ (hPm _ (hsing b))) (hmem (hPm _ (hsing b)))
      (hmem (hPm _ (hsing b))), hNc]
    have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdpos.ne'
    have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
    rw [hκ, Complex.ofReal_div]
    field_simp

  have hone : tfRdiag ε (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := (tfRdiag_isURepOn ε).1.1
  have hmul : ∀ a b : Formalism.REAL.UJ ε, tfRdiag ε (Formalism.MainNotions.S.umat (a * b)) =
      (tfRdiag ε (Formalism.MainNotions.S.umat a)).comp (tfRdiag ε (Formalism.MainNotions.S.umat b)) := fun a b =>
    (tfRdiag_isURepOn ε).1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ (g : Formalism.REAL.UJ ε) v, ‖tfRdiag ε (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ := fun g v =>
    (tfRdiag_isURepOn ε).2.1 _ (umat_mem_UJset ε g) v
  have hadj : ∀ (g : Formalism.REAL.UJ ε) (x x' : tfL2n ε), inner ℂ (tfRdiag ε (Formalism.MainNotions.S.umat g) x) x' =
      inner ℂ x (tfRdiag ε (Formalism.MainNotions.S.umat g⁻¹) x') := by
    intro g x x'
    have hs := GraphTrick.star_eq (ρ := fun g : Formalism.REAL.UJ ε => tfRdiag ε (Formalism.MainNotions.S.umat g)) hone hmul hiso g
    rw [← hs, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hJr : ∀ (x : tfL2n ε) c, tfJ ε x c = (((if ε c then (1 : ℝ) else -1 : ℝ)) : ℂ) • x c := by
    intro x c
    rw [tfJ_apply]
    congr 1
    unfold tfSgn
    split_ifs <;> simp
  have hswap := tf_tr_swap (μ := Formalism.REAL.muG ε) (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g)) hadj (tfJ ε)
    (fun c => if ε c then (1 : ℝ) else -1) hJr (fun g x => tfRdiag_tfJ ε _ x) HP
    (fun g v hv => hst _ (umat_mem_UJset ε g) v hv) κ u w huHP (fun c => rfl) hrep

  have hJu : ∀ c', starRingEnd ℂ (inner ℂ (tfJ ε (u c')) (w c')) =
      ∑ b, tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) := by
    intro c'
    rw [PiLp.inner_apply, map_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [tfJ_apply, inner_smul_left, map_mul, Complex.conj_conj]
  have haa : ∀ c', inner ℂ (tfJ ε (u c')) (w c') = (κ : ℂ) * ((‖a c'‖ ^ 2 : ℝ) : ℂ) := by
    intro c'
    rw [hw]
    simp only
    rw [inner_smul_right, ha]
    simp only
    rw [← hproj _ _ (Submodule.starProjection_apply_mem HP (tfJ ε (u c'))), inner_self_eq_norm_sq_to_K,
      Complex.ofReal_pow]
    rfl
  set T : ℝ := ∑ c', ‖a c'‖ ^ 2 with hT
  have hTnn : 0 ≤ T := sum_nonneg fun c' _ => sq_nonneg _
  have hmain : c0 * (Nr : ℂ) = ((κ * T : ℝ) : ℂ) := by
    rw [hT1, sum_congr rfl fun b _ => by rw [← hub b]]
    have e1 : ∀ b, tfSgn ε b * inner ℂ (u b) (w b) =
        ∑ c', tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) := by
      intro b
      rw [PiLp.inner_apply, mul_sum]
      exact sum_congr rfl fun c' _ => by rw [hswap b c']
    rw [sum_congr rfl fun b _ => e1 b, sum_comm]
    have e : ∀ c', ∑ b, tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) =
        (κ : ℂ) * ((‖a c'‖ ^ 2 : ℝ) : ℂ) := by
      intro c'
      rw [← hJu, haa, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [sum_congr rfl fun c' _ => e c', ← mul_sum, hT]
    push_cast
    rfl
  have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
  have hc0eq : c0 = ((κ * T / Nr : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, ← hmain]
    field_simp
  have hwT : ∑ c', ‖w c'‖ ^ 2 = κ ^ 2 * T := by
    rw [hT, mul_sum]
    refine sum_congr rfl fun c' _ => ?_
    rw [hw]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hκpos.le, mul_pow]
  refine ⟨HP, w, hHPc, rfl, hst, hrep, ?_⟩
  rw [hc0eq, hwT]
  congr 1
  rw [hκ]
  field_simp

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_ph_inj (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : D} (hyG : y ∈ genSub E V) (hy0 : (y : H) ≠ 0) {g0 : Fin n → D} (hg0m : g0 ∈ tensSub (genSub E V))
    (h0 : tfPh dual ε σ (y : H) (fun i => ((g0 i : D) : H)) = 0) : g0 = 0 := by
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  have hcoeC : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c : Fin n, ((f c : D) : H) ∈ closGen E V :=
    fun f hf c => Submodule.le_topologicalClosure _ ⟨f c, (tset_mem.1 hf) c, rfl⟩
  set f2 : Fin n → D := fun c => tfSgn ε c • g0 c with hf2
  have hf2m : f2 ∈ tensSub (genSub E V) := by
    rw [tset_mem]; intro c; exact Submodule.smul_mem _ _ ((tset_mem.1 hg0m) c)
  have hT2b := tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC (hcoeC _ hf2m) (hcoeC _ hg0m)
    (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf2m) (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hg0m)
  rw [h0, map_zero, inner_zero_right] at hT2b
  have hform : tfFormBH ε (fun i => ((f2 i : D) : H)) (fun i => ((g0 i : D) : H)) =
      ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) := by
    unfold tfFormBH
    push_cast
    refine sum_congr rfl fun c _ => ?_
    rw [hf2]
    simp only [Submodule.coe_smul, inner_smul_left, ← mul_assoc, inner_self_eq_norm_sq_to_K]
    rw [show (starRingEnd ℂ) (tfSgn ε c) = tfSgn ε c from tf_star_sgn ε c, tfSgn_mul_self, one_mul]
    rfl
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  have hN0 : inner ℂ (y : H) (y : H) ≠ 0 := inner_self_ne_zero.2 hy0
  rw [hform] at hT2b
  have hs0 : (∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) = 0 := by
    have h1 : ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) = 0 := by
      have h2 := hT2b.symm
      rw [mul_div_assoc] at h2
      exact (mul_eq_zero.1 h2).resolve_right (div_ne_zero hN0 hd0)
    exact_mod_cast h1
  funext c
  have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖((g0 i : D) : H)‖)).1 hs0 c (mem_univ _)
  have h2 : ((g0 c : D) : H) = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  exact Subtype.ext h2

theorem tf_trace_core (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) :
    ∃ r : ℝ, 0 ≤ r ∧ c0 = r ∧ (c0 = 0 → ∀ b, P (Pi.single b y) = 0) := by
  obtain ⟨d, hd⟩ := tfClRep_fdeg hgap hσ hD hV hc hVK (tf_sqInt_of_hW hσ hD hgap hV hc hVK hW)
  obtain ⟨HP, w, -, hHPeq, -, hrep, hc0eq⟩ :=
    tf_trace_data dual hσ hD hsm hgap hV hc hVK hW hP hPP hPB hEP hc0 hyV hy0 hd
  have hdpos : 0 < d := hd.1
  refine ⟨(∑ c, ‖w c‖ ^ 2) / d, div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hdpos.le, hc0eq, fun h0 b => ?_⟩
  have hT0 : ∑ c, ‖w c‖ ^ 2 = 0 := by
    rw [h0] at hc0eq
    have h1 : (∑ c, ‖w c‖ ^ 2) / d = 0 := by exact_mod_cast hc0eq.symm
    exact (div_eq_zero_iff.1 h1).resolve_right hdpos.ne'
  have hw0 : ∀ c, w c = 0 := by
    intro c
    have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖w i‖)).1 hT0 c (mem_univ _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  have hHP0 : ∀ v ∈ HP, v = 0 := by
    intro v hv
    refine vectorL2_ext fun c => ?_
    have h1 := hrep v hv c
    simp only [hw0, inner_zero_left] at h1
    exact Lp.ext (h1.trans (Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε)).symm)
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hsing : (Pi.single b y : Fin n → D) ∈ tensSub (genSub E V) := by
    simpa using tf_single_smul_mem b (1 : ℂ) hyG
  have hmemHP : tfPh dual ε σ (y : H) (fun i => ((P (Pi.single b y) i : D) : H)) ∈ HP := by
    rw [hHPeq]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, hsing, rfl⟩)
  exact tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hyG hy0 (hP.1 _ hsing) (hHP0 _ hmemHP)

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_ge_abstract {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (HP H' : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) (hH'c : IsClosed (H' : Set (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))))
    (hH'P : H' ≤ HP) (hH'st : ∀ g, ∀ v ∈ H', ρ g v ∈ H') (hH'0 : H' ≠ ⊥)
    (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    {d' : ℝ} (hd' : 0 < d')
    (hschur : ∀ x ∈ H', ∀ v ∈ H', ∫ g, ‖inner ℂ x (ρ g v)‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖v‖ ^ 2 / d') :
    d' ≤ ∑ c, ‖w c‖ ^ 2 ∧ (∑ c, ‖w c‖ ^ 2 = d' → HP ≤ H') := by
  have : CompleteSpace H' := hH'c.completeSpace_coe
  set Pw : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) := fun c => H'.starProjection (w c) with hPw
  have hPwm : ∀ c, Pw c ∈ H' := fun c => H'.starProjection_apply_mem (w c)
  have horth : ∀ c, ∀ y ∈ H', inner ℂ (w c - Pw c) y = 0 := fun c y hy =>
    H'.starProjection_inner_eq_zero (w c) y hy
  have hinnerP : ∀ c, ∀ y ∈ H', inner ℂ (w c) y = inner ℂ (Pw c) y := fun c y hy => by
    have := horth c y hy
    rwa [inner_sub_left, sub_eq_zero] at this
  have hpyth : ∀ c, ‖w c‖ ^ 2 = ‖Pw c‖ ^ 2 + ‖w c - Pw c‖ ^ 2 := fun c => by
    have h0 : inner ℂ (Pw c) (w c - Pw c) = 0 := by
      rw [← inner_conj_symm, horth c _ (hPwm c), map_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Pw c) (w c - Pw c) h0
    rw [add_sub_cancel] at this
    simp only [sq]; linarith
  have hL2 : ∀ f : Lp ℂ 2 μ, ‖f‖ ^ 2 = ∫ g, ‖(f : G → ℂ) g‖ ^ 2 ∂μ := fun f => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
      ← integral_re (MeasureTheory.L2.integrable_inner f f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ((f : G → ℂ) g)
  have hcomp : ∀ v ∈ H', ∀ c, ‖v c‖ ^ 2 = ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := fun v hv c => by
    rw [hL2, ← hschur (Pw c) (hPwm c) v hv]
    refine integral_congr_ae ?_
    filter_upwards [hrep v (hH'P hv) c] with g hg
    rw [hg, hinnerP c _ (hH'st g v hv)]
  have hkey : ∀ v ∈ H', ‖v‖ ^ 2 = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := fun v hv => by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Lp ℂ 2 μ) v
    calc ‖v‖ ^ 2 = ∑ c, ‖v c‖ ^ 2 := h
      _ = ∑ c, ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := Finset.sum_congr rfl fun c _ => hcomp v hv c
      _ = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := by rw [Finset.sum_mul, Finset.sum_div]
  obtain ⟨v0, hv0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH'0
  have hsum : ∑ c, ‖Pw c‖ ^ 2 = d' := by
    have h := hkey v0 hv0
    have hn : ‖v0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
    field_simp at h
    nlinarith [h, hn, sq_nonneg ‖v0‖]
  refine ⟨hsum ▸ Finset.sum_le_sum fun c _ => by rw [hpyth c]; nlinarith [sq_nonneg ‖w c - Pw c‖], fun heq => ?_⟩
  have hwc : ∀ c, w c ∈ H' := by
    have h0 : ∑ c, ‖w c - Pw c‖ ^ 2 = 0 := by
      have := congrArg (fun t => t - d') heq
      simp only [sub_self] at this
      rw [← this, ← hsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [hpyth c]; ring
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg ‖w c - Pw c‖).mp h0 c (Finset.mem_univ c)
    have h1 : w c - Pw c = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [sub_eq_zero.mp h1]; exact hPwm c
  have hadj : ∀ g (a b : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), inner ℂ a (ρ g b) = inner ℂ (ρ g⁻¹ a) b := fun g a b => by
    let L : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗᵢ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) :=
      ⟨(ρ g : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), hiso g⟩
    have e : ρ g (ρ g⁻¹ a) = a := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
    conv_lhs => rw [← e]
    exact L.inner_map_map _ _
  intro v hv
  set u := v - H'.starProjection v with hu
  have huP : u ∈ HP := HP.sub_mem hv (hH'P (H'.starProjection_apply_mem v))
  have hu0 : ∀ c, ((u c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] 0 := fun c => by
    filter_upwards [hrep u huP c] with g hg
    rw [hg, hadj, Pi.zero_apply]
    have := H'.starProjection_inner_eq_zero v _ (hH'st g⁻¹ _ (hwc c))
    rw [← inner_conj_symm, this, map_zero]
  have hu' : u = 0 := by
    refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
    funext c
    exact Lp.eq_zero_iff_ae_eq_zero.mpr (hu0 c)
  have : v = H'.starProjection v := sub_eq_zero.mp hu'
  rw [this]; exact H'.starProjection_apply_mem v

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_schur_transfer {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (S₁ : Submodule ℂ H₁) [S₁.HasOrthogonalProjection] (S₂ : Submodule ℂ H₂) (U : S₁ ≃ₗᵢ[ℂ] S₂)
    (hU : ∀ g ∈ UJset ε, ∀ x y : S₁, (x : H₁) = σ₁ g (y : H₁) → ((U x : S₂) : H₂) = σ₂ g ((U y : S₂) : H₂))
    (hS₁ : ∀ g ∈ UJset ε, ∀ x ∈ S₁, σ₁ g x ∈ S₁) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ₁ S₁) d) :
    ∀ x ∈ S₂, ∀ v ∈ S₂, ∫ g : Formalism.REAL.UJ ε, ‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 ∂(Formalism.REAL.muG ε) =
      ‖x‖ ^ 2 * ‖v‖ ^ 2 / d := by
  intro x hx v hv
  set x1 : S₁ := U.symm ⟨x, hx⟩ with hx1
  set v1 : S₁ := U.symm ⟨v, hv⟩ with hv1
  have ex : ((U x1 : S₂) : H₂) = x := by rw [hx1, LinearIsometryEquiv.apply_symm_apply]
  have ev : ((U v1 : S₂) : H₂) = v := by rw [hv1, LinearIsometryEquiv.apply_symm_apply]
  have hcoef : ∀ g : Formalism.REAL.UJ ε, inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g := by
    intro g
    have hg := umat_mem_UJset ε g
    set y : S₁ := ⟨σ₁ (Formalism.MainNotions.S.umat g) (v1 : H₁), hS₁ _ hg _ v1.2⟩ with hy
    have h1 := hU _ hg y v1 rfl
    rw [← ex, ← ev, ← h1, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    show inner ℂ x1 y = inner ℂ x1 (tfClRep σ₁ S₁ (Formalism.MainNotions.S.umat g) v1)
    congr 1
    exact Subtype.ext (tfClRep_coe σ₁ S₁ (hS₁ _ hg) v1).symm
  obtain ⟨-, hint, hval⟩ := hd.1, (hd.2 v1 x1 v1 x1).1, (hd.2 v1 x1 v1 x1).2
  have hnx : ‖x‖ = ‖x1‖ := by rw [← ex]; exact U.norm_map x1
  have hnv : ‖v‖ = ‖v1‖ := by rw [← ev]; exact U.norm_map v1
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ g : Formalism.REAL.UJ ε, ((‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 : ℝ) : ℂ) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g * star (Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g) := by
    intro g
    rw [hcoef, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  have h1 : inner ℂ v1 v1 = ((‖v1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : inner ℂ x1 x1 = ((‖x1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hval, h1, h2, hnx, hnv]
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_kstable_fin (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V0 : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V0) (hVK : IsKStableSub ε E V0) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : D} (hv : v ∈ V0) : σ k (v : H) ∈ V0.map D.subtype := by
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk
  have hE := hD.glRep
  have hv0 : v ∈ layer ε E V0 0 := hv
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_inK hE hVK hVf hZ 0
  have hs : Summable fun m : ℕ => C ^ m * ‖v‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_right ‖v‖
    refine this.congr fun m => ?_
    simp
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv0 m) 0 1 hs
  rw [exp_zero_smul, hσ.1.1] at hsum
  simp only [Complex.ofReal_one, one_smul, ContinuousLinearMap.one_apply] at hsum
  have : FiniteDimensional ℂ (V0.map D.subtype) := Module.Finite.map _ _
  have hcl : IsClosed ((V0.map D.subtype : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
  refine hcl.mem_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_map_of_mem (actM_pow_mem_layer_of_inK hE hVK hZ hv0 m)

theorem tf_tensGrp_kDiag (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ k f = kDiag dual σ k f := by
  have hu : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hu
  funext c
  simp only [tensGrp, kDiag, hinv, Matrix.conjTranspose_apply]

theorem tf_kirr_map {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    {E₁ : Fin n → Fin n → Module.End ℂ M} {E₂ : Fin n → Fin n → Module.End ℂ M'} {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E₁ Λ V) (Ψ : M →ₗ[ℂ] M')
    (hΨ : ∀ a b, ∀ x ∈ V, Ψ (E₁ a b x) = E₂ a b (Ψ x)) (hinj : ∀ x ∈ V, Ψ x = 0 → x = 0) :
    IsKIrrHW ε E₂ Λ (V.map Ψ) := by
  have := hV.1
  refine ⟨Module.Finite.map _ _, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨x, hx, rfl⟩
    exact ⟨E₁ a b x, hV.2.1 a b hab x hx, hΨ a b x hx⟩
  · intro S' hS' hst
    have hT : IsKStableSub ε E₁ (S'.comap Ψ ⊓ V) := by
      rintro a b hab x ⟨hx1, hx2⟩
      refine ⟨?_, hV.2.1 a b hab x hx2⟩
      show Ψ (E₁ a b x) ∈ S'
      rw [hΨ a b x hx2]
      exact hst a b hab _ hx1
    rcases hV.2.2.1 _ inf_le_right hT with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨x, hx, rfl⟩ := hS' hs
      have hx0 : x ∈ S'.comap Ψ ⊓ V := ⟨hs, hx⟩
      rw [h, Submodule.mem_bot] at hx0
      rw [hx0, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ S'.comap Ψ ⊓ V := by rw [h]; exact hx
      exact hx'.1
  · obtain ⟨w, hwV, hw0, hw1, hw2⟩ := hV.2.2.2
    refine ⟨Ψ w, ⟨w, hwV, rfl⟩, fun h => hw0 (hinj w hwV h), fun a => ?_, fun a b hab h => ?_⟩
    · rw [← hΨ a a w hwV, hw1 a, map_smul]
    · rw [← hΨ a b w hwV, hw2 a b hab h, map_zero]

theorem tf_kfin_tens (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ f ∈ W ∧ W ≤ tensSub (genSub E V) ∧
      ∀ k ∈ Kset ε, ∀ w ∈ W, ∃ w' ∈ W,
        (fun c => ((w' c : D) : H)) = kDiag dual σ k (fun c => ((w c : D) : H)) := by
  have hE := hD.glRep
  have hmono : Monotone (layer ε E V) := fun k l hkl => layer_mono hkl
  have hlay : ∀ c, ∃ m, f c ∈ layer ε E V m := fun c => by
    have h1 := (tset_mem.1 hf) c
    rw [genSub_eq_iSup_layer hE hVk] at h1
    exact (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 h1
  choose m hm using hlay
  set M := Finset.univ.sup m with hM
  have hfM : ∀ c, f c ∈ layer ε E V M := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hLf : FiniteDimensional ℂ (layer ε E V M) := finiteDimensional_layer hVf M
  have hLk : IsKStableSub ε E (layer ε E V M) := layer_kStable hE hVk M
  refine ⟨tensSub (layer ε E V M), ?_, tset_mem.2 hfM,
    fun w hw => tset_mem.2 fun c => layer_le_genSub M ((tset_mem.1 hw) c), ?_⟩
  · exact Module.Finite.of_injective (LinearMap.pi fun c => LinearMap.codRestrict (layer ε E V M)
      ((LinearMap.proj c : (Fin n → D) →ₗ[ℂ] D) ∘ₗ (tensSub (layer ε E V M)).subtype) fun f => tset_mem.mp f.2 c)
      (fun f f' h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  · intro k hk w hw
    have hu : ∀ d, ∃ u ∈ layer ε E V M, (u : H) = σ k ((w d : D) : H) := fun d => by
      obtain ⟨u, hu, e⟩ := tf_kstable_fin hσ hD hLf hLk hk ((tset_mem.1 hw) d)
      exact ⟨u, hu, e⟩
    choose u hu hue using hu
    refine ⟨fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • u d,
      tset_mem.2 fun c => Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hu d), ?_⟩
    funext c
    simp only [kDiag, Submodule.coe_sum, Submodule.coe_smul, hue]

section Datum

variable [CompleteSpace H]

theorem tf_phi (dual : Bool) {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {y : D} (hy : y ∈ genSub E V) :
    ∃ Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε),
      (∀ f, ((Φ f : smD ε (tfRdiag ε)) : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H))) ∧
      ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
        Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := by
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _
    (tf_single_smul_mem c (tfSgn ε c) hy) f hf
  simp only [tf_coe_single] at hce
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, mul_sum, mul_left_comm]) }
  refine ⟨Φ, fun f => rfl, fun a b f => Subtype.ext (vectorL2_ext fun c => ?_)⟩
  refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
  refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
  exact (hce c f.1 f.2).2.1 a b g hg

end Datum

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_datum2 (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {V' : Submodule ℂ D} (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    ∃ V₂ : Submodule ℂ (smD ε (tfRdiag ε)), IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂ ∧
      (∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v) ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v) ∧ V₂ ≠ ⊥ ∧
      (∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) ∧
      (∀ x ∈ genSub E V', ∃ v ∈ genSub (smE ε (tfRdiag ε)) V₂,
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) := by
  obtain ⟨Φ, hΦ, hΦE⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (tensSub (n := n) (genSub E V))
  let π := Submodule.linearProjOfIsCompl _ q hq
  let Ψ : D →ₗ[ℂ] smD ε (tfRdiag ε) := Φ ∘ₗ π ∘ₗ ι
  have hΨ : ∀ x (hx : x ∈ genSub E V'), Ψ x = Φ ⟨ι x, hι.1 x hx⟩ := by
    intro x hx
    show Φ (π (ι x)) = _
    congr 1
    exact Submodule.linearProjOfIsCompl_apply_left hq ⟨ι x, hι.1 x hx⟩
  have hΨc : ∀ x ∈ genSub E V', (Ψ x : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) :=
    fun x hx => by rw [hΨ x hx, hΦ]
  have hΨE : ∀ a b, ∀ x ∈ genSub E V', Ψ (E a b x) = smE ε (tfRdiag ε) a b (Ψ x) := by
    intro a b x hx
    rw [hΨ _ (tset_genSub_E E V' a b hx), hΨ x hx, hΦE]
    congr 1
    exact Subtype.ext (hι.2.2.1 a b x hx)
  have hV'le : V' ≤ genSub E V' := fun x hx => Submodule.mem_sInf.mpr fun _ hT => hT.1 hx
  have hinj : ∀ x ∈ genSub E V', Ψ x = 0 → x = 0 := by
    intro x hx h
    have h1 : tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) = 0 := by
      rw [← hΨc x hx, h]; rfl
    exact hι.2.1 x hx (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 (hι.1 x hx) h1)
  have hK2 := tf_kirr_map hV' Ψ (fun a b x hx => hΨE a b x (hV'le hx)) (fun x hx => hinj x (hV'le hx))
  refine ⟨V'.map Ψ, hK2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxG := hV'le hx
    have e : casimir (smE ε (tfRdiag ε)) (Ψ x) = Ψ (casimir E x) := by
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hΨE a b _ (tset_genSub_E E V' b a hxG), hΨE b a x hxG]
    rw [e, hc' x hx, map_smul]
  · rintro k hk _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := hVK' k hk x hx
    refine ⟨Ψ x', ⟨x', hx', rfl⟩, ?_⟩
    have hk' : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
    rw [hΨc x' (hV'le hx'), hΨc x (hV'le hx), tfRdiag_tfPh dual hσ hk', tf_tensGrp_kDiag dual hk,
      ← hι.2.2.2 k hk x (hV'le hx) x' (hV'le hx') hxx']
  · intro h
    obtain ⟨w, hw, hw0, -⟩ := hK2.2.2.2
    apply hw0
    have hwb : w ∈ (⊥ : Submodule ℂ (smD ε (tfRdiag ε))) := h ▸ hw
    exact (Submodule.mem_bot ℂ).1 hwb
  · intro v hv
    have hle : genSub (smE ε (tfRdiag ε)) (V'.map Ψ) ≤ (genSub E V').map Ψ := by
      refine sInf_le ⟨Submodule.map_mono hV'le, ?_⟩
      rintro a b _ ⟨x, hx, rfl⟩
      exact ⟨E a b x, tset_genSub_E E V' a b hx, hΨE a b x hx⟩
    obtain ⟨x, hx, rfl⟩ := hle hv
    exact ⟨x, hx, hΨc x hx⟩
  · intro x hx
    have hle : genSub E V' ≤ (genSub (smE ε (tfRdiag ε)) (V'.map Ψ)).comap Ψ ⊓ genSub E V' := by
      refine sInf_le ⟨fun z hz => ⟨Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨z, hz, rfl⟩, hV'le hz⟩, ?_⟩
      rintro a b z ⟨hz1, hz2⟩
      refine ⟨?_, tset_genSub_E E V' a b hz2⟩
      show Ψ (E a b z) ∈ genSub (smE ε (tfRdiag ε)) (V'.map Ψ)
      rw [hΨE a b z hz2]
      exact tset_genSub_E _ _ a b hz1
    exact ⟨Ψ x, (hle hx).1, hΨc x hx⟩

theorem tf_eq_case (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)} (hι : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hgap' : StdGap ε lam') {V₂ : Submodule ℂ (smD ε (tfRdiag ε))}
    (hV₂ : IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂)
    (hc₂ : ∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v)
    (hgen : ∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)))
    (hin : ∀ f ∈ tensSub (genSub E V),
      tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ closGen (smE ε (tfRdiag ε)) V₂) :
    ∀ f ∈ tensSub (genSub E V), ∃ x ∈ genSub E V', P f = ι x := by
  obtain ⟨Φ, hΦ, -⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  intro f hf
  obtain ⟨W, hWf, hfW, hWle, hWK⟩ := tf_kfin_tens dual hσ hD hV.1 hV.2.1 hf
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let W' : Submodule ℂ (tensSub (n := n) (genSub E V)) := W.comap (tensSub (genSub E V)).subtype
  have hW'f : FiniteDimensional ℂ W' := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hWle).symm
  let S0 : Submodule ℂ (tfL2n ε) := W'.map ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P')
  have hS0v : ∀ w : tensSub (n := n) (genSub E V),
      ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P') w = tfPh dual ε σ (y : H) (fun c => ((P w.1 c : D) : H)) :=
    fun w => hΦ (P' w)
  have hS0 : S0 ≤ closGen (smE ε (tfRdiag ε)) V₂ := by
    rintro _ ⟨w, -, rfl⟩
    rw [hS0v]
    exact hin w.1 w.2
  have hS0f : FiniteDimensional ℂ S0 := Module.Finite.map _ _
  have hS0K : ∀ k ∈ Kset ε, ∀ x ∈ S0, tfRdiag ε k x ∈ S0 := by
    rintro k hk _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hww'⟩ := hWK k hk w.1 hw
    refine ⟨⟨w', hWle hw'⟩, hw', ?_⟩
    rw [hS0v, hS0v, tfRdiag_tfPh dual hσ (closure_inUJ_of_mem_Kset hk), tf_tensGrp_kDiag dual hk,
      hP.2.2 k hk w.1 w.2 w' (hWle hw') hww']
  have hkf := data_kfin_le hgap' (tfRdiag_isURepOn ε) (isDerivedOn_smE (tfRdiag_isURepOn ε)) hV₂ hc₂ hVK₂
    S0 hS0 hS0f hS0K
  have hfS0 : tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ S0 :=
    ⟨⟨f, hf⟩, hfW, hS0v ⟨f, hf⟩⟩
  obtain ⟨v, hv, hve⟩ := hkf hfS0
  obtain ⟨x, hx, hxe⟩ := hgen v hv
  refine ⟨x, hx, ?_⟩
  have hd0 : (P f - ι x) ∈ tensSub (genSub E V) := Submodule.sub_mem _ (hP.1 f hf) (hι x hx)
  have e1 : Φ ⟨P f - ι x, hd0⟩ = Φ ⟨P f, hP.1 f hf⟩ - Φ ⟨ι x, hι x hx⟩ := by
    rw [← map_sub]; rfl
  have h0 : tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H)) = 0 := by
    calc tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H))
        = ((Φ ⟨P f - ι x, hd0⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := (hΦ ⟨P f - ι x, hd0⟩).symm
      _ = ((Φ ⟨P f, hP.1 f hf⟩ : smD ε (tfRdiag ε)) : tfL2n ε) -
          ((Φ ⟨ι x, hι x hx⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := by rw [e1, Submodule.coe_sub]
      _ = 0 := by
        rw [sub_eq_zero]
        exact ((hΦ ⟨P f, hP.1 f hf⟩).trans hve.symm).trans (hxe.trans (hΦ ⟨ι x, hι x hx⟩).symm)
  exact sub_eq_zero.1 (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 hd0 h0)

end ReciprocityTheory.ChartRestriction.DS
end
end
