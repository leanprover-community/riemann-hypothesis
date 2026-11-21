import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import BuildAid.ForwardExisting

section
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory

theorem integrable_conj_mul_translate_path {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (c : ℝ → G) (hc : Continuous c) {f' : G → ℂ} (hf' : MemL2Quotient Γ μ f')
    (_hcont : Continuous f') (H : L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc]; exact measure_Ioc_lt_top⟩
  have hm : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => rmul Γ (c s) q) :=
    measurable_rmul_uncurry.comp (measurable_snd.prodMk (hc.measurable.comp measurable_fst))
  have hp := (MeasurePreserving.id (volume.restrict (Set.uIoc (0 : ℝ) t))).skew_product
    (μc := quotMeasure Γ μ) (μd := quotMeasure Γ μ) hm
    (Filter.Eventually.of_forall fun s => (measurePreserving_rmul (c s)).map_eq)
  have h1 := ((Lp.memLp H).star).comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))
  have h2 := (hf'.2.comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))).comp_measurePreserving hp
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
  have e : descend Γ f' (rmul Γ (c p.1) p.2) = f' (sec Γ p.2 * c p.1) := by
    rw [← hf'.1.descend_mk, ← rmul_mk, mk_sec]
  change star (H p.2) * descend Γ f' (rmul Γ (c p.1) p.2) = _
  rw [e]
  rfl

end GlobalTheory
end

open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_conj_mul_translate_path' : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → ∀ {f' : G → ℂ}, MemL2Quotient Γ μ f' → Continuous f' → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  atlas_forward_decl GlobalTheory.integrable_conj_mul_translate_path
end

section
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Unitary

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

theorem coeFn_right_translate {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    R Γ μ g h.toL2 =ᵐ[quotMeasure Γ μ] fun q => φ (sec Γ q * g) := by
  rw [right_translate_toL2]
  refine (h.mul_right g).coeFn_toL2.trans (Filter.Eventually.of_forall fun q => ?_)
  have := (h.1.mul_right g).descend_mk (sec Γ q)
  rwa [mk_sec] at this

theorem inner_right_translate_integral {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) (H : L2 Γ μ) :
    inner ℂ H (R Γ μ g h.toL2) = ∫ q, starRingEnd ℂ (H q) * φ (sec Γ q * g) ∂quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_right_translate h g] with q e
  simp [e, mul_comm]

theorem inner_R_sub_eq_intervalIntegral :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) → inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc h0 f f' hf hf' hcf hd H t hint
  have ftc : ∀ x, ∫ s in (0 : ℝ)..t, f' (x * c s) = f (x * c t) - f (x * 1) := fun x => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd x s)
      ((hcf.comp (continuous_const.mul hc)).intervalIntegrable _ _), h0]
  simp only [inner_right_translate_integral hf']
  rw [MeasureTheory.intervalIntegral_integral_swap hint, ← inner_sub_right, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have e1 := coeFn_right_translate hf 1
  rw [map_one, ContinuousLinearMap.one_apply] at e1
  filter_upwards [coeFn_right_translate hf (c t), e1, Lp.coeFn_sub (R Γ μ (c t) hf.toL2) hf.toL2] with q a b e
  rw [intervalIntegral.integral_const_mul, ftc, e, Pi.sub_apply, a, b]
  simp [mul_comm]

end GlobalTheory.AutomorphicL2Unitary
end

open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_rightRegularRep_sub_eq_intervalIntegral_derivative : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) → inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  atlas_forward_decl GlobalTheory.AutomorphicL2Unitary.inner_R_sub_eq_intervalIntegral
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.LieSkew

open GlobalTheory.ExpDeriv

theorem inner_integral_identity : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H t
  exact GlobalTheory.T.inner_rightRegularRep_sub_eq_intervalIntegral_derivative Γ μ c hc hc0 hf hf' hcf' hd H t (GlobalTheory.T.integrable_conj_mul_translate_path' Γ μ c hc hf' hcf' H t)

theorem hasDerivAt_inner_R : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ H : L2 Γ μ, HasDerivAt (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) (inner ℂ H hf'.toL2) 0 := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H
  have hk : Continuous fun s => inner ℂ H (R Γ μ (c s) hf'.toL2) :=
    continuous_const.inner ((continuous_R hf'.toL2).comp hc)
  have e : (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) =
      fun t => inner ℂ H hf.toL2 + ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
    funext t
    rw [← inner_integral_identity Γ μ c hc hc0 hf hf' hcf' hd H t, add_sub_cancel]
  rw [e]
  have := ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add (inner ℂ H hf.toL2)
  simpa [hc0] using this

theorem inner_lie_eq_neg_inner_lie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)
    (hW : IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (X : Lie E N) (φ ψ : W) :
    inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) =
      - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  set c : ℝ → GA E N := fun t => infGL E N (expGL X t) with hcdef
  have hc : Continuous c := by
    have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Matrix.of X) := by
      open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have hinv : ∀ t, (expGL X t)⁻¹ = expGL X (-t) := fun t =>
      (eq_inv_of_mul_eq_one_right (by rw [← expGL_add, add_neg_cancel, expGL_zero])).symm
    have he : Continuous (expGL X) := Units.continuous_iff.2 ⟨hv, by
      simp only [hinv, expGL_val]
      exact hv.comp continuous_neg⟩
    exact GlobalTheory.CuspQuot.continuous_infGL.comp he
  have hc0 : c 0 = 1 := by simp only [c, expGL_zero, map_one]
  have hcinv : ∀ t, c (-t) = (c t)⁻¹ := fun t => by
    simp only [c, ← map_inv]
    congr 1
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [← expGL_add, add_neg_cancel, expGL_zero]
  have hcont : ∀ θ ∈ W, Continuous (θ : GA E N → ℂ) := fun θ hθ =>
    ContAut.continuous_of_isOpen_stab E N θ (hA θ hθ).level
  set F := toL2ₗ μ W h φ
  set Ψ := toL2ₗ μ W h ψ
  set F' := toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩
  set Ψ' := toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩
  have dF := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h φ φ.2) (h _ (hW (.lie X) φ.1 φ.2))
    (hcont _ (hW (.lie X) φ.1 φ.2)) (fun x t => hasDerivAt_along X φ.1 x t) Ψ
  have dΨ := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h ψ ψ.2) (h _ (hW (.lie X) ψ.1 ψ.2))
    (hcont _ (hW (.lie X) ψ.1 ψ.2)) (fun x t => hasDerivAt_along X ψ.1 x t) F
  have d1 : HasDerivAt (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) (inner ℂ F' Ψ) 0 := by
    have := dF.star
    simp only [← starRingEnd_apply, inner_conj_symm] at this
    exact this
  have d2 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ)) (-inner ℂ F Ψ') 0 := by
    have h0 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c t) Ψ)) (inner ℂ F Ψ') (-0) := by
      rw [neg_zero]; exact dΨ
    have := h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  have e : (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) =
      fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ) := by
    funext t
    let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
      ⟨(R (latticeGL E N) μ (c t)).toLinearMap, fun v => norm_R _ v⟩
    have hU : ∀ v, U v = R (latticeGL E N) μ (c t) v := fun _ => rfl
    have hΨ : R (latticeGL E N) μ (c t) (R (latticeGL E N) μ (c t)⁻¹ Ψ) = Ψ := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    calc inner ℂ (R (latticeGL E N) μ (c t) F) Ψ
        = inner ℂ (U F) (U (R (latticeGL E N) μ (c t)⁻¹ Ψ)) := by rw [hU, hU, hΨ]
      _ = inner ℂ F (R (latticeGL E N) μ (c t)⁻¹ Ψ) := U.inner_map_map _ _
      _ = _ := by rw [hcinv]
  rw [e] at d1
  exact d1.unique d2

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hW : IsStable W), (∀ φ ∈ W, IsAutForm φ) → ∀ (X : Matrix (Fin N) (Fin N) (Cinf E)) (φ ψ : W), inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) = - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  intro E _ _ _ N μ _ _ W h hW hA X φ ψ
  exact inner_lie_eq_neg_inner_lie μ W h hW hA X φ ψ

end GlobalTheory.LieSkew
end
