import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFamilySmoothEntriesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateForm
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PhiISemipositive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructure
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpan
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.CuspsLocallyFiniteFamily

section
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s :=
  (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))

def extend (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (K := E) (emb_injective s)

theorem extend_comp (s : 𝓞 E →+* ℂ) : (extend s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, extend, IsFractionRing.lift_algebraMap]

def chr (t : E →+* ℂ) : 𝓞 E →* ℂ := ((t.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)

theorem chr_injective : Function.Injective (chr (E := E)) := fun t t' h =>
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => DFunLike.congr_fun h x)

theorem span_eq_top :
    Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
  apply hφ0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp (chr (E := E)) chr_injective
  have hc := Fintype.linearIndependent_iff.1 li
    (fun t => φ fun j => if t = j then 1 else 0) (by
      funext a
      have h0 : φ (fun t : E →+* ℂ => t (algebraMap (𝓞 E) E a)) = 0 :=
        hφ (Submodule.subset_span ⟨a, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ φ] at h0
      simpa [chr, Finset.sum_apply, mul_comm] using h0)
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.pi_apply_eq_sum_univ φ w]
  simp only [hc, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

open Classical in

theorem exists_coeffs (s : 𝓞 E →+* ℂ) : ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ),
    ∀ t : E →+* ℂ, ∑ i, c i * t (algebraMap (𝓞 E) E (a i)) = if t = extend s then 1 else 0 := by
  have hmem : (fun t : E →+* ℂ => if t = extend s then (1 : ℂ) else 0) ∈
      Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) := by
    rw [span_eq_top]; trivial
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨f.support.card, fun i => (f.support.equivFin.symm i).1,
    fun i => f (f.support.equivFin.symm i).1, fun t => ?_⟩
  have ht := congrFun hf t
  rw [Finsupp.sum, Finset.sum_apply] at ht
  rw [← ht]
  refine (Equiv.sum_comp f.support.equivFin.symm
    (fun x : f.support => f x.1 * t (algebraMap (𝓞 E) E x.1))).trans ?_
  exact Finset.sum_coe_sort f.support (fun x => f x * t (algebraMap (𝓞 E) E x))

theorem eigComp_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ),
    ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ]
      (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  classical
  intro E _ _ _ s
  obtain ⟨N, a, c, h⟩ := exists_coeffs s
  refine ⟨N, a, c, ?_⟩
  intro g Λ _ _ R z
  obtain ⟨-, -, hs, hsum, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hB : ∀ (b : 𝓞 E) (t : E →+* ℂ), R.B b (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z) =
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b t
    have hm := (hs (t.comp (algebraMap (𝓞 E) E))).1 z
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker] at hm
    have := hm b
    simpa [sub_eq_zero] using this
  have hz : ∀ b : 𝓞 E, R.B b z = ∑ t : E →+* ℂ,
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b
    conv_lhs => rw [← hsum z]
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => hB b t
  calc eigComp R.B s z
      = ∑ t : E →+* ℂ, (if t = extend s then (1 : ℂ) else 0) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp [extend_comp]
    _ = ∑ t : E →+* ℂ, (∑ i, c i * t (algebraMap (𝓞 E) E (a i))) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [h]
    _ = ∑ i, c i • ∑ t : E →+* ℂ, t (algebraMap (𝓞 E) E (a i)) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = ∑ i, c i • R.B (a i) z := by simp only [hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula
end
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_component_polynomial_in_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ), ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum
end

section
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Metric.QuotHol

theorem differentiableOn_det {m n : ℕ} {A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    {V : Set (Fin n → ℂ)} (hA : ∀ i j, DifferentiableOn ℂ (fun t => A t i j) V) :
    DifferentiableOn ℂ (fun t => (A t).det) V := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  have hs : ∀ s : Finset (Fin m), DifferentiableOn ℂ (fun t => ∏ i ∈ s, A t (σ i) i) V := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact differentiableOn_const _
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).fun_mul ih
  exact hs Finset.univ

theorem exists_complement {k g' : ℕ} (v : Fin k → Fin (k + g') → ℂ)
    (hv : LinearIndependent ℂ v) :
    ∃ f : Fin g' → Fin (k + g') → ℂ,
      (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
        Matrix (Fin (k + g')) (Fin (k + g')) ℂ).det ≠ 0 := by
  classical
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range v))
  have hfr : Module.finrank ℂ W' = g' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW'
    have h2 := finrank_span_eq_card hv
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1 h2
    omega
  let bW := Module.finBasisOfFinrankEq ℂ W' hfr
  let f : Fin g' → Fin (k + g') → ℂ := fun j => (bW j : Fin (k + g') → ℂ)
  have hf : LinearIndependent ℂ f :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span ℂ (Set.range v)) (Submodule.span ℂ (Set.range f)) := by
    refine hW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hs : LinearIndependent ℂ (Sum.elim v f) := hv.sum_type hf hdisj
  have hc := hs.comp _ (finSumFinEquiv.symm.injective)
  refine ⟨f, ?_⟩
  have hu := Matrix.linearIndependent_cols_iff_isUnit
    (A := (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
      Matrix (Fin (k + g')) (Fin (k + g')) ℂ)) |>.1 hc
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem exists_holomorphic_quotient (g' k g n : ℕ) (U : Set (Fin n → ℂ))
    (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hg : k + g' = g) (he : ∀ i, DifferentiableOn ℂ (e i) U)
    (hli : LinearIndependent ℂ (fun i => e i t₀)) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧
      ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ),
        (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧
        ∀ t ∈ V, Function.Surjective (q t) ∧
          LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  classical
  subst hg
  obtain ⟨f, hf⟩ := exists_complement (fun i => e i t₀) hli
  let M : (Fin n → ℂ) → Matrix (Fin (k + g')) (Fin (k + g')) ℂ := fun t =>
    Matrix.of fun i j => Sum.elim (fun a => e a t) f (finSumFinEquiv.symm j) i
  have hMc : ∀ t a i, M t i (Fin.castAdd g' a) = e a t i := by
    intro t a i
    simp [M]
  have hMn : ∀ t b i, M t i (Fin.natAdd k b) = f b i := by
    intro t b i
    simp [M]
  have hMent : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) U := by
    intro i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with a | c
    · simp only [finSumFinEquiv_apply_left, hMc]
      exact (differentiableOn_pi.1 (he a)) i
    · simp only [finSumFinEquiv_apply_right, hMn]
      exact differentiableOn_const _
  have hdet : DifferentiableOn ℂ (fun t => (M t).det) U := differentiableOn_det hMent
  let V : Set (Fin n → ℂ) := U ∩ (fun t => (M t).det) ⁻¹' {0}ᶜ
  have hVo : IsOpen V := hdet.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hVU : V ⊆ U := Set.inter_subset_left
  have hinv : ∀ i j, DifferentiableOn ℂ (fun t => (M t)⁻¹ i j) V := by
    intro i j
    have h1 : DifferentiableOn ℂ (fun t => ((M t).det)⁻¹) V :=
      (hdet.mono hVU).inv (fun t ht => ht.2)
    have h2 : DifferentiableOn ℂ (fun t => (M t).adjugate i j) V := by
      simp only [Matrix.adjugate_apply]
      refine differentiableOn_det fun a b => ?_
      by_cases h : a = j
      · subst h
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne h]
        exact (hMent a b).mono hVU
    simpa [Matrix.inv_def, Ring.inverse_eq_inv'] using h1.fun_mul h2
  let q : (Fin n → ℂ) → (Fin (k + g') → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := fun t =>
    LinearMap.funLeft ℂ ℂ (Fin.natAdd k) ∘ₗ ((M t)⁻¹).mulVecLin
  have hq : ∀ t x j, q t x j = ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) := by
    intro t x j
    simp [q, LinearMap.funLeft_apply]
  refine ⟨V, hVo, ⟨ht₀, hf⟩, hVU, q, ?_, ?_⟩
  · intro x
    refine differentiableOn_pi.2 fun j => ?_
    simp only [hq, Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun l _ => (hinv _ l).mul_const _
  · intro t ht
    have hu : IsUnit (M t).det := isUnit_iff_ne_zero.2 ht.2
    have hMi : M t * (M t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have hiM : (M t)⁻¹ * M t = 1 := Matrix.nonsing_inv_mul _ hu
    refine ⟨fun y => ?_, ?_⟩
    · refine ⟨M t *ᵥ (fun j => Sum.elim 0 y (finSumFinEquiv.symm j)), ?_⟩
      ext j
      rw [hq, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
      simp
    · apply le_antisymm
      · intro x hx
        have hx0 : ∀ j, ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) = 0 := by
          intro j
          rw [← hq, LinearMap.mem_ker.1 hx]
          rfl
        have hxc : x = M t *ᵥ ((M t)⁻¹ *ᵥ x) := by
          rw [Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
        obtain ⟨c, hc⟩ : ∃ c, c = (M t)⁻¹ *ᵥ x := ⟨_, rfl⟩
        rw [← hc] at hx0 hxc
        have hsum : x = ∑ a, c (Fin.castAdd g' a) • e a t := by
          conv_lhs => rw [hxc]
          ext i
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, hx0, mul_zero,
            Finset.sum_const_zero, add_zero, hMc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [hsum]
        exact Submodule.sum_mem _ fun a _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have hcol : e a t = M t *ᵥ Pi.single (Fin.castAdd g' a) 1 := by
          ext i
          simp [hMc]
        refine LinearMap.mem_ker.2 ?_
        ext j
        rw [hq]
        show ((M t)⁻¹ *ᵥ e a t) (Fin.natAdd k j) = 0
        rw [hcol, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        have := a.2
        omega

end GlobalTheory.CompanionTheory.Metric.QuotHol
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_local_quotient_map : ∀ (g' k g n : ℕ) (U : Set (Fin n → ℂ)) (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen U → t₀ ∈ U → k + g' = g → (∀ i, DifferentiableOn ℂ (e i) U) → LinearIndependent ℂ (fun i => e i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧ ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧ ∀ t ∈ V, Function.Surjective (q t) ∧ LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.Regular

section Proj

variable {V O : Type} [AddCommGroup V] [Module ℂ V] [CommRing O]

theorem mem_eigSp_iff (B : O →+* Module.End ℂ V) (s : O →+* ℂ) (y : V) :
    y ∈ eigSp B s ↔ ∀ a, B a y = s a • y := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem exists_proj (B : O →+* Module.End ℂ V) (W : Submodule ℂ V) (hW : ∀ a, ∀ y ∈ W, B a y ∈ W)
    (s : O →+* ℂ) (F : Finset (O →+* ℂ)) (hF : s ∉ F) :
    ∃ L : V →ₗ[ℂ] V, (∀ y ∈ W, L y ∈ W) ∧ (∀ y ∈ eigSp B s, L y = y) ∧
      ∀ t ∈ F, ∀ y ∈ eigSp B t, L y = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, fun y hy => hy, fun _ _ => rfl, by simp⟩
  | insert t F ht ih =>
    obtain ⟨L, hLW, hLs, hLF⟩ := ih (fun h => hF (Finset.mem_insert_of_mem h))
    have hts : t ≠ s := fun h => hF (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨a, ha⟩ : ∃ a, t a ≠ s a := by
      by_contra h
      push Not at h
      exact hts (RingHom.ext h)
    have hc : s a - t a ≠ 0 := sub_ne_zero.2 ha.symm
    let T : V →ₗ[ℂ] V := (s a - t a)⁻¹ • ((B a : V →ₗ[ℂ] V) - t a • (LinearMap.id : V →ₗ[ℂ] V))
    have hT : ∀ y, T y = (s a - t a)⁻¹ • (B a y - t a • y) := fun y => rfl
    refine ⟨L ∘ₗ T, ?_, ?_, ?_⟩
    · intro y hy
      rw [LinearMap.comp_apply, hT]
      exact hLW _ (W.smul_mem _ (W.sub_mem (hW a y hy) (W.smul_mem _ hy)))
    · intro y hy
      have e : T y = y := by
        rw [hT, (mem_eigSp_iff B s y).1 hy a, ← sub_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [LinearMap.comp_apply, e, hLs y hy]
    · intro t' ht' y hy
      have e : T y = ((s a - t a)⁻¹ * (t' a - t a)) • y := by
        rw [hT, (mem_eigSp_iff B t' y).1 hy a, ← sub_smul, smul_smul]
      rw [LinearMap.comp_apply, e, map_smul]
      rcases Finset.mem_insert.1 ht' with rfl | h
      · simp
      · rw [hLF t' h y hy, smul_zero]

end Proj

section Riem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_sub_right (x y y' : Fin g → ℂ) : R.ip x (y - y') = R.ip x y - R.ip x y' := by
  simp [RiemLat.ip, sub_dotProduct]

theorem ip_smul_right (x : Fin g → ℂ) (c : ℂ) (y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_sub_left (x x' y : Fin g → ℂ) : R.ip (x - x') y = R.ip x y - R.ip x' y := by
  simp [RiemLat.ip, star_sub, mulVec_sub, dotProduct_sub]

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp [RiemLat.ip, star_add, mulVec_add, dotProduct_add]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  simp [RiemLat.ip, star_smul, mulVec_smul, dotProduct_smul]

theorem ip_zero_left (y : Fin g → ℂ) : R.ip 0 y = 0 := by
  simp [RiemLat.ip]

theorem ip_zero_right (x : Fin g → ℂ) : R.ip x 0 = 0 := by
  simp [RiemLat.ip]

theorem ip_sum_right {ι : Type} (t : Finset ι) (x : Fin g → ℂ) (f : ι → Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [ip_zero_right]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ip_add_right, ih]

theorem ip_sum_left {ι : Type} (t : Finset ι) (f : ι → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ip_add_left, ih]

theorem eq_zero_of_ip_self (y : Fin g → ℂ) (h : R.ip y y = 0) : y = 0 := by
  by_contra hy
  have := R.pos y hy
  rw [show y ⬝ᵥ R.Hm *ᵥ star y = R.ip y y from rfl, h] at this
  simp at this

theorem gram_det_ne_zero {r : ℕ} (w : Fin r → Fin g → ℂ) (hw : LinearIndependent ℂ w) : (R.gram w).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hAc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 : ∀ a, R.ip (w a) (∑ b, c b • w b) = 0 := fun a => by
    have e := congrFun hAc a
    rw [ip_sum_right]
    simp only [ip_smul_right]
    simpa [mulVec, dotProduct, RiemLat.gram, mul_comm] using e
  have h2 : R.ip (∑ b, c b • w b) (∑ b, c b • w b) = 0 := by
    rw [ip_sum_left]
    simp only [ip_smul_left, h1, mul_zero, Finset.sum_const_zero]
  exact hc (funext (Fintype.linearIndependent_iff.mp hw c (eq_zero_of_ip_self R _ h2)))

theorem gram_append_det {r k : ℕ} (w : Fin r → Fin g → ℂ) (x : Fin k → Fin g → ℂ) (hw : LinearIndependent ℂ w) :
    ∃ M : Matrix (Fin r) (Fin k) ℂ,
      (∀ b j, R.ip (w b) (x j - ∑ a, M a j • w a) = 0) ∧
      (R.gram (Fin.append w x)).det =
        (R.gram w).det * (R.gram fun j => x j - ∑ a, M a j • w a).det := by
  classical
  have hdet : IsUnit (R.gram w).det := isUnit_iff_ne_zero.2 (gram_det_ne_zero R w hw)
  set A := R.gram w with hA
  let _ := Matrix.invertibleOfIsUnitDet A hdet
  let Bm : Matrix (Fin r) (Fin k) ℂ := Matrix.of fun a j => R.ip (w a) (x j)
  let C : Matrix (Fin k) (Fin r) ℂ := Matrix.of fun i b => R.ip (x i) (w b)
  let D := R.gram x
  let M := A⁻¹ * Bm
  have hAM : A * M = Bm := Matrix.mul_nonsing_inv_cancel_left _ _ hdet
  have horth : ∀ b j, R.ip (w b) (x j - ∑ a, M a j • w a) = 0 := by
    intro b j
    have e := congrFun (congrFun hAM b) j
    rw [Matrix.mul_apply] at e
    have h2 : ∑ a, M a j * R.ip (w b) (w a) = R.ip (w b) (x j) := by
      simpa [mul_comm, A, RiemLat.gram, Bm] using e
    rw [ip_sub_right, ip_sum_right]
    simp only [ip_smul_right]
    rw [h2, sub_self]
  refine ⟨M, horth, ?_⟩
  have hblock : (R.gram (Fin.append w x)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A Bm C D := by
    ext (a | a) (b | b) <;> simp [RiemLat.gram, Bm, C, D, A]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblock, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv]
  congr 2
  ext i j
  have e1 : (D - C * A⁻¹ * Bm) i j = R.ip (x i) (x j) - ∑ a, M a j * R.ip (x i) (w a) := by
    rw [Matrix.mul_assoc, Matrix.sub_apply, Matrix.mul_apply]
    simp [D, C, RiemLat.gram, M, mul_comm]
  have e2 : R.ip (x i - ∑ a, M a i • w a) (x j - ∑ a, M a j • w a) =
      R.ip (x i) (x j) - ∑ a, M a j * R.ip (x i) (w a) := by
    rw [ip_sub_left, ip_sum_left]
    simp only [ip_smul_left, horth, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [ip_sub_right, ip_sum_right]
    simp only [ip_smul_right]
  rw [e1]
  exact e2.symm

theorem exists_eigLin (s : 𝓞 E →+* ℂ) :
    ∃ L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, L x = eigComp R.B s x := by
  obtain ⟨-, -, h1, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hl := (h1 s).2.2.1
  have h0 : eigComp R.B s 0 = 0 := by simpa using hl (-1) 0 0
  exact ⟨{ toFun := eigComp R.B s
           map_add' := fun x y => by simpa using hl 1 x y
           map_smul' := fun c x => by simpa [h0] using hl c x 0 }, fun _ => rfl⟩

theorem eigComp_mem (W : Submodule ℂ (Fin g → ℂ)) (hW : ∀ a, ∀ y ∈ W, R.B a y ∈ W) (s : 𝓞 E →+* ℂ)
    {y : Fin g → ℂ} (hy : y ∈ W) : eigComp R.B s y ∈ W := by
  classical
  obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  obtain ⟨Ls, hLs⟩ := exists_eigLin R s
  obtain ⟨L, hLW, hLid, hLF⟩ := exists_proj R.B W hW s
    ((Finset.univ.image fun t : E →+* ℂ => t.comp (algebraMap (𝓞 E) E)).erase s) (Finset.notMem_erase _ _)
  have key : ∀ t : E →+* ℂ, ∀ x ∈ eigSp R.B (t.comp (algebraMap (𝓞 E) E)), L x = Ls x := by
    intro t x hx
    by_cases ht : t.comp (algebraMap (𝓞 E) E) = s
    · rw [ht] at hx
      rw [hLid x hx, hLs, (h1 s).2.1 x hx]
    · rw [hLF _ (Finset.mem_erase.2 ⟨ht, Finset.mem_image_of_mem _ (Finset.mem_univ t)⟩) x hx]
      obtain ⟨a, ha⟩ : ∃ a, (t.comp (algebraMap (𝓞 E) E)) a ≠ s a := by
        by_contra h
        push Not at h
        exact ht (RingHom.ext h)
      have e1 := (h1 s).2.2.2 a x
      rw [(mem_eigSp_iff _ _ _).1 hx a, ← hLs, ← hLs, map_smul] at e1
      have e2 : ((t.comp (algebraMap (𝓞 E) E)) a - s a) • Ls x = 0 := by rw [sub_smul, e1, sub_self]
      exact ((smul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 ha)).symm
  have e : L y = Ls y := by
    calc L y = L (∑ t : E →+* ℂ, eigComp R.B (t.comp (algebraMap (𝓞 E) E)) y) := by rw [h2 y]
      _ = Ls (∑ t : E →+* ℂ, eigComp R.B (t.comp (algebraMap (𝓞 E) E)) y) := by
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl fun t _ => key t _ ((h1 _).1 y)
      _ = Ls y := by rw [h2 y]
  rw [← hLs, ← e]
  exact hLW y hy

end Riem

theorem gram_append_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) (r k : ℕ) (v : Fin r → Λ) (x : Fin k → Fin g → ℂ), IsIsoSub R.form I → IsNzFamily I r v → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → (∀ y z, (∀ u ∈ I, R.ip (R.P u) y = 0) → R'.ip (q y) (q z) = R.ip y z) → (∀ j, x j ∈ eigSp R.B s) → (R.gram (Fin.append (fun a => eigComp R.B s (R.P (v a))) x)).det = (R.gram (fun a => eigComp R.B s (R.P (v a)))).det * (R'.gram (fun j => q (x j))).det := by
  intro E _ _ _ g g' Λ Λ' _ _ _ _ R R' q I s r k v x hI hv hq hR hx
  classical
  obtain ⟨-, hvI, hvli, hidx⟩ := hv
  obtain ⟨-, -, h1, h2, h3⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hwli : LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) :=
    (GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Unit R I hI s).2 r v hvI hvli
  obtain ⟨M, hz, hdet⟩ := gram_append_det R _ x hwli
  rw [hdet]
  congr 2
  obtain ⟨Ls, hLs⟩ := exists_eigLin R s
  set w : Fin r → Fin g → ℂ := fun a => eigComp R.B s (R.P (v a)) with hw
  set z : Fin k → Fin g → ℂ := fun j => x j - ∑ a, M a j • w a with hzdef
  have hstable : ∀ a, ∀ y ∈ Submodule.span ℂ (R.P '' I), R.B a y ∈ Submodule.span ℂ (R.P '' I) := by
    intro a y hy
    have hle : (Submodule.span ℂ (R.P '' I)).map (R.B a) ≤ Submodule.span ℂ (R.P '' I) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨a • u, I.smul_mem a hu, R.act a u⟩
    exact hle (Submodule.mem_map_of_mem hy)
  have hwq : ∀ a, q (w a) = 0 := fun a => by
    have : w a ∈ LinearMap.ker q := by
      rw [hq]
      exact eigComp_mem R _ hstable s (Submodule.subset_span ⟨v a, hvI a, rfl⟩)
    exact this
  have hqz : ∀ j, q (z j) = q (x j) := fun j => by
    simp [hzdef, map_sub, map_sum, hwq]
  have hzeig : ∀ j, z j ∈ eigSp R.B s := fun j =>
    Submodule.sub_mem _ (hx j) (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ((h1 s).1 _))
  have hspan : ∀ u ∈ I, ∀ j, R.ip (eigComp R.B s (R.P u)) (z j) = 0 := by
    intro u hu j
    obtain ⟨n, hn, -, hmem⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hidx (a := u) hu
    have hmem' : n • u ∈ Submodule.span (𝓞 E) (Set.range v) := hmem.1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hmem'
    have e1 : (n : ℂ) • eigComp R.B s (R.P u) = ∑ a, s (c a) • w a := by
      have e2 := (h1 s).2.2.2 (n : 𝓞 E) (R.P u)
      rw [← R.act, Nat.cast_smul_eq_nsmul, ← hc, map_natCast] at e2
      rw [← e2, map_sum, ← hLs, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [R.act, hLs, (h1 s).2.2.2, hw]
    have e3 : starRingEnd ℂ (n : ℂ) * R.ip (eigComp R.B s (R.P u)) (z j) = 0 := by
      rw [← ip_smul_left, e1, ip_sum_left]
      simp only [ip_smul_left]
      exact Finset.sum_eq_zero fun a _ => by rw [hz a j, mul_zero]
    refine (mul_eq_zero.1 e3).resolve_left ?_
    simpa using hn.ne'
  have horth : ∀ j, ∀ u ∈ I, R.ip (R.P u) (z j) = 0 := by
    intro j u hu
    rw [← h2 (R.P u), ip_sum_left]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t.comp (algebraMap (𝓞 E) E) = s
    · rw [ht]
      exact hspan u hu j
    · exact h3 _ s ht _ ((h1 _).1 _) _ (hzeig j)
  ext i j
  simp only [RiemLat.gram, Matrix.of_apply]
  rw [← hqz i, ← hqz j]
  exact (hR _ _ (horth i)).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram
end
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_family_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) (r k : ℕ) (v : Fin r → Λ) (x : Fin k → Fin g → ℂ), IsIsoSub R.form I → IsNzFamily I r v → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → (∀ y z, (∀ u ∈ I, R.ip (R.P u) y = 0) → R'.ip (q y) (q z) = R.ip y z) → (∀ j, x j ∈ eigSp R.B s) → (R.gram (Fin.append (fun a => eigComp R.B s (R.P (v a))) x)).det = (R.gram (fun a => eigComp R.B s (R.P (v a)))).det * (R'.gram (fun j => q (x j))).det := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram.gram_append_eq
end

section
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem ip_sum_right (R : RiemLat E g Λ) {k : ℕ} (x : Fin g → ℂ) (a : Fin k → ℂ)
    (u : Fin k → Fin g → ℂ) : R.ip x (∑ j, a j • u j) = ∑ j, a j * R.ip x (u j) := by
  simp only [RiemLat.ip, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem ip_sum_left (R : RiemLat E g Λ) {k : ℕ} (a : Fin k → ℂ) (u : Fin k → Fin g → ℂ)
    (y : Fin g → ℂ) : R.ip (∑ i, a i • u i) y = ∑ i, star (a i) * R.ip (u i) y := by
  simp only [RiemLat.ip, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem star_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip x y) = R.ip y x := by
  have h := R.herm
  simp only [RiemLat.ip]
  rw [← star_dotProduct_star, star_mulVec, star_star, h.eq, dotProduct_comm, dotProduct_mulVec]
  exact dotProduct_comm _ _

theorem gram_comb (R : RiemLat E g Λ) {k l : ℕ} (T : Matrix (Fin l) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    R.gram (fun a => ∑ i, T a i • u i) = T.map star * R.gram u * Tᵀ := by
  ext a a'
  simp only [RiemLat.gram, Matrix.of_apply, ip_sum_left, ip_sum_right, Matrix.mul_apply,
    Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gram_comb_det (R : RiemLat E g Λ) {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    (R.gram (fun a => ∑ i, T a i • u i)).det.re = Complex.normSq T.det * (R.gram u).det.re := by
  have h1 : (T.map star).det = star T.det := by
    have : T.map star = Tᴴᵀ := by ext; simp
    rw [this, det_transpose, det_conjTranspose]
  rw [gram_comb, det_mul, det_mul, det_transpose, h1]
  have h2 : star T.det * (R.gram u).det * T.det = (Complex.normSq T.det : ℂ) * (R.gram u).det := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h2, Complex.re_ofReal_mul]

theorem sum_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → V) (v : Fin k → ℂ) :
    ∑ i, v i • ∑ j, T i j • u j = ∑ j, (v ᵥ* T) j • u j := by
  simp only [Finset.smul_sum, Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem det_ne_zero_of_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V)
    (hc : LinearIndependent ℂ fun i => ∑ j, T i j • u j) : T.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvT⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  funext i
  refine Fintype.linearIndependent_iff.1 hc v ?_ i
  rw [sum_comb, hvT]
  simp

theorem linearIndependent_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V) (hu : LinearIndependent ℂ u)
    (hT : T.det ≠ 0) : LinearIndependent ℂ fun i => ∑ j, T i j • u j := by
  refine Fintype.linearIndependent_iff.2 fun v hv i => ?_
  rw [sum_comb] at hv
  have h0 : v ᵥ* T = 0 := funext fun j => Fintype.linearIndependent_iff.1 hu _ hv j
  have := Matrix.eq_zero_of_vecMul_eq_zero hT h0
  simp [this]

theorem differentiableOn_det {n k : ℕ} {W : Set (Fin n → ℂ)}
    {M : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) W) :
    DifferentiableOn ℂ (fun t => (M t).det) W := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_smul ?_ _
  have h1 : ∀ s : Finset (Fin k), DifferentiableOn ℂ (fun t => ∏ i ∈ s, M t (σ i) i) W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).mul ih
  exact h1 _

theorem gram_det_re_pos (R : RiemLat E g Λ) {k : ℕ} (u : Fin k → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det.re := by
  have hH : (R.gram u).IsHermitian := by
    ext a b
    simp only [RiemLat.gram, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact star_ip R _ _
  have hq : ∀ x : Fin k → ℂ, star x ⬝ᵥ (R.gram u) *ᵥ x = R.ip (∑ i, x i • u i) (∑ i, x i • u i) := by
    intro x
    simp only [ip_sum_left, ip_sum_right, dotProduct, mulVec, RiemLat.gram, Matrix.of_apply,
      Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hP : (R.gram u).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    rw [hq]
    set w := ∑ i, x i • u i with hw
    have hw0 : w ≠ 0 := fun h0 =>
      hx (funext (Fintype.linearIndependent_iff.1 hu x h0))
    refine Complex.pos_iff.2 ⟨R.pos w hw0, ?_⟩
    have := Complex.conj_eq_iff_im.1 (star_ip R w w)
    simpa using this.symm
  exact (Complex.pos_iff.1 hP.det_pos).1

theorem log_gram_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (n m : ℕ) (W : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (b c : Fin m → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen W → t₀ ∈ W → (∀ i, DifferentiableOn ℂ (b i) W) → (∀ i, DifferentiableOn ℂ (c i) W) → (∀ t ∈ W, LinearIndependent ℂ fun i => b i t) → (∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t)) → LinearIndependent ℂ (fun i => c i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V ∧ ∀ t ∈ V, LinearIndependent ℂ (fun i => c i t) ∧ Real.log ((R t).gram fun i => c i t).det.re = Real.log ((R t).gram fun i => b i t).det.re + (G t).re := by
  intro E _ _ _ g Λ _ _ n m W R b c t₀ hW ht₀ hb hc hbi hcs hci
  have hinj : LinearMap.ker (Fintype.linearCombination ℂ fun i => b i t₀) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    rw [Fintype.linearCombination_apply] at hv
    exact funext (Fintype.linearIndependent_iff.1 (hbi t₀ ht₀) v hv)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hφb : ∀ i, φ (b i t₀) = Pi.single i 1 := by
    intro i
    have h1 := LinearMap.congr_fun hφ (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using h1
  have hφd : ∀ u : (Fin n → ℂ) → Fin g → ℂ, DifferentiableOn ℂ u W →
      ∀ j, DifferentiableOn ℂ (fun t => φ (u t) j) W := by
    intro u hu j
    have h1 : DifferentiableOn ℂ (fun t => LinearMap.toContinuousLinearMap φ (u t)) W :=
      (LinearMap.toContinuousLinearMap φ).differentiable.comp_differentiableOn hu
    exact differentiableOn_pi.1 h1 j
  let Bm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (b i t) j
  let Cm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (c i t) j
  have hdB : DifferentiableOn ℂ (fun t => (Bm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hb i) j
  have hdC : DifferentiableOn ℂ (fun t => (Cm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hc i) j
  have hT : ∀ t ∈ W, ∃ T : Matrix (Fin m) (Fin m) ℂ,
      (∀ i, c i t = ∑ j, T i j • b j t) ∧ Cm t = T * Bm t := by
    intro t ht
    have h1 := fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hcs t ht i)
    choose T hT using h1
    refine ⟨Matrix.of T, fun i => (hT i).symm, ?_⟩
    ext i j
    simp only [Cm, Bm, Matrix.of_apply, Matrix.mul_apply, ← hT i, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hB0 : Bm t₀ = 1 := by
    ext i j
    simp only [Bm, Matrix.of_apply, hφb, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  obtain ⟨T₀, hT₀, hCT₀⟩ := hT t₀ ht₀
  have hf₀ : (Cm t₀).det ≠ 0 := by
    rw [hCT₀, hB0, mul_one]
    have h1 : (fun i => c i t₀) = fun i => ∑ j, T₀ i j • b j t₀ := funext hT₀
    exact det_ne_zero_of_comb T₀ _ (h1 ▸ hci)
  let f₀ : ℂ := (Cm t₀).det
  let q : (Fin n → ℂ) → ℂ := fun t => (Cm t).det / (Bm t).det / f₀
  let V₁ : Set (Fin n → ℂ) := W ∩ (fun t => (Bm t).det) ⁻¹' {0}ᶜ
  have hV₁ : IsOpen V₁ := hdB.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hfd : DifferentiableOn ℂ (fun t => (Cm t).det / (Bm t).det) V₁ := by
    simp only [div_eq_mul_inv]
    have hinv : DifferentiableOn ℂ (fun t => ((Bm t).det)⁻¹) V₁ :=
      DifferentiableOn.fun_inv (hdB.mono Set.inter_subset_left) fun t ht => ht.2
    exact (hdC.mono Set.inter_subset_left).mul hinv
  have hqd : DifferentiableOn ℂ q V₁ := by
    have h1 := hfd.mul_const f₀⁻¹
    simpa only [q, div_eq_mul_inv] using h1
  let V : Set (Fin n → ℂ) := V₁ ∩ q ⁻¹' Metric.ball 1 1
  have hVo : IsOpen V := hqd.continuousOn.isOpen_inter_preimage hV₁ Metric.isOpen_ball
  have hq0 : q t₀ = 1 := by
    simp only [q, f₀, hB0, det_one, div_one]
    exact div_self hf₀
  have hslit : ∀ t ∈ V, q t ∈ Complex.slitPlane := by
    intro t ht
    have h1 : ‖q t - 1‖ < 1 := by simpa [dist_eq_norm] using ht.2
    have h2 := Complex.mem_slitPlane_of_norm_lt_one h1
    simpa using h2
  refine ⟨V, hVo, ⟨⟨ht₀, by simp [hB0]⟩, by simp [hq0]⟩, fun t ht => ht.1.1,
    fun t => 2 * Complex.log (q t) + 2 * ((Real.log ‖f₀‖ : ℝ) : ℂ), ?_, ?_⟩
  · exact (((hqd.mono Set.inter_subset_left).clog hslit).const_mul 2).add_const _
  · intro t ht
    obtain ⟨T, hTc, hCT⟩ := hT t ht.1.1
    have hBne : (Bm t).det ≠ 0 := ht.1.2
    have hqne : q t ≠ 0 := Complex.slitPlane_ne_zero (hslit t ht)
    have hdet : T.det = q t * f₀ := by
      have h1 : (Cm t).det = T.det * (Bm t).det := by rw [hCT, det_mul]
      have hf₀' : f₀ ≠ 0 := hf₀
      show T.det = (Cm t).det / (Bm t).det / f₀ * f₀
      rw [div_mul_cancel₀ _ hf₀', h1, mul_div_cancel_right₀ _ hBne]
    have hTne : T.det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero hqne hf₀
    have hcf : (fun i => c i t) = fun i => ∑ j, T i j • b j t := funext hTc
    refine ⟨hcf ▸ linearIndependent_comb T _ (hbi t ht.1.1) hTne, ?_⟩
    have hpos := gram_det_re_pos (R t) _ (hbi t ht.1.1)
    rw [hcf, gram_comb_det, Real.log_mul (by simpa using hTne) hpos.ne', add_comm, hdet]
    congr 1
    have hf₀n : ‖f₀‖ ≠ 0 := norm_ne_zero_iff.2 hf₀
    have hqn : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 hqne
    rw [Complex.normSq_eq_norm_sq, norm_mul, Real.log_pow, Real.log_mul (mul_ne_zero hqn hf₀n |> left_ne_zero_of_mul) hf₀n]
    simp [Complex.add_re, Complex.mul_re, Complex.log_re]
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange
end
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_span_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (n m : ℕ) (W : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (b c : Fin m → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen W → t₀ ∈ W → (∀ i, DifferentiableOn ℂ (b i) W) → (∀ i, DifferentiableOn ℂ (c i) W) → (∀ t ∈ W, LinearIndependent ℂ fun i => b i t) → (∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t)) → LinearIndependent ℂ (fun i => c i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V ∧ ∀ t ∈ V, LinearIndependent ℂ (fun i => c i t) ∧ Real.log ((R t).gram fun i => c i t).det.re = Real.log ((R t).gram fun i => b i t).det.re + (G t).re := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change
end

section
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramPos

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem posDef_Hm_transpose (R : RiemLat E g Λ) : (R.Hmᵀ).PosDef := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := R.pos x hx
  have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
  rw [Complex.pos_iff]
  exact ⟨by rw [e]; exact h1, him.symm⟩

theorem gram_eq_mul (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = ((Matrix.of u)ᵀ)ᴴ * R.Hmᵀ * (Matrix.of u)ᵀ := by
  ext a b
  simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_pos_of_linearIndependent (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det := by
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := Matrix.mulVec_injective_iff.2 hu
  rw [gram_eq_mul]
  exact ((posDef_Hm_transpose R).conjTranspose_mul_mul_same hC).det_pos

theorem linearIndependent_of_det_ne_zero (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hd : (R.gram u).det ≠ 0) : LinearIndependent ℂ u := by
  have hinj : Function.Injective (R.gram u).mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := by
    intro x y hxy
    apply hinj
    have hxy' : (Matrix.of u)ᵀ *ᵥ x = (Matrix.of u)ᵀ *ᵥ y := hxy
    simp only [gram_eq_mul, ← Matrix.mulVec_mulVec, hxy']
  exact Matrix.mulVec_injective_iff.1 hC

theorem gram_det_pos_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (LinearIndependent ℂ u → 0 < (R.gram u).det.re ∧ (R.gram u).det.im = 0) ∧ ((R.gram u).det ≠ 0 → LinearIndependent ℂ u) := by
  intro E _ _ _ g Λ _ _ R m u
  refine ⟨fun hu => ?_, linearIndependent_of_det_ne_zero R u⟩
  have h := Complex.pos_iff.1 (det_pos_of_linearIndependent R u hu)
  exact ⟨h.1, h.2.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.GramPos
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_pos_iff_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (LinearIndependent ℂ u → 0 < (R.gram u).det.re ∧ (R.gram u).det.im = 0) ∧ ((R.gram u).det ≠ 0 → LinearIndependent ℂ u) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.GramPos.gram_det_pos_iff
end

section
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhiI

open ReciprocityTheory.AnForm.A (IsPsh)

theorem isPsh_add {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ) (hψ : IsPsh U ψ) :
    IsPsh U (fun z => φ z + ψ z) := by
  refine ⟨hφ.1.add hψ.1, fun z w hd => ?_⟩
  obtain ⟨h1, h2⟩ := hφ.2 z w hd
  obtain ⟨h3, h4⟩ := hψ.2 z w hd
  refine ⟨h1.add h3, ?_⟩
  have e := Real.circleAverage_fun_add h1 h3
  show φ z + ψ z ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w) + ψ (z + ζ • w)) 0 1
  rw [e]
  linarith

theorem isPsh_zero {d : ℕ} (U : Set (Fin d → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) := by
  refine ⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩
  rw [Real.circleAverage_const]

theorem isPsh_sum {d : ℕ} {U : Set (Fin d → ℂ)} {ι : Type} (S : Finset ι) {f : ι → (Fin d → ℂ) → ℝ}
    (h : ∀ i ∈ S, IsPsh U (f i)) : IsPsh U (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isPsh_zero U 0
  | insert a S ha ih =>
    have := isPsh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine GroundTheory.Heights₂.Heights.NineStatements.isPsh_congr' (fun z _ => ?_) this
    simp [Finset.sum_insert ha]

theorem hol_apply {n g g' : ℕ} {V : Set (Fin n → ℂ)} {q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)}
    (hq : ∀ x, DifferentiableOn ℂ (fun t => q t x) V) {z : (Fin n → ℂ) → Fin g → ℂ}
    (hz : DifferentiableOn ℂ z V) : DifferentiableOn ℂ (fun t => q t (z t)) V := by
  have e : (fun t => q t (z t)) = fun t => ∑ i, z t i • q t (fun j => if i = j then 1 else 0) := by
    funext t
    exact LinearMap.pi_apply_eq_sum_univ (q t) (z t)
  rw [e]
  refine DifferentiableOn.fun_sum fun i _ => ?_
  exact ((differentiableOn_pi.1 hz) i).smul (hq _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {n : ℕ}

theorem hol_eig {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ} (hP : ∀ x, DifferentiableOn ℂ (fun t => (R t).P x) U)
    (s : 𝓞 E →+* ℂ) (x : Λ) : DifferentiableOn ℂ (fun t => eigComp (R t).B s ((R t).P x)) U := by
  obtain ⟨N, a, c, h⟩ := GlobalTheory.T.eigen_component_polynomial_in_action E s
  have e : (fun t => eigComp (R t).B s ((R t).P x)) = fun t => ∑ i, c i • (R t).P (a i • x) := by
    funext t
    rw [h g Λ (R t)]
    simp only [(R t).act]
  rw [e]
  exact DifferentiableOn.fun_sum fun i _ => (hP _).const_smul (c i)

theorem isHolFam_mono {g' : ℕ} {Λ' : Type} [AddCommGroup Λ'] [Module (𝓞 E) Λ'] {W V : Set (Fin n → ℂ)}
    {R' : (Fin n → ℂ) → RiemLat E g' Λ'} (h : IsHolFam W R') (hV : V ⊆ W) : IsHolFam V R' :=
  ⟨fun t ht t' ht' => h.1 t (hV ht) t' (hV ht'), fun x => (h.2 x).mono hV⟩

theorem perEmb {U W : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ} (hHol : IsHolFam U R)
    {g' : ℕ} {Λ' : Type} [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (hW : IsOpen W) (hWU : W ⊆ U) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ W)
    {R' : (Fin n → ℂ) → RiemLat E g' Λ'} (hR' : IsHolFam W R')
    {q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)} (hq : ∀ x, DifferentiableOn ℂ (fun t => q t x) W)
    {I : Submodule (𝓞 E) Λ} (hker : ∀ t ∈ W, LinearMap.ker (q t) = Submodule.span ℂ ((R t).P '' I))
    (hcomp : ∀ t ∈ W, ∀ y z, (∀ u ∈ I, (R t).ip ((R t).P u) y = 0) → (R' t).ip (q t y) (q t z) = (R t).ip y z)
    (hiso : ∀ t ∈ U, IsIsoSub (R t).form I) (s : 𝓞 E →+* ℂ) {r : ℕ} {v : Fin r → Λ} (hv : IsNzFamily I r v)
    {m : ℕ} {b : Fin m → (Fin n → ℂ) → Fin g → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) U)
    (hbl : ∀ t ∈ U, LinearIndependent ℂ fun i => b i t)
    (hbs : ∀ t ∈ U, Submodule.span ℂ (Set.range fun i => b i t) = eigSp (R t).B s) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧
      IsPsh V (fun t => Real.log ((R t).gram fun i => b i t).det.re -
        Real.log ((R t).gram fun a => eigComp (R t).B s ((R t).P (v a))).det.re) := by
  obtain ⟨hr1, hvI, hvli, hvidx⟩ := hv
  have hv : IsNzFamily I r v := ⟨hr1, hvI, hvli, hvidx⟩
  set w : Fin r → (Fin n → ℂ) → Fin g → ℂ := fun a t => eigComp (R t).B s ((R t).P (v a)) with hw
  have hwh : ∀ a, DifferentiableOn ℂ (w a) U := fun a => hol_eig hHol.2 s (v a)
  have hwl : ∀ t ∈ U, LinearIndependent ℂ fun a => w a t := fun t ht =>
    (GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Unit (R t) I (hiso t ht) s).2 r v hvI hvli
  have hwe : ∀ t, ∀ a, w a t ∈ eigSp (R t).B s := fun t a =>
    ((GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit (R t)).2.2.1 s).1 _
  have ht₀U := hWU ht₀
  obtain ⟨k, J, rfl, hli⟩ := GlobalTheory.T.exists_extend_linearIndependent_of_span g m r (fun a => w a t₀) (fun i => b i t₀) (hwl _ ht₀U) (hbl _ ht₀U)
    (fun a => by rw [hbs _ ht₀U]; exact hwe _ a)
  set c : Fin (r + k) → (Fin n → ℂ) → Fin g → ℂ := fun i t => Fin.append (fun a => w a t) (fun j => b (J j) t) i with hc
  have hch : ∀ i, DifferentiableOn ℂ (c i) W := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · simp only [hc, Fin.append_left]; exact (hwh a).mono hWU
    · simp only [hc, Fin.append_right]; exact (hb _).mono hWU
  have hcs : ∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t) := by
    intro t ht i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · simp only [hc, Fin.append_left]; rw [hbs t (hWU ht)]; exact hwe t a
    · simp only [hc, Fin.append_right]; exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨V, hVo, ht₀V, hVW, G, hG, hGl⟩ := GlobalTheory.T.holomorphic_span_coefficients E g Λ n (r + k) W R b c t₀ hW ht₀
    (fun i => (hb i).mono hWU) hch (fun t ht => hbl t (hWU ht)) hcs hli
  have hSc : ∀ t ∈ V, ((R t).gram fun i => c i t).det =
      ((R t).gram fun a => w a t).det * ((R' t).gram fun j => q t (b (J j) t)).det := by
    intro t ht
    have htW := hVW ht
    exact GlobalTheory.T.quotient_family_eigen_frame E g g' Λ Λ' (R t) (R' t) (q t) I s r k v (fun j => b (J j) t) (hiso t (hWU htW)) hv
      (hker t htW) (hcomp t htW) (fun j => by rw [← hbs t (hWU htW)]; exact Submodule.subset_span ⟨_, rfl⟩)
  have hcpos : ∀ t ∈ V, 0 < ((R t).gram fun i => c i t).det.re ∧ ((R t).gram fun i => c i t).det.im = 0 :=
    fun t ht => (GlobalTheory.T.gram_det_pos_iff_linearIndependent E g Λ (R t) _ _).1 (hGl t ht).1
  have hwpos : ∀ t ∈ V, 0 < ((R t).gram fun a => w a t).det.re ∧ ((R t).gram fun a => w a t).det.im = 0 :=
    fun t ht => (GlobalTheory.T.gram_det_pos_iff_linearIndependent E g Λ (R t) _ _).1 (hwl t (hWU (hVW ht)))
  have hul : ∀ t ∈ V, LinearIndependent ℂ fun j => q t (b (J j) t) := by
    intro t ht
    refine (GlobalTheory.T.gram_det_pos_iff_linearIndependent E g' Λ' (R' t) _ _).2 fun h0 => ?_
    have := hSc t ht
    rw [h0, mul_zero] at this
    have h1 := (hcpos t ht).1
    rw [this] at h1
    simp at h1
  have hup : IsPsh V (fun t => Real.log ((R' t).gram fun j => q t (b (J j) t)).det.re) :=
    (GlobalTheory.T.holomorphic_family_smooth_entries E g' Λ' Unit n V R' hVo (isHolFam_mono hR' hVW)).2.2 k (fun j t => q t (b (J j) t))
      (fun j => hol_apply (fun x => (hq x).mono hVW) (((hb _).mono hWU).mono hVW)) hul
  have hneg : DifferentiableOn ℂ (fun t => - G t) V := hG.neg
  have hfin := GroundTheory.Heights₂.Heights.NineStatements.isPsh_add_re_add_const hVo hup hneg 0
  refine ⟨V, hVo, ht₀V, hVW, GroundTheory.Heights₂.Heights.NineStatements.isPsh_congr' (fun t ht => ?_) hfin⟩
  have e1 := (hGl t ht).2
  have e2 := hSc t ht
  have hc1 := hcpos t ht
  have hw1 := hwpos t ht
  have hre : ((R t).gram fun i => c i t).det.re =
      ((R t).gram fun a => w a t).det.re * ((R' t).gram fun j => q t (b (J j) t)).det.re := by
    rw [e2, Complex.mul_re, hw1.2]; ring
  have hupos : ((R' t).gram fun j => q t (b (J j) t)).det.re ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hre
    rw [hre] at hc1
    exact lt_irrefl _ hc1.1
  rw [hre, Real.log_mul hw1.1.ne' hupos] at e1
  simp only [Complex.neg_re, add_zero]
  linarith

theorem localQuot {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ} (hU : IsOpen U) (hHol : IsHolFam U R)
    {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ U) {I : Submodule (𝓞 E) Λ} (hsat : IsSaturated I) (hiso : IsIsoSub (R t₀).form I) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ U ∧ ∃ (g' : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ')
      (R' : (Fin n → ℂ) → RiemLat E g' Λ') (q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)),
      IsHolFam W R' ∧ (∀ x, DifferentiableOn ℂ (fun t => q t x) W) ∧
      (∀ t ∈ W, LinearMap.ker (q t) = Submodule.span ℂ ((R t).P '' I)) ∧
      ∀ t ∈ W, ∀ y z, (∀ u ∈ I, (R t).ip ((R t).P u) y = 0) → (R' t).ip (q t y) (q t z) = (R t).ip y z := by
  obtain ⟨g', k, Λ', i1, i2, e, form', π, hk, hπ, hall⟩ := GlobalTheory.T.isotropic_quotient_structure E g Λ (R t₀) I hsat hiso
  have hform : ∀ t ∈ U, (R t).form = (R t₀).form := fun t ht => hHol.1 t ht t₀ ht₀
  obtain ⟨W, hWo, ht₀W, hWU, q, hq, hqs⟩ := GlobalTheory.T.holomorphic_local_quotient_map g' k g n U (fun i t => (R t).P (e i)) t₀ hU ht₀ hk
    (fun i => hHol.2 (e i)) (hall (R t₀) rfl).1
  have hker : ∀ t ∈ W, LinearMap.ker (q t) = Submodule.span ℂ ((R t).P '' I) := fun t ht => by
    rw [(hqs t ht).2, (hall (R t) (hform t (hWU ht))).2.1]
  have hex : ∀ t ∈ W, ∃ R' : RiemLat E g' Λ', R'.form = form' ∧
      (∀ x, (∀ y ∈ I, (R t).form x y = 0) → R'.P (π x) = q t ((R t).P x)) ∧
      ∀ x y, (∀ v ∈ I, (R t).ip ((R t).P v) x = 0) → R'.ip (q t x) (q t y) = (R t).ip x y := fun t ht =>
    (hall (R t) (hform t (hWU ht))).2.2 (q t) (hqs t ht).1 (hker t ht)
  have hex' : ∀ t, ∃ R' : RiemLat E g' Λ', t ∈ W → (R'.form = form' ∧
      (∀ x, (∀ y ∈ I, (R t).form x y = 0) → R'.P (π x) = q t ((R t).P x)) ∧
      ∀ x y, (∀ v ∈ I, (R t).ip ((R t).P v) x = 0) → R'.ip (q t x) (q t y) = (R t).ip x y) := by
    intro t
    by_cases ht : t ∈ W
    · obtain ⟨R', h⟩ := hex t ht
      exact ⟨R', fun _ => h⟩
    · obtain ⟨R', _⟩ := hex t₀ ht₀W
      exact ⟨R', fun h => absurd h ht⟩
  choose R' hR' using hex'
  refine ⟨W, hWo, ht₀W, hWU, g', Λ', i1, i2, R', q, ⟨fun t ht t' ht' => ?_, fun x' => ?_⟩, hq, hker,
    fun t ht => (hR' t ht).2.2⟩
  · rw [(hR' t ht).1, (hR' t' ht').1]
  · obtain ⟨x, hx, rfl⟩ := hπ x'
    have e1 : Set.EqOn (fun t => (R' t).P (π x)) (fun t => q t ((R t).P x)) W := fun t ht =>
      (hR' t ht).2.1 x (fun y hy => by rw [hform t (hWU ht)]; exact hx y hy)
    exact (hol_apply hq ((hHol.2 x).mono hWU)).congr e1

end GlobalTheory.CompanionTheory.Ar.Cusp.PhiI

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open GlobalTheory.CompanionTheory.Ar.Cusp.PhiI
open ReciprocityTheory.AnForm.A (IsPsh)

theorem phi_isPsh_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (I : Submodule (𝓞 E) Λ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → (∀ t ∈ U, (R t).IsCusp I) → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) - Real.log ((R t).nz σ I)) ∧ ContinuousOn (fun t => (R t).nz σ I) U := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m b I hU hHol hCM hB hC
  have hcusp : ∀ t ∈ U, I ≠ ⊥ ∧ IsIsoSub (R t).form I := fun t ht => ⟨(hC t ht).1, (hC t ht).2.2⟩
  rcases U.eq_empty_or_nonempty with rfl | ⟨t₁, ht₁⟩
  · refine ⟨GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n _ _ isOpen_empty (fun z hz => absurd hz (Set.notMem_empty z)),
      continuousOn_empty _⟩
  obtain ⟨⟨r, v, hv⟩, -⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t₁) σ I hCM (hcusp t₁ ht₁).2 (hcusp t₁ ht₁).1
  have hnz : ∀ t ∈ U, (R t).nz σ I = (R t).nzOf σ I v ∧ 0 < (R t).nz σ I := fun t ht => by
    have := ((GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I hCM (hcusp t ht).2 (hcusp t ht).1).2 r v hv)
    exact ⟨this.1, this.2.1⟩
  set w : Ψ → Fin r → (Fin n → ℂ) → Fin g → ℂ := fun τ a t => eigComp (R t).B (σ τ) ((R t).P (v a)) with hw
  set idx : ℝ := ((Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) with hidx
  have hidx0 : idx ≠ 0 := by
    rw [hidx]; exact_mod_cast hv.2.2.2
  have hwpos : ∀ t ∈ U, ∀ τ, 0 < ((R t).gram fun a => w τ a t).det.re := fun t ht τ =>
    ((GlobalTheory.T.gram_det_pos_iff_linearIndependent E g Λ (R t) _ _).1
      ((GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Unit (R t) I (hcusp t ht).2 (σ τ)).2 r v hv.2.1 hv.2.2.1)).1
  have hlog : ∀ t ∈ U, (R t).logDet (fun τ i => b τ i t) - Real.log ((R t).nz σ I) =
      (∑ τ, (Real.log ((R t).gram fun i => b τ i t).det.re - Real.log ((R t).gram fun a => w τ a t).det.re)) +
        Real.log idx := by
    intro t ht
    rw [(hnz t ht).1]
    unfold RiemLat.nzOf RiemLat.logDet
    rw [Real.log_div (Finset.prod_ne_zero_iff.2 fun τ _ => (hwpos t ht τ).ne') hidx0,
      Real.log_prod (fun τ _ => (hwpos t ht τ).ne'), Finset.sum_sub_distrib]
    ring
  refine ⟨GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun t₀ ht₀ => ?_, ?_⟩
  · obtain ⟨W, hWo, ht₀W, hWU, g', Λ', i1, i2, R', q, hR', hq, hker, hcomp⟩ :=
      localQuot hU hHol ht₀ (hC t₀ ht₀).2.1 (hcusp t₀ ht₀).2
    have hloc : ∀ τ, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧
        IsPsh V (fun t => Real.log ((R t).gram fun i => b τ i t).det.re -
          Real.log ((R t).gram fun a => w τ a t).det.re) := fun τ =>
      perEmb hHol hWo hWU ht₀W hR' hq hker hcomp (fun t ht => (hcusp t ht).2) (σ τ) hv (hB.1 τ)
        (fun t ht => (hB.2 t ht τ).1) (fun t ht => (hB.2 t ht τ).2)
    choose V hVo ht₀V hVW hVp using hloc
    classical
    let V₀ : Set (Fin n → ℂ) := W ∩ ⋂ τ, V τ
    have hV₀o : IsOpen V₀ := hWo.inter (isOpen_iInter_of_finite hVo)
    have hV₀ : ∀ τ, V₀ ⊆ V τ := fun τ x hx => Set.mem_iInter.1 hx.2 τ
    refine ⟨V₀, hV₀o, ⟨ht₀W, Set.mem_iInter.2 ht₀V⟩, ?_⟩
    have hs := isPsh_add (isPsh_sum Finset.univ fun τ _ => GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono (hV₀ τ) (hVp τ))
      (isPsh_zero V₀ (Real.log idx))
    exact GroundTheory.Heights₂.Heights.NineStatements.isPsh_congr' (fun t ht => (hlog t (hWU ht.1)).symm) hs
  · have hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U := by
      intro i j
      obtain ⟨h1, h2⟩ := (GlobalTheory.T.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hHol).1 i j
      have e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I := by
        funext t; exact (Complex.re_add_im _).symm
      rw [e]
      exact (Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add
        ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)
    have hwc : ∀ τ a, ContinuousOn (w τ a) U := fun τ a => (hol_eig hHol.2 (σ τ) (v a)).continuousOn
    have hip : ∀ τ a c, ContinuousOn (fun t => (R t).ip (w τ a t) (w τ c t)) U := by
      intro τ a c
      unfold RiemLat.ip
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      refine continuousOn_finset_sum _ fun i _ => ((continuousOn_pi.1 (hwc τ c) i)).mul ?_
      refine continuousOn_finset_sum _ fun j _ => (hHm i j).mul ?_
      exact (continuous_star.comp_continuousOn (continuousOn_pi.1 (hwc τ a) j))
    have hdet : ∀ τ, ContinuousOn (fun t => ((R t).gram fun a => w τ a t).det.re) U := by
      intro τ
      have hm : ContinuousOn (fun t => (R t).gram fun a => w τ a t) U :=
        continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => hip τ a c
      exact Complex.continuous_re.comp_continuousOn ((continuous_id.matrix_det).comp_continuousOn hm)
    have hc : ContinuousOn (fun t => (∏ τ, ((R t).gram fun a => w τ a t).det.re) / idx) U :=
      (continuousOn_finset_prod _ fun τ _ => hdet τ).div_const _
    refine hc.congr fun t ht => ?_
    rw [(hnz t ht).1]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cusp
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_cusp_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (I : Submodule (𝓞 E) Λ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → (∀ t ∈ U, (R t).IsCusp I) → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) - Real.log ((R t).nz σ I)) ∧ ContinuousOn (fun t => (R t).nz σ I) U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous
end

section
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  first | exact @LevelTowerAlt.cusps_locally_finite_family | exact LevelTowerAlt.cusps_locally_finite_family
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_submodules_locally_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite
end

section
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open ReciprocityTheory.AnForm.A (IsPsh)

theorem psh_add {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ) (hψ : IsPsh U ψ) :
    IsPsh U (fun z => φ z + ψ z) := by
  refine ⟨hφ.1.add hψ.1, fun z w hd => ?_⟩
  obtain ⟨h1, h2⟩ := hφ.2 z w hd
  obtain ⟨h3, h4⟩ := hψ.2 z w hd
  refine ⟨h1.add h3, ?_⟩
  rw [Real.circleAverage_fun_add h1 h3]
  exact add_le_add h2 h4

theorem psh_const {d : ℕ} (U : Set (Fin d → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) := by
  refine ⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩
  rw [Real.circleAverage_const]

theorem psh_sum {d : ℕ} {U : Set (Fin d → ℂ)} {ι : Type} (S : Finset ι) {f : ι → (Fin d → ℂ) → ℝ}
    (h : ∀ i ∈ S, IsPsh U (f i)) : IsPsh U (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psh_const U 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact psh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem psh_congr {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : ∀ z ∈ U, φ z = ψ z)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h z hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h x hxU]
  · obtain ⟨h1, h2⟩ := hφ.2 z w hd
    have e : ∀ θ : ℝ, φ (z + circleMap 0 1 θ • w) = ψ (z + circleMap 0 1 θ • w) := fun θ =>
      h _ (hd _ (by simp))
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    refine ⟨?_, ?_⟩
    · unfold CircleIntegrable at h1 ⊢
      simpa only [e] using h1
    · rw [← h z hz]
      simpa only [Real.circleAverage_def, e] using h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

noncomputable def term (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ)) :
    Option F → ℝ
  | none => 0
  | some I => -Real.log (R.nz σ I.1)

theorem cuspW_eq (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ))
    (h1 : ∀ I ∈ F, R.IsCusp I) (h2 : ∀ I, R.IsCusp I → R.nz σ I ≤ 1 → I ∈ F) :
    R.cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
  have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) :=
    Finset.le_sup' (term R σ F) (Finset.mem_univ none)
  have hb : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)},
      x ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
    rintro x ⟨I, hI, rfl⟩
    by_cases h : R.nz σ I ≤ 1
    · exact Finset.le_sup' (term R σ F) (Finset.mem_univ (some ⟨I, h2 I hI h⟩))
    · have := Real.log_nonneg (not_le.1 h).le
      linarith
  unfold RiemLat.cuspW
  refine le_antisymm (max_le h0 (Real.sSup_le hb h0)) (Finset.sup'_le _ _ fun o _ => ?_)
  cases o with
  | none => exact le_max_left _ _
  | some I => exact le_max_of_le_right (le_csSup ⟨_, hb⟩ ⟨I.1, h1 I.1 I.2, rfl⟩)

theorem add_sup {ι : Type} [Fintype ι] [Nonempty ι] (a : ℝ) (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j => a + f j) = a + Finset.univ.sup' Finset.univ_nonempty f := by
  refine le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) ?_
  · have := Finset.le_sup' f hj
    linarith
  · obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f
    rw [e]
    exact Finset.le_sup' (fun j => a + f j) hj

end GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open GlobalTheory.CompanionTheory.Ar.Cusp.Corr in
theorem _root_.GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m b hU hH hσ hb
  have hrank : ∀ t ∈ U, (R t).HasRank σ m := by
    intro t ht τ
    have h := hb.2 t ht τ
    have e : Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => b τ i t)) = m := by
      rw [finrank_span_eq_card h.1, Fintype.card_fin]
    rw [h.2] at e
    exact e
  have hL : ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) :=
    psh_sum Finset.univ fun τ _ =>
      (GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hH).2.2 m (b τ) (hb.1 τ) (fun t ht => (hb.2 t ht τ).1)
  have hloc : ∀ t₀ ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧
      ReciprocityTheory.AnForm.A.IsPsh (U ∩ W) (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧
      ContinuousOn (fun t => (R t).cuspW σ) (U ∩ W) := by
    intro t₀ ht₀
    obtain ⟨ε, F, hε, hF⟩ := GlobalTheory.T.cusp_submodules_locally_finite E g Λ Ψ n U R σ m hU hH hσ hrank t₀ ht₀
    have hVo : IsOpen (U ∩ Metric.ball t₀ ε) := hU.inter Metric.isOpen_ball
    have hVU : U ∩ Metric.ball t₀ ε ⊆ U := Set.inter_subset_left
    have hphi := fun I : F => GlobalTheory.T.log_det_cusp_frame_plurisubharmonic E g Λ Ψ n (U ∩ Metric.ball t₀ ε) R σ m b I.1 hVo
      ⟨fun t ht t' ht' => hH.1 t ht.1 t' ht'.1, fun x => (hH.2 x).mono hVU⟩ hσ
      ⟨fun τ i => (hb.1 τ i).mono hVU, fun t ht => hb.2 t ht.1⟩ (fun t ht => (hF t ht).1 I.1 I.2)
    have heq : ∀ t ∈ U ∩ Metric.ball t₀ ε,
        (R t).cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term (R t) σ F) :=
      fun t ht => cuspW_eq (R t) σ F (hF t ht).1 (hF t ht).2
    refine ⟨Metric.ball t₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_⟩
    · have hs := ReciprocityTheory.AnForm.A.isPsh_sup_thm n (Option F) (U ∩ Metric.ball t₀ ε)
        (fun o t => (R t).logDet (fun τ i => b τ i t) + term (R t) σ F o) hVo (fun o => by
          cases o with
          | none =>
            exact psh_congr (fun z _ => (add_zero _).symm) (GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono hVU hL)
          | some I => exact psh_congr (fun z _ => sub_eq_add_neg _ _) (hphi I).1)
      refine psh_congr (fun t ht => ?_) hs
      rw [heq t ht]
      exact add_sup _ _
    · have hc : ∀ o : Option F, ContinuousOn (fun t => term (R t) σ F o) (U ∩ Metric.ball t₀ ε) := by
        intro o
        cases o with
        | none => exact continuousOn_const
        | some I =>
          refine ContinuousOn.neg ((hphi I).2.log fun t ht => ?_)
          have hI := (hF t ht).1 I.1 I.2
          obtain ⟨⟨r, v, hv⟩, h2⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I.1 hσ hI.2.2 hI.1
          exact (h2 r v hv).2.1.ne'
      have hs : ContinuousOn (fun t => Finset.univ.sup' Finset.univ_nonempty (fun o => term (R t) σ F o))
          (U ∩ Metric.ball t₀ ε) :=
        ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun o _ => hc o
      exact hs.congr heq
  refine ⟨hL, GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun z hz => ?_,
    continuousOn_of_locally_continuousOn fun z hz => ?_⟩
  · obtain ⟨W, h1, h2, h3, -⟩ := hloc z hz
    exact ⟨U ∩ W, hU.inter h1, ⟨hz, h2⟩, h3⟩
  · obtain ⟨W, h1, h2, -, h4⟩ := hloc z hz
    exact ⟨W, h1, h2, h4⟩
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic
end
