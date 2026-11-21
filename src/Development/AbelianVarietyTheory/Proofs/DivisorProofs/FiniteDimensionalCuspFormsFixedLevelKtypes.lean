import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenforms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalHarishChandraFiniteFormBoundedDetNormBan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroupStatement

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem finiteDimensional_of_totallyBounded_supBall :
    ∀ (T : Type) (V : Submodule ℂ (T → ℂ)) (B : Set T), (∀ φ ∈ V, (∀ x ∈ B, φ x = 0) → φ = 0) →
      (∀ φ ∈ V, ∃ M : ℝ, ∀ x ∈ B, ‖φ x‖ ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ F : Finset (T → ℂ), ∀ φ ∈ V, (∀ x ∈ B, ‖φ x‖ ≤ 1) →
        ∃ ψ ∈ F, ∀ x ∈ B, ‖φ x - ψ x‖ ≤ ε) → FiniteDimensional ℂ V := by
  intro T V B hinj hbdd htb
  classical
  have hmem : ∀ φ : V, Memℓp (fun x : B => (φ : T → ℂ) x) (⊤ : ENNReal) := by
    intro φ
    obtain ⟨M, hM⟩ := hbdd φ φ.2
    apply memℓp_infty
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hM x x.2
  let L : V →ₗ[ℂ] lp (fun _ : B => ℂ) (⊤ : ENNReal) :=
    { toFun := fun φ => ⟨fun x : B => (φ : T → ℂ) x, hmem φ⟩
      map_add' := fun φ ψ => lp.ext (funext fun _ => rfl)
      map_smul' := fun c φ => lp.ext (funext fun _ => rfl) }
  have hLapp : ∀ (φ : V) (x : B), (L φ) x = (φ : T → ℂ) x := fun _ _ => rfl
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun φ hφ => ?_
    have h0 : ∀ x ∈ B, (φ : T → ℂ) x = 0 := by
      intro x hx
      rw [← hLapp φ ⟨x, hx⟩, hφ]
      rfl
    exact Subtype.ext (hinj φ φ.2 h0)
  haveI : FiniteDimensional ℂ (LinearMap.range L) := by
    by_contra hfin
    obtain ⟨R, f, hR, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
    have hRpos : 0 < R := by linarith
    obtain ⟨F, hF⟩ := htb (1 / (3 * R)) (by positivity)
    have hpre : ∀ n, ∃ φ : V, L φ = (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)) := fun n => (f n).2
    choose φ hφ using hpre
    have hφle : ∀ n, ∀ x ∈ B, ‖(φ n : T → ℂ) x‖ ≤ R := by
      intro n x hx
      rw [← hLapp (φ n) ⟨x, hx⟩, hφ n]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _).trans (hfR n)
    have hball : ∀ n, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 1 := by
      intro n x hx
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
      rw [inv_mul_le_iff₀ hRpos, mul_one]
      exact hφle n x hx
    have hch : ∀ n, ∃ ψ ∈ F, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ x‖ ≤ 1 / (3 * R) :=
      fun n => hF _ (V.smul_mem _ (φ n).2) (hball n)
    choose ψ hψF hψ using hch
    obtain ⟨m, n, hmn, hmn'⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨ψ k, hψF k⟩ : F))
    have hψeq : ψ m = ψ n := congrArg Subtype.val hmn'
    have hpt : ∀ x ∈ B, ‖(φ m : T → ℂ) x - (φ n : T → ℂ) x‖ ≤ 2 / 3 := by
      intro x hx
      have h1 := hψ m x hx
      have h2 := hψ n x hx
      rw [hψeq] at h1
      have h3 : ‖((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 2 / (3 * R) := by
        calc _ = ‖(((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ψ n x) - (((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ n x)‖ := by
                congr 1; ring
          _ ≤ _ := norm_sub_le _ _
          _ ≤ 1 / (3 * R) + 1 / (3 * R) := add_le_add h1 h2
          _ = 2 / (3 * R) := by ring
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg hRpos.le] at h3
      rw [inv_mul_le_iff₀ hRpos] at h3
      calc _ ≤ R * (2 / (3 * R)) := h3
        _ = 2 / 3 := by field_simp
    have hnorm : ‖f m - f n‖ ≤ 2 / 3 := by
      show ‖((f m : lp (fun _ : B => ℂ) (⊤ : ENNReal)) - (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)))‖ ≤ 2 / 3
      rw [← hφ m, ← hφ n]
      refine lp.norm_le_of_forall_le (by norm_num) fun x => ?_
      rw [lp.coeFn_sub, Pi.sub_apply, hLapp, hLapp]
      exact hpt x x.2
    have := hsep hmn
    linarith
  exact LinearEquiv.finiteDimensional (LinearEquiv.ofInjective L hL).symm

end GlobalTheory
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_totallyBounded_supNormBall : ∀ (T : Type) (V : Submodule ℂ (T → ℂ)) (B : Set T), (∀ φ ∈ V, (∀ x ∈ B, φ x = 0) → φ = 0) → (∀ φ ∈ V, ∃ M : ℝ, ∀ x ∈ B, ‖φ x‖ ≤ M) → (∀ ε : ℝ, 0 < ε → ∃ F : Finset (T → ℂ), ∀ φ ∈ V, (∀ x ∈ B, ‖φ x‖ ≤ 1) → ∃ ψ ∈ F, ∀ x ∈ B, ‖φ x - ψ x‖ ≤ ε) → FiniteDimensional ℂ V := by
  atlas_forward_decl GlobalTheory.finiteDimensional_of_totallyBounded_supBall
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_exists_reproducing_testFunction_GL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  first | exact @GlobalTheory.HCAlphaGL.exists_alpha | exact GlobalTheory.HCAlphaGL.exists_alpha | (intros; apply GlobalTheory.HCAlphaGL.exists_alpha <;> assumption)
end

section
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Pointwise

namespace GlobalTheory.HCF.Equi

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL' : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf')

omit [IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

theorem absDetA_eq (g : GA E a) :
    absDetA g = (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) := by
  unfold absDetA
  exact GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) _

omit [IsTotallyComplex E] in

theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  rw [absDetA_eq, absDetA_eq, absDetA_eq, map_mul, map_mul, Positive.val_mul]

omit [IsTotallyComplex E] in

theorem continuous_absDetA : Continuous (absDetA (E := E) (a := a)) := by
  have e : (absDetA (E := E) (a := a)) =
      fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GroundTheory.Automorphic.AdelicGLn.det E a g) : ℝ) :=
    funext absDetA_eq
  rw [e]
  exact continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp
    (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))

theorem continuous_along (ψ : Sm E a) (g : GA E a) : Continuous fun z : GL (Fin a) (Cinf E) => ψ.1 (g * infGL E a z) := by
  have h := (ψ.2 g).continuousOn
  have h2 : Continuous fun z : GL (Fin a) (Cinf E) => chart ψ.1 g (toL z.val) :=
    h.comp_continuous (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)) : _) fun z => val_mem_invSet z
  exact h2.congr fun z => chart_val ψ.1 g z

theorem equicontinuous_band : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ),
    FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ U ∈ 𝓝 (1 : GA E a), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ g ∈ band E a, ∀ u ∈ U, g * u ∈ band E a → ‖φ.1 (g * u) - φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin a) (Cinf E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  set μ : Measure (GL (Fin a) (Cinf E)) := Measure.haar
  obtain ⟨α, hαc, hαs, hα⟩ := GlobalTheory.T.harishChandra_exists_reproducing_testFunction_GL E a L hL W hW X hX N μ inferInstance
  have hint : ∀ (ψ : Sm E a) (g : GA E a), Integrable (fun y => ψ.1 (g * infGL E a y) * α y) μ := fun ψ g =>
    ((continuous_along ψ g).mul hαc).integrable_of_hasCompactSupport hαs.mul_left

  have hrep : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g,
      ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hα x hx
    | zero => intro g; change ∫ z, (0 : ℂ) * α z ∂μ = 0; simp
    | add x y _ _ hx hy =>
      intro g
      change ∫ z, (x.1 (g * infGL E a z) + y.1 (g * infGL E a z)) * α z ∂μ = x.1 g + y.1 g
      simp_rw [add_mul]
      rw [integral_add (hint x g) (hint y g), hx, hy]
    | smul c x _ hx =>
      intro g
      change ∫ z, (c * x.1 (g * infGL E a z)) * α z ∂μ = c * x.1 g
      simp_rw [mul_assoc]
      rw [integral_const_mul, hx]

  have hfix : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ k ∈ L, ∀ x, φ.1 (x * finGL E a k) = φ.1 x := by
    intro φ hφ k hk x
    induction hφ using Submodule.span_induction with
    | mem ψ hψ => exact congrArg (fun f : Sm E a => f.1 x) (hψ.2.1 k hk)
    | zero => rfl
    | add ψ χ _ _ h1 h2 =>
      change ψ.1 (x * finGL E a k) + χ.1 (x * finGL E a k) = ψ.1 x + χ.1 x
      rw [h1, h2]
    | smul c ψ _ h =>
      change c * ψ.1 (x * finGL E a k) = c * ψ.1 x
      rw [h]

  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GL (Fin a) (Cinf E))
  have hKc : IsCompact (tsupport α) := hαs
  set K' := V * tsupport α with hK'
  have hK'c : IsCompact K' := hVc.mul hKc
  have hK'm : MeasurableSet K' := hK'c.measurableSet

  have hfc : Continuous fun z : GL (Fin a) (Cinf E) => absDetA (infGL E a z) :=
    continuous_absDetA.comp continuous_infGL'
  obtain ⟨B₁, hB₁⟩ := hK'c.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK'c.exists_bound_of_continuousOn
    (hfc.inv₀ fun z => (absDetA_pos _).ne').continuousOn
  set c := max 1 (max B₁ B₂) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcK : ∀ z ∈ K', c⁻¹ ≤ absDetA (infGL E a z) ∧ absDetA (infGL E a z) ≤ c := by
    intro z hz
    have hp := absDetA_pos (infGL E a z)
    have h1 := hB₁ z hz
    have h2 : ‖(absDetA (infGL E a z))⁻¹‖ ≤ B₂ := hB₂ z hz
    rw [Real.norm_of_nonneg hp.le] at h1
    rw [Real.norm_of_nonneg (inv_nonneg.2 hp.le)] at h2
    refine ⟨?_, h1.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
    rw [inv_le_comm₀ (by positivity) hp]
    exact h2.trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C, hC⟩ := GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N c hc1
  set C' := |C| + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set m := μ.real K' with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ := ε / (C' * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : C' * δ * (m + 1) = ε := by rw [hδ]; field_simp

  obtain ⟨v, hv, hvK⟩ := hK'c.mem_uniformity_of_prod (f := fun p x => α (p⁻¹ * x)) (s := Set.univ) (q := 1)
    (by exact (hαc.comp (continuous_fst.inv.mul continuous_snd)).continuousOn) (Set.mem_univ _)
    (Metric.dist_mem_uniformity hδ0)
  rw [nhdsWithin_univ] at hv

  refine ⟨{u | Matrix.GeneralLinearGroup.map (pInf E) u ∈ v ∩ V ∧ Matrix.GeneralLinearGroup.map (pFin E) u ∈ L}, ?_, ?_⟩
  · refine Filter.inter_mem ?_ ?_
    · exact continuous_mapInf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact Filter.inter_mem hv hV1)
    · exact continuous_mapFin.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hL.mem_nhds L.one_mem)
  intro φ hφ M hM g hg u hu _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 one_mem_band)
  set y := Matrix.GeneralLinearGroup.map (pInf E) u with hy
  set k := Matrix.GeneralLinearGroup.map (pFin E) u with hk
  have hyv : y ∈ v := hu.1.1
  have hyV : y ∈ V := hu.1.2
  have hkL : k ∈ L := hu.2
  have hgu : φ.1 (g * u) = φ.1 (g * infGL E a y) := by
    rw [← infGL_mul_finGL u, ← mul_assoc, hfix φ hφ k hkL]
  rw [hgu]

  have e1 : φ.1 (g * infGL E a y) = ∫ z, φ.1 (g * infGL E a z) * α (y⁻¹ * z) ∂μ := by
    rw [← hrep φ hφ (g * infGL E a y),
      ← integral_mul_left_eq_self (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) y]
    congr 1
    funext x
    simp only [map_mul, mul_assoc, inv_mul_cancel_left]
  have hi1 : Integrable (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) μ :=
    ((continuous_along φ g).mul (hαc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hαs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)))
  have e2 : φ.1 (g * infGL E a y) - φ.1 g = ∫ z, φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z) ∂μ := by
    rw [e1, ← hrep φ hφ g, ← integral_sub hi1 (hint φ g)]
    simp_rw [mul_sub]
  rw [e2]

  have hpt : ∀ z, ‖φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z)‖ ≤ K'.indicator (fun _ => C' * M * δ) z := by
    intro z
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, norm_mul]
      have hd := hcK z hz
      have hg' := hg
      obtain ⟨hg1, hg2⟩ := hg'
      have hb1 : c⁻¹ ≤ absDetA (g * infGL E a z) := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have hb2 : absDetA (g * infGL E a z) ≤ 2 * c := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have h1 : ‖φ.1 (g * infGL E a z)‖ ≤ C' * M :=
        (hC φ hφ M hM _ hb1 hb2).trans (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_abs_self C]) hM0)
      have h2 : ‖α (y⁻¹ * z) - α z‖ ≤ δ := by
        have := hvK y hyv z hz
        simp only [inv_one, one_mul, Set.mem_setOf_eq] at this
        rw [← dist_eq_norm]; exact this.le
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hz]
      have hz1 : α z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz ⟨1, mem_of_mem_nhds hV1, z, h, one_mul z⟩
      have hz2 : α (y⁻¹ * z) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hz ⟨y, hyV, y⁻¹ * z, h, mul_inv_cancel_left y z⟩
      simp [hz1, hz2]
  have hint' : Integrable (K'.indicator (fun _ => C' * M * δ)) μ :=
    (integrableOn_const (C := C' * M * δ) hK'c.measure_lt_top.ne).integrable_indicator hK'm
  refine (norm_integral_le_of_norm_le hint' (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_indicator_const _ hK'm, smul_eq_mul, ← hm]
  have : 0 ≤ C' * M * δ := by positivity
  calc m * (C' * M * δ) ≤ (m + 1) * (C' * M * δ) := by nlinarith
    _ = ε * M := by rw [← hδe]; ring

end GlobalTheory.HCF.Equi
end
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraForms_equicontinuous_on_band : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : GA E a), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ∀ g ∈ band E a, ∀ u ∈ U, g * u ∈ band E a → ‖φ.1 (g * u) - φ.1 g‖ ≤ ε * M := by
  atlas_forward_decl GlobalTheory.HCF.Equi.equicontinuous_band
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

open scoped Pointwise

namespace GlobalTheory.SiegelBand

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

theorem le_pow_mul_of_adjacent {a : ℕ} (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {Q : ℝ} (hQ : 1 ≤ Q)
    (hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i) (i j : Fin a) :
    ρ i ≤ Q ^ a * ρ j := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have key : ∀ m : ℕ, ∀ i j : Fin a, (j : ℕ) = i + m → ρ i ≤ Q ^ m * ρ j ∧ ρ j ≤ Q ^ m * ρ i := by
    intro m
    induction m with
    | zero =>
      intro i j h
      have : i = j := Fin.ext (by omega)
      subst this
      simp
    | succ m ih =>
      intro i j h
      let j' : Fin a := ⟨i + m, by omega⟩
      obtain ⟨h1, h2⟩ := ih i j' rfl
      obtain ⟨h3, h4⟩ := hadj j' j (by simp [j']; omega)
      have hpm : 0 ≤ Q ^ m := pow_nonneg hQ0 m
      constructor
      · calc ρ i ≤ Q ^ m * ρ j' := h1
          _ ≤ Q ^ m * (Q * ρ j) := mul_le_mul_of_nonneg_left h3 hpm
          _ = Q ^ (m + 1) * ρ j := by ring
      · calc ρ j ≤ Q * ρ j' := h4
          _ ≤ Q * (Q ^ m * ρ i) := mul_le_mul_of_nonneg_left h2 hQ0
          _ = Q ^ (m + 1) * ρ i := by ring
  rcases le_total (i : ℕ) j with hij | hij
  · have h := (key ((j : ℕ) - i) i j (by omega)).1
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)
  · have h := (key ((i : ℕ) - j) j i (by omega)).2
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)

theorem absDetA_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) :
    absDetA g = (ideleModule E (AdelicGLn.det E a g) : ℝ) := by
  unfold absDetA
  rw [Reduction.adeleAbs_units (K := E)]
  rfl

theorem posIdele_congr {E : Type} [Field E] [NumberField E] {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    Reduction.posIdele (K := E) x hx = Reduction.posIdele (K := E) y hy := by
  subst h; rfl

theorem exists_isCompact_band_siegel : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := by
  intro E _ _ a ω hω t R ht
  classical
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hfc : Continuous fun b : GA E a => (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := Reduction.exists_pos_bounds hω hfc
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  set Q : ℝ := max 1 (max R t⁻¹) with hQdef
  have hQ : 1 ≤ Q := le_max_left _ _
  set Qa : ℝ := (Q ^ a) ^ a with hQadef
  have hQa : 0 < Qa := pow_pos (pow_pos (zero_lt_one.trans_le hQ) _) _
  set lo : ℝ := min 1 (X₁ / Qa) with hlodef
  set hi : ℝ := max 1 (Qa * X₂) with hhidef
  have hlo : 0 < lo := lt_min one_pos (div_pos hX₁ hQa)
  let g : {r : ℝ // 0 < r} → IdeleGroup E := fun r => Reduction.posIdele (K := E) r.1 r.2
  have hg : Continuous g := Reduction.continuous_posIdele_subtype
  let h : (Fin a → ℝ) → (Fin a → IdeleGroup E) := fun ρ i => g ⟨max (ρ i) lo, hlo.trans_le (le_max_right _ _)⟩
  have hh : Continuous h := continuous_pi fun i => hg.comp
      (((continuous_apply i).max continuous_const).subtype_mk fun ρ => hlo.trans_le (le_max_right _ _))
  let F : (Fin a → ℝ) → GA E a := fun ρ => Reduction.diagUnits a (h ρ)
  have hF : Continuous F := (Reduction.continuous_diagUnits (K := E) a).comp hh
  have hT : IsCompact (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) := (isCompact_univ_pi fun _ => isCompact_Icc).image hF
  have hband : band E a = {g | 1 ≤ (ideleModule E (AdelicGLn.det E a g) : ℝ)} ∩
      {g | (ideleModule E (AdelicGLn.det E a g) : ℝ) ≤ 2} := by
    ext g; simp [band, absDetA_eq]
  have hclosed : IsClosed (band E a) := by
    rw [hband]; exact (isClosed_le continuous_const hfc).inter (isClosed_le hfc continuous_const)
  refine ⟨ω * (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) * (Reduction.maxCompact (K := E) (n := a) : Set (GA E a)) ∩ band E a,
    ((hω.mul hT).mul Reduction.isCompact_maxCompact).inter_right hclosed, Set.inter_subset_right, ?_⟩
  intro b hb ρ hρ hlow hup k hk hmem
  refine ⟨?_, hmem⟩
  set P : ℝ := ∏ i, ρ i with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => hρ i
  have hdet := Reduction.det_mul_mul b (Reduction.diagUnits a fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) k
  rw [Reduction.ideleModule_det_diagUnits_posIdele ρ hρ,
    Reduction.mem_normOneGL.1 (Reduction.maxCompact_le_normOneGL hk), mul_one] at hdet
  have hm := hmem
  simp only [band, Set.mem_setOf_eq, absDetA_eq] at hm
  rw [hdet] at hm
  obtain ⟨h1, h2⟩ := hm
  have hbb := hB b hb
  have hPd1 : P ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc P ^ d * B₁ ≤ P ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hbb.1 (pow_nonneg hP.le _)
      _ = _ := mul_comm _ _
      _ ≤ 2 := h2
  have hPd2 : B₂⁻¹ ≤ P ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ ≤ B₂ * P ^ d := mul_le_mul_of_nonneg_right hbb.2 (pow_nonneg hP.le _)
  have hPlow : X₁ ≤ P := by
    rcases le_or_gt 1 P with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hPd2.trans (pow_le_of_le_one hP.le h.le hd0.ne'))
  have hPup : P ≤ X₂ := by
    rcases le_or_gt P 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hPd1.trans (le_max_right _ _))
  have hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i := by
    intro i j hij
    constructor
    · exact (hup i j hij).trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (hρ j).le)
    · calc ρ j = t⁻¹ * (t * ρ j) := by field_simp
        _ ≤ t⁻¹ * ρ i := mul_le_mul_of_nonneg_left (hlow i j hij) (inv_nonneg.2 ht.le)
        _ ≤ Q * ρ i := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) (hρ i).le
  have hratio := le_pow_mul_of_adjacent ρ hρ hQ hadj
  have hbox : ∀ i, ρ i ∈ Set.Icc lo hi := by
    intro i
    have ha0 : a ≠ 0 := by have := i.2; omega
    have hup' : ρ i ^ a ≤ Qa * P := by
      calc ρ i ^ a = ∏ _j : Fin a, ρ i := by simp
        _ ≤ ∏ j : Fin a, (Q ^ a * ρ j) :=
          Finset.prod_le_prod (fun _ _ => (hρ i).le) fun j _ => hratio i j
        _ = Qa * P := by rw [Finset.prod_mul_distrib]; simp [hQadef, hPdef]
    have hlow' : P ≤ Qa * ρ i ^ a := by
      calc P = ∏ j : Fin a, ρ j := rfl
        _ ≤ ∏ _j : Fin a, (Q ^ a * ρ i) :=
          Finset.prod_le_prod (fun j _ => (hρ j).le) fun j _ => hratio j i
        _ = Qa * ρ i ^ a := by rw [Finset.prod_mul_distrib]; simp [hQadef]
    constructor
    · rcases le_or_gt 1 (ρ i) with h | h
      · exact (min_le_left _ _).trans h
      · refine (min_le_right _ _).trans ?_
        refine (pow_le_of_le_one (hρ i).le h.le ha0).trans' ?_
        rw [div_le_iff₀ hQa, mul_comm]
        exact hPlow.trans hlow'
    · rcases le_or_gt (ρ i) 1 with h | h
      · exact h.trans (le_max_left _ _)
      · exact (le_self_pow₀ h.le ha0).trans (hup'.trans
          ((mul_le_mul_of_nonneg_left hPup hQa.le).trans (le_max_right _ _)))
  have hFρ : F ρ = Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) := by
    show Reduction.diagUnits a (h ρ) = _
    congr 1
    funext i
    exact posIdele_congr _ _ (max_eq_left (hbox i).1)
  rw [← hFρ]
  exact Set.mul_mem_mul (Set.mul_mem_mul hb ⟨ρ, fun i _ => hbox i, rfl⟩) hk

end GlobalTheory.SiegelBand
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCompact_detBand_siegelSet : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := by
  atlas_forward_decl GlobalTheory.SiegelBand.exists_isCompact_band_siegel
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Filter
open scoped NumberField.AdeleRing

namespace GlobalTheory.InfConj

theorem continuous_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

def liftMat (E : Type) [Field E] [NumberField E] (a : ℕ)
    (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) : Matrix (Fin a) (Fin a) (Ad E) :=
  Matrix.of fun i j => (((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (Y i j), 0) : Ad E)

theorem continuous_liftMat (E : Type) [Field E] [NumberField E] (a : ℕ) : Continuous (liftMat E a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.prodMk ((continuous_mixedSpace_symm E).comp ?_) continuous_const
  exact (continuous_apply j).comp (continuous_apply i)

theorem liftMat_zero (E : Type) [Field E] [NumberField E] (a : ℕ) : liftMat E a 0 = 0 := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm 0 = 0
    exact map_zero _
  · rfl

theorem liftMat_archMat (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Ad E))
    (hZ : ∀ i j, (Z i j).2 = 0) : liftMat E a (GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z) = Z := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (InfiniteAdeleRing.ringEquiv_mixedSpace E (Z i j).1) = (Z i j).1
    exact RingEquiv.symm_apply_apply _ _
  · exact (hZ i j).symm

end GlobalTheory.InfConj

namespace GlobalTheory.InfConj

theorem conj_blockEntry_snd (E : Type) [Field E] [NumberField E] (a r : ℕ) (x : GA E a)
    (P : BlockIx a r → Ad E) (hP : ∀ p, (P p).2 = 0) (i j : Fin a) :
    ((((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j).2 = 0 := by
  let f : Matrix (Fin a) (Fin a) (Ad E) →+* Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) :=
    (RingHom.snd (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)).mapMatrix
  have hB : f (GroundTheory.Automorphic.AutomorphicForm.blockEntry P) = 0 := by
    refine Matrix.ext fun k l => ?_
    change (GroundTheory.Automorphic.AutomorphicForm.blockEntry P k l).2 = 0
    unfold GroundTheory.Automorphic.AutomorphicForm.blockEntry
    rw [Matrix.of_apply]
    split_ifs with h
    · exact hP _
    · rfl
  change f (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j = 0
  rw [map_mul, map_mul, hB, mul_zero, zero_mul]
  rfl

theorem conj_unip_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := by
  intro E _ _ a r U hU
  rw [(Units.isInducing_embedProduct (M := Matrix (Fin a) (Fin a) (Ad E))).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  let φ : Matrix (Fin a) (Fin a) (Ad E) → Matrix (Fin a) (Fin a) (Ad E) × (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    fun Z => (1 + Z, MulOpposite.op (1 - Z))
  have hφ : Continuous φ :=
    (continuous_const.add continuous_id).prodMk (MulOpposite.continuous_op.comp (continuous_const.sub continuous_id))
  have hφ0 : φ (liftMat E a 0) = Units.embedProduct _ (1 : GA E a) := by
    rw [liftMat_zero]
    simp only [φ, add_zero, sub_zero, Units.embedProduct_apply, inv_one, Units.val_one]
  have hnb : (φ ∘ liftMat E a) ⁻¹' t ∈ 𝓝 (0 : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) :=
    (hφ.comp (continuous_liftMat E a)).continuousAt.preimage_mem_nhds (by
      rw [Function.comp_apply, hφ0]; exact ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnb
  refine ⟨ε / 2, by positivity, fun x P hP hnorm => htU ?_⟩
  set Z := ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
    GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)) with hZdef
  have hmem : GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z ∈ Metric.ball 0 ε := by
    rw [mem_ball_zero_iff]; linarith
  have h1 := hball hmem
  rw [Set.mem_preimage, Function.comp_apply, liftMat_archMat E a Z (conj_blockEntry_snd E a r x P hP)] at h1
  rw [Set.mem_preimage]
  convert h1 using 1
  have hv : ((x⁻¹ * unip P * x : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1 + Z := by
    rw [Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 + nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_add, add_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  have hi : ((x⁻¹ * unip P * x : GA E a)⁻¹ : GA E a).val = 1 - Z := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 - nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_sub, sub_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  simp only [Units.embedProduct_apply, φ]
  rw [hv, hi]

end GlobalTheory.InfConj
end
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_archUnipotent_mem_nhds_one : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := by
  atlas_forward_decl GlobalTheory.InfConj.conj_unip_mem_nhds
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspTail

theorem norm_le_of_osc_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := by
  intro E _ _ _ a r hr hra φ _ hcusp hφ M hM x B hB
  set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef
  set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r
  have hD : IsAddFundamentalDomain (ratN E a r) D ν :=
    GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM
  have hD1 : ν D = 1 := GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM
  have hunip : (unip : (BlockIx a r → Ad E) → GA E a) =
      (GroundTheory.Automorphic.AutomorphicForm.unipGL (n := a) (r := r) (R := Ad E)) :=
    funext fun X => Units.ext rfl
  have hcont : Continuous fun X : BlockIx a r → Ad E => φ (unip X * x) := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    rw [hunip]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM
  have hint : IntegrableOn (fun X => φ (unip X * x)) D ν :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hDC
  have hmean : ∫ X in D, φ (unip X * x) ∂ν = 0 :=
    hcusp r hr hra ν D inferInstance hD x
  have hfin : ν D < ⊤ := by rw [hD1]; exact ENNReal.one_lt_top
  have hkey : ∫ X in D, (φ (unip X * x) - φ x) ∂ν = -φ x := by
    rw [integral_sub hint (integrableOn_const hfin.ne)]
    simp only [hmean, setIntegral_const, measureReal_def, hD1, ENNReal.toReal_one, one_smul, zero_sub]
  calc ‖φ x‖ = ‖∫ X in D, (φ (unip X * x) - φ x) ∂ν‖ := by rw [hkey, norm_neg]
    _ ≤ B * ν.real D := norm_setIntegral_le_of_norm_le_const hfin hB
    _ = B := by simp [measureReal_def, hD1]

end GlobalTheory.CuspTail
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_norm_le_of_oscillation_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := by
  atlas_forward_decl GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section
namespace GlobalTheory.HCF.Tail

theorem compactPart : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := GlobalTheory.T.exists_isCompact_detBand_siegelSet

theorem finConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup

theorem infConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := GlobalTheory.T.conj_archUnipotent_mem_nhds_one

theorem meanZero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := GlobalTheory.T.cuspidal_norm_le_of_oscillation_scaledUnipFD

section Band
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E),
    GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), map_mul, map_mul]
  rfl

theorem absDetA_ratGL (γ : GL (Fin a) E) : absDetA (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = GroundTheory.Global.IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map _ γ)
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal]
  rfl

theorem absDetA_unip {r : ℕ} (P : BlockIx a r → Ad E) : absDetA (unip P) = 1 := by
  unfold absDetA
  rw [det_unip]
  simpa [absDetA] using (absDetA_one (E := E) (a := a))

theorem absDetA_conj (x u : GA E a) (hu : absDetA u = 1) : absDetA (x * (x⁻¹ * u * x)) = absDetA x := by
  have h1 : absDetA x⁻¹ * absDetA x = 1 := by rw [← absDetA_mul, inv_mul_cancel, absDetA_one]
  rw [absDetA_mul, absDetA_mul, absDetA_mul, hu, mul_one, h1, mul_one]

theorem mem_band_ratGL_mul {γ : GL (Fin a) E} {g : GA E a} (hg : g ∈ band E a) : ratGL E a γ * g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_mul, absDetA_ratGL, one_mul] at hg ⊢
  exact hg

end Band

section Span
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {L : Subgroup (GL (Fin a) (Af E))}
  {W : Submodule ℂ (Kinf E a → ℂ)} {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ}

theorem span_left {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.1.left
  | zero => intro γ g; rfl
  | add x y _ _ hx hy => intro γ g; simp [hx γ g, hy γ g]
  | smul c x _ hx => intro γ g; simp [hx γ g]

theorem span_fin {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ l ∈ L, finRep E a l φ = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.2.1
  | zero => intro l _; exact map_zero _
  | add x y _ _ hx hy => intro l hl; rw [map_add, hx l hl, hy l hl]
  | smul c x _ hx => intro l hl; rw [map_smul, hx l hl]

theorem span_right {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) {l : GL (Fin a) (Af E)} (hl : l ∈ L)
    (g : GA E a) : φ.1 (g * finGL E a l) = φ.1 g :=
  congrFun (congrArg Subtype.val (span_fin hφ l hl)) g

theorem span_cont (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) : Continuous φ.1 := by
  refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ ?_
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun l => k * l) '' (L : Set (GL (Fin a) (Af E))), ?_, ?_, ⟨1, L.one_mem, mul_one k⟩⟩
  · rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, span_fin hφ l hl]
    exact hk
  · exact (Homeomorph.mulLeft k).isOpenMap _ hL

end Span

open GroundTheory.Automorphic.Reduction in
theorem oneRoot (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (hX : X.Finite) (N : ℕ)
    {ω : Set (GA E a)} (hω : IsCompact ω) (hωB : ω ⊆ (adelicBorel (K := E) (n := a) : Set (GA E a)))
    {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 0 < r) (hra : r < a) :
    ∃ R : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ k ∈ (maxCompact (K := E) (n := a)),
      b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
      R * ρ ⟨r, hra⟩ ≤ ρ ⟨r - 1, by omega⟩ →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k)‖ ≤ ε * M := by
  obtain ⟨U, hU, hequi⟩ := GlobalTheory.T.harishChandraForms_equicontinuous_on_band E a L hL W hW X hX N ε hε
  obtain ⟨M₀, hM₀, hfin⟩ := finConj E a r L hL ω hω
  obtain ⟨C₁, hC₁⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_norm_archMat_conj_le hω hωB ht hr hra
    (GroundTheory.Automorphic.isCompact_scaledInfSet (K := E) M₀)
  obtain ⟨δ, hδ, hinf⟩ := infConj E a r U hU
  refine ⟨max C₁ 0 / δ + 1, ?_⟩
  intro φ hφ hcusp M hM b hb ρ hρ hs k hk hband hR
  set x := b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k with hx
  have hq0 : 0 < ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ := div_pos (hρ _) (hρ _)
  have hgain : C₁ * (ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩) ≤ δ := by
    set q := ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩
    set c := max C₁ 0
    have hc0 : 0 ≤ c := le_max_right _ _
    have hRq : (c / δ + 1) * q ≤ 1 := by
      rw [show q = ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ from rfl, mul_div_assoc', div_le_one (hρ _)]
      exact hR
    have h1 : C₁ * q ≤ c * q := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le
    have h2 : c * q ≤ δ := by
      have e : c = δ * (c / δ) := by field_simp
      nlinarith [mul_nonneg (div_nonneg hc0 hδ.le) hq0.le]
    linarith
  refine meanZero E a r hr hra φ.1 (span_left hφ) hcusp (span_cont hL hφ) M₀ hM₀ x (ε * M) ?_
  intro Y hY
  have hsplit : unip Y * x = x * (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x) *
      (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) * x) := by
    conv_lhs => rw [← GroundTheory.Automorphic.CuspidalSpectrum.truncInf_add_truncFin Y, unip_add]
    group
  obtain ⟨l, hl, hle⟩ := hfin b hb ρ hρ k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) (fun p => rfl)
    (fun p => GroundTheory.Automorphic.exists_finite_eq_natCast_mul hM₀ hY p)
  have hv : x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x ∈ U :=
    hinf x _ (fun p => rfl) ((hC₁ b hb ρ hρ hs k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.infinite_mem_scaledInfSet hM₀ hY p)).trans hgain)
  rw [hsplit, hle, span_right hφ hl]
  refine hequi φ hφ M hM x hband _ hv ?_
  have h := absDetA_conj x (unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y)) (absDetA_unip _)
  simp only [band, Set.mem_setOf_eq] at hband ⊢
  rw [h]
  exact hband

open GroundTheory.Automorphic.Reduction in

theorem tails : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W →
    ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : Set (GA E a), IsCompact C ∧
    C ⊆ band E a ∧ ∀ g ∈ band E a, (∃ γ : GL (Fin a) E, ratGL E a γ * g ∈ C) ∨
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ‖φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  have hex : ∀ r : ℕ, ∀ (hr : 0 < r) (hra : r < a), ∃ R : ℝ, _ := fun r hr hra =>
    oneRoot E a L hL W hW X hX N hω hωB ht hε hr hra
  choose Rf hRf using hex
  set R : ℝ := 1 + ∑ r : Fin a, if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0 with hRdef
  have hRle : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), Rf r hr hra ≤ R := by
    intro r hr hra
    have h1 := Finset.single_le_sum (f := fun r : Fin a => if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hra⟩)
    simp only [hr, dif_pos] at h1
    linarith [le_max_left (Rf r hr hra) 0]
  obtain ⟨C, hC, hCb, hCmem⟩ := compactPart E a ω hω t R ht
  refine ⟨C, hC, hCb, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg g
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, k, hk, he⟩ := hγ
  have he' : ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k := he
  have hgb : ratGL E a γ * g ∈ band E a := mem_band_ratGL_mul hg
  by_cases hall : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), ρ ⟨r - 1, by omega⟩ ≤ R * ρ ⟨r, hra⟩
  · refine Or.inl ⟨γ, ?_⟩
    rw [he'] at hgb ⊢
    refine hCmem b hb ρ hρ hs (fun i j hij => ?_) k hk hgb
    have h1 := hall j (by omega) j.2
    have e : (⟨(j : ℕ) - 1, by omega⟩ : Fin a) = i := Fin.ext (by simp; omega)
    rwa [e] at h1
  · push_neg at hall
    obtain ⟨r, hr, hra, hlt⟩ := hall
    refine Or.inr fun φ hφ hc M hM => ?_
    rw [← span_left hφ γ g, he']
    rw [he'] at hgb
    refine hRf r hr hra φ hφ hc M hM b hb ρ hρ hs k hk hgb ?_
    exact (mul_le_mul_of_nonneg_right (hRle r hr hra) (hρ _).le).trans hlt.le

end GlobalTheory.HCF.Tail

end
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_uniformly_small_outside_compact_band : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧ ∀ g ∈ band E a, (∃ γ : GL (Fin a) E, ratGL E a γ * g ∈ C) ∨ ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ‖φ.1 g‖ ≤ ε * M := by
  atlas_forward_decl GlobalTheory.HCF.Tail.tails
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem totallyBounded_sup_of_equicontinuous_tails
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G)
    (Φ : Set (G → ℂ))
    (hinv : ∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g)
    (hbd : ∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B →
      ‖φ (g * u) - φ g‖ ≤ ε)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧
      ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  classical
  intro ε hε
  have hδpos : 0 < ε / 4 := by positivity
  obtain ⟨U, hU, hUeq⟩ := heq (ε / 4) hδpos
  obtain ⟨C, hCc, hCB, hCt⟩ := htail (ε / 4) hδpos
  obtain ⟨t, htC, hCcov⟩ := hCc.elim_nhds_subcover (fun x => (fun h => x⁻¹ * h) ⁻¹' U) (by
    intro x _
    have hc : Continuous (fun h : G => x⁻¹ * h) := continuous_const.mul continuous_id
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hU)
  let T : (G → ℂ) → (t → ℂ) := fun φ i => φ i
  have hTb : T '' Φ ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    exact hbd φ hφ i (hCB (htC i i.2))
  have htb : TotallyBounded (T '' Φ) :=
    ((isCompact_closedBall (0 : t → ℂ) 1).totallyBounded).subset hTb
  obtain ⟨s, hsT, hsf, hscov⟩ := Metric.finite_approx_of_totallyBounded htb (ε / 4) hδpos
  let c : (t → ℂ) → (G → ℂ) := fun y => if h : ∃ φ ∈ Φ, T φ = y then h.choose else 0
  have hc : ∀ y ∈ s, c y ∈ Φ ∧ T (c y) = y := by
    intro y hy
    have h : ∃ φ ∈ Φ, T φ = y := hsT hy
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨hsf.toFinset.image c, fun φ hφ => ?_⟩
  obtain ⟨y, hy, hdist⟩ : ∃ y ∈ s, dist (T φ) y < ε / 4 := by
    have := hscov ⟨φ, hφ, rfl⟩
    simpa using this
  obtain ⟨hψ, hTψ⟩ := hc y hy
  refine ⟨c y, Finset.mem_image.2 ⟨y, hsf.mem_toFinset.2 hy, rfl⟩, fun g hg => ?_⟩
  rcases hCt g hg with ⟨s', hs', hsg⟩ | hsmall
  · obtain ⟨x, hxt, hxU⟩ : ∃ x ∈ t, x⁻¹ * (s' * g) ∈ U := by
      have := hCcov hsg
      simpa using this
    have hxB : x ∈ B := hCB (htC x hxt)
    have hmul : x * (x⁻¹ * (s' * g)) = s' * g := mul_inv_cancel_left x _
    have hsgB : s' * g ∈ B := hCB hsg
    have h1 := hUeq φ hφ x hxB _ hxU (by rw [hmul]; exact hsgB)
    have h2 := hUeq (c y) hψ x hxB _ hxU (by rw [hmul]; exact hsgB)
    rw [hmul] at h1 h2
    have h3 : ‖φ x - c y x‖ ≤ ε / 4 := by
      calc ‖φ x - c y x‖ = dist (T φ ⟨x, hxt⟩) (T (c y) ⟨x, hxt⟩) := (dist_eq_norm _ _).symm
        _ ≤ dist (T φ) (T (c y)) := dist_le_pi_dist _ _ _
        _ = dist (T φ) y := by rw [hTψ]
        _ ≤ ε / 4 := hdist.le
    rw [← hinv φ hφ s' hs' g, ← hinv (c y) hψ s' hs' g]
    calc ‖φ (s' * g) - c y (s' * g)‖
        = ‖(φ (s' * g) - φ x) + (φ x - c y x) - (c y (s' * g) - c y x)‖ := by congr 1; ring
      _ ≤ ‖φ (s' * g) - φ x‖ + ‖φ x - c y x‖ + ‖c y (s' * g) - c y x‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ ≤ ε := by linarith
  · exact (norm_sub_le _ _).trans (by linarith [hsmall φ hφ, hsmall (c y) hψ])

end GlobalTheory
end

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyBounded_sup_of_equicontinuous_invariant_tails : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G) (Φ : Set (G → ℂ)), (∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g) → (∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1) → (∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B → ‖φ (g * u) - φ g‖ ≤ ε) → (∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) → ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  atlas_forward_decl GlobalTheory.totallyBounded_sup_of_equicontinuous_tails
end

section
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem finiteDimensional_cuspGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ V : Submodule ℂ (Sm E a), V ≤ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) → (∀ φ ∈ V, IsCuspidal φ.1) → FiniteDimensional ℂ V := by
  intro E _ _ _ a L hL W hW X hX N V hV hc
  have hleft : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ (γ : GL (Fin a) E) (g : GA E a),
      φ.1 (ratGL E a γ * g) = φ.1 g := by
    intro φ hφ γ g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy =>
      change x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g
      rw [hx, hy]
    | smul c x _ hx =>
      change c * x.1 (ratGL E a γ * g) = c * x.1 g
      rw [hx]
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ V' := by
    refine GlobalTheory.T.finiteDimensional_of_totallyBounded_supNormBall (GA E a) V' (band E a) ?_ ?_ ?_
    · rintro _ ⟨φ, hφ, rfl⟩ h0
      funext g
      obtain ⟨C, hC⟩ := GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N (max 1 (max (absDetA g) (absDetA g)⁻¹)) (le_max_left _ _)
      have hp := absDetA_pos g
      have h1 : (max 1 (max (absDetA g) (absDetA g)⁻¹))⁻¹ ≤ absDetA g := by
        rw [inv_le_comm₀ (by positivity) hp]
        exact (le_max_right _ _).trans (le_max_right _ _)
      have h2 : absDetA g ≤ 2 * max 1 (max (absDetA g) (absDetA g)⁻¹) := by
        have := (le_max_left (absDetA g) (absDetA g)⁻¹).trans (le_max_right 1 _)
        have := le_max_left 1 (max (absDetA g) (absDetA g)⁻¹)
        linarith
      have := hC φ (hV hφ) 0 (fun h hh => by rw [show φ.1 h = 0 from h0 h hh, norm_zero]) g h1 h2
      simpa using this
    · rintro _ ⟨φ, hφ, rfl⟩
      exact GlobalTheory.T.cuspidal_harishChandraFiniteForm_bounded_detNormBand E a L hL W hW X hX N φ (hV hφ) (hc φ hφ)
    · intro ε hε
      obtain ⟨F, hF⟩ := GlobalTheory.T.totallyBounded_sup_of_equicontinuous_invariant_tails (GA E a) (Set.range (ratGL E a)) (band E a)
        {f | ∃ φ ∈ V, φ.1 = f ∧ ∀ x ∈ band E a, ‖f x‖ ≤ 1}
        (by rintro f ⟨φ, hφ, rfl, -⟩ s ⟨γ, rfl⟩ g; exact hleft φ (hV hφ) γ g)
        (by rintro f ⟨φ, -, rfl, hb⟩; exact hb)
        (by
          intro ε hε
          obtain ⟨U, hU, h⟩ := GlobalTheory.T.harishChandraForms_equicontinuous_on_band E a L hL W hW X hX N ε hε
          refine ⟨U, hU, ?_⟩
          rintro f ⟨φ, hφ, rfl, hb⟩ g hg u hu hgu
          simpa using h φ (hV hφ) 1 hb g hg u hu hgu)
        (by
          intro ε hε
          obtain ⟨C, hC, hCB, h⟩ := GlobalTheory.T.cuspForms_uniformly_small_outside_compact_band E a L hL W hW X hX N ε hε
          refine ⟨C, hC, hCB, fun g hg => ?_⟩
          rcases h g hg with ⟨γ, hγ⟩ | h'
          · exact Or.inl ⟨_, ⟨γ, rfl⟩, hγ⟩
          · refine Or.inr ?_
            rintro f ⟨φ, hφ, rfl, hb⟩
            simpa using h' φ (hV hφ) (hc φ hφ) 1 hb) ε hε
      refine ⟨F, ?_⟩
      rintro _ ⟨φ, hφ, rfl⟩ hb
      exact hF _ ⟨φ, hφ, rfl, hb⟩
  exact (Submodule.equivMapOfInjective (Sm E a).subtype Subtype.val_injective V).symm.finiteDimensional

end GlobalTheory.HCF

end
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspidalForms_GL_totallyComplex : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ V : Submodule ℂ (Sm E a), V ≤ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) → (∀ φ ∈ V, IsCuspidal φ.1) → FiniteDimensional ℂ V := by
  atlas_forward_decl GlobalTheory.HCF.finiteDimensional_cuspGL
end

section
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory Topology

noncomputable section

namespace GlobalTheory.HCFCusp

theorem finiteDimensional_cuspSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α : Lie E a → ℂ, IsTest (invSet E a) α → (∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1) → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}) := by
  intro E _ _ _ a L hL W _ χ N ν _ α _ _
  have hopen : ∀ φ : Sm E a, (∀ k ∈ L, finRep E a k φ = φ) → IsOpen {k | finRep E a k φ = φ} := by
    intro φ hφ
    rw [isOpen_iff_forall_mem_open]
    intro k hk
    refine ⟨(k * ·) '' (L : Set (GL (Fin a) (Af E))), ?_, isOpenMap_mul_left k _ hL, ⟨1, L.one_mem, mul_one k⟩⟩
    rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, hφ l hl]
    exact hk
  refine GlobalTheory.T.finiteDimensional_cuspidalForms_GL_totallyComplex E a L hL W ‹_› {χ} (Set.finite_singleton χ) N _
    (Submodule.span_mono fun φ hφ => hφ.1) ?_
  intro φ hφ
  have P : (∀ k ∈ L, finRep E a k φ = φ) ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsCuspidal φ.1 := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨hx.1.2.1, hx.1.1.left, hx.2⟩
    | zero =>
      refine ⟨fun k _ => map_zero _, fun _ _ => rfl, fun r _ _ _ _ μ 𝓕 _ _ g => ?_⟩
      change ∫ z in 𝓕, (0 : ℂ) ∂μ = 0
      exact integral_zero _ _
    | add x y _ _ hx hy =>
      refine ⟨fun k hk => by rw [map_add, hx.1 k hk, hy.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change x.1 _ + y.1 _ = x.1 g + y.1 g
        rw [hx.2.1, hy.2.1]
      · haveI := hμ
        have ix := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a x (hopen x hx.1)) hx.2.1 μ h𝓕 g
        have iy := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a y (hopen y hy.1)) hy.2.1 μ h𝓕 g
        change ∫ z in 𝓕, (x.1 (unip z * g) + y.1 (unip z * g)) ∂μ = 0
        rw [integral_add ix iy, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, hy.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, add_zero]
    | smul c x _ hx =>
      refine ⟨fun k hk => by rw [map_smul, hx.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change c * x.1 _ = c * x.1 g
        rw [hx.2.1]
      · change ∫ z in 𝓕, c * x.1 (unip z * g) ∂μ = 0
        rw [integral_const_mul, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, mul_zero]
  exact P.2.2

end GlobalTheory.HCFCusp

end
end

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspForms_fixedLevel_Ktypes : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α : Lie E a → ℂ, IsTest (invSet E a) α → (∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1) → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}) := by
  atlas_forward_decl GlobalTheory.HCFCusp.finiteDimensional_cuspSpan
end
