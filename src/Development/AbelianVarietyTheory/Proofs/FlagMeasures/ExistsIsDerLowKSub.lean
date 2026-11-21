import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVector

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.DerOf

variable {n : ℕ} {ε : Fin n → Bool}

theorem rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : Rd X f g = Rd X f' g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

theorem eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Eab ε a b f g = Eab ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold Eab Ec
  rw [rd_congr h h1 hg, rd_congr h h2 hg]

theorem J_single_J (a b : Fin n) :
    Jm ε * Matrix.single a b (1 : ℂ) * Jm ε = (sgn ε a b : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Jm, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem sgn_comm (a b : Fin n) : sgn ε a b = sgn ε b a := by
  simp only [sgn, eq_comm]

theorem sgn_sq (a b : Fin n) : (sgn ε a b : ℂ) * sgn ε a b = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem cpart1_swap (a b : Fin n) : cpart1 ε (Matrix.single a b (1 : ℂ)) =
    ((-sgn ε a b : ℝ) : ℂ) • cpart1 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart1, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  push_cast
  match_scalars
  · linear_combination (-1 / 2 : ℂ) * this
  · ring

theorem cpart2_swap (a b : Fin n) : cpart2 ε (Matrix.single a b (1 : ℂ)) =
    ((sgn ε a b : ℝ) : ℂ) • cpart2 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart2, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  match_scalars
  · linear_combination (-1 / (2 * Complex.I) : ℂ) * this
  · ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H}

theorem exists_D (hV : ∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ D : Module.End ℂ V, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) (D v : H) 0 := by
  by_cases hX : inG ε X
  · choose d hd hd' using fun v : V => hV v v.2 X hX
    refine ⟨⟨⟨fun v => ⟨d v, hd v⟩, fun v w => Subtype.ext ?_⟩, fun c v => Subtype.ext ?_⟩, fun _ v => hd' v⟩
    · refine (hd' (v + w)).unique ?_
      simpa using (hd' v).fun_add (hd' w)
    · refine (hd' (c • v)).unique ?_
      simpa using (hd' v).fun_const_smul c
  · exact ⟨0, fun h => absurd h hX⟩

theorem rd_coef (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v v' : H}
    (h : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (y : H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g v'⟫_ℂ := by
  have h1 := (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  refine Eq.trans ?_ h1.deriv
  unfold Rd
  congr 1
  funext t
  have := hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t)
  simp only [this]
  rfl

theorem skew (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {x x' y y' : H}
    (hx : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) x' 0)
    (hy : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) y) y' 0) :
    ⟪x', y⟫_ℂ = -⟪x, y'⟫_ℂ := by
  have h := hx.inner ℂ hy
  have hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, σ (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hσ.2.1 _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

theorem exists_isDer : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H),
    IsURepOn (UJset ε) σ →
    (∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) →
    (∀ v ∈ V, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) →
    ∃ E : Fin n → Fin n → Module.End ℂ V, IsDer ε σ V E := by
  intro n ε H _ _ _ σ V hσ hV hs
  choose D hD using exists_D hV
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have h1 : ∀ v : H, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hc := fun a b : Fin n => complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have hR : ∀ X, inG ε X → ∀ (v : V) (y : H) g, inUJ ε g →
      Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (D X v)⟫_ℂ :=
    fun X hX v y g hg => rd_coef hσ hX (hD X hX v) y hg
  set E : Fin n → Fin n → Module.End ℂ V := fun a b =>
    D (cpart1 ε (Matrix.single a b 1)) + Complex.I • D (cpart2 ε (Matrix.single a b 1)) with hE
  have hEab : ∀ a b (v : V) (y : H) g, inUJ ε g →
      Eab ε a b (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro a b v y g hg
    unfold Eab Ec
    rw [hR _ (hc a b).1 v y g hg, hR _ (hc a b).2.1 v y g hg]
    simp [hE, inner_add_right, inner_smul_right]
  have hsm : ∀ X (r : ℝ), inG ε X → inG ε ((r : ℂ) • X) → ∀ v : V,
      (D ((r : ℂ) • X) v : H) = (r : ℂ) • (D X v : H) := by
    intro X r hX hrX v
    refine ext_inner_left ℂ fun y => ?_
    have := (rdLin n ε _ _ X X r 0 1 (hs v v.2 y) (hs v v.2 y) hX hX hone).2.1
    rwa [hR _ hX v y 1 hone, hR _ hrX v y 1 hone, h1, h1, ← inner_smul_right] at this
  refine ⟨E, ?_, ?_, ?_, fun v y => hs v v.2 y⟩
  · intro a b c d
    refine LinearMap.ext fun v => Subtype.ext (ext_inner_left ℂ fun y => ?_)
    have := eabGl n ε _ a b c d 1 (hs v v.2 y) hone
    rw [eab_congr (hEab c d v y) a b hone, eab_congr (hEab a b v y) c d hone] at this
    simp only [hEab _ _ _ y 1 hone, h1] at this
    split_ifs at this ⊢ <;> simpa [inner_sub_right] using this
  · intro a b x y
    have e1 := hsm _ (-sgn ε a b) (hc b a).1 (cpart1_swap a b ▸ (hc a b).1) y
    have e2 := hsm _ (sgn ε a b) (hc b a).2.1 (cpart2_swap a b ▸ (hc a b).2.1) y
    rw [← cpart1_swap] at e1
    rw [← cpart2_swap] at e2
    have s1 := skew hσ (hc a b).1 (hD _ (hc a b).1 x) (hD _ (hc a b).1 y)
    have s2 := skew hσ (hc a b).2.1 (hD _ (hc a b).2.1 x) (hD _ (hc a b).2.1 y)
    rw [e1, inner_smul_right] at s1
    rw [e2, inner_smul_right] at s2
    simp only [hE, Submodule.coe_inner, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      Submodule.coe_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, s1, s2,
      Complex.conj_I]
    push_cast
    ring
  · intro X hX v
    convert hD X hX v using 1
    refine ext_inner_left ℂ fun y => ?_
    have := ecSumV n ε ℂ _ X 1 (hs v v.2 y) hone
    obtain ⟨e1, e2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    simp only [eabV_eq, hEab _ _ _ y 1 hone, h1] at this
    rw [EcV, e1, e2, rdV_eq, rdV_eq, hR _ hX v y 1 hone, h1] at this
    simpa [Rd, inner_sum, inner_smul_right] using this.symm

end GlobalTheory.DerOf
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder ContDiff Topology Pointwise

namespace GlobalTheory.GardingStep

theorem hasDerivAt_orbit {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w v : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) (a : G → ℂ) (ha : Continuous a) (hs : HasCompactSupport a)
    (hw : ∫ y, a y • ρ y w ∂μ = v) (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (D : ℝ → G → ℂ) (hD : Continuous fun p : ℝ × G => D p.1 p.2)
    (hd : ∀ s y, HasDerivAt (fun t => a ((e t)⁻¹ * y)) (D s y) s) :
    HasCompactSupport (D 0) ∧ HasDerivAt (fun s => ρ (e s) v) (∫ y, D 0 y • ρ y w ∂μ) 0 := by
  have hint : Integrable (fun y => a y • ρ y w) μ :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hform : (fun s => ρ (e s) v) = fun s => ∫ y, a ((e s)⁻¹ * y) • ρ y w ∂μ := by
    funext s
    rw [← integral_mul_left_eq_self (fun y => a ((e s)⁻¹ * y) • ρ y w) (e s)]
    conv_lhs => rw [← hw]
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [inv_mul_cancel_left, hmul, map_smul]
  have hzero : ∀ s y, (e s)⁻¹ * y ∉ tsupport a → D s y = 0 := by
    intro s y hy
    have h1 : ∀ᶠ t in 𝓝 s, (e t)⁻¹ * y ∈ (tsupport a)ᶜ :=
      (he.inv.mul continuous_const).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport a).isOpen_compl.mem_nhds hy)
    have h2 : HasDerivAt (fun t => a ((e t)⁻¹ * y)) 0 s :=
      (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq
        (h1.mono fun t ht => image_eq_zero_of_notMem_tsupport ht)
    exact (hd s y).unique h2
  have hK : IsCompact ((fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a)) :=
    (isCompact_Icc.prod hs.isCompact).image ((he.comp continuous_fst).mul continuous_snd)
  set K := (fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hKdef
  have hcD : Continuous fun p : ℝ × G => D p.1 p.2 • ρ p.2 w := hD.smul (hc.comp continuous_snd)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    hcD.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun s y => a ((e s)⁻¹ * y) • ρ y w) (F' := fun s y => D s y • ρ y w) (x₀ := 0)
    (bound := K.indicator fun _ => M) (s := Set.Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun s =>
      ((ha.comp (continuous_const.mul continuous_id)).smul hc).aestronglyMeasurable)
    (by simpa [he0] using hint)
    (hcD.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y s hs' => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]; exact hM (s, y) ⟨hs', hy⟩
      · rw [Set.indicator_of_notMem hy, hzero s y, zero_smul, norm_zero]
        intro h
        exact hy ⟨(s, (e s)⁻¹ * y), ⟨hs', h⟩, by simp⟩)
    ((integrable_indicator_iff hK.isClosed.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun y s _ => (hd s y).smul_const _)
  refine ⟨HasCompactSupport.intro hs.isCompact fun y hy => hzero 0 y (by simpa [he0] using hy), ?_⟩
  rw [hform]
  exact key.2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_coef (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} {s v : H}
    (hα : SmoothOnG ε α) (hαc : HasCompactSupport (fun g : UJ ε => α (umat g)))
    (hfix : ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, v⟫_ℂ) (u : H) :
    SmoothOnG ε (fun g => ⟪u, σ g v⟫_ℂ) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  obtain ⟨F, hF, hFα⟩ := GlobalTheory.smoothOnG_exists_contDiff_extension n ε α hα
  have hmem : ∀ g : UJ ε, inUJ ε (umat g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : UJ ε => ⟪u, σ (umat g) s⟫_ℂ :=
    continuous_const.inner ((hcont s).comp_continuous hu hmem)
  have hlift : ∀ x, inUJ ε x → ∃ z : UJ ε, umat z = x := fun x hx => by
    have : x ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [show Set.range (fun g : UJ ε => umat g) = _ from hrange]; exact hx
    exact this
  have hinv : ∀ z : UJ ε, Jm ε * (umat z)ᴴ * Jm ε = umat z⁻¹ := fun z => by
    have h : (umat z)ᴴ * Jm ε * umat z = Jm ε := hmem z
    have i2 : umat z * umat z⁻¹ = 1 := Units.mul_inv _
    calc Jm ε * (umat z)ᴴ * Jm ε = Jm ε * (umat z)ᴴ * Jm ε * (umat z * umat z⁻¹) := by rw [i2, Matrix.mul_one]
      _ = Jm ε * ((umat z)ᴴ * Jm ε * umat z) * umat z⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Jm_mul_self, Matrix.one_mul]
  have hform : ∀ z : UJ ε, ⟪u, σ (umat z) v⟫_ℂ
      = ∫ g : UJ ε, α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro z
    rw [← ContinuousLinearMap.adjoint_inner_left, ← hfix,
      ← integral_mul_left_eq_self (fun g : UJ ε => α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = umat z * umat g := rfl
    simp only [inv_mul_cancel_left, e]
    rw [hmul _ (hmem z) _ (hmem g), ContinuousLinearMap.adjoint_inner_left]
    rfl
  intro g₀ hg₀
  have hC : IsCompact ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) :=
    hemb.isCompact_preimage (isCompact_closedBall g₀ 1)
  have hK := hC.mul hαc
  set K := ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) * tsupport (fun g : UJ ε => α (umat g))
  have hΨ : ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
      F (fun i j => (Jm ε * z.1ᴴ * Jm ε * z.2.1) i j) * z.2.2 := by
    refine ContDiff.mul (hF.comp ?_) (contDiff_snd.comp contDiff_snd)
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e1 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        star (z.1 a b) := fun a b =>
      Complex.conjCLE.contDiff.comp ((contDiff_apply_apply ℝ ℂ a b).comp contDiff_fst)
    have e2 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        z.2.1 a b := fun a b =>
      (contDiff_apply_apply ℝ ℂ a b).comp (contDiff_fst.comp contDiff_snd)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiff.sum fun a _ => (ContDiff.sum fun b _ => (ContDiff.sum fun c _ =>
      contDiff_const.mul (e1 _ _)).mul contDiff_const).mul (e2 _ _)
  refine ⟨Metric.ball g₀ 1, fun x => ∫ g in K, F (fun i j => (Jm ε * xᴴ * Jm ε * umat g) i j) *
    ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε), Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_, ?_⟩
  · exact (contDiff_infty.2 fun m =>
      GlobalTheory.GardingVec.contDiff_setIntegral_nat (muG ε) hK (hu.prodMk hb) m _ hΨ).contDiffOn
  · intro x hx hxJ
    obtain ⟨z, rfl⟩ := hlift x hxJ
    have e : ∀ g : UJ ε, F (fun i j => (Jm ε * (umat z)ᴴ * Jm ε * umat g) i j) = α (umat (z⁻¹ * g)) := fun g => by
      rw [hinv]; exact hFα _ (hmem (z⁻¹ * g))
    simp only [e]
    rw [hform z]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    exact hg ⟨z, Metric.ball_subset_closedBall hx, z⁻¹ * g,
      subset_tsupport _ fun h => hne (by rw [show α (umat (z⁻¹ * g)) = 0 from h, zero_mul]),
      mul_inv_cancel_left z g⟩

theorem contDiff_fderiv_mul {F : (Fin n → Fin n → ℂ) → ℂ} (hF : ContDiff ℝ ∞ F) (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => fderiv ℝ F y (X * y : Matrix _ _ ℂ) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ fun y : Fin n → Fin n → ℂ => fun i j => ∑ k, X i k * y k j :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ ℂ k j)
  exact h1.clm_apply h2

theorem garding_step : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s v : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ) → (∀ y, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (v' : H), SmoothOnG ε β ∧ HasCompactSupport (fun g : UJ ε => β (umat g)) ∧ (∀ y : H, ∫ g : UJ ε, β (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v'⟫_ℂ) ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
  intro n ε H _ _ _ σ α w v hσ hα hs hw
  refine ⟨smooth_coef hσ hα hs hw, fun X hX => ?_⟩
  obtain ⟨F, hF, hFα⟩ := smoothOnG_exists_contDiff_extension n ε α hα
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hum : ∀ a b : UJ ε, umat (a * b) = umat a * umat b := fun _ _ => rfl
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) w = σ (umat a) (σ (umat b) w) := by
    intro a b
    rw [hum, hσ.1.2 _ (hmem a) _ (hmem b)]; rfl
  have hc : Continuous fun y : UJ ε => σ (umat y) w := (hσ.2.2 w).comp_continuous hu hmem
  have hFα' : ∀ g : UJ ε, α (umat g) = F (umat g) := fun g => (hFα _ g.2).symm
  have ha : Continuous fun g : UJ ε => α (umat g) := by
    simp only [hFα']; exact hF.continuous.comp hu
  have hint : Integrable (fun y : UJ ε => α (umat y) • σ (umat y) w) (muG ε) :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hw' : ∫ y : UJ ε, α (umat y) • σ (umat y) w ∂(muG ε) = v := by
    refine ext_inner_left ℂ fun u => ?_
    rw [← integral_inner hint, ← hw u]
    simp only [inner_smul_right]
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  let e : ℝ → UJ ε := fun t =>
    ⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, exp_indefinite_unitary_holds n ε X hX t⟩
  have hev : ∀ t, umat (e t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
  have hei : ∀ t, umat (e t)⁻¹ = NormedSpace.exp ((t : ℂ) • (-X)) := fun t => by
    rw [smul_neg, Matrix.exp_neg, ← hev]
    exact Matrix.coe_units_inv _
  have he : Continuous e := by
    rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
    exact GlobalTheory.GardingVec.continuous_exp_curve X
  have he0 : e 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    show umat (e 0) = 1
    rw [hev]; simp
  have hcE := GlobalTheory.GardingVec.continuous_exp_curve (-X)
  have key := hasDerivAt_orbit (muG ε) (fun g => σ (umat g)) w v hmul hc _ ha hs hw' e he he0
    (fun s y => fderiv ℝ F (NormedSpace.exp ((s : ℂ) • (-X)) * umat y : Matrix _ _ ℂ)
      (NormedSpace.exp ((s : ℂ) • (-X)) * (-X) * umat y : Matrix _ _ ℂ))
    ((hfd.comp ((hcE.comp continuous_fst).matrix_mul (hu.comp continuous_snd))).clm_apply
      (((hcE.comp continuous_fst).matrix_mul continuous_const).matrix_mul (hu.comp continuous_snd)))
    (fun s y => by
      simp only [hFα']
      simp only [hum, hei]
      exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s
        (GlobalTheory.GardingVec.hasDerivAt_exp_mul (-X) (umat y) s))
  simp only [hev, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at key
  have hβ := contDiff_fderiv_mul hF (-X)
  refine ⟨fun y => fderiv ℝ F y (-X * y : Matrix _ _ ℂ), _,
    fun g _ => ⟨Set.univ, _, isOpen_univ, trivial, hβ.contDiffOn, fun _ _ _ => rfl⟩, key.1, fun u => ?_, key.2⟩
  have hβi : Integrable (fun y : UJ ε => fderiv ℝ F (umat y) (-X * umat y : Matrix _ _ ℂ) • σ (umat y) w)
      (muG ε) :=
    ((hβ.continuous.comp hu).smul hc).integrable_of_hasCompactSupport key.1.smul_right
  rw [← integral_inner hβi]
  simp only [inner_smul_right]

end GlobalTheory.GardingStep
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DerEx

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem smoothOnG_comb {n : ℕ} {ε : Fin n → Bool} {f g : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hg : SmoothOnG ε g) : SmoothOnG ε (fun x => c * f x + g x) := by
  intro x hx
  obtain ⟨U, F, hU, hxU, hF, hFf⟩ := hf x hx
  obtain ⟨U', G, hU', hxU', hG, hGg⟩ := hg x hx
  refine ⟨U ∩ U', fun y => c * F y + G y, hU.inter hU', ⟨hxU, hxU'⟩,
    (contDiffOn_const.mul (hF.mono Set.inter_subset_left)).add (hG.mono Set.inter_subset_right), ?_⟩
  intro y hy hyJ
  simp only [hFf y hy.1 hyJ, hGg y hy.2 hyJ]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem smoothOnG_zero {n : ℕ} (ε : Fin n → Bool) : SmoothOnG ε (fun _ => 0) := fun _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem exists_isDer_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsDer ε σ V E ∧ lowKSub ε lam σ ≤ V := by
  intro n ε lam H _ _ _ σ hσ hK
  let S : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ S, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ S,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ S, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ S) hσ hder hsm
  obtain ⟨α, h1, h2, h3⟩ := GlobalTheory.exists_smooth_fix_lowKSub n ε lam H σ hσ hK
  exact ⟨_, E, hE, fun s hs => Submodule.subset_span ⟨α, s, h1, h2, h3 s hs⟩⟩

end GlobalTheory.DerEx
end
