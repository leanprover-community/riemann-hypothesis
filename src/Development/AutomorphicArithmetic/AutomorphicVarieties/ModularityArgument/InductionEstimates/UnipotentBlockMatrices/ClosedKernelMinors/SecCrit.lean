import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmissibleCuspFormsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TensInterp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem secStr_side {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ : Submodule ℂ (L2 μ₂)) (D : TypeDat K n) (hτ : CuspIrr μ₂ τ) (ι : G1 K 2 →* G1 K n)
    (hι : Continuous ι) (hιK : ∀ x ∈ KG K 2, ι x ∈ KG K n) (hK : IsCompact (KG K n : Set (G1 K n))) :
    ∃ E : Submodule ℂ (G1 K 2 → ℂ), FiniteDimensional ℂ E ∧ (∀ φ ∈ E, Rd τ φ) ∧
      ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, ∀ k ∈ KG K n,
        (∃ v ∈ τ, Reps μ₂ v fun m => f (g * ι m * k)) → (fun m => f (g * ι m * k)) ∈ E := by
  classical
  obtain ⟨-, hUK, 𝒜, hfd, hA, hfix⟩ := typeFin D
  obtain ⟨O, hO, hOU⟩ := D.isOpen
  have hmem : ∀ g ∈ KG K n, g ∈ D.U ↔ (g : AdelicGLn.AdelicGL K n) ∈ O := fun g hg =>
    ⟨fun h => ((hOU g).1 h).1, fun h => (hOU g).2 ⟨h, hg⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun k : KG K n => {y : G1 K n | (((k : G1 K n)⁻¹ * y : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O})
    (fun k => hO.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id)))
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by
      have := (hmem 1 (one_mem _)).1 (one_mem _)
      simpa using this⟩)
  let c : KG K n → G1 K 2 →* G1 K n := fun k => (MulAut.conj ((k : G1 K n)⁻¹)).toMonoidHom.comp ι
  have hc : ∀ k x, c k x = (k : G1 K n)⁻¹ * ι x * k := fun k x => by simp [c]
  have hcc : ∀ k, Continuous (c k) := fun k => by
    have : (c k : G1 K 2 → G1 K n) = fun x => (k : G1 K n)⁻¹ * ι x * k := funext (hc k)
    rw [this]
    exact (continuous_const.mul hι).mul continuous_const
  let U : Subgroup (G1 K 2) := KG K 2 ⊓ ⨅ j : t, D.U.comap (c j)
  have hU : ∀ x, x ∈ U ↔ x ∈ KG K 2 ∧ ∀ j : t, c j x ∈ D.U := fun x => by
    simp only [U, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  let d : t → U → D.U := fun j x => ⟨c j x, ((hU x).1 x.2).2 j⟩
  have hd : ∀ j, Continuous (d j) := fun j => ((hcc j).comp continuous_subtype_val).subtype_mk _
  have hdm : ∀ j x y, d j (x * y) = d j x * d j y := fun j x y => Subtype.ext (map_mul (c j) _ _)
  let ℬ : Submodule ℂ (U → ℂ) := ⨆ j : t, 𝒜.map (LinearMap.funLeft ℂ ℂ (d j))
  have hin : ∀ j, ∀ a ∈ 𝒜, (fun x => a (d j x)) ∈ ℬ := fun j a ha =>
    Submodule.mem_iSup_of_mem j ⟨a, ha, rfl⟩
  have hcK : ∀ j : KG K n, ∀ x ∈ KG K 2, c j x ∈ KG K n := fun j x hx => by
    rw [hc]
    exact mul_mem (mul_mem (inv_mem j.2) (hιK x hx)) j.2
  obtain ⟨E, hE, hR, hP⟩ := adm μ₂ τ hτ U inf_le_left
    ⟨⋂ j : t, {x | ((c j x : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O},
      isOpen_iInter_of_finite fun j => hO.preimage (continuous_subtype_val.comp (hcc j)), fun x hx => by
        rw [hU, Set.mem_iInter]
        exact ⟨fun h j => (hmem _ (hcK j x hx)).1 (h.2 j), fun h => ⟨hx, fun j => (hmem _ (hcK j x hx)).2 (h j)⟩⟩⟩
    ℬ inferInstance (fun a ha => by
      refine Submodule.iSup_induction _ (motive := fun a : U → ℂ => Continuous a ∧ ∀ u : U, (fun x => a (x * u)) ∈ ℬ) ha ?_ ?_ ?_
      · rintro j _ ⟨b, hb, rfl⟩
        refine ⟨(hA b hb).1.comp (hd j), fun u => ?_⟩
        have := hin j _ ((hA b hb).2 (d j u))
        simpa only [LinearMap.funLeft_apply, hdm] using this
      · exact ⟨continuous_zero, fun _ => zero_mem _⟩
      · exact fun a b ha hb => ⟨ha.1.add hb.1, fun u => add_mem (ha.2 u) (hb.2 u)⟩)
  refine ⟨E, hE, hR, fun f hf hD g k hk hrep => hP _ (hf.comp ((continuous_const.mul hι).mul continuous_const)) hrep fun m => ?_⟩
  obtain ⟨j, hj, hjk⟩ := Set.mem_iUnion₂.1 (ht hk)
  have hu : (j : G1 K n)⁻¹ * k ∈ D.U := (hmem _ (mul_mem (inv_mem j.2) hk)).2 hjk
  have h := hin ⟨j, hj⟩ _ ((hA _ (hfix f hf hD (g * ι m * j))).2 ⟨_, hu⟩)
  convert h using 3 with x
  change _ = g * ι m * j * (c j x * ((j : G1 K n)⁻¹ * k))
  rw [hc, map_mul]
  group

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secStr :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ →
      ∃ E₁ E₂ : Submodule ℂ (G1 K 2 → ℂ), FiniteDimensional ℂ E₁ ∧ FiniteDimensional ℂ E₂ ∧ (∀ φ ∈ E₁, Rd τ₁ φ) ∧ (∀ φ ∈ E₂, Rd τ₂ φ) ∧
        ∀ f : G1 K (2 + 2) → ℂ, Continuous f → D.Fix f → Slices τ₁ τ₂ f → ∀ k ∈ KG K (2 + 2),
          (∀ m₂, (fun m₁ => f (lv m₁ m₂ 0 * k)) ∈ E₁) ∧ ∀ m₁, (fun m₂ => f (lv m₁ m₂ 0 * k)) ∈ E₂ := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ D h₁ h₂
  obtain ⟨-, hmul, -, hcont, -, -, -, -, -, -, hK, hcpt⟩ := @blkLaws K _ _
  obtain ⟨ι₁, d₁⟩ : ∃ ι : G1 K 2 →* G1 K (2 + 2), ∀ m, ι m = lv m 1 0 :=
    ⟨MonoidHom.mk' (fun m => lv m 1 0) fun a b => by rw [hmul, mul_one, add_zero], fun _ => rfl⟩
  obtain ⟨ι₂, d₂⟩ : ∃ ι : G1 K 2 →* G1 K (2 + 2), ∀ m, ι m = lv 1 m 0 :=
    ⟨MonoidHom.mk' (fun m => lv 1 m 0) fun a b => by rw [hmul, mul_one, add_zero], fun _ => rfl⟩
  have c₁ : Continuous ι₁ := by
    have h : Continuous fun m : G1 K 2 => ((m, 1, 0) : G1 K 2 × G1 K 2 × ℝ) := continuous_id.prodMk continuous_const
    exact (hcont.comp' h).congr fun m => (d₁ m).symm
  have c₂ : Continuous ι₂ := by
    have h : Continuous fun m : G1 K 2 => ((1, m, 0) : G1 K 2 × G1 K 2 × ℝ) :=
      continuous_const.prodMk (continuous_id.prodMk continuous_const)
    exact (hcont.comp' h).congr fun m => (d₂ m).symm
  have e₁ : ∀ m₁ m₂, lv m₁ m₂ 0 = lv 1 m₂ 0 * ι₁ m₁ := fun m₁ m₂ => by
    rw [d₁, hmul, mul_one, one_mul, add_zero]
  have e₂ : ∀ m₁ m₂, lv m₁ m₂ 0 = lv m₁ 1 0 * ι₂ m₂ := fun m₁ m₂ => by
    rw [d₂, hmul, mul_one, one_mul, add_zero]
  obtain ⟨E₁, f₁, r₁, p₁⟩ := secStr_side μ₂ τ₁ D h₁ ι₁ c₁ (fun x hx => by rw [d₁]; exact hK x hx 1 (one_mem _)) (hcpt _).1
  obtain ⟨E₂, f₂, r₂, p₂⟩ := secStr_side μ₂ τ₂ D h₂ ι₂ c₂ (fun x hx => by rw [d₂]; exact hK 1 (one_mem _) x hx) (hcpt _).1
  refine ⟨E₁, E₂, f₁, f₂, r₁, r₂, fun f hf hD hS k hk => ⟨fun m₂ => ?_, fun m₁ => ?_⟩⟩
  · have h := (hS k).1 m₂
    have e : (fun m₁ => f (lv m₁ m₂ 0 * k)) = fun m₁ => f (lv 1 m₂ 0 * ι₁ m₁ * k) := funext fun m₁ => by rw [← e₁]
    rw [e] at h ⊢
    exact p₁ f hf hD _ k hk h
  · have h := (hS k).2 m₁
    have e : (fun m₂ => f (lv m₁ m₂ 0 * k)) = fun m₂ => f (lv m₁ 1 0 * ι₂ m₂ * k) := funext fun m₂ => by rw [← e₂]
    rw [e] at h ⊢
    exact p₂ f hf hD _ k hk h
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem reps_right {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (h : Reps μ v φ) (g : G1 K n) :
    Reps μ (rightRegularRep (Gam K n) μ g v) (fun y => φ (y * g)) := by
  have h1 := (quasiMeasurePreserving_mk (Gam K n) μ).ae (coeFn_rightRegularRep (Gam K n) μ g v)
  have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h
  filter_upwards [h1, h2] with y e1 e2
  rw [e1]
  exact e2

private theorem reps_sum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) {ι : Type} (s : Finset ι) (φ : ι → G1 K n → ℂ) (c : ι → ℂ)
    (h : ∀ i, ∃ v ∈ τ, Reps μ v (φ i)) : ∃ v ∈ τ, Reps μ v (fun y => ∑ i ∈ s, c i * φ i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, τ.zero_mem, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y e
    simpa using e
  | insert i s hi ih =>
    obtain ⟨v, hv, hr⟩ := ih
    obtain ⟨w, hw, hq⟩ := h i
    refine ⟨c i • w + v, τ.add_mem (τ.smul_mem _ hw) hv, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c i • w) v),
      (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c i) w), hr, hq] with y e1 e2 e3 e4
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, e4, Finset.sum_insert hi, smul_eq_mul]

private theorem zt_zero {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, this, map_one]

private theorem lv_zero {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) :
    ((lv m₁ m₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (m₁ : AdelicGLn.AdelicGL K 2) (m₂ : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt_zero, mul_one, mul_one]

private theorem lv_ray {K : Type} [Field K] [NumberField K] (r : {r : ℝ // 0 < r}) (t : ℝ) (h : r.1 = Real.exp t) :
    ((lv 1 1 t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (centralSection K 2 r) (centralSection K 2 r⁻¹) := by
  have h1 : (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r}) = r := Subtype.ext h.symm
  have h2 : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = r⁻¹ := by
    apply Subtype.ext
    change Real.exp (-t) = r.1⁻¹
    rw [h, Real.exp_neg]
  rw [blkLaws.1, zt, zt, h1, h2]
  simp

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secCrit :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ → ∀ f : G1 K (2 + 2) → ℂ, D.Fix f →
      (IsSec τ₁ τ₂ f ↔ Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ X g, f (nn X * g) = f g) ∧ (∀ t g, f (lv 1 1 t * g) = f g) ∧ Slices τ₁ τ₂ f) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ D h₁ h₂ f hf
  constructor
  · intro hs
    refine ⟨hs.cont, hs.bdd, hs.unip, fun t g => ?_, fun g => ?_⟩
    · refine hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
      rw [Subgroup.coe_mul, lv_ray ⟨Real.exp t, Real.exp_pos t⟩ t rfl]
    · obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hs.levi g
      have hx' : ∀ m₁ m₂, f (lv m₁ m₂ 0 * g) = ∑ i, φ i m₁ * ψ i m₂ := fun m₁ m₂ =>
        hx m₁ m₂ _ (by rw [Subgroup.coe_mul, lv_zero])
      refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
      · have := reps_sum μ₂ τ₁ Finset.univ φ (fun i => ψ i m₂) (fun i => (hφ i).2)
        simpa only [hx', mul_comm] using this
      · have := reps_sum μ₂ τ₂ Finset.univ ψ (fun i => φ i m₁) (fun i => (hψ i).2)
        simpa only [hx'] using this
  · rintro ⟨hc, hb, hu, hr, hsl⟩
    refine ⟨hc, hb, hu, fun r x g hx => ?_, fun g => ?_⟩
    · have : x = lv 1 1 (Real.log r.1) * g := by
        apply Subtype.ext
        rw [hx, Subgroup.coe_mul, lv_ray r _ (Real.exp_log r.2).symm]
      rw [this, hr]
    · obtain ⟨E₁, E₂, hE₁, hE₂, hR₁, hR₂, hE⟩ := secStr μ₂ τ₁ τ₂ D h₁ h₂
      obtain ⟨X, n₁, n₂, t, k, hk, rfl⟩ := iwa g
      obtain ⟨a, b, φ, ψ, x, y, s, u, hφ, hψ, hT⟩ := tens E₁ E₂
      obtain ⟨hk₁, hk₂⟩ := hE f hc hf hsl k hk
      have hT' := hT (fun m₁ m₂ => f (lv m₁ m₂ 0 * k)) hk₁ hk₂
      set c : Fin a → Fin b → ℂ := fun i j => ∑ p, ∑ q, s i p * u j q * f (lv (x i p) (y j q) 0 * k) with hcdef
      refine ⟨a * b, fun l m => c (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2 * φ (finProdFinEquiv.symm l).1 (m * n₁),
        fun l m => ψ (finProdFinEquiv.symm l).2 (m * n₂), fun l => ⟨?_, ?_⟩, fun l => ⟨?_, ?_⟩, fun m₁ m₂ z hz => ?_⟩
      · exact continuous_const.mul ((hR₁ _ (hφ _)).cont.comp (continuous_mul_const n₁))
      · obtain ⟨v, hv, hq⟩ := (hR₁ _ (hφ (finProdFinEquiv.symm l).1)).rep
        have := reps_sum μ₂ τ₁ (Finset.univ : Finset Unit) (fun _ m => φ (finProdFinEquiv.symm l).1 (m * n₁))
          (fun _ => c (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2)
          (fun _ => ⟨_, h₁.inv n₁ v hv, reps_right μ₂ hq n₁⟩)
        simpa only [Finset.univ_unique, Finset.sum_singleton] using this
      · exact (hR₂ _ (hψ _)).cont.comp (continuous_mul_const n₂)
      · obtain ⟨v, hv, hq⟩ := (hR₂ _ (hψ (finProdFinEquiv.symm l).2)).rep
        exact ⟨_, h₂.inv n₂ v hv, reps_right μ₂ hq n₂⟩
      · obtain ⟨e, he, -⟩ := adMeas m₁ m₂ 0
        have h1 : lv m₁ m₂ 0 * nn X = nn (e.symm X) * lv m₁ m₂ 0 := by
          rw [he, e.apply_symm_apply]
        have h2 : lv m₁ m₂ 0 * lv n₁ n₂ t = lv 1 1 t * lv (m₁ * n₁) (m₂ * n₂) 0 := by
          rw [blkLaws.2.1, blkLaws.2.1]; simp
        have hz' : z = nn (e.symm X) * (lv 1 1 t * (lv (m₁ * n₁) (m₂ * n₂) 0 * k)) := by
          have : z = lv m₁ m₂ 0 * (nn X * lv n₁ n₂ t * k) := by
            apply Subtype.ext
            rw [hz, Subgroup.coe_mul (x := lv m₁ m₂ 0), lv_zero]
          rw [this, ← mul_assoc, ← mul_assoc, h1, mul_assoc (nn _), h2]
          simp only [mul_assoc]
        rw [hz', hu, hr, hT', ← Fintype.sum_prod_type']
        exact (Equiv.sum_comp finProdFinEquiv.symm
          (fun p : Fin a × Fin b => c p.1 p.2 * φ p.1 (m₁ * n₁) * ψ p.2 (m₂ * n₂))).symm
end
