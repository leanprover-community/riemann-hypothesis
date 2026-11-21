import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt

section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem sz_fderiv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} {f : V → F} {x : V} {b : ℝ} (h : Sz (k + 1) f x b) : Sz k (fderiv ℝ f) x b :=
  fun i hi => by
    rw [norm_iteratedFDeriv_fderiv]
    exact h (i + 1) (Nat.succ_le_succ hi)

private theorem sum_deriv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {Y : Set V} (hY : IsOpen Y) {y : ℕ → V → F}
    (hy : ∀ j, ContDiffOn ℝ ∞ (y j) Y)
    (hb : ∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j))
    {p : V} (hp : p ∈ Y) :
    Summable (fun j => fderiv ℝ (y j) p) ∧
      HasFDerivAt (fun x => ∑' j, y j x) (∑' j, fderiv ℝ (y j) p) p := by
  obtain ⟨N, hN, b, hs, hle⟩ := hb 1 p hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hN (hY.mem_nhds hp))
  have hpN : p ∈ N := mem_of_mem_nhds hN
  have h1 : ∀ j, ∀ x ∈ N, ‖fderiv ℝ (y j) x‖ ≤ b j := fun j x hx => (sz_fderiv (k := 0) (hle j x hx)).norm_le
  refine ⟨Summable.of_norm_bounded hs fun j => h1 j p hpN, ?_⟩
  refine hasFDerivAt_tsum_of_isPreconnected (u := b) (s := Metric.ball p r) (f := y)
    (f' := fun j x => fderiv ℝ (y j) x) (x₀ := p) hs Metric.isOpen_ball (convex_ball p r).isPreconnected
    (fun j x hx => ?_) (fun j x hx => h1 j x (hball hx).1) (Metric.mem_ball_self hr) ?_ (Metric.mem_ball_self hr)
  · exact (((hy j).contDiffAt (hY.mem_nhds (hball hx).2)).differentiableAt (by simp)).hasFDerivAt
  · exact Summable.of_norm_bounded hs fun j => (hle j p hpN).norm_le

private theorem sum_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (y : ℕ → V → F),
    (∀ j, ContDiffOn ℝ ∞ (y j) Y) →
    (∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j)) →
    ContDiffOn ℝ n (fun x => ∑' j, y j x) Y := by
  induction n with
  | zero =>
    intro F _ _ _ y hy hb
    simp only [CharP.cast_eq_zero, Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (sum_deriv hY hy hb hp).2.continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ _ y hy hb
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hY]
    refine ⟨fun p hp => (sum_deriv hY hy hb hp).2.differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have h := ih (V →L[ℝ] F) (fun j => fderiv ℝ (y j))
      (fun j => (hy j).fderiv_of_isOpen hY (by simp)) (fun k p hp => by
        obtain ⟨N, hN, b, hs, hle⟩ := hb (k + 1) p hp
        exact ⟨N, hN, b, hs, fun j x hx => sz_fderiv (hle j x hx)⟩)
    exact h.congr fun p hp => (sum_deriv hY hy hb hp).2.fderiv

theorem UpperTheory.V.Lit.Geo.Cs.sumSm :
    SumSm := by
  intro V F _ _ _ _ _ Y hY y hy hb
  refine ⟨contDiffOn_infty.2 fun n => sum_smooth hY n F y hy hb, fun p hp => ?_⟩
  rw [(sum_deriv hY hy hb hp).2.fderiv]
  exact (sum_deriv hY hy hb hp).1.hasSum
end

section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.geoCut :
    GeoCut := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q η hη hinv
  classical
  set χ : ℝ → ℝ := fun t => Real.smoothTransition (2 * (t - R) - 1) with hχ
  have hχc : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sub contDiff_const)
  have hχ0 : ∀ t, t ≤ R + 1 / 2 → χ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hχ1 : ∀ t, R + 1 ≤ t → χ t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by linarith)
  let f : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun s p => if p ∈ G.Y ∧ R < Φ s p then χ (Φ s p) • η s p else 0
  have hf : f ∈ G.Om q := by
    show ∀ s, ContDiffOn ℝ ∞ (f s) G.Y ∧ ∀ p ∉ G.Y, f s p = 0
    refine fun s => ⟨?_, fun p hp => by simp [f, hp]⟩
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    by_cases hR : R < Φ s p
    · refine ⟨G.Y ∩ Φ s ⁻¹' Set.Ioi R, (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi,
        ⟨hp, hR⟩, ?_⟩
      have hsm : ContDiffOn ℝ ∞ (fun x => χ (Φ s x) • η s x) (G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) :=
        ((hχc.comp_contDiffOn (hΦ.1 s)).mono (fun x hx => hx.1)).smul
          ((hη s).mono (fun x hx => ⟨hx.2.1, hx.2.2⟩))
      refine hsm.congr (fun x hx => ?_)
      have hx' : x ∈ G.Y ∧ R < Φ s x := ⟨hx.2.1, hx.2.2⟩
      simp only [f, if_pos hx']
    · push_neg at hR
      refine ⟨G.Y ∩ Φ s ⁻¹' Set.Iio (R + 1 / 2),
        (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Iio,
        ⟨hp, show Φ s p < R + 1 / 2 by linarith⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)))).congr (fun x hx => ?_)
      have hx2 : Φ s x < R + 1 / 2 := hx.2.2
      simp only [f]
      split_ifs with h
      · rw [hχ0 _ hx2.le, zero_smul]
      · rfl
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro γ
    apply Subtype.ext
    funext s p
    show G.tr q γ (f (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) = f s p
    have hρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := by
      intro x
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    by_cases hp : p ∈ G.Y
    · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
      have hΦ' : Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = Φ s p := hΦ.2.1 γ⁻¹ s p hp
      by_cases hR : R < Φ s p
      · have h1 : G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := ⟨hp', by rw [hΦ']; exact hR⟩
        have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, hR⟩
        simp only [f, if_pos h1, if_pos h2]
        rw [hΦ', map_smul, hinv γ s p hp hR]
      · have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := by
          rw [hΦ']
          exact fun h => hR h.2
        have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hR h.2
        simp only [f, if_neg h1, if_neg h2, map_zero]
    · have hp' : G.ρ γ⁻¹ p ∉ G.Y := fun h => hp (by simpa [hρ] using G.maps γ _ h)
      have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := fun h => hp' h.1
      have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hp h.1
      simp only [f, if_neg h1, if_neg h2, map_zero]
  · intro s p hp h1
    have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, by linarith⟩
    show f s p = η s p
    simp only [f, if_pos h2, hχ1 _ h1, one_smul]
end

section
open UpperTheory.V.Lit.Geo.Cs
open scoped Topology ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.geoSum :
    GeoSum := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q y w hy hdy hsz hw
  have hopen : ∀ s, IsOpen {p | p ∈ G.Y ∧ R < Φ s p} := fun s =>
    (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi
  have hmem : ∀ j s, ContDiffOn ℝ ∞ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y :=
    fun j s => ((y j).2 s).1
  have hsm : ∀ s,
      ContDiffOn ℝ ∞ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
        {p | p ∈ G.Y ∧ R < Φ s p} ∧
      ∀ p ∈ {p | p ∈ G.Y ∧ R < Φ s p},
        HasSum (fun j => fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p)
          (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) :=
    fun s => sumSm V _ _ (hopen s) (fun j x => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
      (fun j => (hmem j s).mono (fun p hp => hp.1)) (fun k p hp => hsz k s p hp.1 hp.2)
  have hsumv : ∀ s, ∀ p ∈ G.Y, R < Φ s p →
      Summable (fun j => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) := by
    intro s p hp hR
    obtain ⟨N, hN, b, hb, hbd⟩ := hsz 0 s p hp hR
    refine Summable.of_norm_bounded hb (fun j => ?_)
    have h0 := hbd j p (mem_of_mem_nhds hN) 0 le_rfl
    simpa using h0
  obtain ⟨z, hzinv, hz⟩ := geoCut Γ V S d G Φ hΦ R q
    (fun s p => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p)
    (fun s => (hsm s).1.neg) (by
      intro γ s p hp hR
      have hp2 : (G.ρ γ⁻¹) p ∈ G.Y := G.maps _ p hp
      have hR2 : R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by rw [hΦ.2.1 γ⁻¹ s p hp]; exact hR
      simp only [map_neg]
      congr 1
      rw [ContinuousLinearMap.map_tsum _ (hsumv _ _ hp2 hR2)]
      congr 1
      funext j
      exact congrFun (congrFun (congrArg Subtype.val (hy j γ)) s) p)
  refine ⟨z, hzinv, fun s p hp hR => ?_⟩
  have hev : (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[𝓝 p]
      (fun x => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) := by
    have hc : ContinuousAt (Φ s) p := (hΦ.1 s).continuousOn.continuousAt (G.isOpen.mem_nhds hp)
    filter_upwards [G.isOpen.mem_nhds hp, Filter.Tendsto.eventually hc (lt_mem_nhds hR)]
      with x hx hx'
    exact hz s x hx hx'.le
  have hp' : p ∈ {p | p ∈ G.Y ∧ R < Φ s p} := ⟨hp, by linarith⟩
  have hD := ((hsm s).2 p hp').mapL (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  have hterm : ∀ j, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p) =
      (w (j + 1) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p -
        (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    intro j
    have h1 := congrFun (congrFun (congrArg Subtype.val (hdy j)) s) p
    rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    change _ = ((w (j + 1) - w j : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p
    rw [← h1]
    show _ = G.Y.indicator (extDeriv ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p
    rw [Set.indicator_of_mem hp]
    rfl
  have hL : ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) =
      -(w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    have ht := hD.tendsto_sum_nat
    simp_rw [hterm, Finset.sum_range_sub
      (fun j => (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)] at ht
    have ht2 := (hw s p hp (by linarith)).sub_const
      ((w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)
    rw [zero_sub] at ht2
    exact tendsto_nhds_unique ht ht2
  show G.Y.indicator (extDeriv ((z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p = _
  rw [Set.indicator_of_mem hp, hev.extDeriv_eq]
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ
    (-(fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)) p) = _
  rw [fderiv_neg, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_neg, hL, neg_neg]
end
