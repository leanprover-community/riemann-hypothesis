import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.NormNatCastLtOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
  Topology Filter
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Places

variable {F : Type} [Field F] [NumberField F]

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x
  have h2 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv
  have hv1 : v.valuation F x ≤ 1 := not_lt.1 hv.1
  have hv2 : v.valuation F x⁻¹ ≤ 1 := not_lt.1 hv.2
  have hpos : 0 < v.valuation F x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have hval : v.valuation F x = 1 := by
    rw [map_inv₀, inv_le_one₀ hpos] at hv2
    exact le_antisymm hv1 hv2
  have h := NumberField.FinitePlace.norm_def' (K := F) v x
  rw [hval] at h
  simp only [map_one, NNReal.coe_one] at h
  exact h


theorem exists_good_int (Δ : F) (hΔ : Δ ≠ 0) : ∃ N0 : ℕ, N0 ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    ‖(N0 : v.adicCompletion F)‖ = 1 →
      ‖(2 : v.adicCompletion F)‖ = 1 ∧ ‖algebraMap F (v.adicCompletion F) Δ‖ = 1 := by
  classical
  obtain ⟨S1, hS1⟩ := exists_finset_norm_one Δ hΔ
  obtain ⟨S2, hS2⟩ := exists_finset_norm_one (2 : F) two_ne_zero
  refine ⟨∏ w ∈ S1 ∪ S2, Ideal.absNorm w.asIdeal, ?_, fun v hv => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun w _ h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  · by_cases hvS : v ∈ S1 ∪ S2
    · exfalso
      have hmem : ((∏ w ∈ S1 ∪ S2, Ideal.absNorm w.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := by
        rw [Finset.prod_eq_mul_prod_diff_singleton v _ (fun h => absurd hvS h), Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)
      have hlt := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 hmem
      rw [map_natCast, map_natCast] at hlt
      linarith
    · simp only [Finset.mem_union, not_or] at hvS
      refine ⟨?_, hS1 v hvS.1⟩
      have h2 := hS2 v hvS.2
      rwa [map_ofNat] at h2

theorem con_inf (Δ : F) (a b : AF F) (h : a * a - algebraMap F (AF F) Δ * (b * b) = 1) (w : InfinitePlace F) :
    a.1 w * a.1 w - algebraMap F w.Completion Δ * (b.1 w * b.1 w) = 1 :=
  congrArg (fun z : AF F => z.1 w) h

theorem con_fin (Δ : F) (a b : AF F) (h : a * a - algebraMap F (AF F) Δ * (b * b) = 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    a.2 v * a.2 v - algebraMap F (v.adicCompletion F) Δ * (b.2 v * b.2 v) = 1 :=
  congrArg (fun z : AF F => z.2 v) h

theorem cayley_one {K : Type*} [Field K] (Δ p r : K) (h : nrm Δ p r ≠ 0) :
    (p * p + Δ * (r * r)) / nrm Δ p r * ((p * p + Δ * (r * r)) / nrm Δ p r) -
      Δ * ((2 * p * r) / nrm Δ p r * ((2 * p * r) / nrm Δ p r)) = 1 := by
  have hn : p * p - Δ * (r * r) ≠ 0 := by simpa [nrm] using h
  simp only [nrm]
  rw [div_mul_div_comm, div_mul_div_comm, mul_div_assoc', div_sub_div_same,
    div_eq_one_iff_eq (mul_ne_zero hn hn)]
  ring

theorem cAq_eq {K : Type*} [Field K] (φ : F →+* K) (Δ p r : F) (a b : K) :
    a * φ ((p * p + Δ * (r * r)) / nrm Δ p r) + φ Δ * (b * -φ ((2 * p * r) / nrm Δ p r)) =
      cAq (φ Δ) a b (φ p) (φ r) := by
  simp only [cAq, nrm, map_div₀, map_add, map_mul, map_sub, map_neg, map_ofNat]
  ring

theorem cBq_eq {K : Type*} [Field K] (φ : F →+* K) (Δ p r : F) (a b : K) :
    a * -φ ((2 * p * r) / nrm Δ p r) + b * φ ((p * p + Δ * (r * r)) / nrm Δ p r) =
      cBq (φ Δ) a b (φ p) (φ r) := by
  simp only [cBq, nrm, map_div₀, map_add, map_mul, map_sub, map_neg, map_ofNat]
  ring

theorem compA_inf (Δ P R : F) (a b : AF F) (w : InfinitePlace F) :
    (a * algebraMap F (AF F) P + algebraMap F (AF F) Δ * (b * -algebraMap F (AF F) R)).1 w =
      a.1 w * algebraMap F w.Completion P + algebraMap F w.Completion Δ * (b.1 w * -algebraMap F w.Completion R) := rfl

theorem compB_inf (P R : F) (a b : AF F) (w : InfinitePlace F) :
    (a * -algebraMap F (AF F) R + b * algebraMap F (AF F) P).1 w =
      a.1 w * -algebraMap F w.Completion R + b.1 w * algebraMap F w.Completion P := rfl

theorem compA_fin (Δ P R : F) (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * algebraMap F (AF F) P + algebraMap F (AF F) Δ * (b * -algebraMap F (AF F) R)).2 v =
      a.2 v * algebraMap F (v.adicCompletion F) P +
        algebraMap F (v.adicCompletion F) Δ * (b.2 v * -algebraMap F (v.adicCompletion F) R) := rfl

theorem compB_fin (P R : F) (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * -algebraMap F (AF F) R + b * algebraMap F (AF F) P).2 v =
      a.2 v * -algebraMap F (v.adicCompletion F) R + b.2 v * algebraMap F (v.adicCompletion F) P := rfl

theorem alg_con (Δ P R : F) (h : P * P - Δ * (R * R) = 1) :
    algebraMap F (AF F) P * algebraMap F (AF F) P -
      algebraMap F (AF F) Δ * (-algebraMap F (AF F) R * -algebraMap F (AF F) R) = 1 := by
  rw [neg_mul_neg, ← map_mul, ← map_mul, ← map_mul, ← map_sub, h, map_one]

theorem approx_point (Δ : F) (hΔ : Δ ≠ 0) (a b : AF F) (hab : a * a - algebraMap F (AF F) Δ * (b * b) = 1)
    (ε : InfinitePlace F → ℝ) (hε : ∀ w, 0 < ε w) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ρ : HeightOneSpectrum (𝓞 F) → ℝ) (hρ : ∀ v, 0 < ρ v) :
    ∃ P R : F, P * P - Δ * (R * R) = 1 ∧
      (∀ w, ‖(a * algebraMap F (AF F) P + algebraMap F (AF F) Δ * (b * -algebraMap F (AF F) R)).1 w - 1‖ < ε w ∧
        ‖(a * -algebraMap F (AF F) R + b * algebraMap F (AF F) P).1 w‖ < ε w) ∧
      (∀ v ∈ S, ‖(a * algebraMap F (AF F) P + algebraMap F (AF F) Δ * (b * -algebraMap F (AF F) R)).2 v - 1‖ < ρ v ∧
        ‖(a * -algebraMap F (AF F) R + b * algebraMap F (AF F) P).2 v‖ < ρ v) := by
  have two_w : ∀ w : InfinitePlace F, (2 : w.Completion) ≠ 0 := fun w => by
    have := (algebraMap F w.Completion).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  have two_v : ∀ v : HeightOneSpectrum (𝓞 F), (2 : v.adicCompletion F) ≠ 0 := fun v => by
    have := (algebraMap F (v.adicCompletion F)).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  have hlocI : ∀ w : InfinitePlace F, ∃ p0 r0 : w.Completion, ∃ η > 0, ∀ p r : w.Completion,
      ‖p - p0‖ < η → ‖r - r0‖ < η →
        nrm (algebraMap F w.Completion Δ) p r ≠ 0 ∧
        ‖cAq (algebraMap F w.Completion Δ) (a.1 w) (b.1 w) p r - 1‖ < ε w ∧
        ‖cBq (algebraMap F w.Completion Δ) (a.1 w) (b.1 w) p r‖ < ε w := fun w =>
    loc_near (algebraMap F w.Completion Δ) (a.1 w) (b.1 w) (two_w w) ((map_ne_zero _).2 hΔ)
      (con_inf Δ a b hab w) (ε w) (hε w)
  choose pI rI ηI hηI hI using hlocI
  have hlocF : ∀ v : HeightOneSpectrum (𝓞 F), ∃ p0 r0 : v.adicCompletion F, ∃ η > 0,
      ∀ p r : v.adicCompletion F, ‖p - p0‖ < η → ‖r - r0‖ < η →
        nrm (algebraMap F (v.adicCompletion F) Δ) p r ≠ 0 ∧
        ‖cAq (algebraMap F (v.adicCompletion F) Δ) (a.2 v) (b.2 v) p r - 1‖ < ρ v ∧
        ‖cBq (algebraMap F (v.adicCompletion F) Δ) (a.2 v) (b.2 v) p r‖ < ρ v := fun v =>
    loc_near (algebraMap F (v.adicCompletion F) Δ) (a.2 v) (b.2 v) (two_v v) ((map_ne_zero _).2 hΔ)
      (con_fin Δ a b hab v) (ρ v) (hρ v)
  choose pF rF ηF hηF hF using hlocF
  obtain ⟨p, hpI, hpF⟩ := weakApprox S pI pF ηI hηI ηF hηF
  obtain ⟨r, hrI, hrF⟩ := weakApprox S rI rF ηI hηI ηF hηF
  have hN' : nrm Δ p r ≠ 0 := by
    intro h0
    obtain w0 := Classical.arbitrary (InfinitePlace F)
    have h1 := (hI w0 _ _ (hpI w0) (hrI w0)).1
    have e : nrm (algebraMap F w0.Completion Δ) (algebraMap F w0.Completion p) (algebraMap F w0.Completion r) =
        algebraMap F w0.Completion (nrm Δ p r) := by
      simp only [nrm, map_sub, map_mul]
    rw [e, h0, map_zero] at h1
    exact h1 rfl
  refine ⟨(p * p + Δ * (r * r)) / nrm Δ p r, (2 * p * r) / nrm Δ p r, cayley_one Δ p r hN', fun w => ?_,
    fun v hv => ?_⟩
  · rw [compA_inf, compB_inf, cAq_eq (algebraMap F w.Completion) Δ p r, cBq_eq (algebraMap F w.Completion) Δ p r]
    obtain ⟨-, h2, h3⟩ := hI w _ _ (hpI w) (hrI w)
    exact ⟨h2, h3⟩
  · rw [compA_fin, compB_fin, cAq_eq (algebraMap F (v.adicCompletion F)) Δ p r,
      cBq_eq (algebraMap F (v.adicCompletion F)) Δ p r]
    obtain ⟨-, h2, h3⟩ := hF v _ _ (hpF v hv) (hrF v hv)
    exact ⟨h2, h3⟩

end Places

section Main

variable {D : D7} (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

include hδ0 in

theorem pos_of_near (lam : FirstPropositionFrame D →* Circle)
    (hsplit : ∀ e, IsSplitIdem D e → ∀ x : FirstPropositionFrame D, SuppAtU D e (x : (AE D)ˣ) → lam x = 1)
    (W : Set (AF D.host.F × AF D.host.F))
    (hW : ∀ (a b : AF D.host.F) (h : a * a - DA Δ * (b * b) = 1), (a, b) ∈ W →
      0 < ((lam (mkU δ hδ Δ hΔ h) : Circle) : ℂ).re)
    (ε : InfinitePlace D.host.F → ℝ) (N1 N : ℕ)
    (hbasic : ∀ a b : AF D.host.F, (∀ w, ‖a.1 w - 1‖ < ε w ∧ ‖b.1 w‖ < ε w) →
      (∀ v, ‖a.2 v - 1‖ ≤ ‖(N1 : v.adicCompletion D.host.F)‖ ∧ ‖b.2 v‖ ≤ ‖(N1 : v.adicCompletion D.host.F)‖) →
        (a, b) ∈ W)
    (hNle : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      ‖(N : v.adicCompletion D.host.F)‖ ≤ ‖(N1 : v.adicCompletion D.host.F)‖)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS1 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∉ S → ‖(N1 : v.adicCompletion D.host.F)‖ = 1)
    (hSgood : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∉ S → ‖(2 : v.adicCompletion D.host.F)‖ = 1 ∧
      ‖algebraMap D.host.F (v.adicCompletion D.host.F) Δ‖ = 1)
    (A B : AF D.host.F) (hAB : A * A - DA Δ * (B * B) = 1)
    (hinf : ∀ w, ‖A.1 w - 1‖ < ε w ∧ ‖B.1 w‖ < ε w)
    (hfin : ∀ v ∈ S, ‖A.2 v - 1‖ < ‖(N : v.adicCompletion D.host.F)‖ ∧
      ‖B.2 v‖ < ‖(N : v.adicCompletion D.host.F)‖) :
    0 < ((lam (mkU δ hδ Δ hΔ hAB) : Circle) : ℂ).re := by
  classical
  have hfinA := Filter.eventually_cofinite.mp A.2.2
  have hfinB := Filter.eventually_cofinite.mp B.2.2
  obtain ⟨A', B', hAB', hlam', h1A, h1B, hSAB, hint⟩ :=
    removal δ hδ hδ0 Δ hΔ lam hsplit S hSgood (hfinA.union hfinB).toFinset A B hAB (by
      intro v _ hbad
      rw [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
      by_cases h1 : ‖A.2 v‖ ≤ 1
      · right; intro h2; exact hbad ⟨h1, (norm_le_one_iff_int v _).2 h2⟩
      · left; intro h2; exact h1 ((norm_le_one_iff_int v _).2 h2))
  have hin : (A', B') ∈ W := by
    refine hbasic A' B' (fun w => ?_) (fun v => ?_)
    · rw [h1A, h1B]; exact hinf w
    · by_cases hv : v ∈ S
      · obtain ⟨e1, e2⟩ := hSAB v hv
        rw [e1, e2]
        obtain ⟨h2, h3⟩ := hfin v hv
        exact ⟨(h2.le.trans (hNle v)), (h3.le.trans (hNle v))⟩
      · rw [hS1 v hv]
        obtain ⟨i1, i2⟩ := hint v hv
        refine ⟨?_, i2⟩
        rw [sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
        rw [norm_neg, norm_one]
        exact max_le i1 le_rfl
  have := hW A' B' hAB' hin
  rwa [hlam'] at this

include hδ0 in

theorem pos_of_alt (lam : FirstPropositionFrame D →* Circle)
    (hrat : ∀ (x : FirstPropositionFrame D) (q : D.host.E), ((x : (AE D)ˣ) : AE D) = incA D q → lam x = 1)
    (hsplit : ∀ e, IsSplitIdem D e → ∀ x : FirstPropositionFrame D, SuppAtU D e (x : (AE D)ˣ) → lam x = 1)
    (W : Set (AF D.host.F × AF D.host.F))
    (hW : ∀ (a b : AF D.host.F) (h : a * a - DA Δ * (b * b) = 1), (a, b) ∈ W →
      0 < ((lam (mkU δ hδ Δ hΔ h) : Circle) : ℂ).re)
    (ε : InfinitePlace D.host.F → ℝ) (hε : ∀ w, 0 < ε w) (N1 N : ℕ) (hN : N ≠ 0)
    (hbasic : ∀ a b : AF D.host.F, (∀ w, ‖a.1 w - 1‖ < ε w ∧ ‖b.1 w‖ < ε w) →
      (∀ v, ‖a.2 v - 1‖ ≤ ‖(N1 : v.adicCompletion D.host.F)‖ ∧ ‖b.2 v‖ ≤ ‖(N1 : v.adicCompletion D.host.F)‖) →
        (a, b) ∈ W)
    (hNle : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      ‖(N : v.adicCompletion D.host.F)‖ ≤ ‖(N1 : v.adicCompletion D.host.F)‖)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS1 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∉ S → ‖(N1 : v.adicCompletion D.host.F)‖ = 1)
    (hSgood : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∉ S → ‖(2 : v.adicCompletion D.host.F)‖ = 1 ∧
      ‖algebraMap D.host.F (v.adicCompletion D.host.F) Δ‖ = 1)
    (hΔ0 : Δ ≠ 0) (x : FirstPropositionFrame D) : 0 < ((lam x : Circle) : ℂ).re := by
  obtain ⟨a, ha⟩ : ∃ a, a = coA δ hδ hδ0 ((x : (AE D)ˣ) : AE D) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = coB δ hδ hδ0 ((x : (AE D)ˣ) : AE D) := ⟨_, rfl⟩
  have hab : a * a - DA Δ * (b * b) = 1 := by rw [ha, hb]; exact con_of_U1A δ hδ hδ0 Δ hΔ x
  have hxv : ((x : (AE D)ˣ) : AE D) = pt δ a b := by rw [ha, hb]; exact (pt_co δ hδ hδ0 _).symm
  obtain ⟨P, R, hPR, hinf, hfin⟩ := approx_point Δ hΔ0 a b hab ε hε S
    (fun v => ‖(N : v.adicCompletion D.host.F)‖) (fun v => norm_pos_iff.2 (nat_ne_zero_fin v hN))
  have hPRa : algebraMap D.host.F (AF D.host.F) P * algebraMap D.host.F (AF D.host.F) P -
      DA Δ * (-algebraMap D.host.F (AF D.host.F) R * -algebraMap D.host.F (AF D.host.F) R) = 1 :=
    alg_con Δ P R hPR
  have hq : lam (mkU δ hδ Δ hΔ hPRa) = 1 := by
    refine hrat _ (algebraMap D.host.F D.host.E P + algebraMap D.host.F D.host.E (-R) * δ) ?_
    rw [mkU_val, incA_eq_pt, map_neg]
  have hAB : (a * algebraMap D.host.F (AF D.host.F) P + DA Δ * (b * -algebraMap D.host.F (AF D.host.F) R)) *
      (a * algebraMap D.host.F (AF D.host.F) P + DA Δ * (b * -algebraMap D.host.F (AF D.host.F) R)) -
      DA Δ * ((a * -algebraMap D.host.F (AF D.host.F) R + b * algebraMap D.host.F (AF D.host.F) P) *
        (a * -algebraMap D.host.F (AF D.host.F) R + b * algebraMap D.host.F (AF D.host.F) P)) = 1 := by
    linear_combination (algebraMap D.host.F (AF D.host.F) P * algebraMap D.host.F (AF D.host.F) P -
      DA Δ * (algebraMap D.host.F (AF D.host.F) R * algebraMap D.host.F (AF D.host.F) R)) * hab + hPRa
  have hy : mkU δ hδ Δ hΔ hAB = x * mkU δ hδ Δ hΔ hPRa := by
    apply Subtype.ext; apply Units.ext
    show pt δ _ _ = ((x : (AE D)ˣ) : AE D) * pt δ (algebraMap D.host.F (AF D.host.F) P)
      (-algebraMap D.host.F (AF D.host.F) R)
    rw [hxv, pt_mul δ Δ hΔ]
  have hlamy : lam (mkU δ hδ Δ hΔ hAB) = lam x := by rw [hy, map_mul, hq, mul_one]
  rw [← hlamy]
  exact pos_of_near δ hδ hδ0 Δ hΔ lam hsplit W hW ε N1 N hbasic hNle S hS1 hSgood _ _ hAB hinf hfin

end Main

variable {D : D7}


end Formalism.IndefR.Fin.U1

namespace Formalism.IndefR.Fin


end Formalism.IndefR.Fin

end
