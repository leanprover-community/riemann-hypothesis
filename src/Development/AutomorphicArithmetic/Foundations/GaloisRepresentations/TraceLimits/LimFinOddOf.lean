import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LimWUOfSeeds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosedAtL

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

open Filter Topology

namespace UpperTheory.Gal.Lim

theorem exists_trace_limit : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (a : ℕ) (J I : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → ∀ (ρ : I → (Γ →* GL (Fin a) (PadicAlgCl l))) (η : I → J → PadicAlgCl l) (D : I → Set J), (∀ i, Continuous (ρ i)) → (∀ i, ∀ j ∈ D i, η i j = trc (ρ i) (x j)) → (∀ s : Finset I, Dense (x '' ⋂ i ∈ s, D i)) → PolyApprox θ (Set.range η) → ∃ t : Γ → PadicAlgCl l, (∀ g, t g ∈ L) ∧ (∀ (F : Finset I) (c : I → PadicAlgCl l) (ε : ℝ), (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) → ∀ g, ‖t g - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ ε) ∧ ∀ A : Set I, PolyApprox θ (η '' A) → PolyApprox t ((fun i => trc (ρ i)) '' A) ∧ ∀ j, (∀ i ∈ A, j ∈ D i) → t (x j) = θ j := by
  classical
  intro l _ Γ _ _ _ a J I x θ L hL hθL ρ η D hρ hη hD hθ
  have hcont : ∀ i, Continuous (trc (ρ i)) := fun i =>
    (Units.continuous_val.comp (hρ i)).matrix_trace
  have hLc : IsComplete (L : Set (PadicAlgCl l)) := by
    haveI : FiniteDimensional ℚ_[l] L.toSubalgebra.toSubmodule := hL
    exact Submodule.complete_of_finiteDimensional L.toSubalgebra.toSubmodule
  have conv : ∀ A : Set I, PolyApprox θ (η '' A) → ∀ ε > 0, ∃ F : Finset I, (↑F ⊆ A) ∧
      ∃ c : I → PadicAlgCl l, ∀ P : MvPolynomial J ℤ,
        ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε := by
    intro A hA ε hε
    obtain ⟨s, c, hs, hc⟩ := hA ε hε
    rcases s.eq_empty_or_nonempty with rfl | ⟨f0, hf0⟩
    · exact ⟨∅, by simp, fun _ => 0, fun P => le_of_eq_of_le (by simp only [Finset.sum_empty]; rfl) (hc P)⟩
    haveI : Nonempty I := ⟨(hs hf0).choose⟩
    have hex : ∀ f ∈ s, ∃ i, i ∈ A ∧ η i = f := fun f hf => hs hf
    choose! k hkA hk using hex
    refine ⟨s.image k, ?_, fun i => c (η i), fun P => ?_⟩
    · intro i hi
      rw [Finset.coe_image] at hi
      obtain ⟨f, hf, rfl⟩ := hi
      exact hkA f hf
    · rw [Finset.sum_image (fun f hf f' hf' e => by rw [← hk f hf, ← hk f' hf', e])]
      have e2 : ∑ f ∈ s, c (η (k f)) * MvPolynomial.aeval (η (k f)) P
          = ∑ f ∈ s, c f * MvPolynomial.aeval f P :=
        Finset.sum_congr rfl fun f hf => by rw [hk f hf]
      rw [e2]
      exact hc P
  set B : Filter J := ⨅ i, Filter.principal (D i) with hBdef
  have hDF : ∀ F : Finset I, (⋂ i ∈ F, D i) ∈ B := fun F =>
    (Filter.biInter_finset_mem F).2 fun i _ => Filter.mem_iInf_of_mem i (Filter.mem_principal_self _)
  have hne : ∀ g : Γ, (Filter.comap x (𝓝 g) ⊓ B).NeBot := by
    intro g
    refine (((nhds_basis_opens g).comap x).inf (Filter.hasBasis_iInf_principal_finite D)).neBot_iff.2 ?_
    rintro ⟨U, T⟩ ⟨⟨hgU, hU⟩, hT⟩
    obtain ⟨y, hyU, j, hj, rfl⟩ := (hD hT.toFinset).inter_open_nonempty U hU ⟨g, hgU⟩
    exact ⟨j, hyU, by simpa using hj⟩
  have hbd : ∀ g (F : Finset I) (c : I → PadicAlgCl l) (ε : ℝ),
      (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) →
      ∀ r > 0, ∀ᶠ j in Filter.comap x (𝓝 g) ⊓ B, ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ ε + r := by
    intro g F c ε hc r hr
    have hTc : Continuous fun y => ∑ i ∈ F, c i * trc (ρ i) y :=
      continuous_finset_sum _ fun i _ => continuous_const.mul (hcont i)
    have hU : {y | ‖(∑ i ∈ F, c i * trc (ρ i) y) - ∑ i ∈ F, c i * trc (ρ i) g‖ < r} ∈ 𝓝 g :=
      (isOpen_lt (continuous_norm.comp (hTc.sub continuous_const)) continuous_const).mem_nhds (by simpa using hr)
    filter_upwards [Filter.mem_inf_of_left (Filter.preimage_mem_comap hU), Filter.mem_inf_of_right (hDF F)] with j hj1 hj2
    have hj2' : ∀ i ∈ F, j ∈ D i := by simpa using hj2
    have e1 : ∑ i ∈ F, c i * trc (ρ i) (x j)
        = ∑ i ∈ F, c i * MvPolynomial.aeval (η i) (MvPolynomial.X j : MvPolynomial J ℤ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [MvPolynomial.aeval_X, hη i j (hj2' i hi)]
    have h1 := hc (MvPolynomial.X j)
    rw [MvPolynomial.aeval_X, ← e1] at h1
    have h2 : ‖(∑ i ∈ F, c i * trc (ρ i) (x j)) - ∑ i ∈ F, c i * trc (ρ i) g‖ < r := hj1
    calc ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖
        = ‖(θ j - ∑ i ∈ F, c i * trc (ρ i) (x j)) + ((∑ i ∈ F, c i * trc (ρ i) (x j)) - ∑ i ∈ F, c i * trc (ρ i) g)‖ := by
          congr 1; abel
      _ ≤ ε + r := (norm_add_le _ _).trans (add_le_add h1 h2.le)
  have hlim : ∀ g : Γ, ∃ v ∈ L, Filter.Tendsto θ (Filter.comap x (𝓝 g) ⊓ B) (𝓝 v) := by
    intro g
    haveI := hne g
    have hcau : Cauchy (Filter.map θ (Filter.comap x (𝓝 g) ⊓ B)) := by
      refine Metric.cauchy_iff.2 ⟨inferInstance, fun e he => ?_⟩
      obtain ⟨F, -, c, hc⟩ := conv Set.univ (by rw [Set.image_univ]; exact hθ) (e / 5) (by positivity)
      refine ⟨θ '' {j | ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ e / 5 + e / 5},
        Filter.image_mem_map (hbd g F c _ hc _ (by positivity)), ?_⟩
      rintro _ ⟨j, hj, rfl⟩ _ ⟨j', hj', rfl⟩
      simp only [Set.mem_setOf_eq] at hj hj'
      rw [dist_eq_norm]
      calc ‖θ j - θ j'‖ = ‖(θ j - ∑ i ∈ F, c i * trc (ρ i) g) - (θ j' - ∑ i ∈ F, c i * trc (ρ i) g)‖ := by
            congr 1; abel
        _ ≤ ‖θ j - ∑ i ∈ F, c i * trc (ρ i) g‖ + ‖θ j' - ∑ i ∈ F, c i * trc (ρ i) g‖ := norm_sub_le _ _
        _ < e := by linarith
    obtain ⟨v, hv, hlimv⟩ := hLc _ hcau
      (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' fun j => hθL j)))
    exact ⟨v, hv, hlimv⟩
  choose t htL htlim using hlim
  have hev : ∀ Q : MvPolynomial Γ ℤ, Continuous fun u : Γ → PadicAlgCl l => MvPolynomial.aeval u Q := by
    intro Q
    simp_rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    exact MvPolynomial.continuous_eval _
  have core : ∀ (F : Finset I) (c : I → PadicAlgCl l) (ε : ℝ),
      (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) →
      ∀ Q : MvPolynomial Γ ℤ, ‖MvPolynomial.aeval t Q - ∑ i ∈ F, c i * MvPolynomial.aeval (trc (ρ i)) Q‖ ≤ ε := by
    intro F c ε hc Q
    let Ψ : (Γ → Γ × PadicAlgCl l) → PadicAlgCl l := fun w =>
      MvPolynomial.aeval (fun g => (w g).2) Q - ∑ i ∈ F, c i * MvPolynomial.aeval (fun g => trc (ρ i) (w g).1) Q
    have hΨc : Continuous Ψ :=
      ((hev Q).comp (continuous_pi fun g => continuous_snd.comp (continuous_apply g))).sub
        (continuous_finset_sum _ fun i _ => continuous_const.mul
          ((hev Q).comp (continuous_pi fun g => (hcont i).comp (continuous_fst.comp (continuous_apply g)))))
    let Z : Set (Γ × PadicAlgCl l) := (fun j => (x j, θ j)) '' ⋂ i ∈ F, D i
    have hmem : (fun g => (g, t g)) ∈ closure (Set.univ.pi fun _ : Γ => Z) := by
      rw [closure_pi_set]
      intro g _
      haveI := hne g
      refine mem_closure_of_tendsto ((Filter.tendsto_comap.mono_left inf_le_left).prodMk_nhds (htlim g)) ?_
      filter_upwards [Filter.mem_inf_of_right (hDF F)] with j hj
      exact ⟨j, hj, rfl⟩
    have hsub : closure (Set.univ.pi fun _ : Γ => Z) ⊆ {w | ‖Ψ w‖ ≤ ε} := by
      refine closure_minimal ?_ (isClosed_le (continuous_norm.comp hΨc) continuous_const)
      intro w hw
      have hw' : ∀ g, ∃ j, j ∈ ⋂ i ∈ F, D i ∧ (x j, θ j) = w g := fun g => hw g (Set.mem_univ g)
      choose σ hσD hσ using hw'
      have hwσ : w = fun g => (x (σ g), θ (σ g)) := funext fun g => (hσ g).symm
      subst hwσ
      have hσD' : ∀ g, ∀ i ∈ F, σ g ∈ D i := fun g => by simpa using hσD g
      show ‖MvPolynomial.aeval (fun g => θ (σ g)) Q
        - ∑ i ∈ F, c i * MvPolynomial.aeval (fun g => trc (ρ i) (x (σ g))) Q‖ ≤ ε
      have e0 : MvPolynomial.aeval (fun g => θ (σ g)) Q = MvPolynomial.aeval θ (MvPolynomial.rename σ Q) := by
        rw [MvPolynomial.aeval_rename]; rfl
      have e2 : ∑ i ∈ F, c i * MvPolynomial.aeval (fun g => trc (ρ i) (x (σ g))) Q
          = ∑ i ∈ F, c i * MvPolynomial.aeval (η i) (MvPolynomial.rename σ Q) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [MvPolynomial.aeval_rename,
          show (fun g => trc (ρ i) (x (σ g))) = η i ∘ σ from
            funext fun g => (hη i (σ g) (hσD' g i hi)).symm]
      rw [e0, e2]
      exact hc _
    have h := hsub hmem
    simp only [Set.mem_setOf_eq, Ψ] at h
    exact h
  refine ⟨t, htL, fun F c ε hc g => ?_, fun A hA => ⟨?_, ?_⟩⟩
  · have := core F c ε hc (MvPolynomial.X g)
    simpa [MvPolynomial.aeval_X] using this
  · intro ε hε
    obtain ⟨F, hFA, c, hc⟩ := conv A hA ε hε
    refine ⟨F.image (fun i => trc (ρ i)), fun f => ∑ i ∈ F.filter (fun i => trc (ρ i) = f), c i, ?_, fun Q => ?_⟩
    · rw [Finset.coe_image]; exact Set.image_mono hFA
    · have e : ∑ f ∈ F.image (fun i => trc (ρ i)),
          (∑ i ∈ F.filter (fun i => trc (ρ i) = f), c i) * MvPolynomial.aeval f Q
          = ∑ i ∈ F, c i * MvPolynomial.aeval (trc (ρ i)) Q := by
        calc _ = ∑ f ∈ F.image (fun i => trc (ρ i)), ∑ i ∈ F.filter (fun i => trc (ρ i) = f),
                c i * MvPolynomial.aeval (trc (ρ i)) Q := by
              refine Finset.sum_congr rfl fun f _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [(Finset.mem_filter.1 hi).2]
          _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _
      exact le_of_eq_of_le (congrArg (fun z => ‖MvPolynomial.aeval t Q - z‖) e) (core F c ε hc Q)
  · intro j hj
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨F, hFA, c, hc⟩ := conv A hA (ε / 2) (by positivity)
    have h1 := core F c _ hc (MvPolynomial.X (x j))
    have h2 := hc (MvPolynomial.X j)
    simp only [MvPolynomial.aeval_X] at h1 h2
    have e : ∑ i ∈ F, c i * trc (ρ i) (x j) = ∑ i ∈ F, c i * η i j :=
      Finset.sum_congr rfl fun i hi => by rw [hη i j (hj i (hFA (Finset.mem_coe.2 hi)))]
    rw [e] at h1
    rw [dist_eq_norm]
    calc ‖t (x j) - θ j‖ = ‖(t (x j) - ∑ i ∈ F, c i * η i j) - (θ j - ∑ i ∈ F, c i * η i j)‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _
      _ ≤ ε := by linarith

end UpperTheory.Gal.Lim
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL
open Polynomial

namespace UpperTheory.Gal.Lim

theorem approx_index {k J I : Type} [NormedField k] [IsUltrametricDist k] {θ : J → k} {η : I → J → k} {A : Set I}
    (h : PolyApprox θ (η '' A)) {ε : ℝ} (hε : 0 < ε) : ∃ (F : Finset I) (c : I → k), (↑F : Set I) ⊆ A ∧
      ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε := by
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  choose ι hιA hιη using fun e : s => hs e.2
  have inj : Function.Injective ι := fun e₁ e₂ h => Subtype.ext (by rw [← hιη e₁, ← hιη e₂, h])
  refine ⟨Finset.univ.image ι, fun i => c (η i), ?_, fun P => ?_⟩
  · intro i hi
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
    exact hιA e
  rw [Finset.sum_image inj.injOn]
  simp only [hιη]
  rw [Finset.sum_coe_sort s fun e => c e * MvPolynomial.aeval e P]
  exact hP P

theorem approx_left {k J J' I : Type} [NormedField k] [IsUltrametricDist k] {θ : J → k} {θ' : J' → k} {η : I → J → k}
    {η' : I → J' → k} {A : Set I} (h : PolyApprox (Sum.elim θ θ') ((fun i => Sum.elim (η i) (η' i)) '' A)) :
    PolyApprox θ (η '' A) := by
  classical
  intro ε hε
  obtain ⟨F, c, hF, hP⟩ := approx_index h hε
  refine ⟨F.image η, fun e => ∑ i ∈ F.filter (fun i => η i = e), c i, ?_, fun P => ?_⟩
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
    exact ⟨i, hF hi, rfl⟩
  have hsum : ∑ e ∈ F.image η, (∑ i ∈ F.filter (fun i => η i = e), c i) * MvPolynomial.aeval e P =
      ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := η) (t := F.image η) (fun i hi => Finset.mem_image_of_mem _ hi)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  have h0 := hP (MvPolynomial.rename Sum.inl P)
  simp only [MvPolynomial.aeval_rename, Sum.elim_comp_inl] at h0
  exact le_of_eq_of_le (congrArg (fun z => ‖MvPolynomial.aeval θ P - z‖) hsum) h0

theorem joint {k Γ J J' I : Type} [NormedField k] [IsUltrametricDist k] [Group Γ] {a : ℕ} {r : Γ →* GL (Fin a) k}
    {ρ : I → Γ →* GL (Fin a) k} {θ : J → k} {θ' : J' → k} {η : I → J → k} {η' : I → J' → k} {A : Set I}
    (h : PolyApprox (Sum.elim θ θ') ((fun i => Sum.elim (η i) (η' i)) '' A))
    (ht : ∀ (F : Finset I) (c : I → k) (ε : ℝ),
      (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) →
      ∀ g, ‖trc r g - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ ε)
    (S : ℕ → k) (s : (Γ →* GL (Fin a) k) → ℕ → k) (p : ℕ → J') (u : ℕ → k) (hS : ∀ n, S n = u n * θ' (p n))
    (hs : ∀ i ∈ A, ∀ n, s (ρ i) n = u n * η' i (p n)) : GlobalTheory.CongPhi.JointApprox r (ρ '' A) S s := by
  classical
  intro n ε hε
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ j ≤ n, ‖u j‖ ≤ M :=
    ⟨1 + ∑ j ∈ Finset.range (n + 1), ‖u j‖, le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _), fun j hj =>
      (Finset.single_le_sum (f := fun j => ‖u j‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))).trans
        (le_add_of_nonneg_left zero_le_one)⟩
  have hM0 : 0 < M := by linarith
  obtain ⟨F, c, hF, hP⟩ := approx_index h (div_pos hε hM0)
  have hsum : ∀ f : (Γ →* GL (Fin a) k) → k, ∑ e ∈ F.image ρ, (∑ i ∈ F.filter (fun i => ρ i = e), c i) * f e =
      ∑ i ∈ F, c i * f (ρ i) := fun f => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := ρ) (t := F.image ρ) (fun i hi => Finset.mem_image_of_mem _ hi)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  refine ⟨F.image ρ, fun e => ∑ i ∈ F.filter (fun i => ρ i = e), c i, ?_, fun g => ?_, fun j hj => ?_⟩
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
    exact ⟨i, hF hi, rfl⟩
  · rw [hsum fun e => trc e g]
    refine (ht F c (ε / M) (fun P => ?_) g).trans (div_le_self hε.le hM1)
    have h0 := hP (MvPolynomial.rename Sum.inl P)
    simpa only [MvPolynomial.aeval_rename, Sum.elim_comp_inl] using h0
  · rw [hsum fun e => s e j]
    have h0 := hP (MvPolynomial.X (Sum.inr (p j)))
    simp only [MvPolynomial.aeval_X, Sum.elim_inr] at h0
    have e : S j - ∑ i ∈ F, c i * s (ρ i) j = u j * (θ' (p j) - ∑ i ∈ F, c i * η' i (p j)) := by
      rw [hS, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by rw [hs i (hF hi)]; ring
    rw [e, norm_mul]
    calc _ ≤ M * (ε / M) := mul_le_mul (hM j hj) h0 (norm_nonneg _) hM0.le
      _ = ε := by field_simp

theorem phiSum_satWD {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) (σ : Weil h) (n : ℕ) :
    GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD h a B) σ n =
      ((UpperTheory.V.Af.algSat a (normV w) B).map fun z => z ^ (-(deg σ) * n : ℤ)).sum := by
  have e := Multiset.map_map (fun z : ℂ => X - C z) (fun b : ℂˣ =>
    (((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - a) / 2 : ℝ)) : ℂ)) ^ deg σ * ((b : ℂ)⁻¹) ^ deg σ) B
  rw [GlobalTheory.CongPhi.phiSum, GlobalTheory.SatChar.charPol_satWD]
  erw [← e]
  rw [roots_multiset_prod_X_sub_C, UpperTheory.V.Af.algSat]
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  have hq : (((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - a) / 2 : ℝ)) : ℂ)) = ((((normV w : ℕ) : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _)]
    congr 2
    ring
  simp only [Function.comp_apply]
  rw [hq, ← mul_zpow, ← mul_inv, inv_zpow', zpow_mul, zpow_natCast]

theorem powSatU_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U)
    {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) {B : Multiset ℂˣ} (hB : SatU U w B) (n : ℤ) :
    PowSatU U w n = ((UpperTheory.V.Af.algSat a (normV w) B).map fun z => z ^ n).sum := by
  have h : ∃ B, SatU U w B := ⟨B, hB⟩
  obtain ⟨σ, hσ, h1⟩ := h.choose_spec
  obtain ⟨σ', hσ', h2⟩ := hB
  obtain ⟨e⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E a U hU w hw).2 _ _ hσ hσ'
  rw [PowSatU, dif_pos h, GlobalTheory.LFun.HasSatGL.unique (GlobalTheory.PrinSat.hasSatGL_of_equiv e.symm h1) h2]

end UpperTheory.Gal.Lim
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace UpperTheory.Gal.Lim

open GlobalTheory.Cong.OffTLimit GlobalTheory.CongL.UnitLim in

theorem limWU4_of : ∀ (Rk : ℕ → Prop) (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU),
    SeedWU4 Rk Ty Gen Wt → CongUW4 Rk Ty Gen Wt → LimWU4 Rk := by
  intro Rk Ty Gen Wt hSd hC E Ω _ _ _ _ _ _ l _ ι a ha hRk d hF T hT U hU w₀ v' hw₀ hsp₀ hv' hspv hvap
  have hS : SphOps := GlobalTheory.Cong.SphOpsProof.sphOps
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨Kw, hlev, -, hKGL, hcong⟩ := hC E l ι a ha hRk T hT U hU w₀ v' hw₀ hsp₀ hv' hspv hvap
  have hlsplit : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := fun w hw =>
    Classical.byContradiction fun h => (hF.2.2.2 w h).1 hw
  have hfin := finite_not_sph a U hU.1
  set S : Finset (HeightOneSpectrum (𝓞 E)) := hfin.toFinset with hSdef
  have hsph : ∀ w, IsSplitAt w → ApartAll S w → ∃ B, SatU U w B := by
    intro w hs hA
    by_contra h
    exact hA w (hfin.mem_toFinset.2 ⟨hs, h⟩) rfl
  have hSap : ∀ w, IsSplitAt w → (∃ B, SatU U w B) → ApartAll S w := by
    intro w hs hB u hu hwu
    exact (hfin.mem_toFinset.1 hu).2 (GlobalTheory.CongL.SatConj.exists_satU_of_under_eq E a U hU.1 w u hs hwu.symm hB)
  set W0 : Set (HeightOneSpectrum (𝓞 E)) := {w | IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ∃ B, SatU U w B} with hW0def
  have hW0 : ∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w a := fun w hw =>
    ⟨hw.1, hw.2.1, hKGL w hw.1 (apart_of_not_mem hw₀ hw.2.1) (apart_of_not_mem hv' hw.2.1) hw.2.2⟩
  obtain ⟨J, O, x, fr, n, hx, hpl, hcov, hrat, hidx, hconv⟩ := GlobalTheory.FrobOpsIdx.frobOpsIdx hS E Ω l ι a Kw W0 hW0
  have hcomp : ∀ U' : Submodule ℂ (UA E a → ℂ), IsAutRepU U' → ∀ w, IsSplitAt w →
      ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U' (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ :=
    fun U' hU' w hw => (GlobalTheory.SplitComp.exists_comp_and_unique E a U' hU' w hw).1
  obtain ⟨θ, hθ⟩ : ∃ θ : J → Qbar l, IsSysU O U θ := by
    choose σ hσ using fun j => hcomp U hU.1 (O.pl j) (O.split j)
    refine ⟨fun j => ι.symm (O.z j (σ j)), fun j σ' h' => ?_⟩
    obtain ⟨e⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E a U hU.1 (O.pl j) (O.split j)).2 _ _ (hσ j) h'
    show ι.symm (O.z j (σ j)) = ι.symm (O.z j σ')
    rw [z_eq_of_equiv O j e (hlev _ (O.split j) (apart_of_not_mem hw₀ (O.away j)) (apart_of_not_mem hv' (O.away j)) _ (hσ j))]
  have hsphSeed : ∀ U' : Submodule ℂ (UA E a → ℂ), IsAutRepU U' → HasLevelOff w₀ v' Kw U' → (∃ B, SatU U' v' B) →
      SphOffU w₀ S U' := by
    intro U' hU' hl' hb w hs hap hA
    by_cases hv : Apart w v'
    swap
    · exact GlobalTheory.CongL.SatConj.exists_satU_of_under_eq E a U' hU' v' w hspv (not_not.1 hv) hb
    obtain ⟨σ, hσ⟩ := hcomp U' hU' w hs
    have hfix := hl' w hs hap hv σ hσ
    rw [hKGL w hs hap hv (hsph w hs hA)] at hfix
    obtain ⟨B, hB⟩ := (hS E w a).1 σ hfix
    exact ⟨B, σ, hσ, hB⟩
  choose Z₀ hZ₀ hQ using fun Y => hSd E Ω l ι a ha hRk d hF T hT w₀ v' hw₀ hsp₀ hv' hspv hvap U S Y
  choose! rr hrr using hQ
  let Zs : Finset (HeightOneSpectrum (𝓞 E)) → Finset (HeightOneSpectrum (𝓞 E)) := fun Y =>
    Z₀ Y ∪ Y.filter (fun w => IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ∃ B, SatU U w B)
  have hZs : ∀ Y, ∀ z ∈ Zs Y, IsSplitAt z ∧ Apart z w₀ ∧ Apart z v' ∧ ∃ B, SatU U z B := by
    intro Y z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨hus, hzl, hap, hA⟩ := hZ₀ Y z h
      exact ⟨hus.1, hap, apart_of_not_mem hv' hzl, hsph z hus.1 hA⟩
    · obtain ⟨-, hs, hzl, hB⟩ := Finset.mem_filter.1 h
      exact ⟨hs, apart_of_not_mem hw₀ hzl, apart_of_not_mem hv' hzl, hB⟩
  let Ws : Finset (HeightOneSpectrum (𝓞 E)) → Finset (HeightOneSpectrum (𝓞 E)) := fun Y =>
    Y.filter (fun w => ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B)
  choose cc hcc0 hcc using fun Y => hcong (Zs Y) (Ws Y) (hZs Y) fun w hw =>
    ⟨hlsplit w (Finset.mem_filter.1 hw).2.1, (Finset.mem_filter.1 hw).2⟩
  let Good : Finset (HeightOneSpectrum (𝓞 E)) → Submodule ℂ (UA E a → ℂ) → (J → Qbar l) → Prop := fun Y U' θ' =>
    AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ ((∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧ ∀ w ∈ Ws Y, GenAtU Gen U' w) ∧
      Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Zs Y, GenAtU Gen U' z) ∧ IsSysU O U' θ'
  let I : Type := {p : Finset (HeightOneSpectrum (𝓞 E)) × Submodule ℂ (UA E a → ℂ) × (J → Qbar l) // Good p.1 p.2.1 p.2.2}
  let ρ : I → (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) := fun i => rr i.1.1 i.1.2.1
  let η : I → J → Qbar l := fun i => i.1.2.2
  let D : I → Set J := fun i => {j | η i j = trc (ρ i) (x j)}
  have hQi := fun i : I => hrr i.1.1 i.1.2.1 i.2.1 i.2.2.2.2.2.1 i.2.2.2.2.1 (hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1) i.2.2.2.1.1
    (fun z hz => i.2.2.2.2.2.2.1 z (Finset.mem_union_left _ hz))
  have hpaJ : ∀ Y, PolyApprox (Sum.elim θ fun p : ↥(Ws Y) × ℤ => ι.symm (cc Y p.1 p.2 * PowSatU U p.1 p.2))
      ((fun i : I => Sum.elim (η i) fun p : ↥(Ws Y) × ℤ => ι.symm (cc Y p.1 p.2 * PowSatU i.1.2.1 p.1 p.2)) ''
        {i : I | i.1.1 = Y}) := by
    intro Y
    refine ((hcc Y J O θ hθ).1).mono ?_
    rintro _ ⟨U', θ', h1, h2, hb, h3, h4, h5, h6, hW, h7, rfl⟩
    exact ⟨⟨(Y, U', θ'), h1, h2, ⟨hb, h3, hW⟩, h4, h5, h6, h7⟩, rfl, rfl⟩
  have hpaY : ∀ Y, PolyApprox θ (η '' {i : I | i.1.1 = Y}) := fun Y => approx_left (hpaJ Y)
  obtain ⟨L, hL⟩ := (hcc ∅ J O θ hθ).2 hrat
  have hdense : ∀ s : Finset I, Dense (x '' ⋂ i ∈ s, D i) := by
    intro s
    choose V X hVo hVd hVX using fun i : I => (hQi i).2.2.1
    have hVa : ∀ t : Finset I, IsOpen (⋂ i ∈ t, V i) ∧ Dense (⋂ i ∈ t, V i) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.set_biInter_insert]
        exact ⟨(hVo b).inter ih.1, (hVd b).inter_of_isOpen_left ih.2 (hVo b)⟩
    have hD := (dense_frob_usable_off E Ω l hl d hF.1 (S ∪ s.biUnion X)).inter_of_isOpen_right (hVa s).2 (hVa s).1
    refine Dense.mono ?_ ((inv_surjective.denseRange).dense_image continuous_inv hD)
    rintro _ ⟨g, ⟨⟨w, hwX, hus, hwl, hA, A, hAw, hg⟩, hgV⟩, rfl⟩
    have hwS : ApartAll S w := fun u hu => hA u (Finset.mem_union_left _ hu)
    have hsw : ∃ B, SatU U w B := hsph w hus.1 hwS
    obtain ⟨j, hj1, hj2, hj3⟩ := hcov w ⟨hus.1, hwl, hsw⟩ A hAw g hg
    refine ⟨j, ?_, by rw [hx j, hj2, hj3, pow_one]⟩
    simp only [Set.mem_iInter]
    intro i hi
    subst hj1
    have hap := apart_of_not_mem hw₀ hwl
    obtain ⟨B', σ', hσ', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 (O.pl j) hus.1 hap hwS
    have hchar := ((hVX i (O.pl j) (fun h => hwX (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, h⟩)))
      hus hwl hwS B' ⟨σ', hσ', hB'⟩ A hAw).2 g hg (Set.mem_iInter₂.1 hgV i hi))
    show i.1.2.2 j = trc (ρ i) (x j)
    rw [i.2.2.2.2.2.2.2 j σ' hσ']
    exact hidx j σ' (i.2.2.1 (O.pl j) hus.1 hap (apart_of_not_mem hv' hwl) σ' hσ') B' hB' (ρ i) (by rw [hj2]; exact hchar)
  obtain ⟨t, htL, ht3, ht⟩ := exists_trace_limit l (Formalism.ConjugateSelfDual.G E Ω) a J I x θ L.1 L.2 hL ρ η D
    (fun i => (hQi i).1) (fun i j hj => hj) hdense ((hpaY ∅).mono (Set.image_subset_range _ _))
  have hpt : PolyApprox t ((fun ρ' g => trc ρ' (id g)) '' Set.range ρ) := by
    have := (ht Set.univ (by rw [Set.image_univ]; exact (hpaY ∅).mono (Set.image_subset_range _ _))).1
    rw [Set.image_univ] at this
    rw [← Set.range_comp]
    exact this
  obtain ⟨r, hrc, hrss, hrt, -⟩ := GlobalTheory.Cong.exists_limit_rep l (Formalism.ConjugateSelfDual.G E Ω) a (Formalism.ConjugateSelfDual.G E Ω) id denseRange_id t L.1 L.2 htL
    (Set.range ρ) (by rintro _ ⟨i, rfl⟩; exact (hQi i).1) hpt
  have htr : trc r = t := funext hrt
  have hlin : ∀ A : Set I, PolyApprox θ (η '' A) → LinApprox r (ρ '' A) := by
    intro A hA
    refine GlobalTheory.Cong.linApprox_of_polyApprox_trc (Qbar l) (Formalism.ConjugateSelfDual.G E Ω) a r (ρ '' A) ?_
    rw [htr, Set.image_image]
    exact (ht A hA).1
  refine ⟨r, hrc, hrss, ?_, ?_, ?_⟩
  · intro w hwU hwl B hB
    have hws := hwU.1
    have hsw : ∃ B, SatU U w B := ⟨B, hB⟩
    have hwS := hSap w hws hsw
    have hap := apart_of_not_mem hw₀ hwl
    have hwZ : ∀ i : I, i.1.1 = {w} → w ∈ Zs i.1.1 := fun i hi => by
      rw [hi]
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_singleton_self w, hws, hwl, hsw⟩)
    have hseedFE : ∀ i : I, i.1.1 = {w} → ∀ B', SatU i.1.2.1 w B' →
        UpperTheory.V.Af.FrobEig ι (ρ i) w (UpperTheory.V.Af.algSat a (normV w) B') := by
      intro i hi B' hB'
      have hwY : w ∈ i.1.1 := by rw [hi]; exact Finset.mem_singleton_self w
      exact (hQi i).2.2.2.1 w hwY hwU hwl hwS B' hB' (i.2.2.2.2.2.2.1 w (hwZ i hi) B' hB')
    have hlin0 := hlin {i : I | i.1.1 = {w}} (hpaY {w})
    intro A hA
    refine ⟨fun s hs => GlobalTheory.Cong.ker_of_linApprox l (Formalism.ConjugateSelfDual.G E Ω) a r _ hrss hlin0 s ?_, fun s hs => ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨B', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 w hws hap hwS
      exact (hseedFE i hi B' hB' A hA).1 s hs
    · obtain ⟨σ, hσ, hBσ⟩ := hB
      refine hconv w ⟨hws, hwl, hsw⟩ σ (hlev w hws hap (apart_of_not_mem hv' hwl) σ hσ) B hBσ r ?_ A hA s hs
      intro j hj
      subst hj
      rw [htr, (ht {i : I | i.1.1 = {O.pl j}} (hpaY {O.pl j})).2 j ?_]
      · exact hθ j σ hσ
      · intro i hi
        obtain ⟨B', σ', hσ', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 (O.pl j) hws hap hwS
        obtain ⟨A', hA', hfr⟩ := (hpl j).2
        have hFE := (hseedFE i hi B' ⟨σ', hσ', hB'⟩ A' hA').2 (fr j) hfr
        show i.1.2.2 j = trc (ρ i) (x j)
        rw [i.2.2.2.2.2.2.2 j σ' hσ']
        exact hidx j σ' (i.2.2.1 (O.pl j) hws hap (apart_of_not_mem hv' hwl) σ' hσ') B' hB' (ρ i) hFE
  · intro w hwl hap hapv hsw
    refine GlobalTheory.CongL.crysDRU_of_linApprox GlobalTheory.LimitTop.closedAtL E Ω l ι a ha U hU.1
      (GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E a ha U hU.1) r w hwl hrc hrss _ (hlin _ (hpaY {w})) ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨(hQi i).1, i.1.2.1, sameWtAt_of_off ι i.2.2.2.1.2.1 (fun τ hτ u hu => overPl_unique ι τ hτ hu) hap hapv,
      (hQi i).2.2.2.2.1 w (by rw [show i.1.1 = {w} from hi]; exact Finset.mem_singleton_self w) hwl hap hapv
        (hSap w (hlsplit w hwl) hsw)⟩
  · intro w hwl hap hapv B hB P AI hTi A hA O' _ _ _ Bw hBw σ
    have hws := hlsplit w hwl
    have hwS := hSap w hws ⟨B, hB⟩
    have hwW : w ∈ Ws {w} := Finset.mem_filter.2 ⟨Finset.mem_singleton_self w, hwl, hap, hapv, B, hB⟩
    have hwY : ∀ i : I, i.1.1 = {w} → w ∈ i.1.1 := fun i hi => by rw [hi]; exact Finset.mem_singleton_self w
    choose lam hlam using GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E a ha U hU.1
    refine ⟨ρ '' {i : I | i.1.1 = {w}}, fun τ => LimAtLU.jumpsOf (lam (ι.toRingHom.comp τ)), ?_, ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      have h := (hQi i).2.2.2.2.1 w (hwY i hi) hwl hap hapv hwS P AI hTi A hA O' Bw hBw
      have hWW := sameWtAt_of_off ι i.2.2.2.1.2.1 (fun τ hτ u hu => overPl_unique ι τ hτ hu) hap hapv
      exact ⟨(hQi i).1, h.1, fun τ LL' τ' hi' => h.2.2 τ LL' τ' hi' _ _
        ((hWW _ (LimAtLU.overPl_of_induced ι hA hBw hi') _).1 (hlam _)) (LimAtLU.jumpsOf_map _)⟩
    · have hu : ∀ (n : ℤ) (z : ℂ), ι.symm z = (ι.symm (cc {w} w n))⁻¹ * ι.symm (cc {w} w n * z) := fun n z => by
        rw [map_mul, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero ι.symm).2 (hcc0 {w} w n)), one_mul]
      refine joint (hpaJ {w}) (fun F c ε hP g => by rw [htr]; exact ht3 F c ε hP g) _ _
        (fun n => (⟨w, hwW⟩, -(deg σ) * n)) (fun n => (ι.symm (cc {w} w (-(deg σ) * n)))⁻¹) (fun n => ?_) (fun i hi n => ?_)
      · rw [phiSum_satWD, ← powSatU_eq hU.1 hws hB]
        exact hu _ _
      · obtain ⟨B', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 w hws hap hwS
        have hg : Gen a (normV w) B' := i.2.2.2.1.2.2 w (by rw [show i.1.1 = {w} from hi]; exact hwW) B' hB'
        have e := (hQi i).2.2.2.2.2 w (hwY i hi) hwl hap hapv hwS B' hB' hg P AI hTi A hA O' Bw hBw σ n
        rw [phiSum_satWD, ← powSatU_eq i.2.1.1 hws hB'] at e
        exact (congrArg ι.symm e).trans (hu _ _)

theorem limFinOdd_of (h : SeedFinOdd) (h' : CongFinOdd) : LimFinOdd := limWU4_of _ _ _ _ h h'

end UpperTheory.Gal.Lim
end
