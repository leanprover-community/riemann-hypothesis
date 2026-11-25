module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AdelicSchrodingerTensorEqLocalOfSupportedAt
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
public import Development.WeilBound.CoreStatements.LocalThetaKernels.ExistsSmallSubgroups
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepAd
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKH.Locrep

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def schrL {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    Module.End ℂ ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' a b := by funext x; simp [schr, mul_add]
  map_smul' c a := by funext x; simp [schr, mul_left_comm]

theorem idem_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} (hz : At (evFin F v) z) :
    atPlace v (1 : Fv F v) • z = z := by
  have := hz (1 - atPlace v 1) (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem act_away {X : Spc F E n} {W : Spc F E d} {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v))
    {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : atPlace v (1 : Fv F v) • u = 0) : mat g * u * (mat h)ᵀ = u := by
  have e1 : mat g * u = u := by
    have : (mat g - 1) * u = 0 := by
      rw [← idem_smul hg, Matrix.smul_mul, ← Matrix.mul_smul, hu, Matrix.mul_zero]
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have : u * (mat h - 1)ᵀ = 0 := by
    rw [← idem_smul hh, Matrix.transpose_smul, Matrix.mul_smul, ← Matrix.smul_mul, hu, Matrix.zero_mul]
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  rw [e1, this]

theorem one_mem_UAt (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
  change u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
  rw [sub_self, smul_zero]

theorem mul_mem_UAt {X : Spc F E n} {v : Pl F} {g g' : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v))
    (hg' : g' ∈ UAt σ X (evFin F v)) : g * g' ∈ UAt σ X (evFin F v) := fun u hu => by
  change u • (mat g * mat g' - 1) = 0
  rw [show mat g * mat g' - 1 = mat g * (mat g' - 1) + (mat g - 1) by noncomm_ring, smul_add, hg u hu,
    ← Matrix.mul_smul, hg' u hu, Matrix.mul_zero, add_zero]

/-- Localize the splitting at `v`. Each Schwartz–Bruhat function is fixed by sufficiently small
pairs supported at `v`. -/
theorem exists_smooth_local_rep {ψ : AddChar (AF F) ℂ} {X : Spc F E n} {W : Spc F E d}
    {M : Model σ X W} {om : Rep σ X W} (hstd : IsStd ψ)
    (hs : IsUSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (v : Pl F) :
    ∃ ω ρ, IsLocRep M ψ om v ω ρ ∧
      ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∀ p ∈ U,
        p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ω p φ = φ := by
  have hne : ψ ≠ 1 := fun h => Tw.PsiNontriv.psiV_ne_one ψ hstd v (by rw [h]; rfl)
  have hH := (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F (Fin n × Fin d) ψ hstd.1 hne hstd.2.1).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ) → Module.End ℂ (Fn F n d v) := fun T =>
    res v x₀ ∘ₗ T ∘ₗ tensL v r₀
  have hloc : ∀ T φ, loc T φ = res v x₀ (T (tens (evFin F v) φ r₀)) := fun _ _ => rfl
  have pres : ∀ p, ∀ φ ∈ SB _, loc (om p) φ ∈ SB _ := fun p φ hφ => res_mem v x₀ (hs.pres p _ (h₀ φ hφ).2)
  have presH : ∀ u, ∀ φ ∈ SB _, loc (schrL ψ (M.co.e u)) φ ∈ SB _ := fun u φ hφ => res_mem v x₀ (hH _ _ (h₀ φ hφ).2)
  have acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      Acts (evFin F v) (om (g, h)) φ (loc (om (g, h)) φ) := by
    intro g hg h hh φ hφ
    refine acts_res v hstd.1 hne hstd.2.1 (hs.pres _) (hs.adm _) (fun w h1 h2 Φ hΦ => ?_) h₁ hφ (h₀ φ hφ)
    obtain ⟨u, rfl⟩ := M.co.e.surjective w
    have hu : atPlace v (1 : Fv F v) • u = 0 := by
      apply M.co.e.injective
      rw [map_smul, map_zero]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · change atPlace v 1 * (M.co.e u).1 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).1 i) = 0 from congrFun h1 i, mul_zero, map_zero]
      · change atPlace v 1 * (M.co.e u).2 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).2 i) = 0 from congrFun h2 i, mul_zero, map_zero]
    have := hs.impl (g, h) u Φ hΦ
    rwa [show actAB (cA σ) (g, h) u = u from act_away hg hh hu] at this
  have actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
      Acts (evFin F v) (M.co.rho ψ u) φ (loc (schrL ψ (M.co.e u)) φ) := by
    intro u hu φ hφ
    have e : ∀ a, evFin F v a = 0 → a • M.co.e u = 0 := fun a ha => by rw [← map_smul, hu a ha, map_zero]
    have A : Acts (evFin F v) (M.co.rho ψ u) φ _ := fun r hr =>
      Tw.SchrLoc.schr_tens_of_at ψ v (M.co.e u) (fun i a ha => congrFun (congrArg Prod.fst (e a ha)) i)
        (fun i a ha => congrFun (congrArg Prod.snd (e a ha)) i) φ r hr.1
    have := eq_of_acts v h₁ (h₀ φ hφ) A
    rw [this] at A
    exact A
  have one : ∀ φ ∈ SB _, loc (om 1) φ = φ := fun φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm
  have mul : ∀ p : UA σ X.J × UA σ W.J, ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      loc (om (p * (g', h'))) φ = loc (om p) (loc (om (g', h')) φ) := fun p g' hg' h' hh' φ hφ => by
    rw [hloc, hloc (om p), ← acts g' hg' h' hh' φ hφ r₀ (h₀ φ hφ), map_mul]
    rfl
  have smooth (φ : Fn F n d v) (hφ : φ ∈ SB _) :
      ∃ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∀ p ∈ U,
        p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → loc (om p) φ = φ := by
    obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
    obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
    obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
      (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
      (fun U hU => by
        obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
        obtain ⟨a, ha⟩ := hK2 U₁ h1
        obtain ⟨b, hb⟩ := hK2' U₂ h2
        exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
      (fun p => loc (om p)) (fun p _ => pres p) one
      (fun p _ q hq => mul p q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2))
      (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
    obtain ⟨U, hU, hUK⟩ := hK4 m
    obtain ⟨U', hU', hUK'⟩ := hK4' m
    exact ⟨U ×ˢ U', prod_mem_nhds hU hU', fun p hp hg hh => hm p ⟨hUK _ hp.1 hg, hUK' _ hp.2 hh⟩⟩
  refine ⟨fun p => loc (om p), fun u => loc (schrL ψ (M.co.e u)), ⟨fun g _ h _ => pres _,
    fun g hg h hh φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ acts g hg h hh φ hφ⟩, one,
    fun g _ h _ => mul (g, h), fun φ hφ => ?_, fun u _ => presH u,
    fun u hu φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ actsH u hu φ hφ⟩,
    fun g hg h hh u hu φ hφ => ?_⟩, smooth⟩
  · obtain ⟨U, hU, hfix⟩ := smooth φ hφ
    refine ⟨(fun h : UA σ W.J => ((1 : UA σ X.J), h)) ⁻¹' U, ?_,
      fun h hh hu => hfix (1, h) hh (one_mem_UAt X v) hu⟩
    exact (continuous_const.prodMk continuous_id).continuousAt hU
  · rw [hloc (om (g, h)), hloc _ (loc (om (g, h)) φ), ← actsH u hu φ hφ r₀ (h₀ φ hφ),
      ← acts g hg h hh φ hφ r₀ (h₀ φ hφ), hs.impl _ _ _ (h₀ φ hφ).2]
    rfl

theorem locRepEx : LocRepEx := by
  intro F E _ _ _ _ _ σ n d B X W M om hP v
  obtain ⟨χX, χW, hw⟩ := hP.weil
  obtain ⟨ω, ρ, L, _⟩ := exists_smooth_local_rep hP.base.std (IsUWeilPair.isUSplitting hw) v
  exact ⟨ω, ρ, L⟩

theorem exists_unique_local_actions {ψ : AddChar (AF F) ℂ} {X : Spc F E n} {W : Spc F E d}
    {M : Model σ X W} {om : Rep σ X W} (hstd : IsStd ψ)
    (hs : IsUSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (v : Pl F) :
    (∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      ∃! φ₁, φ₁ ∈ SB _ ∧ Acts (evFin F v) (om (g, h)) φ φ₁) ∧
    (∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
      ∃! φ₁, φ₁ ∈ SB _ ∧ Acts (evFin F v) (M.co.rho ψ u) φ φ₁) ∧
    ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∀ p ∈ U,
      p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → Acts (evFin F v) (om p) φ φ := by
  obtain ⟨ω, ρ, L, smooth⟩ := exists_smooth_local_rep hstd hs v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  obtain ⟨U, hU, hfix⟩ := smooth φ hφ
  exact ⟨U, hU, fun p hp hg hh => (L.acts p.1 hg p.2 hh φ hφ _).2 (hfix p hp hg hh).symm⟩

end PositivityTheory.ThKH.Locrep
